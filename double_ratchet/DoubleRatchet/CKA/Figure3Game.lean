/-
Copyright (c) 2026 BAIF. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DoubleRatchet.CKA.Defs
import VCVio.OracleComp.SimSemantics.Append
import VCVio.OracleComp.HasQuery
import VCVio.EvalDist.Bool

/-!
# Figure 3: CKA Security Game (Oracle-Based)

Paper-faithful formalization of Figure 3 from Alwen-Coretti-Dodis (2020)
"The Double Ratchet: Security Notions, Proofs, and Modularization for the
Signal Protocol."

## Game structure (Figure 3)

The adversary interacts adaptively with the following oracles:

- `send-P`: honest send for party P, returns `(T, I)` (message + output key)
- `send-P'(r)`: send with adversary-chosen randomness (requires `allow-corr`)
- `receive-P`: deliver pending message to party P, updates state
- `chall-P`: challenge send at epoch `t*`, returns `(T, I_b)` where `b` is hidden
- `corr-P`: reveal current state of party P (requires corruption permission)

## Corruption predicates

- `allow-corr ⟺ max(t_A, t_B) + 2 ≤ t*` (before challenge window)
- `finished_P ⟺ t_P ≥ t* + Δ` (after healing)
- Corruption permitted when `allow-corr ∨ finished_P`

## Adversary model

The adversary is an `OracleComp` client of the game oracles, following
VCV-io's standard oracle-interaction pattern (cf. PRF, PRFTagReader).
This is the adaptive model from the paper, replacing the restricted
non-adaptive transcript adversary in `MultiEpochGame.lean`.

## Ping-pong ordering

Parties alternate: A sends → B receives → B sends → A receives → ...
Enforced via `GamePhase` in the challenger state. Invalid queries
return `none` with state unchanged, modeling the paper's `req` guards
as failed oracle calls (the adversary continues querying).

## End-of-game condition

The paper says the game ends (not made explicit) once both parties'
states have been revealed after the challenge phase. Tracked via
`corruptedPostChalA` and `corruptedPostChalB` in the game state:
when both are set and `challengeUsed` is true, all oracle handlers
return `none`.
-/

set_option autoImplicit false

open OracleComp ENNReal

namespace CKA

namespace Figure3

/-! ## Party and phase types -/

/-- Which party in the CKA protocol. -/
inductive Party where
  | A
  | B
  deriving DecidableEq, Inhabited, Repr

/-- The other party. -/
def Party.other : Party → Party
  | .A => .B
  | .B => .A

@[simp] lemma Party.other_other (p : Party) : p.other.other = p := by
  cases p <;> rfl

/-- Whose turn it is in the ping-pong protocol. -/
inductive GamePhase where
  /-- Expecting a send (or challenge) from party `p`. -/
  | awaitingSend : Party → GamePhase
  /-- Expecting party `p` to receive the pending message. -/
  | awaitingReceive : Party → GamePhase
  deriving DecidableEq, Inhabited, Repr

/-! ## Oracle query index and spec -/

section OracleSetup

variable (SendCoins Msg Output SenderState ReceiverState : Type)

/-- Query types for the Figure 3 CKA security game.
Each constructor represents an oracle the adversary can call. -/
inductive CKAQueryIdx where
  /-- `send-P`: honest send for party `p`. -/
  | sendHonest : Party → CKAQueryIdx
  /-- `send-P'(r)`: send with adversary-chosen coins `r`. -/
  | sendBadRand : Party → SendCoins → CKAQueryIdx
  /-- `receive-P`: deliver pending message to party `p`. -/
  | receive : Party → CKAQueryIdx
  /-- `chall-P`: challenge send at epoch `t*` for party `p`. -/
  | challenge : Party → CKAQueryIdx
  /-- `corr-P`: reveal current state of party `p`. -/
  | corrupt : Party → CKAQueryIdx
  deriving Inhabited

/-- Return type for each oracle query in the Figure 3 game.
All oracles return `Option` — failed `req` guards yield `none` with
state unchanged (paper's rollback semantics). -/
@[reducible] def ckaReturnType : CKAQueryIdx SendCoins → Type
  | .sendHonest _ => Option (Msg × Output)
  | .sendBadRand _ _ => Option (Msg × Output)
  | .receive _ => Option Unit
  | .challenge _ => Option (Msg × Output)
  | .corrupt _ => Option (SenderState ⊕ ReceiverState)

/-- Oracle specification for the Figure 3 CKA game.
Maps each query index to its return type. -/
@[reducible] def ckaOracleSpec : OracleSpec (CKAQueryIdx SendCoins) :=
  ckaReturnType SendCoins Msg Output SenderState ReceiverState

end OracleSetup

/-! ## Game state -/

/-- State of the Figure 3 CKA security game challenger. -/
structure CKAGameState (SenderState ReceiverState Msg : Type) where
  /-- Current state of party A. -/
  stateA : SenderState ⊕ ReceiverState
  /-- Current state of party B. -/
  stateB : SenderState ⊕ ReceiverState
  /-- Epoch counter for party A (increments on send, receive, and challenge). -/
  epochA : ℕ
  /-- Epoch counter for party B (increments on send, receive, and challenge). -/
  epochB : ℕ
  /-- Challenge epoch `t*`. -/
  tStar : ℕ
  /-- Healing parameter `Δ`. -/
  delta : ℕ
  /-- Whether the challenge epoch uses random output (`true`) or real (`false`). -/
  challengeIsRandom : Bool
  /-- Current phase of the ping-pong protocol. -/
  phase : GamePhase
  /-- Pending message from the last send (if any). -/
  pendingMsg : Option Msg
  /-- Whether the challenge oracle has been used. -/
  challengeUsed : Bool
  /-- Party A's state was revealed after the challenge phase (`finished_A` held). -/
  corruptedPostChalA : Bool
  /-- Party B's state was revealed after the challenge phase (`finished_B` held). -/
  corruptedPostChalB : Bool

instance {SenderState ReceiverState Msg : Type}
    [Inhabited SenderState] [Inhabited ReceiverState] [Inhabited Msg] :
    Inhabited (CKAGameState SenderState ReceiverState Msg) where
  default := {
    stateA := .inl default
    stateB := .inr default
    epochA := 0
    epochB := 0
    tStar := 0
    delta := 0
    challengeIsRandom := false
    phase := .awaitingSend .A
    pendingMsg := none
    challengeUsed := false
    corruptedPostChalA := false
    corruptedPostChalB := false
  }

/-! ## Party-specific corruption predicates (Figure 3) -/

section Corruption

variable {SenderState ReceiverState Msg : Type}

/-- `allow-corr` from Figure 3: corruption allowed when the game has not
yet entered the challenge window. Uses `max(t_A, t_B)`. -/
def allowCorrFig3 (st : CKAGameState SenderState ReceiverState Msg) : Prop :=
  max st.epochA st.epochB + 2 ≤ st.tStar

/-- `finished_P` from Figure 3: party P's state can be safely revealed once
its epoch counter reaches `t* + Δ`. -/
def finishedParty (st : CKAGameState SenderState ReceiverState Msg)
    (p : Party) : Prop :=
  match p with
  | .A => st.epochA ≥ st.tStar + st.delta
  | .B => st.epochB ≥ st.tStar + st.delta

/-- Corruption is permitted for party P iff `allow-corr ∨ finished_P`. -/
def corruptionPermittedFig3 (st : CKAGameState SenderState ReceiverState Msg)
    (p : Party) : Prop :=
  allowCorrFig3 st ∨ finishedParty st p

instance (st : CKAGameState SenderState ReceiverState Msg) :
    Decidable (allowCorrFig3 st) :=
  inferInstanceAs (Decidable (_ ≤ _))

instance (st : CKAGameState SenderState ReceiverState Msg) (p : Party) :
    Decidable (finishedParty st p) := by
  unfold finishedParty; cases p <;> exact inferInstanceAs (Decidable (_ ≥ _))

instance (st : CKAGameState SenderState ReceiverState Msg) (p : Party) :
    Decidable (corruptionPermittedFig3 st p) :=
  inferInstanceAs (Decidable (_ ∨ _))

end Corruption

/-! ## State accessors -/

section StateAccess

variable {SenderState ReceiverState Msg : Type}

/-- Get a party's current state. -/
def CKAGameState.stateOf (st : CKAGameState SenderState ReceiverState Msg)
    (p : Party) : SenderState ⊕ ReceiverState :=
  match p with
  | .A => st.stateA
  | .B => st.stateB

/-- Get a party's epoch counter. -/
def CKAGameState.epochOf (st : CKAGameState SenderState ReceiverState Msg)
    (p : Party) : ℕ :=
  match p with
  | .A => st.epochA
  | .B => st.epochB

/-- Update a party's state. -/
def CKAGameState.setStateOf (st : CKAGameState SenderState ReceiverState Msg)
    (p : Party) (newState : SenderState ⊕ ReceiverState) :
    CKAGameState SenderState ReceiverState Msg :=
  match p with
  | .A => { st with stateA := newState }
  | .B => { st with stateB := newState }

/-- Increment a party's epoch counter. -/
def CKAGameState.incEpoch (st : CKAGameState SenderState ReceiverState Msg)
    (p : Party) : CKAGameState SenderState ReceiverState Msg :=
  match p with
  | .A => { st with epochA := st.epochA + 1 }
  | .B => { st with epochB := st.epochB + 1 }

end StateAccess

/-! ## Post-increment corruption check -/

section PostIncrementCorr

variable {SenderState ReceiverState Msg : Type}

/-- `allow-corr` evaluated against the post-increment epoch for party `p`.
Paper's `send-A'(r)`: `t_A++` then `req allow-corr`, rolled back on failure.
Pre-checking against `st.incEpoch p` avoids needing rollback. -/
def allowCorrPostIncrement (st : CKAGameState SenderState ReceiverState Msg)
    (p : Party) : Prop :=
  allowCorrFig3 (st.incEpoch p)

instance (st : CKAGameState SenderState ReceiverState Msg) (p : Party) :
    Decidable (allowCorrPostIncrement st p) := by
  unfold allowCorrPostIncrement
  exact inferInstanceAs (Decidable (allowCorrFig3 _))

end PostIncrementCorr

/-! ## End-of-game tracking -/

section EndOfGame

variable {SenderState ReceiverState Msg : Type}

/-- The game has ended: challenge was used and both parties' states have
been revealed post-challenge. After this, all oracle queries return `none`. -/
def CKAGameState.gameEnded (st : CKAGameState SenderState ReceiverState Msg) : Bool :=
  st.challengeUsed && st.corruptedPostChalA && st.corruptedPostChalB

/-- Mark that party `p` was corrupted post-challenge. -/
def CKAGameState.setCorruptedPostChal
    (st : CKAGameState SenderState ReceiverState Msg)
    (p : Party) : CKAGameState SenderState ReceiverState Msg :=
  match p with
  | .A => { st with corruptedPostChalA := true }
  | .B => { st with corruptedPostChalB := true }

end EndOfGame

/-! ## Oracle implementation -/

section OracleImpl

variable {SharedKey SenderState ReceiverState Msg Output SendCoins : Type}

/-- Handle a send operation: given sender state and coins, update game state
and return `some (msg, output)`. Returns `none` (state unchanged) if party
not in sender state. -/
private def handleSend
    (cka : CKASchemeWithCoins SharedKey SenderState ReceiverState Msg Output SendCoins)
    (p : Party) (coins : SendCoins) :
    StateT (CKAGameState SenderState ReceiverState Msg) ProbComp (Option (Msg × Output)) := do
  let st ← get
  match st.stateOf p with
  | .inl ss =>
    let (rs', msg, output) := cka.sendDet ss coins
    let st' := (st.setStateOf p (.inr rs')).incEpoch p
    set { st' with
      phase := .awaitingReceive p.other,
      pendingMsg := some msg }
    pure (some (msg, output))
  | .inr _ =>
    pure none

/-- Oracle implementation for the Figure 3 CKA game.

Each oracle handler runs in `StateT CKAGameState ProbComp`, maintaining the
challenger's hidden state. Failed `req` guards return `none` with state
unchanged (paper's rollback semantics). Once the game has ended (both
parties corrupted post-challenge), all queries return `none`. -/
noncomputable def ckaGameQueryImpl
    (cka : CKASchemeWithCoins SharedKey SenderState ReceiverState Msg Output SendCoins)
    [SampleableType SendCoins] [SampleableType Output]
    [Inhabited Msg] [Inhabited Output]
    [Inhabited SenderState] [Inhabited ReceiverState] :
    QueryImpl (ckaOracleSpec SendCoins Msg Output SenderState ReceiverState)
      (StateT (CKAGameState SenderState ReceiverState Msg) ProbComp)
  | .sendHonest p => do
      let st ← get
      if st.gameEnded then pure none
      else match st.phase with
      | .awaitingSend p' =>
        if p = p' then do
          let coins ← liftM ($ᵗ SendCoins : ProbComp SendCoins)
          handleSend cka p coins
        else pure none
      | _ => pure none

  | .sendBadRand p r => do
      let st ← get
      if st.gameEnded then pure none
      else match st.phase with
      | .awaitingSend p' =>
        if p = p' ∧ decide (allowCorrPostIncrement st p) then
          handleSend cka p r
        else pure none
      | _ => pure none

  | .receive p => do
      let st ← get
      if st.gameEnded then pure none
      else match st.phase with
      | .awaitingReceive p' =>
        if p = p' then
          match st.pendingMsg, st.stateOf p with
          | some msg, .inr rs => do
            let (ss', _output) ← liftM (cka.recv rs msg)
            let st' := (st.setStateOf p (.inl ss')).incEpoch p
            set ({ st' with
              phase := .awaitingSend p,
              pendingMsg := none } : CKAGameState SenderState ReceiverState Msg)
            pure (some ())
          | _, _ => pure none
        else pure none
      | _ => pure none

  | .challenge p => do
      let st ← get
      if st.gameEnded then pure none
      else match st.phase with
      | .awaitingSend p' =>
        if p = p' ∧ st.epochOf p + 1 = st.tStar ∧ !st.challengeUsed then do
          let coins ← liftM ($ᵗ SendCoins : ProbComp SendCoins)
          match st.stateOf p with
          | .inl ss => do
            let (rs', msg, realOutput) := cka.sendDet ss coins
            let output ← if st.challengeIsRandom
              then liftM ($ᵗ Output : ProbComp Output)
              else pure realOutput
            let st' := (st.setStateOf p (.inr rs')).incEpoch p
            set { st' with
              phase := .awaitingReceive p.other,
              pendingMsg := some msg,
              challengeUsed := true }
            pure (some (msg, output))
          | .inr _ => pure none
        else pure none
      | _ => pure none

  | .corrupt p => do
      let st ← get
      if st.gameEnded then pure none
      else if decide (corruptionPermittedFig3 st p) then do
        if st.challengeUsed && decide (finishedParty st p) then
          modify fun s => s.setCorruptedPostChal p
        pure (some (st.stateOf p))
      else
        pure none

end OracleImpl

/-! ## Adversary, game experiment, and security definition -/

section Game

variable {SharedKey SenderState ReceiverState Msg Output SendCoins : Type}

/-- Full oracle spec for the Figure 3 game: adversary gets private randomness
(`unifSpec`) and the CKA game oracles. -/
abbrev Figure3OracleSpec (SendCoins Msg Output SenderState ReceiverState : Type) :=
  unifSpec + ckaOracleSpec SendCoins Msg Output SenderState ReceiverState

/-- Adversary for the Figure 3 CKA game. Interacts adaptively with game
oracles and outputs a boolean guess. -/
abbrev Figure3Adversary (SendCoins Msg Output SenderState ReceiverState : Type) :=
  OracleComp (Figure3OracleSpec SendCoins Msg Output SenderState ReceiverState) Bool

/-- Run the Figure 3 CKA experiment with a given challenge mode.

- `challengeIsRandom = false`: real experiment (all outputs genuine)
- `challengeIsRandom = true`: random experiment (challenge output replaced)

Returns the adversary's guess bit directly. Failed oracle calls return
`none` with state unchanged — the adversary continues querying. -/
noncomputable def figure3Exp
    [SampleableType SharedKey] [SampleableType SendCoins] [SampleableType Output]
    [Inhabited Msg] [Inhabited Output]
    [Inhabited SenderState] [Inhabited ReceiverState]
    (cka : CKASchemeWithCoins SharedKey SenderState ReceiverState Msg Output SendCoins)
    (tStar delta : ℕ) (challengeIsRandom : Bool)
    (adversary : Figure3Adversary SendCoins Msg Output SenderState ReceiverState) :
    ProbComp Bool := do
  let k ← $ᵗ SharedKey
  let (ss, rs) ← cka.init k
  let initState : CKAGameState SenderState ReceiverState Msg :=
    { stateA := .inl ss
      stateB := .inr rs
      epochA := 0
      epochB := 0
      tStar := tStar
      delta := delta
      challengeIsRandom := challengeIsRandom
      phase := .awaitingSend .A
      pendingMsg := none
      challengeUsed := false
      corruptedPostChalA := false
      corruptedPostChalB := false }
  let unifImpl :=
    (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
      (StateT (CKAGameState SenderState ReceiverState Msg) ProbComp)
  let gameImpl := ckaGameQueryImpl cka
  let guess ← (simulateQ (unifImpl + gameImpl) adversary).run' initState
  pure guess

/-- Figure 3 CKA distinguishing advantage.
`Adv^CKA_{ror,Δ}(A) = |Pr[A=1 | real] - Pr[A=1 | random]|`
(Definition 13, Alwen-Coretti-Dodis 2020.) -/
noncomputable def figure3Advantage
    [SampleableType SharedKey] [SampleableType SendCoins] [SampleableType Output]
    [Inhabited Msg] [Inhabited Output]
    [Inhabited SenderState] [Inhabited ReceiverState]
    (cka : CKASchemeWithCoins SharedKey SenderState ReceiverState Msg Output SendCoins)
    (tStar delta : ℕ)
    (adversary : Figure3Adversary SendCoins Msg Output SenderState ReceiverState) : ℝ :=
  |(Pr[= true | figure3Exp cka tStar delta false adversary]).toReal -
    (Pr[= true | figure3Exp cka tStar delta true adversary]).toReal|

/-- A CKA scheme is `(Δ, ε)`-secure in the Figure 3 game if every adaptive
adversary has distinguishing advantage at most `ε`, for all choices of
challenge epoch `t*`.

This is Definition 13 from Alwen-Coretti-Dodis (2020) with adaptive
oracle interaction, party-specific corruption, and bad-randomness oracles. -/
def Figure3CKASecure
    [SampleableType SharedKey] [SampleableType SendCoins] [SampleableType Output]
    [Inhabited Msg] [Inhabited Output]
    [Inhabited SenderState] [Inhabited ReceiverState]
    (cka : CKASchemeWithCoins SharedKey SenderState ReceiverState Msg Output SendCoins)
    (delta : ℕ) (ε : ℝ) : Prop :=
  ∀ (tStar : ℕ) (adversary : Figure3Adversary SendCoins Msg Output SenderState ReceiverState),
    figure3Advantage cka tStar delta adversary ≤ ε

end Game

end Figure3

end CKA
