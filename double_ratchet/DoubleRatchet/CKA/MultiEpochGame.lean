/-
Copyright (c) 2026 BAIF. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DoubleRatchet.CKA.Security
import VCVio.OracleComp.Constructions.SampleableType

/-!
# Multi-Epoch CKA Security Game (Figure 3)

The full CKA security game from Alwen-Coretti-Dodis (2020), Figure 3,
parameterized by a healing parameter `Δ_CKA`.

## Game structure (Figure 3)

1. **Init**: Adversary chooses challenge epoch `t*`. Game samples shared key
   `k ←$ K`, initializes both parties, sets epoch counters `t_A, t_B ← 0`,
   and samples hidden bit `b ←$ {0,1}`.

2. **Epochs**: Parties alternate in ping-pong order:
   - `send-P`: honest send, returns `(T, I)`
   - `send-P'(r)`: send with adversary-chosen randomness (requires `allow-corr`)
   - `receive-P`: receive message, update state
   - `chall-P`: challenge send at epoch `t*`, returns `(T, I_real)` or `(T, I_rand)`

3. **Corruption**: `corr-P` reveals party state, permitted when:
   - `allow-corr_P ⟺ max(t_A, t_B) ≤ t* - 2` (before challenge window)
   - `finished_P ⟺ t_P ≥ t* + Δ_CKA` (after healing)

4. **Output**: Adversary outputs bit `b'`, wins if `b' = b`.

## Δ parameter semantics

`Δ_CKA` is the number of epochs after `t*` before the state can be safely
revealed. For DDH-CKA, `Δ = 1`: one fresh DH exchange after the challenge
epoch makes the state independent of the challenged key.

## Simplification

This formalization uses a non-adaptive adversary: it commits to `t*` and
epoch count upfront, then sees the full transcript before guessing. For
DDH-CKA (Theorem 3), adaptivity is WLOG — the reduction doesn't exploit it.
-/

set_option autoImplicit false

open OracleComp ENNReal

namespace CKA

/-! ## Corruption predicates (Figure 3) -/

/-- `allow-corr` from Figure 3: corruption is allowed when the game has not
yet entered the challenge window. Specifically, the current epoch must be
at least 2 before the challenge epoch `t*`. -/
def allowCorr (epoch tStar : ℕ) : Prop := epoch + 2 ≤ tStar

/-- `finished` from Figure 3: a party's state can be safely revealed once
its epoch counter reaches `t* + Δ`. -/
def epochFinished (epoch tStar delta : ℕ) : Prop := epoch ≥ tStar + delta

/-- Corruption is permitted at a given epoch iff `allow-corr ∨ finished`. -/
def corruptionPermitted (epoch tStar delta : ℕ) : Prop :=
  allowCorr epoch tStar ∨ epochFinished epoch tStar delta

instance (epoch tStar : ℕ) : Decidable (allowCorr epoch tStar) :=
  inferInstanceAs (Decidable (_ ≤ _))

instance (epoch tStar delta : ℕ) : Decidable (epochFinished epoch tStar delta) :=
  inferInstanceAs (Decidable (_ ≥ _))

instance (epoch tStar delta : ℕ) : Decidable (corruptionPermitted epoch tStar delta) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-! ## Multi-epoch game execution -/

section Execution

variable {SharedKey SenderState ReceiverState Msg Output : Type}

/-- Result of running multiple CKA epochs. Bundles the transcript,
intermediate sender states at each epoch (for potential corruption reveal),
and the final state pair. -/
structure EpochResult (Msg Output SenderState ReceiverState : Type) where
  /-- Transcript: `(message, output_key)` per epoch. -/
  transcript : List (Msg × Output)
  /-- Sender's state AFTER each epoch (indexed by epoch number).
  Used to compute corruption reveals: the sender's state after epoch `i`
  is `Sum.inr r'` (a `ReceiverState`, since `send` returns `ReceiverState`). -/
  senderStatesAfter : List (SenderState ⊕ ReceiverState)
  /-- Final sender state. -/
  finalSender : SenderState
  /-- Final receiver state. -/
  finalReceiver : ReceiverState

/-- Run `remaining` CKA epochs starting from epoch `currentEpoch`.
At each epoch the sender sends and the receiver receives; their roles
swap automatically because `send` returns `ReceiverState` and `recv`
returns `SenderState`.

Returns the full transcript AND intermediate states for corruption. -/
def runEpochs (cka : CKAScheme SharedKey SenderState ReceiverState Msg Output)
    (currentEpoch : ℕ) :
    (remaining : ℕ) → SenderState → ReceiverState →
    ProbComp (EpochResult Msg Output SenderState ReceiverState)
  | 0, s, r => pure ⟨[], [], s, r⟩
  | n + 1, s, r => do
      let (r', msg, output) ← cka.send s
      let (s', _) ← cka.recv r msg
      -- After this epoch: sender held `s : SenderState`, now holds `r' : ReceiverState`
      -- Record the sender's post-epoch state as `Sum.inr r'`
      let rest ← runEpochs cka (currentEpoch + 1) n s' r'
      pure ⟨(msg, output) :: rest.transcript,
            Sum.inr r' :: rest.senderStatesAfter,
            rest.finalSender, rest.finalReceiver⟩

/-- Run `remaining` CKA epochs, but at epoch `tStar` replace the output key
with a uniformly random sample. All other epochs are honest.

Returns the full transcript AND intermediate states for corruption. -/
def runEpochsRand [SampleableType Output]
    (cka : CKAScheme SharedKey SenderState ReceiverState Msg Output)
    (tStar : ℕ) (currentEpoch : ℕ) :
    (remaining : ℕ) → SenderState → ReceiverState →
    ProbComp (EpochResult Msg Output SenderState ReceiverState)
  | 0, s, r => pure ⟨[], [], s, r⟩
  | n + 1, s, r => do
      let (r', msg, realOutput) ← cka.send s
      let (s', _) ← cka.recv r msg
      let output ← if currentEpoch = tStar then $ᵗ Output else pure realOutput
      let rest ← runEpochsRand cka tStar (currentEpoch + 1) n s' r'
      pure ⟨(msg, output) :: rest.transcript,
            Sum.inr r' :: rest.senderStatesAfter,
            rest.finalSender, rest.finalReceiver⟩

/-- Filter intermediate states by corruption permissions.
Given a list of corruption requests (epoch numbers), the challenge epoch
`tStar`, and healing parameter `delta`, return the states at epochs where
`corruptionPermitted` holds. States at forbidden epochs are silently dropped. -/
def filterCorruptionReveals
    (allStates : List (ℕ × (SenderState ⊕ ReceiverState)))
    (tStar delta : ℕ) : List (SenderState ⊕ ReceiverState) :=
  (allStates.filter fun (epoch, _) => decide (corruptionPermitted epoch tStar delta)).map (·.2)

/-- Index a list with 1-based epoch numbers. -/
def indexFrom {α : Type} (start : ℕ) : List α → List (ℕ × α)
  | [] => []
  | x :: xs => (start, x) :: indexFrom (start + 1) xs

/-- Compute revealed states: zip epoch numbers with intermediate states,
keep only those requested by the adversary AND permitted by the game. -/
def computeRevealedStates
    (intermediateStates : List (SenderState ⊕ ReceiverState))
    (corruptionRequests : List ℕ)
    (tStar delta : ℕ) : List (SenderState ⊕ ReceiverState) :=
  let indexed := indexFrom 1 intermediateStates
  let requested := List.filter (fun (epoch, _) => decide (epoch ∈ corruptionRequests)) indexed
  filterCorruptionReveals requested tStar delta

end Execution

/-! ## Multi-epoch adversary and game -/

section Game

variable {SharedKey SenderState ReceiverState Msg Output : Type}

/-- A multi-epoch CKA adversary for the Figure 3 game.

The adversary commits to a challenge epoch `tStar` and total epoch count
`numEpochs`, then after observing the game transcript (and any permitted
corrupted states), outputs a bit guess.

This is a non-adaptive model. The paper's Figure 3 allows fully adaptive
oracle interaction; for DDH-CKA with Δ=1, the two models are equivalent
because the reduction simulates all non-challenge epochs independently. -/
structure MultiEpochCKAAdversary
    (Msg Output SenderState ReceiverState : Type) where
  /-- Challenge epoch `t*` (1-indexed). -/
  tStar : ℕ
  /-- Total number of epochs. -/
  numEpochs : ℕ
  /-- Challenge epoch is within range. -/
  tStar_le : tStar ≤ numEpochs
  /-- Challenge epoch is positive (epoch 0 is init). -/
  tStar_pos : 0 < tStar
  /-- Epochs at which the adversary requests corruption.
  Only epochs where `corruptionPermitted` holds yield actual state. -/
  corruptionRequests : List ℕ
  /-- After seeing the transcript and any revealed states, guess the bit.
  - `transcript` has length `numEpochs`: each entry is `(message, output_key)`.
    At epoch `tStar`, the output key is either genuine (real) or random.
  - `revealedStates` contains states at epochs where corruption was permitted. -/
  guess : List (Msg × Output) →
          List (SenderState ⊕ ReceiverState) →
          ProbComp Bool

variable [SampleableType SharedKey]

/-- Multi-epoch CKA real experiment (Figure 3 with `b = 0`).
All output keys, including at the challenge epoch, are genuine.
Corruption reveals are filtered by `corruptionPermitted epoch tStar delta`. -/
noncomputable def multiEpochCKARealExp
    (cka : CKAScheme SharedKey SenderState ReceiverState Msg Output)
    (delta : ℕ)
    (adversary : MultiEpochCKAAdversary Msg Output SenderState ReceiverState) :
    ProbComp Bool := do
  let k ← $ᵗ SharedKey
  let (s, r) ← cka.init k
  let result ← runEpochs cka 1 adversary.numEpochs s r
  let revealed := computeRevealedStates result.senderStatesAfter
    adversary.corruptionRequests adversary.tStar delta
  adversary.guess result.transcript revealed

/-- Multi-epoch CKA random experiment (Figure 3 with `b = 1`).
The output key at epoch `tStar` is replaced with a uniform random sample;
all other epoch keys are genuine.
Corruption reveals are filtered by `corruptionPermitted epoch tStar delta`. -/
noncomputable def multiEpochCKARandExp
    [SampleableType Output]
    (cka : CKAScheme SharedKey SenderState ReceiverState Msg Output)
    (delta : ℕ)
    (adversary : MultiEpochCKAAdversary Msg Output SenderState ReceiverState) :
    ProbComp Bool := do
  let k ← $ᵗ SharedKey
  let (s, r) ← cka.init k
  let result ← runEpochsRand cka adversary.tStar 1 adversary.numEpochs s r
  let revealed := computeRevealedStates result.senderStatesAfter
    adversary.corruptionRequests adversary.tStar delta
  adversary.guess result.transcript revealed

variable [SampleableType Output]

/-- Multi-epoch CKA distinguishing advantage.
`Adv^CKA_{ror,Δ}(A) = |Pr[A outputs 1 | real] - Pr[A outputs 1 | random]|`
(Definition 13, Alwen-Coretti-Dodis 2020.) -/
noncomputable def multiEpochAdvantage
    (cka : CKAScheme SharedKey SenderState ReceiverState Msg Output)
    (delta : ℕ)
    (adversary : MultiEpochCKAAdversary Msg Output SenderState ReceiverState) : ℝ :=
  |(Pr[= true | multiEpochCKARealExp cka delta adversary]).toReal -
    (Pr[= true | multiEpochCKARandExp cka delta adversary]).toReal|

/-! ## Security definition with Δ (Definition 13) -/

/-- A CKA scheme is `(Δ, ε)`-secure if every multi-epoch adversary has
distinguishing advantage at most `ε` in the Figure 3 game with healing
parameter `Δ`.

This is Definition 13 from Alwen-Coretti-Dodis (2020), minus the runtime
parameter `t` (we quantify over all adversaries, not just `t`-time ones). -/
def CKASecureDelta
    (cka : CKAScheme SharedKey SenderState ReceiverState Msg Output)
    (delta : ℕ) (ε : ℝ) : Prop :=
  ∀ adversary : MultiEpochCKAAdversary Msg Output SenderState ReceiverState,
    multiEpochAdvantage cka delta adversary ≤ ε

/-- The single-epoch game is a special case of the multi-epoch game:
any single-epoch adversary can be lifted to a 1-epoch multi-epoch adversary
with `tStar = 1`. Therefore `CKASecureDelta` implies `CKASecure`. -/
lemma CKASecureDelta_implies_CKASecure
    (cka : CKAScheme SharedKey SenderState ReceiverState Msg Output)
    (delta : ℕ) (ε : ℝ) :
    CKASecureDelta cka delta ε → CKASecure cka ε := by
  sorry

end Game

end CKA
