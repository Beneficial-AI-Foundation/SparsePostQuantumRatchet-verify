/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Lacramioara Astefanoaei
-/
module

public import Spqr.Specs.Braid.StateMachine.PartialModel

/-! # A runtime checker for one party's observed steps

A runtime monitor observes the calls of one party: each `send` with the randomness it drew, the
message and key it returned and the state it reached, and each `recv` with the message it got
and its result. It also observes the primitive calls the party makes during each of these
calls, which give partial primitives `Q : OPrims` for that call. `checkRun σ steps` replays the
pairs `(Q, obs)` of `steps` from `σ` through `sendO` and `receiveO`, each observation with its
own `Q`. It returns the final state when every primitive value a step needs is known from that
step's `Q` and every observation is what the model's step gives.

`checkRun_sound`, `accepted_alice` and `accepted_bob` state what an accepted replay means: for
every `P` that extends each `Q` (`Agrees P Q`), the observations are steps of the model under
`P` (`Explains`), with the observed messages of `send`, keys, state names and epochs, and the
model has a `Run` under `P` that emits the observed keys. A monitor builds each `Q` from the
calls it logs; nothing here depends on how.

**Source**: ML-KEM Braid Rev. 1, §2.5, §2.6 -/

@[expose] public section

open Aeneas Aeneas.Std

namespace BraidModel

deriving instance DecidableEq for Payload
deriving instance DecidableEq for Msg

/-- The name of a state of §2.5, without its values. -/
inductive Label where
  | keysUnsampled | keysSampled | headerSent | ct1Received | ekSentCt1Received
  | noHeaderReceived | headerReceived | ct1Sampled | ekReceivedCt1Sampled | ct1Acknowledged
  | ct2Sampled
  deriving DecidableEq, Repr, Inhabited

variable {Enc Dec Chunk : Type}

/-- The name of a state. -/
def State.label : State Enc Dec → Label
  | .keysUnsampled .. => .keysUnsampled
  | .keysSampled .. => .keysSampled
  | .headerSent .. => .headerSent
  | .ct1Received .. => .ct1Received
  | .ekSentCt1Received .. => .ekSentCt1Received
  | .noHeaderReceived .. => .noHeaderReceived
  | .headerReceived .. => .headerReceived
  | .ct1Sampled .. => .ct1Sampled
  | .ekReceivedCt1Sampled .. => .ekReceivedCt1Sampled
  | .ct1Acknowledged .. => .ct1Acknowledged
  | .ct2Sampled .. => .ct2Sampled

/-- One observed call of one party. `send r m k l e`: a `send` that drew the randomness `r`,
returned the message `m` and the key `k`, and reached a state named `l` at epoch `e`.
`recvOk m k l e`: a `recv` of `m` that succeeded with the key `k` and reached a state named `l`
at epoch `e`. `recvErr m`: a `recv` of `m` that returned an error. -/
inductive Obs (Chunk : Type) where
  | send (r : Bytes) (m : Msg Chunk) (k : Option Key) (l : Label) (e : Nat)
  | recvOk (m : Msg Chunk) (k : Option Key) (l : Label) (e : Nat)
  | recvErr (m : Msg Chunk)

/-- The key that an observation reports, if any. -/
def Obs.key : Obs Chunk → Option Key
  | .send _ _ k _ _ => k
  | .recvOk _ k _ _ => k
  | .recvErr _ => none

/-- The keys that a list of observations reports, in order. -/
def obsKeys : List (Obs Chunk) → List Key
  | [] => []
  | o :: os => o.key.toList ++ obsKeys os

/-- `Explains P σ obs σ'`: the observations `obs` are steps of the model under `P` from `σ` to
`σ'`. A `send` is `Send()` with the observed randomness that gives the observed message, key,
state name and epoch. A successful `recv` is a successful `Receive()` of the observed message
that gives the observed key, state name and epoch. A failed `recv` is a failed `Receive()` of
the observed message, and leaves the state unchanged. -/
inductive Explains (P : Prims Enc Dec Chunk) :
    State Enc Dec → List (Obs Chunk) → State Enc Dec → Prop
  | nil (σ : State Enc Dec) : Explains P σ [] σ
  | send {σ σ₁ σ₂ : State Enc Dec} {r : Bytes} {m : Msg Chunk} {k : Option Key} {l : Label}
      {e : Nat} {os : List (Obs Chunk)} :
      BraidModel.send P σ r = (σ₁, m, k) → σ₁.label = l → σ₁.epoch = e →
      Explains P σ₁ os σ₂ → Explains P σ (.send r m k l e :: os) σ₂
  | recvOk {σ σ₁ σ₂ : State Enc Dec} {m : Msg Chunk} {k : Option Key} {l : Label} {e : Nat}
      {os : List (Obs Chunk)} :
      receive P σ m = some (σ₁, k) → σ₁.label = l → σ₁.epoch = e →
      Explains P σ₁ os σ₂ → Explains P σ (.recvOk m k l e :: os) σ₂
  | recvErr {σ σ₂ : State Enc Dec} {m : Msg Chunk} {os : List (Obs Chunk)} :
      receive P σ m = none → Explains P σ os σ₂ → Explains P σ (.recvErr m :: os) σ₂

/-- If `Explains P σ obs σ'`, then the model under `P` has a run from `σ` to `σ'` that emits the
keys `obsKeys obs`. -/
theorem Explains.run {P : Prims Enc Dec Chunk} {σ σ' : State Enc Dec}
    {obs : List (Obs Chunk)} (h : Explains P σ obs σ') : Run P σ σ' (obsKeys obs) := by
  induction h with
  | nil σ => exact .nil σ
  | @send σ σ₁ σ₂ r m k l e os hs _ _ _ ih =>
    have hstep : Step P σ σ₁ k := by
      have := Step.send (P := P) σ r
      rw [hs] at this
      exact this
    exact .cons hstep ih
  | @recvOk σ σ₁ σ₂ m k l e os hr _ _ _ ih =>
    exact .cons (Step.recv σ σ₁ m k hr) ih
  | recvErr _ _ ih => exact ih

variable [DecidableEq Chunk]

/-- Replay one observation from `σ` over the partial primitives `Q`. The result is the model's
next state when every primitive value the step needs is known and the model's step gives what
was observed, and `none` otherwise. A failed `recv` matches when the model's `Receive()` fails,
and gives `σ`. -/
def checkStep (Q : OPrims Enc Dec Chunk) (σ : State Enc Dec) :
    Obs Chunk → Option (State Enc Dec)
  | .send r m k l e =>
    match sendO Q σ r with
    | some (σ', m', k') =>
      if m' = m ∧ k' = k ∧ σ'.label = l ∧ σ'.epoch = e then some σ' else none
    | none => none
  | .recvOk m k l e =>
    match receiveO Q σ m with
    | some (some (σ', k')) => if k' = k ∧ σ'.label = l ∧ σ'.epoch = e then some σ' else none
    | _ => none
  | .recvErr m =>
    match receiveO Q σ m with
    | some none => some σ
    | _ => none

/-- Replay a list of observations from `σ`, each over its own partial primitives. -/
def checkRun (σ : State Enc Dec) :
    List (OPrims Enc Dec Chunk × Obs Chunk) → Option (State Enc Dec)
  | [] => some σ
  | (Q, o) :: os => (checkStep Q σ o).bind fun σ' => checkRun σ' os

/-- Assume:

* `checkRun σ steps = some σ'`;
* `P` extends the partial primitives of each step of `steps`.

Then `Explains P σ (steps.map (·.2)) σ'`. -/
theorem checkRun_sound {P : Prims Enc Dec Chunk} {σ σ' : State Enc Dec}
    {steps : List (OPrims Enc Dec Chunk × Obs Chunk)} (hA : ∀ q ∈ steps, Agrees P q.1)
    (h : checkRun σ steps = some σ') : Explains P σ (steps.map (·.2)) σ' := by
  induction steps generalizing σ with
  | nil =>
    simp only [checkRun, Option.some.injEq] at h
    subst h
    exact .nil σ
  | cons q os ih =>
    obtain ⟨Q, o⟩ := q
    have hQ : Agrees P Q := hA _ List.mem_cons_self
    have ih := fun {σ} => @ih σ (fun q hq => hA q (List.mem_cons_of_mem _ hq))
    simp only [checkRun, Option.bind_eq_some_iff] at h
    obtain ⟨σ₁, h₁, h₂⟩ := h
    simp only [List.map_cons]
    cases o with
    | send r m k l e =>
      simp only [checkStep] at h₁
      split at h₁
      · next hs =>
        obtain ⟨⟨rfl, rfl, hl, he⟩, h⟩ := Option.ite_none_right_eq_some.mp h₁
        cases h
        exact .send (sendO_sound hQ hs) hl he (ih h₂)
      · cases h₁
    | recvOk m k l e =>
      simp only [checkStep] at h₁
      split at h₁
      · next hr =>
        obtain ⟨⟨rfl, hl, he⟩, h⟩ := Option.ite_none_right_eq_some.mp h₁
        cases h
        exact .recvOk (receiveO_sound hQ hr) hl he (ih h₂)
      · cases h₁
    | recvErr m =>
      simp only [checkStep] at h₁
      split at h₁
      · next hr =>
        cases h₁
        exact .recvErr (receiveO_sound hQ hr) (ih h₂)
      · cases h₁

/-- Assume:

* `initAliceO Q₀ ss = some σ₀`;
* `checkRun σ₀ steps = some σ'`;
* `P` extends `Q₀` and the partial primitives of each step of `steps`.

Then the observations of `steps` are steps of the model under `P` from `initAlice P ss` to `σ'`
(`Explains`), and the model has a run from `initAlice P ss` to `σ'` that emits their keys. -/
theorem accepted_alice {Q₀ : OPrims Enc Dec Chunk} {ss : Bytes} {σ₀ σ' : State Enc Dec}
    {steps : List (OPrims Enc Dec Chunk × Obs Chunk)} (h₀ : initAliceO Q₀ ss = some σ₀)
    (h : checkRun σ₀ steps = some σ') (P : Prims Enc Dec Chunk) (hA₀ : Agrees P Q₀)
    (hA : ∀ q ∈ steps, Agrees P q.1) :
    Explains P (initAlice P ss) (steps.map (·.2)) σ' ∧
      Run P (initAlice P ss) σ' (obsKeys (steps.map (·.2))) := by
  rw [initAliceO_sound hA₀ h₀]
  exact ⟨checkRun_sound hA h, (checkRun_sound hA h).run⟩

/-- Assume:

* `initBobO Q₀ ss = some σ₀`;
* `checkRun σ₀ steps = some σ'`;
* `P` extends `Q₀` and the partial primitives of each step of `steps`.

Then the observations of `steps` are steps of the model under `P` from `initBob P ss` to `σ'`
(`Explains`), and the model has a run from `initBob P ss` to `σ'` that emits their keys. -/
theorem accepted_bob {Q₀ : OPrims Enc Dec Chunk} {ss : Bytes} {σ₀ σ' : State Enc Dec}
    {steps : List (OPrims Enc Dec Chunk × Obs Chunk)} (h₀ : initBobO Q₀ ss = some σ₀)
    (h : checkRun σ₀ steps = some σ') (P : Prims Enc Dec Chunk) (hA₀ : Agrees P Q₀)
    (hA : ∀ q ∈ steps, Agrees P q.1) :
    Explains P (initBob P ss) (steps.map (·.2)) σ' ∧
      Run P (initBob P ss) σ' (obsKeys (steps.map (·.2))) := by
  rw [initBobO_sound hA₀ h₀]
  exact ⟨checkRun_sound hA h, (checkRun_sound hA h).run⟩

end BraidModel
