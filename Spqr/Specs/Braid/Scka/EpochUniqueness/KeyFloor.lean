/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Lacramioara Astefanoaei
-/
import SrcTranslated.Funs
import SrcTranslated.FunsExternal
import Spqr.Auxiliary.Aeneas.Result
import Spqr.Specs.Braid.Scka.EpochUniqueness.CalleeEpoch
import Spqr.Specs.Braid.StateMachine.Run

/-! # The epoch of the next key a state can emit

Support lemmas for `Spqr.Specs.Braid.Scka.EpochUniqueness`, which proves that each party
outputs at most one key per epoch. The argument is explained there.

`keyFloor s` is the epoch the next key emitted from `s` would carry. `send_step` and
`recv_step` walk every arm of `States::send` and `States::recv` and show that a call either
emits no key and keeps `keyFloor`, or emits a key at epoch `keyFloor s` in transition (7) or
(5). `send_HeaderReceived_key_isSome` and `recv_EkSentCt1Received_key_isSome` give the
converse: those two transitions always emit a key. `Step.keyFloor_step` combines `send_step`
and `recv_step`, and `epochs_consecutive` extends it by induction to runs. `keyFloor_init_a`
and `keyFloor_init_b` give `keyFloor = 1` for the initial states.

Transitions are numbered as in the state machine of [ML-KEM Braid] §2.5, drawn in its
Fig. 1 (p. 10) and marked `# Transition (n)` in the pseudocode of that section.

## References

* [ML-KEM Braid] R. Schmidt, *The ML-KEM Braid Protocol*, Rev. 1, last updated 2025-09-26.
  <https://signal.org/docs/specifications/mlkembraid/mlkembraid.pdf>

**Source**: spqr/src/v1/chunked/states.rs:203-220, spqr/src/v1/chunked/states.rs:361-368 -/

open Aeneas Aeneas.Std Result
open core.result.Result.Insts.CoreOpsTry (branch_eq_continue)
open core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible (from_residual_ne_ok)
open spqr.v1.chunked.states.epoch_uniqueness

/-- Closes a `recv` branch, given its equation `h`, when the branch either returns `Err` or
returns its input state unchanged with no key. -/
local macro "keep_arm " "at " h:ident : tactic => `(tactic| first
  | (simp only [ok.injEq, reduceCtorEq] at $h:ident; done)
  | (simp only [ok.injEq, core.result.Result.Ok.injEq] at $h:ident; subst $h; exact rfl))

/-- Closes a `recv` branch, given its equation `h`, when the branch returns a new state with no
key. `e` proves that the new state has the same `keyFloor` as the input state. -/
local macro "new_arm " "at " h:ident " using " e:term : tactic => `(tactic|
  (simp only [ok.injEq, core.result.Result.Ok.injEq] at $h:ident; subst $h; exact $e))

/-- Closes a `recv` branch, given its equation `h` and a hypothesis `hs` that the new state is
`NoHeaderReceived`, when the branch either returns `Err` or returns another state. -/
local macro "other_state_arm " "at " h:ident ", " hs:ident : tactic => `(tactic| first
  | (simp only [ok.injEq, reduceCtorEq] at $h:ident; done)
  | (simp only [ok.injEq, core.result.Result.Ok.injEq] at $h:ident; subst $h;
     simp only [reduceCtorEq] at $hs:ident))

namespace spqr.v1.chunked.states

/-- The epoch the next key emitted from a state would carry. For the states that have not yet
emitted the key for their epoch this is the epoch itself; for `Ct1Sampled` and the states after
it, which have, it is the epoch plus one. The epoch is `st.uc.epoch`, where `st.uc` is the
state's struct in the unchunked layer (`src/v1/unchunked/`). The result is in `ℕ`, so the
`+ 1` cannot overflow. -/
def keyFloor : States → Nat
  | .KeysUnsampled st | .KeysSampled st | .HeaderSent st | .Ct1Received st
  | .EkSentCt1Received st | .NoHeaderReceived st | .HeaderReceived st => st.uc.epoch.val
  | .Ct1Sampled st | .EkReceivedCt1Sampled st | .Ct1Acknowledged st
  | .Ct2Sampled st => st.uc.epoch.val + 1

/-- What one successful `send` from `s` does to the key epochs.

* If it emits no key, the new state has the same `keyFloor` as `s`.
* If it emits a key `k`, then `s` is `HeaderReceived st`, `k` carries the epoch of `st`, and the
  new state is `Ct1Sampled` at that same epoch.

The second case is transition (7) of the ML-KEM Braid spec, §2.5, marked in
*HeaderReceived.Send* on p. 18. -/
theorem send_step {R : Type} (i₁ : rand.rng.Rng R) (i₂ : rand_core.CryptoRng R)
    (s : States) (rng rng' : R) (r : v1.chunked.states.Send)
    (h : States.send i₁ i₂ s rng = ok (.Ok r, rng')) :
    match (generalizing := false) r.key with
    | none => keyFloor r.state = keyFloor s
    | some k => ∃ st st', s = .HeaderReceived st ∧ r.state = .Ct1Sampled st' ∧
        k.epoch = st.uc.epoch ∧ st'.uc.epoch = st.uc.epoch := by
  cases s <;> simp only [States.send, send_ek.KeysUnsampled.epoch, send_ek.KeysSampled.epoch,
    send_ek.HeaderSent.epoch,
    send_ek.Ct1Received.epoch, send_ek.EkSentCt1Received.epoch, send_ct.NoHeaderReceived.epoch,
    send_ct.HeaderReceived.epoch, send_ct.Ct1Sampled.epoch, send_ct.EkReceivedCt1Sampled.epoch,
    send_ct.Ct1Acknowledged.epoch, send_ct.Ct2Sampled.epoch, bind_tc_ok, bind_eq_ok,
    Prod.exists, uncurry_apply_pair, ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq,
    exists_eq_right_right] at h
  case EkSentCt1Received | NoHeaderReceived | Ct1Acknowledged =>
    obtain ⟨rfl, -⟩ := h
    exact rfl
  case KeysUnsampled =>
    obtain ⟨_, _, hc, rfl⟩ := h
    exact congrArg (·.val) (KeysUnsampled_send_hdr_chunk_epoch i₁ i₂ _ rng hc)
  case KeysSampled =>
    obtain ⟨_, _, hc, rfl, -⟩ := h
    exact congrArg (·.val) (KeysSampled_send_hdr_chunk_epoch _ hc)
  case HeaderSent =>
    obtain ⟨_, _, hc, rfl, -⟩ := h
    exact congrArg (·.val) (HeaderSent_send_ek_chunk_epoch _ hc)
  case Ct1Received =>
    obtain ⟨_, _, hc, rfl, -⟩ := h
    exact congrArg (·.val) (Ct1Received_send_ek_chunk_epoch _ hc)
  case HeaderReceived st =>
    obtain ⟨st', _, _, hc, rfl⟩ := h
    obtain ⟨h1, h2⟩ := HeaderReceived_send_ct1_chunk_epoch i₁ i₂ st rng hc
    exact ⟨st, st', rfl, rfl, h2, h1⟩
  case Ct1Sampled =>
    obtain ⟨_, _, hc, rfl, -⟩ := h
    exact congrArg (·.val + 1) (Ct1Sampled_send_ct1_chunk_epoch _ hc)
  case EkReceivedCt1Sampled =>
    obtain ⟨_, _, hc, rfl, -⟩ := h
    exact congrArg (·.val + 1) (EkReceivedCt1Sampled_send_ct1_chunk_epoch _ hc)
  case Ct2Sampled =>
    obtain ⟨_, _, hc, rfl, -⟩ := h
    exact congrArg (·.val + 1) (Ct2Sampled_send_ct2_chunk_epoch _ hc)

/-- What one successful `recv` of `msg` from `s` does to the key epochs.

* If it emits no key, the new state has the same `keyFloor` as `s`.
* If it emits a key `k`, then `s` is `EkSentCt1Received st`, `msg` is a `Ct2` chunk at the epoch
  of `st`, `k` carries that epoch, and the new state is `NoHeaderReceived` one epoch later.

The second case is transition (5) of the ML-KEM Braid spec, §2.5, marked in
*EkSentCt1Received.Receive* on p. 16. -/
theorem recv_step (s : States) (msg : Message) (r : v1.chunked.states.Recv)
    (h : States.recv s msg = ok (.Ok r)) :
    match (generalizing := false) r.key with
    | none => keyFloor r.state = keyFloor s
    | some k => ∃ st st' chunk, s = .EkSentCt1Received st ∧ r.state = .NoHeaderReceived st' ∧
        msg.epoch = st.uc.epoch ∧ msg.payload = .Ct2 chunk ∧
        k.epoch = st.uc.epoch ∧ st'.uc.epoch.val = st.uc.epoch.val + 1 := by
  cases s <;> simp only [States.recv, send_ek.KeysUnsampled.epoch, send_ek.KeysSampled.epoch,
    send_ek.HeaderSent.epoch,
    send_ek.Ct1Received.epoch, send_ek.EkSentCt1Received.epoch, send_ct.NoHeaderReceived.epoch,
    send_ct.HeaderReceived.epoch, send_ct.Ct1Sampled.epoch, send_ct.EkReceivedCt1Sampled.epoch,
    send_ct.Ct1Acknowledged.epoch, send_ct.Ct2Sampled.epoch, lift,
    core.cmp.impls.OrdU64.cmp, bind_tc_ok] at h
  case KeysUnsampled | HeaderReceived => split at h <;> keep_arm at h
  case KeysSampled =>
    split at h <;> try keep_arm at h
    split at h <;> try keep_arm at h
    obtain ⟨_, hres, h⟩ := bind_eq_ok.1 h
    new_arm at h using congrArg (·.val) (KeysSampled_recv_ct1_chunk_epoch _ _ _ hres)
  case HeaderSent =>
    split at h <;> try keep_arm at h
    split at h <;> try keep_arm at h
    obtain ⟨res, hres, h⟩ := bind_eq_ok.1 h
    have hv := HeaderSent_recv_ct1_chunk_epoch _ _ _ hres
    cases res <;> new_arm at h using congrArg (·.val) hv
  case Ct1Received =>
    split at h <;> try keep_arm at h
    split at h <;> try keep_arm at h
    obtain ⟨_, hres, h⟩ := bind_eq_ok.1 h
    new_arm at h using congrArg (·.val) (Ct1Received_recv_ct2_chunk_epoch _ _ _ hres)
  case EkSentCt1Received st =>
    split at h <;> try keep_arm at h
    next hcmp =>
    have he : msg.epoch = st.uc.epoch := UScalar.eq_of_val_eq (Nat.compare_eq_eq.1 hcmp)
    split at h <;> try keep_arm at h
    next chunk hpay =>
    simp only [bind_eq_ok] at h
    obtain ⟨res, hres, cf, hcf, h⟩ := h
    cases cf with
    | Break _ => exact (from_residual_ne_ok h).elim
    | Continue val =>
      obtain rfl := branch_eq_continue hcf
      have hv := EkSentCt1Received_recv_ct2_chunk_epoch _ _ _ hres
      cases val with
      | StillReceiving _ => new_arm at h using congrArg (·.val) hv
      | Done p =>
        obtain ⟨st', sec⟩ := p
        simp only at hv
        simp only [uncurry_apply_pair, ok.injEq, core.result.Result.Ok.injEq] at h
        subst h
        exact ⟨st, st', chunk, rfl, rfl, he, hpay, hv.2, hv.1⟩
  case NoHeaderReceived =>
    split at h <;> try keep_arm at h
    split at h <;> try keep_arm at h
    simp only [bind_eq_ok] at h
    obtain ⟨res, hres, cf, hcf, h⟩ := h
    cases cf with
    | Break _ => exact (from_residual_ne_ok h).elim
    | Continue val =>
      obtain rfl := branch_eq_continue hcf
      have hv := NoHeaderReceived_recv_hdr_chunk_epoch _ _ _ hres
      cases val <;> new_arm at h using congrArg (·.val) hv
  case Ct1Sampled =>
    split at h <;> try keep_arm at h
    obtain ⟨⟨chunk, _⟩, -, h⟩ := bind_eq_ok.1 h
    simp only [uncurry_apply_pair] at h
    cases chunk
    · keep_arm at h
    simp only [bind_eq_ok] at h
    obtain ⟨res, hres, cf, hcf, h⟩ := h
    cases cf with
    | Break _ => exact (from_residual_ne_ok h).elim
    | Continue val =>
      obtain rfl := branch_eq_continue hcf
      have hv := Ct1Sampled_recv_ek_chunk_epoch _ _ _ _ hres
      cases val <;> new_arm at h using congrArg (·.val + 1) hv
  case EkReceivedCt1Sampled =>
    split at h <;> try keep_arm at h
    obtain ⟨_, -, h⟩ := bind_eq_ok.1 h
    split at h <;> try keep_arm at h
    obtain ⟨_, hres, h⟩ := bind_eq_ok.1 h
    new_arm at h using congrArg (·.val + 1) (EkReceivedCt1Sampled_recv_ct1_ack_epoch _ _ hres)
  case Ct1Acknowledged =>
    split at h <;> try keep_arm at h
    obtain ⟨chunk, -, h⟩ := bind_eq_ok.1 h
    cases chunk
    · keep_arm at h
    simp only [bind_eq_ok] at h
    obtain ⟨res, hres, cf, hcf, h⟩ := h
    cases cf with
    | Break _ => exact (from_residual_ne_ok h).elim
    | Continue val =>
      obtain rfl := branch_eq_continue hcf
      have hv := Ct1Acknowledged_recv_ek_chunk_epoch _ _ _ hres
      cases val <;> new_arm at h using congrArg (·.val + 1) hv
  case Ct2Sampled =>
    split at h <;> try keep_arm at h
    obtain ⟨_, -, h⟩ := bind_eq_ok.1 h
    split at h <;> try keep_arm at h
    obtain ⟨_, hres, h⟩ := bind_eq_ok.1 h
    new_arm at h using Ct2Sampled_recv_next_epoch_epoch _ _ hres

/-- If `send` from `s` succeeds and emits a key `k`, then `s` is `HeaderReceived st`, `k`
carries the epoch of `st`, and the new state is `Ct1Sampled` at that same epoch. This is
transition (7) of the ML-KEM Braid spec, §2.5, marked in *HeaderReceived.Send* on
p. 18. -/
theorem send_key_epoch {R : Type} (i₁ : rand.rng.Rng R) (i₂ : rand_core.CryptoRng R)
    (s : States) (rng rng' : R) (r : v1.chunked.states.Send) (k : EpochSecret)
    (h : States.send i₁ i₂ s rng = ok (.Ok r, rng')) (hk : r.key = some k) :
    ∃ st st', s = .HeaderReceived st ∧ r.state = .Ct1Sampled st' ∧
      k.epoch = st.uc.epoch ∧ st'.uc.epoch = st.uc.epoch := by
  have := send_step i₁ i₂ s rng rng' r h
  rw [hk] at this
  exact this

/-- If `recv` of `msg` from `s` succeeds and emits a key `k`, then `s` is
`EkSentCt1Received st`, `msg` is a `Ct2` chunk at the epoch of `st`, `k` carries that
epoch, and the new state is `NoHeaderReceived` one epoch later. This is transition (5) of
the ML-KEM Braid spec, §2.5, marked in *EkSentCt1Received.Receive* on p. 16. -/
theorem recv_key_epoch (s : States) (msg : Message) (r : v1.chunked.states.Recv)
    (k : EpochSecret)
    (h : States.recv s msg = ok (.Ok r)) (hk : r.key = some k) :
    ∃ st st' chunk, s = .EkSentCt1Received st ∧ r.state = .NoHeaderReceived st' ∧
      msg.epoch = st.uc.epoch ∧ msg.payload = .Ct2 chunk ∧
      k.epoch = st.uc.epoch ∧ st'.uc.epoch.val = st.uc.epoch.val + 1 := by
  have := recv_step s msg r h
  rw [hk] at this
  exact this

/-- A successful `send` from `HeaderReceived` emits a key. With `send_key_epoch`, a `send`
emits a key exactly when it starts from `HeaderReceived`. -/
theorem send_HeaderReceived_key_isSome {R : Type} (i₁ : rand.rng.Rng R)
    (i₂ : rand_core.CryptoRng R) (st : v1.chunked.send_ct.HeaderReceived) (rng rng' : R)
    (r : v1.chunked.states.Send)
    (h : States.send i₁ i₂ (.HeaderReceived st) rng = ok (.Ok r, rng')) : r.key.isSome := by
  simp only [States.send, bind_eq_ok, Prod.exists, uncurry_apply_pair, ok.injEq, Prod.mk.injEq,
    core.result.Result.Ok.injEq, exists_eq_right_right] at h
  obtain ⟨_, -, _, _, _, -, rfl⟩ := h
  rfl

/-- A successful `recv` from `EkSentCt1Received` that moves to `NoHeaderReceived` emits a key.
With `recv_key_epoch`, a `recv` emits a key exactly when it makes this move. -/
theorem recv_EkSentCt1Received_key_isSome (st : v1.chunked.send_ek.EkSentCt1Received)
    (msg : Message) (r : v1.chunked.states.Recv) (st' : v1.chunked.send_ct.NoHeaderReceived)
    (h : States.recv (.EkSentCt1Received st) msg = ok (.Ok r))
    (hs : r.state = .NoHeaderReceived st') : r.key.isSome := by
  simp only [States.recv, send_ek.EkSentCt1Received.epoch, lift, core.cmp.impls.OrdU64.cmp,
    bind_tc_ok] at h
  split at h <;> try other_state_arm at h, hs
  split at h <;> try other_state_arm at h, hs
  simp only [bind_eq_ok] at h
  obtain ⟨_, -, cf, hcf, h⟩ := h
  cases cf with
  | Break _ => exact (from_residual_ne_ok h).elim
  | Continue val =>
    obtain rfl := branch_eq_continue hcf
    cases val with
    | StillReceiving _ => other_state_arm at h, hs
    | Done p =>
      obtain ⟨_, _⟩ := p
      simp only [uncurry_apply_pair, ok.injEq, core.result.Result.Ok.injEq] at h
      subst h
      rfl

/-- A `send` that emits no key keeps `keyFloor`. -/
theorem send_keyFloor {R : Type} (i₁ : rand.rng.Rng R) (i₂ : rand_core.CryptoRng R)
    (s : States) (rng rng' : R) (r : v1.chunked.states.Send)
    (h : States.send i₁ i₂ s rng = ok (.Ok r, rng')) (hk : r.key = none) :
    keyFloor r.state = keyFloor s := by
  have := send_step i₁ i₂ s rng rng' r h
  rw [hk] at this
  exact this

/-- A `recv` that emits no key keeps `keyFloor`. -/
theorem recv_keyFloor (s : States) (msg : Message) (r : v1.chunked.states.Recv)
    (h : States.recv s msg = ok (.Ok r)) (hk : r.key = none) :
    keyFloor r.state = keyFloor s := by
  have := recv_step s msg r h
  rw [hk] at this
  exact this

/-- What one step from `s` to `s'` does to `keyFloor`. If it emits no key, `keyFloor` is
unchanged. If it emits a key, the key carries epoch `keyFloor s`, and `keyFloor s'` is one
more. -/
theorem Step.keyFloor_step {s s' : States} {k : Option EpochSecret} (h : Step s s' k) :
    match (generalizing := false) k with
    | none => keyFloor s' = keyFloor s
    | some key => key.epoch.val = keyFloor s ∧ keyFloor s' = keyFloor s + 1 := by
  cases h with
  | send i₁ i₂ rng rng' r h =>
    cases hk : r.key with
    | none => exact send_keyFloor i₁ i₂ _ rng rng' r h hk
    | some key =>
      obtain ⟨st, st', rfl, hs, hke, hse⟩ := send_key_epoch i₁ i₂ _ rng rng' r key h hk
      simp [keyFloor, hs, hke, hse]
  | recv msg r h =>
    cases hk : r.key with
    | none => exact recv_keyFloor _ msg r h hk
    | some key =>
      obtain ⟨st, st', _, rfl, hs, -, -, hke, hse⟩ := recv_key_epoch _ msg r key h hk
      simp [keyFloor, hs, hke, hse]

variable {s s' : States} {ks : List EpochSecret}

/-- If a run from `s` to `s'` emits keys `k₀, …, kₙ₋₁`, then `kᵢ` carries epoch
`keyFloor s + i`, and `keyFloor s' = keyFloor s + n`. -/
theorem epochs_consecutive (h : Run s s' ks) :
    ks.map (·.epoch.val) = List.range' (keyFloor s) ks.length ∧
      keyFloor s' = keyFloor s + ks.length := by
  induction h with
  | nil => simp
  | @cons s s₁ s₂ k ks hs _ ih =>
    have := hs.keyFloor_step
    cases k with
    | none => simp_all
    | some key =>
      obtain ⟨hke, hfl⟩ := this
      obtain ⟨ih₁, ih₂⟩ := ih
      refine ⟨?_, ?_⟩
      · simp [hke, ih₁, hfl, List.range'_succ]
      · simp [ih₂, hfl]
        omega

/-- The first key emitted from the state `init_a` returns carries epoch 1. -/
theorem keyFloor_init_a {k : Slice Std.U8} (h : States.init_a k = ok s) : keyFloor s = 1 := by
  simp only [States.init_a, send_ek.KeysUnsampled.new, v1.unchunked.send_ek.KeysUnsampled.new,
    bind_eq_ok, ok.injEq] at h
  obtain ⟨_, ⟨_, ⟨_, -, _, -, rfl⟩, rfl⟩, rfl⟩ := h
  rfl

/-- The first key emitted from the state `init_b` returns carries epoch 1. -/
theorem keyFloor_init_b {k : Slice Std.U8} (h : States.init_b k = ok s) : keyFloor s = 1 := by
  simp only [States.init_b, send_ct.NoHeaderReceived.new, v1.unchunked.send_ct.NoHeaderReceived.new,
    bind_eq_ok, ok.injEq] at h
  obtain ⟨_, ⟨_, -, _, -, _, -, _, ⟨_, -, _, -, rfl⟩, _, -, rfl⟩, rfl⟩ := h
  rfl

end spqr.v1.chunked.states
