/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Lacramioara Astefanoaei
-/
module

public import SrcTranslated.Funs
public meta import Spqr.Auxiliary.SpecTags
public import Spqr.Auxiliary.Aeneas.SpecImpExists

/-! # The epoch guards of `States::recv`

Let `e = States.epochOf s` be the epoch of the state `s`. Every arm of `States::recv` first
compares `msg.epoch` with `e`. When `msg.epoch ≠ e`, the arm decides without reading the payload:

* `recv_of_lt`: if `msg.epoch < e`, the state is unchanged and no key is emitted.
* `recv_of_gt`: if `msg.epoch > e`, the result is `Err(EpochOutOfRange msg.epoch)`, except in
  `Ct2Sampled` with `msg.epoch = e + 1`.
* `recv_Ct2Sampled_next_epoch`: in that exception the state becomes `KeysUnsampled` at epoch
  `e + 1` with the same authenticator, and no key is emitted. This is transition (13) of
  [ML-KEM Braid] §2.5, marked in *Ct2Sampled.Receive* on p. 23.

The theorems state the code. `recv_of_lt` and `recv_Ct2Sampled_next_epoch` agree with §2.5 and
carry its tag. `recv_of_gt` does not, because of one departure from the spec:

1. D2. In §2.5 every `Receive` function ignores a message with `msg.epoch > e`, apart from
   transition (13). The code returns `Err(EpochOutOfRange msg.epoch)` instead, so it is
   stricter than the spec: a message from a future epoch is reported as an error
   instead of being dropped. D2 is the project's label for this departure. It is provisional:
   `recv_of_gt` states what the code does, until Signal rules whether the spec or the code
   changes. If the code adopts the spec's no-op, `recv_of_gt` no longer holds and must be
   restated.

## References

* [ML-KEM Braid] R. Schmidt, *The ML-KEM Braid Protocol*, Rev. 1, last updated 2025-09-26.
  <https://signal.org/docs/specifications/mlkembraid/mlkembraid.pdf>

**Source**: spqr/src/v1/chunked/states.rs:275-533 -/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace spqr.v1.chunked.states

/-- The epoch `States::recv` compares `msg.epoch` against: `state.epoch()` in every arm, which
is the epoch of the state's struct in the unchunked layer (`src/v1/unchunked/`). -/
def States.epochOf : States → Std.U64
  | .KeysUnsampled st | .KeysSampled st | .HeaderSent st | .Ct1Received st
  | .EkSentCt1Received st | .NoHeaderReceived st | .HeaderReceived st | .Ct1Sampled st
  | .EkReceivedCt1Sampled st | .Ct1Acknowledged st | .Ct2Sampled st => st.uc.epoch

private theorem add_one (x : Std.U64) (h : x.val < Std.U64.max) :
    ∃ z, x + 1#u64 = ok z ∧ z.val = x.val + 1 :=
  WP.spec_imp_exists (U64.add_spec (by scalar_tac))

/-- A message from an earlier epoch leaves every state unchanged and emits no key. -/
@[correctness_spec, braid_spec "§2.5"]
theorem recv_of_lt (s : States) (msg : Message) (h : msg.epoch.val < s.epochOf.val) :
    States.recv s msg = ok (.Ok { key := none, state := s }) := by
  cases s <;> simp only [States.epochOf] at h <;> simp only [States.recv,
    send_ek.KeysUnsampled.epoch, send_ek.KeysSampled.epoch, send_ek.HeaderSent.epoch,
    send_ek.Ct1Received.epoch, send_ek.EkSentCt1Received.epoch, send_ct.NoHeaderReceived.epoch,
    send_ct.HeaderReceived.epoch, send_ct.Ct1Sampled.epoch, send_ct.EkReceivedCt1Sampled.epoch,
    send_ct.Ct1Acknowledged.epoch, send_ct.Ct2Sampled.epoch, lift, core.cmp.impls.OrdU64.cmp,
    bind_ok, Nat.compare_eq_lt.2 h]

/-- Let `e` be the epoch of `s`, let `msg.epoch > e`, and if `s` is `Ct2Sampled`, let
`msg.epoch ≠ e + 1`. Then `States.recv s msg` returns `Err(EpochOutOfRange msg.epoch)`.
§2.5 ignores such a message instead. This is deviation D2. -/
theorem recv_of_gt (s : States) (msg : Message) (h : s.epochOf.val < msg.epoch.val)
    (hnext : ∀ st, s = .Ct2Sampled st → msg.epoch.val ≠ st.uc.epoch.val + 1) :
    States.recv s msg = ok (.Err (Error.EpochOutOfRange msg.epoch)) := by
  cases s <;> simp only [States.epochOf] at h
  case Ct2Sampled st =>
    obtain ⟨e1, he1, he1v⟩ := add_one st.uc.epoch (by scalar_tac)
    have hmsg : msg.epoch ≠ e1 := fun heq => hnext st rfl (by rw [heq, he1v])
    simp only [States.recv, send_ct.Ct2Sampled.epoch, lift, core.cmp.impls.OrdU64.cmp,
      bind_ok, Nat.compare_eq_gt.2 h, he1, hmsg, ite_false]
  all_goals simp only [States.recv, send_ek.KeysUnsampled.epoch, send_ek.KeysSampled.epoch,
    send_ek.HeaderSent.epoch, send_ek.Ct1Received.epoch, send_ek.EkSentCt1Received.epoch,
    send_ct.NoHeaderReceived.epoch, send_ct.HeaderReceived.epoch, send_ct.Ct1Sampled.epoch,
    send_ct.EkReceivedCt1Sampled.epoch, send_ct.Ct1Acknowledged.epoch,
    lift, core.cmp.impls.OrdU64.cmp, bind_ok, Nat.compare_eq_gt.2 h]

/-- In `Ct2Sampled`, a message exactly one epoch ahead moves to `KeysUnsampled` at the
message's epoch with the same authenticator and emits no key; the payload is not read. -/
@[correctness_spec, braid_spec "§2.5"]
theorem recv_Ct2Sampled_next_epoch (st : send_ct.Ct2Sampled) (msg : Message)
    (h : msg.epoch.val = st.uc.epoch.val + 1) :
    States.recv (.Ct2Sampled st) msg =
      ok (.Ok { key := none, state := .KeysUnsampled ⟨⟨msg.epoch, st.uc.auth⟩⟩ }) := by
  obtain ⟨e1, he1, he1v⟩ := add_one st.uc.epoch (by scalar_tac)
  obtain rfl : e1 = msg.epoch := UScalar.eq_of_val_eq (by omega)
  simp only [States.recv, send_ct.Ct2Sampled.epoch, lift, core.cmp.impls.OrdU64.cmp, bind_ok,
    Nat.compare_eq_gt.2 (show st.uc.epoch.val < msg.epoch.val by omega), he1, ite_true,
    send_ct.Ct2Sampled.recv_next_epoch, unchunked.send_ct.Ct2Sent.recv_next_epoch, massert]

end spqr.v1.chunked.states
