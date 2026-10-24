/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Lacramioara Astefanoaei
-/
module

public import SrcTranslated.Funs
public meta import Spqr.Auxiliary.SpecTags
public import Spqr.Auxiliary.Aeneas.SpecImpExists

/-! # `States::recv` on a message from another epoch

Let `e = States.epochOf s` be the epoch of the state `s`. Every arm of `States::recv` first
compares `msg.epoch` with `e`. When `msg.epoch ≠ e`, the arm decides without reading the payload:

* `recv_of_lt`: if `msg.epoch < e`, the state is unchanged and no key is emitted.
* `recv_of_gt`: if `msg.epoch > e`, the result is `Err(EpochOutOfRange msg.epoch)`, except in
  `Ct2Sampled` with `msg.epoch = e + 1`.
* `recv_Ct2Sampled_next_epoch`: in that exception the state becomes `KeysUnsampled` at epoch
  `e + 1` with the same authenticator, and no key is emitted. This is transition (13) of
  [ML-KEM Braid] §2.5 (p. 23).

All three theorems are total. `recv_of_lt` and `recv_Ct2Sampled_next_epoch` agree with §2.5 and
carry its tag. `recv_of_gt` states Deviation 1 and does not.

## Deviations from §2.5

`States::recv` differs from §2.5 in three places. The theorems state what the code does, and
each place is marked "Deviation n". With `Equal.lean`, they show that these are the only
differences in the next state's name, key presence and `Ok`/`Err`. This holds for calls that
return, with the code's decoder and checks taken as the spec's, and with `specRecvEq` taken as
a faithful reading of §2.5 (see `Equal.lean`).

1. A message from a later epoch, except in `Ct2Sampled` at `e + 1`. See below.
2. `Ct1Ack true` in `EkReceivedCt1Sampled` takes transition (12). See `Equal.lean`.
3. An `Ek` chunk in `Ct1Acknowledged` goes to the `ek` decoder. See `Equal.lean`.

Each deviation has four parts. *§2.5* and *Code* say what the sources do. *Effect* is our
reasoning from the cited pages and lines, and is not proved. *Proved* says what the theorems
show. Paths are relative to `src/` at `dd8e6b9`.

### Deviation 1: a message from a later epoch

* §2.5: every `Receive` function ignores a message with `msg.epoch > e`, for example
  *KeysUnsampled.Receive* (p. 11). The exception is transition (13) (p. 23).
* Code: every arm returns `Err(EpochOutOfRange msg.epoch)`, for example
  `v1/chunked/states.rs:283-285`. The exception is at `v1/chunked/states.rs:514-526`.
  `spqr::recv` returns the error at `lib.rs:460` with no new state and no key. The caller's
  serialized state is borrowed and does not change (`lib.rs:355`).
* Effect: the code reports the message as an error, where §2.5 drops it.
* Proved: `recv_of_gt`. What `spqr::recv` does with the error is read from the code and is not
  proved.

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
§2.5 ignores such a message instead: Deviation 1 in the module doc. -/
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
