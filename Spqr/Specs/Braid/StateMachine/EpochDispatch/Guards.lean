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
carry its tag. `recv_of_gt` does not, because it states Deviation 1 below.

## Deviations from §2.5

On the receive path, the code differs from §2.5 in three places, numbered here and in
`Equal.lean`. Each deviation is marked "Deviation n" where it takes effect. The theorems state
what the code does. If the code changes to follow the spec, the marked statements must change.

1. A message from a later epoch (this module, `recv_of_gt`). In §2.5 every `Receive` function
   ignores a message with `msg.epoch > e` (for example *KeysUnsampled.Receive*, p. 11), apart
   from transition (13) (p. 23). The code returns `Err(EpochOutOfRange msg.epoch)` instead, in
   every arm (for example `states.rs:283-285`; the exception is `states.rs:514-526`), so it is
   stricter than the spec: the message is reported as an error instead of being dropped.
2. `Ct1Ack true` in `EkReceivedCt1Sampled` (`Equal.lean`, `States.Expects` and `specRecvEq`).
   §2.5 acts only on `EkCt1Ack` in this state (*EkReceivedCt1Sampled.Receive*, p. 21). The code
   also takes transition (12) on `Ct1Ack true` (`states.rs:465-474`), which the peer sends from
   `EkSentCt1Received` (`states.rs:175-186`) where §2.5 sends nothing
   (*EkSentCt1Received.Send*, p. 15). §2.3 defines `Ct1Ack`, but §2.5 never uses it.
   When both parties follow the protocol, this arm is never reached: the peer is in
   `EkSentCt1Received` only after a `Ct2` chunk (`states.rs:338-344`), which is sent only from
   `Ct2Sampled` (`states.rs:267`), so the receiver has already left `EkReceivedCt1Sampled`. A
   lost `EkCt1Ack` needs no extra message, because `Ct1Received` keeps sending `EkCt1Ack`
   chunks (`states.rs:170`). An injected `Ct1Ack true` takes the same transition that an
   injected `EkCt1Ack` takes in §2.5, which does not read the chunk. Neither claim is proved
   here. `Equal.lean` covers only the receiving side. `Ct1Ack false` is never sent and stays a
   no-op.
3. `Ek` in `Ct1Acknowledged` (`Equal.lean`, `States.Expects` and `specRecvEq`). §2.5 acts only
   on `EkCt1Ack` in this state (*Ct1Acknowledged.Receive*, pp. 21-22). The code also feeds `Ek`
   chunks to the same decoder, for out-of-order delivery, and checks the completed key against
   the header as in transition (11) (`states.rs:486-507`).

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
