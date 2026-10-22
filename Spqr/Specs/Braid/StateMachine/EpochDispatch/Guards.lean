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
The three are the only differences in state names, key presence and `Ok`/`Err`, for calls that
return, with the code's decoder and checks taken as the spec's (`Equal.lean` explains why).

For each deviation, *§2.5* and *Code* say what the sources do. *Effect* is our reasoning from
the cited pages and lines. *Proved* says what the theorems here show.

1. A message from a later epoch.
   * §2.5: every `Receive` function ignores a message with `msg.epoch > e` (for example
     *KeysUnsampled.Receive*, p. 11). The exception is transition (13) in *Ct2Sampled.Receive*
     (p. 23).
   * Code: every arm returns `Err(EpochOutOfRange msg.epoch)` (for example `states.rs:283-285`),
     except `Ct2Sampled` at `e + 1` (`states.rs:514-526`).
   * Effect: the code reports the message as an error instead of dropping it. The error leaves
     `spqr::recv` at `lib.rs:460` with no updated state and no message key. The serialized state
     that the caller passes in is borrowed and does not change (`lib.rs:355`).
   * Proved: `recv_of_gt`.
2. `Ct1Ack true` in `EkReceivedCt1Sampled`.
   * §2.5: *EkReceivedCt1Sampled.Receive* acts only on `EkCt1Ack` (p. 21), and
     *EkSentCt1Received.Send* sends `None` (p. 15). §2.3 defines `Ct1Ack` (p. 8), but §2.5
     never uses it.
   * Code: `EkSentCt1Received` sends `Ct1Ack(true)` (`states.rs:175-186`), and
     `EkReceivedCt1Sampled` takes transition (12) on it as on `EkCt1Ack` (`states.rs:465-474`).
     The code gives no reason for this arm. The code sends only `Ct1Ack(true)`, and the wire
     decoder produces only `Ct1Ack(true)` (`states/serialize.rs:208`). In the model,
     `Ct1Ack false` is a no-op.
   * Effect: assume that both parties only move forward, and that the other party in this
     session generated every message that `recv` gets. Then this arm is never reached. The peer
     is in `EkSentCt1Received` only after a `Ct2` chunk (`states.rs:338-344`), which only
     `Ct2Sampled` sends (`states.rs:267`), so the receiver has already left
     `EkReceivedCt1Sampled`. A lost `EkCt1Ack` does not need the arm either, because
     `Ct1Received` keeps sending `EkCt1Ack` chunks (`states.rs:170`).

     The arm is reached in two other cases. In case (a), `recv` gets a `Ct2` chunk that the
     other party did not generate. The first `Ct2` chunk goes to a new decoder with no check
     (`send_ek.rs:165-180`, and §2.5 p. 14). In case (b), the receiver restores its own earlier
     `EkReceivedCt1Sampled` state of this session and epoch while the peer is in
     `EkSentCt1Received`. Neither §2.5 nor the code describes when a party restores an earlier
     state.

     In both cases, assume that no earlier message is delivered. Under §2.5, the new messages
     then move neither party: the peer sends `None`, and the receiver waits for `EkCt1Ack`. With
     the arm, the receiver takes transition (12). In case (b), it rebuilds the encoder that it
     had before, because `send_ct2` calls `encaps2` and `mac_ct` with no random input
     (`unchunked/send_ct.rs:177-197`, `incremental_mlkem768.rs:71`, `send_ct.rs:159-163`). The
     new encoder sends the same chunks again from the first one (`polynomial.rs:708`).

     In this state, a party that can deliver an equal-epoch message triggers transition (12)
     with either type: with `EkCt1Ack` under §2.5, which does not read the chunk (p. 21), and
     also with `Ct1Ack(true)` in the code. This compares one transition. It is not a security
     result.
   * Proved: only the receiving side. `States.Expects` and `specRecvEq` in `Equal.lean` include
     the arm. The claims under *Effect* are not proved.
3. `Ek` in `Ct1Acknowledged`.
   * §2.5: *Ct1Acknowledged.Receive* acts only on `EkCt1Ack` (pp. 21-22).
   * Code: `Ek` chunks go to the same decoder as `EkCt1Ack` chunks. When the decoder completes,
     the code runs the check of transition (11). When the check passes, it takes the step of
     (11) (`states.rs:486-507`). The comment at `states.rs:486-489` gives the reason: messages
     can arrive out of order.
   * Effect: an `Ek` chunk reaches this state when it arrives after the first `EkCt1Ack` chunk.
     For chunks that the peer generated, both payloads come from one encoder, because
     `send_ek.rs:141` moves `HeaderSent.sending_ek` into `Ct1Received`. So the late chunk is a
     point of the same encoding. §2.5 drops it. §2.5 completes `ek` when enough distinct
     `EkCt1Ack` chunks arrive, and the peer must go on sending them for that
     (`states.rs:162-173`). The code also uses the late chunk, so it can complete `ek` with
     fewer messages. A chunk that the peer did not generate also goes to the decoder. When the
     completed key then fails the check, `recv` returns `Err`, where §2.5 ignores the chunk.
   * Proved: `States.Expects` and `specRecvEq` in `Equal.lean` include the arm. The claims under
     *Effect* are not proved.

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
