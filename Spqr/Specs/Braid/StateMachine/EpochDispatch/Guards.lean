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
the cited pages and lines. *Proved* says what the theorems here show. Paths are relative to
`src/`, and line numbers are those of `src/` at `dd8e6b9`.

1. A message from a later epoch.
   * §2.5: every `Receive` function ignores a message with `msg.epoch > e` (for example
     *KeysUnsampled.Receive*, p. 11). The exception is transition (13) in *Ct2Sampled.Receive*
     (p. 23).
   * Code: every arm returns `Err(EpochOutOfRange msg.epoch)` (for example
     `v1/chunked/states.rs:283-285`), except `Ct2Sampled` at `e + 1`
     (`v1/chunked/states.rs:514-526`).
   * Effect: the code reports the message as an error instead of dropping it. The error leaves
     `spqr::recv` at `lib.rs:460` with no updated state and no message key. The serialized state
     that the caller passes in is borrowed and does not change (`lib.rs:355`).
   * Proved: `recv_of_gt`.
2. `Ct1Ack true` in `EkReceivedCt1Sampled`.
   * §2.5: *EkReceivedCt1Sampled.Receive* acts only on `EkCt1Ack` (p. 21), and
     *EkSentCt1Received.Send* sends a message of type `None` (p. 15). §2.3 defines `Ct1Ack`
     (p. 8), but §2.5 never uses it.
   * Code: `EkSentCt1Received` sends `Ct1Ack(true)` (`v1/chunked/states.rs:175-186`), and
     `EkReceivedCt1Sampled` takes transition (12) on it as on `EkCt1Ack`
     (`v1/chunked/states.rs:465-474`). The code gives no reason for this arm. No sender builds
     `Ct1Ack(false)`, and the wire format cannot carry it: the serializer drops the flag
     (`v1/chunked/states/serialize.rs:128`), and the deserializer always gives `Ct1Ack(true)`
     (`v1/chunked/states/serialize.rs:208`). On a message from the state's own epoch,
     `States::recv` ignores `Ct1Ack(false)`.
   * Effect: call the party in `EkReceivedCt1Sampled` the receiver, and the other party the
     peer. Assume two things. First, each party's successful calls form one chain: the state
     that a call gets is the state that the previous successful call of that party returned.
     Second, every message that a party's `recv` gets is the output of the other party's `send`
     in this session. Then this arm is never reached. The peer is in `EkSentCt1Received` only
     after a `Ct2` chunk (`v1/chunked/states.rs:338-344`), which only `Ct2Sampled` sends
     (`v1/chunked/states.rs:267`). So the receiver has reached `Ct2Sampled` at this epoch. No
     transition of `send` or `recv` leads from `Ct2Sampled` back to `EkReceivedCt1Sampled` at the
     same epoch (`v1/chunked/states.rs:115-533`), so by the first assumption the receiver is not
     in `EkReceivedCt1Sampled` when the `Ct1Ack(true)` arrives. A lost `EkCt1Ack` does not need
     the arm either, because the peer sends an `EkCt1Ack` chunk on every call of `send` while it
     is in `Ct1Received` (`v1/chunked/states.rs:162-173`).

     When an assumption does not hold, the arm can be reached. Three examples:
     - (a) The peer, in `Ct1Received`, gets a `Ct2` chunk that the receiver did not send. The
       peer puts this first chunk into a new decoder and checks no MAC or hash on it
       (`v1/chunked/send_ek.rs:165-180`, and §2.5 p. 14). The peer is then in
       `EkSentCt1Received` and sends `Ct1Ack(true)`.
     - (b) The receiver calls `recv` again with its own earlier `EkReceivedCt1Sampled` state of
       this session and epoch, while the peer is in `EkSentCt1Received`. This happens when the
       caller restores an earlier state, or passes one state to two calls: `spqr::send` and
       `spqr::recv` take the serialized state by reference and return a new one (`lib.rs:264`,
       `lib.rs:355`). Neither §2.5 nor the code describes when a caller does this.
     - (c) The receiver gets a `Ct1Ack` message that the peer did not send.

     In (a) and (b), assume also that no message sent before the peer entered
     `EkSentCt1Received` is delivered. Under §2.5, the new messages then move neither party. The
     peer sends messages of type `None` (p. 15). The receiver sends `Ct1` chunks, which
     *EkSentCt1Received.Receive* ignores (p. 15), and waits for `EkCt1Ack` (p. 21). With the
     arm, the receiver takes transition (12) on the peer's `Ct1Ack(true)`. This text does not
     analyze whether the session then completes. In (b), the receiver builds the same `ct2`
     encoder that it built when it first took transition (12) from this state. `send_ct2` calls
     `encaps2` and `mac_ct` (`v1/unchunked/send_ct.rs:177-197`), and neither takes a random
     input (`incremental_mlkem768.rs:71`, `authenticator.rs:66`). `send_ct2_encoder` encodes
     their output (`v1/chunked/send_ct.rs:159-163`). The new encoder starts again at chunk
     index 0 (`encoding/polynomial.rs:709`).

     In this state, anyone who can deliver to the receiver a message with the receiver's
     epoch triggers transition (12) with either type: with `EkCt1Ack` under §2.5, which does not
     read the chunk (p. 21), and also with `Ct1Ack(true)` in the code. This compares one
     transition. It is not a security result.
   * Proved: only the receiving side. `States.Expects` and `specRecvEq` in `Equal.lean` include
     the arm. The claims under *Effect* are not proved.
3. `Ek` in `Ct1Acknowledged`.
   * §2.5: *Ct1Acknowledged.Receive* acts only on `EkCt1Ack` (pp. 21-22).
   * Code: `Ek` chunks go to the same decoder as `EkCt1Ack` chunks. When the decoder completes,
     the code runs the check of transition (11). When the check passes, it takes the step of
     (11) (`v1/chunked/states.rs:486-507`). The comment at `v1/chunked/states.rs:486-489` gives
     the reason: messages can arrive out of order.
   * Effect: the receiver is in `Ct1Acknowledged` after an `EkCt1Ack` chunk that did not
     complete its decoder (transition (8)). Make the two assumptions of Deviation 2, so that
     the `EkCt1Ack` chunk and a later `Ek` chunk both come from the peer's `send` in this
     session and epoch. The peer sends `Ek` chunks in `HeaderSent` and `EkCt1Ack` chunks in
     `Ct1Received` (`v1/chunked/states.rs:150-173`), and it enters `Ct1Received` after
     `HeaderSent`. So the peer sent the `Ek` chunk before the `EkCt1Ack` chunk, which arrived
     first. Both payloads come from one encoder, because `v1/chunked/send_ek.rs:141` moves
     `HeaderSent.sending_ek` into `Ct1Received`. So the late chunk is a chunk of the same
     encoding.

     §2.5 drops the late chunk. Its decoder keeps the chunks received in `Ct1Sampled`
     (transition (8), p. 20), and in `Ct1Acknowledged` it adds only `EkCt1Ack` chunks
     (pp. 21-22). The code also adds the late `Ek` chunk. When that chunk has an index that the
     decoder lacks, the code can complete `ek` with fewer `EkCt1Ack` chunks than §2.5 needs.
     The code also adds an `Ek` chunk that the peer did not send, which §2.5 ignores. If the
     decoder then completes with a key that fails the check, `recv` returns `Err` on the call
     that completes it.
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
