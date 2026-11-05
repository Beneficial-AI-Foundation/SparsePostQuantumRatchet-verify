/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Lacramioara Astefanoaei
-/
module

/-! # Where the code differs from ML-KEM Braid §2.5

The chunked state machine of `src/v1/chunked/states.rs` differs from [ML-KEM Braid] §2.5 in three
places. Each is a constructor of `Braid.Deviation`, and its docstring says what the two sources do.
A declaration that states a deviation, or follows the code at one, carries
`@[braid_deviation Braid.Deviation.x]` (`Spqr/Auxiliary/SpecTags.lean`). Lean checks that the
argument names a constructor. Comments on the arms of a `match` name the constructor in the same
way, for example `-- Deviation.lateEkChunk`.

Two modules use them. `StateMachine/EpochDispatch.lean` compares `States::recv` with §2.5 at the
level of state names. Its `specRecvEq` and `States.Expects` include `ct1AckAccepted` and
`lateEkChunk`, and `recv_of_gt` states `futureEpochError`. `StateMachine/Model.lean` is an
abstract §2.5 machine whose `send`, `receiveEq` and `receive` follow the code at all three, so
that the refinement theorems of `StateMachine/Refinement.lean` hold.

The docstring of each deviation has four parts. *§2.5* and *Code* say what the sources do.
*Effect* is our reasoning from the cited pages and lines, and is not proved. *Proved* says what
the theorems of `EpochDispatch.lean` show. In these docstrings, paths are relative to `src/` at
`dd8e6b9`. Call the party that runs
`recv` the receiver, and the other party the peer. A *normal run* satisfies three conditions:

1. The parties start in the states that `init_a` and `init_b` return
   (`v1/chunked/states.rs:58-64`), as *InitAlice* and *InitBob* of §2.6 do (p. 23).
2. Each party's successful calls form one chain: a call gets the state that the previous
   successful call of that party returned.
3. Every message that a party's `recv` gets is the output of the other party's `send` in this
   session, possibly out of order.

## References

* [ML-KEM Braid] R. Schmidt, *The ML-KEM Braid Protocol*, Rev. 1, last updated 2025-09-26.
  <https://signal.org/docs/specifications/mlkembraid/mlkembraid.pdf>

**Source**: spqr/src/v1/chunked/states.rs:115-533 -/

@[expose] public section

namespace Braid

/-- A place where the chunked state machine differs from ML-KEM Braid §2.5. -/
inductive Deviation where
  /-- A message from a later epoch, except in `Ct2Sampled` at `e + 1`.

* §2.5: every `Receive` function ignores a message with `msg.epoch > e`, for example
  *KeysUnsampled.Receive* (p. 11). The exception is transition (13) (p. 23).
* Code: every arm returns `Err(EpochOutOfRange msg.epoch)`, for example
  `v1/chunked/states.rs:283-285`. The exception is at `v1/chunked/states.rs:514-526`.
  `spqr::recv` returns the error at `lib.rs:460` with no new state and no key. The caller's
  serialized state is borrowed and does not change (`lib.rs:355`).
* Effect: the code reports the message as an error, where §2.5 drops it.
* Proved: `recv_of_gt`. What `spqr::recv` does with the error is read from the code and is not
  proved. -/
  | futureEpochError
  /-- `Ct1Ack true` in `EkReceivedCt1Sampled` takes transition (12).

* §2.5: *EkReceivedCt1Sampled.Receive* acts only on `EkCt1Ack` (p. 21), and
  *EkSentCt1Received.Send* sends a message of type `None` (p. 15). §2.3 defines `Ct1Ack`
  (p. 8), but §2.5 does not use it.
* Code: `EkSentCt1Received` sends `Ct1Ack(true)` (`v1/chunked/states.rs:175-186`), and
  `EkReceivedCt1Sampled` takes transition (12) on it (`v1/chunked/states.rs:465-474`). The code
  gives no reason. No sender builds `Ct1Ack(false)`, and the wire format cannot carry it: the
  serializer drops the flag (`v1/chunked/states/serialize.rs:128`), and the deserializer always
  gives `Ct1Ack(true)` (`v1/chunked/states/serialize.rs:208`).
* Effect: in a normal run the arm is never reached. The peer enters `EkSentCt1Received` only on
  a `Ct2` chunk (`v1/chunked/states.rs:338-344`), and only `Ct2Sampled` sends one
  (`v1/chunked/states.rs:267`). No transition leads from `Ct2Sampled` back to
  `EkReceivedCt1Sampled` at the same epoch. A lost `EkCt1Ack` does not need the arm either,
  because `Ct1Received` sends an `EkCt1Ack` chunk on every `send`
  (`v1/chunked/states.rs:162-173`).

  Outside a normal run the arm can be reached. Three examples:
  - (a) The peer, in `Ct1Received`, gets a `Ct2` chunk that the receiver did not send. The peer
    checks no MAC or hash on this first chunk (`v1/chunked/send_ek.rs:165-180`, §2.5 p. 14).
    It enters `EkSentCt1Received` and sends `Ct1Ack(true)`.
  - (b) The receiver calls `recv` again with its earlier `EkReceivedCt1Sampled` state, while
    the peer is in `EkSentCt1Received`. A caller can do this because `spqr::send` and
    `spqr::recv` take the serialized state by reference (`lib.rs:264`, `lib.rs:355`).
  - (c) The receiver gets a `Ct1Ack` message that the peer did not send.

  In (a) and (b), assume also that no older message arrives. Then §2.5 stalls: the peer sends
  `None`, and the receiver sends `Ct1` chunks, which the peer ignores (p. 15), and waits for
  `EkCt1Ack` (p. 21). The code takes transition (12) instead. Whether the session then completes
  is not analyzed. In (b), the new `ct2` encoder equals the first one, because `encaps2` and
  `mac_ct` take no random input (`v1/unchunked/send_ct.rs:177-197`, `incremental_mlkem768.rs:71`,
  `authenticator.rs:66`). It starts again at chunk index 0 (`encoding/polynomial.rs:709`).

  §2.5 also takes transition (12) on any `EkCt1Ack` message with the receiver's epoch, without
  reading its chunk (p. 21). This compares one transition. It is not a security result.
* Proved: if a `Ct1Ack true` message has the receiver's epoch and `States.recv` on
  `EkReceivedCt1Sampled` returns, then by `recv_of_eq_refines` it returns `Ok` with next state
  `Ct2Sampled` and no key. The theorems do not cover `send` or runs, so the claim that the arm is
  never reached is not proved. -/
  | ct1AckAccepted
  /-- An `Ek` chunk in `Ct1Acknowledged` goes to the `ek` decoder.

* §2.5: *Ct1Acknowledged.Receive* acts only on `EkCt1Ack` (pp. 21-22).
* Code: `Ek` chunks go to the same decoder as `EkCt1Ack` chunks. When the decoder completes,
  the code runs the check of transition (11), and if the check passes, it takes the step of
  (11) (`v1/chunked/states.rs:486-507`). The comment at `v1/chunked/states.rs:486-489` gives
  the reason: messages can arrive out of order.
* Effect: the receiver is in `Ct1Acknowledged` after an `EkCt1Ack` chunk that did not complete
  its decoder (transition (8)). In a normal run, an `Ek` chunk that arrives now was sent before
  that `EkCt1Ack` chunk, because it sends `Ek` chunks in `HeaderSent` and then `EkCt1Ack` chunks in
  `Ct1Received` (`v1/chunked/states.rs:150-173`). Both come from one encoder, which
  `v1/chunked/send_ek.rs:141` moves from `HeaderSent` into `Ct1Received`. §2.5 drops the late
  chunk: its decoder keeps the chunks from `Ct1Sampled` (p. 20) and then adds only `EkCt1Ack`
  chunks (pp. 21-22). The code adds it. If the late chunk has an index that the decoder lacks,
  the code can complete `ek` with fewer `EkCt1Ack` chunks than §2.5 needs. Outside a normal
  run, the code also adds an `Ek` chunk that the peer did not send. If the decoder then
  completes with a key that fails the check, `recv` returns `Err`.
* Proved: `recv_of_eq_refines` on `Ct1Acknowledged` and an `Ek` message with the receiver's epoch,
  if `States.recv` returns. If no message completes the decoder, the next state is named
  `Ct1Acknowledged`. If the completed message passes `ek_matches_header`, the next state is named
  `Ct2Sampled` and no key is emitted. If it does not pass, the result is `Err`. The claims under
  *Effect* are not proved. -/
  | lateEkChunk

end Braid
