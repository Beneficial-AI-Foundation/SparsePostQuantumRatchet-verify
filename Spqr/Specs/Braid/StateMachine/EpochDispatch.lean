/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Lacramioara Astefanoaei
-/
module

public import SrcTranslated.Funs
public meta import Spqr.Auxiliary.SpecTags
public import Spqr.Auxiliary.Aeneas.Result
public import Spqr.Auxiliary.Aeneas.SpecImpExists

/-! # `States::recv` against ML-KEM Braid §2.5

The module is about the call `States.recv s msg`. Its parameters are the receiver's state
`s : States` and the received message `msg : Message`, with epoch `msg.epoch` and payload
`msg.payload : MessagePayload`. If the call returns `Ok`, the result is `Ok ⟨key, s'⟩`, with next
state `s'` and an optional key `key`. Let `e = States.epochOf s`. Every arm of `States::recv`
first compares `msg.epoch` with `e`. The module compares the result with the `Receive` functions
of [ML-KEM Braid] §2.5. Transitions are numbered as in §2.5, Fig. 1 (p. 10).

## Messages from another epoch

When `msg.epoch ≠ e`, the arm decides without reading the payload.

* If `msg.epoch < e`, the state is unchanged and no key is emitted (`recv_of_lt`).
* If `msg.epoch > e`, the result is `Err(EpochOutOfRange msg.epoch)`, except in `Ct2Sampled`
  with `msg.epoch = e + 1` (`recv_of_gt`).
* If `s` is `Ct2Sampled` and `msg.epoch = e + 1`, the state becomes `KeysUnsampled` at epoch
  `e + 1` with the same authenticator, and no key is emitted (`recv_Ct2Sampled_next_epoch`).
  This is transition (13) of §2.5 (p. 23).

All three theorems are total. `recv_of_lt` and `recv_Ct2Sampled_next_epoch` agree with §2.5, so
they carry the attributes `correctness_spec` and `braid_spec "§2.5"`. `recv_of_gt` states
Deviation `future-epoch-error`, where the code differs from §2.5, so it carries neither
attribute.

## Messages from the state's own epoch

`States.Expects s p` holds for the pairs of a state `s` and a payload `p` that `States::recv`
acts on. In eight of the eleven states, some payload satisfies it. In `KeysUnsampled`,
`HeaderReceived` and `Ct2Sampled`, no payload does.

* If `msg.epoch = e` and `¬ States.Expects s msg.payload`, then `States.recv s msg` returns
  `Ok ⟨none, s⟩`: the state is unchanged and no key is emitted (`recv_of_eq_unexpected`). The
  theorem is total.
* If `msg.epoch = e` and `States.recv s msg` returns `Ok`, the next state's name and key
  presence are the ones `specRecvEq s msg.payload` gives. If the call returns, it returns `Err`
  exactly when `specRecvEq s msg.payload` is `none` (`recv_of_eq_refines`).

`specRecvEq` is the §2.5 `Receive` at the level of state names and key presence, plus Deviations
`ct1ack-accepted` and `late-ek-chunk`. When a chunk completes a decoder, it takes the transition if
the state's check passes on the completed message (`States.Accepts`), and it is `none` if the check
fails (`States.Rejects`). The decoder and the checks are the code's calls: `add_chunk` and
`decoded_message` for the decoder, `recv_ct2` for `Decaps`, `KDF_OK`, `Update` and `VfyCt`,
`verify_hdr` for `VfyHdr`, and `ek_matches_header` for `SHA3-256(ek_seed || ek_vector) = hek`.
`HeaderSent` has no check. That `specRecvEq` follows §2.5 is our reading of §2.5, not a theorem.

## What the theorems do not show

* `recv_of_eq_refines` holds only for calls that return. It is not total because some handlers
  panic when state fields have the wrong size, for example transition (2) at
  `src/v1/chunked/send_ek.rs:91-92` and transition (12) at `src/incremental_mlkem768.rs:75-76`.
  Ruling this out needs state invariants and specifications of the opaque libcrux calls.
* `States.Accepts s p` and `States.Rejects s p` hold only if the chunk in `p` completes the decoder
  of `s`. Transitions (3), (5), (6), (9), (10) and (11), and Deviation `late-ek-chunk`, need one of
  them. For these pairs of state and payload, if the chunk does not complete the decoder,
  `recv_of_eq_refines` says only that the state keeps its name. The exception is `Ct1Sampled` on
  `EkCt1Ack`, which takes transition (8). That the peer's chunks complete the decoder after enough
  calls is not proved. So `recv_of_eq_refines` also holds for a run in which the decoder never
  completes and none of these transitions occurs.
* That the code's decoder and checks compute the spec's decoder and checks is not proved. For
  the `ek` check, the model of `validate_pk_bytes` differs from the spec (see
  `States.CheckPasses`).
* `recv_of_eq_refines` compares the next state's name and key presence, not the next state's
  fields or the key's value. `recv_of_eq_unexpected` states the whole next state.

## Deviations from §2.5

`States::recv` differs from §2.5 in three places. The theorems state what the code does, and each
place is marked with the deviation's name, for example "Deviation `future-epoch-error`". The five
theorems cover every value of `msg.epoch` relative to `e`. In each case they give the code's next
state name, key presence and `Ok`/`Err`. We compare these with §2.5 by reading it: by hand for
`msg.epoch ≠ e`, and through `specRecvEq` for `msg.epoch = e`, whose arms we read as §2.5 plus
Deviations `ct1ack-accepted` and `late-ek-chunk`. Under this reading, the three deviations are the
only differences. This holds for calls that return, with the code's decoder and checks taken as
the spec's.

* `future-epoch-error`: a message from a later epoch, except in `Ct2Sampled` at `e + 1`.
* `ct1ack-accepted`: `Ct1Ack true` in `EkReceivedCt1Sampled` takes transition (12).
* `late-ek-chunk`: an `Ek` chunk in `Ct1Acknowledged` goes to the `ek` decoder.

Each deviation has four parts. *§2.5* and *Code* say what the sources do. *Effect* is our
reasoning from the cited pages and lines, and is not proved. *Proved* says what the theorems
show. In this section, paths are relative to `src/` at `dd8e6b9`. Call the party that runs
`recv` the receiver, and the other party the peer. A *normal run* satisfies three conditions:

1. The parties start in the states that `init_a` and `init_b` return
   (`v1/chunked/states.rs:58-64`), as *InitAlice* and *InitBob* of §2.6 do (p. 23).
2. Each party's successful calls form one chain: a call gets the state that the previous
   successful call of that party returned.
3. Every message that a party's `recv` gets is the output of the other party's `send` in this
   session, possibly out of order.

### Deviation `future-epoch-error`: a message from a later epoch

* §2.5: every `Receive` function ignores a message with `msg.epoch > e`, for example
  *KeysUnsampled.Receive* (p. 11). The exception is transition (13) (p. 23).
* Code: every arm returns `Err(EpochOutOfRange msg.epoch)`, for example
  `v1/chunked/states.rs:283-285`. The exception is at `v1/chunked/states.rs:514-526`.
  `spqr::recv` returns the error at `lib.rs:460` with no new state and no key. The caller's
  serialized state is borrowed and does not change (`lib.rs:355`).
* Effect: the code reports the message as an error, where §2.5 drops it.
* Proved: `recv_of_gt`. What `spqr::recv` does with the error is read from the code and is not
  proved.

### Deviation `ct1ack-accepted`: `Ct1Ack true` in `EkReceivedCt1Sampled`

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
  never reached is not proved.

### Deviation `late-ek-chunk`: an `Ek` chunk in `Ct1Acknowledged`

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
  *Effect* are not proved.

## References

* [ML-KEM Braid] R. Schmidt, *The ML-KEM Braid Protocol*, Rev. 1, last updated 2025-09-26.
  <https://signal.org/docs/specifications/mlkembraid/mlkembraid.pdf>

**Source**: spqr/src/v1/chunked/states.rs:275-533, spqr/src/v1/chunked/send_ek.rs,
spqr/src/v1/chunked/send_ct.rs -/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace spqr.v1.chunked.states

/-! ## Messages from another epoch -/

/-- The epoch `States::recv` compares `msg.epoch` against: `state.epoch()` in every arm, which
is the epoch of the state's struct in the unchunked layer (`src/v1/unchunked/`). -/
def States.epochOf : States → Std.U64
  | .KeysUnsampled st | .KeysSampled st | .HeaderSent st | .Ct1Received st
  | .EkSentCt1Received st | .NoHeaderReceived st | .HeaderReceived st | .Ct1Sampled st
  | .EkReceivedCt1Sampled st | .Ct1Acknowledged st | .Ct2Sampled st => st.uc.epoch

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
§2.5 ignores such a message instead: Deviation `future-epoch-error` in the module doc. -/
theorem recv_of_gt (s : States) (msg : Message) (h : s.epochOf.val < msg.epoch.val)
    (hnext : ∀ st, s = .Ct2Sampled st → msg.epoch.val ≠ st.uc.epoch.val + 1) :
    States.recv s msg = ok (.Err (Error.EpochOutOfRange msg.epoch)) := by
  cases s <;> simp only [States.epochOf] at h
  case Ct2Sampled st =>
    obtain ⟨e1, he1, he1v⟩ :=
      WP.spec_imp_exists (U64.add_spec (x := st.uc.epoch) (y := 1#u64) (by scalar_tac))
    simp only [UScalar.ofNatCore_val_eq] at he1v
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
  obtain ⟨e1, he1, he1v⟩ :=
    WP.spec_imp_exists (U64.add_spec (x := st.uc.epoch) (y := 1#u64) (by scalar_tac))
  simp only [UScalar.ofNatCore_val_eq] at he1v
  obtain rfl : e1 = msg.epoch := UScalar.eq_of_val_eq (by omega)
  simp only [States.recv, send_ct.Ct2Sampled.epoch, lift, core.cmp.impls.OrdU64.cmp, bind_ok,
    Nat.compare_eq_gt.2 (show st.uc.epoch.val < msg.epoch.val by omega), he1, ite_true,
    send_ct.Ct2Sampled.recv_next_epoch, unchunked.send_ct.Ct2Sent.recv_next_epoch, massert]

/-! ## Messages from the state's own epoch -/

/-- `s.Expects p` holds when `States::recv` in state `s` acts on payload `p` of a message from
the epoch of `s`. The pairs are those that pass a `msg.type ==` test of a `Receive` function in
ML-KEM Braid §2.5, plus `Ct1Ack true` in `EkReceivedCt1Sampled` (`ct1ack-accepted`) and `Ek` in
`Ct1Acknowledged` (`late-ek-chunk`). -/
def States.Expects : States → MessagePayload → Prop
  | .KeysSampled _, .Ct1 _ => True
  | .HeaderSent _, .Ct1 _ => True
  | .Ct1Received _, .Ct2 _ => True
  | .EkSentCt1Received _, .Ct2 _ => True
  | .NoHeaderReceived _, .Hdr _ => True
  | .Ct1Sampled _, .Ek _ => True
  | .Ct1Sampled _, .EkCt1Ack _ => True
  | .EkReceivedCt1Sampled _, .EkCt1Ack _ => True
  | .EkReceivedCt1Sampled _, .Ct1Ack true => True  -- deviation ct1ack-accepted
  | .Ct1Acknowledged _, .EkCt1Ack _ => True
  | .Ct1Acknowledged _, .Ek _ => True              -- deviation late-ek-chunk
  | _, _ => False

/-- `decodes d c m` holds when chunk `c` completes decoder `d` with message `m`: the code's
`add_chunk d c` gives a decoder `d'`, and `decoded_message d'` gives `some m`. These calls have
the role of the spec's `decoder.add_chunk(msg.data)`, `decoder.has_message()` and
`decoder.message()`. That they compute the spec's decoder is not proved here. `decodes d c m`
does not require that `d` had no message before `c`. -/
def decodes (d : encoding.polynomial.PolyDecoder) (c : encoding.Chunk)
    (m : alloc.vec.Vec Std.U8) : Prop :=
  ∃ d', encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk d c = ok d' ∧
    encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.decoded_message d' = ok (some m)

/-- `s.Decodes p m` holds when payload `p` carries a chunk that completes, with message `m`,
the decoder that state `s` feeds it to. The pairs of `s` and `p` are `HeaderSent` on `Ct1`,
`EkSentCt1Received` on `Ct2`, `NoHeaderReceived` on `Hdr`, and `Ct1Sampled` and
`Ct1Acknowledged` on `Ek` and `EkCt1Ack`. On every other pair this is `False`. -/
def States.Decodes : States → MessagePayload → alloc.vec.Vec Std.U8 → Prop
  | .HeaderSent st, .Ct1 c, m => decodes st.receiving_ct1 c m
  | .EkSentCt1Received st, .Ct2 c, m => decodes st.receiving_ct2 c m
  | .NoHeaderReceived st, .Hdr c, m => decodes st.receiving_hdr c m
  | .Ct1Sampled st, .Ek c, m => decodes st.receiving_ek c m
  | .Ct1Sampled st, .EkCt1Ack c, m => decodes st.receiving_ek c m
  | .Ct1Acknowledged st, .Ek c, m => decodes st.receiving_ek c m
  | .Ct1Acknowledged st, .EkCt1Ack c, m => decodes st.receiving_ek c m
  | _, _, _ => False

/-- `s.CheckPasses m` holds when the code's check of state `s` on a completed message `m`
returns without panicking and passes. Write
`m[..i]` for the first `i` bytes of `m` and `m[i..]` for the rest.

* `EkSentCt1Received`: `recv_ct2` on ciphertext `m[..i]` and MAC `m[i..]`, with
  `i = CIPHERTEXT2_SIZE`, gives `Ok`. It has the role of the spec's `Decaps`, `KDF_OK`,
  `Update` and `VfyCt` (§2.5 p. 15). That it computes these is not proved here. Its only inner
  error is the one `verify_ct` returns.
* `NoHeaderReceived`: `verify_hdr` on header `m[..i]` and MAC `m[i..]`, with `i = HEADER_SIZE`,
  gives `Ok`. It has the role of the spec's `VfyHdr` (§2.5 p. 17). That it computes `VfyHdr` is
  not proved here.
* `Ct1Sampled` and `Ct1Acknowledged`: `ek_matches_header m hdr` gives `true`, where `hdr` is
  the header that the state stores. It has the role of the spec's
  `SHA3-256(ek_seed || ek_vector) = hek` (§2.5 pp. 19, 22). It calls libcrux
  `validate_pk_bytes` (`src/incremental_mlkem768.rs:28-29`). The model of `validate_pk_bytes` in
  `SrcTranslated/FunsExternal.lean` differs from the spec's check in two ways. It hashes
  `ek_vector || ek_seed`, the order of FIPS 203, and it also checks the input lengths and that
  `ek_vector` is a canonical encoding (`Fips203.Refinement.pk2Valid`).
* Every other state: `True`. In particular, `HeaderSent` takes transition (3) without a check. -/
def States.CheckPasses : States → alloc.vec.Vec Std.U8 → Prop
  | .EkSentCt1Received st, m =>
      ∃ (i : Std.Usize) (ct2 mac : alloc.vec.Vec Std.U8)
          (v : v1.unchunked.send_ct.NoHeaderReceived × EpochSecret),
        incremental_mlkem768.CIPHERTEXT2_SIZE = ok i ∧
        ct2.val = m.val.take i.val ∧ mac.val = m.val.drop i.val ∧
        v1.unchunked.send_ek.EkSentCt1Received.recv_ct2 st.uc ct2 mac = ok (.Ok v)
  | .NoHeaderReceived st, m =>
      ∃ (i : Std.Usize) (hdr mac : alloc.vec.Vec Std.U8), incremental_mlkem768.HEADER_SIZE = ok i ∧
        hdr.val = m.val.take i.val ∧ mac.val = m.val.drop i.val ∧
        authenticator.Authenticator.verify_hdr st.uc.auth st.uc.epoch
          (alloc.vec.Vec.deref hdr) (alloc.vec.Vec.deref mac) = ok (.Ok ())
  | .Ct1Sampled st, m => incremental_mlkem768.ek_matches_header m st.uc.hdr = ok true
  | .Ct1Acknowledged st, m => incremental_mlkem768.ek_matches_header m st.uc.hdr = ok true
  | _, _ => True

/-- `s.Accepts p` holds when the chunk in payload `p` completes the decoder of state `s` with
some message `m` (`s.Decodes p m`), and `m` passes the code's check (`s.CheckPasses m`). Then
`specRecvEq s p` takes the numbered transition of `s` on `p`. -/
def States.Accepts (s : States) (p : MessagePayload) : Prop :=
  ∃ m, s.Decodes p m ∧ s.CheckPasses m

/-- `s.Rejects p` holds when the chunk in payload `p` completes the decoder of state `s` with
some message `m`, and `m` does not pass the code's check. Then `specRecvEq s p` is `none`, at
the place of the spec's `raise` or `FAIL`. This does not say that the spec's check fails on `m`:
the code's check can differ from it (see `States.CheckPasses`). Not passing includes the check
call panicking (for example, the epoch increment in `recv_ct2` at `U64.max`). -/
def States.Rejects (s : States) (p : MessagePayload) : Prop :=
  ∃ m, s.Decodes p m ∧ ¬ s.CheckPasses m

/-- The state names of ML-KEM Braid §2.5, the abstraction the comparison is made at. -/
inductive SpecState where
  | KeysUnsampled | KeysSampled | HeaderSent | Ct1Received | EkSentCt1Received
  | NoHeaderReceived | HeaderReceived | Ct1Sampled | EkReceivedCt1Sampled | Ct1Acknowledged
  | Ct2Sampled
  deriving DecidableEq

/-- The spec name of a code state. -/
def States.name : States → SpecState
  | .KeysUnsampled _ => .KeysUnsampled
  | .KeysSampled _ => .KeysSampled
  | .HeaderSent _ => .HeaderSent
  | .Ct1Received _ => .Ct1Received
  | .EkSentCt1Received _ => .EkSentCt1Received
  | .NoHeaderReceived _ => .NoHeaderReceived
  | .HeaderReceived _ => .HeaderReceived
  | .Ct1Sampled _ => .Ct1Sampled
  | .EkReceivedCt1Sampled _ => .EkReceivedCt1Sampled
  | .Ct1Acknowledged _ => .Ct1Acknowledged
  | .Ct2Sampled _ => .Ct2Sampled

open Classical in
/-- `specRecvEq s p` is ML-KEM Braid §2.5 `Receive` in state `s` on payload `p` of a message
from the epoch of `s`, extended by Deviations `ct1ack-accepted` and `late-ek-chunk`. Its decoder
and checks are the code's, through `States.Accepts` and `States.Rejects`, not the spec's. The
result is the next state's name and whether a key is emitted, or `none` when `s.Rejects p` holds.
`none` stands at the places of the spec's `raise` in the `ek` check and its `FAIL` in `VfyHdr` or
`VfyCt` (§2.4, p. 9), with the code's checks. What the session does after a failure (§2.4, p. 9)
is outside `specRecvEq`.
The comments on the arms give the spec's transition numbers, or the deviation that adds the arm.

* Transitions (2), (4) and (12), and Deviation `ct1ack-accepted`, need no completed message
  and are taken directly.
* Transitions (3), (5), (6), (9), (10), (11), and Deviation `late-ek-chunk`, are taken when
  `States.Accepts` holds. The result is `none` when `States.Rejects` holds. When no message
  completes the decoder, neither holds and the state keeps its name. The exception is `Ct1Sampled`
  on `EkCt1Ack`, which then takes transition (8).
* If `¬ s.Expects p`, the state keeps its name.

Only transition (5) emits a key. `States.Accepts` and `States.Rejects` read the code's calls.
A call that returns excludes the panic cases. It does not make the code's decoder and checks
agree with the spec's. -/
noncomputable def specRecvEq (s : States) (p : MessagePayload) : Option (SpecState × Bool) :=
  let stay := some (s.name, false)
  let complete (n : SpecState) (key : Bool) (otherwise : Option (SpecState × Bool)) :=
    if s.Accepts p then some (n, key) else if s.Rejects p then none else otherwise
  match s, p with
  | .KeysSampled _, .Ct1 _ => some (.HeaderSent, false)                   -- (2)
  | .HeaderSent _, .Ct1 _ => complete .Ct1Received false stay            -- (3)
  | .Ct1Received _, .Ct2 _ => some (.EkSentCt1Received, false)           -- (4)
  | .EkSentCt1Received _, .Ct2 _ => complete .NoHeaderReceived true stay -- (5)
  | .NoHeaderReceived _, .Hdr _ => complete .HeaderReceived false stay   -- (6)
  | .Ct1Sampled _, .Ek _ => complete .EkReceivedCt1Sampled false stay    -- (10)
  | .Ct1Sampled _, .EkCt1Ack _ =>
      complete .Ct2Sampled false (some (.Ct1Acknowledged, false))        -- (9), (8)
  | .EkReceivedCt1Sampled _, .EkCt1Ack _ => some (.Ct2Sampled, false)    -- (12)
  -- deviation ct1ack-accepted
  | .EkReceivedCt1Sampled _, .Ct1Ack true => some (.Ct2Sampled, false)
  | .Ct1Acknowledged _, .EkCt1Ack _ => complete .Ct2Sampled false stay   -- (11)
  -- deviation late-ek-chunk
  | .Ct1Acknowledged _, .Ek _ => complete .Ct2Sampled false stay
  | _, _ => stay

/-- If state `s` does not expect payload `p`, then `specRecvEq s p` keeps the state's name and
emits no key. This keeps `States.Expects` consistent with the last arm of `specRecvEq`. -/
theorem specRecvEq_of_not_expects {s : States} {p : MessagePayload} (hp : ¬ s.Expects p) :
    specRecvEq s p = some (s.name, false) := by
  cases s <;> rcases p with _ | _ | _ | _ | (_ | _) | _ | _ <;>
    simp only [States.Expects, not_true_eq_false] at hp <;> rfl

/-! ## Support lemmas

The code's slicing of a completed message, and the uniqueness of the message a chunk
completes. -/

private theorem as_slice_val {v : alloc.vec.Vec Std.U8} {s : Slice Std.U8}
    (h : alloc.vec.Vec.as_slice Global v = ok s) : s.val = v.val := by
  simp only [alloc.vec.Vec.as_slice, ok.injEq] at h; subst h; exact Slice.from_val _ _

private theorem index_from_val {s s1 : Slice Std.U8} {i : Std.Usize}
    (h : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8) s
      { start := i } = ok s1) : s1.val = s.val.drop i.val := by
  simp only [Slice.index_SliceIndexRangeFromUsizeSliceInst,
    core.slice.index.SliceIndexRangeFromUsizeSlice.index] at h
  split at h
  · simp only [ok.injEq] at h; subst h; exact Slice.from_val _ _
  · exact absurd h fail_not_ok

private theorem index_to_val {s s1 : Slice Std.U8} {i : Std.Usize}
    (h : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) s
      { «end» := i } = ok s1) : s1.val = s.val.take i.val := by
  simp only [Slice.index_SliceIndexRangeToUsizeSliceInst,
    core.slice.index.SliceIndexRangeToUsizeSlice.index] at h
  split at h
  · simp only [ok.injEq] at h; subst h; simp [List.slice]
  · exact absurd h fail_not_ok

private theorem to_vec_val {s : Slice Std.U8} {v : alloc.vec.Vec Std.U8}
    (h : alloc.slice.Slice.to_vec core.clone.CloneU8 s = ok v) : v.val = s.val := by
  obtain ⟨w, hw, hp⟩ := WP.spec_imp_exists
    (alloc.slice.Slice.to_vec_spec core.clone.CloneU8 s (fun _ _ => rfl))
  rw [hw, ok.injEq] at h; subst h; rw [hp]; rfl

/-- A chunk completes a decoder with at most one message: `add_chunk` and `decoded_message` are
functions. -/
theorem decodes_unique {d : encoding.polynomial.PolyDecoder} {c : encoding.Chunk}
    {m m' : alloc.vec.Vec Std.U8} (h : decodes d c m) (h' : decodes d c m') : m = m' := by
  obtain ⟨d1, h1, h2⟩ := h; obtain ⟨d2, h3, h4⟩ := h'
  rw [h1, ok.injEq] at h3; subst h3
  rw [h2, ok.injEq, Option.some.injEq] at h4; exact h4

/-! ### The chunk handlers

For each state that accumulates chunks: if the chunk handler returns, its result tells whether
the chunk completes a message and whether that message passes `CheckPasses`.

* A result that keeps receiving means that no message completes the decoder.
* A result that stops receiving means that a completed message passes the check.
* `Err` means that a completed message fails the check.

`recv_header_check` and `recv_ek_check` give the same split for the unchunked calls that the
handlers make. -/

open core.result.Result.Insts.CoreOpsTry (branch_eq_continue branch_eq_break)

/-- If `decoded_message` returns `none` after `add_chunk`, then `decodes d c m` is false for every
`m`. -/
theorem not_decodes_of_none {d d' : encoding.polynomial.PolyDecoder} {c : encoding.Chunk}
    (h1 : encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk d c = ok d')
    (h2 : encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.decoded_message d' = ok none)
    (m : alloc.vec.Vec Std.U8) : ¬ decodes d c m := by
  rintro ⟨d'', h3, h4⟩
  rw [h1, ok.injEq] at h3; subst h3
  rw [h2, ok.injEq] at h4; cases h4

/-- If `HeaderSent::recv_ct1_chunk st e c` returns `r`, then `r = StillReceiving` means that
chunk `c` completes no message in the decoder `st.receiving_ct1`. `r = Done`, the move to
`Ct1Received` by transition (3), means that `c` completes a message. There is no check. -/
theorem HeaderSent_recv_ct1_chunk_outcome (st : send_ek.HeaderSent) (e : Std.U64)
    (c : encoding.Chunk) {r : send_ek.HeaderSentRecvChunk}
    (h : send_ek.HeaderSent.recv_ct1_chunk st e c = ok r) :
    match r with
    | .StillReceiving _ => ∀ m, ¬ decodes st.receiving_ct1 c m
    | .Done _ => ∃ m, decodes st.receiving_ct1 c m := by
  simp only [send_ek.HeaderSent.recv_ct1_chunk, bind_eq_ok] at h
  obtain ⟨_, -, d', hd, o, ho, h⟩ := h
  cases o with
  | none =>
    simp only [ok.injEq] at h; subst h
    exact not_decodes_of_none hd ho
  | some m =>
    obtain ⟨_, -, h⟩ := bind_eq_ok.1 h
    simp only [ok.injEq] at h; subst h
    exact ⟨m, d', hd, ho⟩

/-- The code's split of a completed message `m` at `i` is `take i` / `drop i`. -/
private theorem split_vals {m : alloc.vec.Vec Std.U8} {i : Std.Usize} {s s1 s2 : Slice Std.U8}
    {lo hi : alloc.vec.Vec Std.U8}
    (hs : alloc.vec.Vec.as_slice Global m = ok s)
    (hs1 : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8) s
      { start := i } = ok s1)
    (hhi : alloc.slice.Slice.to_vec core.clone.CloneU8 s1 = ok hi)
    (hs2 : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) s
      { «end» := i } = ok s2)
    (hlo : alloc.slice.Slice.to_vec core.clone.CloneU8 s2 = ok lo) :
    lo.val = m.val.take i.val ∧ hi.val = m.val.drop i.val := by
  refine ⟨?_, ?_⟩
  · rw [to_vec_val hlo, index_to_val hs2, as_slice_val hs]
  · rw [to_vec_val hhi, index_from_val hs1, as_slice_val hs]

/-- If `EkSentCt1Received::recv_ct2_chunk st e c` returns `r`, then:

* `Ok StillReceiving` means that chunk `c` completes no message in the decoder
  `st.receiving_ct2`.
* `Ok Done`, transition (5), means that a message `m` completes it and `recv_ct2` accepts `m`
  split into ciphertext and MAC.
* `Err` means that a message `m` completes it and `recv_ct2` rejects the split. -/
theorem EkSentCt1Received_recv_ct2_chunk_outcome (st : send_ek.EkSentCt1Received) (e : Std.U64)
    (c : encoding.Chunk) {r : core.result.Result send_ek.EkSentCt1ReceivedRecvChunk Error}
    (h : send_ek.EkSentCt1Received.recv_ct2_chunk st e c = ok r) :
    match r with
    | .Ok (.StillReceiving _) => ∀ m, ¬ decodes st.receiving_ct2 c m
    | .Ok (.Done _) => ∃ m, decodes st.receiving_ct2 c m ∧
        (States.EkSentCt1Received st).CheckPasses m
    | .Err _ => ∃ m, decodes st.receiving_ct2 c m ∧
        ¬ (States.EkSentCt1Received st).CheckPasses m := by
  simp only [send_ek.EkSentCt1Received.recv_ct2_chunk, bind_eq_ok] at h
  obtain ⟨_, -, d', hd, o, ho, h⟩ := h
  cases o with
  | none =>
    simp only [ok.injEq] at h; subst h
    exact not_decodes_of_none hd ho
  | some m =>
    simp only [bind_eq_ok] at h
    obtain ⟨s, hs, i, hi, s1, hs1, mac, hmac, s2, hs2, ct2, hct, res, hres, cf, hcf, h⟩ := h
    obtain ⟨hlo, hhi⟩ := split_vals hs hs1 hmac hs2 hct
    cases cf with
    | Continue val =>
      obtain rfl := branch_eq_continue hcf
      obtain ⟨uc, sec⟩ := val
      simp only [uncurry_apply_pair, bind_eq_ok, ok.injEq] at h
      obtain ⟨_, -, _, -, _, -, _, -, rfl⟩ := h
      exact ⟨m, ⟨d', hd, ho⟩, i, ct2, mac, (uc, sec), hi, hlo, hhi, hres⟩
    | Break rs =>
      obtain ⟨err, rfl, rfl⟩ := branch_eq_break hcf
      simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok, ok.injEq] at h
      subst h
      refine ⟨m, ⟨d', hd, ho⟩, ?_⟩
      rintro ⟨i', ct2', mac', v, hi', hlo', hhi', hres'⟩
      rw [hi, ok.injEq] at hi'; subst hi'
      obtain rfl : ct2' = ct2 := alloc.vec.Vec.ext _ _ (by rw [hlo', hlo])
      obtain rfl : mac' = mac := alloc.vec.Vec.ext _ _ (by rw [hhi', hhi])
      rw [hres, ok.injEq] at hres'; cases hres'

/-- If `NoHeaderReceived::recv_header uc e hdr mac` returns, an `Ok` result means that
`verify_hdr` with authenticator `uc.auth` at epoch `uc.epoch` accepts `hdr` and `mac`. An `Err`
result means that this call returns an inner `Err`. -/
theorem recv_header_check (uc : v1.unchunked.send_ct.NoHeaderReceived) (e : Std.U64)
    (hdr mac : alloc.vec.Vec Std.U8)
    {r : core.result.Result v1.unchunked.send_ct.HeaderReceived Error}
    (h : v1.unchunked.send_ct.NoHeaderReceived.recv_header uc e hdr mac = ok r) :
    match r with
    | .Ok _ => authenticator.Authenticator.verify_hdr uc.auth uc.epoch
        (alloc.vec.Vec.deref hdr) (alloc.vec.Vec.deref mac) = ok (.Ok ())
    | .Err _ => ∃ err, authenticator.Authenticator.verify_hdr uc.auth uc.epoch
        (alloc.vec.Vec.deref hdr) (alloc.vec.Vec.deref mac) = ok (.Err err) := by
  simp only [v1.unchunked.send_ct.NoHeaderReceived.recv_header, bind_eq_ok] at h
  obtain ⟨_, -, res, hres, cf, hcf, h⟩ := h
  cases cf with
  | Continue val =>
    obtain rfl := branch_eq_continue hcf
    simp only [ok.injEq] at h; subst h
    exact hres
  | Break rs =>
    obtain ⟨err, rfl, rfl⟩ := branch_eq_break hcf
    simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      bind_tc_eq, bind_eq_ok] at h
    obtain ⟨_, -, h⟩ := h
    simp only [ok.injEq] at h; subst h
    exact ⟨err, hres⟩

/-- If `NoHeaderReceived::recv_hdr_chunk st e c` returns `r`, then:

* `Ok StillReceiving` means that chunk `c` completes no message in the decoder
  `st.receiving_hdr`.
* `Ok Done`, transition (6), means that a message `m` completes it and `verify_hdr` accepts `m`
  split into header and MAC.
* `Err` means that a message `m` completes it and `verify_hdr` rejects the split. -/
theorem NoHeaderReceived_recv_hdr_chunk_outcome (st : send_ct.NoHeaderReceived) (e : Std.U64)
    (c : encoding.Chunk) {r : core.result.Result send_ct.NoHeaderReceivedRecvChunk Error}
    (h : send_ct.NoHeaderReceived.recv_hdr_chunk st e c = ok r) :
    match r with
    | .Ok (.StillReceiving _) => ∀ m, ¬ decodes st.receiving_hdr c m
    | .Ok (.Done _) => ∃ m, decodes st.receiving_hdr c m ∧
        (States.NoHeaderReceived st).CheckPasses m
    | .Err _ => ∃ m, decodes st.receiving_hdr c m ∧
        ¬ (States.NoHeaderReceived st).CheckPasses m := by
  simp only [send_ct.NoHeaderReceived.recv_hdr_chunk, bind_eq_ok] at h
  obtain ⟨_, -, d', hd, o, ho, h⟩ := h
  cases o with
  | none =>
    simp only [ok.injEq] at h; subst h
    exact not_decodes_of_none hd ho
  | some m =>
    simp only [bind_eq_ok] at h
    obtain ⟨s, hs, i, hi, s1, hs1, mac, hmac, s2, hs2, hdr, hhdr, _, -, _, -, res, hres, cf, hcf,
      h⟩ := h
    obtain ⟨hlo, hhi⟩ := split_vals hs hs1 hmac hs2 hhdr
    have hchk := recv_header_check _ _ _ _ hres
    cases cf with
    | Continue val =>
      obtain rfl := branch_eq_continue hcf
      simp only [bind_eq_ok, ok.injEq] at h
      obtain ⟨_, -, rfl⟩ := h
      exact ⟨m, ⟨d', hd, ho⟩, i, hdr, mac, hi, hlo, hhi, hchk⟩
    | Break rs =>
      obtain ⟨err, rfl, rfl⟩ := branch_eq_break hcf
      simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok, ok.injEq] at h
      subst h
      obtain ⟨verr, hv⟩ := hchk
      refine ⟨m, ⟨d', hd, ho⟩, ?_⟩
      rintro ⟨i', hdr', mac', hi', hlo', hhi', hv'⟩
      rw [hi, ok.injEq] at hi'; subst hi'
      obtain rfl : hdr' = hdr := alloc.vec.Vec.ext _ _ (by rw [hlo', hlo])
      obtain rfl : mac' = mac := alloc.vec.Vec.ext _ _ (by rw [hhi', hhi])
      rw [hv, ok.injEq] at hv'; cases hv'

/-- If `Ct1Sent::recv_ek uc e ek` returns, an `Ok` result means that
`ek_matches_header ek uc.hdr` gives `true`. An `Err` result means that it gives `false`. -/
theorem recv_ek_check (uc : v1.unchunked.send_ct.Ct1Sent) (e : Std.U64)
    (ek : alloc.vec.Vec Std.U8)
    {r : core.result.Result v1.unchunked.send_ct.Ct1SentEkReceived Error}
    (h : v1.unchunked.send_ct.Ct1Sent.recv_ek uc e ek = ok r) :
    match r with
    | .Ok _ => incremental_mlkem768.ek_matches_header ek uc.hdr = ok true
    | .Err _ => incremental_mlkem768.ek_matches_header ek uc.hdr = ok false := by
  simp only [v1.unchunked.send_ct.Ct1Sent.recv_ek, bind_eq_ok] at h
  obtain ⟨_, -, b, hb, h⟩ := h
  cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true, ok.injEq] at h <;> subst h <;>
    exact hb

/-- If chunk `c` completes decoder `d` with message `m`, and `ek_matches_header m hdr` returns
`false`, then `c` completes `d` with a message that fails the `ek` check. -/
theorem ek_fail_of_err {d d' : encoding.polynomial.PolyDecoder} {c : encoding.Chunk}
    {m : alloc.vec.Vec Std.U8} {hdr : alloc.vec.Vec Std.U8}
    (hd : encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk d c = ok d')
    (ho : encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.decoded_message d' =
      ok (some m))
    (hb : incremental_mlkem768.ek_matches_header m hdr = ok false) :
    ∃ m, decodes d c m ∧ ¬ incremental_mlkem768.ek_matches_header m hdr = ok true :=
  ⟨m, ⟨d', hd, ho⟩, fun h => by rw [hb, ok.injEq] at h; cases h⟩

/-- `States::recv` calls `Ct1Sampled::recv_ek_chunk st e c ack` with `ack = true` for an
`EkCt1Ack` payload and `ack = false` for `Ek`. If the call returns `r`, then:

* `Ok StillReceivingStillSending` means that `ack = false` and chunk `c` completes no message
  in the decoder `st.receiving_ek`. `States::recv` maps this result to `Ct1Sampled`.
* `Ok StillReceiving` means that `ack = true` and no message completes the decoder.
  `States::recv` maps it to `Ct1Acknowledged`, transition (8).
* `Ok StillSending` means that `ack = false` and a completed message passes the `ek` check.
  `States::recv` maps it to `EkReceivedCt1Sampled`, transition (10).
* `Ok Done` means that `ack = true` and a completed message passes the check.
  `States::recv` maps it to `Ct2Sampled`, transition (9).
* `Err` means that a completed message fails the check. -/
theorem Ct1Sampled_recv_ek_chunk_outcome (st : send_ct.Ct1Sampled) (e : Std.U64)
    (c : encoding.Chunk) (ack : Bool)
    {r : core.result.Result send_ct.Ct1SampledRecvChunk Error}
    (h : send_ct.Ct1Sampled.recv_ek_chunk st e c ack = ok r) :
    match r with
    | .Ok (.StillReceivingStillSending _) => ack = false ∧ ∀ m, ¬ decodes st.receiving_ek c m
    | .Ok (.StillReceiving _) => ack = true ∧ ∀ m, ¬ decodes st.receiving_ek c m
    | .Ok (.StillSending _) => ack = false ∧ ∃ m, decodes st.receiving_ek c m ∧
        (States.Ct1Sampled st).CheckPasses m
    | .Ok (.Done _) => ack = true ∧ ∃ m, decodes st.receiving_ek c m ∧
        (States.Ct1Sampled st).CheckPasses m
    | .Err _ => ∃ m, decodes st.receiving_ek c m ∧ ¬ (States.Ct1Sampled st).CheckPasses m := by
  simp only [send_ct.Ct1Sampled.recv_ek_chunk, bind_eq_ok] at h
  obtain ⟨d', hd, o, ho, h⟩ := h
  cases o with
  | none =>
    cases ack <;> simp only [Bool.false_eq_true, ite_false, ite_true, ok.injEq] at h <;> subst h <;>
      exact ⟨rfl, not_decodes_of_none hd ho⟩
  | some m =>
    simp only [bind_eq_ok] at h
    obtain ⟨res, hres, cf, hcf, h⟩ := h
    have hchk := recv_ek_check _ _ _ hres
    cases cf with
    | Continue val =>
      obtain rfl := branch_eq_continue hcf
      cases ack
      · simp only [Bool.false_eq_true, ite_false, ok.injEq] at h; subst h
        exact ⟨rfl, m, ⟨d', hd, ho⟩, hchk⟩
      · simp only [ite_true, bind_eq_ok, Prod.exists, uncurry_apply_pair, ok.injEq] at h
        obtain ⟨_, _, _, -, _, -, rfl⟩ := h
        exact ⟨rfl, m, ⟨d', hd, ho⟩, hchk⟩
    | Break rs =>
      obtain ⟨err, rfl, rfl⟩ := branch_eq_break hcf
      simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok, ok.injEq] at h
      subst h
      exact ek_fail_of_err hd ho hchk

/-- If `Ct1Acknowledged::recv_ek_chunk st e c` returns `r`, then:

* `Ok StillReceiving` means that chunk `c` completes no message in the decoder
  `st.receiving_ek`.
* `Ok Done` means that a completed message passes the `ek` check. On an `EkCt1Ack` payload this
  is transition (11). On an `Ek` payload it is Deviation `late-ek-chunk`.
* `Err` means that a completed message fails the check. -/
theorem Ct1Acknowledged_recv_ek_chunk_outcome (st : send_ct.Ct1Acknowledged) (e : Std.U64)
    (c : encoding.Chunk) {r : core.result.Result send_ct.Ct1AcknowledgedRecvChunk Error}
    (h : send_ct.Ct1Acknowledged.recv_ek_chunk st e c = ok r) :
    match r with
    | .Ok (.StillReceiving _) => ∀ m, ¬ decodes st.receiving_ek c m
    | .Ok (.Done _) => ∃ m, decodes st.receiving_ek c m ∧
        (States.Ct1Acknowledged st).CheckPasses m
    | .Err _ => ∃ m, decodes st.receiving_ek c m ∧
        ¬ (States.Ct1Acknowledged st).CheckPasses m := by
  simp only [send_ct.Ct1Acknowledged.recv_ek_chunk, bind_eq_ok] at h
  obtain ⟨d', hd, o, ho, h⟩ := h
  cases o with
  | none =>
    simp only [ok.injEq] at h; subst h
    exact not_decodes_of_none hd ho
  | some m =>
    simp only [bind_eq_ok] at h
    obtain ⟨res, hres, cf, hcf, h⟩ := h
    have hchk := recv_ek_check _ _ _ hres
    cases cf with
    | Continue val =>
      obtain rfl := branch_eq_continue hcf
      simp only [bind_eq_ok, Prod.exists, uncurry_apply_pair, ok.injEq] at h
      obtain ⟨_, _, _, -, _, -, rfl⟩ := h
      exact ⟨m, ⟨d', hd, ho⟩, hchk⟩
    | Break rs =>
      obtain ⟨err, rfl, rfl⟩ := branch_eq_break hcf
      simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok, ok.injEq] at h
      subst h
      exact ek_fail_of_err hd ho hchk

private theorem not_accepts_rejects {s : States} {p : MessagePayload}
    {d : encoding.polynomial.PolyDecoder}
    {c : encoding.Chunk} (hD : ∀ m, s.Decodes p m ↔ decodes d c m)
    (h : ∀ m, ¬ decodes d c m) : ¬ s.Accepts p ∧ ¬ s.Rejects p :=
  ⟨fun ⟨m, hm, _⟩ => h m ((hD m).1 hm), fun ⟨m, hm, _⟩ => h m ((hD m).1 hm)⟩

private theorem accepts_of {s : States} {p : MessagePayload} {d : encoding.polynomial.PolyDecoder}
    {c : encoding.Chunk} (hD : ∀ m, s.Decodes p m ↔ decodes d c m)
    (h : ∃ m, decodes d c m ∧ s.CheckPasses m) : s.Accepts p :=
  let ⟨m, hm, hc⟩ := h; ⟨m, (hD m).2 hm, hc⟩

private theorem rejects_of {s : States} {p : MessagePayload} {d : encoding.polynomial.PolyDecoder}
    {c : encoding.Chunk} (hD : ∀ m, s.Decodes p m ↔ decodes d c m)
    (h : ∃ m, decodes d c m ∧ ¬ s.CheckPasses m) : ¬ s.Accepts p ∧ s.Rejects p := by
  obtain ⟨m, hm, hc⟩ := h
  refine ⟨?_, m, (hD m).2 hm, hc⟩
  rintro ⟨m', hm', hc'⟩
  obtain rfl := decodes_unique hm ((hD m').1 hm')
  exact hc hc'

/-! ## Theorems for messages from the state's own epoch -/

/-- If `msg.epoch = s.epochOf` and `¬ s.Expects msg.payload`, then `States.recv s msg` leaves
the state unchanged and emits no key. -/
@[correctness_spec, braid_spec "§2.5"]
theorem recv_of_eq_unexpected (s : States) (msg : Message) (h : msg.epoch = s.epochOf)
    (hp : ¬ s.Expects msg.payload) :
    States.recv s msg = ok (.Ok { key := none, state := s }) := by
  obtain ⟨e, p⟩ := msg
  cases s <;> rcases p with _ | _ | _ | _ | (_ | _) | _ | _ <;>
    simp only [States.epochOf, States.Expects, not_true_eq_false] at h hp ⊢ <;>
    simp only [States.recv, send_ek.KeysUnsampled.epoch, send_ek.KeysSampled.epoch,
      send_ek.HeaderSent.epoch, send_ek.Ct1Received.epoch, send_ek.EkSentCt1Received.epoch,
      send_ct.NoHeaderReceived.epoch, send_ct.HeaderReceived.epoch, send_ct.Ct1Sampled.epoch,
      send_ct.EkReceivedCt1Sampled.epoch, send_ct.Ct1Acknowledged.epoch,
      send_ct.Ct2Sampled.epoch, lift, core.cmp.impls.OrdU64.cmp, bind_ok, h,
      Nat.compare_eq_eq.2 rfl, Bool.false_eq_true, ite_false]
  all_goals rfl

/-- If `msg.epoch = s.epochOf` and `States.recv s msg` returns `r`, then `r` agrees with
`specRecvEq s msg.payload`, our model of §2.5 `Receive` extended by Deviations
`ct1ack-accepted` and `late-ek-chunk`. An `Ok` result has the next state's name and key
presence that `specRecvEq` gives. An `Err` result occurs exactly when `specRecvEq` gives `none`. -/
@[correctness_spec, braid_spec "§2.5"]
theorem recv_of_eq_refines (s : States) (msg : Message) (h : msg.epoch = s.epochOf)
    (r : core.result.Result Recv Error) (hr : States.recv s msg = ok r) :
    match r with
    | .Ok ⟨key, s'⟩ => specRecvEq s msg.payload = some (s'.name, key.isSome)
    | .Err _ => specRecvEq s msg.payload = none := by
  obtain ⟨e, p⟩ := msg
  cases s <;> rcases p with _ | c | c | c | (_ | _) | c | c <;>
    simp only [States.epochOf] at h <;>
    simp only [States.recv, send_ek.KeysUnsampled.epoch, send_ek.KeysSampled.epoch,
      send_ek.HeaderSent.epoch, send_ek.Ct1Received.epoch, send_ek.EkSentCt1Received.epoch,
      send_ct.NoHeaderReceived.epoch, send_ct.HeaderReceived.epoch, send_ct.Ct1Sampled.epoch,
      send_ct.EkReceivedCt1Sampled.epoch, send_ct.Ct1Acknowledged.epoch,
      send_ct.Ct2Sampled.epoch, lift, core.cmp.impls.OrdU64.cmp, bind_ok, h,
      Nat.compare_eq_eq.2 rfl, Bool.false_eq_true, ite_false, ite_true] at hr
  all_goals try (rw [ok.injEq] at hr; subst hr; rfl)
  case KeysSampled.Ct1 st _ =>
    obtain ⟨hs, -, hr⟩ := bind_eq_ok.1 hr
    rw [ok.injEq] at hr; subst hr; rfl
  case Ct1Received.Ct2 st _ =>
    obtain ⟨hs, -, hr⟩ := bind_eq_ok.1 hr
    rw [ok.injEq] at hr; subst hr; rfl
  case EkReceivedCt1Sampled.EkCt1Ack st _ =>
    obtain ⟨hs, -, hr⟩ := bind_eq_ok.1 hr
    rw [ok.injEq] at hr; subst hr; rfl
  case EkReceivedCt1Sampled.Ct1Ack.true st _ =>
    obtain ⟨hs, -, hr⟩ := bind_eq_ok.1 hr
    rw [ok.injEq] at hr; subst hr; rfl
  case HeaderSent.Ct1 st _ =>
    obtain ⟨res, hres, hr⟩ := bind_eq_ok.1 hr
    have ho := HeaderSent_recv_ct1_chunk_outcome _ _ _ hres
    have hD : ∀ m, (States.HeaderSent st).Decodes (.Ct1 c) m ↔ decodes st.receiving_ct1 c m :=
      fun _ => Iff.rfl
    cases res <;> rw [ok.injEq] at hr <;> subst hr <;> simp only [specRecvEq]
    · obtain ⟨hA, hR⟩ := not_accepts_rejects hD ho
      rw [ite_eq_right hA, ite_eq_right hR]; rfl
    · obtain ⟨m, hm⟩ := ho
      rw [ite_eq_left (accepts_of hD ⟨m, hm, trivial⟩)]; rfl
  case EkSentCt1Received.Ct2 st _ =>
    simp only [bind_eq_ok] at hr
    obtain ⟨res, hres, cf, hcf, hr⟩ := hr
    have ho := EkSentCt1Received_recv_ct2_chunk_outcome _ _ _ hres
    have hD : ∀ m, (States.EkSentCt1Received st).Decodes (.Ct2 c) m ↔
        decodes st.receiving_ct2 c m := fun _ => Iff.rfl
    cases cf with
    | Continue v =>
      obtain rfl := branch_eq_continue hcf
      cases v with
      | StillReceiving st1 =>
        rw [ok.injEq] at hr; subst hr; simp only [specRecvEq]
        obtain ⟨hA, hR⟩ := not_accepts_rejects hD ho
        rw [ite_eq_right hA, ite_eq_right hR]; rfl
      | Done p =>
        obtain ⟨st1, sec⟩ := p
        change ok (core.result.Result.Ok
          { key := some sec, state := States.NoHeaderReceived st1 }) = ok r at hr
        rw [ok.injEq] at hr; subst hr; simp only [specRecvEq]
        rw [ite_eq_left (accepts_of hD ho)]; rfl
    | Break rs =>
      obtain ⟨err, rfl, rfl⟩ := branch_eq_break hcf
      simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok, ok.injEq] at hr
      subst hr; simp only [specRecvEq]
      obtain ⟨hA, hR⟩ := rejects_of hD ho
      rw [ite_eq_right hA, ite_eq_left hR]
  case NoHeaderReceived.Hdr st _ =>
    simp only [bind_eq_ok] at hr
    obtain ⟨res, hres, cf, hcf, hr⟩ := hr
    have ho := NoHeaderReceived_recv_hdr_chunk_outcome _ _ _ hres
    have hD : ∀ m, (States.NoHeaderReceived st).Decodes (.Hdr c) m ↔
        decodes st.receiving_hdr c m := fun _ => Iff.rfl
    cases cf with
    | Continue v =>
      obtain rfl := branch_eq_continue hcf
      cases v with
      | StillReceiving st1 =>
        rw [ok.injEq] at hr; subst hr; simp only [specRecvEq]
        obtain ⟨hA, hR⟩ := not_accepts_rejects hD ho
        rw [ite_eq_right hA, ite_eq_right hR]; rfl
      | Done st1 =>
        rw [ok.injEq] at hr; subst hr; simp only [specRecvEq]
        rw [ite_eq_left (accepts_of hD ho)]; rfl
    | Break rs =>
      obtain ⟨err, rfl, rfl⟩ := branch_eq_break hcf
      simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok, ok.injEq] at hr
      subst hr; simp only [specRecvEq]
      obtain ⟨hA, hR⟩ := rejects_of hD ho
      rw [ite_eq_right hA, ite_eq_left hR]
  case Ct1Acknowledged.EkCt1Ack st _ =>
    simp only [bind_eq_ok] at hr
    obtain ⟨res, hres, cf, hcf, hr⟩ := hr
    have ho := Ct1Acknowledged_recv_ek_chunk_outcome _ _ _ hres
    have hD : ∀ m, (States.Ct1Acknowledged st).Decodes (.EkCt1Ack c) m ↔
        decodes st.receiving_ek c m := fun _ => Iff.rfl
    cases cf with
    | Continue v =>
      obtain rfl := branch_eq_continue hcf
      cases v with
      | StillReceiving st1 =>
        rw [ok.injEq] at hr; subst hr; simp only [specRecvEq]
        obtain ⟨hA, hR⟩ := not_accepts_rejects hD ho
        rw [ite_eq_right hA, ite_eq_right hR]; rfl
      | Done st1 =>
        rw [ok.injEq] at hr; subst hr; simp only [specRecvEq]
        rw [ite_eq_left (accepts_of hD ho)]; rfl
    | Break rs =>
      obtain ⟨err, rfl, rfl⟩ := branch_eq_break hcf
      simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok, ok.injEq] at hr
      subst hr; simp only [specRecvEq]
      obtain ⟨hA, hR⟩ := rejects_of hD ho
      rw [ite_eq_right hA, ite_eq_left hR]
  case Ct1Acknowledged.Ek st _ =>
    simp only [bind_eq_ok] at hr
    obtain ⟨res, hres, cf, hcf, hr⟩ := hr
    have ho := Ct1Acknowledged_recv_ek_chunk_outcome _ _ _ hres
    have hD : ∀ m, (States.Ct1Acknowledged st).Decodes (.Ek c) m ↔
        decodes st.receiving_ek c m := fun _ => Iff.rfl
    cases cf with
    | Continue v =>
      obtain rfl := branch_eq_continue hcf
      cases v with
      | StillReceiving st1 =>
        rw [ok.injEq] at hr; subst hr; simp only [specRecvEq]
        obtain ⟨hA, hR⟩ := not_accepts_rejects hD ho
        rw [ite_eq_right hA, ite_eq_right hR]; rfl
      | Done st1 =>
        rw [ok.injEq] at hr; subst hr; simp only [specRecvEq]
        rw [ite_eq_left (accepts_of hD ho)]; rfl
    | Break rs =>
      obtain ⟨err, rfl, rfl⟩ := branch_eq_break hcf
      simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok, ok.injEq] at hr
      subst hr; simp only [specRecvEq]
      obtain ⟨hA, hR⟩ := rejects_of hD ho
      rw [ite_eq_right hA, ite_eq_left hR]
  case Ct1Sampled.None st _ | Ct1Sampled.Hdr st _ | Ct1Sampled.Ct1Ack.false st _
      | Ct1Sampled.Ct1Ack.true st _ | Ct1Sampled.Ct1 st _ | Ct1Sampled.Ct2 st _ =>
    change ok (core.result.Result.Ok { key := none, state := States.Ct1Sampled st }) = ok r at hr
    rw [ok.injEq] at hr; subst hr; rfl
  case Ct1Sampled.Ek st _ =>
    obtain ⟨res, hres, hr⟩ := bind_eq_ok.1 hr
    simp only [bind_eq_ok] at hr
    obtain ⟨cf, hcf, hr⟩ := hr
    have ho := Ct1Sampled_recv_ek_chunk_outcome _ _ _ _ hres
    have hD : ∀ m, (States.Ct1Sampled st).Decodes (.Ek c) m ↔
        decodes st.receiving_ek c m := fun _ => Iff.rfl
    cases cf with
    | Continue v =>
      obtain rfl := branch_eq_continue hcf
      cases v <;> rw [ok.injEq] at hr <;> subst hr <;> simp only [specRecvEq] <;>
        simp only [Bool.false_eq_true, false_and] at ho
      all_goals first
        | (obtain ⟨-, ho⟩ := ho; obtain ⟨hA, hR⟩ := not_accepts_rejects hD ho
           rw [ite_eq_right hA, ite_eq_right hR]; rfl)
        | (obtain ⟨-, ho⟩ := ho; rw [ite_eq_left (accepts_of hD ho)]; rfl)
    | Break rs =>
      obtain ⟨err, rfl, rfl⟩ := branch_eq_break hcf
      simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok, ok.injEq] at hr
      subst hr; simp only [specRecvEq]
      obtain ⟨hA, hR⟩ := rejects_of hD ho
      rw [ite_eq_right hA, ite_eq_left hR]
  case Ct1Sampled.EkCt1Ack st _ =>
    obtain ⟨res, hres, hr⟩ := bind_eq_ok.1 hr
    simp only [bind_eq_ok] at hr
    obtain ⟨cf, hcf, hr⟩ := hr
    have ho := Ct1Sampled_recv_ek_chunk_outcome _ _ _ _ hres
    have hD : ∀ m, (States.Ct1Sampled st).Decodes (.EkCt1Ack c) m ↔
        decodes st.receiving_ek c m := fun _ => Iff.rfl
    cases cf with
    | Continue v =>
      obtain rfl := branch_eq_continue hcf
      cases v <;> rw [ok.injEq] at hr <;> subst hr <;> simp only [specRecvEq] <;>
        simp only [Bool.true_eq_false, false_and] at ho
      all_goals first
        | (obtain ⟨-, ho⟩ := ho; obtain ⟨hA, hR⟩ := not_accepts_rejects hD ho
           rw [ite_eq_right hA, ite_eq_right hR]; rfl)
        | (obtain ⟨-, ho⟩ := ho; rw [ite_eq_left (accepts_of hD ho)]; rfl)
    | Break rs =>
      obtain ⟨err, rfl, rfl⟩ := branch_eq_break hcf
      simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok, ok.injEq] at hr
      subst hr; simp only [specRecvEq]
      obtain ⟨hA, hR⟩ := rejects_of hD ho
      rw [ite_eq_right hA, ite_eq_left hR]

end spqr.v1.chunked.states
