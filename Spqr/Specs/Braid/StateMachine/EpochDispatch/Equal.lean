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
public import Spqr.Specs.Braid.StateMachine.EpochDispatch.Guards

/-! # `States::recv` on a message from the state's own epoch

When `msg.epoch` equals the state's epoch, `States::recv` acts on the payload type in eight of
the eleven states. `KeysUnsampled`, `HeaderReceived` and `Ct2Sampled` ignore the message. This
module compares that dispatch with the `Receive` functions of [ML-KEM Braid] §2.5.

* `recv_of_eq_unexpected`: a payload type the state does not act on (`States.Expects`) leaves
  the state unchanged and emits no key.
* `recv_of_eq_refines`: for every payload, if `States.recv` returns, an `Ok` result has the
  successor state name and key presence that `specRecvEq` gives, and an `Err` happens exactly
  when `specRecvEq` is `none`.

`specRecvEq` follows the branches of the spec's `Receive` bodies at the level of state names
and key presence, plus Deviations 2 and 3 listed below. A chunk that completes a decoder takes
the transition if the completed message passes the state's check (`States.Accepts`). It fails if
the message does not pass (`States.Rejects`). Decoding and the check are stated with the code's
own calls. The decoder is `add_chunk` and `decoded_message`. The checks are `recv_ct2` and
`verify_hdr`, on the message split with `take` / `drop`, and `ek_matches_header`, on the whole
message. `HeaderSent` has no check.

`recv_of_eq_refines` covers every payload, and `specRecvEq` adds only Deviations 2 and 3 to the
branches of §2.5. So, for calls that return, and with the code's decoder and checks taken as
the spec's, these two are the only places where the equal-epoch dispatch differs from §2.5 in
state names and key presence. That the code's decoder and checks compute the spec's is not
proved here.

Transitions are numbered as in the state machine of [ML-KEM Braid] §2.5, drawn in its Fig. 1
(p. 10) and marked `# Transition (n)` in the pseudocode of that section.

## What the theorems do not show

* `recv_of_eq_unexpected` is total, but `recv_of_eq_refines` is in the "if it returns" form. It
  constrains only the runs where `States.recv` returns, so an implementation that panics on
  every expected payload also satisfies it. It is not stated as total because some handlers can
  panic when the state's fields have the wrong sizes. For example, transition (2) calls
  `expect` on `encode_bytes` of the state's `ek` (`src/v1/chunked/send_ek.rs:91-92`), which
  fails when the length of `ek` is odd or too large (`src/encoding/polynomial.rs:692-695`).
  Transition (12) calls `encaps2`, which calls `expect` on size conversions of the state's
  encapsulation state and key (`src/incremental_mlkem768.rs:75-76`). Ruling these panics out
  needs invariants on the state, and specifications of the opaque libcrux functions that the
  handlers call. This module proves neither.
* The branches selected by `States.Accepts` and `States.Rejects` constrain the code only when
  some chunk completes the decoder. This module does not prove that such a chunk exists.
* The theorems relate the dispatch to the results of the code's decoder and checks. That
  `add_chunk` and `decoded_message` compute the spec's decoder is not proved here. That
  the code's checks compute the spec's checks is not proved here either: `recv_ct2` for
  `Decaps`, `KDF_OK`, `Update` and `VfyCt`, `verify_hdr` for `VfyHdr`, and
  `ek_matches_header` for `SHA3-256(ek_seed || ek_vector) = hek`.
* Only the successor's name and whether a key is emitted are compared. A successor with the
  right name but a wrong epoch, authenticator, KEM material or decoder, or a wrong key value,
  satisfies `recv_of_eq_refines`.

## Departures from §2.5

The three deviations on the receive path are listed and numbered in the module doc of
`Guards.lean`. Two of them concern this module, and `States.Expects` and `specRecvEq` follow the
code on both:

* Deviation 2: `Ct1Ack true` in `EkReceivedCt1Sampled` takes transition (12).
* Deviation 3: `Ek` in `Ct1Acknowledged` feeds the decoder. When the decoder completes, the
  code runs the check of transition (11), and when the check passes, it takes the step of
  (11).

## References

* [ML-KEM Braid] R. Schmidt, *The ML-KEM Braid Protocol*, Rev. 1, last updated 2025-09-26.
  <https://signal.org/docs/specifications/mlkembraid/mlkembraid.pdf>

**Source**: spqr/src/v1/chunked/states.rs:275-533, spqr/src/v1/chunked/send_ek.rs,
spqr/src/v1/chunked/send_ct.rs -/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace spqr.v1.chunked.states

/-- The payload types a state acts on when the message is from its own epoch: the
`msg.type ==` tests of the `Receive` functions in ML-KEM Braid §2.5, plus `Ct1Ack true` in
`EkReceivedCt1Sampled` (Deviation 2) and `Ek` in `Ct1Acknowledged` (Deviation 3). -/
def States.Expects : States → MessagePayload → Prop
  | .KeysSampled _, .Ct1 _ => True
  | .HeaderSent _, .Ct1 _ => True
  | .Ct1Received _, .Ct2 _ => True
  | .EkSentCt1Received _, .Ct2 _ => True
  | .NoHeaderReceived _, .Hdr _ => True
  | .Ct1Sampled _, .Ek _ => True
  | .Ct1Sampled _, .EkCt1Ack _ => True
  | .EkReceivedCt1Sampled _, .EkCt1Ack _ => True
  | .EkReceivedCt1Sampled _, .Ct1Ack true => True  -- Deviation 2
  | .Ct1Acknowledged _, .EkCt1Ack _ => True
  | .Ct1Acknowledged _, .Ek _ => True              -- Deviation 3
  | _, _ => False

/-- The chunk completes the decoder with message `m`, by the code's `add_chunk` and
`decoded_message`. These calls have the role of the spec's `decoder.add_chunk(msg.data)`,
`decoder.has_message()` and `decoder.message()`. That they compute the spec's decoder is not
proved here. -/
def decodes (d : encoding.polynomial.PolyDecoder) (c : encoding.Chunk)
    (m : alloc.vec.Vec Std.U8) : Prop :=
  ∃ d', encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk d c = ok d' ∧
    encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.decoded_message d' = ok (some m)

/-- The payload's chunk completes, with message `m`, the decoder the state feeds it to. The
pairs are `HeaderSent` on `Ct1`, `EkSentCt1Received` on `Ct2`, `NoHeaderReceived` on `Hdr`, and
`Ct1Sampled` and `Ct1Acknowledged` on `Ek` and `EkCt1Ack`. On every other pair this is
`False`. -/
def States.Decodes : States → MessagePayload → alloc.vec.Vec Std.U8 → Prop
  | .HeaderSent st, .Ct1 c, m => decodes st.receiving_ct1 c m
  | .EkSentCt1Received st, .Ct2 c, m => decodes st.receiving_ct2 c m
  | .NoHeaderReceived st, .Hdr c, m => decodes st.receiving_hdr c m
  | .Ct1Sampled st, .Ek c, m => decodes st.receiving_ek c m
  | .Ct1Sampled st, .EkCt1Ack c, m => decodes st.receiving_ek c m
  | .Ct1Acknowledged st, .Ek c, m => decodes st.receiving_ek c m
  | .Ct1Acknowledged st, .EkCt1Ack c, m => decodes st.receiving_ek c m
  | _, _, _ => False

/-- The code's check on a completed message `m` returns without panicking and passes. Write
`m[..i]` for the first `i` bytes of `m` and `m[i..]` for the rest.

* `EkSentCt1Received`: `recv_ct2` on ciphertext `m[..i]` and MAC `m[i..]`, with
  `i = CIPHERTEXT2_SIZE`, gives `Ok`. It has the role of the spec's `Decaps`, `KDF_OK`,
  `Update` and `VfyCt` (§2.5 p. 15). That it computes these is not proved here. Its only inner
  error is the one `verify_ct` returns.
* `NoHeaderReceived`: `verify_hdr` on header `m[..i]` and MAC `m[i..]`, with `i = HEADER_SIZE`,
  gives `Ok`. It has the role of the spec's `VfyHdr` (§2.5 p. 17). That it computes `VfyHdr` is
  not proved here.
* `Ct1Sampled` and `Ct1Acknowledged`: `ek_matches_header m hdr` gives `true`. It has the role of
  the spec's `SHA3-256(ek_seed || ek_vector) = hek` (§2.5 pp. 19, 22). It calls libcrux
  `validate_pk_bytes` (`src/incremental_mlkem768.rs:28-29`). That it computes the spec's check is
  not proved here.
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

/-- Some message completes the state's decoder from this payload and passes the code's check
(`CheckPasses`). On it, `specRecvEq` takes the state's numbered transition. -/
def States.Accepts (s : States) (p : MessagePayload) : Prop :=
  ∃ m, s.Decodes p m ∧ s.CheckPasses m

/-- The chunk completes the state's decoder and the code's check on the completed message does
not pass: the spec raises or FAILs. Not passing includes the check call panicking (for example,
the epoch increment in `recv_ct2` at `U64.max`), so this matches the spec only on runs where the
call returns. -/
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
/-- ML-KEM Braid §2.5 `Receive` on a message from the state's own epoch, extended by
Deviations 2 and 3. The result is the successor's name and whether a key is emitted, or `none`
when the spec fails: a `raise` in the `ek` check, or a `FAIL` in `VfyHdr` or `VfyCt` (§2.4,
p. 9). What the session does after a failure (§2.4, p. 9) is outside this table. The comments
on the arms give the spec's transition numbers, or the deviation that adds the arm.

* Transitions (2), (4) and (12), and Deviation 2, need no completed message and are taken
  directly.
* Transitions (3), (5), (6), (9), (10), (11), and Deviation 3, are taken when `States.Accepts`
  holds. The result is `none` when `States.Rejects` holds. When no message completes the
  decoder, neither holds and the state keeps its name. The exception is `Ct1Sampled` on
  `EkCt1Ack`, which then takes transition (8).
* A payload type the state does not expect keeps the state's name.

Only transition (5) emits a key. `States.Accepts` and `States.Rejects` read the code's calls,
so the table matches the spec only on runs where those calls return. -/
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
  | .EkReceivedCt1Sampled _, .Ct1Ack true => some (.Ct2Sampled, false)   -- Deviation 2
  | .Ct1Acknowledged _, .EkCt1Ack _ => complete .Ct2Sampled false stay   -- (11)
  | .Ct1Acknowledged _, .Ek _ => complete .Ct2Sampled false stay         -- Deviation 3
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

/-- If `HeaderSent::recv_ct1_chunk` returns `r`, then `r = StillReceiving` means that no message
completes the decoder. `r = Done`, the move to `Ct1Received` by transition (3), means that a
message completes it. There is no check. -/
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

/-- If `EkSentCt1Received::recv_ct2_chunk` returns `r`, then:

* `Ok StillReceiving` means that no message completes the decoder.
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

/-- If `NoHeaderReceived::recv_header` returns, an `Ok` result means that `verify_hdr` accepts
the header and MAC. An `Err` result means that `verify_hdr` returns an inner `Err` on them. -/
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

/-- If `NoHeaderReceived::recv_hdr_chunk` returns `r`, then:

* `Ok StillReceiving` means that no message completes the decoder.
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

/-- If `Ct1Sent::recv_ek` returns, an `Ok` result means that `ek_matches_header` gives `true`.
An `Err` result means that it gives `false`. -/
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

/-- A completed message on which `ek_matches_header` returns `false` fails the `ek` check. -/
theorem ek_fail_of_err {d d' : encoding.polynomial.PolyDecoder} {c : encoding.Chunk}
    {m : alloc.vec.Vec Std.U8} {hdr : alloc.vec.Vec Std.U8}
    (hd : encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk d c = ok d')
    (ho : encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.decoded_message d' =
      ok (some m))
    (hb : incremental_mlkem768.ek_matches_header m hdr = ok false) :
    ∃ m, decodes d c m ∧ ¬ incremental_mlkem768.ek_matches_header m hdr = ok true :=
  ⟨m, ⟨d', hd, ho⟩, fun h => by rw [hb, ok.injEq] at h; cases h⟩

/-- Let `ack` be the flag argument. `States::recv` sets it to `true` for an `EkCt1Ack` payload
and to `false` for `Ek`. If `Ct1Sampled::recv_ek_chunk` returns `r`, then:

* `Ok StillReceivingStillSending` means that `ack = false` and no message completes the
  decoder. `States::recv` maps this result to `Ct1Sampled`.
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

/-- If `Ct1Acknowledged::recv_ek_chunk` returns `r`, then:

* `Ok StillReceiving` means that no message completes the decoder.
* `Ok Done` means that a completed message passes the `ek` check. On an `EkCt1Ack` payload this
  is transition (11). On an `Ek` payload it is Deviation 3.
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

/-- A message from the state's own epoch with a payload type the state does not act on
leaves the state unchanged and emits no key. -/
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

/-- If `States.recv` returns on a message from the state's own epoch, it agrees with the §2.5
`Receive` table extended by Deviations 2 and 3 (`specRecvEq`) on the successor's name and on
whether a key is emitted, and its result is an error exactly when that table gives `none`. -/
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
