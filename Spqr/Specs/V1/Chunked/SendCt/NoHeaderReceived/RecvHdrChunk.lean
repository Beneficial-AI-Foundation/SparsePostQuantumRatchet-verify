/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import SrcTranslated.Funs
public import Spqr.Specs.Encoding.Polynomial.PolyDecoder.AddChunk
public import Spqr.Specs.Encoding.Polynomial.PolyDecoder.DecodedMessage.DecodedMessage
public import Spqr.Specs.V1.Unchunked.SendCt.NoHeaderReceived.RecvHeader
import Spqr.Specs.Encoding.Polynomial.PolyDecoder.New
import Spqr.Specs.IncrementalMlkem768.HEADER_SIZE
import Spqr.Specs.Authenticator.Authenticator.MACSIZE
import Spqr.Specs.Aeneas.ResultExpect
import Spqr.Auxiliary.Aeneas.Vec
/-!
# Spec theorem for `spqr::v1::chunked::send_ct::{NoHeaderReceived}::recv_hdr_chunk`

`NoHeaderReceived` is the initial state of the ciphertext-sending (B→A) side of the *chunked*
V1 ratchet.  It wraps the unchunked state of the same name (carrying the current `epoch : u64`
and the `Authenticator`) and adds a `PolyDecoder` sized for `HEADER_SIZE + MACSIZE = 96` bytes
that erasure-decodes the incoming chunks of A's authenticated header.

`NoHeaderReceived::recv_hdr_chunk` is the only transition out of this state.  On receipt of a
32-byte `Chunk` it:

  1. asserts `epoch == self.uc.epoch` (discharged by the hax contract
     `requires(epoch == self.uc.epoch)`);
  2. feeds the chunk to the decoder (`receiving_hdr.add_chunk(chunk)`), which routes each of the
     16 big-endian GF(2¹⁶) symbols of the chunk to polynomial `j` at x-coordinate `chunk.index`
     and inserts the resulting point into the corresponding sorted set — unless that polynomial
     already holds enough points;
  3. asks the decoder for the reassembled message (`receiving_hdr.decoded_message()`):
       • **`None`** — the header is not yet recoverable; the state is rebuilt with the updated
         decoder and returned as `StillReceiving`;
       • **`Some(msg)`** — the full `96`-byte message `hdr ‖ mac` has been reconstructed.  It
         is split at `HEADER_SIZE = 64` into the 64-byte ML-KEM header `hdr = msg[..64]` and the
         32-byte tag `mac = msg[64..]` (hax does not model `Vec::split_off`, hence the two
         `to_vec` copies).  A fresh `PolyDecoder::new(ENCAPSULATION_KEY_SIZE)` is prepared for
         the upcoming `ek` chunks, and the unchunked `NoHeaderReceived::recv_header` verifies
         `mac` against `hdr`:
           – on mismatch the `?` operator propagates `Err(MacVerifyFailed)`;
           – otherwise the result is `Done(HeaderReceived { uc, receiving_ek })`, where the
             `.expect("should be able to decode EncapsulationKey size")` can never panic because
             `ENCAPSULATION_KEY_SIZE = 1152` is even.

Two facts needed on the `Some` path are not derivable from the specs of the callees and are
therefore taken as explicit hypotheses, in the predicate-lifting style of
`Specs/Encoding/Decoder/DecodedMessage.lean`:

  * The main theorem is parametrised by a postcondition `decodedPost` for
    `PolyDecoder::decoded_message` (hypothesis `h_decoded`, stated for every decoder that is
    `PointsValid` and satisfies `addChunkPost self.receiving_hdr chunk` — exactly what
    `add_chunk_spec` / `add_chunk_spec_valid` guarantee about the updated decoder),
    together with the length refinement `h_decoded_len` stating that any decoded message has
    exactly `96` bytes — this is what the Rust struct refinement
    `receiving_hdr.get_pts_needed() == (HEADER_SIZE + MACSIZE) / 2` guarantees, and it is what
    makes the two slices `hdr`/`mac` have the lengths `64`/`32` required by `recv_header`.
    `recv_hdr_chunk_spec_concrete` instantiates both with the registered `decoded_message_spec`
    and the refinement `pts_needed = 48`.
  * `ENCAPSULATION_KEY_SIZE` is extracted as the opaque `libcrux_ml_kem::…::pk2_len`, so its
    value `1152` is assumed via `h_ek_size`.

All other callees (`add_chunk`, `as_slice`, `HEADER_SIZE`, range indexing, `to_vec`,
`PolyDecoder::new`, `recv_header`, `expect`) are discharged by their registered specs.

**Source**: spqr/src/v1/chunked/send_ct.rs (lines 82:4-110:5)
-/

@[expose] public section

open Aeneas Aeneas.Std Result spqr encoding.polynomial encoding.gf

/- Helper definitions live in a CamelCase namespace (mirroring
`Spqr.V1.Unchunked.SendCt.NoHeaderReceived` in `RecvHeader.lean`) so that their full names
satisfy the `defsWithUnderscore` linter; the spec theorems themselves stay in the
Rust-mirroring `spqr.v1.chunked.send_ct.NoHeaderReceived` namespace. -/
namespace Spqr.V1.Chunked.SendCt.NoHeaderReceived

open spqr spqr.v1 spqr.v1.chunked spqr.v1.chunked.send_ct

/-- Postcondition of `PolyDecoder::add_chunk` as a relation between the decoder before (`pd0`)
and after (`pd`) absorbing `chunk` (see
`PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk_spec`):

  - `pts_needed` and `is_complete` are preserved;
  - there is a chain `selfs 0 = pd0, …, selfs 16 = pd` of intermediate decoders in which the
    `j`-th two-byte pair of `chunk` becomes the point
    `(x, y) = (chunk.index, 256 · chunk.data[2j] + chunk.data[2j+1])` of polynomial `j`, and is
    inserted into `pts[j]` (append / replace / `sortedInsert`) iff
    `chunk.index < np ∨ |pts[j]| < np` for `np = necessary_points(j)`; otherwise the step is
    the identity. -/
def addChunkPost (pd0 : PolyDecoder) (chunk : encoding.Chunk) (pd : PolyDecoder) : Prop :=
  pd.pts_needed = pd0.pts_needed ∧
  pd.is_complete = pd0.is_complete ∧
  ∃ (selfs : Nat → PolyDecoder),
    selfs 0 = pd0 ∧
    selfs 16 = pd ∧
    ∀ (j : Nat), j < 16 →
      let total_idx := chunk.index.val * 16 + j
      let poly := total_idx % 16
      let poly_idx := total_idx / 16
      let np := pd0.pts_needed.val / 16 +
        (if poly < pd0.pts_needed.val % 16 then 1 else 0)
      (selfs (j + 1)).pts_needed = pd0.pts_needed ∧
      (selfs (j + 1)).is_complete = pd0.is_complete ∧
      poly < 16 ∧
      poly_idx = chunk.index.val ∧
      ∃ (p : Pt),
        p.x.value.val = poly_idx ∧
        p.y.value.val = (chunk.data[j * 2]!) * 256 + (chunk.data[j * 2 + 1]!) ∧
        (if poly_idx < np ∨ ((selfs j).pts.val[poly]!).val.length < np
         then
           (∀ (k : Nat), k ≠ poly → (selfs (j + 1)).pts[k]! = (selfs j).pts.val[k]!) ∧
           PolyDecoder.Insts.SpqrEncodingDecoder.IsSortedPushResult
             ((selfs j).pts.val[poly]!).val
             ((selfs (j + 1)).pts.val[poly]!).val p
         else
           selfs (j + 1) = selfs j)

/-- The decoded `96`-byte message `msg` splits as `msg = hdr ‖ mac` with `hdr` the 64-byte
ML-KEM header (`msg[..HEADER_SIZE]`) and `mac` the 32-byte tag (`msg[HEADER_SIZE..]`).

The literal `64` is `incremental_mlkem768.HEADER_SIZE` (see `HEADER_SIZE_eq`); keep it in sync
if the Rust constant ever changes. -/
def splitsAt64 (msg hdr mac : alloc.vec.Vec U8) : Prop :=
  hdr.val = msg.val.take 64 ∧ mac.val = msg.val.drop 64

open List in
/-- Characterisation of the `HeaderReceived` state `st` produced on the `Done` path, given the
unchunked state `uc : NoHeaderReceived` B started from and the authenticated header `hdr`:

  - the unchunked successor carries `epoch` and `auth` over unchanged and stores `hdr`
    (see `Spqr.V1.Unchunked.SendCt.NoHeaderReceived.recvHeaderPost`);
  - the fresh `ek` decoder is `PolyDecoder::new(ENCAPSULATION_KEY_SIZE)`, i.e. it needs
    `1152 / 2 = 576` points, starts with all `16` polynomials empty and is not complete. -/
def doneHeaderPost (uc : unchunked.send_ct.NoHeaderReceived) (hdr : alloc.vec.Vec U8)
    (st : HeaderReceived) : Prop :=
  st.uc.epoch = uc.epoch ∧
  st.uc.auth = uc.auth ∧
  st.uc.hdr = hdr ∧
  st.receiving_ek.pts_needed.val = 576 ∧
  st.receiving_ek.pts.val = replicate 16 default ∧
  st.receiving_ek.is_complete = false

/-- Postcondition of `NoHeaderReceived::recv_hdr_chunk` as a predicate on the returned
`core.result.Result`, parametrised by the postcondition `decodedPost` assumed for
`PolyDecoder::decoded_message` on the updated decoder.

  - **`Ok (StillReceiving st)`** — decoder yields `none`; unchunked state preserved, decoder
    advanced by `addChunkPost`.
  - **`Ok (Done st)`** — decoder yields `some msg` with `msg = hdr ‖ mac` accepted by
    `verify_hdr` (`hdrAccepted self.uc hdr mac`); `doneHeaderPost self.uc hdr st`.
  - **`Err e`** — decoder yields `some msg` with `msg = hdr ‖ mac` rejected by `verify_hdr`;
    `e = MacVerifyFailed`.

Note: `msg` is related to the received chunks only through `decodedPost`; callers who need the
content guarantee (`BytesDecode`) should use `recv_hdr_chunk_spec_concrete`, which instantiates
`decodedPost` with the registered `decoded_message_spec`. -/
def recvHdrChunkPost (self : NoHeaderReceived) (chunk : encoding.Chunk)
    (decodedPost : PolyDecoder → Option (alloc.vec.Vec U8) → Prop)
    (result : core.result.Result NoHeaderReceivedRecvChunk spqr.Error) : Prop :=
  match result with
  | .Ok (.StillReceiving st) =>
      st.uc = self.uc ∧
      addChunkPost self.receiving_hdr chunk st.receiving_hdr ∧
      decodedPost st.receiving_hdr none
  | .Ok (.Done st) =>
      ∃ (pd : PolyDecoder) (msg hdr mac : alloc.vec.Vec U8),
        addChunkPost self.receiving_hdr chunk pd ∧
        decodedPost pd (some msg) ∧
        msg.length = 96 ∧
        splitsAt64 msg hdr mac ∧
        Spqr.V1.Unchunked.SendCt.NoHeaderReceived.hdrAccepted self.uc hdr mac ∧
        doneHeaderPost self.uc hdr st
  | .Err e =>
      ∃ (pd : PolyDecoder) (msg hdr mac : alloc.vec.Vec U8),
        addChunkPost self.receiving_hdr chunk pd ∧
        decodedPost pd (some msg) ∧
        msg.length = 96 ∧
        splitsAt64 msg hdr mac ∧
        ¬ Spqr.V1.Unchunked.SendCt.NoHeaderReceived.hdrAccepted self.uc hdr mac ∧
        e = spqr.Error.MacVerifyFailed

end Spqr.V1.Chunked.SendCt.NoHeaderReceived

namespace spqr.v1.chunked.send_ct.NoHeaderReceived

open Spqr.V1.Chunked.SendCt.NoHeaderReceived

/-- **Spec theorem for `spqr.v1.chunked.send_ct.NoHeaderReceived.recv_hdr_chunk`**:

• Takes a chunked `NoHeaderReceived` state `self`, the epoch `epoch : U64` announced by the
  peer, and a received 32-byte `chunk`.
• Checks `massert (epoch = self.uc.epoch)`, which succeeds because of `h_epoch`.
• Absorbs the chunk into the decoder via `add_chunk`, then queries `decoded_message`.
• If `decoded_message` returns `none`, returns `StillReceiving` (state unchanged except the
  decoder).
• If `decoded_message` returns `some msg` (with `msg.length = 96` by `h_decoded_len`):
    – views `msg` as a slice, splits it at `HEADER_SIZE = 64` into `hdr = msg[..64]` (64 bytes)
      and `mac = msg[64..]` (32 bytes) via `to_vec`;
    – builds `PolyDecoder::new 1152`, which is `Ok` since `1152` is even;
    – calls `recv_header self.uc epoch hdr mac`:
        * on `Err` the `?` operator propagates `MacVerifyFailed`;
        * on `Ok uc'`, `expect` unwraps the decoder and the result is `Done { uc', pd }`.

• Requires, besides the hax contract `h_epoch`, the no-overflow side conditions of
  `add_chunk` (`h_overflow`, `h_push_cap`), the `SortedSet` invariant of the decoder slots
  (`h_valid`, preserved by `add_chunk_spec_valid`), the lifted postcondition of
  `decoded_message` (`h_decoded`) with its length refinement (`h_decoded_len`), the value of
  the opaque `ENCAPSULATION_KEY_SIZE` (`h_ek_size`), and the boundedness of the MAC key
  inherited from `recv_header_spec` (`h_key`).  Under these hypotheses the call always succeeds
  (no panic).

The result satisfies `recvHdrChunkPost self chunk decodedPost result`.

The proof unfolds `recv_hdr_chunk`, discharges the assertion with `h_epoch`, runs
`add_chunk_spec` and the lifted `h_decoded`, and performs case analysis on the decoded option.
On the `some` path the slice/`to_vec` steps are driven by their Aeneas specs (with the length
side conditions following from `h_decoded_len`), `PolyDecoder::new` is reduced to its `Ok`
branch using `h_ek_size`, and `recv_header_spec` is applied; the `Ok`/`Err` arms of the `?`
operator are then closed by case analysis on its result.

**Source**: spqr/src/v1/chunked/send_ct.rs (lines 82:4-110:5)
-/
@[step]
theorem recv_hdr_chunk_spec (self : NoHeaderReceived) (epoch : U64) (chunk : encoding.Chunk)
    (decodedPost : PolyDecoder → Option (alloc.vec.Vec U8) → Prop)
    (h_epoch : epoch = self.uc.epoch)
    (h_overflow : chunk.index * 16 + 16 ≤ Usize.max)
    (h_push_cap : ∀ (k : Nat), k < 16 →
      (self.receiving_hdr.pts[k]!).length + 17 ≤ Usize.max)
    (h_valid : PolyDecoder.PointsValid self.receiving_hdr.pts)
    (h_decoded : ∀ (pd : PolyDecoder),
      addChunkPost self.receiving_hdr chunk pd →
      PolyDecoder.PointsValid pd.pts →
      PolyDecoder.Insts.SpqrEncodingDecoder.decoded_message pd ⦃
        (o : Option (alloc.vec.Vec U8)) => decodedPost pd o ⦄)
    (h_decoded_len : ∀ (pd : PolyDecoder) (msg : alloc.vec.Vec U8),
      decodedPost pd (some msg) → msg.length = 96)
    (h_ek_size : incremental_mlkem768.ENCAPSULATION_KEY_SIZE ⦃ (r : Usize) => r.val = 1152 ⦄)
    (h_key : self.uc.auth.mac_key.length ≤ U32.max) :
    recv_hdr_chunk self epoch chunk ⦃
      (result : core.result.Result NoHeaderReceivedRecvChunk Error) =>
      recvHdrChunkPost self chunk decodedPost result ⦄ := by
  unfold recv_hdr_chunk
  step with massert_spec _ h_epoch
  step with WP.spec_and
    (PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk_spec self.receiving_hdr chunk
      h_overflow h_push_cap)
    (PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk_spec_valid self.receiving_hdr chunk
      h_overflow h_push_cap h_valid)
    as ⟨receiving_hdr, h_pn, h_ic, selfs, h_s0, h_s16, h_chain, h_valid'⟩
  have h_add : addChunkPost self.receiving_hdr chunk receiving_hdr :=
    ⟨h_pn, h_ic, selfs, h_s0, h_s16, h_chain⟩
  step with h_decoded receiving_hdr h_add h_valid'
  cases o with
  | none =>
    simp only [WP.spec_ok, recvHdrChunkPost, true_and]
    exact ⟨h_add, o_post⟩
  | some msg =>
    have h_len : msg.length = 96 := h_decoded_len receiving_hdr msg o_post
    have h_len' : msg.val.length = 96 := h_len
    step with alloc.vec.Vec.as_slice_spec Global msg as ⟨s, h_s⟩
    have h_s_len : s.length = 96 := by simp only [Slice.length, h_s, h_len']
    rw [incremental_mlkem768.HEADER_SIZE_eq]
    simp only [bind_ok]
    step with core.slice.index.SliceIndexRangeFromUsizeSlice.index.step_spec
      { start := 64#usize } s (by rw [h_s_len]; scalar_tac) as ⟨s1, h_s1, h_s1_len⟩
    step with alloc.slice.Slice.to_vec_spec core.clone.CloneU8 s1 (by intros _ _; rfl)
      as ⟨mac, h_mac⟩
    step with core.slice.index.SliceIndexRangeToUsizeSlice.index.step_spec
      { «end» := 64#usize } s (by rw [h_s_len]; scalar_tac) as ⟨s2, h_s2, h_s2_len⟩
    step with alloc.slice.Slice.to_vec_spec core.clone.CloneU8 s2 (by intros _ _; rfl)
      as ⟨hdr1, h_hdr⟩
    step with h_ek_size as ⟨i1, h_i1⟩
    step with PolyDecoder.Insts.SpqrEncodingDecoder.new_spec i1 as ⟨receiving_ek, h_new⟩
    simp only [h_i1, Nat.reduceMod, ↓reduceIte] at h_new
    have h_hdr_val : hdr1.val = msg.val.take 64 := by
      have : hdr1.val = s2.val := by rw [h_hdr]; rfl
      rw [this, h_s2, h_s, List.slice_zero_j]
    have h_mac_val : mac.val = msg.val.drop 64 := by
      have : mac.val = s1.val := by rw [h_mac]; rfl
      rw [this, h_s1, h_s]
    have h_hdr_len : hdr1.length = 64 := by
      change hdr1.val.length = 64
      rw [h_hdr_val, List.length_take, h_len']; rfl
    have h_mac_len : mac.length = authenticator.Authenticator.MACSIZE.val := by
      change mac.val.length = _
      rw [h_mac_val, List.length_drop, h_len', authenticator.Authenticator.MACSIZE_spec]
    have h_split : splitsAt64 msg hdr1 mac := ⟨h_hdr_val, h_mac_val⟩
    step with unchunked.send_ct.NoHeaderReceived.recv_header_spec self.uc epoch hdr1 mac
      h_epoch h_hdr_len h_mac_len h_key as ⟨r, h_r⟩
    cases r with
    | Ok uc' =>
      obtain ⟨h_acc, h_ep, h_auth, h_hdr'⟩ := h_r
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      cases receiving_ek with
      | Err e =>
        -- `new_spec` rules out the `Err` branch (`1152` is even), so `h_new : False`.
        exact h_new.elim
      | Ok pd0 =>
        obtain ⟨h_pts, h_vec, h_done⟩ := h_new
        step with core.result.Result.expect_ok_spec encoding.EncodingError.Insts.CoreFmtDebug
          pd0 _ as ⟨pd, h_pd⟩
        subst h_pd
        simp only [recvHdrChunkPost]
        refine ⟨receiving_hdr, msg, hdr1, mac, h_add, o_post, h_len, h_split, h_acc,
          h_ep, h_auth, h_hdr', ?_, h_vec, h_done⟩
        rw [h_pts]; rfl
    | Err e =>
      obtain ⟨h_rej, h_e⟩ := h_r
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok, WP.spec_ok, recvHdrChunkPost]
      exact ⟨receiving_hdr, msg, hdr1, mac, h_add, o_post, h_len, h_split, h_rej, h_e⟩

/-- **Spec theorem for `spqr.v1.chunked.send_ct.NoHeaderReceived.recv_hdr_chunk`**
(still-receiving case):

If the updated decoder yields no message yet (`decoded_message` returns `none`), the call
returns `Ok (StillReceiving st)` with the unchunked state untouched and the decoder advanced by
`addChunkPost`.  Projection of `recv_hdr_chunk_spec` with `decodedPost := fun _ o => o = none`.

**Source**: spqr/src/v1/chunked/send_ct.rs (lines 82:4-110:5)
-/
theorem recv_hdr_chunk_spec_still_receiving (self : NoHeaderReceived) (epoch : U64)
    (chunk : encoding.Chunk)
    (h_epoch : epoch = self.uc.epoch)
    (h_overflow : chunk.index * 16 + 16 ≤ Usize.max)
    (h_push_cap : ∀ (k : Nat), k < 16 →
      (self.receiving_hdr.pts[k]!).length + 17 ≤ Usize.max)
    (h_valid : PolyDecoder.PointsValid self.receiving_hdr.pts)
    (h_decoded_none : ∀ (pd : PolyDecoder),
      addChunkPost self.receiving_hdr chunk pd →
      PolyDecoder.PointsValid pd.pts →
      PolyDecoder.Insts.SpqrEncodingDecoder.decoded_message pd ⦃
        (o : Option (alloc.vec.Vec U8)) => o = none ⦄)
    (h_ek_size : incremental_mlkem768.ENCAPSULATION_KEY_SIZE ⦃ (r : Usize) => r.val = 1152 ⦄)
    (h_key : self.uc.auth.mac_key.length ≤ U32.max) :
    recv_hdr_chunk self epoch chunk ⦃
      (result : core.result.Result NoHeaderReceivedRecvChunk Error) =>
      ∃ st : NoHeaderReceived,
        result = .Ok (.StillReceiving st) ∧
        st.uc = self.uc ∧
        addChunkPost self.receiving_hdr chunk st.receiving_hdr ⦄ := by
  apply WP.spec_mono (recv_hdr_chunk_spec self epoch chunk (fun _ o => o = none) h_epoch
    h_overflow h_push_cap h_valid h_decoded_none (fun _ _ h => absurd h (by simp)) h_ek_size h_key)
  intro result h
  match result with
  | .Ok (.StillReceiving st) => exact ⟨st, rfl, h.1, h.2.1⟩
  | .Ok (.Done _) =>
    obtain ⟨_, _, _, _, _, h_none, _⟩ := h; exact absurd h_none (by simp)
  | .Err _ =>
    obtain ⟨_, _, _, _, _, h_none, _⟩ := h; exact absurd h_none (by simp)

/-- **Spec theorem for `spqr.v1.chunked.send_ct.NoHeaderReceived.recv_hdr_chunk`**
(decoded-and-accepted case):

If the updated decoder yields a message (`decoded_message` returns `some msg`, `96` bytes) and
every such `msg = hdr ‖ mac` carries a valid tag (`hdrAccepted self.uc hdr mac`), the call
returns `Ok (Done st)` with `doneHeaderPost self.uc hdr st`.  Projection of
`recv_hdr_chunk_spec`.

**Source**: spqr/src/v1/chunked/send_ct.rs (lines 82:4-110:5)
-/
theorem recv_hdr_chunk_spec_done (self : NoHeaderReceived) (epoch : U64)
    (chunk : encoding.Chunk)
    (h_epoch : epoch = self.uc.epoch)
    (h_overflow : chunk.index * 16 + 16 ≤ Usize.max)
    (h_push_cap : ∀ (k : Nat), k < 16 →
      (self.receiving_hdr.pts[k]!).length + 17 ≤ Usize.max)
    (h_valid : PolyDecoder.PointsValid self.receiving_hdr.pts)
    (h_decoded_some : ∀ (pd : PolyDecoder),
      addChunkPost self.receiving_hdr chunk pd →
      PolyDecoder.PointsValid pd.pts →
      PolyDecoder.Insts.SpqrEncodingDecoder.decoded_message pd ⦃
        (o : Option (alloc.vec.Vec U8)) =>
          ∃ msg, o = some msg ∧ msg.length = 96 ∧
            ∀ hdr mac, splitsAt64 msg hdr mac →
              Spqr.V1.Unchunked.SendCt.NoHeaderReceived.hdrAccepted self.uc hdr mac ⦄)
    (h_ek_size : incremental_mlkem768.ENCAPSULATION_KEY_SIZE ⦃ (r : Usize) => r.val = 1152 ⦄)
    (h_key : self.uc.auth.mac_key.length ≤ U32.max) :
    recv_hdr_chunk self epoch chunk ⦃
      (result : core.result.Result NoHeaderReceivedRecvChunk Error) =>
      ∃ (st : HeaderReceived) (msg hdr mac : alloc.vec.Vec U8),
        result = .Ok (.Done st) ∧
        msg.length = 96 ∧
        splitsAt64 msg hdr mac ∧
        Spqr.V1.Unchunked.SendCt.NoHeaderReceived.hdrAccepted self.uc hdr mac ∧
        doneHeaderPost self.uc hdr st ⦄ := by
  apply WP.spec_mono (recv_hdr_chunk_spec self epoch chunk
    (fun _ o => ∃ msg, o = some msg ∧ msg.length = 96 ∧
      ∀ hdr mac, splitsAt64 msg hdr mac →
        Spqr.V1.Unchunked.SendCt.NoHeaderReceived.hdrAccepted self.uc hdr mac)
    h_epoch h_overflow h_push_cap h_valid h_decoded_some
    (fun _ _ ⟨_, h_eq, h_len, _⟩ => by
      simp only [Option.some.injEq] at h_eq; subst h_eq; exact h_len)
    h_ek_size h_key)
  intro result h
  match result with
  | .Ok (.StillReceiving _) =>
    obtain ⟨_, _, _, h_eq, _⟩ := h
    exact absurd h_eq (by simp)
  | .Ok (.Done st) =>
    obtain ⟨_, msg, hdr, mac, _, _, h_len, h_split, h_acc, h_done⟩ := h
    exact ⟨st, msg, hdr, mac, rfl, h_len, h_split, h_acc, h_done⟩
  | .Err _ =>
    obtain ⟨_, msg, hdr, mac, _, ⟨msg', h_eq, _, h_all⟩, _, h_split, h_rej, _⟩ := h
    simp only [Option.some.injEq] at h_eq
    subst h_eq
    exact absurd (h_all hdr mac h_split) h_rej

/-- **Spec theorem for `spqr.v1.chunked.send_ct.NoHeaderReceived.recv_hdr_chunk`**
(decoded-and-rejected case):

If the updated decoder yields a message (`decoded_message` returns `some msg`, `96` bytes) and
every such `msg = hdr ‖ mac` carries an invalid tag (`¬ hdrAccepted self.uc hdr mac`), the call
returns `Err Error.MacVerifyFailed`.  Projection of `recv_hdr_chunk_spec`.

**Source**: spqr/src/v1/chunked/send_ct.rs (lines 82:4-110:5)
-/
theorem recv_hdr_chunk_spec_err (self : NoHeaderReceived) (epoch : U64)
    (chunk : encoding.Chunk)
    (h_epoch : epoch = self.uc.epoch)
    (h_overflow : chunk.index * 16 + 16 ≤ Usize.max)
    (h_push_cap : ∀ (k : Nat), k < 16 →
      (self.receiving_hdr.pts[k]!).length + 17 ≤ Usize.max)
    (h_valid : PolyDecoder.PointsValid self.receiving_hdr.pts)
    (h_decoded_some : ∀ (pd : PolyDecoder),
      addChunkPost self.receiving_hdr chunk pd →
      PolyDecoder.PointsValid pd.pts →
      PolyDecoder.Insts.SpqrEncodingDecoder.decoded_message pd ⦃
        (o : Option (alloc.vec.Vec U8)) =>
          ∃ msg, o = some msg ∧ msg.length = 96 ∧
            ∀ hdr mac, splitsAt64 msg hdr mac →
              ¬ Spqr.V1.Unchunked.SendCt.NoHeaderReceived.hdrAccepted self.uc hdr mac ⦄)
    (h_ek_size : incremental_mlkem768.ENCAPSULATION_KEY_SIZE ⦃ (r : Usize) => r.val = 1152 ⦄)
    (h_key : self.uc.auth.mac_key.length ≤ U32.max) :
    recv_hdr_chunk self epoch chunk ⦃
      (result : core.result.Result NoHeaderReceivedRecvChunk Error) =>
      result = .Err Error.MacVerifyFailed ⦄ := by
  apply WP.spec_mono (recv_hdr_chunk_spec self epoch chunk
    (fun _ o => ∃ msg, o = some msg ∧ msg.length = 96 ∧
      ∀ hdr mac, splitsAt64 msg hdr mac →
        ¬ Spqr.V1.Unchunked.SendCt.NoHeaderReceived.hdrAccepted self.uc hdr mac)
    h_epoch h_overflow h_push_cap h_valid h_decoded_some
    (fun _ _ ⟨_, h_eq, h_len, _⟩ => by
      simp only [Option.some.injEq] at h_eq; subst h_eq; exact h_len)
    h_ek_size h_key)
  intro result h
  match result with
  | .Ok (.StillReceiving _) =>
    obtain ⟨_, _, _, h_eq, _⟩ := h
    exact absurd h_eq (by simp)
  | .Ok (.Done _) =>
    obtain ⟨_, msg, hdr, mac, _, ⟨msg', h_eq, _, h_all⟩, _, h_split, h_acc, _⟩ := h
    simp only [Option.some.injEq] at h_eq
    subst h_eq
    exact absurd h_acc (h_all hdr mac h_split)
  | .Err _ =>
    obtain ⟨_, _, _, _, _, _, _, _, _, h_e⟩ := h
    rw [h_e]

/-- **Spec theorem for `spqr.v1.chunked.send_ct.NoHeaderReceived.recv_hdr_chunk`**
(concrete `decoded_message` semantics):

Instantiation of `recv_hdr_chunk_spec` with the registered `decoded_message_spec` instead of a
lifted `decodedPost`.  Besides the hypotheses shared with `recv_hdr_chunk_spec`, it assumes the
`#[hax_lib::refine]` struct invariant of the Rust `NoHeaderReceived`,
`h_pts_needed : self.receiving_hdr.pts_needed = 48` (= `(HEADER_SIZE + MACSIZE) / 2`, see
`new_spec`), from which `h_decoded_len` (`msg.length = 96`) is derived rather than assumed.
The resulting `decodedPost` is exactly the postcondition of `decoded_message_spec`: `none` iff
the decoder is complete or some slot lacks points; `some msg` with `msg.length = 96` and
`BytesDecode pd.pts pd.pts_needed msg.val 0` otherwise.

**Source**: spqr/src/v1/chunked/send_ct.rs (lines 82:4-110:5)
-/
theorem recv_hdr_chunk_spec_concrete (self : NoHeaderReceived) (epoch : U64)
    (chunk : encoding.Chunk)
    (h_epoch : epoch = self.uc.epoch)
    (h_overflow : chunk.index * 16 + 16 ≤ Usize.max)
    (h_push_cap : ∀ (k : Nat), k < 16 →
      (self.receiving_hdr.pts[k]!).length + 17 ≤ Usize.max)
    (h_valid : PolyDecoder.PointsValid self.receiving_hdr.pts)
    (h_pts_needed : self.receiving_hdr.pts_needed.val = 48)
    (h_ek_size : incremental_mlkem768.ENCAPSULATION_KEY_SIZE ⦃ (r : Usize) => r.val = 1152 ⦄)
    (h_key : self.uc.auth.mac_key.length ≤ U32.max) :
    recv_hdr_chunk self epoch chunk ⦃
      (result : core.result.Result NoHeaderReceivedRecvChunk Error) =>
      recvHdrChunkPost self chunk
        (fun pd o =>
          pd.pts_needed.val = 48 ∧
          match o with
          | none => pd.is_complete = true ∨
              PolyDecoder.Insts.SpqrEncodingDecoder.someIncomplete pd.pts pd.pts_needed 0 16
          | some out => pd.is_complete = false ∧
              ¬ PolyDecoder.Insts.SpqrEncodingDecoder.someIncomplete pd.pts pd.pts_needed 0 16 ∧
              out.length = 2 * pd.pts_needed.val ∧
              PolyDecoder.Insts.SpqrEncodingDecoder.BytesDecode pd.pts pd.pts_needed out.val 0)
        result ⦄ := by
  apply recv_hdr_chunk_spec self epoch chunk _ h_epoch h_overflow h_push_cap h_valid
    _ _ h_ek_size h_key
  · intro pd h_add h_pv
    have h_pn' : pd.pts_needed.val = 48 := by rw [h_add.1, h_pts_needed]
    apply WP.spec_mono (PolyDecoder.Insts.SpqrEncodingDecoder.decoded_message_spec pd h_pv
      (by rw [h_pn']; scalar_tac))
    intro o h
    exact ⟨h_pn', h⟩
  · intro pd msg h
    obtain ⟨h_pn', _, _, h_len, _⟩ := h
    rw [h_len, h_pn']

end spqr.v1.chunked.send_ct.NoHeaderReceived
