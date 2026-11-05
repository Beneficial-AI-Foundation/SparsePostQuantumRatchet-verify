/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import SrcTranslated.Funs
public import Spqr.Specs.Encoding.Polynomial.PolyDecoder.AddChunk
public import Spqr.Specs.Encoding.Polynomial.PolyDecoder.DecodedMessage.DecodedMessage
public import Spqr.Specs.V1.Unchunked.SendEk.EkSentCt1Received.RecvCt2
import Spqr.Specs.Encoding.Polynomial.PolyDecoder.New
import Spqr.Specs.IncrementalMlkem768.HEADER_SIZE
import Spqr.Specs.Authenticator.Authenticator.MACSIZE
import Spqr.Specs.Aeneas.ResultExpect
import Spqr.Auxiliary.Aeneas.Vec
/-!
# Spec theorem for `spqr::v1::chunked::send_ek::{EkSentCt1Received}::recv_ct2_chunk`

`EkSentCt1Received` is the state of the encapsulation-key-sending (A→B) side of the *chunked*
V1 ratchet after A has fully streamed its encapsulation key `ek` to B and has received
(erasure-decoded) B's first ciphertext `ct1`, while B's second ciphertext `ct2` (together with
the authentication tag) is still being streamed to A in fixed-size chunks.  It wraps the
unchunked state `unchunked::EkSentCt1Received` (carrying the current `epoch : u64`, the
`Authenticator`, the 2400-byte decapsulation key `dk` and the 960-byte `ct1`) and adds a
`PolyDecoder` sized for `CIPHERTEXT2_SIZE + MACSIZE = 128 + 32 = 160` bytes that
erasure-decodes the incoming chunks of `ct2 ‖ mac`.

`EkSentCt1Received::recv_ct2_chunk` is the only transition out of this state.  On receipt of a
32-byte `Chunk` it:

  1. asserts `epoch == self.uc.epoch` (discharged by the hax contract
     `requires(epoch == self.uc.epoch)`);
  2. feeds the chunk to the decoder (`receiving_ct2.add_chunk(chunk)`), which routes each of the
     16 big-endian GF(2¹⁶) symbols of the chunk to polynomial `j` at x-coordinate `chunk.index`
     and inserts the resulting point into the corresponding sorted set — unless that polynomial
     already holds enough points;
  3. asks the decoder for the reassembled message (`receiving_ct2.decoded_message()`):
       • **`None`** — `ct2 ‖ mac` is not yet recoverable; the state is rebuilt with the updated
         decoder and returned as `StillReceiving`;
       • **`Some(msg)`** — the full `160`-byte message `ct2 ‖ mac` has been reconstructed.  It
         is split at `CIPHERTEXT2_SIZE = 128` into the 128-byte second ciphertext half
         `ct2 = msg[..128]` and the 32-byte tag `mac = msg[128..]` (hax does not model
         `Vec::split_off`, hence the two `to_vec` copies).  The unchunked
         `EkSentCt1Received::recv_ct2` then decapsulates `ct1 ‖ ct2`, derives the epoch secret,
         ratchets the authenticator and verifies `mac` over the complete ciphertext:
           – on mismatch the `?` operator propagates `Err(MacVerifyFailed)`;
           – otherwise the roles swap: a fresh `PolyDecoder::new(HEADER_SIZE + MACSIZE)` is
             prepared for B's upcoming authenticated header of the next epoch, and the result is
             `Done((send_ct::NoHeaderReceived { uc, receiving_hdr }, sec))`, where the
             `.expect("should be able to decode header size")` can never panic because
             `HEADER_SIZE + MACSIZE = 96` is even.

The main theorem `recv_ct2_chunk_spec` follows the predicate-lifting style of
`Specs/Encoding/Decoder/DecodedMessage.lean`: it is parametrised by a postcondition
`decodedPost` for `PolyDecoder::decoded_message` on the updated decoder (hypothesis
`h_decoded`), together with the length refinement `h_decoded_len` stating that any decoded
message has exactly `160` bytes.  The corollary `recv_ct2_chunk_spec_concrete` discharges both
with the registered `decoded_message_spec`, under the two struct invariants of the Rust type:
the `SortedSet` ordering of every slot (`PointsValid`) and the `#[hax_lib::refine]`
`receiving_ct2.get_pts_needed() == (CIPHERTEXT2_SIZE + MACSIZE) / 2`, i.e. `pts_needed = 80`,
which is what makes the two slices `ct2`/`mac` have the lengths `128`/`32` required by
`recv_ct2`.

One fact is not derivable from any registered spec and is taken as an explicit hypothesis:
`CIPHERTEXT2_SIZE` is extracted as the opaque `libcrux_ml_kem::…::Ciphertext2::len`, so its
value `128` is assumed via `h_ct2_size` (as `ENCAPSULATION_KEY_SIZE` is in
`SendCt/NoHeaderReceived/RecvHdrChunk.lean`).

All other callees (`add_chunk`, `as_slice`, range indexing, `to_vec`, `recv_ct2`,
`HEADER_SIZE`, `PolyDecoder::new`, `expect`) are discharged by their registered specs; the
outcome of `recv_ct2` is reused verbatim through `recvCt2Post`, so the `Ok`/`Err` branch of the
chunked wrapper is decided exactly as in the unchunked spec.

**Source**: spqr/src/v1/chunked/send_ek.rs (lines 195:4-227:5)
-/

@[expose] public section

open Aeneas Aeneas.Std Result spqr encoding.polynomial encoding.gf

/- Helper definitions live in a CamelCase namespace (mirroring
`Spqr.V1.Unchunked.SendEk.EkSentCt1Received` in `RecvCt2.lean`) so that their full names satisfy
the `defsWithUnderscore` linter; the spec theorems themselves stay in the Rust-mirroring
`spqr.v1.chunked.send_ek.EkSentCt1Received` namespace. -/
namespace Spqr.V1.Chunked.SendEk.EkSentCt1Received

open spqr spqr.v1.chunked spqr.v1.chunked.send_ek

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

/-- The decoded `160`-byte message `msg` splits as `msg = ct2 ‖ mac` with `ct2` the 128-byte
second ciphertext half (`msg[..CIPHERTEXT2_SIZE]`) and `mac` the 32-byte tag
(`msg[CIPHERTEXT2_SIZE..]`). -/
def splitsAt128 (msg ct2 mac : alloc.vec.Vec U8) : Prop :=
  ct2.val = msg.val.take 128 ∧ mac.val = msg.val.drop 128

open List in
/-- Characterisation of the fresh header decoder `receiving_hdr` of the
`send_ct::NoHeaderReceived` state produced on the `Done` path: it is
`PolyDecoder::new(HEADER_SIZE + MACSIZE)`, i.e. it needs `96 / 2 = 48` points, starts with all
`16` polynomials empty and is not complete. -/
def freshHdrDecoder (pd : PolyDecoder) : Prop :=
  pd.pts_needed.val = 48 ∧
  pd.pts.val = replicate 16 default ∧
  pd.is_complete = false

/-- Postcondition of `EkSentCt1Received::recv_ct2_chunk` as a predicate on the returned
`core.result.Result`, parametrised by the postcondition `decodedPost` assumed for
`PolyDecoder::decoded_message` on the updated decoder.

  - **`Ok (StillReceiving st)`** — decoder yields `none`; unchunked state preserved, decoder
    advanced by `addChunkPost` with `PointsValid` preserved (so the spec can be re-applied to
    the next chunk).
  - **`Ok (Done (st, sec))`** — decoder yields `some msg` with `msg = ct2 ‖ mac`; the unchunked
    `recv_ct2 self.uc ct2 mac` returned `Ok (st.uc, sec)` (so, by
    `Spqr.V1.Unchunked.SendEk.EkSentCt1Received.recvCt2Post`, the tag was accepted under the
    ratcheted authenticator, `st.uc.epoch = self.uc.epoch + 1`, `sec.epoch = self.uc.epoch` and
    `sec.secret` is the derived epoch secret); `st.receiving_hdr` is a fresh header decoder.
  - **`Err e`** — decoder yields `some msg` with `msg = ct2 ‖ mac`; `recv_ct2 self.uc ct2 mac`
    returned `Err e` (so the tag was rejected and `e = MacVerifyFailed`). -/
def recvCt2ChunkPost (self : EkSentCt1Received) (chunk : encoding.Chunk)
    (decodedPost : PolyDecoder → Option (alloc.vec.Vec U8) → Prop)
    (result : core.result.Result EkSentCt1ReceivedRecvChunk spqr.Error) : Prop :=
  match result with
  | .Ok (.StillReceiving st) =>
      st.uc = self.uc ∧
      addChunkPost self.receiving_ct2 chunk st.receiving_ct2 ∧
      PolyDecoder.PointsValid st.receiving_ct2.pts ∧
      decodedPost st.receiving_ct2 none
  | .Ok (.Done (st, sec)) =>
      ∃ (pd : PolyDecoder) (msg ct2 mac : alloc.vec.Vec U8),
        addChunkPost self.receiving_ct2 chunk pd ∧
        decodedPost pd (some msg) ∧
        msg.length = 160 ∧
        splitsAt128 msg ct2 mac ∧
        Spqr.V1.Unchunked.SendEk.EkSentCt1Received.recvCt2Post self.uc ct2 mac
          (.Ok (st.uc, sec)) ∧
        freshHdrDecoder st.receiving_hdr
  | .Err e =>
      ∃ (pd : PolyDecoder) (msg ct2 mac : alloc.vec.Vec U8),
        addChunkPost self.receiving_ct2 chunk pd ∧
        decodedPost pd (some msg) ∧
        msg.length = 160 ∧
        splitsAt128 msg ct2 mac ∧
        Spqr.V1.Unchunked.SendEk.EkSentCt1Received.recvCt2Post self.uc ct2 mac (.Err e)

end Spqr.V1.Chunked.SendEk.EkSentCt1Received

namespace spqr.v1.chunked.send_ek.EkSentCt1Received

open Spqr.V1.Chunked.SendEk.EkSentCt1Received

/-- **Spec theorem for `spqr.v1.chunked.send_ek.EkSentCt1Received.recv_ct2_chunk`**:

• Takes a chunked `EkSentCt1Received` state `self`, consisting of the unchunked inner state
  `self.uc : unchunked.send_ek.EkSentCt1Received` and the chunk decoder
  `self.receiving_ct2 : PolyDecoder`, the epoch `epoch : U64` announced by the peer, and the
  received 32-byte `chunk`.  In the original Rust source `self` is consumed by value and
  `chunk` is passed by shared reference; after Aeneas extraction both are plain values.
• Checks `massert (epoch = self.uc.epoch)`, which succeeds because of `h_epoch`.
• Absorbs the chunk into the decoder via `add_chunk`, obtaining `receiving_ct2` with
  `addChunkPost self.receiving_ct2 chunk receiving_ct2`, then queries `decoded_message`,
  obtaining `o : Option (Vec U8)` with `decodedPost receiving_ct2 o`.
• If `o = none`, returns `Ok (StillReceiving { self with receiving_ct2 })`.
• If `o = some msg` (with `msg.length = 160` by `h_decoded_len`):
    – views `msg` as a slice, splits it at `CIPHERTEXT2_SIZE = 128` into `ct2 = msg[..128]`
      (128 bytes) and `mac = msg[128..]` (32 bytes) via `to_vec`;
    – calls `unchunked.send_ek.EkSentCt1Received.recv_ct2 self.uc ct2 mac`:
        * on `Err e` the `?` operator (`branch` / `from_residual` with the identity `From`
          instance) returns `Err e`, where `e = MacVerifyFailed`;
        * on `Ok (uc, sec)` it computes `HEADER_SIZE + MACSIZE = 96` (no overflow), builds
          `PolyDecoder::new 96` (which is `Ok` since `96` is even), unwraps it with `expect`,
          and returns `Ok (Done ({ uc, receiving_hdr := pd }, sec))`.

• Requires:
    – `h_epoch : epoch = self.uc.epoch` — the hax precondition, discharging the `assert_eq!`;
    – `h_overflow`, `h_push_cap` — the `usize` guards of `add_chunk_spec`: the base index
      `chunk.index * 16 + 16` fits, and each of the 16 sorted sets has room for 16 more points;
    – `h_valid` — every slot of `self.receiving_ct2.pts` is `SlotSorted` (the `SortedSet`
      invariant), which `add_chunk_spec_valid` carries to the updated decoder;
    – `h_decoded` — the assumed behaviour of `decoded_message` on any decoder related to
      `self.receiving_ct2` by `addChunkPost self.receiving_ct2 chunk` and satisfying
      `PointsValid` (everything `add_chunk_spec` / `add_chunk_spec_valid` guarantee about the
      updated decoder; `pts_needed`/`is_complete` agreement is the first two conjuncts of
      `addChunkPost`), with its length refinement `h_decoded_len`; see
      `recv_ct2_chunk_spec_concrete` for the instantiation with `decoded_message_spec`;
    – `h_ct2_size` — the value of the opaque `CIPHERTEXT2_SIZE`;
    – `h_dk`, `h_ct1`, `h_uc_epoch`, `h_root` — the guards of `recv_ct2_spec`: the struct
      refinements `dk.len() == 2400`, `ct1.len() == 960`, the hax `assume!(epoch < u64::MAX)`
      and the memory-boundedness of the authenticator ratchet.  The remaining guards
      `ct2.length = 128 ∧ mac.length = MACSIZE` are *not* assumed: they follow from
      `h_decoded_len` and the split.
  Under these hypotheses the call never panics.
• The chunked wrapper introduces no epoch logic of its own: on the `StillReceiving` path the
  unchunked state is untouched, and on the `Done` path the epoch advance, the authenticator
  ratchet and the epoch secret are exactly those of the unchunked `recv_ct2`.

The result satisfies `recvCt2ChunkPost self chunk decodedPost result`.

The proof unfolds `recv_ct2_chunk`, discharges the assertion with `h_epoch`, runs
`add_chunk_spec` and the lifted `h_decoded`, and performs case analysis on the decoded option.
On the `some` path the slice/`to_vec` steps are driven by their Aeneas specs (with the length
side conditions following from `h_decoded_len` and `h_ct2_size`), `recv_ct2_spec` is applied and
its `Result` split; the `Ok` arm reduces `branch` to `Continue`, rewrites `HEADER_SIZE`, reduces
`PolyDecoder::new 96` to its `Ok` branch and unwraps it with `expect_ok_spec`; the `Err` arm
reduces `branch` / `from_residual` to the propagated error.

**Source**: spqr/src/v1/chunked/send_ek.rs (lines 195:4-227:5)
-/
theorem recv_ct2_chunk_spec (self : EkSentCt1Received) (epoch : U64) (chunk : encoding.Chunk)
    (decodedPost : PolyDecoder → Option (alloc.vec.Vec U8) → Prop)
    (h_epoch : epoch = self.uc.epoch)
    (h_overflow : chunk.index * 16 + 16 ≤ Usize.max)
    (h_push_cap : ∀ (k : Nat), k < 16 →
      (self.receiving_ct2.pts[k]!).length + 17 ≤ Usize.max)
    (h_valid : PolyDecoder.PointsValid self.receiving_ct2.pts)
    (h_decoded : ∀ (pd : PolyDecoder),
      addChunkPost self.receiving_ct2 chunk pd →
      PolyDecoder.PointsValid pd.pts →
      PolyDecoder.Insts.SpqrEncodingDecoder.decoded_message pd ⦃
        (o : Option (alloc.vec.Vec U8)) => decodedPost pd o ⦄)
    (h_decoded_len : ∀ (pd : PolyDecoder) (msg : alloc.vec.Vec U8),
      decodedPost pd (some msg) → msg.length = 160)
    (h_ct2_size : incremental_mlkem768.CIPHERTEXT2_SIZE ⦃ (r : Usize) => r.val = 128 ⦄)
    (h_dk : self.uc.dk.length = 2400)
    (h_ct1 : self.uc.ct1.length = 960)
    (h_uc_epoch : self.uc.epoch < U64.max)
    (h_root : self.uc.auth.root_key.length + 32 ≤ Usize.max) :
    recv_ct2_chunk self epoch chunk ⦃
      (result : core.result.Result EkSentCt1ReceivedRecvChunk Error) =>
      recvCt2ChunkPost self chunk decodedPost result ⦄ := by
  unfold recv_ct2_chunk
  step with massert_spec _ h_epoch
  step with WP.spec_and
    (PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk_spec self.receiving_ct2 chunk
      h_overflow h_push_cap)
    (PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk_spec_valid self.receiving_ct2 chunk
      h_overflow h_push_cap h_valid)
    as ⟨receiving_ct2, h_pn, h_ic, selfs, h_s0, h_s16, h_chain, h_valid'⟩
  have h_add : addChunkPost self.receiving_ct2 chunk receiving_ct2 :=
    ⟨h_pn, h_ic, selfs, h_s0, h_s16, h_chain⟩
  step with h_decoded receiving_ct2 h_add h_valid'
  cases o with
  | none =>
    simp only [WP.spec_ok, recvCt2ChunkPost, true_and]
    exact ⟨h_add, h_valid', o_post⟩
  | some msg =>
    have h_len : msg.length = 160 := h_decoded_len receiving_ct2 msg o_post
    have h_len' : msg.val.length = 160 := h_len
    step with alloc.vec.Vec.as_slice_spec Global msg as ⟨s, h_s⟩
    have h_s_len : s.length = 160 := by simp only [Slice.length, h_s, h_len']
    step with h_ct2_size as ⟨i, h_i⟩
    have h_i' : i = 128#usize := by scalar_tac
    subst h_i'
    step with core.slice.index.SliceIndexRangeFromUsizeSlice.index.step_spec
      { start := 128#usize } s (by rw [h_s_len]; scalar_tac) as ⟨s1, h_s1, h_s1_len⟩
    step with alloc.slice.Slice.to_vec_spec core.clone.CloneU8 s1 (by intros _ _; rfl)
      as ⟨mac, h_mac⟩
    step with core.slice.index.SliceIndexRangeToUsizeSlice.index.step_spec
      { «end» := 128#usize } s (by rw [h_s_len]; scalar_tac) as ⟨s2, h_s2, h_s2_len⟩
    step with alloc.slice.Slice.to_vec_spec core.clone.CloneU8 s2 (by intros _ _; rfl)
      as ⟨ct21, h_ct21⟩
    have h_ct2_val : ct21.val = msg.val.take 128 := by
      have : ct21.val = s2.val := by rw [h_ct21]; rfl
      rw [this, h_s2, h_s, List.slice_zero_j]
    have h_mac_val : mac.val = msg.val.drop 128 := by
      have : mac.val = s1.val := by rw [h_mac]; rfl
      rw [this, h_s1, h_s]
    have h_ct2_len : ct21.length = 128 := by
      change ct21.val.length = 128
      rw [h_ct2_val, List.length_take, h_len']; rfl
    have h_mac_len : mac.length = authenticator.Authenticator.MACSIZE.val := by
      change mac.val.length = _
      rw [h_mac_val, List.length_drop, h_len', authenticator.Authenticator.MACSIZE_spec]
    have h_split : splitsAt128 msg ct21 mac := ⟨h_ct2_val, h_mac_val⟩
    step with unchunked.send_ek.EkSentCt1Received.recv_ct2_spec self.uc ct21 mac
      h_dk h_ct1 h_ct2_len h_mac_len h_uc_epoch h_root as ⟨r, h_r⟩
    cases r with
    | Ok p =>
      obtain ⟨uc, sec⟩ := p
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      rw [incremental_mlkem768.HEADER_SIZE_eq]
      simp only [bind_ok]
      step with Usize.add_spec (x := 64#usize) (y := authenticator.Authenticator.MACSIZE)
        (by simp only [authenticator.Authenticator.MACSIZE_spec]; scalar_tac) as ⟨i2, h_i2⟩
      have h_i2' : i2.val = 96 := by
        simp only [h_i2, authenticator.Authenticator.MACSIZE_spec]
      step with PolyDecoder.Insts.SpqrEncodingDecoder.new_spec i2 as ⟨decoder, h_new⟩
      simp only [h_i2', Nat.reduceMod, ↓reduceIte] at h_new
      cases decoder with
      | Err e => exact absurd h_new not_false
      | Ok pd0 =>
        obtain ⟨h_pts, h_vec, h_done⟩ := h_new
        step with core.result.Result.expect_ok_spec encoding.EncodingError.Insts.CoreFmtDebug
          pd0 _ as ⟨pd, h_pd⟩
        subst h_pd
        simp only [recvCt2ChunkPost]
        refine ⟨receiving_ct2, msg, ct21, mac, h_add, o_post, h_len, h_split, h_r, ?_, h_vec,
          h_done⟩
        rw [h_pts]; rfl
    | Err e =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok, WP.spec_ok, recvCt2ChunkPost]
      exact ⟨receiving_ct2, msg, ct21, mac, h_add, o_post, h_len, h_split, h_r⟩

/-- **Spec theorem for `spqr.v1.chunked.send_ek.EkSentCt1Received.recv_ct2_chunk`**
(still-receiving case):

If the updated decoder yields no message yet (`decoded_message` returns `none`), the call
returns `Ok (StillReceiving st)` with the unchunked state untouched and the decoder advanced by
`addChunkPost` with `PointsValid` preserved.  Projection of `recv_ct2_chunk_spec` with
`decodedPost := fun _ o => o = none`.

**Source**: spqr/src/v1/chunked/send_ek.rs (lines 195:4-227:5)
-/
theorem recv_ct2_chunk_spec_still_receiving (self : EkSentCt1Received) (epoch : U64)
    (chunk : encoding.Chunk)
    (h_epoch : epoch = self.uc.epoch)
    (h_overflow : chunk.index * 16 + 16 ≤ Usize.max)
    (h_push_cap : ∀ (k : Nat), k < 16 →
      (self.receiving_ct2.pts[k]!).length + 17 ≤ Usize.max)
    (h_valid : PolyDecoder.PointsValid self.receiving_ct2.pts)
    (h_decoded_none : ∀ (pd : PolyDecoder),
      addChunkPost self.receiving_ct2 chunk pd →
      PolyDecoder.PointsValid pd.pts →
      PolyDecoder.Insts.SpqrEncodingDecoder.decoded_message pd ⦃
        (o : Option (alloc.vec.Vec U8)) => o = none ⦄)
    (h_ct2_size : incremental_mlkem768.CIPHERTEXT2_SIZE ⦃ (r : Usize) => r.val = 128 ⦄)
    (h_dk : self.uc.dk.length = 2400)
    (h_ct1 : self.uc.ct1.length = 960)
    (h_uc_epoch : self.uc.epoch < U64.max)
    (h_root : self.uc.auth.root_key.length + 32 ≤ Usize.max) :
    recv_ct2_chunk self epoch chunk ⦃
      (result : core.result.Result EkSentCt1ReceivedRecvChunk Error) =>
      ∃ st : EkSentCt1Received,
        result = .Ok (.StillReceiving st) ∧
        st.uc = self.uc ∧
        addChunkPost self.receiving_ct2 chunk st.receiving_ct2 ∧
        PolyDecoder.PointsValid st.receiving_ct2.pts ⦄ := by
  apply WP.spec_mono (recv_ct2_chunk_spec self epoch chunk (fun _ o => o = none) h_epoch
    h_overflow h_push_cap h_valid h_decoded_none (fun _ _ h => absurd h (by simp)) h_ct2_size
    h_dk h_ct1 h_uc_epoch h_root)
  intro result h
  match result with
  | .Ok (.StillReceiving st) => exact ⟨st, rfl, h.1, h.2.1, h.2.2.1⟩
  | .Ok (.Done (_, _)) =>
    obtain ⟨_, _, _, _, _, h_none, _⟩ := h; exact absurd h_none (by simp)
  | .Err _ =>
    obtain ⟨_, _, _, _, _, h_none, _⟩ := h; exact absurd h_none (by simp)

/-- **Spec theorem for `spqr.v1.chunked.send_ek.EkSentCt1Received.recv_ct2_chunk`**
(concrete `decoded_message` semantics):

Instantiation of `recv_ct2_chunk_spec` with the registered `decoded_message_spec` instead of a
lifted `decodedPost`.  Besides the hypotheses shared with `recv_ct2_chunk_spec`, it assumes the
two struct invariants of the Rust `EkSentCt1Received`: `h_valid` (every slot of the decoder is
`SlotSorted`) and the `#[hax_lib::refine]` `h_pts_needed : self.receiving_ct2.pts_needed = 80`
(= `(CIPHERTEXT2_SIZE + MACSIZE) / 2`), from which `h_decoded_len` (`msg.length = 160`) is
derived rather than assumed.  The resulting `decodedPost` is exactly the postcondition of
`decoded_message_spec`: `none` iff the decoder is complete or some slot lacks points; `some msg`
with `msg.length = 160` and `BytesDecode pd.pts pd.pts_needed msg.val 0` otherwise.

**Source**: spqr/src/v1/chunked/send_ek.rs (lines 195:4-227:5)
-/
@[step]
theorem recv_ct2_chunk_spec_concrete (self : EkSentCt1Received) (epoch : U64)
    (chunk : encoding.Chunk)
    (h_epoch : epoch = self.uc.epoch)
    (h_overflow : chunk.index * 16 + 16 ≤ Usize.max)
    (h_push_cap : ∀ (k : Nat), k < 16 →
      (self.receiving_ct2.pts[k]!).length + 17 ≤ Usize.max)
    (h_valid : PolyDecoder.PointsValid self.receiving_ct2.pts)
    (h_pts_needed : self.receiving_ct2.pts_needed.val = 80)
    (h_ct2_size : incremental_mlkem768.CIPHERTEXT2_SIZE ⦃ (r : Usize) => r.val = 128 ⦄)
    (h_dk : self.uc.dk.length = 2400)
    (h_ct1 : self.uc.ct1.length = 960)
    (h_uc_epoch : self.uc.epoch < U64.max)
    (h_root : self.uc.auth.root_key.length + 32 ≤ Usize.max) :
    recv_ct2_chunk self epoch chunk ⦃
      (result : core.result.Result EkSentCt1ReceivedRecvChunk Error) =>
      recvCt2ChunkPost self chunk
        (fun pd o =>
          pd.pts_needed.val = 80 ∧
          match o with
          | none => pd.is_complete = true ∨
              PolyDecoder.Insts.SpqrEncodingDecoder.someIncomplete pd.pts pd.pts_needed 0 16
          | some out => pd.is_complete = false ∧
              ¬ PolyDecoder.Insts.SpqrEncodingDecoder.someIncomplete pd.pts pd.pts_needed 0 16 ∧
              out.length = 2 * pd.pts_needed.val ∧
              PolyDecoder.Insts.SpqrEncodingDecoder.BytesDecode pd.pts pd.pts_needed out.val 0)
        result ⦄ := by
  apply recv_ct2_chunk_spec self epoch chunk _ h_epoch h_overflow h_push_cap h_valid
    _ _ h_ct2_size h_dk h_ct1 h_uc_epoch h_root
  · intro pd h_add h_pv
    have h_pn' : pd.pts_needed.val = 80 := by rw [h_add.1, h_pts_needed]
    apply WP.spec_mono (PolyDecoder.Insts.SpqrEncodingDecoder.decoded_message_spec pd h_pv
      (by rw [h_pn']; scalar_tac))
    intro o h
    exact ⟨h_pn', h⟩
  · intro pd msg h
    obtain ⟨h_pn', _, _, h_len, _⟩ := h
    rw [h_len, h_pn']

end spqr.v1.chunked.send_ek.EkSentCt1Received
