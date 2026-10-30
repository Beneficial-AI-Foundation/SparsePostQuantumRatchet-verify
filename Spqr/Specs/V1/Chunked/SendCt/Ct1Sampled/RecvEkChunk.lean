/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import SrcTranslated.Funs
public import Spqr.Specs.Encoding.Polynomial.PolyDecoder.AddChunk
public import Spqr.Specs.Encoding.Polynomial.PolyDecoder.DecodedMessage.DecodedMessage
public import Spqr.Specs.V1.Unchunked.SendCt.Ct1Sent.RecvEk
public import Spqr.Specs.V1.Unchunked.SendCt.Ct1SentEkReceived.SendCt2
public import Spqr.Specs.V1.Chunked.SendCt.SendCt2Encoder
import Spqr.Auxiliary.Aeneas.Vec
/-!
# Spec theorem for `spqr::v1::chunked::send_ct::{Ct1Sampled}::recv_ek_chunk`

`Ct1Sampled::recv_ek_chunk` processes a single incoming `ek` chunk and an acknowledgment flag
`ct1_ack`.  Depending on whether the decoder reconstructs `ek` and whether `ct1_ack` is set,
the function returns one of four `Ct1SampledRecvChunk` variants:
  – `StillReceivingStillSending` — neither ek decoded nor ct1 ack'd;
  – `StillReceiving` — ct1 ack'd but ek not yet decoded;
  – `StillSending` — ek decoded but ct1 not yet ack'd;
  – `Done` — both ek decoded and ct1 ack'd.

The main theorem `recv_ek_chunk_spec` follows the predicate-lifting style of
`Specs/Encoding/Decoder/DecodedMessage.lean`: it is parametrised by a postcondition
`decodedPost` for `PolyDecoder::decoded_message` on the updated decoder (hypothesis
`h_decoded`).  `h_decoded` is stated for every decoder that agrees with `self.receiving_ek` on
`pts_needed` and `is_complete` and whose slots are `PointsValid` — exactly what `add_chunk_spec`
and `add_chunk_spec_valid` guarantee about the updated decoder — so the registered
`decoded_message_spec` can be plugged in; `recv_ek_chunk_spec_concrete` does so.

**Source**: spqr/src/v1/chunked/send_ct.rs (lines 168:4-200:5)
-/

@[expose] public section

open Aeneas Aeneas.Std Result spqr encoding.polynomial encoding.gf Polynomial
  Spqr.IncrementalMlkem768

/- Helper definitions live in a CamelCase namespace (mirroring
`Spqr.V1.Unchunked.SendCt.Ct1Sent` in `RecvEk.lean`) so that their full names satisfy the
`defsWithUnderscore` linter; the spec theorems themselves stay in the Rust-mirroring
`spqr.v1.chunked.send_ct.Ct1Sampled` namespace. -/
namespace Spqr.V1.Chunked.SendCt.Ct1Sampled

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

open List core.num.U64 authenticator.Authenticator in
/-- Characterisation of the `Ct2Sampled` state `st` produced on the `Done` path, given the
unchunked state `uc : Ct1Sent` B started from and the decoded encapsulation key `ek`. -/
def doneSampledPost (uc : unchunked.send_ct.Ct1Sent) (ek : alloc.vec.Vec U8)
    (st : Ct2Sampled) : Prop :=
  st.uc.epoch = uc.epoch ∧
  st.uc.auth = uc.auth ∧
  ∃ (ct2 mac : alloc.vec.Vec U8),
    ct2.length = 128 ∧
    Encaps2Post ek uc.es ct2 ∧
    mac.length = MACSIZE.val ∧
    (∃ data : Slice U8,
      data.val = MAC_CT_LABEL ++ to_be_bytes uc.epoch ++ (uc.ct1.val ++ ct2.val) ∧
      libcrux_hmac.hmac .Sha256 uc.auth.mac_key.deref data (some MACSIZE) = ok mac) ∧
    st.sending_ct2.idx = 0#u32 ∧
    ∃ pts : Array Point 16#usize,
      st.sending_ct2.s = EncoderState.Points pts ∧
      (∀ (j : Nat), j < 16 → pts[j]!.value.length = 5) ∧
      (∀ (j : Nat), j < 16 →
        ∀ (k : Nat), k < 5 →
          let msg := ct2.val ++ mac.val
          2 * (j + 16 * k) + 1 < 160 ∧
          (listToGF216Poly pts[j]!.value).coeff k =
            (256 * msg[2 * (j + 16 * k)]! + (msg[2 * (j + 16 * k) + 1]!).val).toGF216)

/-- Postcondition of `Ct1Sampled::recv_ek_chunk` as a predicate on the returned
`core.result.Result`, parametrised by the postcondition `decodedPost` assumed for
`PolyDecoder::decoded_message` on the updated decoder.

The four `Ok` variants are:

  - **`StillReceivingStillSending st`** — `ct1_ack = false`, decoder yields `none`;
    unchunked state and encoder preserved, decoder advanced by `addChunkPost`.
  - **`StillReceiving st`** — `ct1_ack = true`, decoder yields `none`;
    unchunked state preserved, decoder advanced by `addChunkPost`.
  - **`StillSending st`** — `ct1_ack = false`, decoder yields `some ek` accepted;
    unchunked `recv_ek` produces `st.uc`, which is `self.uc` with `ek` stored
    (`epoch`, `auth`, `es`, `ct1` carried over unchanged, `st.uc.ek = ek`); encoder preserved.
  - **`Done st`** — `ct1_ack = true`, decoder yields `some ek` accepted;
    `doneSampledPost self.uc ek st`.

The `Err` case means some `ek` was decoded but rejected by `ek_matches_header`. -/
def recvEkChunkPost (self : Ct1Sampled) (chunk : encoding.Chunk) (ct1_ack : Bool)
    (decodedPost : PolyDecoder → Option (alloc.vec.Vec U8) → Prop)
    (result : core.result.Result Ct1SampledRecvChunk spqr.Error) : Prop :=
  match result with
  | .Ok (.StillReceivingStillSending st) =>
      ct1_ack = false ∧
      st.uc = self.uc ∧
      st.sending_ct1 = self.sending_ct1 ∧
      addChunkPost self.receiving_ek chunk st.receiving_ek ∧
      decodedPost st.receiving_ek none
  | .Ok (.StillReceiving st) =>
      ct1_ack = true ∧
      st.uc = self.uc ∧
      addChunkPost self.receiving_ek chunk st.receiving_ek ∧
      decodedPost st.receiving_ek none
  | .Ok (.StillSending st) =>
      ct1_ack = false ∧
      st.sending_ct1 = self.sending_ct1 ∧
      ∃ (pd : PolyDecoder) (ek : alloc.vec.Vec U8),
        addChunkPost self.receiving_ek chunk pd ∧
        decodedPost pd (some ek) ∧
        Spqr.V1.Unchunked.SendCt.Ct1Sent.ekAccepted self.uc ek ∧
        st.uc.epoch = self.uc.epoch ∧ st.uc.auth = self.uc.auth ∧
        st.uc.es = self.uc.es ∧ st.uc.ek = ek ∧ st.uc.ct1 = self.uc.ct1
  | .Ok (.Done st) =>
      ct1_ack = true ∧
      ∃ (pd : PolyDecoder) (ek : alloc.vec.Vec U8),
        addChunkPost self.receiving_ek chunk pd ∧
        decodedPost pd (some ek) ∧
        Spqr.V1.Unchunked.SendCt.Ct1Sent.ekAccepted self.uc ek ∧
        doneSampledPost self.uc ek st
  | .Err e =>
      ∃ (pd : PolyDecoder) (ek : alloc.vec.Vec U8),
        addChunkPost self.receiving_ek chunk pd ∧
        decodedPost pd (some ek) ∧
        ¬ Spqr.V1.Unchunked.SendCt.Ct1Sent.ekAccepted self.uc ek ∧
        e = spqr.Error.ErroneousDataReceived

end Spqr.V1.Chunked.SendCt.Ct1Sampled

namespace spqr.v1.chunked.send_ct.Ct1Sampled

open Spqr.V1.Chunked.SendCt.Ct1Sampled

/-- **Spec theorem for `spqr.v1.chunked.send_ct.Ct1Sampled.recv_ek_chunk`**:

• Takes a chunked `Ct1Sampled` state `self`, the epoch `epoch : U64` announced by the peer,
  a received 32-byte `chunk`, and the acknowledgment flag `ct1_ack : Bool`.
• Absorbs the chunk into the decoder via `add_chunk`, then queries `decoded_message`.
• If `decoded_message` returns `none`, the result depends on `ct1_ack`:
    – `false` → `StillReceivingStillSending` (state unchanged except decoder);
    – `true`  → `StillReceiving` (transition to `Ct1Acknowledged`).
• If `decoded_message` returns `some ek`, calls `recv_ek` on the unchunked state:
    – on `Err` the error is propagated;
    – on `Ok`, the result depends on `ct1_ack`:
        * `false` → `StillSending` (transition to `EkReceivedCt1Sampled`);
        * `true`  → `Done` (transition to `Ct2Sampled` via `send_ct2`).

• Requires:
    – `h_epoch : epoch = self.uc.epoch` — the hax precondition, discharging the `assert_eq!` in
      `recv_ek`;
    – `h_overflow`, `h_push_cap` — the `usize` guards of `add_chunk_spec`;
    – `h_valid` — every slot of `self.receiving_ek.pts` is `SlotSorted` (the `SortedSet`
      invariant of the Rust decoder), preserved by `add_chunk_spec_valid`;
    – `h_decoded` — the assumed behaviour of `decoded_message` on any decoder that agrees with
      `self.receiving_ek` on `pts_needed` and `is_complete` and is `PointsValid`, which is
      exactly what is known about the updated decoder; `recv_ek_chunk_spec_concrete`
      instantiates it with the registered `decoded_message_spec`;
    – `h_es`, `h_key`, `h_ct` — the length guards of `send_ct2_spec`.  The remaining guard
      `ek.length = 1152` is extracted from `ekAccepted self.uc ek` on the accepting path.

The result satisfies `recvEkChunkPost self chunk ct1_ack decodedPost result`.

**Source**: spqr/src/v1/chunked/send_ct.rs (lines 168:4-200:5)
-/
@[step]
theorem recv_ek_chunk_spec (self : Ct1Sampled) (epoch : U64) (chunk : encoding.Chunk)
    (ct1_ack : Bool)
    (decodedPost : PolyDecoder → Option (alloc.vec.Vec U8) → Prop)
    (h_epoch : epoch = self.uc.epoch)
    (h_overflow : chunk.index * 16 + 16 ≤ Usize.max)
    (h_push_cap : ∀ (k : Nat), k < 16 →
      (self.receiving_ek.pts[k]!).length + 17 ≤ Usize.max)
    (h_valid : PolyDecoder.PointsValid self.receiving_ek.pts)
    (h_decoded : ∀ (pd : PolyDecoder),
      pd.pts_needed = self.receiving_ek.pts_needed →
      pd.is_complete = self.receiving_ek.is_complete →
      PolyDecoder.PointsValid pd.pts →
      PolyDecoder.Insts.SpqrEncodingDecoder.decoded_message pd ⦃
        (o : Option (alloc.vec.Vec U8)) => decodedPost pd o ⦄)
    (h_es : self.uc.es.length = 2080)
    (h_key : self.uc.auth.mac_key.length ≤ U32.max)
    (h_ct : self.uc.ct1.length + 128 + 43 ≤ U32.max) :
    recv_ek_chunk self epoch chunk ct1_ack ⦃
      (result : core.result.Result Ct1SampledRecvChunk Error) =>
      recvEkChunkPost self chunk ct1_ack decodedPost result ⦄ := by
  unfold recv_ek_chunk
  step with WP.spec_and
    (PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk_spec self.receiving_ek chunk
      h_overflow h_push_cap)
    (PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk_spec_valid self.receiving_ek chunk
      h_overflow h_push_cap h_valid)
    as ⟨receiving_ek, h_pn, h_ic, selfs, h_s0, h_s16, h_chain, h_valid'⟩
  have h_add : addChunkPost self.receiving_ek chunk receiving_ek :=
    ⟨h_pn, h_ic, selfs, h_s0, h_s16, h_chain⟩
  step with h_decoded receiving_ek h_pn h_ic h_valid'
  cases o with
  | none =>
    cases ct1_ack with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok, recvEkChunkPost, true_and]
      exact ⟨h_add, o_post⟩
    | true =>
      simp only [↓reduceIte, WP.spec_ok, recvEkChunkPost, true_and]
      exact ⟨h_add, o_post⟩
  | some decoded =>
    step with unchunked.send_ct.Ct1Sent.recv_ek_spec self.uc epoch decoded h_epoch
    cases result with
    | Ok uc' =>
      obtain ⟨h_acc, h_ep, h_auth, h_es', h_ek', h_ct1'⟩ := result_post
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      cases ct1_ack with
      | true =>
        simp only [↓reduceIte]
        step with unchunked.send_ct.Ct1SentEkReceived.send_ct2_spec uc'
          (by rw [h_ek']; exact h_acc.2.1) (by rw [h_es']; exact h_es)
          (by rw [h_auth]; exact h_key) (by rw [h_ct1']; exact h_ct)
          as ⟨uc, ct2, mac, h_uc_ep, h_uc_auth, h_ct2_len, h_enc, h_mac_len, data, h_data,
            h_hmac⟩
        step with send_ct2_encoder_spec (alloc.vec.Vec.deref ct2) (alloc.vec.Vec.deref mac)
          (by simpa [Slice.length, alloc.vec.Vec.deref_val] using h_ct2_len)
          (by simpa [Slice.length, alloc.vec.Vec.deref_val] using h_mac_len)
          as ⟨pe, h_idx, pts, h_s, h_lens, h_coeffs⟩
        simp only [recvEkChunkPost, true_and]
        refine ⟨receiving_ek, decoded, h_add, o_post, h_acc,
          h_uc_ep.trans h_ep, h_uc_auth.trans h_auth, ct2, mac, h_ct2_len, ?_, h_mac_len,
          ⟨data, ?_, ?_⟩, h_idx, pts, h_s, h_lens, ?_⟩
        · rw [h_ek', h_es'] at h_enc; exact h_enc
        · rw [h_data, h_ep, h_ct1']
        · rw [h_auth] at h_hmac; exact h_hmac
        · intro j hj k hk
          have := h_coeffs j hj k hk
          simpa only [alloc.vec.Vec.deref_val] using this
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok, recvEkChunkPost, true_and]
        exact ⟨receiving_ek, decoded, h_add, o_post, h_acc, h_ep, h_auth, h_es', h_ek', h_ct1'⟩
    | Err e =>
      obtain ⟨h_rej, h_e⟩ := result_post
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok, WP.spec_ok, recvEkChunkPost]
      exact ⟨receiving_ek, decoded, h_add, o_post, h_rej, h_e⟩

/-- **Spec theorem** (still-receiving-still-sending case):
`decoded_message` returns `none` and `ct1_ack = false`.
Projection of `recv_ek_chunk_spec` with `decodedPost := fun _ o => o = none`.

**Source**: spqr/src/v1/chunked/send_ct.rs (lines 168:4-200:5)
-/
theorem recv_ek_chunk_spec_still_receiving_still_sending
    (self : Ct1Sampled) (epoch : U64) (chunk : encoding.Chunk)
    (h_epoch : epoch = self.uc.epoch)
    (h_overflow : chunk.index * 16 + 16 ≤ Usize.max)
    (h_push_cap : ∀ (k : Nat), k < 16 →
      (self.receiving_ek.pts[k]!).length + 17 ≤ Usize.max)
    (h_valid : PolyDecoder.PointsValid self.receiving_ek.pts)
    (h_decoded_none : ∀ (pd : PolyDecoder),
      pd.pts_needed = self.receiving_ek.pts_needed →
      pd.is_complete = self.receiving_ek.is_complete →
      PolyDecoder.PointsValid pd.pts →
      PolyDecoder.Insts.SpqrEncodingDecoder.decoded_message pd ⦃
        (o : Option (alloc.vec.Vec U8)) => o = none ⦄)
    (h_es : self.uc.es.length = 2080)
    (h_key : self.uc.auth.mac_key.length ≤ U32.max)
    (h_ct : self.uc.ct1.length + 128 + 43 ≤ U32.max) :
    recv_ek_chunk self epoch chunk false ⦃
      (result : core.result.Result Ct1SampledRecvChunk Error) =>
      ∃ st : Ct1Sampled,
        result = .Ok (.StillReceivingStillSending st) ∧
        st.uc = self.uc ∧
        st.sending_ct1 = self.sending_ct1 ∧
        addChunkPost self.receiving_ek chunk st.receiving_ek ⦄ := by
  apply WP.spec_mono (recv_ek_chunk_spec self epoch chunk false (fun _ o => o = none)
    h_epoch h_overflow h_push_cap h_valid h_decoded_none h_es h_key h_ct)
  intro result h
  match result with
  | .Ok (.StillReceivingStillSending st) =>
    exact ⟨st, rfl, h.2.1, h.2.2.1, h.2.2.2.1⟩
  | .Ok (.StillReceiving _) => exact absurd h.1 (by simp)
  | .Ok (.StillSending _) =>
    obtain ⟨_, _, _, h_none, _⟩ := h.2.2; exact (Option.some_ne_none _ h_none).elim
  | .Ok (.Done _) =>
    obtain ⟨_, _, _, h_none, _⟩ := h.2; exact (Option.some_ne_none _ h_none).elim
  | .Err _ =>
    obtain ⟨_, _, _, h_none, _⟩ := h; exact (Option.some_ne_none _ h_none).elim

/-- **Spec theorem** (still-receiving case):
`decoded_message` returns `none` and `ct1_ack = true`.
Projection of `recv_ek_chunk_spec`.

**Source**: spqr/src/v1/chunked/send_ct.rs (lines 168:4-200:5)
-/
theorem recv_ek_chunk_spec_still_receiving
    (self : Ct1Sampled) (epoch : U64) (chunk : encoding.Chunk)
    (h_epoch : epoch = self.uc.epoch)
    (h_overflow : chunk.index * 16 + 16 ≤ Usize.max)
    (h_push_cap : ∀ (k : Nat), k < 16 →
      (self.receiving_ek.pts[k]!).length + 17 ≤ Usize.max)
    (h_valid : PolyDecoder.PointsValid self.receiving_ek.pts)
    (h_decoded_none : ∀ (pd : PolyDecoder),
      pd.pts_needed = self.receiving_ek.pts_needed →
      pd.is_complete = self.receiving_ek.is_complete →
      PolyDecoder.PointsValid pd.pts →
      PolyDecoder.Insts.SpqrEncodingDecoder.decoded_message pd ⦃
        (o : Option (alloc.vec.Vec U8)) => o = none ⦄)
    (h_es : self.uc.es.length = 2080)
    (h_key : self.uc.auth.mac_key.length ≤ U32.max)
    (h_ct : self.uc.ct1.length + 128 + 43 ≤ U32.max) :
    recv_ek_chunk self epoch chunk true ⦃
      (result : core.result.Result Ct1SampledRecvChunk Error) =>
      ∃ st : Ct1Acknowledged,
        result = .Ok (.StillReceiving st) ∧
        st.uc = self.uc ∧
        addChunkPost self.receiving_ek chunk st.receiving_ek ⦄ := by
  apply WP.spec_mono (recv_ek_chunk_spec self epoch chunk true (fun _ o => o = none)
    h_epoch h_overflow h_push_cap h_valid h_decoded_none h_es h_key h_ct)
  intro result h
  match result with
  | .Ok (.StillReceiving st) =>
    exact ⟨st, rfl, h.2.1, h.2.2.1⟩
  | .Ok (.StillReceivingStillSending _) => exact absurd h.1 (by simp)
  | .Ok (.StillSending _) =>
    obtain ⟨_, _, _, h_none, _⟩ := h.2.2; exact (Option.some_ne_none _ h_none).elim
  | .Ok (.Done _) =>
    obtain ⟨_, _, _, h_none, _⟩ := h.2; exact (Option.some_ne_none _ h_none).elim
  | .Err _ =>
    obtain ⟨_, _, _, h_none, _⟩ := h; exact (Option.some_ne_none _ h_none).elim

/-- **Spec theorem** (done case):
`decoded_message` returns `some ek` with `ekAccepted` and `ct1_ack = true`.
Projection of `recv_ek_chunk_spec`.

**Source**: spqr/src/v1/chunked/send_ct.rs (lines 168:4-200:5)
-/
theorem recv_ek_chunk_spec_done
    (self : Ct1Sampled) (epoch : U64) (chunk : encoding.Chunk)
    (h_epoch : epoch = self.uc.epoch)
    (h_overflow : chunk.index * 16 + 16 ≤ Usize.max)
    (h_push_cap : ∀ (k : Nat), k < 16 →
      (self.receiving_ek.pts[k]!).length + 17 ≤ Usize.max)
    (h_valid : PolyDecoder.PointsValid self.receiving_ek.pts)
    (h_decoded_some : ∀ (pd : PolyDecoder),
      pd.pts_needed = self.receiving_ek.pts_needed →
      pd.is_complete = self.receiving_ek.is_complete →
      PolyDecoder.PointsValid pd.pts →
      PolyDecoder.Insts.SpqrEncodingDecoder.decoded_message pd ⦃
        (o : Option (alloc.vec.Vec U8)) =>
          ∃ ek, o = some ek ∧ Spqr.V1.Unchunked.SendCt.Ct1Sent.ekAccepted self.uc ek ⦄)
    (h_es : self.uc.es.length = 2080)
    (h_key : self.uc.auth.mac_key.length ≤ U32.max)
    (h_ct : self.uc.ct1.length + 128 + 43 ≤ U32.max) :
    recv_ek_chunk self epoch chunk true ⦃
      (result : core.result.Result Ct1SampledRecvChunk Error) =>
      ∃ (st : Ct2Sampled) (ek : alloc.vec.Vec U8),
        result = .Ok (.Done st) ∧
        Spqr.V1.Unchunked.SendCt.Ct1Sent.ekAccepted self.uc ek ∧
        doneSampledPost self.uc ek st ⦄ := by
  apply WP.spec_mono (recv_ek_chunk_spec self epoch chunk true
    (fun _ o => ∃ ek, o = some ek ∧ Spqr.V1.Unchunked.SendCt.Ct1Sent.ekAccepted self.uc ek)
    h_epoch h_overflow h_push_cap h_valid h_decoded_some h_es h_key h_ct)
  intro result h
  match result with
  | .Ok (.Done st) =>
    obtain ⟨_, pd, ek, _, ⟨ek', h_eq, h_acc'⟩, h_acc, h_done⟩ := h
    simp only [Option.some.injEq] at h_eq; subst h_eq
    exact ⟨st, ek, rfl, h_acc, h_done⟩
  | .Ok (.StillReceivingStillSending _) => exact absurd h.1 (by simp)
  | .Ok (.StillReceiving _) =>
    obtain ⟨_, _, _, ⟨ek, h_eq, _⟩⟩ := h
    exact absurd h_eq (by simp)
  | .Ok (.StillSending _) => exact absurd h.1 (by simp)
  | .Err _ =>
    obtain ⟨pd, ek, _, ⟨ek', h_eq, h_acc'⟩, h_rej, _⟩ := h
    simp only [Option.some.injEq] at h_eq; subst h_eq
    exact absurd h_acc' h_rej

/-- **Spec theorem** (still-sending case):
`decoded_message` returns `some ek` with `ekAccepted` and `ct1_ack = false`.
Projection of `recv_ek_chunk_spec`.

**Source**: spqr/src/v1/chunked/send_ct.rs (lines 168:4-200:5)
-/
theorem recv_ek_chunk_spec_still_sending
    (self : Ct1Sampled) (epoch : U64) (chunk : encoding.Chunk)
    (h_epoch : epoch = self.uc.epoch)
    (h_overflow : chunk.index * 16 + 16 ≤ Usize.max)
    (h_push_cap : ∀ (k : Nat), k < 16 →
      (self.receiving_ek.pts[k]!).length + 17 ≤ Usize.max)
    (h_valid : PolyDecoder.PointsValid self.receiving_ek.pts)
    (h_decoded_some : ∀ (pd : PolyDecoder),
      pd.pts_needed = self.receiving_ek.pts_needed →
      pd.is_complete = self.receiving_ek.is_complete →
      PolyDecoder.PointsValid pd.pts →
      PolyDecoder.Insts.SpqrEncodingDecoder.decoded_message pd ⦃
        (o : Option (alloc.vec.Vec U8)) =>
          ∃ ek, o = some ek ∧ Spqr.V1.Unchunked.SendCt.Ct1Sent.ekAccepted self.uc ek ⦄)
    (h_es : self.uc.es.length = 2080)
    (h_key : self.uc.auth.mac_key.length ≤ U32.max)
    (h_ct : self.uc.ct1.length + 128 + 43 ≤ U32.max) :
    recv_ek_chunk self epoch chunk false ⦃
      (result : core.result.Result Ct1SampledRecvChunk Error) =>
      ∃ (st : EkReceivedCt1Sampled) (ek : alloc.vec.Vec U8),
        result = .Ok (.StillSending st) ∧
        Spqr.V1.Unchunked.SendCt.Ct1Sent.ekAccepted self.uc ek ∧
        st.sending_ct1 = self.sending_ct1 ∧
        st.uc.epoch = self.uc.epoch ∧
        st.uc.auth = self.uc.auth ∧
        st.uc.es = self.uc.es ∧
        st.uc.ek = ek ∧
        st.uc.ct1 = self.uc.ct1 ⦄ := by
  apply WP.spec_mono (recv_ek_chunk_spec self epoch chunk false
    (fun _ o => ∃ ek, o = some ek ∧ Spqr.V1.Unchunked.SendCt.Ct1Sent.ekAccepted self.uc ek)
    h_epoch h_overflow h_push_cap h_valid h_decoded_some h_es h_key h_ct)
  intro result h
  match result with
  | .Ok (.StillSending st) =>
    obtain ⟨_, h_ct1, pd, ek, _, ⟨ek', h_eq, h_acc'⟩, h_acc, h_ep, h_auth, h_es', h_ek', h_ct1'⟩
      := h
    simp only [Option.some.injEq] at h_eq; subst h_eq
    exact ⟨st, ek, rfl, h_acc, h_ct1, h_ep, h_auth, h_es', h_ek', h_ct1'⟩
  | .Ok (.StillReceivingStillSending _) =>
    obtain ⟨_, _, _, _, ⟨ek, h_eq, _⟩⟩ := h
    exact absurd h_eq (by simp)
  | .Ok (.StillReceiving _) => exact absurd h.1 (by simp)
  | .Ok (.Done _) => exact absurd h.1 (by simp)
  | .Err _ =>
    obtain ⟨pd, ek, _, ⟨ek', h_eq, h_acc'⟩, h_rej, _⟩ := h
    simp only [Option.some.injEq] at h_eq; subst h_eq
    exact absurd h_acc' h_rej

/-- **Spec theorem for `spqr.v1.chunked.send_ct.Ct1Sampled.recv_ek_chunk`**
(concrete `decoded_message` semantics):

Instantiation of `recv_ek_chunk_spec` with the registered `decoded_message_spec` instead of a
lifted `decodedPost`.  Besides the hypotheses shared with `recv_ek_chunk_spec`, it assumes the
`#[hax_lib::refine]` struct invariant of the Rust `Ct1Sampled`,
`h_pts_needed : self.receiving_ek.pts_needed = 576` (= `ENCAPSULATION_KEY_SIZE / 2`), which
discharges the output-capacity guard `2 * pts_needed ≤ Usize.max` of `decoded_message_spec`.
The resulting `decodedPost` is exactly the postcondition of `decoded_message_spec`: `none` iff
the decoder is complete or some slot lacks points; `some ek` with `ek.length = 1152` and
`BytesDecode pd.pts pd.pts_needed ek.val 0` otherwise.

**Source**: spqr/src/v1/chunked/send_ct.rs (lines 168:4-200:5)
-/
theorem recv_ek_chunk_spec_concrete (self : Ct1Sampled) (epoch : U64) (chunk : encoding.Chunk)
    (ct1_ack : Bool)
    (h_epoch : epoch = self.uc.epoch)
    (h_overflow : chunk.index * 16 + 16 ≤ Usize.max)
    (h_push_cap : ∀ (k : Nat), k < 16 →
      (self.receiving_ek.pts[k]!).length + 17 ≤ Usize.max)
    (h_valid : PolyDecoder.PointsValid self.receiving_ek.pts)
    (h_pts_needed : self.receiving_ek.pts_needed.val = 576)
    (h_es : self.uc.es.length = 2080)
    (h_key : self.uc.auth.mac_key.length ≤ U32.max)
    (h_ct : self.uc.ct1.length + 128 + 43 ≤ U32.max) :
    recv_ek_chunk self epoch chunk ct1_ack ⦃
      (result : core.result.Result Ct1SampledRecvChunk Error) =>
      recvEkChunkPost self chunk ct1_ack
        (fun pd o =>
          pd.pts_needed.val = 576 ∧
          match o with
          | none => pd.is_complete = true ∨
              PolyDecoder.Insts.SpqrEncodingDecoder.someIncomplete pd.pts pd.pts_needed 0 16
          | some out => pd.is_complete = false ∧
              ¬ PolyDecoder.Insts.SpqrEncodingDecoder.someIncomplete pd.pts pd.pts_needed 0 16 ∧
              out.length = 2 * pd.pts_needed.val ∧
              PolyDecoder.Insts.SpqrEncodingDecoder.BytesDecode pd.pts pd.pts_needed out.val 0)
        result ⦄ := by
  apply recv_ek_chunk_spec self epoch chunk ct1_ack _ h_epoch h_overflow h_push_cap h_valid
    _ h_es h_key h_ct
  intro pd h_pn _ h_pv
  have h_pn' : pd.pts_needed.val = 576 := by rw [h_pn, h_pts_needed]
  apply WP.spec_mono (PolyDecoder.Insts.SpqrEncodingDecoder.decoded_message_spec pd h_pv
    (by rw [h_pn']; scalar_tac))
  intro o h
  exact ⟨h_pn', h⟩

end spqr.v1.chunked.send_ct.Ct1Sampled
