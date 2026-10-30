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
# Spec theorem for `spqr::v1::chunked::send_ct::{Ct1Acknowledged}::recv_ek_chunk`

`Ct1Acknowledged` is the state of the ciphertext-sending (B→A) side of the *chunked* V1
ratchet after the first ciphertext `ct1` has been fully delivered and acknowledged by A, while
B is still receiving the remaining chunks of A's encapsulation key `ek`.  It wraps the
unchunked state `Ct1Sent` (carrying the current `epoch : u64`, the `Authenticator`, the ML-KEM
header `hdr`, the encapsulation state `es` and `ct1`) and adds a `PolyDecoder` that
erasure-decodes the incoming chunks of `ek`.

`Ct1Acknowledged::recv_ek_chunk` is the only transition out of this state.  On receipt of a
32-byte `Chunk` it:

  1. feeds the chunk to the decoder (`receiving_ek.add_chunk(chunk)`), which routes each of the
     16 big-endian GF(2¹⁶) symbols of the chunk to polynomial `j` at x-coordinate `chunk.index`
     and inserts the resulting point into the corresponding sorted set — unless that polynomial
     already holds enough points;
  2. asks the decoder for the reassembled message (`receiving_ek.decoded_message()`):
       • **`None`** — `ek` is not yet recoverable; the state is rebuilt with the updated decoder
         and returned as `StillReceiving`;
       • **`Some(ek)`** — the full 1152-byte encapsulation key has been reconstructed.  The
         unchunked `Ct1Sent::recv_ek` checks it against the header B already acted upon
         (`ek_matches_header`); on mismatch the `?` operator propagates
         `Err(ErroneousDataReceived)`.  Otherwise `Ct1SentEkReceived::send_ct2` completes the
         encapsulation (`encaps2`) producing the 128-byte second ciphertext half `ct2` and the
         32-byte HMAC `mac` over `ct1 ‖ ct2`, and `send_ct2_encoder(&ct2, &mac)` erasure-codes
         `ct2 ‖ mac` into a fresh `PolyEncoder`.  The result is `Done(Ct2Sampled { uc,
         sending_ct2 })`.

The hax contract `requires(epoch == self.uc.epoch)` discharges the `assert_eq!` inside
`recv_ek`.  The struct refinement `receiving_ek.get_pts_needed() == ENCAPSULATION_KEY_SIZE / 2`
(`pts_needed = 576`) is assumed only by `recv_ek_chunk_spec_concrete`, where it discharges the
output-capacity guard of `decoded_message_spec` and pins the decoded length to `2 · 576`; in the
lifted `recv_ek_chunk_spec` the bound `ek.length = 1152` needed by `send_ct2` is instead
obtained from `ekAccepted` on the accepting path.

The main theorem follows the predicate-lifting pattern of
`Specs/Encoding/Decoder/DecodedMessage.lean`: it is parametrised by a postcondition
`decodedPost` for `decoded_message`, taken as the hypothesis `h_decoded`, and threads it through
to every branch of the result.  `h_decoded` is stated for every decoder that agrees with
`self.receiving_ek` on `pts_needed` and `is_complete` and is `PointsValid` — exactly what
`add_chunk_spec` and `add_chunk_spec_valid` guarantee about the updated decoder — so the
registered `decoded_message_spec` can be plugged in; `recv_ek_chunk_spec_concrete` does so.
All other callees (`add_chunk`, `recv_ek`, `send_ct2`, `send_ct2_encoder`) are discharged by
their registered specs.

**Source**: spqr/src/v1/chunked/send_ct.rs (lines 259:4-279:5)
-/

@[expose] public section

open Aeneas Aeneas.Std Result spqr encoding.polynomial encoding.gf Polynomial
  Spqr.IncrementalMlkem768

/- Helper definitions live in a CamelCase namespace (mirroring
`Spqr.V1.Unchunked.SendCt.Ct1Sent` in `RecvEk.lean`) so that their full names satisfy the
`defsWithUnderscore` linter; the spec theorems themselves stay in the Rust-mirroring
`spqr.v1.chunked.send_ct.Ct1Acknowledged` namespace. -/
namespace Spqr.V1.Chunked.SendCt.Ct1Acknowledged

open spqr spqr.v1 spqr.v1.chunked spqr.v1.chunked.send_ct

/-- Postcondition of `PolyDecoder::add_chunk` as a relation between the decoder before (`pd0`)
and after (`pd`) absorbing `chunk`.  Abbreviation for the shared
`PolyDecoder.Insts.SpqrEncodingDecoder.AddChunkPost` defined next to `add_chunk_spec`, so that
the two cannot drift apart. -/
abbrev addChunkPost (pd0 : PolyDecoder) (chunk : encoding.Chunk) (pd : PolyDecoder) : Prop :=
  PolyDecoder.Insts.SpqrEncodingDecoder.AddChunkPost pd0 chunk pd

open List core.num.U64 authenticator.Authenticator in
/-- Characterisation of the `Ct2Sampled` state `st` produced on the `Done` path, given the
unchunked state `uc : Ct1Sent` B started from and the decoded encapsulation key `ek`:

  - the epoch and authenticator are carried over: `st.uc.epoch = uc.epoch`,
    `st.uc.auth = uc.auth`;
  - there exist the second ciphertext half `ct2` (128 bytes, `Encaps2Post ek uc.es ct2`, i.e.
    FIPS 203 round 2 of the incremental encapsulation against `ek` and the stored state `es`)
    and the tag `mac` (`MACSIZE` bytes, equal to
    `HMAC-SHA256(uc.auth.mac_key, MAC_CT_LABEL ‖ be(uc.epoch) ‖ ct1 ‖ ct2)`);
  - `st.sending_ct2` is the freshly built encoder of `send_ct2_encoder ct2 mac`: index `0`,
    `Points` phase, every one of the 16 points holding exactly 5 symbols, with coefficient `k`
    of point `j` being the big-endian byte pair at offset `2·(j + 16·k)` of `ct2 ‖ mac`. -/
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

/-- Postcondition of `Ct1Acknowledged::recv_ek_chunk` as a predicate on the returned
`core.result.Result`, parametrised by the postcondition `decodedPost` assumed for
`PolyDecoder::decoded_message` on the updated decoder:

  - **`Ok (StillReceiving st)`** — the decoder did not yet yield a message
    (`decodedPost st.receiving_ek none`); the unchunked state is untouched
    (`st.uc = self.uc`) and `st.receiving_ek` is `self.receiving_ek` with `chunk` absorbed
    (`addChunkPost self.receiving_ek chunk st.receiving_ek`).
  - **`Ok (Done st)`** — some updated decoder `pd` with `addChunkPost self.receiving_ek chunk pd`
    yielded `some ek` (`decodedPost pd (some ek)`); `ek` was accepted against the header
    (`ekAccepted self.uc ek`, in particular `ek.length = 1152`), and `st` satisfies
    `doneSampledPost self.uc ek st`.
  - **`Err e`** — as in the `Done` case a key `ek` was decoded, but it was rejected
    (`¬ ekAccepted self.uc ek`) and `e = ErroneousDataReceived`. -/
def recvEkChunkPost (self : Ct1Acknowledged) (chunk : encoding.Chunk)
    (decodedPost : PolyDecoder → Option (alloc.vec.Vec U8) → Prop)
    (result : core.result.Result Ct1AcknowledgedRecvChunk spqr.Error) : Prop :=
  match result with
  | core.result.Result.Ok (Ct1AcknowledgedRecvChunk.StillReceiving st) =>
      st.uc = self.uc ∧
      addChunkPost self.receiving_ek chunk st.receiving_ek ∧
      decodedPost st.receiving_ek none
  | core.result.Result.Ok (Ct1AcknowledgedRecvChunk.Done st) =>
      ∃ (pd : PolyDecoder) (ek : alloc.vec.Vec U8),
        addChunkPost self.receiving_ek chunk pd ∧
        decodedPost pd (some ek) ∧
        Spqr.V1.Unchunked.SendCt.Ct1Sent.ekAccepted self.uc ek ∧
        doneSampledPost self.uc ek st
  | core.result.Result.Err e =>
      ∃ (pd : PolyDecoder) (ek : alloc.vec.Vec U8),
        addChunkPost self.receiving_ek chunk pd ∧
        decodedPost pd (some ek) ∧
        ¬ Spqr.V1.Unchunked.SendCt.Ct1Sent.ekAccepted self.uc ek ∧
        e = spqr.Error.ErroneousDataReceived

end Spqr.V1.Chunked.SendCt.Ct1Acknowledged

namespace spqr.v1.chunked.send_ct.Ct1Acknowledged

open Spqr.V1.Chunked.SendCt.Ct1Acknowledged

/-- **Spec theorem for `spqr.v1.chunked.send_ct.Ct1Acknowledged.recv_ek_chunk`**:

• Takes a chunked `Ct1Acknowledged` state `self`, consisting of the unchunked inner state
  `self.uc : unchunked.send_ct.Ct1Sent` and the chunk decoder
  `self.receiving_ek : PolyDecoder`, the epoch `epoch : U64` announced by the peer, and the
  received 32-byte `chunk`.  In the original Rust source `self` is consumed by value and
  `chunk` is passed by shared reference; after Aeneas extraction both are plain values.
• Absorbs the chunk into the decoder:
    `PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk self.receiving_ek chunk`
  obtaining `receiving_ek` with `addChunkPost self.receiving_ek chunk receiving_ek`.
• Queries `PolyDecoder.Insts.SpqrEncodingDecoder.decoded_message receiving_ek`, obtaining
  `o : Option (Vec U8)` with `decodedPost receiving_ek o`.
• If `o = none`, returns `Ok (StillReceiving { self with receiving_ek })`.
• If `o = some ek`, calls `unchunked.send_ct.Ct1Sent.recv_ek self.uc epoch ek`:
    – on `Err e` the `?` operator (`branch` / `from_residual` with the identity `From`
      instance) returns `Err e`, where `e = ErroneousDataReceived`;
    – on `Ok uc'` it calls `unchunked.send_ct.Ct1SentEkReceived.send_ct2 uc'` to obtain
      `(uc, ct2, mac)`, builds `send_ct2_encoder (Vec.deref ct2) (Vec.deref mac)`, and returns
      `Ok (Done { uc, sending_ct2 })`.

• Requires:
    – `h_epoch : epoch = self.uc.epoch` — the hax precondition, discharging the `assert_eq!` in
      `recv_ek`;
    – `h_overflow`, `h_push_cap` — the `usize` guards of `add_chunk_spec`: the base index
      `chunk.index * 16 + 16` fits, and each of the 16 sorted sets has room for 16 more points;
    – `h_valid` — every slot of `self.receiving_ek.pts` is `SlotSorted` (the `SortedSet`
      invariant of the Rust decoder), preserved by `add_chunk_spec_valid`;
    – `h_decoded` — the assumed behaviour of `decoded_message` on any decoder that agrees with
      `self.receiving_ek` on `pts_needed` and `is_complete` and is `PointsValid` (which is all
      `add_chunk_spec` / `add_chunk_spec_valid` guarantee about the shape of the updated
      decoder).  In particular it must assert totality; everything else it asserts is forwarded
      verbatim through `decodedPost`.  `recv_ek_chunk_spec_concrete` instantiates it with the
      registered `decoded_message_spec`;
    – `h_es`, `h_key`, `h_ct` — the length guards of `send_ct2_spec` on the stored
      encapsulation state, MAC key and `ct1`.  The remaining guard `ek.length = 1152` is *not*
      assumed: it is extracted from `ekAccepted self.uc ek` on the accepting path.
  Under these hypotheses the call never panics.
• The chunked wrapper introduces no epoch of its own: on both the `StillReceiving` and the
  `Done` path the epoch (and the authenticator) of the resulting state is that of `self.uc`.

The result satisfies the postcondition `recvEkChunkPost self chunk decodedPost result`.

This lifted form is not registered with `@[step]`: `step*` cannot synthesise `decodedPost` or
`h_decoded`.  The registered entry point is `recv_ek_chunk_spec_concrete` below; use this
theorem via `step with` when a custom `decodedPost` is wanted.

The proof unfolds `recv_ek_chunk`, applies `add_chunk_spec` and the assumed `h_decoded`, splits
on the decoded option, applies `recv_ek_spec` and splits on its `Result`; the `Ok` branch
reduces `branch` to `Continue`, applies `send_ct2_spec` (deriving `ek.length = 1152` from
`ekAccepted`) and `send_ct2_encoder_spec`, and the `Err` branch reduces `branch` /
`from_residual` to the propagated error.

**Source**: spqr/src/v1/chunked/send_ct.rs (lines 259:4-279:5)
-/
theorem recv_ek_chunk_spec (self : Ct1Acknowledged) (epoch : U64) (chunk : encoding.Chunk)
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
    recv_ek_chunk self epoch chunk ⦃
      (result : core.result.Result Ct1AcknowledgedRecvChunk Error) =>
      recvEkChunkPost self chunk decodedPost result ⦄ := by
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
    simp only [WP.spec_ok, recvEkChunkPost, true_and]
    exact ⟨h_add, o_post⟩
  | some decoded =>
    step with unchunked.send_ct.Ct1Sent.recv_ek_spec self.uc epoch decoded h_epoch
    cases result with
    | Ok uc' =>
      obtain ⟨h_acc, h_ep, h_auth, h_es', h_ek', h_ct1'⟩ := result_post
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      step with unchunked.send_ct.Ct1SentEkReceived.send_ct2_spec uc'
        (by rw [h_ek']; exact h_acc.2.1) (by rw [h_es']; exact h_es)
        (by rw [h_auth]; exact h_key) (by rw [h_ct1']; exact h_ct)
        as ⟨uc, ct2, mac, h_uc_ep, h_uc_auth, h_ct2_len, h_enc, h_mac_len, data, h_data,
          h_hmac⟩
      step with send_ct2_encoder_spec (alloc.vec.Vec.deref ct2) (alloc.vec.Vec.deref mac)
        (by simpa [Slice.length, alloc.vec.Vec.deref_val] using h_ct2_len)
        (by simpa [Slice.length, alloc.vec.Vec.deref_val] using h_mac_len)
        as ⟨pe, h_idx, pts, h_s, h_lens, h_coeffs⟩
      simp only [recvEkChunkPost]
      refine ⟨receiving_ek, decoded, h_add, o_post, h_acc,
        h_uc_ep.trans h_ep, h_uc_auth.trans h_auth, ct2, mac, h_ct2_len, ?_, h_mac_len,
        ⟨data, ?_, ?_⟩, h_idx, pts, h_s, h_lens, ?_⟩
      · rw [h_ek', h_es'] at h_enc; exact h_enc
      · rw [h_data, h_ep, h_ct1']
      · rw [h_auth] at h_hmac; exact h_hmac
      · intro j hj k hk
        have := h_coeffs j hj k hk
        simpa only [alloc.vec.Vec.deref_val] using this
    | Err e =>
      obtain ⟨h_rej, h_e⟩ := result_post
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok, WP.spec_ok, recvEkChunkPost]
      exact ⟨receiving_ek, decoded, h_add, o_post, h_rej, h_e⟩

/-- **Spec theorem for `spqr.v1.chunked.send_ct.Ct1Acknowledged.recv_ek_chunk`**
(still-receiving case):

If the updated decoder does not yet yield a message (`decoded_message` returns `none`), the
call returns `Ok (StillReceiving st)` with `st.uc = self.uc` and the decoder advanced by
`addChunkPost`.  Projection of `recv_ek_chunk_spec` with `decodedPost := fun _ o => o = none`.

**Source**: spqr/src/v1/chunked/send_ct.rs (lines 259:4-279:5)
-/
theorem recv_ek_chunk_spec_still_receiving (self : Ct1Acknowledged) (epoch : U64)
    (chunk : encoding.Chunk)
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
    recv_ek_chunk self epoch chunk ⦃
      (result : core.result.Result Ct1AcknowledgedRecvChunk Error) =>
      ∃ st : Ct1Acknowledged,
        result = core.result.Result.Ok (Ct1AcknowledgedRecvChunk.StillReceiving st) ∧
        st.uc = self.uc ∧
        addChunkPost self.receiving_ek chunk st.receiving_ek ⦄ := by
  apply WP.spec_mono (recv_ek_chunk_spec self epoch chunk (fun _ o => o = none) h_epoch
    h_overflow h_push_cap h_valid h_decoded_none h_es h_key h_ct)
  intro result h
  match result with
  | .Ok (.StillReceiving st) => exact ⟨st, rfl, h.1, h.2.1⟩
  | .Ok (.Done _) => obtain ⟨_, _, _, h_none, _⟩ := h; exact absurd h_none (by simp)
  | .Err _ => obtain ⟨_, _, _, h_none, _⟩ := h; exact absurd h_none (by simp)

/-- **Spec theorem for `spqr.v1.chunked.send_ct.Ct1Acknowledged.recv_ek_chunk`**
(decoded-and-accepted case):

If the updated decoder yields a message (`decoded_message` returns `some ek`) and every such
`ek` is accepted against the header (`ekAccepted self.uc ek`), the call returns `Ok (Done st)`
with `doneSampledPost self.uc ek st`.  Projection of `recv_ek_chunk_spec` with
`decodedPost := fun _ o => ∃ ek, o = some ek ∧ ekAccepted self.uc ek`.

**Source**: spqr/src/v1/chunked/send_ct.rs (lines 259:4-279:5)
-/
theorem recv_ek_chunk_spec_done (self : Ct1Acknowledged) (epoch : U64)
    (chunk : encoding.Chunk)
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
    recv_ek_chunk self epoch chunk ⦃
      (result : core.result.Result Ct1AcknowledgedRecvChunk Error) =>
      ∃ (st : Ct2Sampled) (ek : alloc.vec.Vec U8),
        result = core.result.Result.Ok (Ct1AcknowledgedRecvChunk.Done st) ∧
        Spqr.V1.Unchunked.SendCt.Ct1Sent.ekAccepted self.uc ek ∧
        doneSampledPost self.uc ek st ⦄ := by
  apply WP.spec_mono (recv_ek_chunk_spec self epoch chunk
    (fun _ o => ∃ ek, o = some ek ∧ Spqr.V1.Unchunked.SendCt.Ct1Sent.ekAccepted self.uc ek)
    h_epoch h_overflow h_push_cap h_valid h_decoded_some h_es h_key h_ct)
  intro result h
  match result with
  | .Ok (.StillReceiving _) =>
    obtain ⟨_, _, _, h_eq, _⟩ := h
    exact absurd h_eq (by simp)
  | .Ok (.Done st) =>
    obtain ⟨_, ek, _, _, h_acc, h_done⟩ := h
    exact ⟨st, ek, rfl, h_acc, h_done⟩
  | .Err _ =>
    obtain ⟨_, ek, _, ⟨ek', h_eq, h_acc'⟩, h_rej, _⟩ := h
    simp only [Option.some.injEq] at h_eq
    subst h_eq
    exact absurd h_acc' h_rej

/-- **Spec theorem for `spqr.v1.chunked.send_ct.Ct1Acknowledged.recv_ek_chunk`**
(concrete `decoded_message` semantics):

Instantiation of `recv_ek_chunk_spec` with the registered `decoded_message_spec` instead of a
lifted `decodedPost`.  Besides the hypotheses shared with `recv_ek_chunk_spec`, it assumes the
`#[hax_lib::refine]` struct invariant of the Rust `Ct1Acknowledged`,
`h_pts_needed : self.receiving_ek.pts_needed = 576` (= `ENCAPSULATION_KEY_SIZE / 2`), which
discharges the output-capacity guard `2 * pts_needed ≤ Usize.max` of `decoded_message_spec`.
The resulting `decodedPost` is exactly the postcondition of `decoded_message_spec`: `none` iff
the decoder is complete or some slot lacks points; `some ek` with `ek.length = 1152` and
`BytesDecode pd.pts pd.pts_needed ek.val 0` otherwise.

This is the `@[step]`-registered contract for `recv_ek_chunk`: all its hypotheses are
first-order side conditions that `step*` can leave as goals.

**Source**: spqr/src/v1/chunked/send_ct.rs (lines 259:4-279:5)
-/
@[step]
theorem recv_ek_chunk_spec_concrete (self : Ct1Acknowledged) (epoch : U64)
    (chunk : encoding.Chunk)
    (h_epoch : epoch = self.uc.epoch)
    (h_overflow : chunk.index * 16 + 16 ≤ Usize.max)
    (h_push_cap : ∀ (k : Nat), k < 16 →
      (self.receiving_ek.pts[k]!).length + 17 ≤ Usize.max)
    (h_valid : PolyDecoder.PointsValid self.receiving_ek.pts)
    (h_pts_needed : self.receiving_ek.pts_needed.val = 576)
    (h_es : self.uc.es.length = 2080)
    (h_key : self.uc.auth.mac_key.length ≤ U32.max)
    (h_ct : self.uc.ct1.length + 128 + 43 ≤ U32.max) :
    recv_ek_chunk self epoch chunk ⦃
      (result : core.result.Result Ct1AcknowledgedRecvChunk Error) =>
      recvEkChunkPost self chunk
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
  apply recv_ek_chunk_spec self epoch chunk _ h_epoch h_overflow h_push_cap h_valid
    _ h_es h_key h_ct
  intro pd h_pn _ h_pv
  have h_pn' : pd.pts_needed.val = 576 := by rw [h_pn, h_pts_needed]
  apply WP.spec_mono (PolyDecoder.Insts.SpqrEncodingDecoder.decoded_message_spec pd h_pv
    (by rw [h_pn']; scalar_tac))
  intro o h
  exact ⟨h_pn', h⟩

end spqr.v1.chunked.send_ct.Ct1Acknowledged
