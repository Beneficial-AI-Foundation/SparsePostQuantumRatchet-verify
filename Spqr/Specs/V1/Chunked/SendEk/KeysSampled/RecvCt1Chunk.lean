/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import SrcTranslated.Funs
public import Spqr.Specs.V1.Chunked.SendEk.HeaderSent.RecvCt1Chunk
public import Spqr.Specs.V1.Unchunked.SendEk.HeaderSent.SendEk
public import Spqr.Specs.Encoding.Polynomial.PolyEncoder.Defs
import Spqr.Specs.Encoding.Polynomial.PolyDecoder.New
import Spqr.Specs.Encoding.Polynomial.PolyEncoder.EncodeBytes
import Spqr.Specs.Aeneas.ResultExpect
import Spqr.Auxiliary.Aeneas.Vec
/-!
# Spec theorem for
`spqr::v1::chunked::send_ek::{spqr::v1::chunked::send_ek::KeysSampled}::recv_ct1_chunk`

`KeysSampled` is the state of the encapsulation-key-sending (A→B) side of the *chunked* V1
ratchet after A has sampled its new incremental ML-KEM key pair and is streaming the 96-byte
header‖MAC buffer to B.  It wraps the unchunked state `unchunked::HeaderSent` (carrying the
current `epoch : u64`, the `Authenticator`, the 1152-byte encapsulation key `ek` and the
2400-byte decapsulation key `dk`) and adds the header chunk encoder `sending_hdr`.

`KeysSampled::recv_ct1_chunk` is the transition triggered by the *first* chunk of B's first
ciphertext `ct1`: B has reconstructed the header, so A stops streaming it and switches to
streaming `ek` while collecting `ct1`.  On receipt of a 32-byte `Chunk` it:

  1. asserts `epoch == self.uc.epoch` (discharged by the hax contract
     `requires(epoch == self.uc.epoch)`);
  2. builds a fresh `PolyDecoder::new(CIPHERTEXT1_SIZE)` for the incoming `ct1` chunks; since
     `CIPHERTEXT1_SIZE = 960` is even this is `Ok` and the `.expect("should be able to decode
     header size")` never panics.  The decoder needs `960 / 2 = 480` points, starts with all 16
     polynomial slots empty and is not complete;
  3. feeds the chunk to that decoder (`receiving_ct1.add_chunk(chunk)`), which routes each of
     the 16 big-endian GF(2¹⁶) symbols of the chunk to polynomial `j` at x-coordinate
     `chunk.index` and inserts the resulting point into the corresponding sorted set;
  4. calls the unchunked `HeaderSent::send_ek`, a pure record construction that hands back
     `ek` and moves to `unchunked::EkSent { epoch, auth, dk }` (dropping `ek`);
  5. erasure-encodes `ek` via `PolyEncoder::encode_bytes`; since `ek.len() = 1152` is even and
     far below the `2¹⁶ · 16` cap the result is `Ok` and the `.expect("should be able to send
     ek")` never panics.  The fresh encoder is in the `Points` phase with index `0`, and the
     `576` GF(2¹⁶) words of `ek` are dealt round-robin onto sixteen point-vectors of exactly
     `576 / 16 = 36` values each;
  6. returns `HeaderSent { uc, sending_ek, receiving_ct1 }`.  The header encoder `sending_hdr`
     is dropped: once B sends `ct1` chunks it has necessarily decoded the whole header.

No cryptography happens here: `ek` is already bound to the epoch via the authenticated header
hash `H(ek)`, and `ct1` cannot be authenticated on its own (the tag received with `ct2` covers
`ct1 ‖ ct2`).  The result is a plain `HeaderSent` (no `Result` wrapper): the only fallible
operations are the two `expect`s, both of which are shown to be on `Ok` values.

Two sizes enter the function:

  * `CIPHERTEXT1_SIZE` is extracted as a wrapper around the opaque
    `libcrux_ml_kem::…::Ciphertext1::len`, so its value `960` is assumed via `h_ct1_size`
    (as `ENCAPSULATION_KEY_SIZE` is in `SendCt/NoHeaderReceived/RecvHdrChunk.lean`);
  * `ek.len() = 1152` is the `#[hax_lib::refine]` invariant of the unchunked `HeaderSent`
    (`serialize.HeaderSent.FunctionalModels.WellFormed`); the main theorem takes just the
    length `h_ek_len`, and `recv_ct1_chunk_spec_wellFormed` derives from the full invariant the
    `#[hax_lib::refine]` invariants of the successor `HeaderSent`
    (`receiving_ct1.pts_needed == CIPHERTEXT1_SIZE / 2`) and of its `EkSent` core.

Unlike `HeaderSent::recv_ct1_chunk`, no `h_push_cap` / `h_valid` hypotheses on the decoder are
needed: the decoder is built here, so its slots are provably empty (hence `PointsValid` and
with room for the 16 new points); the `usize` guard `chunk.index * 16 + 16 ≤ Usize.max` of
`add_chunk_spec` holds for every `chunk` because `chunk.index : u16`, so it is discharged
inline; and `decoded_message` is not consulted (a single chunk can never complete a 480-point
decoder, and the Rust code does not even ask).  The postcondition reuses
`PolyDecoder.Insts.SpqrEncodingDecoder.AddChunkPost` from
`Encoding/Polynomial/PolyDecoder/AddChunk.lean`, existentially quantifying the fresh decoder
`pd0` it starts from.

All callees (`PolyDecoder::new`, `expect`, `add_chunk`, `send_ek`, `encode_bytes`) are
discharged by their registered specs.

**Source**: spqr/src/v1/chunked/send_ek.rs (lines 85:4-98:5)
-/

@[expose] public section

open Aeneas Aeneas.Std Result spqr encoding.polynomial encoding.gf
  Spqr.V1.Chunked.SendEk.HeaderSent Spqr.V1.Unchunked.SendEk.HeaderSent

namespace spqr.v1.chunked.send_ek.KeysSampled

/-- **Spec theorem for `spqr.v1.chunked.send_ek.KeysSampled.recv_ct1_chunk`**:

• Takes a chunked `KeysSampled` state `self`, consisting of the unchunked inner state
  `self.uc : unchunked.send_ek.HeaderSent` and the header chunk encoder
  `self.sending_hdr : PolyEncoder`, the epoch `epoch : U64` announced by the peer, and the
  received 32-byte `chunk`.  In the original Rust source `self` is consumed by value and
  `chunk` is passed by shared reference; after Aeneas extraction both are plain values.
• Checks `massert (epoch = self.uc.epoch)`, which succeeds because of `h_epoch`.
• Evaluates `CIPHERTEXT1_SIZE` (= `960` by `h_ct1_size`) and builds
  `PolyDecoder.Insts.SpqrEncodingDecoder.new 960`, which is `Ok pd0` with
  `pd0.pts_needed = 480`, `pd0.pts = replicate 16 default` and `pd0.is_complete = false`;
  `expect` unwraps it.
• Absorbs the chunk via `add_chunk pd0 chunk`, obtaining `receiving_ct1` with
  `AddChunkPost pd0 chunk receiving_ct1` and `PointsValid receiving_ct1.pts`.
• Calls `unchunked.send_ek.HeaderSent.send_ek self.uc = ok (sendEkState self.uc, self.uc.ek)`.
• Erasure-encodes `self.uc.ek` (1152 bytes by `h_ek_len`) with `encode_bytes`, obtaining
  `Ok { idx := 0, s := Points pts }` with every `pts[j]` holding exactly `36` values; `expect`
  unwraps it.
• Returns `{ uc := sendEkState self.uc, sending_ek, receiving_ct1 }`.

• Requires:
    – `h_epoch : epoch = self.uc.epoch` — the hax precondition, discharging the `assert_eq!`;
    – `h_ct1_size` — the value `960` of the opaque `CIPHERTEXT1_SIZE`;
    – `h_ek_len : self.uc.ek.length = 1152` — the `HeaderSent` refinement on `ek`.
  Under these hypotheses the call never panics.  The `usize` guards of `add_chunk_spec` need
  no hypothesis: the base index `chunk.index * 16 + 16` fits because `chunk.index : u16`, and
  the per-slot capacity guard holds trivially for the empty decoder.

The result satisfies:

  • **Unchunked state**: `result.uc = sendEkState self.uc`, i.e. `epoch`, `auth` and `dk` are
    carried over verbatim and `ek` is dropped from the unchunked state.
  • **Decoder**: there is a fresh decoder `pd0` with `pts_needed = 480`, all 16 slots empty and
    `is_complete = false`, such that `AddChunkPost pd0 chunk result.receiving_ct1`; moreover
    `result.receiving_ct1.pts_needed = 480`, `result.receiving_ct1.is_complete = false` and
    `PointsValid result.receiving_ct1.pts` — exactly the hypotheses the follow-up transition
    `HeaderSent::recv_ct1_chunk` requires.
  • **Encoder**: `result.sending_ek.idx = 0` and `result.sending_ek.s = Points pts` where every
    `pts[j]` has exactly `36` values and the `k`-th value of `pts[j]`, read as a GF(2¹⁶)
    element, is the big-endian word `ek[2·(j + 16·k)] ‖ ek[2·(j + 16·k) + 1]` — the
    round-robin layout inherited from `encode_bytes_spec`.

The proof unfolds `recv_ct1_chunk`, discharges the assertion with `h_epoch`, reduces
`PolyDecoder::new` to its `Ok` branch using `h_ct1_size` and `new_spec`, establishes
`PointsValid` and the capacity guard for the empty slots, runs `add_chunk_spec` /
`add_chunk_spec_valid`, rewrites `send_ek` with `send_ek_eq`, reduces `encode_bytes` to its
`Ok`/`Points` branch using `encode_bytes_spec` (the `Err` / `Polys` branches are contradictory)
and collects the conjuncts.

**Source**: spqr/src/v1/chunked/send_ek.rs (lines 85:4-98:5)
-/
@[step]
theorem recv_ct1_chunk_spec (self : KeysSampled) (epoch : U64) (chunk : encoding.Chunk)
    (h_epoch : epoch = self.uc.epoch)
    (h_ct1_size : incremental_mlkem768.CIPHERTEXT1_SIZE ⦃ (r : Usize) => r.val = 960 ⦄)
    (h_ek_len : self.uc.ek.length = 1152) :
    recv_ct1_chunk self epoch chunk ⦃ (result : HeaderSent) =>
      result.uc = sendEkState self.uc ∧
      (∃ pd0 : PolyDecoder,
        pd0.pts_needed.val = 480 ∧
        pd0.pts.val = List.replicate 16 default ∧
        pd0.is_complete = false ∧
        PolyDecoder.Insts.SpqrEncodingDecoder.AddChunkPost pd0 chunk result.receiving_ct1) ∧
      result.receiving_ct1.pts_needed.val = 480 ∧
      result.receiving_ct1.is_complete = false ∧
      PolyDecoder.PointsValid result.receiving_ct1.pts ∧
      result.sending_ek.idx = 0#u32 ∧
      ∃ pts : Array Point 16#usize,
        result.sending_ek.s = .Points pts ∧
        (∀ (j : Nat), j < 16 → (pts[j]!).value.length = 36) ∧
        (∀ (j : Nat), j < 16 → ∀ (k : Nat), k < 36 →
          (listToGF216Poly (pts[j]!).value).coeff k =
            (256 * self.uc.ek.val[2 * (j + 16 * k)]! +
              (self.uc.ek.val[2 * (j + 16 * k) + 1]!).val).toGF216) ⦄ := by
  unfold recv_ct1_chunk
  step with massert_spec _ h_epoch
  step with h_ct1_size as ⟨i, h_i⟩
  step with PolyDecoder.Insts.SpqrEncodingDecoder.new_spec i as ⟨decoder, h_new⟩
  simp only [h_i, Nat.reduceMod, ↓reduceIte] at h_new
  cases decoder with
  | Err e => exact absurd h_new not_false
  | Ok pd0 =>
    obtain ⟨h_pn, h_vec, h_ic⟩ := h_new
    have h_pn' : pd0.pts_needed.val = 480 := by rw [h_pn]; rfl
    step with core.result.Result.expect_ok_spec encoding.EncodingError.Insts.CoreFmtDebug
      pd0 _ as ⟨receiving_ct1, h_rc⟩
    subst receiving_ct1
    -- `chunk.index : u16`, so the base index of the 16 symbols fits in a `usize`
    have h_overflow : chunk.index * 16 + 16 ≤ Usize.max := by scalar_tac
    -- the fresh decoder has empty slots: `PointsValid` and the push-capacity guard are free
    have h_valid0 : PolyDecoder.PointsValid pd0.pts :=
      PolyDecoder.Insts.SpqrEncodingDecoder.PointsValid_replicate_default pd0.pts h_vec
    have h_push_cap : ∀ (k : Nat), k < 16 → (pd0.pts[k]!).length + 17 ≤ Usize.max := by
      intro k hk
      have h_slot : (pd0.pts[k]!).val = [] := by
        rw [Array.getElem!_Nat_eq, h_vec, List.getElem!_replicate]
        · rfl
        · exact hk
      change (pd0.pts[k]!).val.length + 17 ≤ Usize.max
      rw [h_slot]
      scalar_tac
    step with WP.spec_and
      (PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk_spec pd0 chunk h_overflow h_push_cap)
      (PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk_spec_valid pd0 chunk h_overflow
        h_push_cap h_valid0)
      as ⟨receiving_ct11, h_pn1, h_ic1, selfs, h_s0, h_s16, h_chain, h_valid1⟩
    have h_add : PolyDecoder.Insts.SpqrEncodingDecoder.AddChunkPost pd0 chunk receiving_ct11 :=
      ⟨h_pn1, h_ic1, selfs, h_s0, h_s16, h_chain⟩
    rw [unchunked.send_ek.HeaderSent.send_ek_eq]
    simp only [sendEkResult, bind_ok]
    have h_len : (alloc.vec.Vec.deref self.uc.ek).length = 1152 := by
      simp only [Slice.length, alloc.vec.Vec.deref_val]; exact h_ek_len
    step with PolyEncoder.Insts.SpqrEncodingEncoder.encode_bytes_spec
      (alloc.vec.Vec.deref self.uc.ek) (by rw [h_len]) (by rw [h_len]; norm_num)
      as ⟨encoder, h_enc⟩
    simp only [h_len] at h_enc
    cases encoder with
    | Err e => exact absurd h_enc not_false
    | Ok pe =>
      obtain ⟨idx, s⟩ := pe
      cases s with
      | Polys polys => exact absurd h_enc not_false
      | Points pts =>
        obtain ⟨h_idx, h_lens, h_content⟩ := h_enc
        -- `1152 / 2 / 16 = 36` and `(1152 / 2) % 16 = 0`: every point-vector has exactly 36 values
        have h_lens36 : ∀ (j : Nat), j < 16 → (pts[j]!).value.length = 36 := by
          intro j hj
          have := h_lens j hj
          simpa using this
        step with core.result.Result.expect_ok_spec as ⟨sending_ek, h_sending⟩
        subst h_sending
        refine ⟨⟨pd0, h_pn', h_vec, h_ic, h_add⟩, by rw [h_pn1, h_pn'],
          by rw [h_ic1, h_ic], h_valid1, h_idx, pts, rfl, h_lens36, ?_⟩
        intro j hj k hk
        have := (h_content j hj k (by rw [h_lens36 j hj]; exact hk)).2
        rwa [Slice.getElem!_Nat_eq, Slice.getElem!_Nat_eq, alloc.vec.Vec.deref_val] at this

/-- **Spec theorem for `spqr.v1.chunked.send_ek.KeysSampled.recv_ct1_chunk`**
(well-formedness of the successor state):

Under the `#[hax_lib::refine]` invariant of the unchunked `HeaderSent`
(`serialize.HeaderSent.FunctionalModels.WellFormed self.uc`, i.e. `ek.length = 1152 ∧
dk.length = 2400`), the returned chunked `HeaderSent` satisfies the invariants that the
follow-up transitions `HeaderSent::send_ek_chunk` / `HeaderSent::recv_ct1_chunk` and the
serializer require:

  * the `#[hax_lib::refine]` invariant of the chunked `HeaderSent`,
    `receiving_ct1.pts_needed == CIPHERTEXT1_SIZE / 2 = 480`;
  * `PointsValid` for the decoder slots, and `is_complete = false`;
  * the `#[hax_lib::refine]` invariant of the unchunked `EkSent` core,
    `serialize.EkSent.FunctionalModels.WellFormed result.uc` (`dk.length = 2400`), together
    with `epoch` and `auth` carried over from `self.uc`;
  * the encoder index fits in a `u16` (`idx = 0`), and every point-vector has the admissible
    interpolation size `36`, which is the `h_admissible` hypothesis of `next_chunk_spec` used
    by `HeaderSent::send_ek_chunk`.

Projection of `recv_ct1_chunk_spec`.

**Source**: spqr/src/v1/chunked/send_ek.rs (lines 85:4-98:5)
-/
theorem recv_ct1_chunk_spec_wellFormed (self : KeysSampled) (epoch : U64)
    (chunk : encoding.Chunk)
    (h_epoch : epoch = self.uc.epoch)
    (h_ct1_size : incremental_mlkem768.CIPHERTEXT1_SIZE ⦃ (r : Usize) => r.val = 960 ⦄)
    (h_wf : unchunked.send_ek.serialize.HeaderSent.FunctionalModels.WellFormed self.uc) :
    recv_ct1_chunk self epoch chunk ⦃ (result : HeaderSent) =>
      result.uc.epoch = self.uc.epoch ∧
      result.uc.auth = self.uc.auth ∧
      unchunked.send_ek.serialize.EkSent.FunctionalModels.WellFormed result.uc ∧
      result.receiving_ct1.pts_needed.val = 480 ∧
      result.receiving_ct1.is_complete = false ∧
      PolyDecoder.PointsValid result.receiving_ct1.pts ∧
      result.sending_ek.idx.val ≤ U16.max ∧
      (∀ pts, result.sending_ek.s = .Points pts →
        ∀ (j : Nat), j < 16 → (pts[j]!).value.length = 36) ⦄ := by
  apply WP.spec_mono (recv_ct1_chunk_spec self epoch chunk h_epoch h_ct1_size h_wf.1)
  intro result h
  obtain ⟨h_uc, _, h_pn, h_ic, h_valid, h_idx, pts, h_s, h_lens, _⟩ := h
  refine ⟨by rw [h_uc]; rfl, by rw [h_uc]; rfl, ?_, h_pn, h_ic, h_valid, by rw [h_idx]; decide,
    ?_⟩
  · rw [h_uc]; exact h_wf.2
  · intro pts' h_s' j hj
    rw [h_s] at h_s'
    simp only [EncoderState.Points.injEq] at h_s'
    subst h_s'
    exact h_lens j hj

/-- **Completeness of the precondition of `spqr.v1.chunked.send_ek.KeysSampled.recv_ct1_chunk`**:

The hypothesis `epoch = self.uc.epoch` of `recv_ct1_chunk_spec` is not merely sufficient but
necessary: whenever the announced epoch differs from the stored one, the leading `assert_eq!`
fires before any decoder or encoder is built and the call panics.

**Source**: spqr/src/v1/chunked/send_ek.rs (lines 85:4-98:5)
-/
theorem recv_ct1_chunk_fail_of_epoch_ne (self : KeysSampled) (epoch : U64)
    (chunk : encoding.Chunk)
    (h_epoch : epoch ≠ self.uc.epoch) :
    recv_ct1_chunk self epoch chunk = fail Error.assertionFailure := by
  simp [recv_ct1_chunk, massert, h_epoch]

end spqr.v1.chunked.send_ek.KeysSampled
