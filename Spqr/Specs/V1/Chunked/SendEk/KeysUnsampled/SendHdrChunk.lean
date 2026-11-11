/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import SrcTranslated.Funs
public import Spqr.Specs.V1.Unchunked.SendEk.KeysUnsampled.SendHeader
import Spqr.Specs.Encoding.Polynomial.PolyEncoder.NextChunk
import Spqr.Specs.Encoding.Polynomial.PolyEncoder.EncodeBytes
import Spqr.Specs.Aeneas.ResultExpect
import Spqr.Auxiliary.Aeneas.Vec
public import Spqr.Math.Poly.Lagrange.CompletePoints
public import Spqr.Specs.Encoding.Polynomial.PolyEncoder.Defs
/-!
# Spec theorem for
`spqr::v1::chunked::send_ek::{spqr::v1::chunked::send_ek::KeysUnsampled}::send_hdr_chunk`

`KeysUnsampled` is the initial state of the encapsulation-key-sending (A→B) side of the
*chunked* V1 ratchet, before A has sampled its ML-KEM key pair.  It wraps the corresponding
unchunked state `unchunked::KeysUnsampled` (carrying `epoch : u64` and `Authenticator`) in the
single field `uc`.

`KeysUnsampled::send_hdr_chunk` performs the full transition from "no keys" to "header being
streamed":

  1. delegates to `unchunked::KeysUnsampled::send_header(rng)`, which samples an incremental
     ML-KEM-768 key pair, MACs the header, and transitions to `unchunked::HeaderSent`;
  2. appends the 32-byte MAC to the 64-byte header, producing a 96-byte `to_send` buffer;
  3. erasure-encodes `to_send` via `PolyEncoder::encode_bytes` and unwraps the result with
     `expect`;
  4. extracts the first chunk from the encoder via `next_chunk`;
  5. returns `(KeysSampled { uc, sending_hdr }, chunk)` together with the updated RNG.

The resulting `KeysSampled` state carries the unchunked `HeaderSent` (with epoch, authenticator,
ek, and dk) alongside the `PolyEncoder` that will produce subsequent header chunks.

**Source**: spqr/src/v1/chunked/send_ek.rs (lines 59:4-66:5)
-/

@[expose] public section

open Aeneas Aeneas.Std Result spqr encoding.polynomial encoding.gf Polynomial

namespace spqr.v1.chunked.send_ek.KeysUnsampled

open List core.num.U64 authenticator.Authenticator
  libcrux_ml_kem.mlkem768.incremental Spqr.Mlkem in
/-- **Spec theorem for `spqr.v1.chunked.send_ek.KeysUnsampled.send_hdr_chunk`**:

• Takes a chunked `KeysUnsampled` state `self`
  (wrapping `self.uc : unchunked.send_ek.KeysUnsampled`) and a mutable RNG reference
  `rng`, parameterised over `R` with `Rng` and `CryptoRng` instances.
• Delegates to `unchunked.send_ek.KeysUnsampled.send_header rng`, which:
    a. samples an ML-KEM-768 key pair → `hdr` (64 B), `ek` (1152 B), `dk` (2400 B);
    b. MACs the header → 32-byte HMAC-SHA256 tag `mac`;
    c. produces unchunked state `uc : HeaderSent`.
• Appends `mac` to `hdr`, producing a 96-byte buffer `to_send`.
• Erasure-encodes `to_send` via `PolyEncoder::encode_bytes`, unwraps with `expect`.
• Calls `next_chunk` on the encoder, producing the first `chunk` and an advanced encoder
  `sending_hdr`.
• Returns `((KeysSampled { uc, sending_hdr }, chunk), rng1)`.

The result `((state, chunk), rng1)` satisfies:

• **Unchunked state** (inherited from `send_header_spec`): `state.uc.epoch = self.uc.epoch`,
  `state.uc.auth = self.uc.auth`, `state.uc.ek.length = 1152`, `state.uc.dk.length = 2400`,
  and the FIPS 203 seed relation `∃ seed, dk = keyPairList seed ∧ ek = pk2Bytes seed`.
• **Header/MAC witnesses**: there exist `hdr` (64 B) and `mac` (32 B) such that `hdr` is the
  header slice of `dk` (`dk[2·1152 .. 2·1152 + 64]`), `mac_hdr self.uc.auth self.uc.epoch hdr
  = ok mac`, and the encoder was built from the 96-byte message `msg = hdr ++ mac`.
• **First chunk**: `chunk.index = 0`, `chunk.data.length = 32`, `state.sending_hdr.idx = 1`.
• **Encoder content**: there is a point table `pts` with every `pts[j]` holding exactly
  `96 / 2 / 16 = 3` values that are the big-endian word pairs of `msg` placed round-robin
  (`coeff k of pts[j] = msg[2(j+16k)] · 256 + msg[2(j+16k)+1]`), and the resulting
  `state.sending_hdr.s` satisfies the `next_chunk_spec` disjunction at index `0`: either it
  is still `Points pts` and every chunk word is `pts[j][0]`, or it has become `Polys polys'`
  with `polys'[j]` the scaled Lagrange interpolant of `pts[j]` and every chunk word either the
  cached `pts[j][0]` or the evaluation of `polys'[j]` at `0`.

The proof unfolds `send_hdr_chunk`, applies `send_header_spec` (giving `hdr.length = 64` and
`mac.length = 32`), `Vec.append_spec` (so `to_send.length = 96`), then `encode_bytes_spec`
(`96` is even and ≤ `2¹⁶ · 16`, ruling out the `Err`/`Polys` branches and giving every
point-vector exactly `3` values — an admissible interpolation size), unwraps via
`expect_ok_spec`, and finally applies `next_chunk_spec` at index `0`.

**Source**: spqr/src/v1/chunked/send_ek.rs (lines 59:4-66:5)
-/
@[step]
theorem send_hdr_chunk_spec {R : Type} (rngInst : rand_1.rng.Rng R)
    (cryptoInst : rand_core_1.CryptoRng R)
    (self : KeysUnsampled) (rng : R)
    (h_fill : ∀ (r : R) (s : Slice U8),
      rngInst.rand_core_1RngCoreInst.fill_bytes r s ⦃ fun _ => True ⦄)
    (h_key : self.uc.auth.mac_key.length ≤ U32.max) :
    send_hdr_chunk rngInst cryptoInst self rng ⦃
      (((state, chunk), _rng1) : (v1.chunked.send_ek.KeysSampled × encoding.Chunk) × R) =>
      -- Unchunked `HeaderSent` facts inherited from `send_header_spec`
      state.uc.epoch = self.uc.epoch ∧
      state.uc.auth = self.uc.auth ∧
      state.uc.ek.length = mlkem768Params.encapsulationKeyBytes ∧
      state.uc.dk.length = mlkem768Params.decapsulationKeyBytes ∧
      (∃ seed : Fin 64 → UInt8,
        state.uc.dk.val = Fips203.Refinement.keyPairList seed ∧
        state.uc.ek.val = Fips203.Refinement.toU8List (Fips203.Refinement.pk2Bytes seed)) ∧
      state.uc.ek.val = state.uc.dk.val.slice mlkem768Params.encapsulationKeyBytes
        (2 * mlkem768Params.encapsulationKeyBytes) ∧
      -- First chunk and advanced encoder index
      chunk.index.val = 0 ∧
      chunk.data.length = 32 ∧
      state.sending_hdr.idx.val = 1 ∧
      -- Header, MAC, and the encoded message `hdr ++ mac`
      (∃ (hdr mac : alloc.vec.Vec U8), hdr.length = headerBytes ∧ mac.length = MACSIZE.val ∧
        hdr.val = state.uc.dk.val.slice (2 * mlkem768Params.encapsulationKeyBytes)
          (2 * mlkem768Params.encapsulationKeyBytes + headerBytes) ∧
        mac_hdr self.uc.auth self.uc.epoch hdr.deref = ok mac ∧
        let msg := hdr.val ++ mac.val
        ∃ pts : Array Point 16#usize,
          (∀ (j : Nat), j < 16 → (pts[j]!).value.length = 3) ∧
          (∀ (j : Nat), j < 16 → ∀ (k : Nat), k < 3 →
            (listToGF216Poly (pts[j]!).value).coeff k =
              (256 * msg[2 * (j + 16 * k)]! + (msg[2 * (j + 16 * k) + 1]!).val).toGF216) ∧
          ((state.sending_hdr.s = .Points pts ∧
            ∀ (j : Nat), j < 16 →
              PolyEncoder.chunkWord chunk.data j =
                ((pts[j]!).value[0]!).toGF216) ∨
          (∃ polys', state.sending_hdr.s = .Polys polys' ∧
            (∀ (j : Nat), j < 16 →
              polys'[j]!.toGF216Poly =
                ∑ k ∈ Finset.range (pts[j]!).value.length,
                  C (((pts[j]!).value[k]!).toGF216) *
                    scaledLagrangeBasis (alloc.vec.Vec.len ((pts[j]!).value)) k) ∧
            (∀ (j : Nat), j < 16 →
              (polys'[j]!).coefficients.length + 1 ≤ Usize.max) ∧
            (∀ (j : Nat), j < 16 →
              PolyEncoder.chunkWord chunk.data j =
                  ((pts[j]!).value[0]!).toGF216 ∨
              PolyEncoder.chunkWord chunk.data j =
                (polys'[j]!).toGF216Poly.eval (Nat.toGF216 0))))) ⦄ := by
  unfold send_hdr_chunk
  step with v1.unchunked.send_ek.KeysUnsampled.send_header_spec rngInst cryptoInst self.uc rng
    h_fill h_key as ⟨uc, hdr, mac, rng1, h_epoch, h_auth, h_hdr, h_mac, h_ek, h_dk, seed,
      h_seed_dk, h_seed_ek, _, h_ek_slice, h_hdr_slice, h_mac_hdr, _⟩
  have h_hdr_len : hdr.val.length = 64 := by
    simp only [alloc.vec.Vec.length] at h_hdr; rw [h_hdr]; decide
  have h_mac_len : mac.val.length = 32 := by
    simp only [alloc.vec.Vec.length] at h_mac; rw [h_mac]; simp [MACSIZE]
  step with alloc.vec.Vec.append_spec Global hdr mac
    (by rw [h_hdr_len, h_mac_len]; scalar_tac)
    as ⟨to_send, _, h_to_send⟩
  have h_len : (alloc.vec.Vec.deref to_send).length = 96 := by
    simp only [Slice.length, alloc.vec.Vec.deref_val, h_to_send, List.length_append,
      h_hdr_len, h_mac_len]
  step with PolyEncoder.Insts.SpqrEncodingEncoder.encode_bytes_spec (alloc.vec.Vec.deref to_send)
    (by rw [h_len]) (by rw [h_len]; norm_num)
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
      -- `96 / 2 / 16 = 3` and `(96 / 2) % 16 = 0`: every point-vector has exactly 3 values
      have h_lens3 : ∀ (j : Nat), j < 16 → (pts[j]!).value.length = 3 := by
        intro j hj
        have := h_lens j hj
        simpa using this
      step with core.result.Result.expect_ok_spec as ⟨sending_hdr, h_sending⟩
      subst h_sending
      step with PolyEncoder.Insts.SpqrEncodingEncoder.next_chunk_spec ⟨idx, EncoderState.Points pts⟩
        (by
          intro pts' hpts j hj
          simp only [EncoderState.Points.injEq] at hpts
          subst hpts
          -- `3` is an admissible interpolation size; independent of the disjunct order
          simp only [h_lens3 j hj]; decide)
        (by intro polys h; cases h)
        as ⟨chunk, sending_hdr1, h_next⟩
      obtain ⟨h_index, h_chunk_len, h_idx1, h_state⟩ := h_next
      have h0 : (0#u32).val = 0 := rfl
      simp only [h_idx, h0, PolyEncoder.wireIndex, Nat.zero_mod] at h_index h_idx1 h_state
      have h_idx1' : sending_hdr1.idx.val = 1 := by rw [h_idx1]; scalar_tac
      refine ⟨h_epoch, h_auth, h_ek, h_dk, ⟨seed, h_seed_dk, h_seed_ek⟩, h_ek_slice, h_index,
        h_chunk_len, h_idx1', hdr, mac, h_hdr, h_mac, h_hdr_slice, h_mac_hdr, pts, h_lens3, ?_, ?_⟩
      · intro j hj k hk
        have := (h_content j hj k (by rw [h_lens3 j hj]; exact hk)).2
        rwa [Slice.getElem!_Nat_eq, Slice.getElem!_Nat_eq, alloc.vec.Vec.deref_val, h_to_send]
          at this
      · -- drop the `0 < |pts[j]|` conjuncts of the cache-hit cases
        rcases h_state with ⟨hs, hw⟩ | ⟨polys', hs, hl, hb, hw⟩
        · exact Or.inl ⟨hs, fun j hj => (hw j hj).2⟩
        · exact Or.inr ⟨polys', hs, hl, hb, fun j hj =>
            (hw j hj).elim (fun h => Or.inl h.2) Or.inr⟩

end spqr.v1.chunked.send_ek.KeysUnsampled
