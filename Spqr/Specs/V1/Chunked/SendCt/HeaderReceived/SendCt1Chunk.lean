/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import SrcTranslated.Funs
public import Spqr.Specs.V1.Unchunked.SendCt.HeaderReceived.SendCt1
import Spqr.Specs.Encoding.Polynomial.PolyEncoder.NextChunk
import Spqr.Specs.Encoding.Polynomial.PolyEncoder.EncodeBytes
import Spqr.Specs.Aeneas.ResultExpect
import Spqr.Auxiliary.Aeneas.Vec
public import Spqr.Math.Poly.Lagrange.CompletePoints
public import Spqr.Specs.Encoding.Polynomial.PolyEncoder.Defs
/-!
# Spec theorem for
`spqr::v1::chunked::send_ct::{spqr::v1::chunked::send_ct::HeaderReceived}::send_ct1_chunk`

`HeaderReceived` is the state of the ciphertext-sending (B→A) side of the *chunked* V1 ratchet
after B has received A's 64-byte ML-KEM-768 header `hdr = ρ ‖ H(ek)` but has not yet sampled
the first ciphertext.  It wraps the corresponding unchunked state
`unchunked.send_ct.HeaderReceived` (which carries `epoch`, the `Authenticator`, and `hdr`) and
adds a `PolyDecoder` for reassembling `ek` from incoming chunks.

`HeaderReceived::send_ct1_chunk` is the combined *sample-and-first-chunk* step, the only
transition out of this state (the `send_ek` side does not start streaming `ek` before it has
seen the first CT chunk).  It:

  1. calls the unchunked `HeaderReceived::send_ct1` on `self.uc`, producing the successor
     unchunked state `uc : Ct1Sent`, the 960-byte first ciphertext half `ct1`, and the
     `EpochSecret`;
  2. erasure-encodes `ct1` via `PolyEncoder::encode_bytes`, yielding a `PolyEncoder` in the
     `Points` phase with index `0`;
  3. `expect`s the encoding result (infallible: 960 is even and far below the `2¹⁶ · 16` cap);
  4. calls `Encoder::next_chunk` on the fresh encoder, producing the first `Chunk` (tagged
     `index = 0`) and advancing the encoder to index `1`;
  5. returns `(Ct1Sampled { uc, sending_ct1, receiving_ek }, chunk, epoch_secret)`.

Mathematically, the 960 bytes of `ct1` are read as `480` big-endian GF(2¹⁶) words and dealt
round-robin onto sixteen point-vectors: word `j + 16·k` becomes the `k`-th value of `pts[j]`.
Since `480 = 16 · 30` exactly, every `pts[j]` has precisely `30` values — one of the admissible
interpolation sizes — so `next_chunk` can Lagrange-interpolate each `pts[j]` into a polynomial
`polys[j] ∈ GF(2¹⁶)[X]` of degree `< 30` and evaluate it at `x = 0` to produce the first chunk.
The ciphertext is therefore recoverable by A from *any* 30 distinct chunks.

The unchunked-level postcondition (FIPS 203 round-1 ciphertext semantics, HKDF-derived epoch
secret, authenticator ratchet) is inherited from `send_ct1_spec`; the encoder-level
postcondition (round-robin point layout, chunk index/length, Lagrange interpolants) is
inherited from `encode_bytes_spec` and `next_chunk_spec`.

**Source**: spqr/src/v1/chunked/send_ct.rs (lines 123:4-142:5)
-/

@[expose] public section

open Aeneas Aeneas.Std Result spqr crypto encoding.polynomial encoding.gf Polynomial List
     Spqr.V1.Unchunked.SendCt
  core.num.U64 v1.unchunked.send_ct.HeaderReceived

namespace spqr.v1.chunked.send_ct.HeaderReceived

/-- **Spec theorem for `spqr.v1.chunked.send_ct.HeaderReceived.send_ct1_chunk`**:

• Takes the chunked `HeaderReceived` state `self = { uc, receiving_ek }` and a CSPRNG `rng`.
• Delegates first to the unchunked `send_ct1`:
    `unchunked.send_ct.HeaderReceived.send_ct1 rngInst cryptoInst self.uc rng`
  which yields `((uc, ct1, epoch_secret), rng')`.
• Encodes `ct1` via `PolyEncoder::encode_bytes`, `expect`s the result, and calls `next_chunk`
  to obtain the first chunk.
• Returns `(Ct1Sampled { uc, sending_ct1, receiving_ek }, chunk, epoch_secret)`.

• The function succeeds under exactly the preconditions of `send_ct1_spec`:
    – `h_hdr`: the stored header has length 64;
    – `h_fill`: the RNG's `fill_bytes` is panic-free;
    – `h_root`: the authenticator root key leaves room for the 32-byte secret.
  No further hypotheses are needed: the preconditions of `encode_bytes_spec` (even length,
  `≤ 2¹⁶ · 16`) and of `next_chunk_spec` (index fits in `u16`, admissible point-vector lengths)
  are *discharged internally* from `ct1.length = 960`, `idx = 0`, and `480 / 16 = 30`.

• **Unchunked state** `st.uc : Ct1Sent` — inherited verbatim from `send_ct1_spec`:
    `st.uc.epoch = self.uc.epoch`, `st.uc.hdr = self.uc.hdr`,
    `st.uc.ct1.length = 960`, `st.uc.es.length = encapsStateSize`,
    `∃ m, st.uc.ct1.val = ct1List hdr m ∧ st.uc.es.val = stateOut hdr m ∧
          es.secret.val = HKDF(0³², ssOut hdr m, "…SCKA Key" ‖ epoch, 32)`,
    `st.uc.auth.root_key ‖ st.uc.auth.mac_key =
          HKDF(0³², self.uc.auth.root_key ‖ es.secret, updateLabel ‖ epoch, 64)`.
• **Epoch secret**: `es.epoch = self.uc.epoch` and `es.secret.length = 32`.
• **Decoder**: carried through untouched, `st.receiving_ek = self.receiving_ek`.
• **Chunk**: `chunk.index.val = 0` and `chunk.data.length = 32`.
• **Encoder**: `st.sending_ct1.idx.val = 1`, and there exist sixteen point-vectors `pts` with
    – `pts[j].length = 30` for every `j < 16`;
    – round-robin content: for `j < 16`, `k < 30`,
        `(listToGF216Poly pts[j]).coeff k =
            (256 · st.uc.ct1[2(j+16k)] + st.uc.ct1[2(j+16k)+1]).toGF216`;
    – phase clause inherited from `next_chunk_spec` at `idx = 0`: either the encoder stays in
      `Points pts` (cache hit, mirroring Rust's `pts[poly].value[idx]` lookup that leaves the
      state untouched) and every chunk word is the stored point `pts[j][0]`,
        `(256 · chunk.data[2j] + chunk.data[2j+1]).toGF216 = pts[j][0].toGF216`,
      or it transitions to `Polys polys'` with
        `polys'[j].toGF216Poly =
            ∑ k < 30, C (pts[j][k].toGF216) * scaledLagrangeBasis 30 k`,
      bounded coefficient counts, and every chunk word is either `pts[j][0]` or
      `polys'[j].toGF216Poly.eval 0`.
  In either branch the chunk bytes are pinned to the encoded ciphertext, so a wrong
  implementation emitting arbitrary bytes or discarding the points is excluded.

The proof unfolds `send_ct1_chunk`, applies `send_ct1_spec`, then `encode_bytes_spec` (whose
`Err`/`Polys` branches are refuted by the `False` postcondition), `expect_ok_spec`, and finally
`next_chunk_spec` with the admissibility side-condition instantiated at length `30`; its
`Points` disjunction, rewritten with `idx = 0`, is the phase clause above.

**Source**: spqr/src/v1/chunked/send_ct.rs (lines 123:4-142:5)
-/
@[step]
theorem send_ct1_chunk_spec {R : Type} (rngInst : rand_1.rng.Rng R)
    (cryptoInst : rand_core_1.CryptoRng R) (self : HeaderReceived) (rng : R)
    (h_hdr : self.uc.hdr.length = 64)
    (h_fill : ∀ (r : R) (s : Slice U8),
      rngInst.rand_core_1RngCoreInst.fill_bytes r s ⦃ fun _ => True ⦄)
    (h_root : self.uc.auth.root_key.length + 32 ≤ Usize.max) :
    send_ct1_chunk rngInst cryptoInst self rng ⦃
      (result : (v1.chunked.send_ct.Ct1Sampled × encoding.Chunk × EpochSecret) × R) =>
      let st := result.1.1
      let chunk := result.1.2.1
      let es := result.1.2.2
      -- unchunked state and epoch secret (inherited from `send_ct1_spec`)
      st.uc.epoch = self.uc.epoch ∧ st.uc.hdr = self.uc.hdr ∧
      st.uc.ct1.length = 960 ∧ st.uc.es.length = Fips203.Refinement.encapsStateSize ∧
      es.epoch = self.uc.epoch ∧ es.secret.length = 32 ∧
      (∃ m : Fin 32 → UInt8,
        st.uc.ct1.val = Fips203.Refinement.ct1List self.uc.hdr.val (by scalar_tac) m ∧
        st.uc.es.val = Fips203.Refinement.toU8List
          (Fips203.Refinement.stateOut self.uc.hdr.val (by scalar_tac) m) ∧
        es.secret.val = hkdf (replicate 32 0#u8)
          (Fips203.Refinement.toU8List
            (Fips203.Refinement.ssOut self.uc.hdr.val (by scalar_tac) m))
          (sckaKeyLabel ++ to_be_bytes self.uc.epoch) 32) ∧
      st.uc.auth.root_key.length = 32 ∧ st.uc.auth.mac_key.length = 32 ∧
      st.uc.auth.root_key.val ++ st.uc.auth.mac_key.val
        = hkdf (replicate 32 0#u8) (self.uc.auth.root_key.val ++ es.secret.val)
          (authenticator.Authenticator.updateLabel ++ to_be_bytes self.uc.epoch) 64 ∧
      -- decoder carried through
      st.receiving_ek = self.receiving_ek ∧
      -- first chunk and encoder advancement
      chunk.index.val = 0 ∧
      chunk.data.length = 32 ∧
      st.sending_ct1.idx.val = 1 ∧
      -- encoder content: round-robin layout of `ct1` and Lagrange interpolation
      (∃ pts : Array Point 16#usize,
        (∀ (j : Nat), j < 16 → (pts[j]!).value.length = 30) ∧
        (∀ (j : Nat), j < 16 → ∀ (k : Nat), k < 30 →
          (listToGF216Poly (pts[j]!).value).coeff k =
            (256 * st.uc.ct1.val[2 * (j + 16 * k)]! +
              (st.uc.ct1.val[2 * (j + 16 * k) + 1]!).val).toGF216) ∧
        -- phase-dependent clause inherited from `next_chunk_spec` at `idx = 0`: either the
        -- encoder stays in `Points pts` (cache hit) and every chunk word is `pts[j][0]`, or it
        -- transitions to `Polys polys'` satisfying the Lagrange identity, each chunk word being
        -- either `pts[j][0]` or the interpolant evaluated at `0`
        ((st.sending_ct1.s = .Points pts ∧
          ∀ (j : Nat), j < 16 →
            PolyEncoder.chunkWord chunk.data j =
              ((pts[j]!).value[0]!).toGF216) ∨
         (∃ polys', st.sending_ct1.s = .Polys polys' ∧
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
  unfold send_ct1_chunk
  step with v1.unchunked.send_ct.HeaderReceived.send_ct1_spec rngInst cryptoInst self.uc rng
    h_hdr h_fill h_root
  -- `step` applies `encode_bytes_spec`; its side-conditions follow from `ct1.length = 960`
  step
  have h_len : (alloc.vec.Vec.deref ct1).length = 960 := by
    simp only [Slice.length, alloc.vec.Vec.deref_val]; omega
  simp only [h_len] at encoder_post
  cases encoder with
  | Err e => exact absurd encoder_post not_false
  | Ok pe =>
    obtain ⟨idx, s⟩ := pe
    cases s with
    | Polys polys => exact absurd encoder_post not_false
    | Points pts =>
      obtain ⟨h_idx, h_lens, h_coeffs⟩ := encoder_post
      -- `960 / 2 / 16 = 30` and `(960 / 2) % 16 = 0`: every point-vector has exactly 30 values
      have h_lens30 : ∀ (j : Nat), j < 16 → (pts[j]!).value.length = 30 := by
        intro j hj
        have := h_lens j hj
        simpa using this
      step with core.result.Result.expect_ok_spec
      subst sending_ct1_post
      step with PolyEncoder.Insts.SpqrEncodingEncoder.next_chunk_spec ⟨idx, EncoderState.Points pts⟩
        (by simp [h_idx])
        (by
          intro pts' hpts j hj
          simp only [EncoderState.Points.injEq] at hpts
          subst hpts
          have := h_lens30 j hj
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl this)))))
        (by intro polys h; cases h)
        as ⟨chunk, sending_ct11, h_chunk⟩
      obtain ⟨h_chunk_idx, h_chunk_len, h_idx', h_points⟩ := h_chunk
      simp only [h_idx] at h_chunk_idx h_idx'
      -- `next_chunk_spec` yields a disjunction (stayed in `Points` / moved to `Polys`); with
      -- `idx = 0` it is exactly the phase-dependent clause of this contract
      simp only [h_idx] at h_points
      have h_phase :
          (sending_ct11.s = .Points pts ∧
            ∀ (j : Nat), j < 16 →
              PolyEncoder.chunkWord chunk.data j =
                ((pts[j]!).value[0]!).toGF216) ∨
          (∃ polys', sending_ct11.s = .Polys polys' ∧
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
                (polys'[j]!).toGF216Poly.eval (Nat.toGF216 0))) := by
        rcases h_points with ⟨h_same, h_hit⟩ | ⟨polys', h_eq, h_lag, h_bound, h_words⟩
        · exact Or.inl ⟨h_same, fun j hj => (h_hit j hj).2⟩
        · refine Or.inr ⟨polys', h_eq, h_lag, h_bound, fun j hj => ?_⟩
          rcases h_words j hj with ⟨_, h⟩ | h
          · exact Or.inl h
          · exact Or.inr h
      refine ⟨uc_post, uc_post1, ?_, «Fips203.Refinement.encapsStateSize_post», uc_post3, uc_post4,
        ⟨m, ?_, uc_post6, uc_post7⟩, uc_post8, uc_post9, uc_post10, ?_, h_chunk_len, ?_, pts,
        h_lens30, ?_, h_phase⟩
      · rw [ct1_post]; exact uc_post2
      · rw [ct1_post]; exact uc_post5
      · simpa using h_chunk_idx
      · rw [h_idx']; scalar_tac
      · intro j hj k hk
        have := h_coeffs j hj k (by rw [h_lens30 j hj]; exact hk)
        simpa [ct1_post, Slice.getElem!_Nat_eq, alloc.vec.Vec.deref_val] using this.2

end spqr.v1.chunked.send_ct.HeaderReceived
