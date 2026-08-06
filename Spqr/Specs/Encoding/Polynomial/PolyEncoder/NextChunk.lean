/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Encoding.Polynomial.PolyEncoder.ChunkAt

/-!
# Spec theorem for `spqr::encoding::polynomial::{Encoder for PolyEncoder}::next_chunk`

The `Encoder` trait method `next_chunk` on `PolyEncoder` produces the next serialized chunk and
advances the encoder's internal chunk counter.  Given a mutable reference to the encoder state,
the function:

  1. Casts the current chunk index `self.idx : U32` to `U16` (the cast succeeds whenever
     `self.idx.val ≤ U16.max`, i.e. the encoder has produced fewer than 2¹⁶ chunks).
  2. Delegates to `self.chunk_at(idx_u16)` to serialize 16 polynomial evaluations into a
     32-byte `Chunk` (see `chunk_at_spec`).
  3. Wrapping-increments the chunk counter: `self.idx ← self.idx.wrapping_add(1)`,
     i.e. `self.idx ← (self.idx + 1) % 2³²`.
  4. Returns the chunk together with the updated encoder state.

The function composes:
  1. `UScalar.cast .U16 self.idx` — checked narrowing of the 32-bit index to 16 bits.
  2. `chunk_at` — serialization of 16 GF(2¹⁶) evaluations into a 32-byte chunk.
  3. `core.num.U32.wrapping_add` — modular increment of the chunk counter (mod 2³²).

**Source**: spqr/src/encoding/polynomial.rs (lines 734:4-738:5)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf Polynomial

namespace spqr.encoding.polynomial.PolyEncoder.Insts.SpqrEncodingEncoder

/-- **Spec theorem for `encoding.polynomial.PolyEncoder.Insts.SpqrEncodingEncoder.next_chunk`**:

Produces the next serialized chunk and advances the encoder's chunk counter.  The postcondition
captures the chunk's structural properties, the polynomial evaluation / Lagrange interpolation
invariant, and the index update.

The result satisfies:
  * `chunk.index.val = self.idx.val` — the chunk's U16 index equals the (pre-increment) encoder
    index (which fits in 16 bits by `h_idx_fits`).
  * `chunk.data.length = 32` — the data array contains exactly 32 bytes.
  * `self'.idx.val = (self.idx.val + 1) % U32.size` — the encoder's index is wrapping-incremented.
  * If the encoder was initially in the `Polys` state:
      - The encoder state field is unchanged: `self'.s = self.s`.
      - For every `j ∈ [0, 16)`, the big-endian encoding of the `j`-th polynomial evaluation
        satisfies:
        `Nat.toGF216 (256 * chunk.data[2 * j]! + chunk.data[2 * j + 1]!) =
          (polys[j]!).toGF216Poly.eval (self.idx.val.toGF216)`
  * If the encoder was initially in the `Points` state:
      - For any resulting `Polys polys'` state, each polynomial equals the Lagrange interpolation
        of the corresponding points.

This follows from composing:
  1. `UScalar.cast` — succeeds because `self.idx.val ≤ U16.max`.
  2. `chunk_at_spec`: the serialization returns a well-formed chunk with `chunk.index = idx` and
     `chunk.data.length = 32`, with the polynomial evaluation / Lagrange interpolation
     invariant matching on the encoder state.
  3. `core.num.U32.wrapping_add`: the index is incremented modulo 2³².

    This corresponds to the Rust function:
    ```rust
    fn next_chunk(&mut self) -> Chunk {
        let out = self.chunk_at(self.idx as u16);
        self.idx = self.idx.wrapping_add(1);
        out
    }
    ```

**Source**: spqr/src/encoding/polynomial.rs (lines 734:4-738:5)
-/
@[step]
theorem next_chunk_spec
    (self : encoding.polynomial.PolyEncoder)
    (h_idx_fits : self.idx.val ≤ U16.max)
    (h_admissible : ∀ pts, self.s = .Points pts →
        ∀ (j : Nat), j < 16 →
          let len := (pts[j]!).value.length
          len = 0 ∨ len = 1 ∨ len = 3 ∨ len = 5 ∨
          len = 30 ∨ len = 34 ∨ len = 36)
    (h_coeff_bound : ∀ polys, self.s = .Polys polys →
        ∀ (j : Nat), j < 16 →
          (polys[j]!).coefficients.length + 1 ≤ Usize.max) :
    next_chunk self ⦃ ((chunk, self') :
        encoding.Chunk × encoding.polynomial.PolyEncoder) =>
      chunk.index.val = self.idx.val ∧
      chunk.data.length = 32 ∧
      self'.idx.val = (self.idx.val + 1) % U32.size ∧
      match self.s with
      | .Polys polys =>
          self'.s = self.s ∧
          ∀ (j : Nat), j < 16 →
            Nat.toGF216 (256 * chunk.data[2 * j]! + chunk.data[2 * j + 1]!) =
              (polys[j]!).toGF216Poly.eval (self.idx.val.toGF216)
      | .Points pts =>
          ∀ polys', self'.s = .Polys polys' →
            ∀ (j : Nat), j < 16 →
              polys'[j]!.toGF216Poly =
                ∑ k ∈ Finset.range (pts[j]!).value.length,
                  C (((pts[j]!).value[k]!).toGF216) *
                    scaledLagrangeBasis (alloc.vec.Vec.len ((pts[j]!).value)) k ⦄ := by
  unfold next_chunk
  step
  step with chunk_at_spec by
    first | assumption | scalar_tac
  step*
  obtain ⟨h_idx_eq, h_data_len, h_self_idx, h_match⟩ := out_post
  refine ⟨by simp_all [UScalar.cast_val_eq]; grind, h_data_len, by simp_all, ?_⟩
  cases h_s : self.s with
  | Polys polys =>
    simp only [h_s] at h_match ⊢
    obtain ⟨h_self_eq, h_eval⟩ := h_match
    refine ⟨by simp_all, fun j hj => ?_⟩
    have := h_eval j hj
    simp_all [UScalar.cast_val_eq]
    grind
  | Points pts =>
    simp only [h_s] at h_match ⊢
    intro polys' h_polys' j hj
    exact h_match polys' h_polys' j hj

end spqr.encoding.polynomial.PolyEncoder.Insts.SpqrEncodingEncoder
