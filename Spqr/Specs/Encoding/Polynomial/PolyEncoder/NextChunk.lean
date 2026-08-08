/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Encoding.Polynomial.PolyEncoder.ChunkAt

/-! # Spec theorem for `spqr::encoding::polynomial::{Encoder for PolyEncoder}::next_chunk`

Casts `self.idx` to U16, calls `chunk_at`, then wrapping-increments the index mod 2³².

**Source**: spqr/src/encoding/polynomial.rs -/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf Polynomial

namespace spqr.encoding.polynomial.PolyEncoder.Insts.SpqrEncodingEncoder

/-- **Spec theorem for `encoding.polynomial.PolyEncoder.Insts.SpqrEncodingEncoder.next_chunk`**:

Postcondition: `chunk.index = self.idx`, `chunk.data.length = 32`,
`self'.idx = (self.idx + 1) % 2³²`, plus polynomial-evaluation (`Polys`) or
Lagrange-interpolation (`Points`) invariants on the chunk data. -/
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
  step with chunk_at_spec
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
