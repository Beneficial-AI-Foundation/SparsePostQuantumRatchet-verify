/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

import Spqr.Specs.Encoding.Polynomial.PolyEncoder.ChunkAt
public import Spqr.Math.Poly.Lagrange.CompletePoints
public import Spqr.Specs.Encoding.Polynomial.PolyEncoder.Defs
import Mathlib.Order.Int.ConditionallyCompleteOrder
import Mathlib.Tactic.ComputeDegree

/-! # Spec theorem for `spqr::encoding::polynomial::{Encoder for PolyEncoder}::next_chunk`

Casts `self.idx` to U16, calls `chunk_at`, then wrapping-increments the index mod 2³².

**Source**: spqr/src/encoding/polynomial.rs -/

@[expose] public section

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf Polynomial

namespace spqr.encoding.polynomial.PolyEncoder.Insts.SpqrEncodingEncoder

/-- **Spec theorem for `encoding.polynomial.PolyEncoder.Insts.SpqrEncodingEncoder.next_chunk`**:

Postcondition: `NextChunkPostCond self self' chunk` (see `PolyEncoder.Defs`), i.e.
`chunk.index = self.idx`, `chunk.data.length = 32`, `self'.idx = (self.idx + 1) % 2³²`, and

* `Polys`: the state is unchanged and every chunk word is `polys[j](idx)`;
* `Points`: either a cache hit (`idx < |pts[j]|`, state unchanged, every chunk word is the
  stored point `pts[j][idx]`) or an interpolation step (state becomes `Polys polys'` with
  `polys'[j]` the Lagrange interpolant of `pts[j]`, and every chunk word is a stored point or
  `polys'[j](idx)`).

The `send_ct*_chunk` wrappers restate exactly this predicate on their encoder field. -/
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
      NextChunkPostCond self self' chunk ⦄ := by
  unfold next_chunk
  step
  step with chunk_at_spec
  step*
  unfold NextChunkPostCond chunkWord
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
    rcases h_match with ⟨h_eq, h_cache⟩ | ⟨polys', h_polys', h_lagrange, h_coeff, h_trans⟩
    · left
      constructor
      · -- chunk_at preserved the state, so next_chunk also preserves state
        -- h_eq says the chunk_at output encoder = self, but next_chunk changes idx
        -- We need self'.s = self.s
        simp_all
      · intro j hj
        obtain ⟨h_lt, h_bytes⟩ := h_cache j hj
        constructor
        · simp_all [UScalar.cast_val_eq]; grind
        · have := h_bytes
          simp_all [UScalar.cast_val_eq]
          grind
    · right
      refine ⟨polys', h_polys', h_lagrange, h_coeff, fun j hj => ?_⟩
      rcases h_trans j hj with ⟨h_lt, h_bytes⟩ | h_eval
      · left
        constructor
        · simp_all [UScalar.cast_val_eq]; grind
        · have := h_bytes
          simp_all [UScalar.cast_val_eq]
          grind
      · right
        have := h_eval
        simp_all [UScalar.cast_val_eq]
        grind

end spqr.encoding.polynomial.PolyEncoder.Insts.SpqrEncodingEncoder
