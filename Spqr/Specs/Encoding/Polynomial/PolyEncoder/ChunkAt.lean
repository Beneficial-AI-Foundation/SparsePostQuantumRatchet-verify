/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

import Spqr.Specs.Aeneas.TryFromSliceToArray
public import Spqr.Specs.Aeneas.VecIndexRangeFull
public import Spqr.Specs.Aeneas.ResultExpect
public import Spqr.Specs.Encoding.Polynomial.PolyEncoder.PointAt
import Mathlib.Order.Int.ConditionallyCompleteOrder
import Mathlib.Tactic.ComputeDegree
import Spqr.Specs.Encoding.Polynomial.Poly.Serialize
import Spqr.Specs.Aeneas.RangeIteratorNext

/-! # Spec theorem for `PolyEncoder::chunk_at`: loop body 0

One step of the chunk serialization loop in `PolyEncoder::chunk_at` (lines 697–705), which
iterates `i` over `0..16` and appends the 2-byte big-endian encoding of
`self.point_at(i, idx).value` to the output vector.

The proof composes `IteratorRange.next`, usize arithmetic (`total_idx`, `poly`, `poly_idx`),
`PolyEncoder.point_at`, bit-shift/cast, and two `Vec::push` calls.

**Source**: spqr/src/encoding/polynomial.rs -/

@[expose] public section

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf Polynomial

namespace spqr.encoding.polynomial.PolyEncoder.chunk_at_loop

/-- **Spec theorem for `encoding.polynomial.PolyEncoder.chunk_at_loop.body`**:

One iteration of the chunk serialization loop. Retrieves the next index `i` from the range
iterator and either terminates (done) or evaluates `point_at(i, idx)` and appends the 2-byte
big-endian encoding of the GF(2¹⁶) result to `out`.

In the **cont** case, the iterator advances by one, the output extends by `[hi, lo]` with
`256 * hi + lo = g.value.val`, and the encoder's `idx` field is preserved. The GF(2¹⁶) value
`g` is determined by the encoder state: direct lookup (Points cache hit), Lagrange interpolation
(Points cache miss), or polynomial evaluation (Polys).

**Source**: spqr/src/encoding/polynomial.rs (lines 697:8-705:9) -/
@[step]
theorem body_spec
    (idx : U16) (iter : core.ops.range.Range Usize)
    (self : PolyEncoder) (out : alloc.vec.Vec U8)
    (h_end_le : iter.end.val ≤ 16)
    (h_idx_overflow : idx * 16 + 16 ≤ Usize.max)
    (h_out_overflow : out.length + 2 ≤ Usize.max)
    (h_admissible : ∀ pts, self.s = .Points pts →
        ∀ (j : Nat), j < 16 →
          let len := (pts[j]!).value.length
          len = 0 ∨ len = 1 ∨ len = 3 ∨ len = 5 ∨
          len = 30 ∨ len = 34 ∨ len = 36)
    (h_coeff_polys : ∀ polys, self.s = .Polys polys →
        ∀ (j : Nat), j < 16 →
          (polys[j]!).coefficients.length + 1 ≤ Usize.max) :
    body idx iter self out ⦃ cf =>
      match cf with
      | ControlFlow.done (self', out') =>
          self' = self ∧ out' = out ∧ ¬(iter.start.val < iter.end.val)
      | ControlFlow.cont (iter1, self1, out1) =>
          iter.start < iter.end.val ∧
          iter1.start = iter.start.val + 1 ∧
          iter1.end = iter.end ∧
          ∃ (g : GF16) (hi lo : U8),
            out1 = out ++ [hi, lo] ∧
            256 * hi + lo = g.value.val ∧
            self1.idx = self.idx ∧
            match self.s with
            | .Points pts =>
                if idx < (pts[iter.start]!).value.length then
                  g = (pts[iter.start]!).value[idx.val]! ∧
                  self1 = self
                else
                  match self1.s with
                  | .Polys polys' =>
                      (∀ (j : Nat), j < 16 →
                        polys'[j]!.toGF216Poly =
                          ∑ k ∈ Finset.range (pts[j]!).value.length,
                            C (((pts[j]!).value[k]!).toGF216) *
                              scaledLagrangeBasis (alloc.vec.Vec.len ((pts[j]!).value)) k) ∧
                      (∀ (j : Nat), j < 16 →
                        (polys'[j]!).coefficients.length + 1 ≤ Usize.max) ∧
                      g.toGF216 = (polys'[iter.start.val]!).toGF216Poly.eval (idx.val.toGF216)
                  | .Points _ => False
            | .Polys polys =>
                g.toGF216 =(polys[iter.start.val]!).toGF216Poly.eval (idx.val.toGF216) ∧
                self1 = self ⦄ := by
  unfold body
  step with core.iter.range.IteratorRange.next_Usize_spec' iter as
    ⟨opt, iter1', h_none, h_some⟩
  by_cases h_lt : iter.start.val < iter.end.val
  · obtain ⟨h_opt_eq, h_start1, h_end1⟩ := h_some h_lt
    rw [h_opt_eq]
    have h_i_lt_16 : iter.start.val < 16 := by omega
    step as ⟨i1, h_i1⟩
    step as ⟨i2, h_i2⟩
    step as ⟨total, h_total⟩
    step as ⟨poly, h_poly⟩
    step as ⟨poly_idx, h_pidx⟩
    have h_i1_val : i1.val = idx.val := by rw [h_i1]; simp
    have h_poly_eq : poly = iter.start :=
      UScalar.eq_of_val_eq (by rw [h_poly, h_total, h_i2, h_i1_val]; omega)
    have h_pidx_val : poly_idx.val = idx.val := by rw [h_pidx, h_total, h_i2, h_i1_val]; omega
    subst h_poly_eq
    step with point_at_spec as ⟨g, self1, h_pa⟩
    obtain ⟨h_idx1, h_pa⟩ := h_pa
    step as ⟨i3, h_i3, _⟩
    step as ⟨i4, h_i4⟩
    have : out.val.length < Usize.max := by
      simp only [alloc.vec.Vec.length] at h_out_overflow; omega
    step as ⟨out1, h_out1⟩
    have : out1.val.length < Usize.max := by
      rw [h_out1]; simp only [List.length_append, List.length_singleton]
      simp only [alloc.vec.Vec.length] at h_out_overflow; omega
    step as ⟨i5, h_i5⟩
    step as ⟨out2, h_out2⟩
    refine ⟨h_lt, h_start1, h_end1, g, i4, i5, by rw [h_out2, h_out1]; simp, ?_, h_idx1, ?_⟩
    · -- `hi = g.value >>> 8` and `lo = g.value % 256` recombine to `g.value`
      have hv : g.value.val < 2 ^ 16 := g.value.hBounds
      rw [h_i4, h_i5, UScalar.cast_val_eq, UScalar.cast_val_eq, h_i3]
      simp only [UScalarTy.U8_numBits_eq, Nat.shiftRight_eq_div_pow]
      omega
    · -- `point_at`'s postcondition, at `poly = iter.start` and `poly_idx = idx`
      cases hs : self.s <;> cases hs1 : self1.s <;> simp only [hs, hs1] at h_pa ⊢ <;>
        simpa [h_pidx_val, Array.getElem!_Usize_eq, Array.getElem!_Nat_eq,
          alloc.vec.Vec.getElem!_Nat_eq] using h_pa
  · obtain ⟨h_opt_eq, -⟩ := h_none h_lt
    rw [h_opt_eq, WP.spec_ok]
    exact ⟨rfl, rfl, h_lt⟩
end spqr.encoding.polynomial.PolyEncoder.chunk_at_loop

/-!
# Spec theorem for `PolyEncoder::chunk_at`: loop 0

The full chunk serialization loop in `PolyEncoder::chunk_at` (lines 697–705). Drives
`chunk_at_loop.body` through all 16 iterations, accumulating the 2-byte big-endian encoding
of each polynomial evaluation into the output vector.

The proof lifts `body_spec` through `loop.spec_decr_nat` with measure
`iter'.end.val − iter'.start.val`, maintaining the byte-encoding invariant.

**Source**: spqr/src/encoding/polynomial.rs (lines 697:8-705:9) -/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf Polynomial

namespace spqr.encoding.polynomial.PolyEncoder.chunk_at_loop

/-! ## Spec theorem for the chunk_at serialization loop -/

/-- Appending a byte pair leaves the earlier bytes unchanged. -/
private lemma getElem!_append_pair_of_lt {l : List U8} {hi lo : U8} {p : Nat}
    (hp : p < l.length) : (l ++ [hi, lo])[p]! = l[p]! := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD,
    List.getElem?_append_left hp]

private lemma getElem!_append_pair_hi (l : List U8) (hi lo : U8) :
    (l ++ [hi, lo])[l.length]! = hi := by simp

private lemma getElem!_append_pair_lo (l : List U8) (hi lo : U8) :
    (l ++ [hi, lo])[l.length + 1]! = lo := by simp

/-- **Spec theorem for `encoding.polynomial.PolyEncoder.chunk_at_loop`**:

The full serialization loop. Returns the updated encoder state and byte vector satisfying:
- `result.1.idx = self.idx` — encoder index preserved.
- `result.2.length = out.length + 2 * (iter.end − iter.start)` — two bytes per evaluation.
- Big-endian encoding invariant for each `j ∈ [start, end)`.
- **Polys**: encoder state unchanged; each pair decodes to
  `(polys[j]!).toGF216Poly.eval (idx.val.toGF216)`.
- **Points**: Lagrange interpolation identity preserved for any resulting Polys state.

**Source**: spqr/src/encoding/polynomial.rs (lines 697:8-705:9) -/
@[step]
theorem loop_spec
    (iter : core.ops.range.Range Usize)
    (self : PolyEncoder) (idx : U16)
    (out : alloc.vec.Vec U8)
    (h_end_le : iter.end.val ≤ 16)
    (h_start_le : iter.start ≤ iter.end)
    (h_idx_overflow : idx * 16 + 16 ≤ Usize.max)
    (h_out_overflow : out.length + 2 * iter.end ≤ Usize.max)
    (h_admissible : ∀ pts, self.s = .Points pts →
        ∀ (j : Nat), j < 16 →
          let len := (pts[j]!).value.length
          len = 0 ∨ len = 1 ∨ len = 3 ∨ len = 5 ∨
          len = 30 ∨ len = 34 ∨ len = 36)
    (h_coeff_bound : ∀ polys, self.s = .Polys polys →
        ∀ (j : Nat), j < 16 →
          (polys[j]!).coefficients.length + 1 ≤ Usize.max) :
    chunk_at_loop iter self idx out ⦃ (result : PolyEncoder × (alloc.vec.Vec U8)) =>
      result.1.idx = self.idx ∧
      result.2.length = out.length + 2 * (iter.end - iter.start) ∧
      (∀ (j : Nat), iter.start ≤ j → j < iter.end →
        ∃ (g : GF16),
          256 * result.2[out.length + 2 * (j - iter.start)]!
          + result.2[out.length + 2 * (j - iter.start) + 1]! = g.value.val) ∧
      match self.s with
      | .Polys polys =>
          result.1 = self ∧
          ∀ (j : Nat), iter.start ≤ j → j < iter.end →
            Nat.toGF216 (256 * result.2[out.length + 2 * (j - iter.start)]!
              + result.2[out.length + 2 * (j - iter.start) + 1]!) =
              (polys[j]!).toGF216Poly.eval (idx.val.toGF216)
      | .Points pts =>
          ∀ polys', result.1.s = .Polys polys' →
            ∀ (j : Nat), j < 16 →
              polys'[j]!.toGF216Poly =
                ∑ k ∈ Finset.range (pts[j]!).value.length,
                  C (((pts[j]!).value[k]!).toGF216) *
                    scaledLagrangeBasis (alloc.vec.Vec.len ((pts[j]!).value)) k ⦄ := by
  unfold chunk_at_loop
  apply loop.spec_decr_nat
    (measure := fun (p : core.ops.range.Range Usize × PolyEncoder × alloc.vec.Vec U8) =>
        p.1.end - p.1.start)
    (inv := fun (p : core.ops.range.Range Usize × PolyEncoder × alloc.vec.Vec U8) =>
        p.1.end = iter.end ∧
        iter.start ≤ p.1.start ∧
        p.1.start ≤ p.1.end ∧
        p.2.1.idx = self.idx ∧
        p.2.2.val.length = out.val.length +
          2 * (p.1.start - iter.start) ∧
        (∀ polys, self.s = .Polys polys → p.2.1 = self) ∧
        (∀ pts, p.2.1.s = .Points pts →
          ∀ (j : Nat), j < 16 →
            let len := (pts[j]!).value.length
            len = 0 ∨ len = 1 ∨ len = 3 ∨ len = 5 ∨
            len = 30 ∨ len = 34 ∨ len = 36) ∧
        (∀ (j : Nat), iter.start ≤ j → j < p.1.start →
          ∃ (g : encoding.gf.GF16),
             256 * p.2.2.val[out.length + 2 * (j - iter.start)]! +
             p.2.2.val[out.val.length +
              2 * (j - iter.start) + 1]! = g.value.val) ∧
        (∀ polys, self.s = .Polys polys →
          ∀ (j : Nat), iter.start ≤ j → j < p.1.start →
            Nat.toGF216 (256 * p.2.2.val[out.length + 2 * (j - iter.start)]! +
               p.2.2.val[out.val.length +
                2 * (j - iter.start) + 1]!) =
               (polys[j]!).toGF216Poly.eval (idx.val.toGF216)) ∧
        (∀ pts', p.2.1.s = .Points pts' → p.2.1 = self) ∧
        (∀ polys, p.2.1.s = .Polys polys →
            ∀ (j : Nat), j < 16 →
              (polys[j]!).coefficients.length + 1 ≤ Usize.max) ∧
        (∀ pts, self.s = .Points pts →
          ∀ polys', p.2.1.s = .Polys polys' →
            ∀ (j : Nat), j < 16 →
              polys'[j]!.toGF216Poly =
                ∑ k ∈ Finset.range (pts[j]!).value.length,
                  C (((pts[j]!).value[k]!).toGF216) *
                    scaledLagrangeBasis (alloc.vec.Vec.len ((pts[j]!).value)) k))
  · rintro ⟨iter', self', out'⟩ ⟨h_end', h_iter_ge, h_start_le', h_idx', h_out_len',
                                  h_stable', h_adm', h_pre', h_poly_pre',
                                  h_pts_stable', h_coeff_inv', h_lagrange'⟩
    simp only at h_end' h_iter_ge h_start_le' h_idx' h_out_len' h_stable' h_adm'
    simp only at  h_pre' h_pts_stable' ⊢
    dsimp at h_poly_pre' h_coeff_inv' h_lagrange'
    have h_end_val : iter'.end.val = iter.end.val := by rw [h_end']
    -- value-level forms of the invariant's scalar facts, for `omega`
    have h_iter_ge'' : iter.start.val ≤ iter'.start.val := h_iter_ge
    have h_start_le'' : iter'.start.val ≤ iter'.end.val := h_start_le'
    have h_out_len'' : out'.val.length = out.val.length + 2 * (iter'.start.val - iter.start.val) :=
      h_out_len'
    have h_out_ovf : out.val.length + 2 * iter.end.val ≤ Usize.max := h_out_overflow
    have h_coeff' : ∀ polys, self'.s = .Polys polys →
        ∀ (j : Nat), j < 16 →
          (polys[j]!).coefficients.length + 1 ≤ Usize.max :=
      h_coeff_inv'
    by_cases h_iter_lt : iter'.start.val < iter'.end.val
    · have h_body := body_spec idx iter' self' out'
        (by omega) h_idx_overflow (by simp only [alloc.vec.Vec.length]; omega) h_adm' h_coeff'
      apply WP.spec_mono h_body
      intro cf h_cf
      match cf with
      | ControlFlow.done (self'', out'') =>
        simp only [] at h_cf ⊢
        obtain ⟨_, _, h_not_lt⟩ := h_cf
        exact absurd h_iter_lt h_not_lt
      | ControlFlow.cont (iter'', self'', out'') =>
        simp only [] at h_cf ⊢
        obtain ⟨h_lt, h_start1, h_end1, g, hi, lo, h_out_eq, h_encode, h_idx1, h_match⟩ := h_cf
        have h_start1' : iter''.start.val = iter'.start.val + 1 := h_start1
        have h_end1' : iter''.end.val = iter'.end.val := by rw [h_end1]
        constructor
        · refine ⟨by rw [h_end1]; exact h_end',
                 show iter.start.val ≤ iter''.start.val by omega,
                 show iter''.start.val ≤ iter''.end.val by omega,
                 h_idx1.trans h_idx',
                 by rw [h_out_eq]; simp only [List.length_append, List.length_cons,
                   List.length_nil]; omega,
                 ?_, ?_, fun j hj1 hj2 => ?_, fun polys h_polys j hj1 hj2 => ?_,
                 ?_, ?_, ?_⟩
          · intro polys h_polys
            have h_self'_eq := h_stable' polys h_polys
            subst h_self'_eq
            simp only [h_polys] at h_match
            exact h_match.2
          · intro pts h_pts j hj
            cases h_s : self'.s with
            | Points pts' =>
              simp only [h_s] at h_match
              by_cases h_cache :
                  idx < (pts'[iter'.start]!).value.length
              · simp only [ite_eq_left h_cache] at h_match
                rw [h_match.2] at h_pts
                exact h_adm' pts h_pts j hj
              · simp only [ite_eq_right h_cache] at h_match
                simp [h_pts] at h_match
            | Polys polys' =>
              simp only [h_s] at h_match
              rw [h_match.2] at h_pts
              simp [h_s] at h_pts
          · -- the bytes of entry `j`: unchanged for `j < iter'.start`, new for `j = iter'.start`
            simp only [alloc.vec.Vec.length, h_out_eq]
            by_cases hj_lt : j < iter'.start.val
            · obtain ⟨g', hg'⟩ := h_pre' j hj1 hj_lt
              refine ⟨g', ?_⟩
              rw [getElem!_append_pair_of_lt (by omega), getElem!_append_pair_of_lt (by omega)]
              simpa only [alloc.vec.Vec.length] using hg'
            · obtain rfl : j = iter'.start.val := by omega
              have h1 : out.val.length + 2 * (iter'.start.val - iter.start.val) = out'.val.length :=
                h_out_len'.symm
              refine ⟨g, ?_⟩
              rw [h1, getElem!_append_pair_hi, getElem!_append_pair_lo]
              exact h_encode
          · simp only [alloc.vec.Vec.length, h_out_eq]
            by_cases hj_lt : j < iter'.start.val
            · have := h_poly_pre' polys h_polys j hj1 hj_lt
              rw [getElem!_append_pair_of_lt (by omega), getElem!_append_pair_of_lt (by omega)]
              simpa only [alloc.vec.Vec.length] using this
            · obtain rfl : j = iter'.start.val := by omega
              have h1 : out.val.length + 2 * (iter'.start.val - iter.start.val) = out'.val.length :=
                h_out_len'.symm
              have h_self'_eq := h_stable' polys h_polys
              subst h_self'_eq
              simp only [h_polys] at h_match
              rw [h1, getElem!_append_pair_hi, getElem!_append_pair_lo, h_encode, ← h_match.1]
              simp [GF16.toGF216]
          · intro pts_new h_pts_new
            cases h_s : self'.s with
            | Points pts_curr =>
              simp only [h_s] at h_match
              by_cases h_cache : idx < (pts_curr[iter'.start]!).value.length
              · simp only [ite_eq_left h_cache] at h_match
                rw [h_match.2]
                exact h_pts_stable' pts_curr h_s
              · simp only [ite_eq_right h_cache] at h_match
                simp [h_pts_new] at h_match
            | Polys polys_curr =>
              simp only [h_s] at h_match
              rw [h_match.2] at h_pts_new
              simp [h_s] at h_pts_new
          · intro polys_coeff h_polys_coeff j hj
            cases h_s : self'.s with
            | Points pts_curr =>
              simp only [h_s] at h_match
              by_cases h_cache : idx < (pts_curr[iter'.start]!).value.length
              · simp only [ite_eq_left h_cache] at h_match
                rw [h_match.2] at h_polys_coeff
                simp [h_s] at h_polys_coeff
              · simp only [ite_eq_right h_cache] at h_match
                simp only [h_polys_coeff] at h_match
                exact h_match.2.1 j hj
            | Polys polys_curr =>
              simp only [h_s] at h_match
              rw [h_match.2] at h_polys_coeff
              exact h_coeff_inv' polys_coeff h_polys_coeff j hj
          · intro pts_init h_pts_init polys_new h_polys_new j hj
            cases h_s : self'.s with
            | Points pts_curr =>
              simp only [h_s] at h_match
              by_cases h_cache : idx < (pts_curr[iter'.start]!).value.length
              · simp only [ite_eq_left h_cache] at h_match
                rw [h_match.2] at h_polys_new
                simp [h_s] at h_polys_new
              · simp only [ite_eq_right h_cache] at h_match
                have h_self'_eq := h_pts_stable' pts_curr h_s
                subst h_self'_eq
                have h_pts_eq : pts_curr = pts_init := by
                  have h := h_s.symm.trans h_pts_init; cases h; rfl
                subst h_pts_eq
                simp only [h_polys_new] at h_match
                exact h_match.1 j hj
            | Polys polys_curr =>
              simp only [h_s] at h_match
              rw [h_match.2] at h_polys_new
              exact h_lagrange' pts_init h_pts_init polys_new h_polys_new j hj
        · show iter''.end.val - iter''.start.val < iter'.end.val - iter'.start.val
          omega
    · unfold body
      step with core.iter.range.IteratorRange.next_Usize_spec' iter' as
        ⟨opt, iter1', h_none, h_some⟩
      obtain ⟨h_opt_eq, _⟩ := h_none h_iter_lt
      subst h_opt_eq
      dsimp
      have h_start_eq : iter'.start.val = iter.end.val := by omega
      refine (WP.spec_ok _).mpr ⟨h_idx', ?_, fun j hj1 hj2 => h_pre' j hj1 (by omega), ?_⟩
      · change out'.val.length = out.val.length + 2 * (iter.end.val - iter.start.val)
        omega
      · cases h_s : self.s with
        | Polys polys =>
          exact ⟨h_stable' polys h_s, fun j hj1 hj2 =>
            h_poly_pre' polys h_s j hj1 (by omega)⟩
        | Points pts =>
          intro polys' h2 j hj
          exact h_lagrange' pts h_s polys' (by simpa using h2) j hj
  · dsimp
    constructor; · exact rfl
    constructor; · exact le_refl _
    constructor; · exact h_start_le
    constructor; · exact rfl
    constructor; · simp
    constructor; · exact fun _ _ => rfl
    constructor; · exact h_admissible
    constructor; · exact fun j h1 h2 => absurd h2 (by omega)
    constructor; · exact fun _ _ j h1 h2 => absurd h2 (by omega)
    constructor; · exact fun _ _ => rfl
    constructor
    · intro polys h_polys
      exact h_coeff_bound polys h_polys
    intro pts h1 polys' h2 j hj
    exfalso
    have h2' : self.s = .Polys polys' := by simpa using h2
    simp [h1] at h2'

end spqr.encoding.polynomial.PolyEncoder.chunk_at_loop

/-!
# Spec theorem for `spqr::encoding::polynomial::{PolyEncoder}::chunk_at`

Serializes one chunk of 16 polynomial evaluations into a 32-byte `Chunk`. Allocates an output
vector, runs the serialization loop (`chunk_at_loop`) over `0..16`, converts the 32-byte result
to a fixed-size array via `try_into().expect(...)`, and returns `Chunk { index: idx, data }`.

The proof composes `chunk_at_loop.loop_spec`, `Vec::index` with `RangeFull`,
`TryFrom<&[u8]>::try_from`, and `Result::expect`.

**Source**: spqr/src/encoding/polynomial.rs (lines 694:4-710:5) -/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf Polynomial

namespace spqr.encoding.polynomial.PolyEncoder

/-! ## Spec theorems -/

/-- **Spec theorem for `encoding.polynomial.PolyEncoder.chunk_at`** (byte-level):

Serializes 16 polynomial evaluations into a 32-byte `Chunk` satisfying:
- `chunk.index = idx` — chunk index preserved.
- `chunk.data.val.length = 32` — exactly 32 bytes.
- `self'.idx = self.idx` — encoder index preserved.
- **Polys**: encoder state unchanged; each byte pair decodes to
  `(polys[j]!).toGF216Poly.eval (idx.val.toGF216)`.
- **Points**: Lagrange interpolation identity preserved for any resulting Polys state.

**Source**: spqr/src/encoding/polynomial.rs (lines 694:4-710:5) -/
@[step]
theorem chunk_at_spec
    (self : encoding.polynomial.PolyEncoder) (idx : Std.U16)
    (h_idx_overflow : idx.val * 16 + 16 ≤ Usize.max)
    (h_admissible : ∀ pts, self.s = .Points pts →
        ∀ (j : Nat), j < 16 →
          let len := (pts[j]!).value.length
          len = 0 ∨ len = 1 ∨ len = 3 ∨ len = 5 ∨
          len = 30 ∨ len = 34 ∨ len = 36)
    (h_coeff_bound : ∀ polys, self.s = .Polys polys →
        ∀ (j : Nat), j < 16 →
          (polys[j]!).coefficients.length + 1 ≤ Usize.max) :
    chunk_at self idx ⦃ ((chunk, self') :
        encoding.Chunk × encoding.polynomial.PolyEncoder) =>
      chunk.index = idx ∧
      chunk.data.val.length = 32 ∧
      self'.idx = self.idx ∧
      match self.s with
      | .Polys polys =>
          self' = self ∧
          ∀ (j : Nat), j < 16 →
            Nat.toGF216 (256 * chunk.data.val[2 * j]! + chunk.data.val[2 * j + 1]!) =
              (polys[j]!).toGF216Poly.eval (idx.val.toGF216)
      | .Points pts =>
          ∀ polys', self'.s = .Polys polys' →
            ∀ (j : Nat), j < 16 →
              polys'[j]!.toGF216Poly =
                ∑ k ∈ Finset.range (pts[j]!).value.length,
                  C (((pts[j]!).value[k]!).toGF216) *
                    scaledLagrangeBasis (alloc.vec.Vec.len ((pts[j]!).value)) k ⦄ := by
  unfold chunk_at
  have h_wc : (alloc.vec.Vec.with_capacity U8 32#usize).length = 0 := by
    simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new]
  step with chunk_at_loop.loop_spec as ⟨self1, out1, h_idx1, h_len1, h_bytes1, h_match1⟩
  simp only [h_wc, Nat.sub_zero, zero_add] at h_len1 h_match1
  step as ⟨s, h_s⟩
  step as ⟨r, arr, h_r, h_arr⟩
  rw [h_r]
  simp only [core.result.Result.expect, bind_ok, WP.spec_ok]
  refine ⟨trivial, by simp, h_idx1, ?_⟩
  cases hs : self.s with
  | Polys polys =>
    simp only [hs] at h_match1 ⊢
    obtain ⟨h_eq, h_bytes⟩ := h_match1
    refine ⟨h_eq, fun j hj => ?_⟩
    simpa [h_arr, h_s, alloc.vec.Vec.getElem!_Nat_eq] using h_bytes j (Nat.zero_le _) hj
  | Points pts =>
    simp only [hs] at h_match1 ⊢
    exact h_match1

end spqr.encoding.polynomial.PolyEncoder
