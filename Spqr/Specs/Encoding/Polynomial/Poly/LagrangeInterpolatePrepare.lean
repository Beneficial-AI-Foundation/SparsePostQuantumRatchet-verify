/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import Spqr.Specs.Encoding.Polynomial.Poly.Zero
import Spqr.Specs.Encoding.Gf.GF16.Eq
import Spqr.Specs.Encoding.Gf.GF16.ONE
import Spqr.Specs.Encoding.Gf.GF16.ZERO
import Spqr.Specs.Encoding.Polynomial.Poly.MultXdiffAssignTrailing
public import Spqr.Math.Poly.ExpectedTrailing.Defs
public import Spqr.Math.Poly.LinearFactors.Basic
public import SrcTranslated.Funs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Tactic.ComputeDegree
import Spqr.Math.Gf16.Irreducible
import Spqr.Math.Poly.Coeff.MultXdiffPolyIdentity
import Spqr.Math.Poly.LinearFactors.Degree
import Spqr.Specs.Aeneas.RangeIteratorNext
import Spqr.Specs.Encoding.Gf.GF16.Mul
import Spqr.Specs.Encoding.Gf.GF16.SubAssign

/-! # Spec theorem for `lagrange_interpolate_prepare`: loop body 0

Builds `∏_{j<offset} (x − pts[j].x)` by iteratively calling
`mult_xdiff_assign_trailing(offset − i, pts[i].x)` for `i` in `0..offset`.

In char 2: `(x − a) = (x ⊕ a)`. The recurrence is `v[j−1] −= v[j] * diff`.

Invariant: vector length = `offset + 1`; after `i` steps
`p[offset−i..]` = `∏_{j<i} (x − pts[j].x)`.

**Source**: spqr/src/encoding/polynomial.rs -/

@[expose] public section

open Aeneas Aeneas.Std  spqr.encoding.gf Polynomial

namespace spqr.encoding.polynomial.Poly.lagrange_interpolate_prepare_loop

/-- **Spec theorem for `encoding.polynomial.Poly.lagrange_interpolate_prepare_loop.body`**

One iteration of the `∏(x − pts[j].x)` construction. Always succeeds.
- `done`: iterator exhausted, polynomial unchanged.
- `cont`: iterator advanced by one, vector length preserved. Modified positions satisfy
  `p'[j] = p[j] − p[j+1] * pts[i].x` (in GF(2¹⁶)); all other positions unchanged.

Propagates the `mult_xdiff_assign_trailing` spec with `start = offset − i`,
`diff = pts[i].x`.

**Source**: spqr/src/encoding/polynomial.rs -/
@[step]
theorem body_spec
    (pts : Slice Pt)
    (offset : Usize)
    (iter : core.ops.range.Range Usize)
    (p : Poly)
    (h_end_le_pts : iter.end ≤ pts.length)
    (h_end_le_offset : iter.end ≤ offset)
    (h_offset_lt_len : offset < p.coefficients.length) :
    body pts offset iter p ⦃ cf =>
      match cf with
      | ControlFlow.done r =>
          r = p ∧ ¬ (iter.start < iter.end)
      | ControlFlow.cont (iter1, p1) =>
          iter.start < iter.end ∧
          iter1.start = iter.start.val + 1 ∧
          iter1.end = iter.end ∧
          p1.coefficients.length = p.coefficients.length ∧
          (∀ (j : Nat),
            offset - iter.start ≤ j + 1 →
            j + 1 < p.coefficients.length →
            ∀ (hj : j < p1.coefficients.length),
              (p1.coefficients[j]'hj).toGF216 =
                (p.coefficients[j]!).toGF216 -
                (p.coefficients[j + 1]!).toGF216 *
                  (pts[iter.start.val]!).x.toGF216) ∧
          (∀ (j : Nat),
            ¬(offset - iter.start ≤ j + 1 ∧
              j + 1 < p.coefficients.length) →
            p1.coefficients[j]? = p.coefficients[j]?) ⦄ := by
  unfold body
  step with core.iter.range.IteratorRange.next_Usize_spec' iter as
    ⟨opt, iter1', h_none, h_some⟩
  by_cases h_lt : iter.start.val < iter.end.val
  · obtain ⟨h_opt_eq, h_start1, h_end1⟩ := h_some h_lt
    rw [h_opt_eq]
    have h_end_pts : iter.end.val ≤ pts.val.length := h_end_le_pts
    have h_end_off : iter.end.val ≤ offset.val := h_end_le_offset
    have h_i_lt_pts : iter.start.val < pts.val.length := by omega
    step as ⟨pi, h_pi⟩
    step as ⟨i1, h_i1, _⟩
    step as ⟨p1, h_len, h_mod, h_frame, _⟩
    have h_pi' : (pts[iter.start.val]!) = pi := by
      rw [h_pi, Slice.getElem!_Nat_eq, getElem!_pos pts.val iter.start.val h_i_lt_pts]
    refine ⟨h_lt, h_start1, h_end1, h_len, fun j hj1 hj2 hj => ?_, fun j hj => ?_⟩
    · rw [h_pi']
      simpa only [alloc.vec.Vec.getElem_Nat_eq, alloc.vec.Vec.getElem!_Nat_eq,
        List.get_eq_getElem] using h_mod j (by omega) hj2 hj
    · have h_pl : p.coefficients.length = p.coefficients.val.length := rfl
      have h_eq := h_frame j (by omega)
      have h_len' : p1.coefficients.val.length = p.coefficients.val.length := h_len
      simp only [alloc.vec.Vec.getElem?_Nat_eq]
      by_cases hj_lt : j < p.coefficients.val.length
      · rw [List.getElem?_eq_getElem hj_lt, List.getElem?_eq_getElem (by omega),
          ← getElem!_pos p.coefficients.val j hj_lt,
          ← getElem!_pos p1.coefficients.val j (by omega), h_eq]
      · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  · obtain ⟨h_opt_eq, rfl⟩ := h_none h_lt
    rw [h_opt_eq]
    exact (WP.spec_ok _).mpr ⟨rfl, h_lt⟩

/-! # Spec theorem for `lagrange_interpolate_prepare`: loop 0

Full loop building `∏_{j<offset} (x − pts[j].x)` via repeated `mult_xdiff_assign_trailing`.

Invariants: vector length = `offset + 1`, leading coeff = `ONE`, trailing sub-polynomial
`p[offset−i..]` = `∏_{j<i} (x − pts[j].x)`.

**Source**: spqr/src/encoding/polynomial.rs -/

@[step]
theorem loop_spec
    (pts : Slice Pt)
    (offset : Usize)
    (iter : core.ops.range.Range Usize)
    (p : Poly)
    (h_end_le_pts : iter.end ≤ pts.length)
    (h_end_le_offset : iter.end ≤ offset)
    (h_len_eq : p.degree = offset + 1)
    (h_le : iter.start ≤ iter.end)
    (h_start_zero : iter.start.val = 0) :
    lagrange_interpolate_prepare_loop
      iter pts p offset ⦃ (result : Poly) =>
      result.degree = p.degree ∧
      result.coefficients[offset.val]! =
        p.coefficients[offset.val]! ∧
      (∀ (hoff : offset.val < result.degree),
        (result.coefficients[offset.val]'hoff).toGF216 =
          (p.coefficients[offset.val]!).toGF216) ∧
      (∀ (j : Nat), ¬(offset.val - iter.end ≤ j ∧ j < offset) →
        result.coefficients[j]? = p.coefficients[j]?) ∧
      (∀ (m : Nat),
        m ≤ iter.end - iter.start →
        ∀ (hpos : offset - (iter.end - iter.start) + m <
                    result.degree),
          GF16.toGF216
            (result.coefficients[offset - (iter.end - iter.start) + m]) =
            (expectedTrailingPoly p.coefficients pts offset
              iter.start (iter.end - iter.start)).coeff m) ⦄ := by
  unfold spqr.encoding.polynomial.Poly.lagrange_interpolate_prepare_loop
  simp only [degree, alloc.vec.Vec.length] at h_len_eq
  apply loop.spec_decr_nat
    (measure := fun (st : core.ops.range.Range Usize × Poly) =>
                  st.1.end.val - st.1.start.val)
    (inv := fun (st : core.ops.range.Range Usize × Poly) =>
        st.1.end = iter.end ∧
        iter.start ≤ st.1.start.val ∧
        st.1.start.val ≤ iter.end.val ∧
        st.2.degree = p.degree ∧
        st.2.coefficients[offset.val]? =
          p.coefficients[offset.val]? ∧
        (∀ (hoff : offset.val < st.2.coefficients.length),
          (st.2.coefficients.val.get ⟨offset, hoff⟩).toGF216 =
            (p.coefficients[offset]!).toGF216) ∧
        (∀ (j : Nat),
          ¬(offset - st.1.start ≤ j ∧ j < offset.val) →
          st.2.coefficients[j]? = p.coefficients[j]?) ∧
        (∀ (m : Nat), m ≤ st.1.start.val - iter.start.val →
          ∀ (hpos : offset.val - (st.1.start - iter.start) + m < st.2.degree),
            GF16.toGF216
              (st.2.coefficients.val.get
                ⟨offset - (st.1.start - iter.start) + m, hpos⟩) =
              (expectedTrailingPoly p.coefficients pts offset
                iter.start (st.1.start - iter.start)).coeff m))
  · rintro ⟨iter', p'⟩ hinv
    dsimp only at hinv
    obtain ⟨h_end', h_ge', h_le', h_len', h_off', h_gf16_off', h_frame', h_trail'⟩ := hinv
    have h_end_val : iter'.end.val = iter.end.val := by rw [h_end']
    have h_end_off : iter.end.val ≤ offset.val := h_end_le_offset
    have h_end_pts : iter.end.val ≤ pts.length := h_end_le_pts
    have hP'len : p'.coefficients.val.length = offset.val + 1 := by
      have : p'.coefficients.val.length = p.coefficients.val.length := h_len'
      omega
    apply WP.spec_mono (body_spec pts offset iter' p' (show iter'.end.val ≤ pts.length by omega)
      (show iter'.end.val ≤ offset.val by omega)
      (show offset.val < p'.coefficients.val.length by omega))
    rintro (⟨iter'', p''⟩ | r) h_cf
    · obtain ⟨h_lt, h_start1, h_end1, h_v1len, h_modified, h_frame⟩ := h_cf
      have h_lt' : iter'.start.val < iter'.end.val := h_lt
      have hRlen : p''.coefficients.val.length = offset.val + 1 := by
        have : p''.coefficients.val.length = p'.coefficients.val.length := h_v1len
        omega
      have hP'len' : p'.coefficients.length = offset.val + 1 := hP'len
      -- position `offset` and everything below the touched window are unchanged
      have h_keep : ∀ j, ¬(offset.val - iter''.start.val ≤ j ∧ j < offset.val) →
          p''.coefficients[j]? = p.coefficients[j]? := by
        intro j hj
        rw [h_frame j (by omega)]
        exact h_frame' j (by omega)
      have h_off'' : p''.coefficients[offset.val]? = p.coefficients[offset.val]? :=
        h_keep offset.val (by omega)
      dsimp only
      have h_end1' : iter''.end.val = iter'.end.val := by rw [h_end1]
      refine ⟨⟨h_end1.trans h_end', by omega, by omega, h_v1len.trans h_len', h_off'', ?_, h_keep,
        fun m hm hpos => ?_⟩, show iter''.end.val - iter''.start.val <
          iter'.end.val - iter'.start.val by omega⟩
      · intro hoff
        have h_eq : p''.coefficients.val[offset.val]? = p'.coefficients.val[offset.val]? :=
          h_frame offset.val (by omega)
        rw [← h_gf16_off' (by omega)]
        simp only [List.get_eq_getElem]
        rw [List.getElem?_eq_getElem hoff, List.getElem?_eq_getElem (by omega)] at h_eq
        rw [Option.some_inj.mp h_eq]
      · obtain ⟨k, hk⟩ : ∃ k, iter'.start.val - iter.start.val = k := ⟨_, rfl⟩
        have hk1 : iter''.start.val - iter.start.val = k + 1 := by omega
        simp only [hk1, List.get_eq_getElem]
        simp only [hk] at h_trail'
        rw [expectedTrailingPoly_succ]
        have hs : iter'.start.val = iter.start.val + k := by omega
        have hk_off : k + 1 ≤ offset.val := by omega
        have hx : (pts[iter'.start.val]!).x.toGF216 =
            (pts.val[iter.start.val + k]!).x.toGF216 := by
          rw [Slice.getElem!_Nat_eq, hs]
        have hT : ∀ m ≤ k, (p'.coefficients.val[offset.val - k + m]!).toGF216 =
            (expectedTrailingPoly p.coefficients pts offset iter.start k).coeff m := by
          intro m hm
          rw [getElem!_pos _ _ (by omega)]
          exact h_trail' m hm (by change _ < p'.coefficients.val.length; omega)
        have hMod : ∀ j, offset.val - k ≤ j + 1 → j + 1 < offset.val + 1 →
            (p''.coefficients.val[j]!).toGF216 =
              (p'.coefficients.val[j]!).toGF216 - (p'.coefficients.val[j + 1]!).toGF216 *
                (pts.val[iter.start.val + k]!).x.toGF216 := by
          intro j hj1 hj2
          have := h_modified j (by omega) (by change _ < p'.coefficients.val.length; omega)
            (by change _ < p''.coefficients.val.length; omega)
          rw [getElem!_pos _ _ (by omega), ← hx]
          simpa only [alloc.vec.Vec.getElem_Nat_eq, alloc.vec.Vec.getElem!_Nat_eq] using this
        rw [← getElem!_pos _ _ (by omega)]
        rcases Nat.lt_or_ge m (k + 1) with hm_lt | hm_ge
        · rw [hMod _ (by omega) (by omega)]
          cases m with
          | zero =>
            have hFr : p'.coefficients.val[offset.val - (k + 1)]! =
                p.coefficients.val[offset.val - (k + 1)]! := by
              have := h_frame' (offset.val - (k + 1)) (by omega)
              simp only [alloc.vec.Vec.getElem?_Nat_eq] at this
              simp only [List.getElem!_eq_getElem?_getD, this]
            rw [coeff_zero_C_add_X_sub_C_mul, Nat.add_zero, hFr,
              show offset.val - (k + 1) + 1 = offset.val - k + 0 by omega, hT 0 (by omega),
              mul_comm]
          | succ m' =>
            rw [coeff_succ_C_add_X_sub_C_mul,
              show offset.val - (k + 1) + (m' + 1) = offset.val - k + m' by omega,
              hT m' (by omega), show offset.val - k + m' + 1 = offset.val - k + (m' + 1) by omega,
              hT (m' + 1) (by omega), mul_comm]
        · obtain rfl : m = k + 1 := by omega
          have hFr :
              p''.coefficients.val[offset.val]! = p'.coefficients.val[offset.val]! := by
            have := h_frame offset.val (by omega)
            simp only [alloc.vec.Vec.getElem?_Nat_eq] at this
            simp only [List.getElem!_eq_getElem?_getD, this]
          rw [coeff_succ_C_add_X_sub_C_mul,
            show offset.val - (k + 1) + (k + 1) = offset.val by omega, hFr, ← hT k le_rfl,
            show offset.val - k + k = offset.val by omega,
            expectedTrailingPoly_coeff_eq_zero_of_lt _ _ _ _ _ _ (by omega : k < k + 1),
            mul_zero, sub_zero]
    · obtain ⟨rfl, h_nlt⟩ := h_cf
      have h_nlt' : ¬iter'.start.val < iter'.end.val := h_nlt
      have h_eq : iter'.start.val = iter.end.val := by omega
      refine ⟨h_len', ?_, h_gf16_off', fun j hj => h_frame' j (by omega), fun m hm hpos => ?_⟩
      · simp only [alloc.vec.Vec.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD]
        exact congrArg (·.getD default) h_off'
      · have h_iters_eq : iter'.start.val - iter.start.val = iter.end.val - iter.start.val := by
          omega
        rw [h_iters_eq] at h_trail'
        exact h_trail' m hm hpos
  · refine ⟨rfl, le_refl _, h_le, rfl, rfl, ?_, ?_, ?_⟩
    · intro hoff
      rw [List.get_eq_getElem, ← getElem!_pos p.coefficients.val offset.val hoff]
      rfl
    · intro _ _; rfl
    · intro m hm hpos
      have hm0 : m = 0 := by dsimp only at hm; omega
      subst hm0
      simp only [Nat.sub_self, expectedTrailingPoly_zero, coeff_C_zero]
      congr 1
      exact (getElem!_pos p.coefficients.val offset.val (by omega)).symm

end spqr.encoding.polynomial.Poly.lagrange_interpolate_prepare_loop

/-! # Spec theorem for `lagrange_interpolate_prepare`

Constructs `∏_{j<pts.len()} (x − pts[j].x)` as a `Poly` of degree `pts.len()`.

**Source**: spqr/src/encoding/polynomial.rs (lines 144:4-163:5) -/

namespace spqr.encoding.polynomial.Poly

open encoding.gf.GF16

/-- **Spec theorem for `encoding.polynomial.Poly.lagrange_interpolate_prepare`**

Always succeeds when `pts.length + 1 ≤ Usize.max`. Guarantees:
- `result.coefficients.length = pts.length + 1`
- Leading coeff is `ONE` (matches Rust `debug_assert_eq!` at line 161), mapping to `1` in GF(2¹⁶).
- Each coefficient matches `prodLinearFactors` coefficient-wise under `toGF216`.
- `result.toGF216Poly = prodLinearFactors pts 0 pts.length` -/
@[step]
theorem lagrange_interpolate_prepare_spec
    (pts : Slice Pt)
    (h_len : pts.length + 1 ≤ Usize.max) :
    lagrange_interpolate_prepare pts ⦃ (result : Poly) =>
      result.degree = pts.length + 1 ∧
      result.coefficients[pts.length]! = ONE ∧
      (∀ m ≤ pts.length,
        (result.coefficients[m]!).toGF216 = (prodLinearFactors pts 0 pts.length).coeff m) ∧
      result.toGF216Poly = prodLinearFactors pts 0 pts.length ⦄ := by
  unfold lagrange_interpolate_prepare
  have h_plen : (Slice.len pts).val = pts.length := Slice.len_val pts
  step as ⟨i1, h_i1⟩
  step as ⟨v, h_v, _⟩
  · rfl
  step as ⟨x, index_mut_back, _, h_imb⟩
  have h_c : (index_mut_back ONE).val =
      (List.replicate (pts.length + 1) ZERO).set pts.length ONE := by
    rw [h_imb, alloc.vec.Vec.set_val_eq, h_v, h_i1, h_plen]
  have h_clen : (index_mut_back ONE).val.length = pts.length + 1 := by
    rw [h_c, List.length_set, List.length_replicate]
  have h_one : (index_mut_back ONE).val[pts.length]! = ONE := by
    rw [h_c, list_getElem_bang_set_self _ _ _ (by simp)]
  step with lagrange_interpolate_prepare_loop.loop_spec as
    ⟨p, h_pdeg, h_poff, _, _, h_trail⟩
  · change (index_mut_back ONE).val.length = (Slice.len pts).val + 1
    rw [h_clen, h_plen]
  have h_pdeg' : p.coefficients.val.length = pts.length + 1 := by
    change p.coefficients.val.length = (index_mut_back ONE).val.length at h_pdeg
    rw [h_pdeg, h_clen]
  have h_pone : p.coefficients.val[pts.length]! = ONE := by
    have : p.coefficients[(Slice.len pts).val]! = (index_mut_back ONE)[(Slice.len pts).val]! :=
      h_poff
    simp only [alloc.vec.Vec.getElem!_Nat_eq, h_plen] at this
    rw [this, h_one]
  step as ⟨left_val, h_lv⟩
  step as ⟨b, h_b⟩
  have h_lv' : left_val = ONE := by
    rw [h_lv, ← getElem!_pos p.coefficients.val (Slice.len pts).val (by omega), h_plen, h_pone]
  have h_bt : b = true := h_b.mpr (by rw [h_lv'])
  step
  have h_bridge : expectedTrailingPoly
      ((List.replicate (pts.length + 1) ZERO).set pts.length ONE)
      pts pts.length 0 pts.length =
    prodLinearFactors pts 0 pts.length := by
    apply expectedTrailingPoly_eq_prodLinearFactors
    · have hlen : pts.length < (List.replicate (pts.length + 1) ZERO).length := by
        simp
      rw [list_getElem_bang_set_self _ _ _ hlen, ONE_toGF216]
    · intro j hj
      rw [getElem!_pos _ j (by simp only [List.length_set, List.length_replicate]; omega),
        List.getElem_set_ne (by omega), List.getElem_replicate, ZERO_toGF216]
    · exact le_refl _
    · exact le_refl _
  have h_coef : ∀ m ≤ pts.length,
      (p.coefficients.val[m]!).toGF216 = (prodLinearFactors pts 0 pts.length).coeff m := by
    intro m hm
    have h5 := h_trail m (by rw [h_plen]; omega)
      (by change _ < p.coefficients.val.length; rw [h_pdeg', h_plen]; omega)
    simp only [h_plen, Nat.sub_zero, Nat.sub_self, Nat.zero_add, h_c, h_bridge,
      alloc.vec.Vec.getElem_Nat_eq] at h5
    rw [getElem!_pos p.coefficients.val m (by omega)]
    exact h5
  refine ⟨h_pdeg', h_pone, h_coef, ?_⟩
  change listToGF216Poly p.coefficients = prodLinearFactors pts 0 pts.length
  apply listToGF216Poly_eq_of_coeffs
  · intro m hm
    have := h_coef m (by rw [h_pdeg'] at hm; omega)
    rwa [getElem!_pos p.coefficients.val m hm] at this
  · intro m hm
    exact prodLinearFactors_coeff_eq_zero_high _ _ _ _ (by rw [h_pdeg'] at hm; omega)

end spqr.encoding.polynomial.Poly
