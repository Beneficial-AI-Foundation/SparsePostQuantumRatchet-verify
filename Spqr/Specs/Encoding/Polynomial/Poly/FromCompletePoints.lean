/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Aeneas.EnumerateSliceIterNext
import Spqr.Specs.Encoding.Polynomial.ConstPolysToPolys
import Spqr.Specs.Encoding.Polynomial.Poly.LagrangeSum
import Spqr.Specs.Encoding.Polynomial.COMPLETE_POINTS_POLYS_1
import Spqr.Specs.Encoding.Polynomial.COMPLETE_POINTS_POLYS_3
import Spqr.Specs.Encoding.Polynomial.COMPLETE_POINTS_POLYS_5
import Spqr.Specs.Encoding.Polynomial.COMPLETE_POINTS_POLYS_30
import Spqr.Specs.Encoding.Polynomial.COMPLETE_POINTS_POLYS_34
import Spqr.Specs.Encoding.Polynomial.COMPLETE_POINTS_POLYS_36
/-! # Specification for `Poly::from_complete_points`

This file verifies the Rust function `Poly::from_complete_points` from
`src/encoding/polynomial.rs`. That function:

1. **Validates indices**: iterates over `pts.iter().enumerate()`, checking that
   each point's x-coordinate equals its position (`pt.x.value == i as u16`).
   Returns `Err(())` on the first mismatch.

2. **Selects precomputed Lagrange basis polynomials**: matches on `pts.len()`
   against the admissible sizes `{0, 1, 3, 5, 30, 34, 36}` and loads the
   corresponding `COMPLETE_POINTS_POLYS_N` constant arrays, converting them
   to `Vec<Poly>` via `const_polys_to_polys`.

3. **Computes the Lagrange sum**: calls `Poly::lagrange_sum(pts, &polys)` to
   build the interpolation polynomial
   `p = Σⱼ pts[j].y · scaledLagrangeBasis(len, j)` in `GF(2¹⁶)[X]`.

**Source**: `src/encoding/polynomial.rs` -/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf Polynomial
open core.iter.adapters.enumerate core.slice.iter
open PolyConst.lagrange_interpolate_pt_loop


namespace spqr.encoding.polynomial.Poly.from_complete_points_loop

private lemma usize_cast_u16_val (x : Usize) (h : x.val ≤ UScalar.max .U16) :
    (UScalar.cast UScalarTy.U16 x).val = x.val :=
  UScalar.cast_inBounds_spec UScalarTy.U16 x h

/-- Shared postcondition for the `body_spec` helpers (an `abbrev` so `step*` unfolds it):

This captures the three possible outcomes of one iteration of the
`for (i, pt) in pts.iter().enumerate()` loop:

- **`done (Ok p)`** — the iterator was exhausted (`none` branch) and the
  Lagrange sum was successfully computed. The polynomial `p` satisfies
  `p.toGF216Poly = Σⱼ C(pts[j].y.toGF216) * scaledLagrangeBasis(len, j)`.

- **`done (Err ())`** — the current point failed index validation:
  `pts[i].x.value ≠ i`, so the function returns early with `Err(())`.

- **`cont iter'`** — the current point passed validation (`pts[i].x.value = i`),
  the iterator advanced by one, and the loop continues. -/
private abbrev bodyPost
    (pts : Slice Pt) (iter : Enumerate (Iter Pt)) :
    ControlFlow (Enumerate (Iter Pt)) (core.result.Result Poly Unit) → Prop :=
  fun cf =>
    match cf with
    | ControlFlow.done (core.result.Result.Ok p) =>
        ¬ (iter.iter.i < pts.val.length) ∧
        p.degree < Usize.max ∧
        p.toGF216Poly = ∑ j ∈ Finset.range pts.val.length,
          C ((pts.val[j]!).y.toGF216) * scaledLagrangeBasis (Slice.len pts) j
    | ControlFlow.done (core.result.Result.Err ()) =>
        ∃ (h_i : iter.iter.i < pts.val.length),
          (pts.val.get ⟨iter.iter.i, h_i⟩).x.value.val ≠
            iter.count.val
    | ControlFlow.cont iter' =>
        ∃ (h_i : iter.iter.i < pts.val.length),
          (pts.val.get ⟨iter.iter.i, h_i⟩).x.value.val =
            iter.count.val ∧
          iter'.iter.i = iter.iter.i + 1 ∧
          iter'.iter.slice = pts ∧
          iter'.count.val = iter.count.val + 1

/-! ## Spec helper: the `some` (validation) branch

Body spec for the `some` case: the iterator is still in bounds, so we get the current
`(index, point)` pair.  The proof unfolds `body`, applies the `EnumerateSliceIter_next_Pt_some`
lemma for the iterator step, then resolves the `if pt.x.value != i as u16` comparison
with `step*`. -/
private theorem body_spec_some_case
    (pts : Slice Pt)
    (iter : Enumerate (Iter Pt))
    (h_count : iter.count.val ≤ UScalar.max .U16)
    (h_slice_eq : iter.iter.slice = pts)
    (h_in_bounds : iter.iter.i < iter.iter.slice.val.length) :
    body pts iter ⦃ bodyPost pts iter ⦄ := by
  unfold body
  have h_count_bound : iter.count.val + 1 ≤ Usize.max := by scalar_tac
  step as ⟨opt, iter1, hnext⟩
  cases opt with
  | none => exact absurd h_in_bounds hnext.1
  | some p =>
    obtain ⟨idx, pt⟩ := p
    obtain ⟨h_lt', h_idx, h_pt, h_iter1_slice, h_iter1_i, h_iter1_count⟩ := hnext
    have h_lt_pts : iter.iter.i < pts.val.length := by
      rw [← h_slice_eq]; exact h_in_bounds
    have h_cast_val := usize_cast_u16_val iter.count h_count
    step*
    · simp_all
      grind
    · grind

/-! ## Spec helpers: the `none` (computation) branch by size

Empty slice case (`pts.len() == 0`): the Lagrange sum over zero points
is trivially the zero polynomial.  The `match` arm `0 => vec![]` produces
an empty `polys` vector, and `lagrange_sum` returns the zero accumulator. -/
private theorem body_spec_none_0
    (pts : Slice Pt)
    (iter : Enumerate (Iter Pt))
    (h_slice_eq : iter.iter.slice = pts)
    (h_out_of_bounds : ¬(iter.iter.i < iter.iter.slice.val.length))
    (h0 : pts.val.length = 0) :
    body pts iter ⦃ bodyPost pts iter ⦄ := by
  unfold body
  step as ⟨opt, iter1, hnext⟩
  cases opt with
  | some p =>
    obtain ⟨h_lt, -⟩ := hnext
    exact absurd h_lt h_out_of_bounds
  | none =>
    have h_not_lt : ¬ (iter.iter.i < pts.val.length) := by
      rw [← h_slice_eq]; exact hnext.1
    have h_len_0 : Slice.len pts = 0#usize := by
      ext
      simp [Slice.len]
      simp [h0]
      simp [Usize.ofNatCore]
    step as ⟨ s, hs⟩
    have : s = 0#uscalar := by
      simp only [hs, h_len_0]
      simp[UScalar.cast]
    simp only [this, BitVec.ofNat_eq_ofNat, UScalarTy.U64_numBits_eq]
    step
    unfold bodyPost
    simp only [not_lt, List.getElem!_eq_getElem?_getD]
    constructor
    · grind
    · simp_all

/-- For a single point, `scaledLagrangeBasis 1#usize 0` is the constant `1`.
This is the base case: with only one evaluation point at `x = 0`, the
Lagrange basis polynomial is `L₀(X) = 1` (no other points to interpolate
against), so `scaledLagrangeBasis(1, 0) = 1`. -/
private lemma scaledLagrangeBasis_one_zero :
    scaledLagrangeBasis (1#usize) 0 = 1 := by
  simp only [global_simps]
  rw [condProdLinearFactors_skip _ _ 0 (by simp ),
      condProdLinearFactors_ge _ _ 1 (by simp ),
      lagrangeDenomProd_skip _ _ 0 (by simp ),
      lagrangeDenomProd_eq_one_of_le _ _ 1 (by simp )] <;>
  simp_all [ GF16.toGF216, one_pow, mul_one, map_one,
            List.length_finRange, List.get_eq_getElem, Nat.toGF216,
            spqr.math.gf.natToBinaryPoly_one]

/-- Non-empty admissible sizes (`N ∈ {1, 3, 5, 30, 34, 36}`): when the
iterator is exhausted, the code enters the `match pts.len() as u64`
and selects the precomputed `COMPLETE_POINTS_POLYS_N`.  This theorem
unfolds the `body`, applies `const_polys_to_polys` for the matched
size, and verifies that the resulting `lagrange_sum` equals the
mathematical Lagrange interpolation formula:
  `p.toGF216Poly = Σⱼ C(pts[j].y.toGF216) * scaledLagrangeBasis(N, j)`. -/
private theorem body_spec_none_N
    (N : Nat)
    (pts : Slice Pt)
    (iter : Enumerate (Iter Pt))
    (h_slice_eq : iter.iter.slice = pts)
    (h_out_of_bounds : ¬(iter.iter.i < iter.iter.slice.val.length))
    (hN : pts.val.length = N)
    (hN_admissible : N = 1 ∨ N = 3 ∨ N = 5 ∨ N = 30 ∨ N = 34 ∨ N = 36) :
    body pts iter ⦃ bodyPost pts iter ⦄ := by
  unfold body
  step as ⟨opt, iter1, hnext⟩
  cases opt with
  | some p =>
    obtain ⟨h_lt, -⟩ := hnext
    exact absurd h_lt h_out_of_bounds
  | none =>
    have h_not_lt : ¬ (iter.iter.i < pts.val.length) := by
      rw [← h_slice_eq]; exact hnext.1
    rcases hN_admissible with rfl | rfl | rfl | rfl | rfl | rfl
    · have h_len_N : Slice.len pts = 1#usize := by simp [Slice.len, hN, Usize.ofNatCore]
      step as ⟨ s, hs⟩
      have : s = 1#uscalar := by simp [hs, h_len_N]; simp [UScalar.cast]; grind
      simp only [this, BitVec.ofNat_eq_ofNat, UScalarTy.U64_numBits_eq]; step
      unfold bodyPost
      simp only [not_lt, List.getElem!_eq_getElem?_getD, ne_eq, List.get_eq_getElem]
      step; step
      · have : (polys.deref).val.length = (polys).val.length := by
          simp [alloc.vec.Vec.deref]
        grind
      · intros i hi
        have : (polys.deref.val[i]!.coefficients).val.length =
          (polys.val[i]!.coefficients).val.length := by
          simp [alloc.vec.Vec.deref]
        grind [degree]
      · constructor
        · grind
        · constructor
          · grind
          · rw [h_len_N]; simp only [alloc.vec.Vec.deref] at *; simp only [hN] at *
            rw [p_post2]; apply Finset.sum_congr rfl; intro x hx
            simp only [Finset.mem_range] at hx
            simp only [Slice.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD]; congr 1
            have hx_lt_polys : x < (↑polys : List Poly).length := by grind
            simp only [List.getElem?_eq_getElem hx_lt_polys, Option.getD_some]
            have hx0 : x = 0 := by omega
            subst hx0
            apply (polys_post2 0 (by omega) (by omega) (by omega)).2.trans
            simp_all [scaledLagrangeBasis_one_zero.symm]
    · have h_len_N : Slice.len pts = 3#usize := by simp [Slice.len, hN, Usize.ofNatCore]
      step as ⟨ s, hs⟩
      have : s = 3#uscalar := by simp [hs, h_len_N]; simp [UScalar.cast]; grind
      simp only [this, BitVec.ofNat_eq_ofNat, UScalarTy.U64_numBits_eq]; step
      unfold bodyPost
      simp only [not_lt, List.getElem!_eq_getElem?_getD, ne_eq, List.get_eq_getElem]
      step; step
      · have : (polys.deref).val.length = (polys).val.length := by
          simp [alloc.vec.Vec.deref]
        grind
      · intros i hi
        have : (polys.deref.val[i]!.coefficients).val.length =
          (polys.val[i]!.coefficients).val.length := by
          simp [alloc.vec.Vec.deref]
        grind [degree]
      · constructor
        · grind
        · constructor
          · grind
          · rw [h_len_N]; simp only [alloc.vec.Vec.deref] at *; simp only [hN] at *
            rw [p_post2]; apply Finset.sum_congr rfl; intro x hx
            simp only [Finset.mem_range] at hx
            simp only [Slice.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD]; congr 1
            have hx_lt_polys : x < (↑polys : List Poly).length := by grind
            simp only [List.getElem?_eq_getElem hx_lt_polys, Option.getD_some]
            have := (polys_post2 x (by omega) (by omega) (by grind)).2
            have := a_post x (by grind); simp_all
    · have h_len_N : Slice.len pts = 5#usize := by simp [Slice.len, hN, Usize.ofNatCore]
      step as ⟨ s, hs⟩
      have : s = 5#uscalar := by simp [hs, h_len_N]; simp [UScalar.cast]; grind
      simp only [this, BitVec.ofNat_eq_ofNat, UScalarTy.U64_numBits_eq]; step
      unfold bodyPost
      simp only [not_lt, List.getElem!_eq_getElem?_getD, ne_eq, List.get_eq_getElem]
      step; step
      · have : (polys.deref).val.length = (polys).val.length := by
          simp [alloc.vec.Vec.deref]
        grind
      · intros i hi
        have : (polys.deref.val[i]!.coefficients).val.length =
          (polys.val[i]!.coefficients).val.length := by
          simp [alloc.vec.Vec.deref]
        grind [degree]
      · constructor
        · grind
        · constructor
          · grind
          · rw [h_len_N]; simp only [alloc.vec.Vec.deref] at *; simp only [hN] at *
            rw [p_post2]; apply Finset.sum_congr rfl; intro x hx
            simp only [Finset.mem_range] at hx
            simp only [Slice.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD]; congr 1
            have hx_lt_polys : x < (↑polys : List Poly).length := by grind
            simp only [List.getElem?_eq_getElem hx_lt_polys, Option.getD_some]
            have := (polys_post2 x (by omega) (by omega) (by grind)).2
            have := a_post x (by grind); simp_all
    · have h_len_N : Slice.len pts = 30#usize := by simp [Slice.len, hN, Usize.ofNatCore]
      step as ⟨ s, hs⟩
      have : s = 30#uscalar := by simp [hs, h_len_N]; simp [UScalar.cast]; grind
      simp only [this, BitVec.ofNat_eq_ofNat, UScalarTy.U64_numBits_eq]; step
      unfold bodyPost
      simp only [not_lt, List.getElem!_eq_getElem?_getD, ne_eq, List.get_eq_getElem]
      step; step
      · have : (polys.deref).val.length = (polys).val.length := by
          simp [alloc.vec.Vec.deref]
        grind
      · intros i hi
        have : (polys.deref.val[i]!.coefficients).val.length =
          (polys.val[i]!.coefficients).val.length := by
          simp [alloc.vec.Vec.deref]
        grind [degree]
      · constructor
        · grind
        · constructor
          · grind
          · rw [h_len_N]; simp only [alloc.vec.Vec.deref] at *; simp only [hN] at *
            rw [p_post2]; apply Finset.sum_congr rfl; intro x hx
            simp only [Finset.mem_range] at hx
            simp only [Slice.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD]; congr 1
            have hx_lt_polys : x < (↑polys : List Poly).length := by grind
            simp only [List.getElem?_eq_getElem hx_lt_polys, Option.getD_some]
            have := (polys_post2 x (by omega) (by omega) (by grind)).2
            have := a_post x (by grind); simp_all
    · have h_len_N : Slice.len pts = 34#usize := by simp [Slice.len, hN, Usize.ofNatCore]
      step as ⟨ s, hs⟩
      have : s = 34#uscalar := by simp [hs, h_len_N]; simp [UScalar.cast]; grind
      simp only [this, BitVec.ofNat_eq_ofNat, UScalarTy.U64_numBits_eq]; step
      unfold bodyPost
      simp only [not_lt, List.getElem!_eq_getElem?_getD, ne_eq, List.get_eq_getElem]
      step; step
      · have : (polys.deref).val.length = (polys).val.length := by
          simp [alloc.vec.Vec.deref]
        grind
      · intros i hi
        have : (polys.deref.val[i]!.coefficients).val.length =
          (polys.val[i]!.coefficients).val.length := by
          simp [alloc.vec.Vec.deref]
        grind [degree]
      · constructor
        · grind
        · constructor
          · grind
          · rw [h_len_N]; simp only [alloc.vec.Vec.deref] at *; simp only [hN] at *
            rw [p_post2]; apply Finset.sum_congr rfl; intro x hx
            simp only [Finset.mem_range] at hx
            simp only [Slice.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD]; congr 1
            have hx_lt_polys : x < (↑polys : List Poly).length := by grind
            simp only [List.getElem?_eq_getElem hx_lt_polys, Option.getD_some]
            have := (polys_post2 x (by omega) (by omega) (by grind)).2
            have := a_post x (by grind); simp_all
    · have h_len_N : Slice.len pts = 36#usize := by simp [Slice.len, hN, Usize.ofNatCore]
      step as ⟨ s, hs⟩
      have : s = 36#uscalar := by simp [hs, h_len_N]; simp [UScalar.cast]; grind
      simp only [this, BitVec.ofNat_eq_ofNat, UScalarTy.U64_numBits_eq]; step
      unfold bodyPost
      simp only [not_lt, List.getElem!_eq_getElem?_getD, ne_eq, List.get_eq_getElem]
      step; step
      · have : (polys.deref).val.length = (polys).val.length := by
          simp [alloc.vec.Vec.deref]
        grind
      · intros i hi
        have : (polys.deref.val[i]!.coefficients).val.length =
          (polys.val[i]!.coefficients).val.length := by
          simp [alloc.vec.Vec.deref]
        grind [degree]
      · constructor
        · grind
        · constructor
          · grind
          · rw [h_len_N]; simp only [alloc.vec.Vec.deref] at *; simp only [hN] at *
            rw [p_post2]; apply Finset.sum_congr rfl; intro x hx
            simp only [Finset.mem_range] at hx
            simp only [Slice.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD]; congr 1
            have hx_lt_polys : x < (↑polys : List Poly).length := by grind
            simp only [List.getElem?_eq_getElem hx_lt_polys, Option.getD_some]
            have := (polys_post2 x (by omega) (by omega) (by grind)).2
            have := a_post x (by grind); simp_all

/-! ## Spec theorem: in-bounds body (no size restriction)

Body spec for an in-bounds iterator; needs no admissible-size assumption.
When we already know the iterator hasn't been exhausted
(`iter.i < pts.length`), the body can only do one of two things:
- **`done (Err ())`**: the current point fails validation (`pts[i].x ≠ i`).
- **`cont iter'`**: validation passes and the iterator advances.

The `done (Ok _)` branch (Lagrange computation) is impossible here because
the `none` case of `next` cannot fire while the iterator is in bounds.
This simpler spec is useful for `from_complete_points_spec_of_invalid_index`
where we don't need an admissible-size assumption. -/
theorem body_spec_inbounds
    (pts : Slice Pt)
    (iter : Enumerate (Iter Pt))
    (h_count : iter.count ≤ UScalar.max .U16)
    (h_slice_eq : iter.iter.slice = pts)
    (h_in_bounds : iter.iter.i < pts.length) :
    body pts iter ⦃ cf =>
      match cf with
      | ControlFlow.done (core.result.Result.Err ()) =>
          (pts[iter.iter.i]).x.value.val ≠
            iter.count.val
      | ControlFlow.cont iter' =>
          (pts[iter.iter.i]).x.value.val = iter.count.val ∧
          iter'.iter.i = iter.iter.i + 1 ∧
          iter'.iter.slice = pts ∧
          iter'.count.val = iter.count.val + 1
      | ControlFlow.done (core.result.Result.Ok _) => False ⦄ := by
  have h_in_bounds' : iter.iter.i < iter.iter.slice.val.length := by
    rw [h_slice_eq]; exact h_in_bounds
  unfold body
  have h_count_bound : iter.count.val + 1 ≤ Usize.max := by scalar_tac
  step as ⟨opt, iter1, hnext⟩
  cases opt with
  | none => exact absurd h_in_bounds' hnext.1
  | some p =>
    obtain ⟨idx, pt⟩ := p
    obtain ⟨h_lt', h_idx, h_pt, h_iter1_slice, h_iter1_i, h_iter1_count⟩ := hnext
    step*

/-- **Full body spec for `encoding.polynomial.Poly.from_complete_points_loop.body`**:

Combines the `some` case (§ 4) and the `none` case (§ 5) into one theorem.
Requires an admissible-size assumption for the `none` branch (needed to
evaluate the `match pts.len()` and compute the Lagrange sum).

Three-way postcondition on `ControlFlow`:
- **`done (Ok p)`** — iterator exhausted; `p` is the Lagrange interpolation
  polynomial: `p.toGF216Poly = Σⱼ C(pts[j].y) * scaledLagrangeBasis(len,j)`.
- **`done (Err ())`** — index validation failed at position `iter.i`.
- **`cont iter'`** — validation passed, iterator advanced by one step. -/
@[step]
theorem body_spec
    (pts : Slice Pt)
    (iter : Enumerate (Iter Pt))
    (h_count : iter.count ≤ UScalar.max .U16)
    (h_slice_eq : iter.iter.slice = pts)
    (h_len_ok : pts.length = 0 ∨ pts.length = 1 ∨ pts.length = 3 ∨
                pts.length = 5 ∨ pts.length = 30 ∨ pts.length = 34 ∨
                pts.length = 36) :
    body pts iter ⦃ cf =>
      match cf with
      | ControlFlow.done (core.result.Result.Ok p) =>
          ¬ (iter.iter.i < pts.length) ∧
          p.degree < Usize.max ∧
          p.toGF216Poly = ∑ j ∈ Finset.range pts.length,
            C ((pts.val[j]!).y.toGF216) * scaledLagrangeBasis (Slice.len pts) j
      | ControlFlow.done (core.result.Result.Err ()) =>
          ∃ (h_i : iter.iter.i < pts.length),
            (pts[iter.iter.i]).x.value.val ≠ iter.count.val
      | ControlFlow.cont iter' =>
          ∃ (h_i : iter.iter.i < pts.length),
            (pts[iter.iter.i]).x.value.val = iter.count ∧
            iter'.iter.i = iter.iter.i + 1 ∧
            iter'.iter.slice = pts ∧
            iter'.count.val = iter.count.val + 1 ⦄ := by
  by_cases h_in : iter.iter.i < iter.iter.slice.val.length
  · exact body_spec_some_case pts iter h_count h_slice_eq h_in
  · rcases h_len_ok with h | h | h | h | h | h | h
    · exact body_spec_none_0 pts iter h_slice_eq h_in h
    · grind [body_spec_none_N _ pts iter h_slice_eq h_in h]
    · grind [body_spec_none_N _ pts iter h_slice_eq h_in h]
    · grind [body_spec_none_N _ pts iter h_slice_eq h_in h]
    · grind [body_spec_none_N _ pts iter h_slice_eq h_in h]
    · grind [body_spec_none_N _ pts iter h_slice_eq h_in h]
    · grind [body_spec_none_N _ pts iter h_slice_eq h_in h]

/-! # Spec theorem for `Poly::from_complete_points`: loop 0

Runs the loop to completion: validates `pts[i].x.value == i as u16`,
then computes the Lagrange sum for admissible sizes `{0,1,3,5,30,34,36}`.

**Source**: spqr/src/encoding/polynomial.rs -/
@[step]
theorem loop_spec
    (pts : Slice Pt)
    (iter : Enumerate (Iter Pt))
    (h_count : iter.count ≤ UScalar.max .U16)
    (h_count_eq : iter.count = iter.iter.i)
    (h_slice_eq : iter.iter.slice = pts)
    (h_i_le : iter.iter.i ≤ pts.length)
    (h_pts_len : pts.length ≤ UScalar.max .U16)
    (h_len_ok : pts.length = 0 ∨ pts.length = 1 ∨ pts.length = 3 ∨
                pts.length = 5 ∨ pts.length = 30 ∨ pts.length = 34 ∨
                pts.length = 36)
    (h_pre : ∀ (j : Nat), j < iter.iter.i →
        ∀ (hj : j < pts.length), (pts[j]).x.value.val = j) :
    from_complete_points_loop iter pts ⦃ (result : core.result.Result Poly Unit) =>
      match result with
      | core.result.Result.Ok p =>
          (∀ (j : Nat) (hj : j < pts.length), (pts[j]).x.value.val = j) ∧
          p.degree < Usize.max ∧
          p.toGF216Poly = ∑ j ∈ Finset.range pts.length,
            C ((pts.val[j]!).y.toGF216) * scaledLagrangeBasis (Slice.len pts) j
      | core.result.Result.Err () =>
          ∃ (j : Nat) (hj : j < pts.length), (pts[j]).x.value.val ≠ j ⦄ := by
  unfold from_complete_points_loop
  apply loop.spec_decr_nat
    (measure := fun iter' => pts.val.length - iter'.iter.i)
    (inv := fun iter' =>
      iter'.iter.slice = pts ∧
      iter'.iter.i ≤ pts.val.length ∧
      iter'.count.val ≤ UScalar.max .U16 ∧
      iter'.count.val = iter'.iter.i ∧
      (∀ (j : Nat), j < iter'.iter.i →
        ∀ (hj : j < pts.length), (pts[j]).x.value.val = j))
  · intro iter' ⟨h_slice', h_i_le', h_count', h_count_eq', h_pre'⟩
    have h_body := body_spec pts iter' h_count' h_slice' h_len_ok
    apply WP.spec_mono h_body
    intro cf h_cf
    match cf with
    | ControlFlow.done (core.result.Result.Ok p) => grind
    | ControlFlow.done (core.result.Result.Err ()) => grind
    | ControlFlow.cont iter'' => grind
  · grind

end spqr.encoding.polynomial.Poly.from_complete_points_loop


/-! # Spec theorem for `spqr::encoding::polynomial::{Poly}::from_complete_points`

Top-level wrapper: builds the enumerated slice iterator at index 0 and
delegates to `from_complete_points_loop`, inheriting its postcondition.

**Source**: spqr/src/encoding/polynomial.rs -/

namespace spqr.encoding.polynomial.Poly

/-- **Spec theorem for `encoding.polynomial.Poly.from_complete_points`**:

Given a point slice `pts` of admissible length (`∈ {0,1,3,5,30,34,36}`):
- **`Ok p`** ⇒ every index is valid (`pts[j].x.value = j` for all `j`) AND
  the polynomial `p` is the Lagrange interpolation through those points:
  `p.toGF216Poly = Σⱼ C(pts[j].y.toGF216) * scaledLagrangeBasis(len, j)`.
- **`Err ()`** ⇒ at least one index failed validation (`∃ j, pts[j].x.value ≠ j`).

This is the primary correctness theorem for the decoder's polynomial
reconstruction step. -/
@[step]
theorem from_complete_points_spec
    (pts : Slice Pt)
    (h_len_ok : pts.length = 0 ∨ pts.length = 1 ∨ pts.length = 3 ∨
                pts.length = 5 ∨ pts.length = 30 ∨ pts.length = 34 ∨
                pts.length = 36) :
    from_complete_points pts ⦃ (result : core.result.Result Poly Unit) =>
      match result with
      | core.result.Result.Ok p =>
          (∀ (j : Nat) (hj : j < pts.length), (pts[j]).x.value.val = j) ∧
          p.degree < Usize.max ∧
          p.toGF216Poly = ∑ j ∈ Finset.range pts.length,
          C ((pts.val[j]!).y.toGF216) * scaledLagrangeBasis (Slice.len pts) j
      | core.result.Result.Err () =>
          ∃ (j : Nat) (hj : j < pts.val.length), (pts[j]).x.value.val ≠ j ⦄ := by
  have h_pts_len : pts.val.length ≤ UScalar.max .U16 := by grind
  unfold from_complete_points
  simp only [core.slice.Slice.iter,
             core.iter.traits.iterator.Iterator.enumerate.trait_default,
             core.iter.traits.iterator.Iterator.enumerate.default, bind_tc_ok]
  exact from_complete_points_loop.loop_spec pts _
    (by simp) (by simp) rfl (by grind) h_pts_len h_len_ok
    (by intro j hj; grind)


/-- **Spec theorem for `encoding.polynomial.Poly.from_complete_points` (error path)**:

If some index fails validation (`∃ j, pts[j].x.value ≠ j`), the function
returns `Err ()`.  This theorem needs only that the length fits in `U16`;
**no admissible-size assumption** is required, because the loop will detect
the invalid index and return early before reaching the `match pts.len()`
computation branch.

The proof uses `body_spec_inbounds` (which doesn't need admissible sizes)
and a loop invariant that tracks:
- The "all valid so far" prefix property for indices `< iter.i`.
- A witness `k ≥ iter.i` with `pts[k].x.value ≠ k`, guaranteeing the
  loop will eventually hit the mismatch and return `Err`. -/
@[step]
theorem from_complete_points_spec_of_invalid_index
    (pts : Slice Pt)
    (h_pts_len : pts.length ≤ UScalar.max .U16)
    (h_exists : ∃ (j : Nat) (hj : j < pts.length), (pts[j]).x.value.val ≠ j) :
    from_complete_points pts ⦃ (result : core.result.Result Poly Unit) =>
      match result with
      | core.result.Result.Ok _ => False
      | core.result.Result.Err () =>
          ∃ (j : Nat) (hj : j < pts.length), (pts[j]).x.value.val ≠ j ⦄ := by
  unfold from_complete_points
  simp only [core.slice.Slice.iter,
             core.iter.traits.iterator.Iterator.enumerate.trait_default,
             core.iter.traits.iterator.Iterator.enumerate.default, bind_tc_ok]
  unfold from_complete_points_loop
  apply loop.spec_decr_nat
    (measure := fun iter' => pts.val.length - iter'.iter.i)
    (inv := fun iter' =>
      iter'.iter.slice = pts ∧
      iter'.count ≤ UScalar.max .U16 ∧
      iter'.count.val = iter'.iter.i ∧
      (∀ (j : Nat), j < iter'.iter.i →
        ∀ (hj : j < pts.length), (pts[j]).x.value.val = j) ∧
      (∃ (k : Nat), iter'.iter.i ≤ k ∧ k < pts.length ∧
        ∀ (hk : k < pts.length), (pts[k]).x.value.val ≠ k))
  · intro iter' ⟨h_slice', h_count', h_count_eq', h_pre', k, h_k_ge, h_k_lt, h_k_neq⟩
    have h_in_bounds : iter'.iter.i < pts.length := by grind
    have h_body := from_complete_points_loop.body_spec_inbounds pts iter'
      h_count' h_slice' h_in_bounds
    apply WP.spec_mono h_body
    intro cf h_cf
    match cf with
    | ControlFlow.done (core.result.Result.Ok _) => grind
    | ControlFlow.done (core.result.Result.Err ()) => grind
    | ControlFlow.cont iter'' =>
      simp only  at h_cf ⊢
      obtain ⟨h_val_eq, h_iter_i, h_iter_slice, h_iter_count⟩ := h_cf
      constructor
      · refine ⟨h_iter_slice, ?_, ?_, ?_, ?_⟩
        · grind
        · omega
        · intro j hj hj_lt
          by_cases hj' : j < iter'.iter.i
          · exact h_pre' j hj' hj_lt
          · have : j = iter'.iter.i := by omega
            subst this
            rw [h_count_eq'] at h_val_eq
            exact h_val_eq
        · have h_k_ne : k ≠ iter'.iter.i := by
            intro heq; subst heq
            rw [h_count_eq'] at h_val_eq
            exact h_k_neq h_k_lt h_val_eq
          exact ⟨k, by omega, h_k_lt, h_k_neq⟩
      · grind
  · obtain ⟨j, hj, h_neq⟩ := h_exists
    refine ⟨rfl, by simp, by simp, ?_, j, ?_, hj, fun _ => h_neq⟩
    · intro j' hj'; simp at hj'
    · simp

end spqr.encoding.polynomial.Poly
