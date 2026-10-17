/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

import Spqr.Specs.Encoding.Polynomial.ConstPolysToPolys
import Spqr.Specs.Encoding.Polynomial.Poly.LagrangeSum
import Spqr.Specs.Encoding.Polynomial.COMPLETE_POINTS_POLYS_1
import Spqr.Specs.Encoding.Polynomial.COMPLETE_POINTS_POLYS_3
import Spqr.Specs.Encoding.Polynomial.COMPLETE_POINTS_POLYS_5
import Spqr.Specs.Encoding.Polynomial.COMPLETE_POINTS_POLYS_30
import Spqr.Specs.Encoding.Polynomial.COMPLETE_POINTS_POLYS_34
import Spqr.Specs.Encoding.Polynomial.COMPLETE_POINTS_POLYS_36
public import Spqr.Math.Poly.Lagrange.CompletePoints
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Tactic.ComputeDegree

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

@[expose] public section

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf Polynomial
open core.iter.adapters.enumerate core.slice.iter
open PolyConst.lagrange_interpolate_pt_loop


namespace spqr.encoding.polynomial.Poly.from_complete_points_loop

private lemma usize_checked_add_one_val (x : Usize)
    (h : x.val + 1 ≤ Usize.max) :
    ∃ (y : Usize), (x + 1#usize : Result Usize) = ok y ∧ y.val = x.val + 1 := by
  obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (Usize.add_spec (x := x) (y := 1#usize) (by scalar_tac))
  exact ⟨y, hy, by simpa using hyv⟩

private lemma EnumerateSliceIter_next_Pt_post
    (iter : Enumerate (Iter Pt))
    (h_bound : iter.iter.i < iter.iter.slice.val.length → iter.count.val + 1 ≤ Usize.max) :
    ∃ (opt : Option (Usize × Pt))
      (iter' : Enumerate (Iter Pt)),
      IteratorEnumerate.next
        (core.iter.traits.iterator.IteratorSliceIter Pt) iter =
          ok (opt, iter') := by
  simp only [IteratorEnumerate.next,
    IteratorSliceIter.next]
  split
  · have h_add_bound : iter.count.val + 1 ≤ Usize.max := h_bound (by scalar_tac)
    obtain ⟨count', h_add_eq, _⟩ := usize_checked_add_one_val iter.count h_add_bound
    simp [h_add_eq]
  · simp

private lemma EnumerateSliceIter_next_Pt_some
    (iter : Enumerate (Iter Pt))
    (h_lt : iter.iter.i < iter.iter.slice.val.length)
    (h_bound : iter.count.val + 1 ≤ Usize.max) :
    ∃ (iter1 : Enumerate (Iter Pt)),
      IteratorEnumerate.next
        (core.iter.traits.iterator.IteratorSliceIter Pt) iter =
          ok (some (iter.count, iter.iter.slice.val[iter.iter.i]), iter1) ∧
      iter1.iter.i = iter.iter.i + 1 ∧
      iter1.iter.slice = iter.iter.slice ∧
      iter1.count.val = iter.count.val + 1 := by
  simp only [
    IteratorEnumerate.next,
    IteratorSliceIter.next]
  have h_lt' : iter.iter.i < (↑iter.iter.slice.len : Nat) := by scalar_tac
  rw [dif_pos h_lt']
  obtain ⟨count', h_add_eq, h_add_val⟩ := usize_checked_add_one_val iter.count h_bound
  exact ⟨{ iter := { iter.iter with i := iter.iter.i + 1 }, count := count' },
    by simp [h_add_eq]; rfl, rfl, rfl, h_add_val⟩

private lemma EnumerateSliceIter_next_Pt_none
    (iter : Enumerate (Iter Pt))
    (iter' : Enumerate (Iter Pt))
    (hnext : IteratorEnumerate.next
        (core.iter.traits.iterator.IteratorSliceIter Pt) iter =
          ok (none, iter')) :
    ¬ (iter.iter.i < iter.iter.slice.val.length) := by
  simp only [IteratorEnumerate.next,
    IteratorSliceIter.next] at hnext
  split at hnext
  case isTrue h_lt =>
    exfalso
    revert hnext
    generalize (iter.count + 1#usize : Result Usize) = add_res
    cases add_res <;> simp
  case isFalse h_neg => exact h_neg

private lemma usize_cast_u16_val (x : Usize) (h : x.val ≤ UScalar.max .U16) :
    (UScalar.cast UScalarTy.U16 x).val = x.val := by
  simpa [lift, WP.spec_ok] using UScalar.cast_inBounds_spec UScalarTy.U16 x h

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
abbrev bodyPost
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

private lemma absurd_some_out_of_bounds
    (iter : Enumerate (Iter Pt))
    (idx : Usize) (pt : Pt) (iter1 : Enumerate (Iter Pt))
    (hnext : IteratorEnumerate.next
        (core.iter.traits.iterator.IteratorSliceIter Pt) iter =
          ok (some (idx, pt), iter1))
    (h_out : ¬(iter.iter.i < iter.iter.slice.val.length)) :
    False := by
  simp only [IteratorEnumerate.next,
    IteratorSliceIter.next] at hnext
  split at hnext
  case isTrue h_lt => exact absurd h_lt h_out
  case isFalse => simp at hnext


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
  obtain ⟨iter1, hnext, h_iter1_i, h_iter1_slice, h_iter1_count⟩ :=
    EnumerateSliceIter_next_Pt_some iter h_in_bounds h_count_bound
  rw [hnext]
  have h_lt_pts : iter.iter.i < pts.val.length := by
    rw [← h_slice_eq]; exact h_in_bounds
  have h_cast_val := usize_cast_u16_val iter.count h_count
  step as ⟨i1, h_i1⟩
  have h_i1_val : i1.val = iter.count.val := by rw [h_i1, h_cast_val]
  subst h_slice_eq
  split
  next h_ne =>
    -- the point's x-coordinate is not its index: `Err ()`
    rw [WP.spec_ok]
    refine ⟨h_lt_pts, fun h_eq => ?_⟩
    simp only [bne_iff_ne, ne_eq] at h_ne
    exact h_ne (UScalar.eq_of_val_eq (by rw [h_i1_val]; exact h_eq))
  next h_eq =>
    -- valid point: advance
    rw [WP.spec_ok]
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at h_eq
    exact ⟨h_lt_pts, (congrArg UScalar.val h_eq).trans h_i1_val, h_iter1_i, h_iter1_slice,
      h_iter1_count⟩

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
  obtain ⟨opt, iter1, hnext⟩ := EnumerateSliceIter_next_Pt_post iter
    (fun h_lt => absurd h_lt h_out_of_bounds)
  rw [hnext]
  cases opt with
  | some p =>
    obtain ⟨idx, pt⟩ := p
    exact (absurd_some_out_of_bounds iter idx pt iter1 hnext h_out_of_bounds).elim
  | none =>
    have h_not_lt : ¬ (iter.iter.i < pts.val.length) := by
      have := EnumerateSliceIter_next_Pt_none iter iter1 hnext
      rw [h_slice_eq] at this; exact this
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
    step as ⟨p, h_deg, h_sum⟩
    -- both sums range over `pts.length = 0`
    have h_len : pts.length = 0 := h0
    exact ⟨h_not_lt, h_deg, by rw [h_sum, h_len, h0]; rfl⟩

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

/-- Bridges the `const_polys_to_polys` post and a `COMPLETE_POINTS_POLYS_N` post: the `x`-th
converted polynomial is the `x`-th scaled Lagrange basis polynomial. -/
private lemma polys_basis {M : Usize} {a : Std.Array (PolyConst M) M}
    {polys : alloc.vec.Vec Poly} {x : Nat}
    (hpolys : ∀ j < M.val, ∀ (hj : j < polys.length) (hjc : j < a.length),
      polys[j].coefficients.val = a[j].coefficients.val ∧
        polys[j].toGF216Poly = listToGF216Poly a[j].coefficients.val)
    (ha : ∀ j < M.val, listToGF216Poly (a.val[j]!).coefficients.val = scaledLagrangeBasis M j)
    (hlen : polys.length = M.val) (hx : x < M.val) {l : List Poly} (hl : l = polys.val) :
    (l[x]?.getD default).toGF216Poly = scaledLagrangeBasis M x := by
  subst hl
  have hxp : x < polys.val.length := by scalar_tac
  obtain ⟨-, h⟩ := hpolys x hx (by scalar_tac) (by scalar_tac)
  rw [List.getElem?_eq_getElem hxp, Option.getD_some, ← ha x hx,
    getElem!_pos (↑a : List (PolyConst M)) x (by scalar_tac)]
  exact h

/-- One arm of the `match pts.len()`: load the precomputed basis `COMPLETE_POINTS_POLYS_M`
(`constM`, whose `j`-th polynomial is the scaled Lagrange basis polynomial `j`), convert it with
`const_polys_to_polys`, and take the Lagrange sum. -/
private theorem arm_spec {M : Usize} (pts : Slice Pt) (iter : Enumerate (Iter Pt))
    (constM : Result (Std.Array (PolyConst M) M))
    (h_const : constM ⦃ a => ∀ j < M.val,
      listToGF216Poly (a.val[j]!).coefficients.val = scaledLagrangeBasis M j ⦄)
    (h_M : M.val ≤ 36)
    (h_len : Slice.len pts = M)
    (h_not_lt : ¬ iter.iter.i < pts.val.length) :
    (do
      let a ← constM
      let polys ← const_polys_to_polys a
      let p ← lagrange_sum pts (alloc.vec.Vec.deref polys)
      ok (ControlFlow.done (core.result.Result.Ok p))) ⦃ bodyPost pts iter ⦄ := by
  have h_lenN : pts.val.length = M.val := by rw [← h_len]; simp [Slice.len]
  step with h_const as ⟨a, ha⟩
  step with const_polys_to_polys_spec as ⟨polys, h_plen, h_polys⟩
  have h_deref : (alloc.vec.Vec.deref polys).val = polys.val := by simp [alloc.vec.Vec.deref]
  step with lagrange_sum_spec as ⟨p, h_deg, h_sum⟩
  · intro i hi
    have hi' : i < M.val := by simp only [Slice.length] at hi; omega
    obtain ⟨h_coef, -⟩ := h_polys i hi' (by rw [h_plen]; exact hi') (by simpa using hi')
    have h_degi : ((alloc.vec.Vec.deref polys)[i]!).degree = M.val := by
      simp only [degree, Slice.getElem!_Nat_eq, h_deref]
      rw [getElem!_pos polys.val i (by simp only [alloc.vec.Vec.length] at h_plen; omega)]
      simpa using congrArg List.length h_coef
    rw [h_degi]; scalar_tac
  refine ⟨h_not_lt, h_deg, ?_⟩
  rw [h_sum, h_len]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [Finset.mem_range] at hx
  congr 1
  · rw [Slice.getElem!_Nat_eq]
  simp only [Slice.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD]
  exact polys_basis h_polys ha h_plen (by simpa [Slice.length, h_lenN] using hx) h_deref

/-- Non-empty admissible sizes (`N ∈ {1, 3, 5, 30, 34, 36}`): when the iterator is exhausted,
the code matches on `pts.len()` and runs the arm for the precomputed `COMPLETE_POINTS_POLYS_N`
(`arm_spec`). -/
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
  obtain ⟨opt, iter1, hnext⟩ := EnumerateSliceIter_next_Pt_post iter
    (fun h_lt => absurd h_lt h_out_of_bounds)
  rw [hnext]
  cases opt with
  | some p =>
    obtain ⟨idx, pt⟩ := p
    exact (absurd_some_out_of_bounds iter idx pt iter1 hnext h_out_of_bounds).elim
  | none =>
    have h_not_lt : ¬ (iter.iter.i < pts.val.length) := by
      have := EnumerateSliceIter_next_Pt_none iter iter1 hnext
      rw [h_slice_eq] at this; exact this
    step as ⟨s, hs⟩
    have hN36 : N ≤ 36 := by omega
    have hs_val : s.val = N := by rw [hs, UScalar.cast_val_eq]; simp [Slice.len, hN]; omega
    rcases hN_admissible with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [show s = 1#uscalar from UScalar.eq_of_val_eq hs_val]
      refine arm_spec pts iter _ (WP.spec_mono COMPLETE_POINTS_POLYS_1_spec ?_) (by decide)
        (by simp [Slice.len, hN, Usize.ofNatCore]) h_not_lt
      rintro a ⟨-, -, h⟩ j hj
      obtain rfl : j = 0 := by simp at hj; omega
      rw [scaledLagrangeBasis_one_zero]
      simpa [List.getElem!_eq_getElem?_getD] using h
    · rw [show s = 3#uscalar from UScalar.eq_of_val_eq hs_val]
      exact arm_spec pts iter _ COMPLETE_POINTS_POLYS_3_spec (by decide)
        (by simp [Slice.len, hN, Usize.ofNatCore]) h_not_lt
    · rw [show s = 5#uscalar from UScalar.eq_of_val_eq hs_val]
      exact arm_spec pts iter _ COMPLETE_POINTS_POLYS_5_spec (by decide)
        (by simp [Slice.len, hN, Usize.ofNatCore]) h_not_lt
    · rw [show s = 30#uscalar from UScalar.eq_of_val_eq hs_val]
      exact arm_spec pts iter _ COMPLETE_POINTS_POLYS_30_spec (by decide)
        (by simp [Slice.len, hN, Usize.ofNatCore]) h_not_lt
    · rw [show s = 34#uscalar from UScalar.eq_of_val_eq hs_val]
      exact arm_spec pts iter _ COMPLETE_POINTS_POLYS_34_spec (by decide)
        (by simp [Slice.len, hN, Usize.ofNatCore]) h_not_lt
    · rw [show s = 36#uscalar from UScalar.eq_of_val_eq hs_val]
      exact arm_spec pts iter _ COMPLETE_POINTS_POLYS_36_spec (by decide)
        (by simp [Slice.len, hN, Usize.ofNatCore]) h_not_lt

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
  obtain ⟨iter1, hnext, h_iter1_i, h_iter1_slice, h_iter1_count⟩ :=
    EnumerateSliceIter_next_Pt_some iter h_in_bounds' h_count_bound
  rw [hnext]
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
  have h_body : body pts iter ⦃ bodyPost pts iter ⦄ := by
    by_cases h_in : iter.iter.i < iter.iter.slice.val.length
    · exact body_spec_some_case pts iter h_count h_slice_eq h_in
    · rcases h_len_ok with h | h
      · exact body_spec_none_0 pts iter h_slice_eq h_in h
      · exact body_spec_none_N _ pts iter h_slice_eq h_in rfl (by simpa [Slice.length] using h)
  apply WP.spec_mono h_body
  rintro (iter' | (p | ⟨⟩)) h_post <;> exact h_post

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
    rintro (iter'' | (p | ⟨⟩)) h_cf
    · -- the point at `iter'.i` is valid: the invariant extends by one index
      obtain ⟨h_i, h_val, h_i'', h_slice'', h_count''⟩ := h_cf
      have h_i' : iter'.iter.i < pts.val.length := h_i
      have h_len' : pts.val.length ≤ UScalar.max .U16 := h_pts_len
      refine ⟨⟨h_slice'', by omega, by omega, by omega, fun j hj hj_lt => ?_⟩, by omega⟩
      by_cases hj' : j < iter'.iter.i
      · exact h_pre' j hj' hj_lt
      · obtain rfl : j = iter'.iter.i := by omega
        exact h_val.trans h_count_eq'
    · -- iterator exhausted: every index was checked
      obtain ⟨h_ge, h_deg, h_sum⟩ := h_cf
      exact ⟨fun j hj => h_pre' j (by omega) hj, h_deg, h_sum⟩
    · -- invalid point at `iter'.i`
      obtain ⟨h_i, h_ne⟩ := h_cf
      exact ⟨iter'.iter.i, h_i, fun h => h_ne (h.trans h_count_eq'.symm)⟩
  · exact ⟨h_slice_eq, h_i_le, h_count, h_count_eq ▸ rfl, h_pre⟩

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
  have h_pts_len : pts.val.length ≤ UScalar.max .U16 := by
    simp only [Slice.length] at h_len_ok; scalar_tac
  unfold from_complete_points
  simp only [core.slice.Slice.iter,
             core.iter.traits.iterator.Iterator.enumerate.trait_default,
             core.iter.traits.iterator.Iterator.enumerate.default, bind_ok]
  exact from_complete_points_loop.loop_spec pts _
    (by simp) (by simp) rfl (by simp) h_pts_len h_len_ok
    (by intro j hj; simp at hj)


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
             core.iter.traits.iterator.Iterator.enumerate.default, bind_ok]
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
    have h_in_bounds : iter'.iter.i < pts.length := lt_of_le_of_lt h_k_ge h_k_lt
    have h_k_lt' : k < pts.val.length := h_k_lt
    have h_len' : pts.val.length ≤ UScalar.max .U16 := h_pts_len
    have h_body := from_complete_points_loop.body_spec_inbounds pts iter'
      h_count' h_slice' h_in_bounds
    apply WP.spec_mono h_body
    rintro (iter'' | (_ | ⟨⟩)) h_cf
    · obtain ⟨h_val_eq, h_iter_i, h_iter_slice, h_iter_count⟩ := h_cf
      constructor
      · refine ⟨h_iter_slice, ?_, ?_, ?_, ?_⟩
        · show iter''.count.val ≤ UScalar.max .U16
          omega
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
      · show pts.val.length - iter''.iter.i < pts.val.length - iter'.iter.i
        omega
    · exact h_cf.elim
    · exact ⟨_, h_in_bounds, fun h => h_cf (h.trans h_count_eq'.symm)⟩
  · obtain ⟨j, hj, h_neq⟩ := h_exists
    refine ⟨rfl, by simp, by simp, ?_, j, ?_, hj, fun _ => h_neq⟩
    · intro j' hj'; simp at hj'
    · simp

end spqr.encoding.polynomial.Poly
