/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Encoding.Polynomial.ConstPolysToPolys
import Spqr.Specs.Encoding.Polynomial.Poly.LagrangeSum
import Spqr.Specs.Encoding.Polynomial.COMPLETE_POINTS_POLYS_1
import Spqr.Specs.Encoding.Polynomial.COMPLETE_POINTS_POLYS_3
import Spqr.Specs.Encoding.Polynomial.COMPLETE_POINTS_POLYS_5
import Spqr.Specs.Encoding.Polynomial.COMPLETE_POINTS_POLYS_30
import Spqr.Specs.Encoding.Polynomial.COMPLETE_POINTS_POLYS_34
import Spqr.Specs.Encoding.Polynomial.COMPLETE_POINTS_POLYS_36
/-! # Spec theorem for `Poly::from_complete_points`: loop body 0
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf Polynomial
open core.iter.adapters.enumerate core.slice.iter
open PolyConst.lagrange_interpolate_pt_loop


namespace spqr.encoding.polynomial.Poly.from_complete_points_loop

private lemma usize_checked_add_one_val (x : Usize)
    (h : x.val + 1 ≤ Usize.max) :
    ∃ (y : Usize), (x + 1#usize : Result Usize) = ok y ∧ y.val = x.val + 1 := by
  have h_add : x.val + (1#usize : Usize).val ≤ Usize.max := by scalar_tac
  have h_spec := Usize.add_spec h_add
  revert h_spec
  generalize (x + 1#usize : Result Usize) = res
  intro h_spec
  match res with
  | .ok z => exact ⟨z, rfl, by simp_all [WP.spec_ok]⟩
  | .fail e => simp_all
  | .div => simp_all

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
    rw [h_add_eq]
    exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩

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
  rw [h_add_eq]
  exact ⟨_, rfl, rfl, rfl, h_add_val⟩

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
    (UScalar.cast UScalarTy.U16 x).val = x.val :=
  UScalar.cast_inBounds_spec UScalarTy.U16 x h

/-! ## Common postcondition abbreviation -/

/-- Postcondition for body_spec helpers. Transparent via `abbrev` so `step*` sees through it.
    `Ok` ⇒ Lagrange sum over `scaledLagrangeBasis`; `Err` ⇒ validation mismatch;
    `cont` ⇒ iterator advances. -/
private abbrev bodyPost
    (pts : Slice Pt) (iter : Enumerate (Iter Pt)) :
    ControlFlow (Enumerate (Iter Pt)) (core.result.Result Poly Unit) → Prop :=
  fun cf =>
    match cf with
    | ControlFlow.done (core.result.Result.Ok p) =>
        ¬ (iter.iter.i < pts.val.length) ∧
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

/-! ## Spec helper: the `some` (validation) branch -/

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
  simp only [bind_tc_ok]
  have h_lt_pts : iter.iter.i < pts.val.length := by
    rw [← h_slice_eq]; exact h_in_bounds
  have h_cast_val := usize_cast_u16_val iter.count h_count
  step*
  · simp_all
    grind
  · grind

/-! ## Spec helpers: the `none` (computation) branch by size -/

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
  simp only [bind_tc_ok]
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
    step
    unfold bodyPost
    simp only [not_lt, List.getElem!_eq_getElem?_getD]
    constructor
    · grind
    · simp_all

/-- `scaledLagrangeBasis 1#usize 0 = 1`: single-point case reduces to constant `1`. -/
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
  rw [hnext]; simp only [bind_tc_ok]
  cases opt with
  | some p =>
    obtain ⟨idx, pt⟩ := p
    exact (absurd_some_out_of_bounds iter idx pt iter1 hnext h_out_of_bounds).elim
  | none =>
    have h_not_lt : ¬ (iter.iter.i < pts.val.length) := by
      have := EnumerateSliceIter_next_Pt_none iter iter1 hnext
      rw [h_slice_eq] at this; exact this
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
        · rw [h_len_N]; simp only [alloc.vec.Vec.deref] at *; simp only [hN] at *
          rw [p_post]; apply Finset.sum_congr rfl; intro x hx
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
        · rw [h_len_N]; simp only [alloc.vec.Vec.deref] at *; simp only [hN] at *
          rw [p_post]; apply Finset.sum_congr rfl; intro x hx
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
        · rw [h_len_N]; simp only [alloc.vec.Vec.deref] at *; simp only [hN] at *
          rw [p_post]; apply Finset.sum_congr rfl; intro x hx
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
        · rw [h_len_N]; simp only [alloc.vec.Vec.deref] at *; simp only [hN] at *
          rw [p_post]; apply Finset.sum_congr rfl; intro x hx
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
        · rw [h_len_N]; simp only [alloc.vec.Vec.deref] at *; simp only [hN] at *
          rw [p_post]; apply Finset.sum_congr rfl; intro x hx
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
        · rw [h_len_N]; simp only [alloc.vec.Vec.deref] at *; simp only [hN] at *
          rw [p_post]; apply Finset.sum_congr rfl; intro x hx
          simp only [Finset.mem_range] at hx
          simp only [Slice.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD]; congr 1
          have hx_lt_polys : x < (↑polys : List Poly).length := by grind
          simp only [List.getElem?_eq_getElem hx_lt_polys, Option.getD_some]
          have := (polys_post2 x (by omega) (by omega) (by grind)).2
          have := a_post x (by grind); simp_all

/-! ## Spec theorem: in-bounds body (no size restriction) -/

/-- Body spec when iterator is in-bounds. No admissible-size restriction needed. -/
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
  simp only [bind_tc_ok]
  have h_lt_pts : iter.iter.i < pts.val.length := h_in_bounds
  have h_cast_val := usize_cast_u16_val iter.count h_count
  step*

/-- **Spec theorem for `encoding.polynomial.Poly.from_complete_points_loop.body`**:
`Ok` ⇒ Lagrange sum via `scaledLagrangeBasis`; `Err` ⇒ validation mismatch;
`cont` ⇒ validation passes and iterator advances. -/
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
            iter'.count.val = iter.count.val + 1
    ⦄ := by
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

Drives the iterator-based validation/computation loop to completion.
Validates `pts[i].x.value == i as u16` then computes the Lagrange sum
using precomputed basis polynomials for admissible sizes `{0,1,3,5,30,34,36}`.

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
    | ControlFlow.done (core.result.Result.Ok p) =>
      simp only  at h_cf ⊢
      obtain ⟨h_not_lt, h_sum⟩ := h_cf
      exact ⟨fun j hj => h_pre' j (by grind) hj, h_sum⟩
    | ControlFlow.done (core.result.Result.Err ()) =>
      simp only  at h_cf ⊢
      obtain ⟨h_i_lt, h_neq⟩ := h_cf
      exact ⟨iter'.iter.i, h_i_lt, by grind⟩
    | ControlFlow.cont iter'' =>
      simp only  at h_cf ⊢
      obtain ⟨h_i_lt, h_val_eq, h_iter_i, h_iter_slice, h_iter_count⟩ := h_cf
      constructor
      · exact ⟨h_iter_slice, by grind, by grind, by omega, fun j hj hj_lt => by
          by_cases hj_lt' : j < iter'.iter.i
          · exact h_pre' j hj_lt' hj_lt
          · have hj_eq : j = iter'.iter.i := by omega
            subst hj_eq
            exact h_val_eq.trans h_count_eq'⟩
      · grind
  · exact ⟨h_slice_eq, h_i_le, h_count, h_count_eq, h_pre⟩

end spqr.encoding.polynomial.Poly.from_complete_points_loop

/-! # Spec theorem for `spqr::encoding::polynomial::{Poly}::from_complete_points`

Top-level wrapper: sets up `SliceIter` + `Enumerate` at index 0, then delegates to
`from_complete_points_loop`. Postcondition inherited from the loop spec.
Admissible sizes: `{0,1,3,5,30,34,36}`. Requires `pts.val.length ≤ UScalar.max .U16`
for faithful `Usize → U16` casts.

**Source**: spqr/src/encoding/polynomial.rs -/

namespace spqr.encoding.polynomial.Poly

/-- **Spec theorem for `encoding.polynomial.Poly.from_complete_points`**:
`Ok p` ⇒ all slots validated and `p` is the Lagrange sum via `scaledLagrangeBasis`;
`Err ()` ⇒ some `pts[j].x.value.val ≠ j`. -/
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
          p.toGF216Poly = ∑ j ∈ Finset.range pts.length,
          C ((pts.val[j]!).y.toGF216) * scaledLagrangeBasis (Slice.len pts) j
      | core.result.Result.Err () =>
          ∃ (j : Nat) (hj : j < pts.val.length), (pts[j]).x.value.val ≠ j ⦄ := by
  have h_pts_len : pts.val.length ≤ UScalar.max .U16 := by
    grind
  unfold from_complete_points
  simp only [core.slice.Slice.iter,
             core.iter.traits.iterator.Iterator.enumerate.trait_default,
             core.iter.traits.iterator.Iterator.enumerate.default, bind_tc_ok]
  exact from_complete_points_loop.loop_spec pts _
    (by simp) (by simp) rfl (by grind) h_pts_len h_len_ok
    (by intro j hj; grind)


/-- **Spec theorem for `encoding.polynomial.Poly.from_complete_points` (non-admissible sizes)**:
Non-admissible sizes panic on the `none` branch, so success implies `Err ()`.
Requires `h_pts_len` (length fits `U16`) and `h_exists` (a validation failure exists). -/
@[step]
theorem from_complete_points_spec_Not
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
    | ControlFlow.done (core.result.Result.Ok _) =>
      exact h_cf.elim
    | ControlFlow.done (core.result.Result.Err ()) =>
      simp only at h_cf ⊢
      exact ⟨iter'.iter.i, h_in_bounds, by rw [h_count_eq'] at h_cf; exact h_cf⟩
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
