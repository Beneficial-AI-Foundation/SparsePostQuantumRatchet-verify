/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong, Lacramioara Astefanoaei
-/
module

import Spqr.Specs.Encoding.Polynomial.NUM_POLYS
import Spqr.Specs.Encoding.Polynomial.Poly.ComputeAt
public import Spqr.Math.Poly.Lagrange.CompletePoints
import Spqr.Specs.Encoding.Polynomial.Poly.FromCompletePoints
public import Spqr.Specs.Encoding.Polynomial.PolyEncoder.Defs
public import Spqr.Math.Poly.Eval
import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Tactic.ComputeDegree
import Spqr.Specs.Encoding.Gf.GF16.New
import Spqr.Specs.Aeneas.RangeIteratorNext


/-!
# Spec theorem for `PolyEncoder::point_at`: loop body 0

One step of the conversion loop in `PolyEncoder::point_at` (lines 660–680), which iterates over
`0..NUM_POLYS` and constructs the Lagrange interpolating polynomial for each `Point` in GF(2¹⁶).

Given index `i` from the range iterator, the body either returns unchanged (`none`) or builds
evaluation points via the inner enumerate loop (`point_at_loop0_loop0`), calls
`Poly::from_complete_points`, and stores the result in `polys[i]`.

The proof composes `IteratorRange.next`, `Array.index_usize`, the inner enumerate/push loop,
`Poly::from_complete_points`, `Result.expect`, and `Array.update`.

**Source**: spqr/src/encoding/polynomial.rs -/

@[expose] public section

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf Polynomial

namespace spqr.encoding.polynomial.PolyEncoder.point_at_loop0_loop0

/-! ## Spec for the inner `for (x, y) in pts[i].value.iter().enumerate()` loop -/

/-- One step of `Enumerate<slice::Iter<GF16>>::next` when the slice is not yet exhausted. -/
private lemma enum_next_some
    (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter GF16))
    (h_lt : iter.iter.i < iter.iter.slice.val.length)
    (h_bound : iter.count.val + 1 ≤ Usize.max) :
    ∃ (count' : Usize),
      core.iter.adapters.enumerate.IteratorEnumerate.next
        (core.iter.traits.iterator.IteratorSliceIter GF16) iter =
          ok (some (iter.count, iter.iter.slice.val[iter.iter.i]),
            { iter := { slice := iter.iter.slice, i := iter.iter.i + 1 }, count := count' }) ∧
      count'.val = iter.count.val + 1 := by
  obtain ⟨y, h_add_eq, h_y_val⟩ := WP.spec_imp_exists
    (Usize.add_spec (x := iter.count) (y := 1#usize) (by scalar_tac))
  refine ⟨y, ?_, by simpa using h_y_val⟩
  have h_sn : core.slice.iter.IteratorSliceIter.next iter.iter =
      .ok (some (iter.iter.slice.val[iter.iter.i]),
        ⟨iter.iter.slice, iter.iter.i + 1⟩) := by
    unfold core.slice.iter.IteratorSliceIter.next; rw [dif_pos (by simpa using h_lt)]; rfl
  simp [core.iter.adapters.enumerate.IteratorEnumerate.next, h_sn, h_add_eq]

/-- `Enumerate<slice::Iter<GF16>>::next` once the slice is exhausted. -/
private lemma enum_next_none
    (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter GF16))
    (h_ge : ¬ iter.iter.i < iter.iter.slice.val.length) :
    core.iter.adapters.enumerate.IteratorEnumerate.next
        (core.iter.traits.iterator.IteratorSliceIter GF16) iter = ok (none, iter) := by
  simp [core.iter.adapters.enumerate.IteratorEnumerate.next,
    core.slice.iter.IteratorSliceIter.next, Slice.len, h_ge]

/-- Loop invariant for `point_at_loop0_loop0`: after consuming the first `iter.iter.i`
elements of `s`, `pt_vec` holds exactly the points `(j, s[j])` for `j < iter.iter.i`. -/
abbrev _root_.spqr.encoding.polynomial.PolyEncoder.pointAtInnerInv (s : Slice GF16)
    (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter GF16))
    (pt_vec : alloc.vec.Vec Pt) : Prop :=
  iter.iter.slice = s ∧
  iter.count.val = iter.iter.i ∧
  iter.iter.i ≤ s.val.length ∧
  pt_vec.val.length = iter.iter.i ∧
  (∀ j (hj : j < pt_vec.val.length) (hs : j < s.val.length),
    (pt_vec.val.get ⟨j, hj⟩).x.value.val = j ∧
    (pt_vec.val.get ⟨j, hj⟩).y = s.val.get ⟨j, hs⟩)

/-- Postcondition of `point_at_loop0_loop0`: `pt_vec` holds the points `(j, s[j])` for all
`j < s.len()`. -/
abbrev _root_.spqr.encoding.polynomial.PolyEncoder.pointAtInnerPost (s : Slice GF16)
    (pt_vec : alloc.vec.Vec Pt) : Prop :=
  pt_vec.val.length = s.val.length ∧
  (∀ j (hj : j < pt_vec.val.length) (hs : j < s.val.length),
    (pt_vec.val.get ⟨j, hj⟩).x.value.val = j ∧
    (pt_vec.val.get ⟨j, hj⟩).y = s.val.get ⟨j, hs⟩)

/-- **Spec theorem for `encoding.polynomial.PolyEncoder.point_at_loop0_loop0.body`**:

One iteration of `for (x, y) in pts[i].value.iter().enumerate()`: pushes
`Pt { x: GF16::new(x as u16), y: *y }` onto `pt_vec`, preserving `pointAtInnerInv`, or
terminates with `pointAtInnerPost` once the slice is exhausted. -/
@[step]
theorem body_spec
    (s : Slice GF16)
    (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter GF16))
    (pt_vec : alloc.vec.Vec Pt)
    (h_len_le : s.val.length ≤ UScalar.max .U16)
    (h_inv : pointAtInnerInv s iter pt_vec) :
    body iter pt_vec ⦃ cf =>
      match cf with
      | ControlFlow.done pt_vec' => pointAtInnerPost s pt_vec'
      | ControlFlow.cont p =>
          pointAtInnerInv s p.1 p.2 ∧
          s.val.length - p.1.iter.i < s.val.length - iter.iter.i ⦄ := by
  obtain ⟨h_slice, h_count, h_i_le, h_vlen, h_elts⟩ := h_inv
  subst h_slice
  unfold body
  by_cases h_lt : iter.iter.i < iter.iter.slice.val.length
  · have h_u16 : iter.count.val ≤ UScalar.max .U16 := by
      simp only [UScalar.max_UScalarTy_U16_eq, U16.max_eq] at h_len_le ⊢; omega
    obtain ⟨count', h_next, h_count'⟩ :=
      enum_next_some iter h_lt (by have := iter.count.hBounds; scalar_tac)
    simp only [h_next, bind_ok, GF16.new_eq]
    step*
    subst ‹_ = UScalar.cast UScalarTy.U16 iter.count›
    have h_i_val : (UScalar.cast UScalarTy.U16 iter.count).val = iter.iter.i := by
      simp only [UScalar.cast_val_eq, UScalarTy.U16_numBits_eq, Nat.reducePow]
      rw [Nat.mod_eq_of_lt (by
        simp only [UScalar.max_UScalarTy_U16_eq, U16.max_eq] at h_u16; omega)]
      exact h_count
    obtain h_v1 : pt_vec1.val = pt_vec.val ++
        [{ x := { value := UScalar.cast UScalarTy.U16 iter.count },
           y := iter.iter.slice.val[iter.iter.i] }] := ‹_›
    refine ⟨by omega, by omega, by simp [h_v1, h_vlen], ?_, by omega⟩
    intro j hj hs
    simp only [List.get_eq_getElem, h_v1] at hj ⊢
    by_cases hjl : j < pt_vec.val.length
    · rw [List.getElem_append_left hjl]
      simpa using h_elts j hjl hs
    · have hj_eq : j = pt_vec.val.length := by simp at hj; omega
      subst hj_eq
      simp [h_i_val, h_vlen]
  · rw [enum_next_none iter h_lt]
    simp only [GF16.new_eq, bind_ok, uncurry_apply_pair, and_assoc, List.get_eq_getElem,
      WP.spec_ok]
    exact ⟨by omega, h_elts⟩

/-- **Spec theorem for `encoding.polynomial.PolyEncoder.point_at_loop0_loop0`**:

Running the inner loop from a state satisfying `pointAtInnerInv` produces a vector satisfying
`pointAtInnerPost`. -/
@[step]
theorem loop_spec
    (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter GF16))
    (pt_vec : alloc.vec.Vec Pt)
    (h_len_le : iter.iter.slice.val.length ≤ UScalar.max .U16)
    (h_inv : pointAtInnerInv iter.iter.slice iter pt_vec) :
    point_at_loop0_loop0 iter pt_vec ⦃ pt_vec' =>
      pointAtInnerPost iter.iter.slice pt_vec' ⦄ := by
  unfold point_at_loop0_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter GF16) ×
                       alloc.vec.Vec Pt) => iter.iter.slice.val.length - p.1.iter.i)
    (inv := fun p => pointAtInnerInv iter.iter.slice p.1 p.2)
  · rintro ⟨iter', pt_vec'⟩ h_inv'
    apply WP.spec_mono (body_spec iter.iter.slice iter' pt_vec' h_len_le h_inv')
    rintro (_ | _) h <;> exact h
  · exact h_inv

end spqr.encoding.polynomial.PolyEncoder.point_at_loop0_loop0

namespace spqr.encoding.polynomial.PolyEncoder.point_at_loop0

/-! ## Helper lemma: double-set at the same index -/

/-- Setting an array at index `i` twice yields the second value at `i` (List-level). -/
private lemma array_set_restore_set_val_getElem!
    {α : Type} {n : Usize} [Inhabited α]
    (arr : Array α n) (i : Usize) (y : α) (hi : i.val < n.val) :
    ((arr.set i (arr.val[i.val]!)).set i y).val[i.val]! = y := by
  simp only [Array.set_getElem!_eq, Array.set_val_eq]
  have : i.val < arr.val.length := by rw [arr.property]; exact hi
  grind

/-- Setting an array at index `i` twice yields the second value at `i` (Array-level). -/
private lemma array_set_restore_set_getElem!
    {α : Type} {n : Usize} [Inhabited α]
    (arr : Array α n) (i : Usize) (y : α) (hi : i.val < n.val) :
    ((arr.set i (arr.val[i.val]!)).set i y)[i]! = y := by
  simp only [Array.getElem!_Usize_eq, Array.set_getElem!_eq, Array.set_val_eq]
  have : i.val < arr.val.length := by rw [arr.property]; exact hi
  grind

/-! ## Bridge for the map+collect pipeline -/

/-! ## Spec theorem for the point_at loop body -/

/-- **Spec theorem for `encoding.polynomial.PolyEncoder.point_at_loop0.body`**:

One step of the point-to-polynomial conversion loop. Given `pts` (16 `Point`s), a range
iterator, and the current `polys` array, retrieves the next index `i` and either:

• **Done**: returns `polys` unchanged when the iterator is exhausted.
• **Cont**: builds evaluation points via the inner enumerate/push loop, interpolates via
  `Poly::from_complete_points`, stores the result in `polys[i]`, and advances the iterator.

Preconditions: iterator end ≤ 16, each point has admissible length (0/1/3/5/30/34/36).

**Source**: spqr/src/encoding/polynomial.rs (lines 636:12-658:13)
-/
@[step]
theorem body_spec
    (pts : Array Point 16#usize)
    (iter : core.ops.range.Range Std.Usize)
    (polys : Array Poly 16#usize)
    (h_end_le_16 : iter.end.val ≤ 16)
    (h_admissible : ∀ (j : Nat), j < 16 →
        let len := (pts.val[j]!).value.val.length
        len = 0 ∨ len = 1 ∨ len = 3 ∨ len = 5 ∨
        len = 30 ∨ len = 34 ∨ len = 36) :
    body pts iter polys ⦃ cf =>
      match cf with
      | ControlFlow.done polys' =>
          polys' = polys ∧
          ¬(iter.start < iter.end)
      | ControlFlow.cont (iter1, polys') =>
          iter.start < iter.end ∧
          iter1.start = iter.start.val + 1 ∧
          iter1.end = iter.end ∧
          (∀ k, k ≠ iter.start.val →
            polys'.val[k]! = polys.val[k]!) ∧
            (polys'.val[iter.start.val]!).degree + 1 ≤ Usize.max ∧
            (polys'.val[iter.start.val]!.toGF216Poly =
            ∑ j ∈ Finset.range (pts.val[iter.start.val]!).value.val.length,
            C (((pts.val[iter.start.val]!).value.val[j]!).toGF216) *
            scaledLagrangeBasis (alloc.vec.Vec.len ((pts.val[iter.start.val]!).value)) j) ⦄ := by
  unfold body
  step with core.iter.range.IteratorRange.next_Usize_spec' iter as
    ⟨opt, iter1', h_none, h_some⟩
  by_cases h_lt : iter.start.val < iter.end.val
  · obtain ⟨h_opt_eq, h_start1, h_end1⟩ := h_some h_lt
    rw [h_opt_eq]
    have h_i_lt_16 : iter.start.val < 16 := by omega
    have h_adm := h_admissible iter.start.val h_i_lt_16
    simp only [UScalar.lt_equiv, UScalar.ofNatCore_val_eq, not_lt,
      List.getElem!_eq_getElem?_getD, ne_eq]
    simp only [core.slice.Slice.iter, core.iter.traits.iterator.Iterator.enumerate.trait_default,
      core.iter.traits.iterator.Iterator.enumerate.default]
    step as ⟨p, p_post⟩
    subst p_post
    have h_len_le : (alloc.vec.Vec.deref ((pts.val[iter.start.val]!).value)).val.length ≤
        UScalar.max .U16 := by
      have h_dl : (alloc.vec.Vec.deref ((pts.val[iter.start.val]!).value)).val.length =
          (pts.val[iter.start.val]!).value.val.length := by
        simp [alloc.vec.Vec.deref]
      rw [h_dl, UScalar.max_UScalarTy_U16_eq, U16.max_eq]
      rcases h_adm with h | h | h | h | h | h | h <;> omega
    have h_pts_lt : iter.start.val < pts.val.length := by rw [pts.property]; exact h_i_lt_16
    have h_eq : pts.val[iter.start.val] = pts.val[iter.start.val]! :=
      List.Inhabited_getElem_eq_getElem! pts.val iter.start.val h_pts_lt
    simp only [h_eq]; clear h_eq h_pts_lt
    apply WP.spec_bind (point_at_loop0_loop0.loop_spec
      { iter := { slice := alloc.vec.Vec.deref ((pts.val[iter.start.val]!).value), i := 0 },
        count := 0#usize } _ h_len_le
      (by simp [pointAtInnerInv, alloc.vec.Vec.with_capacity, alloc.vec.Vec.new]))
    intro pt_vec ⟨h_pt_len, h_pt_elts⟩
    have h_deref_len : (alloc.vec.Vec.deref pt_vec).val.length =
        (pts.val[iter.start.val]!).value.val.length := by
      simp [alloc.vec.Vec.deref, h_pt_len]
    have h_adm' : (alloc.vec.Vec.deref pt_vec).val.length = 0 ∨
        (alloc.vec.Vec.deref pt_vec).val.length = 1 ∨
        (alloc.vec.Vec.deref pt_vec).val.length = 3 ∨
        (alloc.vec.Vec.deref pt_vec).val.length = 5 ∨
        (alloc.vec.Vec.deref pt_vec).val.length = 30 ∨
        (alloc.vec.Vec.deref pt_vec).val.length = 34 ∨
        (alloc.vec.Vec.deref pt_vec).val.length = 36 := by
      rw [h_deref_len]; exact h_adm
    apply WP.spec_bind
      (encoding.polynomial.Poly.from_complete_points_spec (alloc.vec.Vec.deref pt_vec) h_adm')
    intro res h_res
    have h_valid : ∀ (j : Nat) (hj : j < (alloc.vec.Vec.deref pt_vec).val.length),
        ((alloc.vec.Vec.deref pt_vec).val.get ⟨j, hj⟩).x.value.val = j := by
      intro j hj
      simp only [alloc.vec.Vec.deref, Slice.from_val, List.get_eq_getElem] at hj ⊢
      exact (h_pt_elts j hj (by omega)).1
    match res with
    | core.result.Result.Ok poly =>
      obtain ⟨h_all_valid, h_deg, h_sum⟩ := h_res
      simp only [core.result.Result.expect]
      simp only [massert]
      have h_massert : (iter.start.val < 16) = True := by grind
      simp only [h_massert, ↓reduceIte]
      step*
      constructor
      · grind
      · constructor
        · grind
        · constructor
          · grind
          · constructor
            · intro k hk
              simp_all
            · have h_a_eq : a[iter.start]! = poly := by
                have h_pl : iter.start.val < polys.val.length := by simp; omega
                subst_vars
                simp only [Array.getElem!_Usize_eq, Array.set_val_eq]
                simp [List.getElem?_set_self h_pl]
              constructor
              · simp only [Array.getElem!_Usize_eq] at h_a_eq
                grind
              · have h_slicelen_eq : Slice.len (alloc.vec.Vec.deref pt_vec) =
                    alloc.vec.Vec.len ((pts.val[iter.start.val]!).value) := by
                  simp [Slice.len, alloc.vec.Vec.len, alloc.vec.Vec.deref] at h_deref_len ⊢
                  grind
                rw [h_slicelen_eq] at h_sum
                simp_all only [List.length_eq_zero_iff, not_true_eq_false, reduceCtorEq, false_and,
                    implies_true, and_self, UScalar.max_UScalarTy_U16_eq, List.get_eq_getElem,
                    forall_true_left, List.getElem!_eq_getElem?_getD, eq_iff_iff, iff_true,
                    Array.getElem!_Usize_eq, Array.set_val_eq, List.set_getElem_self]
                apply Finset.sum_congr rfl
                intro j hj
                have hj_range := Finset.mem_range.mp hj
                have hj_pt : j < pt_vec.val.length := by
                  rw [h_pt_len]; simpa [alloc.vec.Vec.deref] using hj_range
                have hy := (h_pt_elts j (by simpa [alloc.vec.Vec.deref] using hj_range)).2
                simp only [alloc.vec.Vec.deref, Slice.from_val] at hy ⊢
                rw [List.getElem?_eq_getElem hj_pt, Option.getD_some, hy]
                simp only [alloc.vec.Vec.len, List.getElem?_eq_getElem hj_range, Option.getD_some]
    | core.result.Result.Err () =>
      exfalso
      obtain ⟨j, hj, h_neq⟩ := h_res
      exact h_neq (h_valid j hj)
  · obtain ⟨h_opt_eq, _⟩ := h_none (by omega)
    simp [h_opt_eq, WP.spec_ok, h_lt]

/-- **Spec theorem for `encoding.polynomial.PolyEncoder.point_at_loop0`**:

The full point-to-polynomial conversion loop. Iterates over `0..NUM_POLYS`, building
Lagrange interpolating polynomials for each point in `pts` and storing them in `polys`.

Succeeds provided: iterator end ≤ 16, each point has admissible length (0/1/3/5/30/34/36),
and pre-existing entries satisfy the interpolation invariant. -/
@[step]
theorem loop_spec
    (pts : Array encoding.polynomial.Point 16#usize)
    (iter : core.ops.range.Range Std.Usize)
    (polys : Array encoding.polynomial.Poly 16#usize)
    (h_end_le_16 : iter.end.val ≤ 16)
    (h_start_le : iter.start.val ≤ iter.end.val)
    (h_admissible : ∀ (j : Nat), j < 16 →
        let len := (pts.val[j]!).value.val.length
        len = 0 ∨ len = 1 ∨ len = 3 ∨ len = 5 ∨
        len = 30 ∨ len = 34 ∨ len = 36)
    (h_pre : ∀ (j : Nat), j < iter.start.val →
        (polys.val[j]!).degree + 1 ≤ Usize.max ∧
        polys.val[j]!.toGF216Poly = ∑ k ∈ Finset.range (pts.val[j]!).value.val.length,
            C (((pts.val[j]!).value.val[k]!).toGF216) *
              scaledLagrangeBasis (alloc.vec.Vec.len ((pts.val[j]!).value)) k) :
    point_at_loop0 iter pts polys ⦃ (polys' : Array encoding.polynomial.Poly 16#usize) =>
      ∀ (j : Nat), j < iter.end.val →
        (polys'.val[j]!).degree + 1 ≤ Usize.max ∧
        polys'.val[j]!.toGF216Poly = ∑ k ∈ Finset.range (pts.val[j]!).value.val.length,
            C (((pts.val[j]!).value.val[k]!).toGF216) *
              scaledLagrangeBasis (alloc.vec.Vec.len ((pts.val[j]!).value)) k ⦄ := by
  unfold point_at_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : core.ops.range.Range Std.Usize ×
                       Array encoding.polynomial.Poly 16#usize) =>
                  p.1.end.val - p.1.start.val)
    (inv := fun (p : core.ops.range.Range Std.Usize ×
                     Array encoding.polynomial.Poly 16#usize) =>
        let iter' := p.1
        let polys' := p.2
        iter'.end = iter.end ∧
        iter'.start.val ≤ iter'.end.val ∧
        (∀ (j : Nat), j < iter'.start.val →
          (polys'.val[j]!).degree + 1 ≤ Usize.max ∧
          polys'.val[j]!.toGF216Poly =
            ∑ k ∈ Finset.range
                (pts.val[j]!).value.val.length,
              C (((pts.val[j]!).value.val[k]!).toGF216) *
                scaledLagrangeBasis
                  (alloc.vec.Vec.len ((pts.val[j]!).value)) k))
  · rintro ⟨iter', polys'⟩ ⟨h_end', h_start_le', h_pre'⟩
    simp only [] at h_end' h_start_le' h_pre' ⊢
    have h_end_val : iter'.end.val = iter.end.val := by rw [h_end']
    have h_body := body_spec pts iter' polys' (by omega) h_admissible
    apply WP.spec_mono h_body
    intro cf h_cf
    match cf with
    | ControlFlow.done polys'' =>
      simp only [] at h_cf ⊢
      obtain ⟨h_out_eq, h_not_lt⟩ := h_cf
      subst h_out_eq
      exact fun j hj => h_pre' j (by grind)
    | ControlFlow.cont (iter'', polys'') =>
      simp only [] at h_cf ⊢
      obtain ⟨h_lt, h_start1, h_end1, h_preserve, h_deg_new, h_sum⟩ := h_cf
      constructor
      · refine ⟨by rw [h_end1]; exact h_end',
               by grind,
               fun j hj => ?_⟩
        by_cases hj_lt : j < iter'.start.val
        · constructor
          · rw [h_preserve j (by omega)]
            exact (h_pre' j hj_lt).1
          · rw [h_preserve j (by omega)]
            exact (h_pre' j hj_lt).2
        · have hj_eq : j = iter'.start.val := by omega
          subst hj_eq
          exact ⟨h_deg_new, h_sum⟩
      · grind
  · exact ⟨rfl, h_start_le, h_pre⟩

end spqr.encoding.polynomial.PolyEncoder.point_at_loop0

/-!
# Spec theorem for `spqr::encoding::polynomial::{PolyEncoder}::point_at`

`PolyEncoder::point_at` returns the GF(2¹⁶) evaluation of the `poly`-th polynomial at index `idx`.
Handles two encoder states:
1. **Polys**: directly evaluates the stored polynomial.
2. **Points**: returns cached value if `idx < len`, otherwise converts all 16 points to
   interpolating polynomials via `point_at_loop0` and evaluates.

**Source**: spqr/src/encoding/polynomial.rs -/

namespace spqr.encoding.polynomial.PolyEncoder

/-- **Spec theorem for `encoding.polynomial.PolyEncoder.point_at`** (Lagrange-sum level):

Returns GF(2¹⁶) evaluation of the `poly`-th polynomial at index `idx`. Three cases:
• **Polys**: evaluates stored polynomial, state unchanged.
• **Points, cache hit**: returns `pts[poly].value[idx]`, state unchanged.
• **Points, cache miss**: converts to `Polys` via Lagrange interpolation, then evaluates.

Composes `point_at_loop0.loop_spec` and `Poly.compute_at_spec`. -/
@[step]
theorem point_at_spec
    (self : encoding.polynomial.PolyEncoder) (poly idx : Std.Usize)
    (h_poly : poly.val < 16)
    (h_idx_u16 : idx.val ≤ UScalar.max .U16)
    (h_admissible : ∀ pts, self.s = .Points pts →
        ∀ (j : Nat), j < 16 →
          let len := (pts.val[j]!).value.val.length
          len = 0 ∨ len = 1 ∨ len = 3 ∨ len = 5 ∨
          len = 30 ∨ len = 34 ∨ len = 36)
    (h_coeff_polys : ∀ polys, self.s = .Polys polys →
        (polys.val[poly.val]!).coefficients.length + 1 ≤ Usize.max) :
    point_at self poly idx ⦃ ((result, self') : GF16 × PolyEncoder) =>
      self'.idx = self.idx ∧
      match self.s with
      | .Points pts =>
            if idx < (pts.val[poly.val]!).value.length then
              result = (pts.val[poly.val]!).value.val[idx.val]! ∧
              self' = self
            else
              match self'.s with
              | .Polys polys' =>
                  (∀ (j : Nat), j < 16 →
                    polys'[j]!.toGF216Poly = ∑ k ∈ Finset.range (pts[j]!).value.length,
                        C (((pts[j]!).value[k]!).toGF216) *
                          scaledLagrangeBasis (alloc.vec.Vec.len ((pts[j]!).value)) k) ∧
                  (∀ (j : Nat), j < 16 →
                    (polys'.val[j]!).coefficients.length + 1 ≤ Usize.max) ∧
                  result.toGF216 = (polys'[poly]!).toGF216Poly.eval (idx.val.toGF216)
              | .Points _ => False
      | .Polys polys =>
            result.toGF216 = (polys.val[poly.val]!).toGF216Poly.eval (idx.val.toGF216) ∧
            self' = self ⦄ := by
  unfold point_at
  cases hs : self.s with
  | Polys polys =>
    simp only
    have h_deg : (polys.val[poly.val]!).degree + 1 ≤ Usize.max :=
      h_coeff_polys polys hs
    have h_polys_len : poly.val < polys.val.length := by rw [polys.property]; exact h_poly
    step*
    · grind
    simp only [Poly.evalAt] at g1_post
    subst p_post
    rw [List.Inhabited_getElem_eq_getElem! polys.val poly.val h_polys_len] at g1_post
    rw [g1_post]
    congr 1
    rw [g_post]
    simp_all [UScalar.cast_val_eq, UScalarTy.U16_numBits_eq, Nat.reducePow]
    grind
  | Points pts =>
    simp only
    have h_adm : ∀ (j : Nat), j < 16 →
        let len := (pts.val[j]!).value.val.length
        len = 0 ∨ len = 1 ∨ len = 3 ∨ len = 5 ∨
        len = 30 ∨ len = 34 ∨ len = 36 := h_admissible pts hs
    have h_pts_len : poly.val < pts.val.length := by rw [pts.property]; exact h_poly
    step
    by_cases h_lt : idx < alloc.vec.Vec.len p.value
    · simp only [h_lt, ↓reduceIte]
      step*
      have h_lt_nat : idx.val < (pts.val[poly.val]!).value.val.length := by
        subst p_post
        simp only [UScalar.lt_equiv, alloc.vec.Vec.len] at h_lt
        rw [List.Inhabited_getElem_eq_getElem! pts.val poly.val h_pts_len] at h_lt
        exact h_lt
      simp only [h_lt_nat, ↓reduceIte]
      subst p_post
      grind
    · simp only [h_lt, ↓reduceIte]
      have h_not_lt_nat : ¬ idx.val < (pts.val[poly.val]!).value.val.length := by
        subst p_post
        simp only [UScalar.lt_equiv, alloc.vec.Vec.len, not_lt] at h_lt ⊢
        rw [List.Inhabited_getElem_eq_getElem! pts.val poly.val h_pts_len] at h_lt
        grind
      step*
      case hl =>
        apply core.array.from_fn_loop_replicate_default
        · intro i
          simp [PolyEncoder.point_at.closure.Insts.CoreOpsFunctionFnMutTupleUsizePoly.call_mut,
                Poly.zero, alloc.vec.Vec.with_capacity]
          rfl
        · scalar_tac
      case hlen => simp
      step*
      case h_len =>
        subst p1_post
        have h_poly_lt : poly.val < polys1.val.length := by
          rw [polys1.property]; exact h_poly
        have h_poly_spec := polys1_post poly.val (by grind)
        rw [List.Inhabited_getElem_eq_getElem! polys1.val poly.val h_poly_lt]
        exact h_poly_spec.1
      simp_all only [↓reduceIte]
      refine ⟨?_, ?_, ?_⟩
      · intro j hj
        have := polys1_post j (by grind)
        grind
      · intro j hj
        have h_spec := polys1_post j (by grind)
        simp only [Poly.degree] at h_spec
        exact h_spec.1
      · have h_poly_lt : poly.val < polys1.val.length := by
          rw [polys1.property]; exact h_poly
        have h_eq : polys1.val[poly.val] = polys1.val[poly.val]! :=
          List.Inhabited_getElem_eq_getElem! polys1.val poly.val h_poly_lt
        simp only [Poly.evalAt, h_eq, Array.getElem!_Usize_eq]
        congr 1
        rw [g_post]
        simp [UScalar.cast_val_eq, UScalarTy.U16_numBits_eq, Nat.reducePow]
        grind

end spqr.encoding.polynomial.PolyEncoder
