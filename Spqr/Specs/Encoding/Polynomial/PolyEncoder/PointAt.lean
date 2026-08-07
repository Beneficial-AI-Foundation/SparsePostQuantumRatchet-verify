/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Encoding.Polynomial.NUM_POLYS
import Spqr.Specs.Encoding.Polynomial.Poly.ComputeAt
import Spqr.Math.Poly.Lagrange.CompletePoints
import Spqr.Specs.Encoding.Polynomial.Poly.FromCompletePoints
import Spqr.Specs.Encoding.Polynomial.PolyEncoder.PointAt.CallOnce
import Spqr.Specs.Aeneas.MapIteratorTransformerNext
import Spqr.Specs.Encoding.Polynomial.PolyEncoder.PointAt.SliceIterEnumMapCollect


/-!
# Spec theorem for `PolyEncoder::point_at`: loop body 0

One step of the conversion loop in `PolyEncoder::point_at` (lines 636–658), which iterates over
`0..NUM_POLYS` and constructs the Lagrange interpolating polynomial for each `Point` in GF(2¹⁶).

Given index `i` from the range iterator, the body either returns unchanged (`none`) or builds
evaluation points via enumerate-map-collect, calls `Poly::from_complete_points`, and stores
the result in `polys[i]`.

The proof composes `IteratorRange.next`, `Array.index_usize`, the enumerate-map-collect pipeline,
`Poly::from_complete_points`, `Result.expect`, and `Array.update`.

**Source**: spqr/src/encoding/polynomial.rs -/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf Polynomial
open PolyEncoder.point_at.closure_1  core.iter.adapters.map.Map

namespace spqr.encoding.polynomial.PolyEncoder.point_at_loop

/-- Default `Inhabited` instance for `Point` (empty value vector). -/
instance instInhabitedPoint_spqr : Inhabited encoding.polynomial.Point := ⟨⟨alloc.vec.Vec.new _⟩⟩

/-! ## Helper lemmas for the enumerate-map-collect pipeline -/

/-- Abbreviation for the Enumerate iterator type used in the point_at pipeline. -/
private abbrev PointAtEnumT := core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter GF16)

/-- Abbreviation for the Map iterator type used in the point_at pipeline. -/
private abbrev PointAtMapT :=
  core.iter.adapters.map.Map (core.iter.adapters.enumerate.Enumerate
    (core.slice.iter.Iter GF16)) PolyEncoder.point_at.closure_1

/-- Inductive characterisation of `iterToList` for the enumerate-map-of-slice iterator
in `PolyEncoder::point_at`. -/
private theorem iterToList_enum_map_acc
    (n : Nat)
    (enum_iter : PointAtEnumT)
    (acc : List Pt)
    (h_n : n = enum_iter.iter.slice.val.length - enum_iter.iter.i)
    (h_count : enum_iter.count.val = enum_iter.iter.i)
    (h_len_le : enum_iter.iter.slice.val.length ≤ UScalar.max .U16)
    (transIterInst : core.iter.traits.iterator.Iterator PointAtEnumT Pt)
    (h_next : transIterInst.next = fun e => do
      let (opt, iter') ←
        (core.iter.traits.iterator.IteratorEnumerate
          (core.iter.traits.iterator.IteratorSliceIter GF16)).next e
      match opt with
      | none =>
        .ok (none, iter')
      | some item => do
        let (b, _) ←
        PolyEncoder.point_at.closure_1.Insts.CoreOpsFunctionFnMutTuplePairUsizeSharedGF16Pt.call_mut
            () item
        .ok (some b, iter')) :
    ∃ (L : List Pt),
      alloc.vec.FromIteratorVec.iterToList transIterInst enum_iter acc =
        .ok (acc.reverse ++ L) ∧
      L.length = enum_iter.iter.slice.val.length - enum_iter.iter.i ∧
      (∀ j (hj : j < L.length) (hs : j + enum_iter.iter.i < enum_iter.iter.slice.val.length),
          (L.get ⟨j, hj⟩).x.value.val = j + enum_iter.iter.i ∧
          (L.get ⟨j, hj⟩).y =
            enum_iter.iter.slice.val.get ⟨j + enum_iter.iter.i, hs⟩) := by
  induction n generalizing enum_iter acc with
  | zero =>
    have h_ge : ¬ (enum_iter.iter.i < enum_iter.iter.slice.val.length) := by omega
    refine ⟨[], ?_, by simp; omega, by intro j hj; omega⟩
    conv_lhs => unfold alloc.vec.FromIteratorVec.iterToList
    rw [h_next]
    simp  [
      core.iter.adapters.enumerate.IteratorEnumerate.next,
      core.slice.iter.IteratorSliceIter.next, Slice.len, h_ge,
      ↓reduceDIte, bind_tc_ok]
  | succ n ih =>
    have h_lt : enum_iter.iter.i < enum_iter.iter.slice.val.length := by omega
    have h_count_lt : enum_iter.count.val < 2 ^ 16 := by
      have : enum_iter.count.val = enum_iter.iter.i := h_count
      have : enum_iter.iter.i < enum_iter.iter.slice.val.length := h_lt
      have : enum_iter.iter.slice.val.length ≤ UScalar.max .U16 := h_len_le
      simp  at h_len_le ⊢
      grind
    have h_count_add : enum_iter.count.val + 1 ≤ Usize.max := by
      have := enum_iter.count.hBounds; scalar_tac
    have h_cm_eq :
      PolyEncoder.point_at.closure_1.Insts.CoreOpsFunctionFnMutTuplePairUsizeSharedGF16Pt.call_mut
        () (enum_iter.count, enum_iter.iter.slice.val.get ⟨enum_iter.iter.i, h_lt⟩) =
        .ok ({ x := { value := UScalar.cast .U16 enum_iter.count },
               y := enum_iter.iter.slice.val.get ⟨enum_iter.iter.i, h_lt⟩ },
              ()) := by
      unfold Insts.CoreOpsFunctionFnMutTuplePairUsizeSharedGF16Pt.call_mut
      simp only [ uncurry_apply_pair]
      simp only [lift, bind_tc_ok]
      unfold encoding.gf.GF16.new
      simp [bind_tc_ok]
    set pt : Pt := { x := { value := UScalar.cast .U16 enum_iter.count },
                     y := enum_iter.iter.slice.val.get ⟨enum_iter.iter.i, h_lt⟩ }
    have h_pt_x : pt.x.value.val = enum_iter.iter.i := by
      simp only [UScalar.cast_val_eq, UScalarTy.U16_numBits_eq, Nat.reducePow, pt]
      rw [Nat.mod_eq_of_lt (by omega)]
      exact h_count
    have h_pt_y : pt.y = enum_iter.iter.slice.val.get ⟨enum_iter.iter.i, h_lt⟩ := by
      simp [pt]
    set enum_iter' : PointAtEnumT :=
      { iter := core.slice.iter.Iter.mk enum_iter.iter.slice (enum_iter.iter.i + 1),
        count := ⟨enum_iter.count.val + 1, by scalar_tac⟩ }
    have hei'_slice : enum_iter'.iter.slice = enum_iter.iter.slice := rfl
    have hei'_i : enum_iter'.iter.i = enum_iter.iter.i + 1 := rfl
    have hei'_count : enum_iter'.count.val = enum_iter'.iter.i := by
      simp [enum_iter', h_count]
      rfl
    have h_step : alloc.vec.FromIteratorVec.iterToList transIterInst enum_iter acc =
        alloc.vec.FromIteratorVec.iterToList transIterInst enum_iter'
          (pt :: acc) := by
      conv_lhs => unfold alloc.vec.FromIteratorVec.iterToList
      rw [h_next]
      simp only [core.iter.adapters.enumerate.IteratorEnumerate.next,
        core.slice.iter.IteratorSliceIter.next, Slice.len, Usize.ofNatCore_val_eq, h_lt,
        ↓reduceDIte, bind_tc_ok, bind_assoc, uncurry_apply_pair]
      erw [h_cm_eq]
      simp only [bind_tc_ok, uncurry_apply_pair]
      have ⟨y, h_add_eq, h_y_val⟩ :
          ∃ y, (enum_iter.count + 1#usize : Result Usize) = ok y
          ∧ y.val = enum_iter.count.val + 1 := by
        have : enum_iter.count.val + (1#usize : Usize).val ≤ Usize.max := by scalar_tac
        have := Usize.add_spec this
        revert this; generalize (enum_iter.count + 1#usize : Result Usize) = res
        match res with
        | .ok z => intro h; exact ⟨z, rfl, by simp_all [WP.spec_ok]⟩
        | .fail _ => simp_all
        | .div => simp_all
      have : y = enum_iter'.count := by apply UScalar.eq_of_val_eq; omega
      subst this
      simp only [h_add_eq, bind_tc_ok, enum_iter']
    have h_n' : n = enum_iter'.iter.slice.val.length - enum_iter'.iter.i := by
      rw [hei'_slice, hei'_i]; omega
    obtain ⟨L', hL'_eq, hL'_len, hL'_elts⟩ :=
      ih enum_iter' (pt :: acc) h_n' hei'_count (by rwa [hei'_slice])
    refine ⟨pt :: L', ?_, ?_, ?_⟩
    · rw [h_step, hL'_eq]
      simp [List.reverse_cons, List.append_assoc]
    · simp [hL'_len, hei'_slice, hei'_i]; omega
    · intro j hj hs
      cases j with
      | zero =>
        simp only [Nat.zero_add]
        exact ⟨h_pt_x, h_pt_y⟩
      | succ k =>
        have hk : k < L'.length := by
          have : (pt :: L').length = L'.length + 1 := rfl
          omega
        have hks : k + enum_iter'.iter.i < enum_iter'.iter.slice.val.length := by
          rw [hei'_slice, hei'_i]; omega
        obtain ⟨hx, hy⟩ := hL'_elts k hk hks
        simp only [List.get_eq_getElem, hei'_slice, hei'_i] at hx hy
        refine ⟨?_, ?_⟩
        · show ((pt :: L').get ⟨k + 1, hj⟩).x.value.val = k + 1 + enum_iter.iter.i
          have : (pt :: L').get ⟨k + 1, hj⟩ = L'.get ⟨k, hk⟩ := by rfl
          rw [this]
          grind
        · show ((pt :: L').get ⟨k + 1, hj⟩).y = _
          have : (pt :: L').get ⟨k + 1, hj⟩ = L'.get ⟨k, hk⟩ := by rfl
          rw [this]
          rw [show enum_iter.iter.slice.val.get ⟨k + 1 + enum_iter.iter.i, hs⟩ =
            enum_iter.iter.slice.val.get ⟨k + enum_iter'.iter.i, hks⟩ from by
              congr 1; ext; simp [hei'_i]; omega]
          exact hy

/-- Spec for `from_iter` (collect) in the point_at pipeline. -/
private theorem from_iter_point_at_spec
    (s : Slice GF16)
    (h_len_le : s.val.length ≤ UScalar.max .U16) :
    alloc.vec.FromIteratorVec.from_iter
      (core.iter.traits.collect.IntoIterator.Blanket
        (core.iter.adapters.map.mapIteratorTransformer
          ({ iter := { iter := { slice := s, i := 0 }, count := 0#usize }, f := () } : PointAtMapT)
          (core.iter.traits.iterator.IteratorEnumerate
            (core.iter.traits.iterator.IteratorSliceIter GF16))
          point_at.closure_1.Insts.CoreOpsFunctionFnMutTuplePairUsizeSharedGF16Pt))
      { iter := { slice := s, i := 0 }, count := 0#usize }
    ⦃ (pt_vec : alloc.vec.Vec Pt) =>
      pt_vec.val.length = s.val.length ∧
      (∀ j (hj : j < pt_vec.val.length) (hs : j < s.val.length),
        (pt_vec.val.get ⟨j, hj⟩).x.value.val = j ∧
        (pt_vec.val.get ⟨j, hj⟩).y = s.val.get ⟨j, hs⟩) ⦄ := by
  unfold alloc.vec.FromIteratorVec.from_iter
  simp only
  apply WP.spec_bind (Pₘ := fun (L : List Pt) =>
    L.length = s.val.length ∧
    L.length ≤ Usize.max ∧
    (∀ j (hj : j < L.length) (hs : j < s.val.length),
        (L.get ⟨j, hj⟩).x.value.val = j ∧
        (L.get ⟨j, hj⟩).y = s.val.get ⟨j, hs⟩))
  · obtain ⟨L, hL_eq, hL_len, hL_elts⟩ := iterToList_enum_map_acc
      s.val.length
      { iter := { slice := s, i := 0 }, count := 0#usize }
      [] (by simp) (by simp) h_len_le
      (core.iter.adapters.map.mapIteratorTransformer
        ({ iter := { iter := { slice := s, i := 0 }, count := 0#usize }, f := () } : PointAtMapT)
        (core.iter.traits.iterator.IteratorEnumerate
          (core.iter.traits.iterator.IteratorSliceIter GF16))
        PolyEncoder.point_at.closure_1.Insts.CoreOpsFunctionFnMutTuplePairUsizeSharedGF16Pt)
      (by
        ext e
        grind[ Insts.CoreIterTraitsIteratorIterator.mapIteratorTransformer_next_spec _ _ _ e])
    simp only [List.reverse_nil, List.nil_append] at hL_eq
    rw [hL_eq]
    simp only [WP.spec, WP.theta, WP.wp_return]
    refine ⟨by simp [hL_len], by simp [hL_len]; grind, ?_⟩
    intro j hj hs
    have hs' : j + 0 < s.val.length := by omega
    obtain ⟨hx, hy⟩ := hL_elts j (by omega) hs'
    simp only [List.get_eq_getElem, add_zero] at hx
    exact ⟨hx, hy⟩
  · intro list ⟨h_len, h_max, h_elts⟩
    split
    · exact ⟨h_len, fun j hj hs => h_elts j hj hs⟩
    · omega

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

/-! ## Axiom for the map+collect pipeline -/

/-- `Iterator.collect.default` on a `Map (Enumerate (Iter GF16)) closure_1` equals
`FromIteratorVec.from_iter` with `mapIteratorTransformer`, using `m.iter` as initial state.

This bridges generated Aeneas code with the hand-verified `from_iter_point_at_spec`. -/
private theorem map_collect_eq_point_at
    (m : PointAtMapT) :
    core.iter.traits.iterator.Iterator.collect.default
        (core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator
          (core.iter.traits.iterator.IteratorEnumerate
            (core.iter.traits.iterator.IteratorSliceIter GF16))
          Insts.CoreOpsFunctionFnMutTuplePairUsizeSharedGF16Pt)
        (core.iter.traits.collect.FromIteratorVec Pt)
        m
    = alloc.vec.FromIteratorVec.from_iter
        (core.iter.traits.collect.IntoIterator.Blanket
          (core.iter.adapters.map.mapIteratorTransformer
            ({ iter := m.iter, f := () } : PointAtMapT)
            (core.iter.traits.iterator.IteratorEnumerate
              (core.iter.traits.iterator.IteratorSliceIter GF16))
            Insts.CoreOpsFunctionFnMutTuplePairUsizeSharedGF16Pt))
        m.iter := by
  sorry

/-! ## Spec theorem for the point_at loop body -/

/-- **Spec theorem for `encoding.polynomial.PolyEncoder.point_at_loop.body`**:

One step of the point-to-polynomial conversion loop. Given `pts` (16 `Point`s), a range
iterator, and the current `polys` array, retrieves the next index `i` and either:

• **Done**: returns `polys` unchanged when the iterator is exhausted.
• **Cont**: builds evaluation points via enumerate-map-collect, interpolates via
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
  step as ⟨opt, iter1', h_none, h_some⟩
  by_cases h_lt : iter.start.val < iter.end.val
  · obtain ⟨h_opt_eq, h_start1, h_end1⟩ := h_some h_lt
    rw [h_opt_eq]
    have h_i_lt_16 : iter.start.val < 16 := by omega
    have h_adm := h_admissible iter.start.val h_i_lt_16
    simp only [UScalar.lt_equiv, UScalar.ofNatCore_val_eq, not_lt,
      List.getElem!_eq_getElem?_getD, ne_eq]
    simp only [core.slice.Slice.iter, core.iter.traits.iterator.Iterator.enumerate.trait_default,
      core.iter.traits.iterator.Iterator.enumerate.default, bind_tc_ok]
    step*
    subst p_post
    have h_len_le : (alloc.vec.Vec.deref ((pts.val[iter.start.val]!).value)).val.length ≤
        UScalar.max .U16 := by
      simp only [alloc.vec.Vec.deref, List.getElem!_eq_getElem?_getD, Subtype.coe_eta,
        UScalar.max_UScalarTy_U16_eq]
      rcases h_adm with h | h | h | h | h | h | h <;> (simp_all only [List.Vector.length_val,
        UScalar.ofNatCore_val_eq, getElem!_pos, List.length_eq_zero_iff, not_true_eq_false,
        reduceCtorEq, false_and, implies_true,  and_self,
        getElem?_pos, Option.getD_some, List.length_nil, zero_le])
      all_goals (grind only [= U16.max_eq])
    have h_pts_lt : iter.start.val < pts.val.length := by rw [pts.property]; exact h_i_lt_16
    have h_eq : pts.val[iter.start.val] = pts.val[iter.start.val]! :=
      List.Inhabited_getElem_eq_getElem! pts.val iter.start.val h_pts_lt
    simp only [alloc.vec.Vec.len]
    -- Apply the collect axiom, substitute m.iter via m_post, normalize with h_eq
    simp only [map_collect_eq_point_at, m_post, h_eq]; clear h_eq h_pts_lt
    apply WP.spec_bind (from_iter_point_at_spec
      (alloc.vec.Vec.deref ((pts.val[iter.start.val]!).value)) h_len_le)
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
      simp only [alloc.vec.Vec.deref, Subtype.coe_eta, List.get_eq_getElem] at hj ⊢
      exact (h_pt_elts j hj (by omega)).1
    match res with
    | core.result.Result.Ok poly =>
      obtain ⟨h_all_valid, h_deg, h_sum⟩ := h_res
      simp only [core.result.Result.expect, bind_tc_ok]
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
                rw [a_post, p2_post1, p2_post2]
                rw [List.Inhabited_getElem_eq_getElem! polys.val iter.start.val
                  (by rw [polys.property]; exact h_i_lt_16)]
                exact array_set_restore_set_getElem! polys iter.start poly (by grind)
              constructor
              · simp only [Array.getElem!_Usize_eq] at h_a_eq
                grind
              · have h_slicelen_eq : Slice.len (alloc.vec.Vec.deref pt_vec) =
                    alloc.vec.Vec.len ((pts.val[iter.start.val]!).value) := by
                  simp [Slice.len, alloc.vec.Vec.len, alloc.vec.Vec.deref] at h_deref_len ⊢
                  grind
                rw [h_slicelen_eq] at h_sum
                simp_all only [List.Vector.length_val, UScalar.ofNatCore_val_eq, getElem!_pos,
                    List.length_eq_zero_iff, not_true_eq_false, reduceCtorEq, false_and,
                    implies_true, and_self,  UScalar.max_UScalarTy_U16_eq,
                    List.get_eq_getElem, forall_true_left, List.getElem!_eq_getElem?_getD,
                    eq_iff_iff, iff_true, Array.getElem!_Usize_eq, Array.set_val_eq,
                    List.set_getElem_self, List.length_set, List.getElem_set_self, getElem?_pos,
                    Option.getD_some]
                apply Finset.sum_congr rfl
                intro j hj
                have hj_range := Finset.mem_range.mp hj
                have hj_pt : j < pt_vec.val.length := by
                  simp [alloc.vec.Vec.deref] at *; omega
                have hy := (h_pt_elts j
                  (by simp [alloc.vec.Vec.deref]; omega)).2
                simp only [alloc.vec.Vec.deref] at hy
                simp only [alloc.vec.Vec.deref,
                  List.getElem?_eq_getElem hj_pt,
                  List.getElem?_eq_getElem hj_range,
                  Option.getD_some]
                rw [hy]
    | core.result.Result.Err () =>
      exfalso
      obtain ⟨j, hj, h_neq⟩ := h_res
      exact h_neq (h_valid j hj)
  · obtain ⟨h_opt_eq, _⟩ := h_none (by omega)
    rw [h_opt_eq]
    exact ⟨rfl, h_lt⟩

/-- **Spec theorem for `encoding.polynomial.PolyEncoder.point_at_loop`**:

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
    point_at_loop iter pts polys ⦃ (polys' : Array encoding.polynomial.Poly 16#usize) =>
      ∀ (j : Nat), j < iter.end.val →
        (polys'.val[j]!).degree + 1 ≤ Usize.max ∧
        polys'.val[j]!.toGF216Poly = ∑ k ∈ Finset.range (pts.val[j]!).value.val.length,
            C (((pts.val[j]!).value.val[k]!).toGF216) *
              scaledLagrangeBasis (alloc.vec.Vec.len ((pts.val[j]!).value)) k ⦄ := by
  unfold point_at_loop
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

end spqr.encoding.polynomial.PolyEncoder.point_at_loop

/-!
# Spec theorem for `spqr::encoding::polynomial::{PolyEncoder}::point_at`

`PolyEncoder::point_at` returns the GF(2¹⁶) evaluation of the `poly`-th polynomial at index `idx`.
Handles two encoder states:
1. **Polys**: directly evaluates the stored polynomial.
2. **Points**: returns cached value if `idx < len`, otherwise converts all 16 points to
   interpolating polynomials via `point_at_loop` and evaluates.

**Source**: spqr/src/encoding/polynomial.rs -/

namespace spqr.encoding.polynomial.PolyEncoder

/-- **Spec theorem for `encoding.polynomial.PolyEncoder.point_at`** (Lagrange-sum level):

Returns GF(2¹⁶) evaluation of the `poly`-th polynomial at index `idx`. Three cases:
• **Polys**: evaluates stored polynomial, state unchanged.
• **Points, cache hit**: returns `pts[poly].value[idx]`, state unchanged.
• **Points, cache miss**: converts to `Polys` via Lagrange interpolation, then evaluates.

Composes `point_at_loop.loop_spec` and `Poly.compute_at_spec`. -/
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
