/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Encoding.Polynomial.ConstPolysToPolys.CallMut
import Spqr.Specs.Aeneas.MapIteratorTransformerNext
import Spqr.Specs.Encoding.Polynomial.ConstPolysToPolys.MapCollect

/-!
# Spec theorem for `core::iter::adapters::map::{Iterator for Map<I, F>}::collect`

Specialized to the `const_polys_to_polys` pipeline.

**Source**: core/src/iter/adapters/map.rs (lines 99:0-101:27)
-/


open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf Polynomial
open const_polys_to_polys.closure.Insts

namespace Aeneas.Std.core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator

-- Convenient aliases
private abbrev ClosureN (N : Usize) := const_polys_to_polys.closure N
private abbrev MapIterT (N : Usize) :=
  core.iter.adapters.map.Map (core.slice.iter.Iter (PolyConst N)) (ClosureN N)

private lemma spec_to_ok {α : Type} {x : Result α} {p : α → Prop}
    (h : WP.spec x p) : ∃ v, x = .ok v ∧ p v := by
  cases x with
  | ok v => exact ⟨v, rfl, h⟩
  | fail e => exact absurd h id
  | div => exact absurd h id

private lemma to_poly_of_call_mut_eq {N : Usize}
    {c : const_polys_to_polys.closure N} {arg : PolyConst N}
    {result : Poly × const_polys_to_polys.closure N}
    (h : CoreOpsFunctionFnMutTupleSharedPolyConstPoly.call_mut
      c arg = .ok result) :
    arg.to_poly = .ok result.1 := by
  unfold CoreOpsFunctionFnMutTupleSharedPolyConstPoly.call_mut at h
  cases h_tp : arg.to_poly <;> simp_all
  subst h; rfl

/-- Inductive characterisation of `iterToList` applied to the map-of-slice
iterator used in `const_polys_to_polys`. -/
private theorem iterToList_map_acc
    {N : Usize}
    (n : Nat)
    (m : MapIterT N)
    (acc : List Poly)
    (h_n : n = m.iter.slice.val.length - m.iter.i)
    (mapIterInst : core.iter.traits.iterator.Iterator (MapIterT N) Poly)
    (h_next : mapIterInst.next = fun m' => do
      let (opt, iter') ← core.slice.iter.IteratorSliceIter.next m'.iter
      match opt with
      | none =>
        .ok (none,
          (core.iter.adapters.map.Map.mk iter' m'.f : MapIterT N))
      | some item => do
        let (b, f') ←
          const_polys_to_polys.closure.Insts.CoreOpsFunctionFnMutTupleSharedPolyConstPoly.call_mut
            m'.f item
        .ok (some b,
          (core.iter.adapters.map.Map.mk iter' f' : MapIterT N))) :
    ∃ (L : List Poly),
      alloc.vec.FromIteratorVec.iterToList mapIterInst m acc =
        .ok (acc.reverse ++ L) ∧
      L.length = m.iter.slice.val.length - m.iter.i ∧
      (∀ j (hj : j < L.length) (hs : j + m.iter.i < m.iter.slice.val.length),
          (L.get ⟨j, hj⟩).coefficients.val =
            (m.iter.slice.val.get ⟨j + m.iter.i, hs⟩).coefficients.val ∧
          (L.get ⟨j, hj⟩).toGF216Poly =
            listToGF216Poly
              (m.iter.slice.val.get ⟨j + m.iter.i, hs⟩).coefficients.val) := by
  induction n generalizing m acc with
  | zero =>
    have h_ge : ¬ (m.iter.i < m.iter.slice.val.length) := by omega
    refine ⟨[], ?_, by simp; omega, by intro j hj; omega⟩
    conv_lhs => unfold alloc.vec.FromIteratorVec.iterToList
    rw [h_next]
    simp [core.slice.iter.IteratorSliceIter.next, Slice.len, h_ge]
  | succ n ih =>
    have h_lt : m.iter.i < m.iter.slice.val.length := by omega
    have h_cm :=
      const_polys_to_polys.closure.Insts.CoreOpsFunctionFnMutTupleSharedPolyConstPoly.call_mut_spec
        m.f (m.iter.slice.val.get ⟨m.iter.i, h_lt⟩)
    obtain ⟨result_cm, h_cm_eq, h_post⟩ := spec_to_ok h_cm
    obtain ⟨h_coeff, h_poly, h_f⟩ := h_post
    set m' : MapIterT N := core.iter.adapters.map.Map.mk
      (core.slice.iter.Iter.mk m.iter.slice (m.iter.i + 1))
      result_cm.2
    have hm'_slice : m'.iter.slice = m.iter.slice := rfl
    have hm'_i : m'.iter.i = m.iter.i + 1 := rfl
    have h_step : alloc.vec.FromIteratorVec.iterToList mapIterInst m acc =
        alloc.vec.FromIteratorVec.iterToList mapIterInst m'
          (result_cm.1 :: acc) := by
      conv_lhs => unfold alloc.vec.FromIteratorVec.iterToList
      rw [h_next]
      simp only [slice.iter.IteratorSliceIter.next, Slice.len, Usize.ofNatCore_val_eq, h_lt,
        ↓reduceDIte, bind_tc_ok, uncurry_apply_pair, bind_assoc]
      unfold CoreOpsFunctionFnMutTupleSharedPolyConstPoly.call_mut
      simp only [bind_assoc, bind_tc_ok, uncurry_apply_pair]
      rw [← h_f]
      exact to_poly_of_call_mut_eq h_cm_eq ▸ rfl
    have h_n'2 : n = m'.iter.slice.val.length - m'.iter.i := by
      rw [hm'_slice, hm'_i]; omega
    obtain ⟨L', hL'_eq, hL'_len, hL'_elts⟩ :=
      ih m' (result_cm.1 :: acc) h_n'2
    refine ⟨result_cm.1 :: L', ?_, ?_, ?_⟩
    · rw [h_step, hL'_eq]
      simp [List.reverse_cons, List.append_assoc]
    · simp [hL'_len, hm'_slice, hm'_i]; omega
    · intro j hj hs
      cases j with
      | zero =>
        simp only [Nat.zero_add]
        exact ⟨h_coeff, h_poly⟩
      | succ k =>
        have hk : k < L'.length := by
          have : (result_cm.1 :: L').length = L'.length + 1 := rfl
          omega
        have hks : k + m'.iter.i < m'.iter.slice.val.length := by
          rw [hm'_slice, hm'_i]; omega
        obtain ⟨hc, hp⟩ := hL'_elts k hk hks
        simp only [List.get_eq_getElem, hm'_slice] at hc hp
        refine ⟨?_, ?_⟩
        · show ((result_cm.1 :: L').get ⟨k + 1, hj⟩).coefficients.val = _
          have : (result_cm.1 :: L').get ⟨k + 1, hj⟩ = L'.get ⟨k, hk⟩ := by rfl
          rw [this, show m.iter.slice.val.get ⟨k + 1 + m.iter.i, hs⟩ =
            m.iter.slice.val.get ⟨k + m'.iter.i, hks⟩ from by
              congr 1; ext; grind]
          exact hc
        · show ((result_cm.1 :: L').get ⟨k + 1, hj⟩).toGF216Poly = _
          have : (result_cm.1 :: L').get ⟨k + 1, hj⟩ = L'.get ⟨k, hk⟩ := by rfl
          rw [this, show m.iter.slice.val.get ⟨k + 1 + m.iter.i, hs⟩ =
            m.iter.slice.val.get ⟨k + m'.iter.i, hks⟩ from by
              congr 1; ext; grind]
          rw [show (m.iter.slice.val.get ⟨k + m'.iter.i, hks⟩).coefficients.val =
            (m.iter.slice.val.get ⟨k + m'.iter.i, hks⟩).coefficients.val from rfl]
          exact hp


/--
The `iterToList` call with `mapIteratorTransformer` (state `Iter (PolyConst N)`)
produces the same result as with a custom instance (state `MapIterT N`), because
the `const_polys_to_polys` closure state is never modified by `call_mut`.
This bridges the generic `collect_spec` unfolding (which uses `mapIteratorTransformer`)
with the inductive characterisation `iterToList_map_acc` (which uses `MapIterT N` state).
-/
private theorem iterToList_mapTrans_eq_custom
    {N : Usize}
    (n : Nat)
    (iter : core.slice.iter.Iter (PolyConst N))
    (f : ClosureN N)
    (acc : List Poly)
    (h_n : n = iter.slice.val.length - iter.i)
    (customInst : core.iter.traits.iterator.Iterator (MapIterT N) Poly)
    (h_next : customInst.next = fun m' => do
      let (opt, iter') ← core.slice.iter.IteratorSliceIter.next m'.iter
      match opt with
      | none =>
        .ok (none,
          (core.iter.adapters.map.Map.mk iter' m'.f : MapIterT N))
      | some item => do
        let (b, f') ←
          CoreOpsFunctionFnMutTupleSharedPolyConstPoly.call_mut
            m'.f item
        .ok (some b,
          (core.iter.adapters.map.Map.mk iter' f' : MapIterT N))) :
    alloc.vec.FromIteratorVec.iterToList
      (core.iter.adapters.map.mapIteratorTransformer
        (core.iter.adapters.map.Map.mk iter f : MapIterT N)
        (core.iter.traits.iterator.IteratorSliceIter (PolyConst N))
        (CoreOpsFunctionFnMutTupleSharedPolyConstPoly N))
      iter acc =
    alloc.vec.FromIteratorVec.iterToList customInst
      (core.iter.adapters.map.Map.mk iter f : MapIterT N) acc := by
  induction n generalizing iter acc with
  | zero =>
    have h_ge : ¬ (iter.i < iter.slice.val.length) := by omega
    have lhs_val : alloc.vec.FromIteratorVec.iterToList
        (core.iter.adapters.map.mapIteratorTransformer
          (core.iter.adapters.map.Map.mk iter f : MapIterT N)
          (core.iter.traits.iterator.IteratorSliceIter (PolyConst N))
          (CoreOpsFunctionFnMutTupleSharedPolyConstPoly N))
        iter acc = .ok acc.reverse := by
      conv_lhs => unfold alloc.vec.FromIteratorVec.iterToList
      simp [mapIteratorTransformer_next_spec,
        core.slice.iter.IteratorSliceIter.next, Slice.len, h_ge]
    have rhs_val : alloc.vec.FromIteratorVec.iterToList customInst
        (core.iter.adapters.map.Map.mk iter f : MapIterT N) acc =
        .ok acc.reverse := by
      conv_lhs => unfold alloc.vec.FromIteratorVec.iterToList
      rw [h_next]
      simp [core.slice.iter.IteratorSliceIter.next, Slice.len, h_ge]
    rw [lhs_val, rhs_val]
  | succ n ih =>
    have h_lt : iter.i < iter.slice.val.length := by omega
    have h_cm :=
      CoreOpsFunctionFnMutTupleSharedPolyConstPoly.call_mut_spec
        f (iter.slice.val.get ⟨iter.i, h_lt⟩)
    obtain ⟨result, h_cm_eq, _, _, h_f⟩ := spec_to_ok h_cm
    set iter' := core.slice.iter.Iter.mk iter.slice (iter.i + 1)
    have lhs_step : alloc.vec.FromIteratorVec.iterToList
        (core.iter.adapters.map.mapIteratorTransformer
          (core.iter.adapters.map.Map.mk iter f : MapIterT N)
          (core.iter.traits.iterator.IteratorSliceIter (PolyConst N))
          (CoreOpsFunctionFnMutTupleSharedPolyConstPoly N))
        iter acc =
      alloc.vec.FromIteratorVec.iterToList
        (core.iter.adapters.map.mapIteratorTransformer
          (core.iter.adapters.map.Map.mk iter f : MapIterT N)
          (core.iter.traits.iterator.IteratorSliceIter (PolyConst N))
          (CoreOpsFunctionFnMutTupleSharedPolyConstPoly N))
        iter' (result.1 :: acc) := by
      conv_lhs => unfold alloc.vec.FromIteratorVec.iterToList
      simp only [mapIteratorTransformer_next_spec,
        slice.iter.IteratorSliceIter.next, Slice.len, Usize.ofNatCore_val_eq, h_lt,
        ↓reduceDIte, bind_tc_ok, uncurry_apply_pair, bind_assoc]
      unfold CoreOpsFunctionFnMutTupleSharedPolyConstPoly.call_mut
      simp only [bind_assoc, bind_tc_ok, uncurry_apply_pair]
      exact to_poly_of_call_mut_eq h_cm_eq ▸ rfl
    have rhs_step : alloc.vec.FromIteratorVec.iterToList customInst
        (core.iter.adapters.map.Map.mk iter f : MapIterT N) acc =
      alloc.vec.FromIteratorVec.iterToList customInst
        (core.iter.adapters.map.Map.mk iter' result.2 : MapIterT N)
          (result.1 :: acc) := by
      conv_lhs => unfold alloc.vec.FromIteratorVec.iterToList
      rw [h_next]
      simp only [slice.iter.IteratorSliceIter.next, Slice.len, Usize.ofNatCore_val_eq, h_lt,
        ↓reduceDIte, bind_tc_ok, uncurry_apply_pair, bind_assoc]
      unfold CoreOpsFunctionFnMutTupleSharedPolyConstPoly.call_mut
      simp only [bind_assoc, bind_tc_ok, uncurry_apply_pair]
      rw [← h_f]
      exact to_poly_of_call_mut_eq h_cm_eq ▸ rfl
    rw [lhs_step, rhs_step, ← h_f]
    exact ih iter' (result.1 :: acc) (by simp [iter']; omega)

/--
**Spec theorem for `collect`** (specialized to `const_polys_to_polys`).

**Source**: core/src/iter/adapters/map.rs (lines 99:0-101:27)
-/
@[step]
theorem collect_const_polys_spec
    {N : Usize}
    (m : MapIterT N) :
    core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.collect
      (core.iter.traits.iterator.IteratorSliceIter (PolyConst N))
      (const_polys_to_polys.closure.Insts.CoreOpsFunctionFnMutTupleSharedPolyConstPoly
        N) (core.iter.traits.collect.FromIteratorVec Poly) m ⦃ (result : alloc.vec.Vec Poly) =>
      result.val.length = m.iter.slice.val.length - m.iter.i ∧
      (∀ (j : Nat), j + m.iter.i < m.iter.slice.val.length →
        ∀ (hj : j < result.val.length)
          (hs : j + m.iter.i < m.iter.slice.val.length),
          (result.val.get ⟨j, hj⟩).coefficients.val =
            (m.iter.slice.val.get ⟨j + m.iter.i, hs⟩).coefficients.val ∧
          (result.val.get ⟨j, hj⟩).toGF216Poly =
            listToGF216Poly
              (m.iter.slice.val.get ⟨j + m.iter.i, hs⟩).coefficients.val) ⦄ := by
  simp only [core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.collect_spec]
  unfold alloc.vec.FromIteratorVec.from_iter
  simp only [traits.collect.IntoIterator.Blanket.into_iter, bind_tc_ok, List.get_eq_getElem]
  apply WP.spec_bind (Pₘ := fun (L : List Poly) =>
    L.length = m.iter.slice.val.length - m.iter.i ∧
    L.length ≤ Usize.max ∧
    (∀ j (hj : j < L.length) (hs : j + m.iter.i < m.iter.slice.val.length),
        (L.get ⟨j, hj⟩).coefficients.val =
          (m.iter.slice.val.get ⟨j + m.iter.i, hs⟩).coefficients.val ∧
        (L.get ⟨j, hj⟩).toGF216Poly =
          listToGF216Poly
            (m.iter.slice.val.get ⟨j + m.iter.i, hs⟩).coefficients.val))
  · obtain ⟨L, hL_eq, hL_len, hL_elts⟩ := iterToList_map_acc
      (m.iter.slice.val.length - m.iter.i)
      m [] rfl
      { next := fun m => do
          let (opt, iter') ← core.slice.iter.IteratorSliceIter.next m.iter
          match opt with
          | none =>
            .ok (none,
              (core.iter.adapters.map.Map.mk iter' m.f : MapIterT N))
          | some item => do
            let (b, f') ←
              CoreOpsFunctionFnMutTupleSharedPolyConstPoly.call_mut
                m.f item
            .ok (some b,
              (core.iter.adapters.map.Map.mk iter' f' : MapIterT N))
        step_by := fun m s => if s.val = 0 then .fail .panic else .ok ⟨m, s⟩
        enumerate := fun m => .ok ⟨m, 0#usize⟩
        take := fun m n => .ok ⟨m, n⟩ }
      rfl
    simp only [List.reverse_nil, List.nil_append] at hL_eq
    have h_bridge := iterToList_mapTrans_eq_custom
      (m.iter.slice.val.length - m.iter.i) m.iter m.f [] rfl
      { next := fun m => do
          let (opt, iter') ← core.slice.iter.IteratorSliceIter.next m.iter
          match opt with
          | none =>
            .ok (none,
              (core.iter.adapters.map.Map.mk iter' m.f : MapIterT N))
          | some item => do
            let (b, f') ←
              CoreOpsFunctionFnMutTupleSharedPolyConstPoly.call_mut
                m.f item
            .ok (some b,
              (core.iter.adapters.map.Map.mk iter' f' : MapIterT N))
        step_by := fun m s => if s.val = 0 then .fail .panic else .ok ⟨m, s⟩
        enumerate := fun m => .ok ⟨m, 0#usize⟩
        take := fun m n => .ok ⟨m, n⟩ }
      rfl
    rw [h_bridge, hL_eq]
    simp only [WP.spec_ok]
    exact ⟨hL_len, by have := m.iter.slice.property; omega, hL_elts⟩
  · intro list ⟨h_len, h_max, h_elts⟩
    split
    · exact ⟨h_len, fun j hj_bound hj hs => h_elts j (by omega) hs⟩
    · omega

end Aeneas.Std.core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator
