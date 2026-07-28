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

Specialized to the `const_polys_to_polys` pipeline, i.e. `I = slice::Iter<PolyConst<N>>`,
`F` the closure `|x| x.to_poly()`, and the collection target `Vec<Poly>`.

The proof is a single induction on the number of remaining slice elements. `collect_spec`
rewrites `collect` into `FromIteratorVec.from_iter` applied to the iterator produced by
`mapIteratorTransformer`; `iterToList_trans` then characterises the list that
`FromIteratorVec.iterToList` accumulates for that iterator. Note the transformer keeps the
closure value `m.f` fixed across steps, which is faithful here because `call_mut` leaves the
`const_polys_to_polys` closure state unchanged.

**Source**: core/src/iter/adapters/map.rs (lines 99:0-101:27)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf Polynomial
open const_polys_to_polys.closure.Insts

namespace Aeneas.Std.core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator

-- Convenient aliases
private abbrev ClosureN (N : Usize) := const_polys_to_polys.closure N

private abbrev MapIterT (N : Usize) :=
  core.iter.adapters.map.Map (core.slice.iter.Iter (PolyConst N)) (ClosureN N)

/-- The `Poly`-valued iterator that `collect` drives: the slice iterator over `PolyConst N`
transformed by the `const_polys_to_polys` closure. -/
private abbrev transInst {N : Usize} (m : MapIterT N) :
    core.iter.traits.iterator.Iterator (core.slice.iter.Iter (PolyConst N)) Poly :=
  core.iter.adapters.map.mapIteratorTransformer m
    (core.iter.traits.iterator.IteratorSliceIter (PolyConst N))
    (CoreOpsFunctionFnMutTupleSharedPolyConstPoly N)

private lemma spec_to_ok {α : Type} {x : Result α} {p : α → Prop}
    (h : WP.spec x p) : ∃ v, x = .ok v ∧ p v := by
  cases x with
  | ok v => exact ⟨v, rfl, h⟩
  | fail e => exact absurd h id
  | div => exact absurd h id

private lemma to_poly_of_call_mut_eq {N : Usize}
    {c : const_polys_to_polys.closure N} {arg : PolyConst N}
    {result : Poly × const_polys_to_polys.closure N}
    (h : CoreOpsFunctionFnMutTupleSharedPolyConstPoly.call_mut c arg = .ok result) :
    arg.to_poly = .ok result.1 := by
  unfold CoreOpsFunctionFnMutTupleSharedPolyConstPoly.call_mut at h
  cases h_tp : arg.to_poly <;>
    simp_all only [bind_tc_ok, ok.injEq, bind_tc_fail, bind_tc_div, reduceCtorEq]
  subst h; rfl

/-- Inductive characterisation of `iterToList` for the map-of-slice iterator used in
`const_polys_to_polys`: it accumulates, in order, the `to_poly` image of every slice element
from index `iter.i` onwards. -/
private theorem iterToList_trans {N : Usize} (n : Nat) (m : MapIterT N)
    (iter : core.slice.iter.Iter (PolyConst N)) (acc : List Poly)
    (h_n : n = iter.slice.val.length - iter.i) :
    ∃ L : List Poly,
      alloc.vec.FromIteratorVec.iterToList (transInst m) iter acc = .ok (acc.reverse ++ L) ∧
      L.length = iter.slice.val.length - iter.i ∧
      ∀ j (hj : j < L.length) (hs : j + iter.i < iter.slice.val.length),
        (L.get ⟨j, hj⟩).coefficients.val = (iter.slice.val.get ⟨j + iter.i, hs⟩).coefficients.val ∧
        (L.get ⟨j, hj⟩).toGF216Poly =
          listToGF216Poly (iter.slice.val.get ⟨j + iter.i, hs⟩).coefficients.val := by
  induction n generalizing iter acc with
  | zero =>
    have h_ge : ¬ (iter.i < iter.slice.val.length) := by omega
    refine ⟨[], ?_, by omega, by omega⟩
    conv_lhs => unfold alloc.vec.FromIteratorVec.iterToList
    simp only [transInst, mapIteratorTransformer_next_spec, Usize.ofNatCore_val_eq,
      slice.iter.IteratorSliceIter.next, Slice.len, h_ge, dite_false, bind_tc_ok,
      List.append_nil]
    rfl
  | succ n ih =>
    have h_lt : iter.i < iter.slice.val.length := by omega
    obtain ⟨r, h_cm, h_coeff, h_poly, -⟩ := spec_to_ok
      (CoreOpsFunctionFnMutTupleSharedPolyConstPoly.call_mut_spec m.f
        (iter.slice.val.get ⟨iter.i, h_lt⟩))
    -- One iteration: emit `r.1` and advance the slice index by one.
    have h_step : alloc.vec.FromIteratorVec.iterToList (transInst m) iter acc =
        alloc.vec.FromIteratorVec.iterToList (transInst m)
          ⟨iter.slice, iter.i + 1⟩ (r.1 :: acc) := by
      conv_lhs => unfold alloc.vec.FromIteratorVec.iterToList
      simp only [transInst, mapIteratorTransformer_next_spec, Usize.ofNatCore_val_eq,
        slice.iter.IteratorSliceIter.next, Slice.len, h_lt, ↓reduceDIte, bind_tc_ok]
      unfold CoreOpsFunctionFnMutTupleSharedPolyConstPoly.call_mut
      simp only [bind_assoc, bind_tc_ok, uncurry_apply_pair]
      exact to_poly_of_call_mut_eq h_cm ▸ rfl
    obtain ⟨L, hL, hLlen, hLelts⟩ :=
      ih ⟨iter.slice, iter.i + 1⟩ (r.1 :: acc) (by simp only; omega)
    refine ⟨r.1 :: L, ?_, ?_, ?_⟩
    · rw [h_step, hL]
      simp only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]
    · simp only [List.length_cons] at hLlen ⊢
      omega
    · intro j hj hs
      cases j with
      | zero =>
        simpa only [List.length_cons, Fin.zero_eta, List.get_eq_getElem, Fin.coe_ofNat_eq_mod,
          Nat.zero_mod, List.getElem_cons_zero, zero_add] using ⟨h_coeff, h_poly⟩
      | succ k =>
        have hk : k < L.length := by
          simp only [List.length_cons, Order.lt_add_one_iff, Order.add_one_le_iff] at hj ⊢
          omega
        obtain ⟨hc, hp⟩ := hLelts k hk (by simp only; omega)
        have hidx :
            k + 1 + iter.i = k + (⟨iter.slice, iter.i + 1⟩ : core.slice.iter.Iter _).i := by
          simp only
          omega
        simp only [List.get_eq_getElem, List.getElem_cons_succ, hidx] at hc hp ⊢
        exact ⟨hc, hp⟩

/-- **Spec theorem for `collect`** (specialized to `const_polys_to_polys`):

Always succeeds. The resulting `Vec<Poly>` has one entry per not-yet-consumed slice element,
and entry `j` carries exactly the coefficients of slice element `j + m.iter.i`. -/
@[step]
theorem collect_const_polys_spec
    {N : Usize}
    (m : MapIterT N) :
    core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.collect
      (core.iter.traits.iterator.IteratorSliceIter (PolyConst N))
      (const_polys_to_polys.closure.Insts.CoreOpsFunctionFnMutTupleSharedPolyConstPoly N)
      (core.iter.traits.collect.FromIteratorVec Poly) m ⦃ (result : alloc.vec.Vec Poly) =>
      result.val.length = m.iter.slice.val.length - m.iter.i ∧
      (∀ (j : Nat) (hj : j < result.val.length) (hs : j + m.iter.i < m.iter.slice.val.length),
        (result.val.get ⟨j, hj⟩).coefficients.val =
          (m.iter.slice.val.get ⟨j + m.iter.i, hs⟩).coefficients.val ∧
        (result.val.get ⟨j, hj⟩).toGF216Poly =
          listToGF216Poly (m.iter.slice.val.get ⟨j + m.iter.i, hs⟩).coefficients.val) ⦄ := by
  obtain ⟨L, hL, hLlen, hLelts⟩ :=
    iterToList_trans (m.iter.slice.val.length - m.iter.i) m m.iter [] rfl
  simp only [collect_spec]
  unfold alloc.vec.FromIteratorVec.from_iter
  simp only [traits.collect.IntoIterator.Blanket.into_iter, bind_tc_ok, List.reverse_nil,
    List.nil_append] at hL ⊢
  rw [hL]
  have hmax : L.length ≤ Usize.max := by have := m.iter.slice.property; omega
  simp only [bind_tc_ok, hmax, ↓reduceDIte, WP.spec_ok]
  exact ⟨hLlen, hLelts⟩

end Aeneas.Std.core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator
