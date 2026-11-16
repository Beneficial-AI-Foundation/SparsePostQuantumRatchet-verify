/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Lacramioara Astefanoaei
-/
module

public import Aeneas
import Spqr.Auxiliary.Aeneas.Result

/-! # `Enumerate::next` over a slice iterator -/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace Aeneas.Std.core.iter.adapters.enumerate.IteratorEnumerate

/-- A successful `next` on an enumerated slice iterator keeps the slice. It yields an item
exactly when the cursor is inside the slice, and then moves the cursor by one. -/
theorem next_slice_ok {T : Type} {it it' : Enumerate (core.slice.iter.Iter T)}
    {o : Option (Usize × T)}
    (h : next (core.iter.traits.iterator.IteratorSliceIter T) it = ok (o, it')) :
    it'.iter.slice = it.iter.slice ∧
      (o = none → ¬ it.iter.i < it.iter.slice.length) ∧
      (o ≠ none → it.iter.i < it.iter.slice.length ∧ it'.iter.i = it.iter.i + 1) := by
  unfold next at h
  by_cases hlt : it.iter.i < it.iter.slice.len
  · simp only [core.slice.iter.IteratorSliceIter.next,
      dite_eq_left hlt, bind_ok, uncurry_apply_pair, Result.bind_eq_ok] at h
    obtain ⟨c, -, h⟩ := h
    simp only [ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, fun h => absurd h (by simp), fun _ => ⟨by scalar_tac, rfl⟩⟩
  · simp only [core.slice.iter.IteratorSliceIter.next,
      dite_eq_right hlt, bind_ok, uncurry_apply_pair, ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, fun _ => by scalar_tac, fun h => absurd rfl h⟩

end Aeneas.Std.core.iter.adapters.enumerate.IteratorEnumerate
