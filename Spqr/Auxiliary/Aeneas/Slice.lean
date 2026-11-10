/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Oliver Butterley
-/
module

public import Aeneas
import Spqr.Auxiliary.Aeneas.SpecImpExists

/-! # Staged for upstream to Aeneas `Std/Slice.lean` -/

@[expose] public section

open Aeneas Aeneas.Std

/-- The empty slice, e.g. to index a list of slices (such as the chunks of a `ChunksExact`
iterator) with `[k]!`. -/
noncomputable instance Aeneas.Std.Slice.instInhabited {α : Type} : Inhabited (Slice α) :=
  ⟨Slice.from [] (by simp)⟩

namespace Aeneas.Std.Slice

open Result

/-- A successful `s[i..]` returns the elements of `s` from index `i` on. -/
theorem index_range_from_ok_val {α : Type} {s s1 : Slice α} {i : Usize}
    (h : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice α) s
      { start := i } = ok s1) : s1.val = s.val.drop i.val := by
  simp only [Slice.index_SliceIndexRangeFromUsizeSliceInst,
    core.slice.index.SliceIndexRangeFromUsizeSlice.index] at h
  split at h
  · simp only [ok.injEq] at h; subst h; exact Slice.from_val _ _
  · exact absurd h fail_not_ok

/-- A successful `s[..i]` returns the first `i` elements of `s`. -/
theorem index_range_to_ok_val {α : Type} {s s1 : Slice α} {i : Usize}
    (h : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice α) s
      { «end» := i } = ok s1) : s1.val = s.val.take i.val := by
  simp only [Slice.index_SliceIndexRangeToUsizeSliceInst,
    core.slice.index.SliceIndexRangeToUsizeSlice.index] at h
  split at h
  · simp only [ok.injEq] at h; subst h; simp [List.slice]
  · exact absurd h fail_not_ok

/-- A successful `to_vec` of a byte slice returns its elements. -/
theorem to_vec_U8_ok_val {s : Slice U8} {v : alloc.vec.Vec U8}
    (h : alloc.slice.Slice.to_vec core.clone.CloneU8 s = ok v) : v.val = s.val := by
  obtain ⟨w, hw, hp⟩ := WP.spec_imp_exists
    (alloc.slice.Slice.to_vec_spec core.clone.CloneU8 s (fun _ _ => rfl))
  rw [hw, ok.injEq] at h; subst h; rw [hp]; rfl

end Aeneas.Std.Slice
