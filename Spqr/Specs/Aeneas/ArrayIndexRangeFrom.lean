/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs

/-!
# Spec theorem for array indexing with `RangeFrom` (`a[start..]`)

Indexing a fixed-size array `a : Array T N` with `start..` returns a slice containing
the elements from index `start` to the end of the array.

**Source**: core/src/slice/index.rs (`SliceIndex<RangeFrom<usize>, [T]>`)
-/

open Aeneas Aeneas.Std Result

namespace Aeneas.Std

/-- **Spec theorem for `Array.index` with `RangeFrom`**:

When `r.start ≤ N`, indexing `a[r.start..]` succeeds and returns a slice whose
value is `a.val.drop r.start` and whose length is `N - r.start`.
-/
@[step]
theorem Array.index_SliceIndexRangeFromUsizeSlice.step {T : Type} {N : Usize}
    (a : Array T N) (r : core.ops.range.RangeFrom Usize)
    (h : r.start ≤ N) :
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeFromUsizeSlice T)) a r
    ⦃ (s : Slice T) =>
      s.val = a.val.drop r.start ∧
      s.length = N.val - r.start.val ⦄ := by
  simp only [Array.index_SliceIndexRangeFromUsizeSlice]
  have hts : a.to_slice.length = N := by simp [Array.to_slice, Slice.length]
  have h1 := core.slice.index.SliceIndexRangeFromUsizeSlice.index.step_spec
    r a.to_slice (by scalar_tac)
  simp only [Array.to_slice] at h1 ⊢
  exact WP.spec_mono h1 (by intro s ⟨hv, hl⟩; exact ⟨hv, by scalar_tac⟩)

end Aeneas.Std
