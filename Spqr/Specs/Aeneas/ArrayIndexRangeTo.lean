/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs

/-!
# Spec theorem for array indexing with `RangeTo` (`a[..end]`)

Indexing a fixed-size array `a : Array T N` with `..end` returns a slice containing
the first `end` elements of the array.

**Source**: core/src/slice/index.rs (`SliceIndex<RangeTo<usize>, [T]>`)
-/

open Aeneas Aeneas.Std Result

namespace Aeneas.Std

/-- **Spec theorem for `Array.index` with `RangeTo`**:

When `r.end ≤ N`, indexing `a[..r.end]` succeeds and returns a slice whose
value is `a.val.slice 0 r.end` and whose length is `r.end`.
-/
@[step]
theorem Array.index_SliceIndexRangeToUsizeSlice.step {T : Type} {N : Usize}
    (a : Array T N) (r : core.ops.range.RangeTo Usize)
    (h : r.end ≤ N) :
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice T)) a r
    ⦃ (s : Slice T) =>
      s.val = a.val.slice 0 r.end ∧
      s.length = r.end ⦄ := by
  simp only [Array.index_SliceIndexRangeToUsizeSlice]
  have hts : a.to_slice.length = N := by simp [Array.to_slice, Slice.length]
  have := core.slice.index.SliceIndexRangeToUsizeSlice.index.step_spec r a.to_slice (by scalar_tac)
  simp only [Array.to_slice] at this ⊢
  exact this

end Aeneas.Std
