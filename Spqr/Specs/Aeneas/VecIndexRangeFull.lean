/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs

/-! # Spec theorem for `alloc.vec.Vec.index` with `RangeFull`

`Vec.index` with `..` returns the full vector as a slice (identity in Aeneas). -/

open Aeneas Aeneas.Std Result spqr

/-- **Spec theorem for `alloc.vec.Vec.index` with `RangeFull`**:
always succeeds, returning the vector's elements. -/
@[step]
theorem alloc.vec.Vec.index_RangeFull_spec {T : Type} (v : alloc.vec.Vec T) :
    alloc.vec.Vec.index
      (core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice T) v ()
    ⦃ (s : Slice T) => s.val = v.val ⦄ := by
  unfold alloc.vec.Vec.index
    core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice
    core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index
  simp [WP.spec_ok]
