/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong, Liao Zhang
-/
import SrcTranslated.Funs

/-!
# `simp`/`step_simps` lemma for `RangeFull` indexing of an array

Indexing an array by `..` yields the whole array as a slice.  This is definitional, but
registering it in the `simp` and `step_simps` sets lets `step*` see through the `a[..]` calls
that appear whenever Rust code passes a fixed-size array to a slice-taking function.

The slice-level counterpart (`s[..] = s`) already has a `@[step]` spec in
`SrcTranslated.FunsExternal`.  Both are analogues of the upstream
`Aeneas.Std.Array.index_SliceIndexRangeUsizeSlice` and should eventually be upstreamed to Aeneas.
-/

-- `spqr` is opened for the `RangeFull` `SliceIndex` instance record, which the extraction places
-- in the crate namespace even though its `index` method is at the root.
open Aeneas Aeneas.Std Result spqr

/-- `RangeFull` indexing of an array yields the whole array as a slice: `a[..] = a`. -/
@[simp, step_simps]
theorem Aeneas.Std.Array.index_RangeFull {T : Type} {N : Usize} (a : Array T N) :
    core.array.Array.index
      (core.ops.index.IndexSlice
        (core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice T))
      a () =
    ok a.to_slice :=
  rfl
