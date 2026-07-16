/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Oliver Butterley
-/
import SrcTranslated.Funs

/-!
# `@[step]` specs for array/slice operations (staged for upstream to Aeneas)

* `core.array.Array.as_slice` — viewing a fixed-size array as a slice preserves the elements.
* the *free* `<[T]>::concat` — flattening a slice of slices. The instance method already has
  `Slice.Insts.AllocSliceConcatTVec.concat_shared_id_spec`, but `step` looks up specs on the free
  function `alloc.slice.Slice.concat` (it does not pre-normalize the head via `concat_eq`), so we
  give the free function its own `@[step]` spec delegating to the instance one. (This one references
  the `spqr`-generated `AllocSliceConcatTVec` instance, so it is spqr glue rather than pure Aeneas.)
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP spqr

@[step]
theorem _root_.core.array.Array.as_slice_spec {T : Type} {N : Usize} (a : Array T N) :
    core.array.Array.as_slice a ⦃ (s : Slice T) => s.val = a.val ⦄ := by
  simp [core.array.Array.as_slice, WP.spec_ok]

@[step]
theorem _root_.alloc.slice.Slice.concat_shared_id_spec {T : Type}
    (cloneInst : core.clone.Clone T) (hclone : ∀ x, cloneInst.clone x = ok x)
    (sv : Slice (Slice T))
    (hlen : (sv.val.map (·.val)).flatten.length ≤ Usize.max) :
    alloc.slice.Slice.concat
        (Slice.Insts.AllocSliceConcatTVec cloneInst
          { borrow := Shared0T.Insts.CoreBorrowBorrow.borrow }) sv
      ⦃ (v : alloc.vec.Vec T) => v.val = (sv.val.map (·.val)).flatten ⦄ := by
  simp only [alloc.slice.Slice.concat_eq]
  exact Slice.Insts.AllocSliceConcatTVec.concat_shared_id_spec cloneInst hclone sv hlen
