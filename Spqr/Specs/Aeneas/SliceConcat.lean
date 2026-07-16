/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Oliver Butterley
-/
import SrcTranslated.Funs

/-!
# `@[step]` spec for the free `<[T]>::concat`

`step` looks up specs on the free function `alloc.slice.Slice.concat` (it does not pre-normalize the
head via `concat_eq`), so we give it its own spec delegating to the instance spec
`Slice.Insts.AllocSliceConcatTVec.concat_shared_id_spec` in `FunsExternal`.

This is spqr glue rather than upstream-bound Aeneas: it is stated over the `spqr`-generated
`AllocSliceConcatTVec` instance and the hand-filled `FunsExternal` concat model, so it lives here
and not under `Auxiliary/Aeneas/`.
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP spqr

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
