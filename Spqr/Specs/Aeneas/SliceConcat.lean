/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Oliver Butterley
-/
module

public import SrcTranslated.Funs
import Spqr.Specs.Aeneas.SliceConcatListAux
import Spqr.Specs.Aeneas.SliceListToVec

/-!
# `@[step]` spec for the the standalone `alloc.slice.Slice.concat` function

Eventually this will be upstreamed to Aeneas but only after the `Slice.concat` models have been
upstreamed.
-/

@[expose] public section

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

/-- A successful `concat` with an identity `clone` returns the concatenation. -/
theorem _root_.alloc.slice.Slice.concat_shared_id_ok_val {T : Type}
    (cloneInst : core.clone.Clone T) (hclone : ∀ x, cloneInst.clone x = ok x)
    {sv : Slice (Slice T)} {v : alloc.vec.Vec T}
    (h : alloc.slice.Slice.concat (Slice.Insts.AllocSliceConcatTVec cloneInst
          { borrow := Shared0T.Insts.CoreBorrowBorrow.borrow }) sv = ok v) :
    v.val = (sv.val.map (·.val)).flatten := by
  simp only [alloc.slice.Slice.concat_eq, Slice.Insts.AllocSliceConcatTVec.concat_eq,
    Slice.concatListAux_shared_id_spec cloneInst hclone, bind_ok] at h
  exact Slice.listToVec_ok_val h
