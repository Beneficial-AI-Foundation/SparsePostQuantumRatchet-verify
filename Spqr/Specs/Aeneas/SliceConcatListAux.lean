/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs

/-!
# `@[step]` spec theorem for `Slice.concatListAux`

`Slice.concatListAux` is a recursive helper that borrows each element of a list to a `Slice T`,
clones the slice elements, and concatenates all results into a single flat `List T`.

When `Clone` is the identity (`hclone`) and `Borrow` is the shared-reference identity borrow,
the function simply flattens a `List (Slice T)` by extracting and concatenating the `.val` fields.
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP spqr

/-- **Spec theorem for `Slice.concatListAux`**: when `Clone` is the identity and `Borrow` is the
shared-reference identity borrow, `concatListAux` produces the flattened concatenation of the
underlying lists. -/
@[simp]
theorem Slice.concatListAux_shared_id_spec {T : Type}
    (cloneInst : core.clone.Clone T) (hclone : ∀ x, cloneInst.clone x = ok x)
    (l : List (Slice T)) :
    Slice.concatListAux cloneInst
        { borrow := Shared0T.Insts.CoreBorrowBorrow.borrow } l =
      ok ((l.map (·.val)).flatten) := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨_, heq, rfl⟩ :=
      WP.spec_imp_exists (Slice.clone_spec (s := hd) fun _ _ => hclone _)
    simp [Slice.concatListAux, Shared0T.Insts.CoreBorrowBorrow.borrow, heq, ih]
