/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Liao Zhang
-/
import SrcTranslated.Funs

/-!
# Spec theorems for `alloc::vec::{impl Clone for Vec<T>}::clone`

`alloc.vec.CloneVec.clone` is elementwise `Slice.clone`; whenever the element `Clone`
instance is the identity (e.g. `U8`), cloning a vector succeeds and returns the vector
unchanged.  Lifts the Aeneas standard-library `Slice.clone_spec` to `Vec`.
-/

open Aeneas Aeneas.Std Result

namespace Aeneas.Std.alloc.vec.CloneVec

/-- **Spec theorem for `alloc.vec.CloneVec.clone`** (generic):

If the element `Clone` instance is the identity on every element of `v`, cloning the
vector succeeds and returns `v` unchanged. -/
theorem clone_spec {T : Type} (cloneInst : core.clone.Clone T) (v : alloc.vec.Vec T)
    (h : ∀ x ∈ v.val, cloneInst.clone x = ok x) :
    alloc.vec.CloneVec.clone cloneInst v ⦃ (r : alloc.vec.Vec T) => r = v ⦄ := by
  unfold alloc.vec.CloneVec.clone
  apply WP.spec_mono (Slice.clone_spec h)
  intro v' h'
  exact h'.symm

/-- **Spec theorem for `alloc.vec.CloneVec.clone` specialised to `U8`**:

`CloneU8.clone` is the identity, so cloning a byte vector returns it unchanged. -/
@[step]
theorem clone_U8_spec (v : alloc.vec.Vec U8) :
    alloc.vec.CloneVec.clone core.clone.CloneU8 v ⦃ (r : alloc.vec.Vec U8) => r = v ⦄ :=
  clone_spec core.clone.CloneU8 v (fun _ _ => rfl)

end Aeneas.Std.alloc.vec.CloneVec
