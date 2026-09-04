/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs

/-!
# Spec theorem for `alloc.vec.Vec.deref_mut`

`alloc.vec.Vec.deref_mut` returns the vector's elements as a mutable slice together with
a back-function that reconstructs a vector from the updated slice.  In Aeneas the
operation is a no-op identity on the underlying list.
-/

open Aeneas Aeneas.Std Result

namespace Aeneas.Std.alloc.vec.Vec

/-- **Spec theorem for `alloc.vec.Vec.deref_mut`**:

Always succeeds, returning a slice whose elements equal the vector's elements and a
back-function that rebuilds the vector from any slice of valid length. -/
@[step]
theorem deref_mut_spec {T : Type} (v : alloc.vec.Vec T) :
    core.ops.deref.DerefMutVec.deref_mut v
    ⦃ (r : Slice T × (Slice T → alloc.vec.Vec T)) =>
      r.1.val = v.val ∧
      ∀ (s : Slice T), (r.2 s).val = s.val ⦄ := by
  unfold core.ops.deref.DerefMutVec
    alloc.vec.Vec.deref_mut
  simp [WP.spec_ok]

end Aeneas.Std.alloc.vec.Vec
