/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Cline
-/
import SrcTranslated.Funs

/-!
# Spec theorem for `Slice.listToVec`

`Slice.listToVec` packages a `List T` as a `Vec T`, succeeding exactly when the list
length fits within `Usize.max`.
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace Aeneas.Std.Slice

/-- **Spec theorem for `Slice.listToVec`**:

If the list length is at most `Usize.max`, then `listToVec` succeeds and returns a
`Vec` whose underlying list is the original list. -/
@[step]
theorem listToVec_spec {T : Type} (l : List T)
    (hlen : l.length ≤ Usize.max) :
    Slice.listToVec l ⦃ (v : alloc.vec.Vec T) => v.val = l ⦄ := by
  simp [Slice.listToVec, dif_pos hlen, spec_ok]

end Aeneas.Std.Slice
