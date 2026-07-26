/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs

/-!# Spec theorem for `core::slice::{[@T]}::iter`

Rust's `core::slice::{[@T]}::iter` creates an immutable iterator over `&[T]`.
The Aeneas-extracted `core.slice.Slice.iter` pairs the input slice with index
`0`, i.e. `ok ⟨s, 0⟩`. It never panics.

**Postcondition**: `result.slice = s ∧ result.i = 0` -/

open Aeneas Aeneas.Std Result

namespace Aeneas.Std.core.slice.Slice

/-- **Spec theorem for `core.slice.Slice.iter`**:

Always succeeds, returning an `Iter T` with `result.slice = s` and
`result.i = 0`. Proved by unfolding and `step*`. -/
@[step]
theorem iter_spec {T : Type} (s : Slice T) :
    core.slice.Slice.iter s ⦃ (result : core.slice.iter.Iter T) =>
      result.slice = s ∧ result.i = 0 ⦄ := by
  unfold core.slice.Slice.iter
  step*

end Aeneas.Std.core.slice.Slice
