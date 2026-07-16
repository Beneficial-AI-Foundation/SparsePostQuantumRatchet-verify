/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Oliver Butterley
-/
import Aeneas

/-!
# `@[step]` spec for `core::array::[T; N]::as_slice` (staged for upstream to Aeneas)

Viewing a fixed-size array as a slice preserves the underlying elements. Depends only on Aeneas
(`core.array.Array.as_slice` lives in `Std/Array/ArraySlice.lean`).
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

@[step]
theorem _root_.core.array.Array.as_slice_spec {T : Type} {N : Usize} (a : Array T N) :
    core.array.Array.as_slice a ⦃ (s : Slice T) => s.val = a.val ⦄ := by
  simp [core.array.Array.as_slice, WP.spec_ok]
