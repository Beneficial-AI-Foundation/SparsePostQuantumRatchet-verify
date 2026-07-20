/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Oliver Butterley
-/
import Aeneas

/-! # Staged for upstream to Aeneas `Std/Array/ArraySlice.lean`. -/
-- https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/305

open Aeneas Aeneas.Std Result Aeneas.Std.WP

@[step]
theorem _root_.core.array.Array.as_slice_spec {T : Type} {N : Usize} (a : Array T N) :
    core.array.Array.as_slice a ⦃ (s : Slice T) => s.val = a.val ⦄ := by
  simp [core.array.Array.as_slice, WP.spec_ok]
