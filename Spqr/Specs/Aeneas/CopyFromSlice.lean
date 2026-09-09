/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs

/-!
# Spec theorem for `core::slice::{[@T]}::copy_from_slice`

`copy_from_slice` overwrites the destination slice with the contents of the source slice,
provided both slices have the same length.  In the Aeneas model the destination is simply
replaced by the source.

**Source**: core/src/slice/mod.rs (`copy_from_slice`)
-/

open Aeneas Aeneas.Std Result

namespace Aeneas.Std.core.slice.Slice

/-- **Spec theorem for `copy_from_slice`**:

When the source and destination slices have the same length, `copy_from_slice`
succeeds and the result equals the source slice (same contents and length).

This wraps the upstream `copy_from_slice.step_spec` with additional content-level
properties for downstream proofs.
-/
@[step]
theorem copy_from_slice_content_spec {T : Type} (copyInst : core.marker.Copy T)
    (dst src : Slice T)
    (h_len : dst.length = src.length) :
    core.slice.Slice.copy_from_slice copyInst dst src ⦃ result =>
      result = src ∧
      result.length = dst.length ∧
      result.val = src.val ⦄ := by
  simp only [copy_from_slice]
  simp only [Slice.len]
  simp at h_len
  simp [h_len, WP.spec_ok]

end Aeneas.Std.core.slice.Slice
