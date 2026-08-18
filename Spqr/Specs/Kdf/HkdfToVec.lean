/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Oliver Butterley
-/
import SrcTranslated.Funs
import Spqr.Auxiliary.Aeneas.Slice
import Spqr.Auxiliary.Aeneas.Vec
import Spqr.Specs.Kdf.HkdfToSlice

/-!
# Spec theorem for `spqr::kdf::hkdf_to_vec`

`hkdf_to_vec` allocates a zero-filled buffer of length `okm_len`, fills it in-place via
`hkdf_to_slice`, and returns it as a `Vec`.

Source: "spqr/src/kdf.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace spqr.kdf

attribute [step_simps] alloc.vec.Vec.deref_mut lift in
/-- **Spec theorem for `spqr::kdf::hkdf_to_vec`**
• Given `okm_len.val ≤ 255 * 32`, the call does not panic.
• The returned `Vec U8` is the `okm_len`-byte HKDF-SHA256 output, and has length `okm_len`.
-/
@[step]
theorem hkdf_to_vec_spec (salt ikm info : Slice U8) (okm_len : Usize) (h : okm_len.val ≤ 255 * 32) :
    hkdf_to_vec salt ikm info okm_len ⦃ (v : alloc.vec.Vec U8) =>
      v.val = hkdf salt.val ikm.val info.val okm_len.val ∧ v.length = okm_len.val ⦄ := by
  unfold hkdf_to_vec
  step*
  simp_all [Slice.length]

end spqr.kdf
