/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Oliver Butterley
-/
import SrcTranslated.Funs
import Spqr.Specs.Authenticator.Authenticator.Update

/-!
# Spec theorem for `spqr::authenticator::Authenticator::new`

`new` initialises an `Authenticator` with all-zero key material and immediately calls `update`
with the provided `root_key` and epoch.  The effect is a single HKDF derivation whose IKM is
`zeros_32 ++ root_key`: the 32 leading zeros represent the empty initial state.

**Source:** "spqr/src/authenticator.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace spqr.authenticator.Authenticator

open List core.num.U64 in
/-- **Spec theorem for `spqr::authenticator::Authenticator::new`**
• Given `root_key.length + 32 ≤ Usize.max`, the call does not panic.
• The result is the same as calling `update` on a zero-initialised authenticator with `root_key`.
• Concretely, the keys are the first and second 32 bytes of HKDF output keyed on
  `zeros_32 ++ root_key`.
-/
@[step]
theorem new_spec (root_key : alloc.vec.Vec U8) (ep : U64)
    (h : root_key.length + 32 ≤ Usize.max) :
    new root_key ep ⦃ result =>
      ∃ kdf_out : alloc.vec.Vec U8,
        kdf.hkdf_to_vec
            (Slice.make (List.replicate 32 0))
            (Slice.make (List.replicate 32 0 ++ root_key.val))
            (Slice.make (UPDATE_LABEL ++ to_be_bytes ep))
            64#usize = ok kdf_out ∧
        kdf_out.length = 64 ∧
        result.root_key.val = kdf_out.val.take 32 ∧
        result.mac_key.val = kdf_out.val.drop 32 ⦄ := by
  unfold new
  step*
  sorry

end spqr.authenticator.Authenticator
