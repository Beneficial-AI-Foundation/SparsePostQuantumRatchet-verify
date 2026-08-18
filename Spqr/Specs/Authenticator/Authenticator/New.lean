/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Oliver Butterley
-/
import SrcTranslated.Funs
import Spqr.Specs.Authenticator.Authenticator.Update

/-!
# Spec theorem for `spqr::authenticator::Authenticator::new`

`new` zero-initialises an `Authenticator` and immediately calls `update` with `root_key`.

Source: "spqr/src/authenticator.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace spqr.authenticator.Authenticator

open List core.num.U64 in
/-- **Spec theorem for `spqr::authenticator::Authenticator::new`**
• Requires that `root_key` prefixed by 32 bytes fits in memory.
• Both keys are 32 bytes.
• They are the halves of the 64-byte HKDF-SHA256 output keyed on `root_key` prefixed by the 32
  zero bytes of the empty initial state. -/
@[step]
theorem new_spec (root_key : alloc.vec.Vec U8) (ep : U64)
    (h : root_key.length + 32 ≤ Usize.max) :
    new root_key ep ⦃ (result : Authenticator) =>
      result.root_key.length = 32 ∧
      result.mac_key.length = 32 ∧
      result.root_key.val ++ result.mac_key.val
        = hkdf (replicate 32 0#u8) (replicate 32 0#u8 ++ root_key.val)
          (updateLabel ++ to_be_bytes ep) 64 ⦄ := by
  unfold new
  step*
  simp_all

end spqr.authenticator.Authenticator
