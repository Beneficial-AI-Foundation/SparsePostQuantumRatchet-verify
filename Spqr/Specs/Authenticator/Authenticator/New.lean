/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Oliver Butterley
-/
module

public import SrcTranslated.Funs
public import Spqr.Specs.Authenticator.Authenticator.Update
import Spqr.Specs.Aeneas.SliceConcat
import Spqr.Specs.Kdf.HkdfToVec
import Spqr.Auxiliary.Aeneas.SpecImpExists

/-!
# Spec theorem for `spqr::authenticator::Authenticator::new`

`new` zero-initialises an `Authenticator` and immediately calls `update` with `root_key`.

Source: "spqr/src/authenticator.rs"
-/

@[expose] public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace spqr.authenticator.Authenticator
open crypto

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

/-- A successful `new` returns a 32-byte MAC key. -/
theorem mac_key_length_of_new_ok {v : alloc.vec.Vec U8} {ep : U64} {a : Authenticator}
    (h : new v ep = ok a) : a.mac_key.length = 32 := by
  simp only [new, Result.bind_eq_ok] at h
  obtain ⟨z, -, hu⟩ := h
  exact (WP.post_of_ok (update_spec _ _ _ (length_le_of_update_ok hu)) hu).2.1

end spqr.authenticator.Authenticator
