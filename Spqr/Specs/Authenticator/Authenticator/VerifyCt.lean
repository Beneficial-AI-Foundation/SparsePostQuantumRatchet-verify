/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Oliver Butterley
-/
import SrcTranslated.Funs
import Spqr.Specs.Authenticator.Authenticator.MacCt
import Spqr.Specs.Util.Compare
import Spqr.Auxiliary.Aeneas.Vec

/-!
# Spec theorem for `spqr::authenticator::Authenticator::verify_ct`

`verify_ct` recomputes the expected ciphertext authentication tag via `mac_ct` and checks it
against `expected_mac` using a constant-time byte comparison.

Source: "spqr/src/authenticator.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace spqr.authenticator.Authenticator
open core.result.Result (Ok)

/-- `mac_ct_spec`, strengthened with the defining `… = ok r` equation. Registered as a
file-local `step` lemma. -/
private theorem mac_ct_spec_refl : type_of% (refl_of% mac_ct_spec) :=
  refl_of% mac_ct_spec

attribute [local step] mac_ct_spec_refl
attribute [-step] mac_ct_spec

/-- **Spec theorem for `spqr::authenticator::Authenticator::verify_ct`**
• Given the boundedness hypotheses and `expected_mac.length = MACSIZE`, the call does not panic.
• The result is `Ok ()` exactly when `expected_mac` equals the `mac_ct` output.
-/
@[step]
theorem verify_ct_spec (self : Authenticator) (ep : U64) (ct : Slice U8) (expected_mac : Slice U8)
    (h_key : self.mac_key.length ≤ U32.max) (h_data : ct.length + 43 ≤ U32.max)
    (h_mac : expected_mac.length = MACSIZE.val) :
    verify_ct self ep ct expected_mac ⦃ (result : core.result.Result Unit Error) =>
      result = Ok () ↔ mac_ct self ep ct = ok { slice := expected_mac } ⦄ := by
  unfold verify_ct
  step*
  · simp only [reduceCtorEq, false_iff, ‹mac_ct self ep ct = ok _›, Result.ok.injEq]
    rintro rfl
    simp_all only [alloc.vec.Vec.length, alloc.vec.Vec.val, Slice.length, MACSIZE_spec,
      bne_iff_ne, ne_eq, UScalar.neq_to_neq_val, getElem!_pos, alloc.vec.Vec.deref_val,
      implies_true, ↓reduceIte, UScalar.ofNatCore_val_eq, not_true_eq_false]
  · simp only [true_iff, ‹mac_ct self ep ct = ok _›, Result.ok.injEq]
    have hall : ∀ j < expected_mac.length, expected_mac.val[j]! = v.val[j]! := by
      by_contra
      simp_all only [alloc.vec.Vec.length, Slice.length, MACSIZE_spec, getElem!_pos,
        alloc.vec.Vec.deref_val, bne_iff_ne, ne_eq, UScalar.neq_to_neq_val,
        UScalar.ofNatCore_val_eq, ite_eq_left_iff, not_forall, one_ne_zero, imp_false,
        not_exists, Decidable.not_not, not_true_eq_false, exists_false]
    apply alloc.vec.Vec.ext
    refine List.ext_getElem! (by simp_all only [alloc.vec.Vec.length, alloc.vec.Vec.val,
      Slice.length, MACSIZE_spec]) fun j => ?_
    by_cases j < expected_mac.length
    · simp_all only [alloc.vec.Vec.val]
    · simp_all only [alloc.vec.Vec.length, alloc.vec.Vec.val, Slice.length, MACSIZE_spec,
        not_lt, getElem!_neg]

end spqr.authenticator.Authenticator
