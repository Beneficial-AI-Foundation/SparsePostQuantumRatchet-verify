/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Oliver Butterley
-/
import SrcTranslated.Funs
import Spqr.Specs.Authenticator.Authenticator.MacHdr
import Spqr.Specs.Util.Compare
import Spqr.Auxiliary.Aeneas.Vec

/-!
# Spec theorem for `spqr::authenticator::Authenticator::verify_hdr`

`verify_hdr` recomputes the expected header authentication tag via `mac_hdr` and checks it
against `expected_mac`.

Source: "spqr/src/authenticator.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace spqr.authenticator.Authenticator
open core.result.Result (Ok)

/-- **Spec theorem for `spqr::authenticator::Authenticator::verify_hdr`**
• Requires the boundedness hypotheses and `expected_mac.length = MACSIZE`.
• The result is `Ok ()` exactly when `expected_mac` equals the `mac_hdr` output. -/
@[step]
theorem verify_hdr_spec (self : Authenticator) (ep : U64) (hdr : Slice U8) (expected_mac : Slice U8)
    (h_key : self.mac_key.length ≤ U32.max) (h_data : hdr.length + 41 ≤ U32.max)
    (h_mac : expected_mac.length = MACSIZE.val) :
    verify_hdr self ep hdr expected_mac ⦃ (result : core.result.Result Unit Error) =>
      result = Ok () ↔ mac_hdr self ep hdr = ok { slice := expected_mac } ⦄ := by
  unfold verify_hdr
  have hmac := refl_of% mac_hdr_spec
  step*
  all_goals clear hmac
  · simp only [reduceCtorEq, false_iff, ‹mac_hdr self ep hdr = ok _›, Result.ok.injEq]
    rintro rfl
    simp_all only [alloc.vec.Vec.length, alloc.vec.Vec.val, Slice.length, MACSIZE_spec,
      bne_iff_ne, ne_eq, UScalar.neq_to_neq_val, getElem!_pos, alloc.vec.Vec.deref_val,
      implies_true, ↓reduceIte, UScalar.ofNatCore_val_eq, not_true_eq_false]
  · simp only [true_iff, ‹mac_hdr self ep hdr = ok _›, Result.ok.injEq]
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
