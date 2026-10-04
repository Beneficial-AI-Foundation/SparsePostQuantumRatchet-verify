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

/-- **Spec theorem for `spqr::authenticator::Authenticator::verify_ct`**
• Given the boundedness hypotheses and `expected_mac.length = MACSIZE`, the call does not panic.
• The result is `Ok ()` exactly when `expected_mac` equals the `mac_ct` output.
-/
@[step]
theorem verify_ct_spec (self : Authenticator) (ep : U64) (ct : Slice U8) (expected_mac : Slice U8)
    (h_key : self.mac_key.length ≤ U32.max) (h_data : ct.length + 43 ≤ U32.max)
    (h_mac : expected_mac.length = MACSIZE.val) :
    verify_ct self ep ct expected_mac ⦃ (result : core.result.Result Unit Error) =>
      result = Ok () ↔ mac_ct self ep ct = ok expected_mac ⦄ := by
  unfold verify_ct
  have hmac := refl_of% mac_ct_spec
  step*
  · grind
  · simp only [true_iff, *]
    exact congrArg ok (Subtype.ext (List.ext_getElem! (by simp [*]) (by grind)))

end spqr.authenticator.Authenticator
