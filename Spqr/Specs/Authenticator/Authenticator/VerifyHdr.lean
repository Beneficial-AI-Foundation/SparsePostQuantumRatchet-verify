/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Oliver Butterley
-/
import SrcTranslated.Funs
import Spqr.Specs.Authenticator.Authenticator.MacHdr
import Spqr.Specs.Util.Compare
import Spqr.Auxiliary.Aeneas.Vec

/-! # Spec theorem for `spqr::authenticator::Authenticator::verify_hdr`

`verify_hdr` recomputes the expected header authentication tag via `mac_hdr` and checks it
against `expected_mac` using a constant-time byte comparison.

Source: "spqr/src/authenticator.rs" -/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace spqr.authenticator.Authenticator
open core.result.Result (Ok)

/-- Spec theorem for `spqr::authenticator::Authenticator::verify_hdr`. Requires several boundedness
hypotheses. Returns `Ok` iff `expected_mac` is byte-for-byte equal to the `mac_hdr` output. -/
@[step]
theorem verify_hdr_spec (self : Authenticator) (ep : U64) (hdr : Slice U8) (expected_mac : Slice U8)
    (h_key : self.mac_key.length ≤ U32.max) (h_data : hdr.length + 41 ≤ U32.max)
    (h_mac : expected_mac.length = MACSIZE.val) :
    verify_hdr self ep hdr expected_mac ⦃ (result : core.result.Result Unit Error) =>
      result = Ok () ↔ mac_hdr self ep hdr = ok expected_mac ⦄ := by
  unfold verify_hdr
  have hmac := refl_of% mac_hdr_spec
  step*
  · grind
  · simp only [true_iff, *]
    exact congrArg ok (Subtype.ext (List.ext_getElem! (by simp [*]) (by grind)))

end spqr.authenticator.Authenticator
