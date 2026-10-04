/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Oliver Butterley
-/
import SrcTranslated.Funs
import Spqr.Crypto.Hkdf

/-!
# Spec axiom for `spqr::kdf::hkdf_to_slice`

`hkdf_to_slice` fills its output buffer with HKDF-SHA256 output keying material.

Source: "spqr/src/kdf.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace spqr.kdf
open crypto

/-- **Spec axiom for `spqr::kdf::hkdf_to_slice`**
• The function implements RFC 5869 HKDF-SHA256.
• The bound `okm.length ≤ 255 * 32` is the RFC's bound on `L`; every call site is well within it. -/
@[step]
axiom hkdf_to_slice_spec (salt ikm info okm : Slice U8) (h : okm.length ≤ 255 * 32) :
    hkdf_to_slice salt ikm info okm ⦃ (out : Slice U8) =>
      out.val = hkdf salt.val ikm.val info.val okm.length ⦄

end spqr.kdf
