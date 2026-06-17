/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Markus Dablander
-/
import SrcTranslated.Funs
import Spqr.Specs.Authenticator.Authenticator.MACSIZE

/-!
# Spec theorem for `spqr::authenticator::Authenticator::mac_ct`

`mac_ct` produces an authentication tag that lets the receiver verify a
ciphertext came from the legitimate sender and wasn't altered.

The tag is computed by feeding three concatenated inputs into HMAC-SHA256 under
a shared secret key:

1. A fixed label identifying the tag's purpose (preventing confusion with tags
   used elsewhere in the protocol).
2. The current epoch counter.
3. The ciphertext.

The output is a 32-byte tag.

**Source:** "spqr/src/authenticator.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace spqr.authenticator.Authenticator

/-- **Spec theorem for `spqr::authenticator::Authenticator::mac_ct`**
• The call always succeeds (no panic).
• The returned tag has length `MACSIZE` (= 32 bytes).
-/
@[step]
theorem mac_ct_spec (self : Authenticator) (ep : U64)
    (ct : Slice U8) :
    mac_ct self ep ct ⦃ (result : alloc.vec.Vec U8) =>
      result.length = MACSIZE.val ⦄ := by
  sorry

end spqr.authenticator.Authenticator
