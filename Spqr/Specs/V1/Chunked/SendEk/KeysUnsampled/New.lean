/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import Spqr.Specs.V1.Unchunked.SendEk.KeysUnsampled.New
/-!
# Spec theorem for `spqr::v1::chunked::send_ek::{KeysUnsampled}::new`

`KeysUnsampled::new` builds the initial A→B state of the chunked V1 ratchet. It is a thin
wrapper: it calls `unchunked::KeysUnsampled::new(auth_key)` and stores the result in `uc`, so
the postcondition (epoch `1`, two 32-byte keys equal to the `hkdf` derivation from the zero
root key and `auth_key`) and the precondition `auth_key.length + 32 ≤ Usize.max` are inherited
from the unchunked spec.

**Source**: spqr/src/v1/chunked/send_ek.rs (lines 53:4-57:5)
-/

@[expose] public section

open Aeneas Aeneas.Std Result spqr crypto

namespace spqr.v1.chunked.send_ek.KeysUnsampled

open List core.num.U64 authenticator.Authenticator in
/-- **Spec theorem for `spqr.v1.chunked.send_ek.KeysUnsampled.new`**:

• Calls `unchunked.send_ek.KeysUnsampled.new auth_key` and returns `{ uc := ku }`.
• Requires `auth_key.length + 32 ≤ Usize.max`; under this the call never panics.
• Postcondition: `result.uc.epoch = 1`, both authenticator keys have length `32`, and
  `root_key.val ++ mac_key.val = hkdf (replicate 32 0#u8) (replicate 32 0#u8 ++ auth_key.val)
  (updateLabel ++ to_be_bytes 1#u64) 64`. -/
@[step]
theorem new_spec (auth_key : Slice U8)
    (h : auth_key.length + 32 ≤ Usize.max) :
    new auth_key ⦃ (result : KeysUnsampled) =>
      result.uc.epoch = 1#u64 ∧
      result.uc.auth.root_key.length = 32 ∧
      result.uc.auth.mac_key.length = 32 ∧
      result.uc.auth.root_key.val ++ result.uc.auth.mac_key.val
        = hkdf (replicate 32 0#u8) (replicate 32 0#u8 ++ auth_key.val)
          (updateLabel ++ to_be_bytes 1#u64) 64 ⦄ := by
  unfold new
  step*

end spqr.v1.chunked.send_ek.KeysUnsampled
