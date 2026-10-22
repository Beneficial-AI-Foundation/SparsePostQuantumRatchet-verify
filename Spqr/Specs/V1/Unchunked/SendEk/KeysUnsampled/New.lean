/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import SrcTranslated.Funs
public import Spqr.Specs.Authenticator.Authenticator.New
/-!
# Spec theorem for `spqr::v1::unchunked::send_ek::{KeysUnsampled}::new`

`KeysUnsampled::new` builds the initial state of the A→B (encapsulation-key-sending) side of
the unchunked V1 ratchet, before any ML-KEM key pair is sampled. It holds the epoch (`1`) and
a fresh `Authenticator::new(auth_key.to_vec(), 1)`, whose root/MAC keys are the two halves of
the 64-byte HKDF output derived from the 32-byte zero root key prefixed to `auth_key`.

It mirrors `send_ct::NoHeaderReceived::new` on the B→A side, so both initial authenticators
agree. The only precondition is that the prefixed key fits in memory:
`auth_key.length + 32 ≤ Usize.max`.

**Source**: spqr/src/v1/unchunked/send_ek.rs -/

@[expose] public section

open Aeneas Aeneas.Std Result spqr crypto

namespace spqr.v1.unchunked.send_ek.KeysUnsampled

open List core.num.U64 authenticator.Authenticator in
/-- **Spec theorem for `spqr.v1.unchunked.send_ek.KeysUnsampled.new`**:

• Copies `auth_key` into a vector (`Slice.to_vec`, identity on contents) and calls
  `Authenticator.new v 1#u64`; returns `{ epoch := 1, auth := a }`.
• Requires `auth_key.length + 32 ≤ Usize.max`; under this the call never panics.
• Postcondition: `result.epoch = 1`, both keys have length `32`, and
  `root_key.val ++ mac_key.val = hkdf (replicate 32 0#u8) (replicate 32 0#u8 ++ auth_key.val)
  (updateLabel ++ to_be_bytes 1#u64) 64`. -/
@[step]
theorem new_spec (auth_key : Slice U8)
    (h : auth_key.length + 32 ≤ Usize.max) :
    new auth_key ⦃ (result : KeysUnsampled) =>
      result.epoch = 1#u64 ∧
      result.auth.root_key.length = 32 ∧
      result.auth.mac_key.length = 32 ∧
      result.auth.root_key.val ++ result.auth.mac_key.val
        = hkdf (replicate 32 0#u8) (replicate 32 0#u8 ++ auth_key.val)
          (updateLabel ++ to_be_bytes 1#u64) 64 ⦄ := by
  unfold new
  step*
  · subst auth_key_post
    simpa [alloc.vec.Vec.length, alloc.vec.Vec.val] using h
  · subst auth_key_post
    simp_all [alloc.vec.Vec.val]

end spqr.v1.unchunked.send_ek.KeysUnsampled
