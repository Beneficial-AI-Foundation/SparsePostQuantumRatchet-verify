/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import SrcTranslated.Funs
public import Spqr.Specs.V1.Chunked.SendEk.KeysUnsampled.New
/-!
# Spec theorem for `spqr::v1::chunked::states::{States}::init_a`

`States::init_a` builds the initial state of party A (the A→B direction) of the *chunked* V1
ratchet.  Party A starts by sending its encapsulation key, before any key pair has been
sampled, so the initial state is the `KeysUnsampled` variant of the `States` enum, whose payload
is produced by `chunked::send_ek::KeysUnsampled::new(auth_key)`.

`init_a` introduces no logic beyond this delegation and constructor injection, so its
postcondition is inherited from the corresponding `KeysUnsampled::new` specification: the
inner unchunked state sits at epoch `1` with a fresh `Authenticator` derived from `auth_key`.
Unlike the B side, no decoder is allocated at this point — the chunked `KeysUnsampled` struct
consists solely of its unchunked payload `uc`.

The precondition `auth_key.length + 32 ≤ Usize.max` is inherited from the constructor chain
(cloning `auth_key` and prefixing the 32-byte zero root key must not overflow `usize`).

The B→A counterpart is `States::init_b` (`NoHeaderReceived`).

**Source**: spqr/src/v1/chunked/states.rs (lines 58:4-60:5)
-/

@[expose] public section

open Aeneas Aeneas.Std Result spqr crypto

namespace spqr.v1.chunked.states.States

open List core.num.U64 authenticator.Authenticator in
/-- **Spec theorem for `spqr.v1.chunked.states.States.init_a`**:

• Takes the shared authentication key `auth_key` (a byte slice).
• Delegates immediately to the chunked constructor:
    `chunked.send_ek.KeysUnsampled.new auth_key`
  and wraps the result in the `States.KeysUnsampled` constructor.
• Requires `auth_key.length + 32 ≤ Usize.max`; then the call never panics.

Postcondition: the result is `States.KeysUnsampled ku` for some `ku` satisfying the
`KeysUnsampled.new` postcondition — `ku.uc.epoch = 1`, both authenticator keys have length
`32` and their concatenation equals the `hkdf` derivation from the zero root key and
`auth_key` at epoch `1`. -/
@[step]
theorem init_a_spec (auth_key : Slice U8)
    (h : auth_key.length + 32 ≤ Usize.max) :
    init_a auth_key ⦃ (result : States) =>
      ∃ ku : send_ek.KeysUnsampled,
        result = States.KeysUnsampled ku ∧
        ku.uc.epoch = 1#u64 ∧
        ku.uc.auth.root_key.length = 32 ∧
        ku.uc.auth.mac_key.length = 32 ∧
        ku.uc.auth.root_key.val ++ ku.uc.auth.mac_key.val
          = hkdf (replicate 32 0#u8) (replicate 32 0#u8 ++ auth_key.val)
            (updateLabel ++ to_be_bytes 1#u64) 64 ⦄ := by
  unfold init_a
  step*

end spqr.v1.chunked.states.States
