/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import Spqr.Specs.V1.Chunked.SendCt.NoHeaderReceived.New
/-!
# Spec theorem for `spqr::v1::chunked::states::{States}::init_b`

`States::init_b` builds the initial state of party B (the B→A direction) of the *chunked* V1
ratchet.  Party B starts by waiting for A's encapsulation-key header, so the initial state is
the `NoHeaderReceived` variant of the `States` enum, whose payload is produced by
`chunked::send_ct::NoHeaderReceived::new(auth_key)`.

`init_b` introduces no logic beyond this delegation and constructor injection, so its
postcondition is inherited from the corresponding `NoHeaderReceived::new` specification: the
inner unchunked state sits at epoch `1` with a fresh `Authenticator` derived from `auth_key`,
and the header decoder is a fresh `PolyDecoder` for the `96`-byte header.

The precondition `auth_key.length + 32 ≤ Usize.max` is inherited from the constructor chain
(cloning `auth_key` and prefixing the 32-byte zero root key must not overflow `usize`).

The A→B counterpart is `States::init_a` (`KeysUnsampled`).

**Source**: spqr/src/v1/chunked/states.rs (lines 62:4-64:5)
-/

@[expose] public section

open Aeneas Aeneas.Std Result spqr crypto

namespace spqr.v1.chunked.states.States

open List core.num.U64 authenticator.Authenticator in
/-- **Spec theorem for `spqr.v1.chunked.states.States.init_b`**:

• Takes the shared authentication key `auth_key` (a byte slice).
• Delegates immediately to the chunked constructor:
    `chunked.send_ct.NoHeaderReceived.new auth_key`
  and wraps the result in the `States.NoHeaderReceived` constructor.
• Requires `auth_key.length + 32 ≤ Usize.max`; then the call never panics.

Postcondition: the result is `States.NoHeaderReceived nhr` for some `nhr` satisfying the
`NoHeaderReceived.new` postcondition — `nhr.uc.epoch = 1`, both authenticator keys have
length `32` and their concatenation equals the `hkdf` derivation from the zero root key and
`auth_key`; `nhr.receiving_hdr` needs `48` points, has `16` default polynomials, and is not
complete.

**Source**: spqr/src/v1/chunked/states.rs (lines 62:4-64:5)
-/
@[step]
theorem init_b_spec (auth_key : Slice U8)
    (h : auth_key.length + 32 ≤ Usize.max) :
    init_b auth_key ⦃ (result : States) =>
      ∃ nhr : send_ct.NoHeaderReceived,
        result = States.NoHeaderReceived nhr ∧
        nhr.uc.epoch = 1#u64 ∧
        nhr.uc.auth.root_key.length = 32 ∧
        nhr.uc.auth.mac_key.length = 32 ∧
        nhr.uc.auth.root_key.val ++ nhr.uc.auth.mac_key.val
          = hkdf (replicate 32 0#u8) (replicate 32 0#u8 ++ auth_key.val)
            (updateLabel ++ to_be_bytes 1#u64) 64 ∧
        nhr.receiving_hdr.pts_needed.val = 48 ∧
        nhr.receiving_hdr.pts.val = replicate 16 default ∧
        nhr.receiving_hdr.is_complete = false ⦄ := by
  unfold init_b
  step*

end spqr.v1.chunked.states.States
