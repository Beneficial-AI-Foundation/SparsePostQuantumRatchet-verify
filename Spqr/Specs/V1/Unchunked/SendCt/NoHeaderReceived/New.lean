/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import SrcTranslated.Funs
public import Spqr.Specs.Authenticator.Authenticator.New
/-!
# Spec theorem for `spqr::v1::unchunked::send_ct::{NoHeaderReceived}::new`

`NoHeaderReceived::new` builds the very first state of the ciphertext-sending (B→A) side of the
unchunked V1 ratchet.  At this point B has received nothing from A yet, so the state carries only
two pieces of data:

  1. the epoch counter, initialised to `1`;
  2. a fresh `Authenticator`, obtained by copying the caller's `auth_key` slice into an owned
     `Vec<u8>` and calling `Authenticator::new(auth_key.to_vec(), 1)`.

`Authenticator::new` zero-initialises a 32-byte root key and immediately performs one `update`
step at epoch `1`, so the resulting root and MAC keys are the two 32-byte halves of the 64-byte
HKDF-SHA256 output keyed on the 32 zero bytes prefixed to `auth_key`.

The only way the construction can fail is if `auth_key` prefixed by the 32-byte zero root key
cannot fit in memory, hence the single precondition `auth_key.length + 32 ≤ Usize.max`.

**Source**: spqr/src/v1/unchunked/send_ct.rs (lines 92:4-97:5)
-/

@[expose] public section

open Aeneas Aeneas.Std Result spqr crypto

namespace spqr.v1.unchunked.send_ct.NoHeaderReceived

open List core.num.U64 authenticator.Authenticator in
/-- **Spec theorem for `spqr.v1.unchunked.send_ct.NoHeaderReceived.new`**:

• Takes a byte slice `auth_key` (the shared authentication key agreed by both parties).
• Copies the slice into an owned vector via `Slice.to_vec`, which is the identity on `u8`
  contents (byte cloning is trivial), so the vector holds exactly `auth_key.val`.
• Delegates to `Authenticator.new v 1#u64`, which produces an authenticator whose keys are the
  two halves of
    `hkdf (replicate 32 0) (replicate 32 0 ++ auth_key.val) (updateLabel ++ to_be_bytes 1) 64`.
• Returns `{ epoch := 1, auth := a }`.

• Requires that `auth_key` prefixed by the 32 zero bytes of the empty initial authenticator
  state fits in memory: `auth_key.length + 32 ≤ Usize.max`.  Under this hypothesis the call
  always succeeds (no panic).

The result satisfies the postcondition:

  `result.epoch = 1`
  `result.auth.root_key.length = 32`
  `result.auth.mac_key.length = 32`
  `result.auth.root_key.val ++ result.auth.mac_key.val =
       hkdf (replicate 32 0#u8) (replicate 32 0#u8 ++ auth_key.val)
         (updateLabel ++ to_be_bytes 1#u64) 64`

The proof unfolds `new` to expose the `to_vec` and `Authenticator.new` calls, discharges them
with `step*` (using the registered `to_vec_spec` and `new_spec`), and closes the remaining
goal by rewriting the vector contents back to `auth_key.val`.

**Source**: spqr/src/v1/unchunked/send_ct.rs (lines 92:4-97:5)
-/
@[step]
theorem new_spec (auth_key : Slice U8)
    (h : auth_key.length + 32 ≤ Usize.max) :
    new auth_key ⦃ (result : NoHeaderReceived) =>
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

end spqr.v1.unchunked.send_ct.NoHeaderReceived
