/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import SrcTranslated.Funs
/-!
# Spec theorem for `spqr::v1::chunked::send_ct::{NoHeaderReceived}::epoch`

`NoHeaderReceived` is the very first state of the ciphertext-sending (B→A) side of the *chunked*
V1 ratchet: B has not yet received (all of) A's header `ρ ‖ H(ek)` and therefore cannot sample a
ciphertext yet.  It wraps the corresponding unchunked state of the same name (which carries the
current `epoch : u64` together with the `Authenticator`) and adds a `PolyDecoder`
(`receiving_hdr`) for reassembling the 96-byte header-plus-MAC out of incoming fixed-size chunks.

`NoHeaderReceived::epoch` is a pure accessor: it simply forwards to the `epoch` field of the inner
unchunked state `uc`.  It performs no arithmetic, allocates nothing, and cannot fail, so the
extracted Lean function is `ok self.uc.epoch` for every input.

**Source**: spqr/src/v1/chunked/send_ct.rs (lines 112:4-114:5)
-/

@[expose] public section

open Aeneas Aeneas.Std Result spqr

namespace spqr.v1.chunked.send_ct.NoHeaderReceived

/-- **Spec theorem for `spqr.v1.chunked.send_ct.NoHeaderReceived.epoch`**:

• Takes a chunked `NoHeaderReceived` state `self`, consisting of the unchunked inner state
  `self.uc : unchunked.send_ct.NoHeaderReceived` and the header chunk decoder
  `self.receiving_hdr : PolyDecoder`.  In the original Rust source `self` is passed by shared
  reference (`&self`); after Aeneas extraction the reference is erased and the argument is a
  plain `NoHeaderReceived` value.
• Projects the `epoch` field out of the inner unchunked state:
    `self.uc.epoch : U64`
  (the Rust type alias `Epoch` is `u64`).
• Returns that value unchanged.

• The function always succeeds (no panic) for any `NoHeaderReceived` input, since a field
  projection is a total operation.
• The chunked wrapper introduces no epoch of its own: the epoch exposed by
  `NoHeaderReceived` is exactly the epoch of the underlying unchunked `NoHeaderReceived`,
  so the following identity holds:
    `NoHeaderReceived.epoch self = ok (self.uc.epoch)`
• The `receiving_hdr` decoder plays no role in the result; in particular, how many header
  chunks have already been received does not affect the reported epoch.
• For a freshly constructed state (`NoHeaderReceived::new`) this epoch is `1`
  (see `new_spec`); it is the epoch against which incoming header chunks are checked in
  `States::recv` and which `States::send` reports while B is still waiting for the header.

The result satisfies the postcondition:

  `result = self.uc.epoch`
-/
@[step]
theorem epoch_spec (self : NoHeaderReceived) :
    epoch self ⦃ (result : U64) =>
      result = self.uc.epoch ⦄ := by
  unfold epoch
  step*

end spqr.v1.chunked.send_ct.NoHeaderReceived
