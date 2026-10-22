/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import SrcTranslated.Funs
/-!
# Spec theorem for `spqr::v1::chunked::send_ct::{spqr::v1::chunked::send_ct::Ct2Sampled}::epoch`

`Ct2Sampled` is the state of the ciphertext-sending (B→A) side of the *chunked* V1 ratchet
after the second ciphertext `ct2` has been sampled and is being streamed to A in fixed-size
chunks.  It wraps the corresponding unchunked state `Ct2Sent` (which carries the current
`epoch : u64` together with the `Authenticator`) and adds a `PolyEncoder` that erasure-codes
`ct2` into chunks.

`Ct2Sampled::epoch` is a pure accessor: it simply forwards to the `epoch` field of the inner
unchunked state `uc`.  It performs no arithmetic, allocates nothing, and cannot fail, so the
extracted Lean function is `ok self.uc.epoch` for every input.

**Source**: spqr/src/v1/chunked/send_ct.rs (lines 303:4-305:5)
-/

@[expose] public section

open Aeneas Aeneas.Std Result spqr

namespace spqr.v1.chunked.send_ct.Ct2Sampled

/-- **Spec theorem for `spqr.v1.chunked.send_ct.Ct2Sampled.epoch`**:

• Takes a chunked `Ct2Sampled` state `self`, consisting of the unchunked inner state
  `self.uc : unchunked.send_ct.Ct2Sent` and the chunk encoder `self.sending_ct2 : PolyEncoder`.
  In the original Rust source `self` is passed by shared reference (`&self`); after Aeneas
  extraction the reference is erased and the argument is a plain `Ct2Sampled` value.
• Projects the `epoch` field out of the inner unchunked state:
    `self.uc.epoch : U64`
  (the Rust type alias `Epoch` is `u64`).
• Returns that value unchanged.

• The function always succeeds (no panic) for any `Ct2Sampled` input, since a field projection
  is a total operation.
• The chunked wrapper introduces no epoch of its own: the epoch exposed by `Ct2Sampled` is
  exactly the epoch of the underlying unchunked `Ct2Sent`, so the following identity holds:
    `Ct2Sampled.epoch self = ok (self.uc.epoch)`

The result satisfies the postcondition:

  `result = self.uc.epoch`

The proof unfolds `epoch` and closes the trivial goal with `step*`.

**Source**: spqr/src/v1/chunked/send_ct.rs (lines 303:4-305:5)
-/
@[step]
theorem epoch_spec (self : Ct2Sampled) :
    epoch self ⦃ (result : U64) =>
      result = self.uc.epoch ⦄ := by
  unfold epoch
  step*

end spqr.v1.chunked.send_ct.Ct2Sampled
