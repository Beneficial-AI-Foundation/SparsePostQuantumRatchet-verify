/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import SrcTranslated.Funs
import Spqr.Specs.V1.Unchunked.SendCt.Ct2Sent.RecvNextEpoch
/-!
# Spec theorem for `spqr::v1::chunked::send_ct::{Ct2Sampled}::recv_next_epoch`

`Ct2Sampled` is the state of the ciphertext-sending (B→A) side of the *chunked* V1 ratchet
after the second ciphertext `ct2` has been sampled and is being streamed to A in fixed-size
chunks.  It wraps the corresponding unchunked state `Ct2Sent` (which carries the current
`epoch : u64` together with the `Authenticator`) and adds a `PolyEncoder` that erasure-codes
`ct2` into chunks.

`Ct2Sampled::recv_next_epoch` is the epoch-advancing transition out of this state: once the
peer announces epoch `e + 1`, B has finished its role as ciphertext sender for epoch `e` and
becomes the encapsulation-key sender for the next epoch.  The chunked wrapper introduces no
logic of its own — it forwards to the unchunked `Ct2Sent::recv_next_epoch` (which computes
`epoch + 1` with a checked addition, asserts it equals the announced epoch, and returns
`send_ek::KeysUnsampled { epoch: epoch + 1, auth }`) and re-wraps the result in the chunked
`send_ek::KeysUnsampled { uc }`.  The chunk encoder `sending_ct2` is simply dropped: the
remaining chunks of `ct2` are no longer needed once A has moved on.

The hax contract `requires(self.uc.epoch < u64::MAX && epoch == self.uc.epoch + 1)` rules out
the overflow and discharges the inner assertion, so the function is total under it.

**Source**: spqr/src/v1/chunked/send_ct.rs (lines 298:4-301:5)
-/

@[expose] public section

open Aeneas Aeneas.Std Result spqr

namespace spqr.v1.chunked.send_ct.Ct2Sampled

/-- **Spec theorem for `spqr.v1.chunked.send_ct.Ct2Sampled.recv_next_epoch`**:

• Takes a chunked `Ct2Sampled` state `self`, consisting of the unchunked inner state
  `self.uc : unchunked.send_ct.Ct2Sent` and the chunk encoder `self.sending_ct2 : PolyEncoder`,
  together with the announced next epoch `epoch : U64` (the Rust type alias `Epoch` is `u64`).
  In the original Rust source `self` is consumed by value; the Lean extraction is identical.
• Delegates immediately to the unchunked transition:
    `unchunked.send_ct.Ct2Sent.recv_next_epoch self.uc epoch`
  which computes `self.uc.epoch + 1#u64`, asserts it equals `epoch`, and returns
  `{ epoch := self.uc.epoch + 1, auth := self.uc.auth }`.
• Wraps that value as the chunked `send_ek.KeysUnsampled { uc }` and returns it.  The field
  `self.sending_ct2` does not flow into the result.

• Requires `h_next : epoch.val = self.uc.epoch.val + 1`.  Since `epoch` is a `U64`, this
  also implies `self.uc.epoch < U64.max`, so the checked addition cannot overflow and the
  inner `massert` succeeds; under this hypothesis the call never panics.  This is exactly the
  hax precondition `self.uc.epoch < u64::MAX && epoch == self.uc.epoch + 1`.
• The chunked wrapper adds no epoch of its own: the epoch of the resulting `KeysUnsampled` is
  exactly the epoch produced by the underlying unchunked `Ct2Sent::recv_next_epoch`, and the
  `Authenticator` is carried over unchanged.

The result satisfies the postcondition:

  `result.uc.epoch.val = self.uc.epoch.val + 1 ∧
   result.uc.epoch = epoch ∧
   result.uc.auth = self.uc.auth`

(the second conjunct is redundant given `h_next` but is stated for convenience, mirroring the
unchunked spec).

The proof unfolds `recv_next_epoch` to expose the underlying unchunked call and discharges the
resulting goal with `step*`, which applies the already-registered
`unchunked.send_ct.Ct2Sent.recv_next_epoch_spec`.

**Source**: spqr/src/v1/chunked/send_ct.rs (lines 298:4-301:5)
-/
@[step]
theorem recv_next_epoch_spec (self : Ct2Sampled) (epoch : U64)
    (h_next : epoch.val = self.uc.epoch.val + 1) :
    recv_next_epoch self epoch ⦃ (result : send_ek.KeysUnsampled) =>
      result.uc.epoch.val = self.uc.epoch.val + 1 ∧
      result.uc.epoch = epoch ∧
      result.uc.auth = self.uc.auth ⦄ := by
  unfold recv_next_epoch
  step*

end spqr.v1.chunked.send_ct.Ct2Sampled
