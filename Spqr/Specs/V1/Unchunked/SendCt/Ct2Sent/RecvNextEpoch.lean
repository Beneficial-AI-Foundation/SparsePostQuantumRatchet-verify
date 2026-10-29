/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import SrcTranslated.Funs
/-!
# Spec theorem for `spqr::v1::unchunked::send_ct::{Ct2Sent}::recv_next_epoch`

`Ct2Sent::recv_next_epoch` transitions the ciphertext-sending side to the next epoch: after
`ct2` for epoch `e` has been sent and the peer announces `e + 1`, B becomes the encapsulation-key
sender.  It computes `epoch + 1` (checked), asserts it equals `next_epoch`, and returns
`send_ek::KeysUnsampled { epoch: epoch + 1, auth }`.

The hax contract `requires(self.epoch < u64::MAX && next_epoch == self.epoch + 1)` rules out
the overflow and discharges the assertion, so the function is total under it.

**Source**: spqr/src/v1/unchunked/send_ct.rs (lines 201:4-208:5) -/

@[expose] public section

open Aeneas Aeneas.Std Result spqr

namespace spqr.v1.unchunked.send_ct.Ct2Sent

/-- **Spec theorem for `spqr.v1.unchunked.send_ct.Ct2Sent.recv_next_epoch`**:

• Computes `self.epoch + 1#u64` (no overflow by `h_epoch`), asserts it equals `next_epoch`
  (by `h_next`), and returns `{ epoch := self.epoch + 1, auth := self.auth }`.
• Requires `h_epoch : self.epoch < U64.max` and `h_next : next_epoch.val = self.epoch.val + 1`;
  under these the call never panics.

Postcondition: `result.epoch.val = self.epoch.val + 1`, `result.epoch = next_epoch` (redundant
given `h_next`, stated for convenience), and `result.auth = self.auth`. -/
@[step]
theorem recv_next_epoch_spec (self : Ct2Sent) (next_epoch : U64)
    (h_next : next_epoch.val = self.epoch.val + 1) :
    recv_next_epoch self next_epoch ⦃ (result : send_ek.KeysUnsampled) =>
      result.epoch.val = self.epoch.val + 1 ∧
      result.epoch = next_epoch ∧
      result.auth = self.auth ⦄ := by
  unfold recv_next_epoch
  step*

end spqr.v1.unchunked.send_ct.Ct2Sent
