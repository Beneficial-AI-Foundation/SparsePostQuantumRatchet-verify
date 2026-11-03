/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import SrcTranslated.Funs
/-!
# Spec theorem for `spqr::v1::chunked::send_ct::{Ct1Acknowledged}::epoch`

Pure accessor forwarding `epoch` from the inner unchunked `Ct1Sent` state (`self.uc.epoch`).
Always succeeds; the `PolyDecoder` field is unused.

**Source**: spqr/src/v1/chunked/send_ct.rs (lines 281:4-283:5)
-/

@[expose] public section

open Aeneas Aeneas.Std Result spqr

namespace spqr.v1.chunked.send_ct.Ct1Acknowledged

/-- **Spec theorem for `spqr.v1.chunked.send_ct.Ct1Acknowledged.epoch`**:

Returns `self.uc.epoch` (the inner unchunked `Ct1Sent` epoch). Total and infallible.
Postcondition: `result = self.uc.epoch`. -/
@[step]
theorem epoch_spec (self : Ct1Acknowledged) :
    epoch self ⦃ (result : U64) =>
      result = self.uc.epoch ⦄ := by
  unfold epoch
  step*

end spqr.v1.chunked.send_ct.Ct1Acknowledged
