/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import SrcTranslated.Funs
/-!
# Spec theorem for `spqr::v1::chunked::send_ct::{EkReceivedCt1Sampled}::epoch`

`EkReceivedCt1Sampled` is the chunked B→A state after B has received A's `ek` and sampled
`ct1`, which is still being streamed in chunks.  It wraps the unchunked `Ct1SentEkReceived`
(holding `epoch : u64`, `ek`, `ct1`, …) plus a `PolyEncoder` for `ct1`.

`epoch` is a pure accessor forwarding to `self.uc.epoch`; it cannot fail.

**Source**: spqr/src/v1/chunked/send_ct.rs (lines 245:4-247:5)
-/

@[expose] public section

open Aeneas Aeneas.Std Result spqr

namespace spqr.v1.chunked.send_ct.EkReceivedCt1Sampled

/-- **Spec theorem for `spqr.v1.chunked.send_ct.EkReceivedCt1Sampled.epoch`**:

• Takes `self : EkReceivedCt1Sampled` (Rust `&self`, reference erased by Aeneas).
• Returns the `epoch : U64` field of the inner unchunked state `self.uc`.
• Always succeeds: a field projection is total.
• The `sending_ct1` encoder does not affect the result.

Postcondition: `result = self.uc.epoch`.

Proof: unfold `epoch`, then `step*`.

**Source**: spqr/src/v1/chunked/send_ct.rs (lines 245:4-247:5)
-/
@[step]
theorem epoch_spec (self : EkReceivedCt1Sampled) :
    epoch self ⦃ (result : U64) =>
      result = self.uc.epoch ⦄ := by
  unfold epoch
  step*

end spqr.v1.chunked.send_ct.EkReceivedCt1Sampled
