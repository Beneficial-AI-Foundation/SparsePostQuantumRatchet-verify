/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import SrcTranslated.Funs
/-!
# Spec theorem for `spqr::v1::chunked::send_ct::{Ct1Sampled}::epoch`

`Ct1Sampled` is the chunked V1 state of the ciphertext-sending (B→A) side after `ct1` has
been sampled and is being streamed in chunks, but before A's `ek` is fully received.  It wraps
the unchunked `Ct1Sent` (holding `epoch : u64`, the `Authenticator` and `ct1`) plus a
`PolyEncoder` for `ct1` chunks and a `PolyDecoder` for `ek` chunks.

`Ct1Sampled::epoch` is a pure accessor forwarding to `uc.epoch`; it cannot fail, so the
extracted function is `ok self.uc.epoch`.

**Source**: spqr/src/v1/chunked/send_ct.rs (lines 219:4-221:5)
-/

@[expose] public section

open Aeneas Aeneas.Std Result spqr

namespace spqr.v1.chunked.send_ct.Ct1Sampled

/-- **Spec theorem for `spqr.v1.chunked.send_ct.Ct1Sampled.epoch`**:

• Takes a chunked state `self : Ct1Sampled` (fields `uc : unchunked.send_ct.Ct1Sent`,
  `sending_ct1 : PolyEncoder`, `receiving_ek : PolyDecoder`); the Rust `&self` is erased
  by Aeneas.
• Returns `self.uc.epoch : U64` unchanged (Rust alias `Epoch = u64`).
• Always succeeds, since a field projection is total.
• The wrapper adds no epoch of its own, so `Ct1Sampled.epoch self = ok self.uc.epoch`;
  the encoder/decoder state is irrelevant to the result.
• This epoch is compared against in `States::recv` and stamped on every `ct1` chunk by
  `States::send`.

Postcondition: `result = self.uc.epoch`.

The proof unfolds `epoch` and closes with `step*`.

**Source**: spqr/src/v1/chunked/send_ct.rs (lines 219:4-221:5)
-/
@[step]
theorem epoch_spec (self : Ct1Sampled) :
    epoch self ⦃ (result : U64) =>
      result = self.uc.epoch ⦄ := by
  unfold epoch
  step*

end spqr.v1.chunked.send_ct.Ct1Sampled
