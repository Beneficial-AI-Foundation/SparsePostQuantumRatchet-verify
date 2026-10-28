/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import SrcTranslated.Funs
/-!
# Spec theorem for `spqr::v1::chunked::send_ct::{HeaderReceived}::epoch`

`HeaderReceived` is the chunked V1 state of the ciphertext-sending (B→A) side after A's header
`ρ ‖ H(ek)` has been reassembled and authenticated, but before `ct1` is sampled.  It wraps the
unchunked `HeaderReceived` (holding `epoch : u64`, the `Authenticator` and the 64-byte `hdr`)
plus a `PolyDecoder` for `ek` chunks.

`HeaderReceived::epoch` is a pure accessor forwarding to `uc.epoch`; it cannot fail, so the
extracted function is `ok self.uc.epoch`.

**Source**: spqr/src/v1/chunked/send_ct.rs (lines 144:4-146:5)
-/

@[expose] public section

open Aeneas Aeneas.Std Result spqr

namespace spqr.v1.chunked.send_ct.HeaderReceived

/-- **Spec theorem for `spqr.v1.chunked.send_ct.HeaderReceived.epoch`**:

• Takes a chunked state `self : HeaderReceived` (fields `uc : unchunked.send_ct.HeaderReceived`,
  `receiving_ek : PolyDecoder`); the Rust `&self` is erased by Aeneas.
• Returns `self.uc.epoch : U64` unchanged (Rust alias `Epoch = u64`).
• Always succeeds, since a field projection is total.
• The wrapper adds no epoch of its own, so `HeaderReceived.epoch self = ok self.uc.epoch`;
  `hdr` and the decoder state are irrelevant to the result.
• The epoch is inherited from `NoHeaderReceived` (see `recv_hdr_chunk_spec`); `States::recv`
  rejects messages with a greater epoch (`EpochOutOfRange`) and `States::send` stamps it on
  the first `ct1` chunk.

Postcondition: `result = self.uc.epoch`.

The proof unfolds `epoch` and closes with `step*`.

**Source**: spqr/src/v1/chunked/send_ct.rs (lines 144:4-146:5)
-/
@[step]
theorem epoch_spec (self : HeaderReceived) :
    epoch self ⦃ (result : U64) =>
      result = self.uc.epoch ⦄ := by
  unfold epoch
  step*

end spqr.v1.chunked.send_ct.HeaderReceived
