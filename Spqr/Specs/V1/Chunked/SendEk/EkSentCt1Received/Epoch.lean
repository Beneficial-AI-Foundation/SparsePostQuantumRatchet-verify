/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import SrcTranslated.Funs
/-!
# Spec theorem for `spqr::v1::chunked::send_ek::{EkSentCt1Received}::epoch`

`EkSentCt1Received` is the state of the encapsulation-key-sending (A→B) side of the *chunked*
V1 ratchet after A has fully streamed its encapsulation key `ek` to B and has received
(erasure-decoded) B's first ciphertext `ct1`, while B's second ciphertext `ct2` is still being
streamed to A in fixed-size chunks.  It wraps the corresponding unchunked state
`unchunked::EkSentCt1Received` (which carries the current `epoch : u64` together with the
`Authenticator`, the 2400-byte decapsulation key `dk`, and the 960-byte `ct1`) and adds a
`PolyDecoder` that erasure-decodes the incoming `ct2` chunks.

`EkSentCt1Received::epoch` is a pure accessor: it simply forwards to the `epoch` field of the
inner unchunked state `uc`.  It performs no arithmetic, allocates nothing, and cannot fail, so
the extracted Lean function is `ok self.uc.epoch` for every input.

**Source**: spqr/src/v1/chunked/send_ek.rs (lines 229:4-231:5)
-/

@[expose] public section

open Aeneas Aeneas.Std Result spqr

namespace spqr.v1.chunked.send_ek.EkSentCt1Received

/-- **Spec theorem for `spqr.v1.chunked.send_ek.EkSentCt1Received.epoch`**:

• Takes a chunked `EkSentCt1Received` state `self`, consisting of the unchunked inner state
  `self.uc : unchunked.send_ek.EkSentCt1Received` and the chunk decoder
  `self.receiving_ct2 : PolyDecoder`.  In the original Rust source `self` is passed by shared
  reference (`&self`); after Aeneas extraction the reference is erased and the argument is a
  plain `EkSentCt1Received` value.
• Projects the `epoch` field out of the inner unchunked state:
    `self.uc.epoch : U64`
  (the Rust type alias `Epoch` is `u64`).
• Returns that value unchanged.

• The function always succeeds (no panic) for any `EkSentCt1Received` input, since a field
  projection is a total operation.
• The chunked wrapper introduces no epoch of its own: the epoch exposed by
  `EkSentCt1Received` is exactly the epoch of the underlying unchunked `EkSentCt1Received`,
  so the following identity holds:
    `EkSentCt1Received.epoch self = ok (self.uc.epoch)`
• The `receiving_ct2` decoder plays no role in the result; in particular, how many chunks of
  `ct2` have already been collected does not affect the reported epoch.
• This is the epoch that `States::send` stamps onto every outgoing `Ct1Ack` message while A
  waits for `ct2`, and against which `States::recv` compares the epoch of an incoming message
  (`msg.epoch.cmp(epoch)`) before forwarding a `Ct2` chunk to `recv_ct2_chunk`.

The result satisfies the postcondition:

  `result = self.uc.epoch`

The proof unfolds `epoch` and closes the trivial goal with `step*`.

**Source**: spqr/src/v1/chunked/send_ek.rs (lines 229:4-231:5)
-/
@[step]
theorem epoch_spec (self : EkSentCt1Received) :
    epoch self ⦃ (result : U64) =>
      result = self.uc.epoch ⦄ := by
  unfold epoch
  step*

end spqr.v1.chunked.send_ek.EkSentCt1Received
