/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import SrcTranslated.Funs
/-!
# Spec theorem for `spqr::v1::chunked::send_ek::{HeaderSent}::epoch`

`HeaderSent` is the state of the encapsulation-key-sending (A→B) side of the *chunked* V1
ratchet after A has fully streamed the header (the first part of its new incremental ML-KEM
encapsulation key) to B, while A is still streaming the remainder of its encapsulation key `ek`
to B in fixed-size chunks and is simultaneously collecting the chunks of B's first ciphertext
`ct1`.  It wraps the corresponding unchunked state `unchunked::EkSent` (which carries the
current `epoch : u64` together with the `Authenticator` and the 2400-byte decapsulation key
`dk`) and adds a `PolyEncoder` that erasure-encodes the outgoing `ek` chunks and a
`PolyDecoder` that erasure-decodes the incoming `ct1` chunks.

`HeaderSent::epoch` is a pure accessor: it simply forwards to the `epoch` field of the inner
unchunked state `uc`.  It performs no arithmetic, allocates nothing, and cannot fail, so the
extracted Lean function is `ok self.uc.epoch` for every input.

**Source**: spqr/src/v1/chunked/send_ek.rs (lines 151:4-153:5)
-/

@[expose] public section

open Aeneas Aeneas.Std Result spqr

namespace spqr.v1.chunked.send_ek.HeaderSent

/-- **Spec theorem for `spqr.v1.chunked.send_ek.HeaderSent.epoch`**:

• Takes a chunked `HeaderSent` state `self`, consisting of the unchunked inner state
  `self.uc : unchunked.send_ek.EkSent`, the chunk encoder `self.sending_ek : PolyEncoder`,
  and the chunk decoder `self.receiving_ct1 : PolyDecoder`.  In the original Rust source
  `self` is passed by shared reference (`&self`); after Aeneas extraction the reference is
  erased and the argument is a plain `HeaderSent` value.
• Projects the `epoch` field out of the inner unchunked state:
    `self.uc.epoch : U64`
  (the Rust type alias `Epoch` is `u64`).
• Returns that value unchanged.

• The function always succeeds (no panic) for any `HeaderSent` input, since a field
  projection is a total operation.
• The chunked wrapper introduces no epoch of its own: the epoch exposed by `HeaderSent` is
  exactly the epoch of the underlying unchunked `EkSent`, so the following identity holds:
    `HeaderSent.epoch self = ok (self.uc.epoch)`
• Neither the `sending_ek` encoder nor the `receiving_ct1` decoder plays any role in the
  result; in particular, how many chunks of `ek` have already been emitted by `send_ek_chunk`
  and how many chunks of `ct1` have already been collected by `recv_ct1_chunk` do not affect
  the reported epoch.  The `hax` refinement on `receiving_ct1`
  (`pts_needed == CIPHERTEXT1_SIZE / 2`) is likewise irrelevant here and is not assumed.
• This is the epoch that `States::send` stamps onto every outgoing `Ek` message (which
  carries the next `ek` chunk) while A is still streaming `ek`, and against which
  `States::recv` compares the epoch of an incoming message (`msg.epoch.cmp(&state.epoch())`)
  before forwarding a `Ct1` chunk to `recv_ct1_chunk`: a greater epoch is rejected with
  `EpochOutOfRange`, a smaller one is ignored, and only an equal one is processed.

The result satisfies the postcondition:

  `result = self.uc.epoch`

The proof unfolds `epoch` and closes the trivial goal with `step*`.

**Source**: spqr/src/v1/chunked/send_ek.rs (lines 151:4-153:5)
-/
@[step]
theorem epoch_spec (self : HeaderSent) :
    epoch self ⦃ (result : U64) =>
      result = self.uc.epoch ⦄ := by
  unfold epoch
  step*

end spqr.v1.chunked.send_ek.HeaderSent
