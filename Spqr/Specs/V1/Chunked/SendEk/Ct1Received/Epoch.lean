/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import SrcTranslated.Funs
/-!
# Spec theorem for `spqr::v1::chunked::send_ek::{Ct1Received}::epoch`

`Ct1Received` is the state of the encapsulation-key-sending (A→B) side of the *chunked* V1
ratchet after A has received (erasure-decoded) B's first ciphertext `ct1`, while A is still
streaming its own encapsulation key `ek` to B in fixed-size chunks.  It wraps the corresponding
unchunked state `unchunked::EkSentCt1Received` (which carries the current `epoch : u64`
together with the `Authenticator`, the 2400-byte decapsulation key `dk`, and the 960-byte
`ct1`) and adds a `PolyEncoder` that erasure-encodes the outgoing `ek` chunks.

`Ct1Received::epoch` is a pure accessor: it simply forwards to the `epoch` field of the inner
unchunked state `uc`.  It performs no arithmetic, allocates nothing, and cannot fail, so the
extracted Lean function is `ok self.uc.epoch` for every input.

**Source**: spqr/src/v1/chunked/send_ek.rs (lines 182:4-184:5)
-/

@[expose] public section

open Aeneas Aeneas.Std Result spqr

namespace spqr.v1.chunked.send_ek.Ct1Received

/-- **Spec theorem for `spqr.v1.chunked.send_ek.Ct1Received.epoch`**:

• Takes a chunked `Ct1Received` state `self`, consisting of the unchunked inner state
  `self.uc : unchunked.send_ek.EkSentCt1Received` and the chunk encoder
  `self.sending_ek : PolyEncoder`.  In the original Rust source `self` is passed by shared
  reference (`&self`); after Aeneas extraction the reference is erased and the argument is a
  plain `Ct1Received` value.
• Projects the `epoch` field out of the inner unchunked state:
    `self.uc.epoch : U64`
  (the Rust type alias `Epoch` is `u64`).
• Returns that value unchanged.

• The function always succeeds (no panic) for any `Ct1Received` input, since a field
  projection is a total operation.
• The chunked wrapper introduces no epoch of its own: the epoch exposed by `Ct1Received` is
  exactly the epoch of the underlying unchunked `EkSentCt1Received`, so the following identity
  holds:
    `Ct1Received.epoch self = ok (self.uc.epoch)`
• The `sending_ek` encoder plays no role in the result; in particular, how many chunks of `ek`
  have already been emitted by `send_ek_chunk` does not affect the reported epoch.
• This is the epoch that `States::send` stamps onto every outgoing `EkCt1Ack` message (which
  carries the next `ek` chunk) while A is still streaming `ek`, and against which
  `States::recv` compares the epoch of an incoming message (`msg.epoch.cmp(epoch)`) before
  forwarding a `Ct2` chunk to `recv_ct2_chunk` (whose precondition `epoch == self.uc.epoch`
  is thereby discharged).

The result satisfies the postcondition:

  `result = self.uc.epoch`

The proof unfolds `epoch` and closes the trivial goal with `step*`.

**Source**: spqr/src/v1/chunked/send_ek.rs (lines 182:4-184:5)
-/
@[step]
theorem epoch_spec (self : Ct1Received) :
    epoch self ⦃ (result : U64) =>
      result = self.uc.epoch ⦄ := by
  unfold epoch
  step*

end spqr.v1.chunked.send_ek.Ct1Received
