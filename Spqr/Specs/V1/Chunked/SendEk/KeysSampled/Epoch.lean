/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import SrcTranslated.Funs
/-!
# Spec theorem for `spqr::v1::chunked::send_ek::{KeysSampled}::epoch`

`KeysSampled` is the state of the encapsulation-key-sending (A→B) side of the *chunked* V1
ratchet after A has sampled its new incremental ML-KEM key pair but before the header has been
fully streamed to B.  It wraps the corresponding unchunked state
`unchunked::HeaderSent` (which carries the current `epoch : u64` together with the
`Authenticator`, the encapsulation key `ek`, and the 2400-byte decapsulation key `dk`) and adds
a `PolyEncoder` that erasure-encodes the outgoing header chunks.

`KeysSampled::epoch` is a pure accessor: it simply forwards to the `epoch` field of the inner
unchunked state `uc`.  It performs no arithmetic, allocates nothing, and cannot fail, so the
extracted Lean function is `ok self.uc.epoch` for every input.

**Source**: spqr/src/v1/chunked/send_ek.rs (lines 100:4-102:5)
-/

@[expose] public section

open Aeneas Aeneas.Std Result spqr

namespace spqr.v1.chunked.send_ek.KeysSampled

/-- **Spec theorem for `spqr.v1.chunked.send_ek.KeysSampled.epoch`**:

• Takes a chunked state `self : KeysSampled` (fields `uc : unchunked.send_ek.HeaderSent`,
  `sending_hdr : PolyEncoder`); the Rust `&self` is erased by Aeneas.
• Returns `self.uc.epoch : U64` unchanged (Rust alias `Epoch = u64`).
• Always succeeds, since a field projection is total.
• The wrapper adds no epoch of its own, so `KeysSampled.epoch self = ok self.uc.epoch`;
  the `sending_hdr` encoder state is irrelevant to the result.
• This epoch is compared against in `States::recv` and stamped on every header chunk by
  `States::send`.

Postcondition: `result = self.uc.epoch`.

The proof unfolds `epoch` and closes with `step*`.

**Source**: spqr/src/v1/chunked/send_ek.rs (lines 100:4-102:5)
-/
@[step]
theorem epoch_spec (self : KeysSampled) :
    epoch self ⦃ (result : U64) =>
      result = self.uc.epoch ⦄ := by
  unfold epoch
  step*

end spqr.v1.chunked.send_ek.KeysSampled
