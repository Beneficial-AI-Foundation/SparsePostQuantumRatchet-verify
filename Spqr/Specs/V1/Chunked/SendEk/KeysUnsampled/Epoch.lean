/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import SrcTranslated.Funs
/-!
# Spec theorem for `spqr::v1::chunked::send_ek::{KeysUnsampled}::epoch`

`KeysUnsampled` is the initial state of the encapsulation-key-sending (A→B) side of the
*chunked* V1 ratchet: A has not yet sampled its incremental ML-KEM key pair for the current
epoch.  It is a thin wrapper around the corresponding unchunked state
`unchunked::KeysUnsampled`, which carries the current `epoch : u64` together with the
`Authenticator` (root key and MAC key) shared with B; the chunked wrapper adds no fields of its
own.

`KeysUnsampled::epoch` is a pure accessor: it simply forwards to the `epoch` field of the inner
unchunked state `uc`.  It performs no arithmetic, allocates nothing, and cannot fail, so the
extracted Lean function is `ok self.uc.epoch` for every input.

**Source**: spqr/src/v1/chunked/send_ek.rs (lines 68:4-70:5)
-/

@[expose] public section

open Aeneas Aeneas.Std Result spqr

namespace spqr.v1.chunked.send_ek.KeysUnsampled

/-- **Spec theorem for `spqr.v1.chunked.send_ek.KeysUnsampled.epoch`**:

• Takes a chunked `KeysUnsampled` state `self`, consisting solely of the unchunked inner state
  `self.uc : unchunked.send_ek.KeysUnsampled`.  In the original Rust source `self` is passed by
  shared reference (`&self`); after Aeneas extraction the reference is erased and the argument
  is a plain `KeysUnsampled` value.
• Projects the `epoch` field out of the inner unchunked state:
    `self.uc.epoch : U64`
  (the Rust type alias `Epoch` is `u64`).
• Returns that value unchanged.

• The function always succeeds (no panic) for any `KeysUnsampled` input, since a field
  projection is a total operation.
• The chunked wrapper introduces no epoch of its own: the epoch exposed by `KeysUnsampled` is
  exactly the epoch of the underlying unchunked `KeysUnsampled`, so the following identity
  holds:
    `KeysUnsampled.epoch self = ok (self.uc.epoch)`
• The authenticator `self.uc.auth` plays no role in the result.
• For a state freshly built by `KeysUnsampled::new` the reported epoch is `1` (see `new_spec`);
  for the state produced by `Ct2Sent::recv_next_epoch` from a `Ct2Sent` at epoch `n` it is
  `n + 1`, i.e. the epoch A is about to start by sampling fresh keys.
• This is the epoch that `States::send` stamps onto the outgoing `EkHdr` message (carrying the
  first header chunk produced by `send_hdr_chunk`), and against which `States::recv` compares
  the epoch of an incoming message (`msg.epoch.cmp(&state.epoch())`): messages at a strictly
  greater epoch are rejected with `EpochOutOfRange`, the others leave the state unchanged.

The result satisfies the postcondition:

  `result = self.uc.epoch`

The proof unfolds `epoch` and closes the trivial goal with `step*`.

**Source**: spqr/src/v1/chunked/send_ek.rs (lines 68:4-70:5)
-/
@[step]
theorem epoch_spec (self : KeysUnsampled) :
    epoch self ⦃ (result : U64) =>
      result = self.uc.epoch ⦄ := by
  unfold epoch
  step*

end spqr.v1.chunked.send_ek.KeysUnsampled
