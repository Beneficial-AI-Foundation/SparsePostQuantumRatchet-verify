/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
/-!
# Spec theorem for `spqr::chain::EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH`

`EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH` is a compile-time constant that controls how many past
epochs are retained *before* the current send epoch when `send_key` advances the chain.  The
send epoch itself and any subsequent epochs are always kept; this constant governs only the
look-back window.

  • Value: **1** (a single prior epoch is kept).

When `Chain::send_key` detects an epoch advance it executes `send_key_loop0`, which repeatedly
calls `pop_front` on `self.links` while `epoch_index > EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH`,
trimming old epochs from the front of the deque.

**Source**: spqr/src/chain.rs (line 125:0-125:52)
-/

open Aeneas Aeneas.Std Result spqr

namespace spqr.chain

/--
**Spec theorem for `spqr.chain.EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH`**:

The constant satisfies:

  `EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH = 1#usize`

This is the exact value used in the Rust source:

```rust
const EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH: usize = 1;
```

The theorem states that `EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH` is definitionally equal to `1#usize`.

**Source**: spqr/src/chain.rs (line 125:0-125:52)
-/
@[simp]
theorem EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH_spec :
    chain.EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH = 1#usize := by
  unfold chain.EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH
  grind

end spqr.chain
