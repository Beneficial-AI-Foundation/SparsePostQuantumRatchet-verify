/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
/-! # Spec theorem for `spqr::chain::EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH`

Constant equal to **1**: the number of past epochs kept before the current send epoch
when `send_key` trims `self.links` via `pop_front`.

**Source**: spqr/src/chain.rs -/

open Aeneas Aeneas.Std Result spqr

namespace spqr.chain

/-- **Spec theorem for `spqr.chain.EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH`**:

`EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH = 1#usize`, matching the Rust source. -/
@[simp]
theorem EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH_spec :
    EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH = 1#usize := by
  unfold chain.EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH
  grind

end spqr.chain
