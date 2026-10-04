/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
/-!
# Spec theorem for `spqr::chain::{spqr::chain::KeyHistory}::KEY_SIZE`

`KEY_SIZE = 4 + 32 = 36`: byte size of one key record (4-byte index + 32-byte key).
Used to stride over the flat `Vec<u8>` backing store in `get_loop`, `add`, and `remove`.

**Source**: spqr/src/chain.rs -/

open Aeneas Aeneas.Std

namespace spqr.chain.KeyHistory

/--
**Spec theorem for `spqr.chain.KeyHistory.KEY_SIZE`**:

`4#usize + 32#usize` succeeds and equals `36#usize`. -/
@[step]
theorem KEY_SIZE_spec :
    KEY_SIZE ⦃ (res : Usize) => res = 36#usize ⦄ := by
  unfold KEY_SIZE
  step
  scalar_tac

end spqr.chain.KeyHistory
