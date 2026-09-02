/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
/-!
# Spec theorem for `spqr::chain::{spqr::chain::KeyHistory}::clear`

Clears the key history via `Vec::clear`, leaving `data.length = 0`.

**Source**: spqr/src/chain.rs -/

open Aeneas Aeneas.Std

namespace spqr.chain.KeyHistory

/--
**Spec theorem for `spqr.chain.KeyHistory.clear`**:

After clearing, `result.data.length = 0`. Always succeeds since `Vec::clear` is infallible. -/
@[step]
theorem clear_spec (self : chain.KeyHistory) :
    clear self ⦃ fun (result : chain.KeyHistory) =>
      result.data.length = 0 ⦄ := by
  unfold clear
  step*

end spqr.chain.KeyHistory
