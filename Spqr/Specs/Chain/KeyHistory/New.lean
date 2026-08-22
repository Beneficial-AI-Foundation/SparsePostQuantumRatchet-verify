/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Chain.KeyHistory.KEY_SIZE
/-! # Spec theorem for `spqr::chain::{spqr::chain::KeyHistory}::new`

Constructs an empty `KeyHistory` with `data.length = 0`. Pre-allocates capacity for 72 bytes
(`KEY_SIZE * 2`) but stores no data. Infallible since `36 * 2` fits in `usize`.

**Source**: spqr/src/chain.rs -/

open Aeneas Aeneas.Std

namespace spqr.chain.KeyHistory

/-- **Spec theorem for `spqr.chain.KeyHistory.new`**:

Postcondition: `result.data.length = 0` (empty history, no stored keys).
Proof unfolds `new`, resolves via `step*` and `KEY_SIZE_spec`. -/
@[step]
theorem new_spec :
    new ⦃ (result : chain.KeyHistory) =>
      result.data.length = 0 ⦄ := by
  unfold new
  step*
  simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new, alloc.vec.Vec.length]

end spqr.chain.KeyHistory
