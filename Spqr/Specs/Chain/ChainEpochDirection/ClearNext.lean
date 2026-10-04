/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
/-!
# Spec theorem for `spqr::chain::{spqr::chain::ChainEpochDirection}::clear_next`

Clears `next` via `Vec::clear`, zeroing its length while preserving `ctr` and `prev`. Infallible.

**Source**: spqr/src/chain.rs, lines 314:4-316:5 -/

open Aeneas Aeneas.Std

namespace spqr.chain.ChainEpochDirection

/-- **Spec theorem for `spqr.chain.ChainEpochDirection.clear_next`**:

Clears `self.next`, yielding `result.next = []` with `ctr` and `prev` unchanged. Infallible. -/
@[step]
theorem clear_next_spec (self : chain.ChainEpochDirection) :
    clear_next self ⦃ fun (result : chain.ChainEpochDirection) =>
      result.next.length = 0 ∧
      result.next.val = [] ∧
      result.ctr = self.ctr ∧
      result.prev = self.prev ⦄ := by
  unfold clear_next
  step*

end spqr.chain.ChainEpochDirection
