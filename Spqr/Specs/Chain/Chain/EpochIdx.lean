/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
/-!
# Spec theorem for `spqr::chain::{spqr::chain::Chain}::epoch_idx`

Computes the deque index for a given epoch as `links.length - 1 - (current_epoch - epoch)`.
Returns `EpochOutOfRange` if the epoch is in the future or already garbage-collected.

**Source**: spqr/src/chain.rs -/

open Aeneas Aeneas.Std Result spqr

namespace spqr.chain.Chain

/-- **Spec theorem for `spqr.chain.Chain.epoch_idx`**:

On success returns `Ok (links.length - 1 - (current_epoch - epoch))` with `self` unchanged.
Errors with `EpochOutOfRange` when `epoch > current_epoch` or the epoch was garbage-collected. -/
@[step]
theorem epoch_idx_spec (self : chain.Chain) (epoch : U64)
    (h_diff_fits : epoch ≤ self.current_epoch →
      self.current_epoch - epoch ≤ Usize.max) :
    epoch_idx self epoch ⦃ (result : (core.result.Result Usize Error) × chain.Chain) =>
      result.2 = self ∧
      match result.1 with
      | core.result.Result.Ok i =>
          epoch ≤ self.current_epoch ∧
          self.current_epoch - epoch < self.links.length.val ∧
          i = self.links.length - 1 - (self.current_epoch.val - epoch)
      | core.result.Result.Err e =>
          e = Error.EpochOutOfRange epoch ∧
          (epoch > self.current_epoch ∨
           self.current_epoch.val - epoch ≥ self.links.length) ⦄ := by
  unfold epoch_idx
  step* <;> cases System.Platform.numBits_eq <;> scalar_tac

end spqr.chain.Chain
