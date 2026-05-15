/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Spqr.Specs.External

/-! # PROP-14: Send Epoch Cannot Decrease

Specification and proof for the `send_key` epoch guard (PROP-14 from
`docs/mlkembraid_spec/1_scka_interface.md`).

`chain.Chain.send_key(epoch)` returns
`Err(Error.SendKeyEpochDecreased(send_epoch, epoch))` when
`epoch < self.send_epoch`. The chain state is returned unchanged.

**Source**: spqr/src/chain.rs (lines 384:4-407:5)
-/

open Aeneas Aeneas.Std Result

namespace spqr

/-! ## PROP-14: Main theorem -/

/-- **PROP-14 — Send Epoch Cannot Decrease.**

If `epoch < self.send_epoch`, then `chain.Chain.send_key` returns
an inner `Err(SendKeyEpochDecreased self.send_epoch epoch)` and
the chain is unchanged.

The outer `Result` (Aeneas monad) succeeds — this is not a panic,
just a Rust `Err` value returned inside a successful computation.
-/
@[step]
theorem chain.Chain.send_key_epoch_guard
  (self : chain.Chain) (epoch : Std.U64)
  (h : epoch < self.send_epoch) :
    chain.Chain.send_key self epoch
      ⦃ r => r.1 = core.result.Result.Err
               (Error.SendKeyEpochDecreased self.send_epoch epoch)
             ∧ r.2 = self ⦄ := by
  unfold chain.Chain.send_key
  simp only [h, ite_true]
  simp [WP.spec, WP.theta, WP.wp_return] -- full simp set needed to close trivial conjunction

end spqr
