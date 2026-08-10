/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Spqr.Specs.External

/-! # PROP-9: Epoch Monotonicity

Specification and proof for `chain.Chain.add_epoch` (PROP-9 from
`docs/mlkembraid_spec/1_scka_interface.md`).

Given precondition `es.epoch = c.current_epoch + 1 ∧ c.current_epoch < U64.max`,
the post-state satisfies `c'.current_epoch = es.epoch`.

`Chain::add_epoch` returns `()` and mutates `self` in Rust
(`chain.rs:350`). The Aeneas extraction models this as a state-passing
function returning the new `Chain`. The Lean postcondition is over the
*post-state*, not over a `result` field.

**Source**: spqr/src/chain.rs (lines 350:4-369:5)
-/

open Aeneas Aeneas.Std Result

namespace spqr

/-! ## Helper specs for intermediate defined functions -/

/-- `Direction.switch` always succeeds: A2B ↦ B2A and B2A ↦ A2B. -/
@[step]
theorem Direction.switch_spec (d : proto.pq_ratchet.Direction) :
    Direction.switch d ⦃ _ => True ⦄ := by
  unfold Direction.switch
  match d with
  | .A2B => simp only [WP.spec, WP.theta, WP.wp_return]
  | .B2A => simp only [WP.spec, WP.theta, WP.wp_return]

/-- `KeyHistory.KEY_SIZE` evaluates to 36. -/
@[step]
theorem chain.KeyHistory.KEY_SIZE_spec :
    chain.KeyHistory.KEY_SIZE ⦃ i => i.val = 36 ⦄ := by
  unfold chain.KeyHistory.KEY_SIZE
  step*

/-- `KeyHistory.new` always succeeds. -/
@[step]
theorem chain.KeyHistory.new_spec :
    chain.KeyHistory.new ⦃ _ => True ⦄ := by
  unfold chain.KeyHistory.new
  step*

/-- `ChainEpochDirection.new` always succeeds for any input slice. -/
@[step]
theorem chain.ChainEpochDirection.new_spec (k : Slice Std.U8) :
    chain.ChainEpochDirection.new k ⦃ _ => True ⦄ := by
  unfold chain.ChainEpochDirection.new
  step*

/-- `Chain.ced_for_direction` always succeeds when the generator
slice has at least 96 bytes (which it always does in `add_epoch`
since `genr8r = Array.repeat 96 0`). -/
@[step]
theorem chain.Chain.ced_for_direction_spec
  (genr8r : Slice Std.U8) (dir : proto.pq_ratchet.Direction)
  (hlen : genr8r.length ≥ 96) :
    chain.Chain.ced_for_direction genr8r dir ⦃ _ => True ⦄ := by
  unfold chain.Chain.ced_for_direction
  match dir with
  | .A2B => simp only []; step*
  | .B2A => simp only []; step*

/-! ## PROP-9: Main theorem -/

/-- **PROP-9 — Epoch Monotonicity.**

If `chain.Chain.add_epoch` succeeds, then the post-state's
`current_epoch` equals `epoch_secret.epoch`.

The preconditions (epoch = current + 1, no overflow) are encoded
in the function body via `massert` and U64 arithmetic. We express
them explicitly as hypotheses; they correspond exactly to the
spec's §3.8 condition and the `hax_lib::assume!` in the Rust source.
-/
@[step]
theorem chain.Chain.add_epoch_spec
  (self : chain.Chain) (epoch_secret : EpochSecret)
  (h_no_overflow : self.current_epoch.val + 1 ≤ U64.max)
  (h_epoch : epoch_secret.epoch.val = self.current_epoch.val + 1) :
    chain.Chain.add_epoch self epoch_secret
      ⦃ c' => c'.current_epoch = epoch_secret.epoch ⦄ := by
  unfold chain.Chain.add_epoch
  step*

end spqr
