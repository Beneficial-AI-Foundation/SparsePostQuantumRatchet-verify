/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Spqr.Specs.External

/-! # PROP-17 / PROP-17b: Key Jump Guard and Key Already Requested

Specification and proofs for the `ChainEpochDirection.key` guards
(PROP-17 and PROP-17b from `docs/mlkembraid_spec/1_scka_interface.md`).

The function dispatches on `at1.cmp(&self.ctr)`:
- **Equal** (PROP-17b): returns `Err(KeyAlreadyRequested(at1))`
- **Greater** with excessive jump (PROP-17): returns `Err(KeyJump(ctr, at1))`

**Source**: spqr/src/chain.rs (lines 247:4-296:5)
-/

open Aeneas Aeneas.Std Result

namespace spqr

/-! ## Helper specs -/

/-- `OrdU32.cmp` lifted into the `Result` monad yields the standard `compare`
on natural-number values. Required because `lift` is not reducible, so
`step*` cannot look through it without a dedicated spec. -/
@[step]
theorem OrdU32_cmp_spec (x y : Std.U32) :
    lift (core.cmp.impls.OrdU32.cmp x y)
      ⦃ o => o = compare x.val y.val ⦄ := by
  simp only [lift, core.cmp.impls.OrdU32.cmp, WP.spec, WP.theta, WP.wp_return]

/-! ## PROP-17b: Key Already Requested -/

/-- **PROP-17b — Key Already Requested.**

When `at1 = self.ctr`, `ChainEpochDirection.key` returns
`Err(KeyAlreadyRequested at1)` and the state is unchanged. -/
@[step]
theorem chain.ChainEpochDirection.key_already_requested
    (self : chain.ChainEpochDirection) (at1 : Std.U32)
    (params : proto.pq_ratchet.ChainParams)
    (h_eq : at1 = self.ctr) :
    chain.ChainEpochDirection.key self at1 params ⦃ r =>
      r.1 = core.result.Result.Err (Error.KeyAlreadyRequested at1) ∧
      r.2 = self ⦄ := by
  unfold chain.ChainEpochDirection.key
  simp [h_eq, lift, core.cmp.impls.OrdU32.cmp, WP.spec, WP.theta, WP.wp_return]

/-! ## PROP-17: Key Jump Guard -/

/-- **PROP-17 — Key Jump Limit.**

When `at1 > self.ctr` and the gap `at1 - self.ctr` exceeds
`max_jump_or_default(params)`, the function returns
`Err(KeyJump(ctr, at1))` and the state is unchanged.

The two hypotheses `h_jump_pos` and `h_jump_zero` cover both
branches of `max_jump_or_default`: when `params.max_jump > 0`
(custom limit) and when it falls back to the default (25000). -/
@[step]
theorem chain.ChainEpochDirection.key_jump_guard
    (self : chain.ChainEpochDirection) (at1 : Std.U32)
    (params : proto.pq_ratchet.ChainParams)
    (h_gt : at1 > self.ctr)
    (h_jump_pos : params.max_jump > 0#u32 →
        at1.val - self.ctr.val > params.max_jump.val)
    (h_jump_zero : ¬(params.max_jump > 0#u32) →
        at1.val - self.ctr.val > chain.DEFAULT_CHAIN_PARAMS.max_jump.val) :
    chain.ChainEpochDirection.key self at1 params ⦃ r =>
      r.1 = core.result.Result.Err (Error.KeyJump self.ctr at1) ∧
      r.2 = self ⦄ := by
  unfold chain.ChainEpochDirection.key chain.ChainParams.max_jump_or_default
  step*
  · -- .lt branch: impossible since at1 > self.ctr
    exfalso
    have h_cmp : compare (↑at1 : ℕ) ↑self.ctr = Ordering.gt := by
      rw [Nat.compare_eq_gt]; scalar_tac
    simp_all -- terminal: derives False from contradictory Ordering hypotheses
  · -- .gt branch: split on max_jump_or_default cases, then show jump check fires
    split <;> (step*; try scalar_tac)

end spqr
