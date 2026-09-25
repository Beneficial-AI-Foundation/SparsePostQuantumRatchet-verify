/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Lib.ChainFromVersionNegotiation.CallOnce
import Spqr.Specs.Chain.Chain.New
import Spqr.Specs.Proto.PqRatchet.Direction.TryFrom
/-!
# Spec theorem for `spqr::chain_from_version_negotiation`

Builds a `Chain` from a `VersionNegotiation` message by:
1. Converting `vn.direction` to `Direction` via `try_from` (fails → `StateDecode`).
2. Unwrapping `vn.chain_params` via `ok_or` (fails → `ChainNotAvailable`).
3. Calling `Chain::new` with `vn.auth_key`, the direction, and chain params.

**Source**: spqr/src/lib.rs (lines 333:0-341:1)
-/

open Aeneas Aeneas.Std Result spqr crypto

namespace spqr

/-- **Spec theorem for `spqr.chain_from_version_negotiation`**:

Converts direction, unwraps chain params, then calls `Chain.new`.
- Unknown direction → `Err StateDecode`.
- Missing chain params → `Err ChainNotAvailable`.
- Otherwise → result of `Chain.new(auth_key, dir, params)`. -/
@[step]
theorem chain_from_version_negotiation_spec
    (vn : proto.pq_ratchet.pq_ratchet_state.VersionNegotiation) :
    chain_from_version_negotiation vn ⦃ (result : core.result.Result chain.Chain Error) =>
      (∀ e, proto.pq_ratchet.Direction.Insts.CoreConvertTryFromI32UnknownEnumValue.try_from
              vn.direction = ok (core.result.Result.Err e) →
        result = core.result.Result.Err Error.StateDecode) ∧
      (∀ dir, proto.pq_ratchet.Direction.Insts.CoreConvertTryFromI32UnknownEnumValue.try_from
                vn.direction = ok (core.result.Result.Ok dir) →
        vn.chain_params = none →
        result = core.result.Result.Err Error.ChainNotAvailable) ∧
      (∀ dir params,
        proto.pq_ratchet.Direction.Insts.CoreConvertTryFromI32UnknownEnumValue.try_from
          vn.direction = ok (core.result.Result.Ok dir) →
        vn.chain_params = some params →
        chain.Chain.new (alloc.vec.Vec.deref vn.auth_key) dir params = ok result) ⦄ := by
  unfold chain_from_version_negotiation
  step*
  split at r_post
  · subst r_post
    simp only [core.result.Result.map_err_Ok, bind_tc_ok,
      core.result.Result.Insts.CoreOpsTry.branch, core.option.Option.ok_or,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      bind_tc_ok]
    split <;> rename_i v hcp
    · simp only [bind_tc_ok]
      have hcn_spec := chain.Chain.new_spec (alloc.vec.Vec.deref vn.auth_key)
        proto.pq_ratchet.Direction.A2B v
      revert hcn_spec
      unfold WP.spec WP.theta
      cases hm : chain.Chain.new (alloc.vec.Vec.deref vn.auth_key) proto.pq_ratchet.Direction.A2B v
      · simp only [WP.wp_return]
        intro hcn_post
        refine ⟨fun e h => ?_, fun dir h1 h2 => ?_, fun dir params h1 h2 => ?_⟩
        · unfold proto.pq_ratchet.Direction.Insts.CoreConvertTryFromI32UnknownEnumValue.try_from
          at h
          simp_all
        · simp_all
        · unfold proto.pq_ratchet.Direction.Insts.CoreConvertTryFromI32UnknownEnumValue.try_from
          at h1
          simp_all
      · intro h; exact h.elim
      · intro h; exact h.elim
    · simp only [bind_tc_ok, WP.spec_ok]
      unfold proto.pq_ratchet.Direction.Insts.CoreConvertTryFromI32UnknownEnumValue.try_from
      simp_all
  · subst r_post
    simp only [core.result.Result.map_err_Ok, bind_tc_ok,
      core.result.Result.Insts.CoreOpsTry.branch, core.option.Option.ok_or,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      bind_tc_ok]
    split <;> rename_i v hcp
    · simp only [bind_tc_ok]
      have hcn_spec := chain.Chain.new_spec (alloc.vec.Vec.deref vn.auth_key)
        proto.pq_ratchet.Direction.B2A v
      revert hcn_spec
      unfold WP.spec WP.theta
      cases hm : chain.Chain.new (alloc.vec.Vec.deref vn.auth_key) proto.pq_ratchet.Direction.B2A v
      · simp only [WP.wp_return]
        intro hcn_post
        refine ⟨fun e h => ?_, fun dir h1 h2 => ?_, fun dir params h1 h2 => ?_⟩
        · unfold proto.pq_ratchet.Direction.Insts.CoreConvertTryFromI32UnknownEnumValue.try_from
          at h
          simp_all
        · simp_all
        · unfold proto.pq_ratchet.Direction.Insts.CoreConvertTryFromI32UnknownEnumValue.try_from
          at h1
          simp_all
      · intro h; exact h.elim
      · intro h; exact h.elim
    · simp only [bind_tc_ok, WP.spec_ok]
      unfold proto.pq_ratchet.Direction.Insts.CoreConvertTryFromI32UnknownEnumValue.try_from
      simp_all
  · subst r_post
    simp only [core.result.Result.map_err_Err, bind_tc_ok,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
    refine ⟨fun e h => ?_, fun dir h1 h2 => ?_, fun dir params h1 h2 => ?_⟩
    · unfold proto.pq_ratchet.Direction.Insts.CoreConvertTryFromI32UnknownEnumValue.try_from
      at h
      simp_all
    · unfold proto.pq_ratchet.Direction.Insts.CoreConvertTryFromI32UnknownEnumValue.try_from
      at h1
      simp_all
    · unfold proto.pq_ratchet.Direction.Insts.CoreConvertTryFromI32UnknownEnumValue.try_from
      at h1
      simp_all

end spqr
