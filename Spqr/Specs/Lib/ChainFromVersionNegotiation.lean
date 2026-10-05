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
  obtain ⟨r, hr, -⟩ := WP.spec_imp_exists
    (proto.pq_ratchet.Direction.Insts.CoreConvertTryFromI32UnknownEnumValue.try_from_spec
      vn.direction)
  simp only [hr, bind_ok]
  cases r with
  | Err e =>
    simp only [core.result.Result.map_err_Err]
    step*
    simp_all
  | Ok dir =>
    simp only [core.result.Result.map_err_Ok]
    cases hcp : vn.chain_params with
    | none =>
      step* <;> simp_all
    | some p =>
      obtain ⟨c, hc, -⟩ := WP.spec_imp_exists (chain.Chain.new_spec vn.auth_key.deref dir p)
      simp only [core.result.Result.Insts.CoreOpsTry.branch, core.option.Option.ok_or, bind_ok, hc,
        WP.spec_ok]
      simp_all

end spqr
