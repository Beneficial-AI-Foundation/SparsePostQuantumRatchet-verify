/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Lib.ChainFromVersionNegotiation
import Spqr.Specs.Chain.Chain.FromPb
/-!
# Spec theorem for `spqr::chain_from`

`chain_from` reconstructs a `Chain` from an optional serialised protobuf `Chain` message
and an optional `VersionNegotiation` message.  Its logic is a nested pattern match:

  1. If `pb = some pb1`, deserialise the chain via `Chain::from_pb(pb1)` and propagate
     any error with the `?` operator.
  2. If `pb = none` and `vn = some vn1`, fall back to constructing a fresh chain via
     `chain_from_version_negotiation(vn1)`.
  3. If both are `none`, return `Err(Error::ChainNotAvailable)`.

The function can fail in exactly two ways originating from this level:
  - `Err ChainNotAvailable` — both `pb` and `vn` are `none`.
  - Any error propagated from `Chain::from_pb` or `chain_from_version_negotiation`.

**Source**: spqr/src/lib.rs (lines 343:0-354:1)
-/

open Aeneas Aeneas.Std Result spqr crypto

namespace spqr

/-- Functional model of `chain_from`:
- `some pb, _`    → result of `Chain.from_pb pb`
- `none, some vn` → result of `chainFromVersionNegotiation vn`
- `none, none`    → `Err ChainNotAvailable` -/
noncomputable def chainFrom
    (pb : Option proto.pq_ratchet.Chain)
    (vn : Option proto.pq_ratchet.pq_ratchet_state.VersionNegotiation)
    : Result (core.result.Result chain.Chain Error) :=
  match pb with
  | some pb1 => ok (chain.Chain.FunctionalModels.fromPb pb1)
  | none =>
    match vn with
    | none     => ok (.Err Error.ChainNotAvailable)
    | some vn1 => chainFromVersionNegotiation vn1

/-- **Spec theorem for `spqr.chain_from`**:

• `some pb, _`    → result equals `FunctionalModels.fromPb pb`.
• `none, some vn` → result equals `chainFromVersionNegotiation vn`.
• `none, none`    → `Err ChainNotAvailable`.

**Source**: spqr/src/lib.rs (lines 343:0-354:1) -/
@[step]
theorem chain_from_spec
    (pb : Option proto.pq_ratchet.Chain)
    (vn : Option proto.pq_ratchet.pq_ratchet_state.VersionNegotiation) :
    chain_from pb vn ⦃ (result : core.result.Result chain.Chain Error) =>
      chainFrom pb vn = ok result ⦄ := by
  unfold chainFrom
  unfold chain_from
  match pb, vn with
  | none, none =>
    simp only [WP.spec_ok]
  | none, some vn1 =>
    simp only []
    have hspec := chain_from_version_negotiation_spec vn1
    revert hspec
    unfold WP.spec WP.theta
    cases hm : chain_from_version_negotiation vn1 with
    | ok r =>
      simp only [WP.wp_return]
      intro hpost
      exact hpost
    | fail e =>
      intro h; exact absurd h id
    | div =>
      intro h; exact absurd h id
  | some pb1, _ =>
    simp only []
    have hspec := chain.Chain.from_pb_spec pb1
    unfold WP.spec WP.theta at hspec
    cases hm : chain.Chain.from_pb pb1 with
    | ok r =>
      cases r with
      | Ok v =>
        simp only [bind_tc_ok,
          core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame.from, WP.spec_ok]
        rw [hm] at hspec; exact hspec ▸ rfl
      | Err e =>
        simp only [bind_tc_ok,
          core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame.from, WP.spec_ok]
        rw [hm] at hspec; exact hspec ▸ rfl
    | fail e =>
      rw [hm] at hspec
      exact absurd hspec id
    | div =>
      rw [hm] at hspec
      exact absurd hspec id

end spqr
