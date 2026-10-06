/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Chain.ChainEpochDirection.FromPb
import Spqr.Specs.Chain.ChainEpochDirection.FunctionalModels
import Spqr.Specs.Chain.Chain.FunctionalModels

/-! # Spec theorem for `spqr::chain::{spqr::chain::Chain}::from_pb::closure#1::call_mut`

Closure converting a protobuf `Epoch` into `ChainEpoch` by unwrapping and converting
its `send`/`recv` fields. Returns `Err StateDecode` if either field is `none`.

**Source**: spqr/src/chain.rs -/

open Aeneas Aeneas.Std Result spqr

namespace spqr.chain.Chain.from_pb.closure_1.Insts
namespace CoreOpsFunctionFnMutTupleEpochResultChainEpochError

/-- **Spec theorem for `spqr.chain.Chain.from_pb.closure_1.Insts
.CoreOpsFunctionFnMutTupleEpochResultChainEpochError.call_mut`**:

Converts a protobuf `Epoch` to `ChainEpoch` via the functional model `epochFromPb`.
Closure value `c` is unchanged. -/
@[step]
theorem call_mut_spec (c : chain.Chain.from_pb.closure_1)
    (tupled_args : proto.pq_ratchet.chain.Epoch) :
    call_mut c tupled_args ⦃ (result : (core.result.Result chain.ChainEpoch Error) ×
      chain.Chain.from_pb.closure_1) =>
      result.1 = Chain.FunctionalModels.epochFromPb tupled_args ∧ result.2 = c ⦄ := by
  unfold call_mut
  simp only [Chain.FunctionalModels.epochFromPb,
    ChainEpochDirection.FunctionalModels.fromPb, Option.map]
  match tupled_args.send, tupled_args.recv with
  | some s, some r =>
    simp only [core.option.Option.ok_or,
      core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok]
    step*
    rcases r1 with ⟨ced1⟩ | ⟨e1⟩
    · simp only [chain.ChainEpochDirection.FunctionalModels.fromPb,
        core.result.Result.Ok.injEq] at r1_post
      subst r1_post; simp only [bind_tc_ok]
      step*
      rcases r3 with ⟨ced2⟩ | ⟨e2⟩
      · simp only [chain.ChainEpochDirection.FunctionalModels.fromPb,
          core.result.Result.Ok.injEq] at r3_post
        subst r3_post; simp only [bind_tc_ok, WP.spec_ok]
      · exact absurd r3_post (by simp [chain.ChainEpochDirection.FunctionalModels.fromPb])
    · exact absurd r1_post (by simp [chain.ChainEpochDirection.FunctionalModels.fromPb])
  | some _, none =>
    simp only [core.option.Option.ok_or,
      core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok]
    step*
    rcases r1 with ⟨ced1⟩ | ⟨e1⟩
    · simp only [chain.ChainEpochDirection.FunctionalModels.fromPb,
        core.result.Result.Ok.injEq] at r1_post
      subst r1_post; simp only [bind_tc_ok,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from, WP.spec_ok]
    · exact absurd r1_post (by simp [chain.ChainEpochDirection.FunctionalModels.fromPb])
  | none, _ =>
    simp only [core.option.Option.ok_or,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
    trivial
end CoreOpsFunctionFnMutTupleEpochResultChainEpochError
end spqr.chain.Chain.from_pb.closure_1.Insts
