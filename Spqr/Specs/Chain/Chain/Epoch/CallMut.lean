/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Chain.ChainEpochDirection.FromPb
/-!
# Spec theorem for `spqr::chain::{spqr::chain::Chain}::from_pb::closure#1::call_mut`

Closure converting a protobuf `Epoch` into `ChainEpoch` by unwrapping and converting
its `send`/`recv` fields. Returns `Err StateDecode` if either field is `none`.

**Source**: spqr/src/chain.rs -/

open Aeneas Aeneas.Std Result spqr

namespace spqr.chain.Chain.from_pb.closure_1.Insts
namespace CoreOpsFunctionFnMutTupleEpochResultChainEpochError

/-- **Spec theorem for `spqr.chain.Chain.from_pb.closure_1.Insts
.CoreOpsFunctionFnMutTupleEpochResultChainEpochError.call_mut`**:

Converts a protobuf `Epoch` to `ChainEpoch`. Returns `Ok` with repackaged `send`/`recv`
directions if both are `some`, otherwise `Err StateDecode`. Closure value `c` is unchanged. -/
@[step]
theorem call_mut_spec (c : chain.Chain.from_pb.closure_1)
    (tupled_args : proto.pq_ratchet.chain.Epoch) :
    call_mut c tupled_args ⦃ (result : (core.result.Result chain.ChainEpoch Error) ×
      chain.Chain.from_pb.closure_1) =>
      match tupled_args.send, tupled_args.recv with
      | some s, some r =>
          result.1 = core.result.Result.Ok {
            send := { ctr := s.ctr, next := s.next, prev := { data := s.prev } },
            recv := { ctr := r.ctr, next := r.next, prev := { data := r.prev } } } ∧
          result.2 = c
      | _, _ =>
          result.1 = core.result.Result.Err Error.StateDecode ∧
          result.2 = c ⦄ := by
  unfold call_mut
  match tupled_args.send, tupled_args.recv with
  | some s, some r =>
    simp only [core.option.Option.ok_or,
      core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok]
    step*
    rcases r1 with ⟨ced1⟩ | ⟨e1⟩
    · obtain ⟨hc1, hn1, hp1⟩ := r1_post
      simp only [bind_tc_ok]
      step*
      rcases r3 with ⟨ced2⟩ | ⟨e2⟩
      · obtain ⟨hc2, hn2, hp2⟩ := r3_post
        simp only [bind_tc_ok, WP.spec_ok]
        simp only [← hc1, ← hn1, ← hp1, ← hc2, ← hn2, ← hp2]
      · exact absurd r3_post (by simp)
    · exact absurd r1_post (by simp)
  | some _, none =>
    simp only [core.option.Option.ok_or,
      core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok]
    step*
    rcases r1 with ⟨ced1⟩ | ⟨e1⟩
    · simp only [bind_tc_ok,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from, WP.spec_ok]
    · exact absurd r1_post (by simp)
  | none, _ =>
    simp only [core.option.Option.ok_or,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
    trivial
end CoreOpsFunctionFnMutTupleEpochResultChainEpochError
end spqr.chain.Chain.from_pb.closure_1.Insts
