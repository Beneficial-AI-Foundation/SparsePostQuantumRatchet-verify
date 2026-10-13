/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import SrcTranslated.Funs
public import Spqr.Specs.Chain.ChainEpochDirection.FromPb
public import Spqr.Specs.Chain.ChainEpochDirection.FunctionalModels
public import Spqr.Specs.Chain.Chain.FunctionalModels

/-! # Spec theorem for `spqr::chain::{spqr::chain::Chain}::from_pb::closure#1::call_mut`

Closure converting a protobuf `Epoch` into `ChainEpoch` by unwrapping and converting
its `send`/`recv` fields. Returns `Err StateDecode` if either field is `none`.

**Source**: spqr/src/chain.rs -/

@[expose] public section

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
  simp only [Chain.FunctionalModels.epochFromPb, Option.map]
  match tupled_args.send, tupled_args.recv with
  | some s, some r =>
    simp only [core.option.Option.ok_or]
    -- Case on the two direction conversions, keeping the model `fromPb` folded; its only
    -- error is `StateDecode` (`fromPb_err`).
    cases hs : ChainEpochDirection.FunctionalModels.fromPb s with
    | Err e =>
      have := ChainEpochDirection.FunctionalModels.fromPb_err _ _ hs
      step*
    | Ok sd =>
      cases hr : ChainEpochDirection.FunctionalModels.fromPb r with
      | Err e =>
        have := ChainEpochDirection.FunctionalModels.fromPb_err _ _ hr
        step*
      | Ok rd => step*
  | some s, none =>
    simp only [core.option.Option.ok_or]
    cases hs : ChainEpochDirection.FunctionalModels.fromPb s with
    | Err e =>
      have := ChainEpochDirection.FunctionalModels.fromPb_err _ _ hs
      step*
    | Ok sd => step*
  | none, _ =>
    simp only [core.option.Option.ok_or]
    step*
end CoreOpsFunctionFnMutTupleEpochResultChainEpochError
end spqr.chain.Chain.from_pb.closure_1.Insts
