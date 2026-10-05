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
    simp only [core.option.Option.ok_or]
    step* <;> grind [cases ChainEpochDirection]
  | some _, none =>
    simp only [core.option.Option.ok_or]
    step*
    grind
  | none, _ =>
    simp only [core.option.Option.ok_or]
    step*
end CoreOpsFunctionFnMutTupleEpochResultChainEpochError
end spqr.chain.Chain.from_pb.closure_1.Insts
