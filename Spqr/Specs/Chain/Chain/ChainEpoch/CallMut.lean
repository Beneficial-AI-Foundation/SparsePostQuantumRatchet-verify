/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Chain.ChainEpochDirection.IntoPb
/-! # Spec theorem for `spqr::chain::{spqr::chain::Chain}::into_pb::closure::call_mut`

Closure mapping `ChainEpoch` to `pqrpb::chain::Epoch` by calling `into_pb` on
`send`/`recv` and wrapping in `some`. Closure state `c` is unchanged. Infallible.

**Source**: spqr/src/chain.rs -/

open Aeneas Aeneas.Std Result spqr

namespace spqr.chain.Chain.into_pb.closure.Insts.CoreOpsFunctionFnMutTupleChainEpochEpoch

/-- **Spec theorem for `spqr.chain.Chain.into_pb.closure.Insts.
CoreOpsFunctionFnMutTupleChainEpochEpoch.call_mut`**:

Maps `tupled_args : ChainEpoch` to a `proto.pq_ratchet.chain.Epoch` whose `send`/`recv`
are `some (into_pb ...)` of the corresponding directions. Returns closure `c` unchanged.
Always succeeds. Proved by unfolding and `step*` with `ChainEpochDirection.into_pb_spec`. -/
@[step]
theorem call_mut_spec (c : chain.Chain.into_pb.closure) (tupled_args : chain.ChainEpoch) :
    call_mut c tupled_args ⦃ (result : proto.pq_ratchet.chain.Epoch ×
    chain.Chain.into_pb.closure) =>
      result.1.send = some {
        ctr  := tupled_args.send.ctr,
        next := tupled_args.send.next,
        prev := tupled_args.send.prev.data } ∧
      result.1.recv = some {
        ctr  := tupled_args.recv.ctr,
        next := tupled_args.recv.next,
        prev := tupled_args.recv.prev.data } ∧
      result.2 = c ⦄ := by
  unfold call_mut
  step*
  constructor
  · congr 1; obtain ⟨_, _, _⟩ := ed; simp_all
  · congr 1; obtain ⟨_, _, _⟩ := ed1; simp_all

end spqr.chain.Chain.into_pb.closure.Insts.CoreOpsFunctionFnMutTupleChainEpochEpoch
