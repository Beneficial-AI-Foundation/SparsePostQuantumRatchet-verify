/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Chain.ChainEpochDirection.IntoPb
import Spqr.Specs.Chain.ChainEpochDirection.FunctionalModels

/-! # Spec theorem for `spqr::chain::{spqr::chain::Chain}::into_pb::closure::call_mut`

Closure mapping `ChainEpoch` to `pqrpb::chain::Epoch` by calling `into_pb` on
`send`/`recv` and wrapping in `some`. Closure state `c` is unchanged. Infallible.

**Source**: spqr/src/chain.rs -/

open Aeneas Aeneas.Std Result spqr

namespace spqr.chain.Chain.into_pb.closure.Insts.CoreOpsFunctionFnMutTupleChainEpochEpoch

/-- **Spec theorem for `spqr.chain.Chain.into_pb.closure.Insts.
CoreOpsFunctionFnMutTupleChainEpochEpoch.call_mut`**:

Maps `tupled_args : ChainEpoch` to a `proto.pq_ratchet.chain.Epoch` whose `send`/`recv`
are `some (FunctionalModels.intoPb ...)` of the corresponding directions. Returns
closure `c` unchanged. Always succeeds. -/
@[step]
theorem call_mut_spec (c : chain.Chain.into_pb.closure) (tupled_args : chain.ChainEpoch) :
    call_mut c tupled_args ⦃ (result : proto.pq_ratchet.chain.Epoch ×
    chain.Chain.into_pb.closure) =>
      result.1.send = some
        (chain.ChainEpochDirection.FunctionalModels.intoPb tupled_args.send) ∧
      result.1.recv = some
        (chain.ChainEpochDirection.FunctionalModels.intoPb tupled_args.recv) ∧
      result.2 = c ⦄ := by
  unfold call_mut
  step*

end spqr.chain.Chain.into_pb.closure.Insts.CoreOpsFunctionFnMutTupleChainEpochEpoch
