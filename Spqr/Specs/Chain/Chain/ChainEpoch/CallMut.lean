/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import SrcTranslated.Funs
public import Spqr.Specs.Chain.ChainEpochDirection.IntoPb
public import Spqr.Specs.Chain.ChainEpochDirection.FunctionalModels
public import Spqr.Specs.Chain.Chain.FunctionalModels

/-! # Spec theorem for `spqr::chain::{spqr::chain::Chain}::into_pb::closure::call_mut`

Closure mapping `ChainEpoch` to `pqrpb::chain::Epoch` by calling `into_pb` on
`send`/`recv` and wrapping in `some`. Closure state `c` is unchanged. Infallible.

**Source**: spqr/src/chain.rs -/

@[expose] public section

open Aeneas Aeneas.Std Result spqr

namespace spqr.chain.Chain.into_pb.closure.Insts.CoreOpsFunctionFnMutTupleChainEpochEpoch

/-- **Spec theorem for `spqr.chain.Chain.into_pb.closure.Insts.
CoreOpsFunctionFnMutTupleChainEpochEpoch.call_mut`**:

The result is exactly the functional model `Chain.FunctionalModels.epochIntoPb tupled_args`.
Closure `c` is unchanged. Always succeeds. -/
@[step]
theorem call_mut_spec (c : chain.Chain.into_pb.closure) (tupled_args : chain.ChainEpoch) :
    call_mut c tupled_args ⦃ (result : proto.pq_ratchet.chain.Epoch ×
      chain.Chain.into_pb.closure) =>
      result.1 = Chain.FunctionalModels.epochIntoPb tupled_args ∧ result.2 = c ⦄ := by
  unfold call_mut Chain.FunctionalModels.epochIntoPb
  step*

end spqr.chain.Chain.into_pb.closure.Insts.CoreOpsFunctionFnMutTupleChainEpochEpoch
