/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Chain.Chain.ChainEpoch.CallMut
import Spqr.Specs.Chain.ChainEpochDirection.FunctionalModels
import Spqr.Specs.Chain.FunctionalModels

/-! # Spec theorem for `spqr::chain::{spqr::chain::Chain}::into_pb::closure::call_once`

`FnOnce::call_once` for the `Chain::into_pb` closure. Delegates to `call_mut`,
discards the closure component, and returns the protobuf `Epoch` with `send` and
`recv` wrapped in `some`. Infallible for any `ChainEpoch` input.

**Source**: spqr/src/chain.rs -/

open Aeneas Aeneas.Std Result spqr

namespace spqr.chain.Chain.into_pb.closure.Insts.CoreOpsFunctionFnOnceTupleChainEpochEpoch

/-- **Spec theorem for `spqr.chain.Chain.into_pb.closure.Insts.
CoreOpsFunctionFnOnceTupleChainEpochEpoch.call_once`**:

• The call always succeeds (no panic).
• The result is exactly the functional model `Chain.FunctionalModels.epochIntoPb ce`. -/
@[step]
theorem call_once_spec (c : chain.Chain.into_pb.closure) (ce : chain.ChainEpoch) :
    call_once c ce ⦃ (result : proto.pq_ratchet.chain.Epoch) =>
      result = Chain.FunctionalModels.epochIntoPb ce ⦄ := by
  unfold call_once
  step*

end spqr.chain.Chain.into_pb.closure.Insts.CoreOpsFunctionFnOnceTupleChainEpochEpoch
