/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Chain.Chain.ChainEpoch.CallMut
/-! # Spec theorem for `spqr::chain::{spqr::chain::Chain}::into_pb::closure::call_once`

`FnOnce::call_once` for the `Chain::into_pb` closure. Delegates to `call_mut`,
discards the closure component, and returns the protobuf `Epoch` with `send` and
`recv` wrapped in `some`. Infallible for any `ChainEpoch` input.

**Source**: spqr/src/chain.rs -/

open Aeneas Aeneas.Std Result spqr

namespace spqr.chain.Chain.into_pb.closure.Insts.CoreOpsFunctionFnOnceTupleChainEpochEpoch

/-- **Spec theorem for `spqr.chain.Chain.into_pb.closure.Insts.
CoreOpsFunctionFnOnceTupleChainEpochEpoch.call_once`**:

Delegates to `call_mut`, discards the closure, and returns an `Epoch` whose `send`
and `recv` fields are `some { ctr, next, prev }` built from `ce`. Always succeeds.
Proof unfolds `call_once` then applies `call_mut_spec` via `step*`. -/
@[step]
theorem call_once_spec (c : chain.Chain.into_pb.closure) (ce : chain.ChainEpoch) :
    call_once c ce ⦃ (result : proto.pq_ratchet.chain.Epoch) =>
      result.send = some {
        ctr  := ce.send.ctr,
        next := ce.send.next,
        prev := ce.send.prev.data } ∧
      result.recv = some {
        ctr  := ce.recv.ctr,
        next := ce.recv.next,
        prev := ce.recv.prev.data } ⦄ := by
  unfold call_once
  step*

end spqr.chain.Chain.into_pb.closure.Insts.CoreOpsFunctionFnOnceTupleChainEpochEpoch
