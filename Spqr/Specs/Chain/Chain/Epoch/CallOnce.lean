/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Chain.Chain.Epoch.CallMut
/-!
# Spec theorem for `spqr::chain::{spqr::chain::Chain}::from_pb::closure#1::call_once`

`FnOnce` wrapper that delegates to `call_mut`, discards closure state, and returns
the inner `Result<ChainEpoch, Error>`. Returns `Ok { send, recv }` when both fields
are `some`, or `Err StateDecode` if either is `none`.

**Source**: spqr/src/chain.rs -/

open Aeneas Aeneas.Std Result spqr

namespace spqr.chain.Chain.from_pb.closure_1.Insts
namespace CoreOpsFunctionFnOnceTupleEpochResultChainEpochError

/-- **Spec theorem for `spqr.chain.Chain.from_pb.closure_1.
Insts.CoreOpsFunctionFnOnceTupleEpochResultChainEpochError.call_once`**:

Delegates to `call_mut`, drops closure state, and returns the inner result.
Both `some` → `Ok { send, recv }`; either `none` → `Err StateDecode`.
Outer `Result` always succeeds. Proof by unfolding and `step*` with `call_mut_spec`. -/
@[step]
theorem call_once_spec (c : chain.Chain.from_pb.closure_1)
    (e : proto.pq_ratchet.chain.Epoch) :
    call_once c e ⦃ (result : core.result.Result chain.ChainEpoch Error) =>
      match e.send, e.recv with
      | some s, some r =>
          result = core.result.Result.Ok {
            send := { ctr := s.ctr, next := s.next, prev := { data := s.prev } },
            recv := { ctr := r.ctr, next := r.next, prev := { data := r.prev } } }
      | _, _ =>
          result = core.result.Result.Err Error.StateDecode ⦄ := by
  unfold call_once
  step*
  exact r_post

end CoreOpsFunctionFnOnceTupleEpochResultChainEpochError
end spqr.chain.Chain.from_pb.closure_1.Insts
