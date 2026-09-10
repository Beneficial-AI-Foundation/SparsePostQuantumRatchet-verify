/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
/-!
# Spec theorem for `spqr::chain::{spqr::chain::ChainEpochDirection}::from_pb`

Converts a protobuf `EpochDirection` into `ChainEpochDirection` via field-by-field
repackaging (`ctr`, `next` copied; `prev` rewrapped as `KeyHistory`). Always succeeds
(no validation). Inverse of `into_pb`.

**Source**: spqr/src/chain.rs (lines 306:4-312:5)
-/

open Aeneas Aeneas.Std Result spqr

namespace spqr.chain.ChainEpochDirection

/-- **Spec theorem for `spqr.chain.ChainEpochDirection.from_pb`**:

Always returns `Ok ced` with `ced.ctr = pb.ctr`, `ced.next = pb.next`, and
`ced.prev = { data := pb.prev }`. Never errors. Proof by unfolding + `step*`.

**Source**: spqr/src/chain.rs (lines 306:4-312:5)
-/
@[step]
theorem from_pb_spec (pb : proto.pq_ratchet.chain.epoch.EpochDirection) :
    from_pb pb ⦃ (result : core.result.Result chain.ChainEpochDirection Error) =>
      match result with
      | core.result.Result.Ok ced =>
        ced.ctr = pb.ctr ∧ ced.next = pb.next ∧ ced.prev = { data := pb.prev }
      | core.result.Result.Err _ => False ⦄ := by
  unfold from_pb
  step*

end spqr.chain.ChainEpochDirection
