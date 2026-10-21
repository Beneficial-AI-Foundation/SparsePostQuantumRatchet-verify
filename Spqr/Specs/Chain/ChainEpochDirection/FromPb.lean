/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import SrcTranslated.Funs
public import Spqr.Specs.Chain.ChainEpochDirection.FunctionalModels

/-! # Spec theorem for `spqr::chain::{spqr::chain::ChainEpochDirection}::from_pb`

Converts a `ChainEpochDirection` from the protobuf form
(`proto.pq_ratchet.chain.epoch.EpochDirection`) back into the in-memory Rust form
(`chain.ChainEpochDirection`). The `ctr` and `next` fields are copied verbatim and
`prev` is rewrapped as a `KeyHistory`. Since upstream v1.6.0 a non-empty `next` must have
length 32, otherwise the conversion returns `Err Error::StateDecode`. The reverse direction is
`into_pb`.

**Source**: spqr/src/chain.rs (lines 306:4-312:5)
-/

@[expose] public section

open Aeneas Aeneas.Std Result spqr

namespace spqr.chain.ChainEpochDirection

/-- **Spec theorem for `spqr.chain.ChainEpochDirection.from_pb`**:
• The call never panics.
• The result is exactly the functional model `FunctionalModels.fromPb pb` (which returns
  `Err Error.StateDecode` when `pb.next` is non-empty and not of length 32). -/
@[step]
theorem from_pb_spec (pb : proto.pq_ratchet.chain.epoch.EpochDirection) :
    from_pb pb ⦃ (result : core.result.Result chain.ChainEpochDirection Error) =>
      result = FunctionalModels.fromPb pb ⦄ := by
  unfold from_pb FunctionalModels.fromPb
  step*

end spqr.chain.ChainEpochDirection
