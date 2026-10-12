/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import SrcTranslated.Funs
public import Spqr.Specs.Chain.ChainEpochDirection.FromPb
public import Spqr.Specs.Chain.Chain.FunctionalModels

/-! # Spec theorem for `spqr::chain::{spqr::chain::Chain}::from_pb`

Converts a `Chain` from the protobuf form (`proto.pq_ratchet.Chain`) back into the
in-memory Rust form (`chain.Chain`). The `direction` is decoded via `directionFromI32`,
`links` are mapped through `ChainEpochDirection.from_pb` on each epoch's `send`/`recv`
fields, and `params` is unwrapped from `Option`. The reverse direction is `into_pb`.

**Source**: spqr/src/chain.rs (lines 434:4-452:5)
-/

@[expose] public section

open Aeneas Aeneas.Std Result spqr

namespace spqr.chain.Chain

/-- **Spec theorem for `spqr.chain.Chain.from_pb`**:
• The call always succeeds (no panic): the direction decode, every epoch conversion and the
  `params` unwrap can only produce `Err StateDecode`, never a panic.
• The result is exactly the functional model `FunctionalModels.fromPb pb`.
**Source**: spqr/src/chain.rs (lines 434:4-452:5) -/
@[step]
theorem from_pb_spec (pb : proto.pq_ratchet.Chain) :
    from_pb pb ⦃ (result : core.result.Result chain.Chain Error) =>
      result = FunctionalModels.fromPb pb ⦄ := by
  unfold from_pb FunctionalModels.fromPb
  sorry -- Blocked on https://github.com/AeneasVerif/aeneas/issues/1043

end spqr.chain.Chain
