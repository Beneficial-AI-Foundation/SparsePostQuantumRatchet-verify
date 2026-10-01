/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Chain.ChainEpochDirection.FromPb
import Spqr.Specs.Chain.FunctionalModels

/-! # Spec theorem for `spqr::chain::{spqr::chain::Chain}::from_pb`

Converts a `Chain` from the protobuf form (`proto.pq_ratchet.Chain`) back into the
in-memory Rust form (`chain.Chain`). The `direction` is converted via `try_from`,
`links` are mapped through `ChainEpochDirection.from_pb` on each epoch's `send`/`recv`
fields, and `params` is unwrapped from `Option`. The reverse direction is `into_pb`.

**Source**: spqr/src/chain.rs (lines 434:4-452:5)
-/

open Aeneas Aeneas.Std Result spqr

namespace spqr.chain.Chain

/-- **Spec theorem for `spqr.chain.Chain.from_pb`**:
• The call always succeeds (no panic).
• The result is exactly the functional model `FunctionalModels.fromPb pb dirResult` where
  `dirResult` is the result of converting `pb.direction` via `try_from` and `map_err`.

The proof is blocked on the Aeneas iterator bridge (aeneas#1043) for the
`into_iter`/`map`/`collect` pipeline over `Vec` and uses `sorry`.

**Source**: spqr/src/chain.rs (lines 434:4-452:5) -/
@[step]
theorem from_pb_spec (pb : proto.pq_ratchet.Chain) :
    from_pb pb ⦃ (result : core.result.Result chain.Chain Error) =>
      ∃ dirResult,
        result = FunctionalModels.fromPb pb dirResult ⦄ := by
  unfold from_pb FunctionalModels.fromPb
  sorry -- Blocked on https://github.com/AeneasVerif/aeneas/issues/1043

end spqr.chain.Chain
