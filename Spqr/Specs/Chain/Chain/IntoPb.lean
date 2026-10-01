/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Chain.Chain.ChainEpoch.CallMut
import Spqr.Specs.Chain.Chain.ChainEpoch.CallOnce
import Spqr.Specs.Chain.ChainEpochDirection.IntoPb
import Spqr.Specs.Chain.FunctionalModels
import Spqr.Specs.Aeneas.MapCollectBridge

/-! # Spec theorem for `spqr::chain::{spqr::chain::Chain}::into_pb`

Converts a `Chain` from the in-memory Rust form (`chain.Chain`) into the protobuf form
(`proto.pq_ratchet.Chain`) used for saving it to disk. The `current_epoch`, `send_epoch`,
`next_root` fields are copied verbatim, `params` is wrapped in `some`, `direction` is
converted via `From<Direction> for i32`, and `links` are produced by mapping each
`ChainEpoch` through `ChainEpochDirection::into_pb` on its `send` and `recv` fields.
The reverse direction is `from_pb`.

**Source**: spqr/src/chain.rs (lines 415:4-431:5)
-/

open Aeneas Aeneas.Std Result spqr

namespace spqr.chain.Chain

/-- **Spec theorem for `spqr.chain.Chain.into_pb`**:
• The call always succeeds (no panic).
• The result is exactly the functional model `FunctionalModels.intoPb self dirI32` where
  `dirI32` is the `I32` obtained from `self.dir` via `core.convert.IntoFrom.into`.

The proof is blocked on the Aeneas iterator bridge (aeneas#1043) for the
`into_iter`/`map`/`collect` pipeline over `VecDeque` and uses `sorry`.

**Source**: spqr/src/chain.rs (lines 415:4-431:5) -/
@[step]
theorem into_pb_spec (self : chain.Chain) :
    into_pb self ⦃ (result : proto.pq_ratchet.Chain) =>
      ∃ dirI32,
        core.convert.IntoFrom.into I32.Insts.CoreConvertFromDirection self.dir =
          ok dirI32 ∧
        result = FunctionalModels.intoPb self dirI32 ⦄ := by
  unfold into_pb FunctionalModels.intoPb
  sorry -- Blocked on https://github.com/AeneasVerif/aeneas/issues/1043

end spqr.chain.Chain
