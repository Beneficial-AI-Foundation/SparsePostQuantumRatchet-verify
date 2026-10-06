/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Chain.Chain.ChainEpoch.CallMut
import Spqr.Specs.Chain.Chain.ChainEpoch.CallOnce
import Spqr.Specs.Chain.ChainEpochDirection.IntoPb
import Spqr.Specs.Chain.Chain.FunctionalModels
import Spqr.Specs.Aeneas.MapCollectBridge

/-! # Spec theorem for `spqr::chain::{spqr::chain::Chain}::into_pb`

Converts a `Chain` from the in-memory Rust form (`chain.Chain`) into the protobuf form
(`proto.pq_ratchet.Chain`) used for saving it to disk. The `current_epoch`, `send_epoch`,
`next_root` fields are copied verbatim, `params` is wrapped in `some`, `direction` is
converted via `directionToI32`, and `links` are produced by mapping each live `ChainEpoch`
through `ChainEpochDirection::into_pb` on its `send` and `recv` fields.
The reverse direction is `from_pb`.

**Source**: spqr/src/chain.rs (lines 415:4-431:5)
-/

open Aeneas Aeneas.Std Result spqr

namespace spqr.chain.Chain

/-- **Spec theorem for `spqr.chain.Chain.into_pb`**:
• Succeeds (no panic) whenever the `links` deque is well-formed, i.e. its live window
  `buf[head], …, buf[head+length-1]` lies inside `buf`.
• The result is exactly the functional model `FunctionalModels.intoPb self`.
**Source**: spqr/src/chain.rs (lines 415:4-431:5) -/
@[step]
theorem into_pb_spec (self : chain.Chain)
    (hwf : self.links.head.val + self.links.length.val ≤ self.links.buf.val.length) :
    into_pb self ⦃ (result : proto.pq_ratchet.Chain) =>
      result = FunctionalModels.intoPb self ⦄ := by
  unfold into_pb FunctionalModels.intoPb
  sorry -- Blocked on https://github.com/AeneasVerif/aeneas/issues/1043

end spqr.chain.Chain
