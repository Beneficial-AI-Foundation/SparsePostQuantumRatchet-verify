/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Chain.ChainEpochDirection.FunctionalModels

/-! # Spec theorem for `spqr::chain::{spqr::chain::ChainEpochDirection}::into_pb`

Converts a `ChainEpochDirection` from the in-memory Rust form
(`chain.ChainEpochDirection`) into the protobuf form
(`proto.pq_ratchet.chain.epoch.EpochDirection`). The `ctr` and `next` fields are
copied verbatim and `prev` is unwrapped to `prev.data`. The reverse direction is
`from_pb`.

**Source**: spqr/src/chain.rs (lines 298:4-304:5)
-/

open Aeneas Aeneas.Std Result spqr

namespace spqr.chain.ChainEpochDirection

/-- **Spec theorem for `spqr.chain.ChainEpochDirection.into_pb`**:
• The call always succeeds (no panic).
• The result is exactly the functional model `FunctionalModels.intoPb self`. -/
@[step]
theorem into_pb_spec (self : chain.ChainEpochDirection) :
    into_pb self ⦃ (result : proto.pq_ratchet.chain.epoch.EpochDirection) =>
      result = FunctionalModels.intoPb self ⦄ := by
  unfold into_pb FunctionalModels.intoPb
  step*

/-- **Round trip `from_pb ∘ into_pb` for the monadic `ChainEpochDirection` serializers**:
Serializing and then deserializing always succeeds and recovers the original value. -/
theorem roundtrip_from_pb_into_pb (self : chain.ChainEpochDirection) :
    (do let pb ← into_pb self; from_pb pb) = ok (.Ok self) := by
  unfold into_pb from_pb
  simp

end spqr.chain.ChainEpochDirection
