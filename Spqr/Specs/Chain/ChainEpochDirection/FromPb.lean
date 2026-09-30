/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Chain.ChainEpochDirection.FunctionalModels

/-! # Spec theorem for `spqr::chain::{spqr::chain::ChainEpochDirection}::from_pb`

Converts a `ChainEpochDirection` from the protobuf form
(`proto.pq_ratchet.chain.epoch.EpochDirection`) back into the in-memory Rust form
(`chain.ChainEpochDirection`). The `ctr` and `next` fields are copied verbatim and
`prev` is rewrapped as a `KeyHistory`. Always succeeds (no validation). The reverse
direction is `into_pb`.

**Source**: spqr/src/chain.rs (lines 306:4-312:5)
-/

open Aeneas Aeneas.Std Result spqr

namespace spqr.chain.ChainEpochDirection

/-- **Spec theorem for `spqr.chain.ChainEpochDirection.from_pb`**:
• The call always succeeds (no panic).
• The result is exactly the functional model `FunctionalModels.fromPb pb`. -/
@[step]
theorem from_pb_spec (pb : proto.pq_ratchet.chain.epoch.EpochDirection) :
    from_pb pb ⦃ (result : core.result.Result chain.ChainEpochDirection Error) =>
      result = FunctionalModels.fromPb pb ⦄ := by
  unfold from_pb FunctionalModels.fromPb
  step*

/-- **Round trip `into_pb ∘ from_pb` for the monadic `ChainEpochDirection` serializers**:
If deserialization succeeds with `Ok x`, then serializing `x` back recovers the original
protobuf value. -/
theorem roundtrip_into_pb_from_pb (pb : proto.pq_ratchet.chain.epoch.EpochDirection)
    (x : chain.ChainEpochDirection)
    (h : from_pb pb = ok (.Ok x)) :
    into_pb x = ok pb := by
  unfold from_pb at h
  simp only [ok.injEq, core.result.Result.Ok.injEq] at h
  subst h
  unfold into_pb
  rfl

end spqr.chain.ChainEpochDirection
