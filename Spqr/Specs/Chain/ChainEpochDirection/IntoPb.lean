/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
/-!
# Spec theorem for `spqr::chain::{spqr::chain::ChainEpochDirection}::into_pb`

Infallible, field-by-field conversion from `ChainEpochDirection` to its protobuf form
`EpochDirection`: `ctr` and `next` are copied verbatim, `prev` is unwrapped to `prev.data`.
Inverse of `from_pb`.

**Source**: spqr/src/chain.rs -/

open Aeneas Aeneas.Std Result spqr

namespace spqr.chain.ChainEpochDirection

/-- **Spec theorem for `spqr.chain.ChainEpochDirection.into_pb`**:

Pure field-by-field repackaging: `ctr` and `next` copied verbatim, `prev` unwrapped to
`prev.data`. Always succeeds; inverse of `from_pb`. -/
@[step]
theorem into_pb_spec (self : chain.ChainEpochDirection) :
    into_pb self ⦃ (result : proto.pq_ratchet.chain.epoch.EpochDirection) =>
      result.ctr = self.ctr ∧
      result.next = self.next ∧
      result.prev = self.prev.data ⦄ := by
  unfold into_pb
  step*

end spqr.chain.ChainEpochDirection
