/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Types

/-!
# Functional models of `spqr::chain::ChainEpochDirection::{into_pb, from_pb}`

Pure, total Lean functions stating what the two Rust serializers compute, written against the
translated data types only, together with the round-trip laws relating them. The spec theorems
in `IntoPb.lean` and `FromPb.lean` pin the extracted, monadic functions to these models.

**Source:** "spqr/src/chain.rs"
-/

open Aeneas.Std
namespace spqr.chain.ChainEpochDirection.FunctionalModels

/-- **Functional model of `spqr::chain::ChainEpochDirection::into_pb`**
• A pure, total, human-readable function on the translated data types.
-/
def intoPb (x : chain.ChainEpochDirection) :
    proto.pq_ratchet.chain.epoch.EpochDirection :=
  { ctr := x.ctr, next := x.next, prev := x.prev.data }

/-- **Functional model of `spqr::chain::ChainEpochDirection::from_pb`**
• A pure, total, human-readable function on the translated data types.
• A non-empty `next` key must have length 32, otherwise the result is
  `Err Error::StateDecode`.
-/
def fromPb (pb : proto.pq_ratchet.chain.epoch.EpochDirection) :
    core.result.Result chain.ChainEpochDirection Error :=
  if pb.next.val.isEmpty ∨ pb.next.length = 32 then
    .Ok { ctr := pb.ctr, next := pb.next, prev := { data := pb.prev } }
  else .Err .StateDecode

/-- The only error `fromPb` can return is `Error::StateDecode`. -/
theorem fromPb_err (pb : proto.pq_ratchet.chain.epoch.EpochDirection) (e : Error)
    (h : fromPb pb = .Err e) : e = .StateDecode := by
  unfold fromPb at h
  split at h
  · cases h
  · cases h; rfl

/-- **Round trip `fromPb ∘ intoPb` for
`spqr::chain::ChainEpochDirection`**, for directions whose `next` key is empty or of
length 32 (the only ones `fromPb` accepts). -/
theorem roundtrip_fromPb_intoPb (x : chain.ChainEpochDirection)
    (hx : x.next.val.isEmpty ∨ x.next.length = 32) :
    fromPb (intoPb x) = .Ok x := by
  simp only [fromPb, intoPb, hx, ↓reduceIte]

/-- **Round trip `intoPb ∘ fromPb` for
`spqr::chain::ChainEpochDirection`** -/
theorem roundtrip_intoPb_fromPb (pb : proto.pq_ratchet.chain.epoch.EpochDirection)
    (x : chain.ChainEpochDirection) (h : fromPb pb = .Ok x) :
    intoPb x = pb := by
  unfold fromPb at h
  split at h
  · simp only [core.result.Result.Ok.injEq] at h
    subst h; rfl
  · cases h

end spqr.chain.ChainEpochDirection.FunctionalModels
