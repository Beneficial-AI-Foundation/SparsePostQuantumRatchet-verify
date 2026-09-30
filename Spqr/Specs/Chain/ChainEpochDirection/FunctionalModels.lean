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
-/
def fromPb (pb : proto.pq_ratchet.chain.epoch.EpochDirection) :
    core.result.Result chain.ChainEpochDirection Error :=
  .Ok { ctr := pb.ctr, next := pb.next, prev := { data := pb.prev } }

/-- **Round trip `fromPb ∘ intoPb` for
`spqr::chain::ChainEpochDirection`** -/
@[simp]
theorem roundtrip_fromPb_intoPb (x : chain.ChainEpochDirection) :
    fromPb (intoPb x) = .Ok x := rfl

/-- **Round trip `intoPb ∘ fromPb` for
`spqr::chain::ChainEpochDirection`** -/
@[simp]
theorem roundtrip_intoPb_fromPb (pb : proto.pq_ratchet.chain.epoch.EpochDirection)
    (x : chain.ChainEpochDirection) (h : fromPb pb = .Ok x) :
    intoPb x = pb := by
  simp only [fromPb, core.result.Result.Ok.injEq] at h
  subst h; rfl

end spqr.chain.ChainEpochDirection.FunctionalModels
