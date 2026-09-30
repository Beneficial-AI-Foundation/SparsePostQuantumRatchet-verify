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

/-- **Round trip `into_pb ∘ from_pb` for the monadic `Chain` serializers**:
If `from_pb` succeeds with `Ok c`, then `into_pb c` succeeds and the result's scalar
fields match the original protobuf value.

Blocked on the Aeneas iterator bridge (aeneas#1043). -/
theorem roundtrip_into_pb_from_pb (pb : proto.pq_ratchet.Chain)
    (c : chain.Chain)
    (h : from_pb pb = ok (.Ok c)) :
    chain.Chain.into_pb c ⦃ (result : proto.pq_ratchet.Chain) =>
      result = { pb with direction := result.direction,
                         links := result.links } ⦄ := by
  sorry -- Blocked on https://github.com/AeneasVerif/aeneas/issues/1043

/-- **Round trip `from_pb ∘ into_pb` for the monadic `Chain` serializers**:
Serializing and then deserializing recovers a chain whose fields match the original.

Blocked on the Aeneas iterator bridge (aeneas#1043). -/
theorem roundtrip_from_pb_into_pb (self : chain.Chain)
    (dirResult : core.result.Result proto.pq_ratchet.Direction Error)
    (hDir : dirResult = .Ok self.dir) :
    (do let pb ← chain.Chain.into_pb self
        from_pb pb) ⦃ (result : core.result.Result chain.Chain Error) =>
      result = .Ok {
        self with
          links := { buf := self.links.buf,
                     head := 0#usize, length := 0#usize } } ⦄ := by
  sorry -- Blocked on https://github.com/AeneasVerif/aeneas/issues/1043

end spqr.chain.Chain
