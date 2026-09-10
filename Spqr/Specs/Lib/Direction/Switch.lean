/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
/-!
# Spec theorem for `spqr::{spqr::proto::pq_ratchet::Direction}::switch`

`switch` swaps `A2B ↔ B2A`. It is a total involution (`switch ∘ switch = id`).

**Source**: spqr/src/lib.rs -/

open Aeneas Aeneas.Std Result spqr

namespace spqr.Direction

/-- **Spec theorem for `spqr.Direction.switch`**:
`switch` maps `A2B ↦ B2A` and `B2A ↦ A2B`. Proof by unfolding and `simp`. -/
@[step]
theorem switch_spec_A2B :
    Direction.switch .A2B ⦃ (result : proto.pq_ratchet.Direction) =>
      result = .B2A ⦄ := by
  unfold Direction.switch
  simp

@[step]
theorem switch_spec_B2A :
    Direction.switch .B2A ⦃ (result : proto.pq_ratchet.Direction) =>
      result = .A2B ⦄ := by
  unfold Direction.switch
  simp

end spqr.Direction
