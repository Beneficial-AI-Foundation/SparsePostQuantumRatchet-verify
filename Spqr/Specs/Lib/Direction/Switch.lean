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
theorem switch_spec (self : proto.pq_ratchet.Direction) :
    switch self ⦃ (result : proto.pq_ratchet.Direction) =>
      result = match self with
        | .A2B => .B2A
        | .B2A => .A2B ⦄ := by
  unfold switch
  step*

end spqr.Direction
