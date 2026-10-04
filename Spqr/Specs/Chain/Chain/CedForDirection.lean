/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Chain.ChainEpochDirection.New
/-!
# Spec theorem for `spqr::chain::{spqr::chain::Chain}::ced_for_direction`

Builds a `ChainEpochDirection` from a 96-byte `genr8r` and a `Direction` by selecting
`genr8r[32..64]` (A2B) or `genr8r[64..96]` (B2A) and passing it to `ChainEpochDirection::new`.

**Source**: spqr/src/chain.rs (lines 322:4-327:5)
-/

open Aeneas Aeneas.Std Result spqr

namespace spqr.chain.Chain

/-- **Spec theorem for `spqr.chain.Chain.ced_for_direction`**:

Given a 96-byte `genr8r` and `dir`, returns a `ChainEpochDirection` with `ctr = 0`,
empty history, and `next` set to `genr8r[32..64]` (A2B) or `genr8r[64..96]` (B2A).
Proof: unfold, case-split on `dir`, then `step*`.

**Source**: spqr/src/chain.rs (lines 322:4-327:5)
-/
@[step]
theorem ced_for_direction_spec (genr8r : Slice U8) (dir : proto.pq_ratchet.Direction)
    (h_len : genr8r.length = 96) :
    ced_for_direction genr8r dir ⦃ fun (result : chain.ChainEpochDirection) =>
      result.ctr = 0#u32 ∧
      result.prev.data.length = 0 ∧
      result.next.val = (match dir with
        | .A2B => genr8r.val.slice 32 64
        | .B2A => genr8r.val.slice 64 96) ⦄ := by
  unfold ced_for_direction
  match dir with
  | .A2B => step*
  | .B2A => step*

end spqr.chain.Chain
