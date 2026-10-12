/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import SrcTranslated.Funs
public import Spqr.Specs.Chain.KeyHistory.New
/-! # Spec theorem for `spqr::chain::{spqr::chain::ChainEpochDirection}::new`

Constructs a `ChainEpochDirection` from a byte slice `k` with `ctr = 0`,
an empty `prev` history, and `next` cloned from `k`. Always succeeds.

**Source**: spqr/src/chain.rs -/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace spqr.chain.ChainEpochDirection

/-- **Spec theorem for `spqr.chain.ChainEpochDirection.new`**:

Returns a `ChainEpochDirection` with `ctr = 0`, empty `prev`, and `next = k`. -/
@[step]
theorem new_spec (k : Slice U8) :
    new k ⦃ (result : chain.ChainEpochDirection) =>
      result.ctr = 0#u32 ∧
      result.prev.data.length = 0 ∧
      result.next.deref = k ⦄ := by
  unfold new
  step*
  simp_all [alloc.vec.Vec.deref, alloc.vec.Vec.val]

end spqr.chain.ChainEpochDirection
