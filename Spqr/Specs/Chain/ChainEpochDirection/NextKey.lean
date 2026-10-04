/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Chain.ChainEpochDirection.NextKeyInternal
import Spqr.Specs.Aeneas.VecDerefMut
/-!
# Spec theorem for `spqr::chain::{spqr::chain::ChainEpochDirection}::next_key`

Wrapper around `next_key_internal`: increments `ctr`, derives 64 bytes via HKDF-SHA256,
updates the chain secret with the first 32 bytes, and returns the last 32 bytes as a `Vec<u8>`.
Infallible when `self.next.length = 32` and `self.ctr < u32::MAX`.

**Source**: spqr/src/chain.rs -/

open Aeneas Aeneas.Std crypto

namespace spqr.chain.ChainEpochDirection

/-- **Spec theorem for `spqr.chain.ChainEpochDirection.next_key`**:

Given `ctr1 = self.ctr + 1` and `okm = nextKeyHkdfOutput self.next ctr1`, the result satisfies:
`idx = ctr1`, `key_vec = okm.drop 32`, `self'.ctr = ctr1`, `self'.next = okm.take 32`,
`self'.next.length` is preserved, and the key history `self'.prev` is untouched. -/
@[step]
theorem next_key_spec (self : chain.ChainEpochDirection)
    (h_next_len : self.next.length = 32)
    (h_ctr : self.ctr < U32.max) :
    next_key self ⦃ (result : (U32 × (alloc.vec.Vec U8)) × chain.ChainEpochDirection) =>
      let ctr1 : U32 := ⟨self.ctr.val + 1, by scalar_tac⟩
      let okm := nextKeyHkdfOutput self.next ctr1
      result.1.1 = self.ctr.val + 1 ∧
      result.2.ctr = self.ctr.val + 1 ∧
      result.2.next.length = self.next.length ∧
      result.2.next = okm.take 32 ∧
      result.2.prev = self.prev ∧
      result.1.2 = okm.drop 32 ⦄ := by
  unfold chain.ChainEpochDirection.next_key
  simp only [alloc.vec.Vec.deref_mut, alloc.vec.Vec.length, lift, bind_tc_ok] at *
  step*
  simp only [Array.to_slice]
  rename_i p _ _ _ _ _ _
  obtain ⟨idx, key⟩ := p
  simp only [Subtype.coe_eta, uncurry_apply_pair, UScalarTy.U32_numBits_eq, Nat.reducePow]
  step*

end spqr.chain.ChainEpochDirection
