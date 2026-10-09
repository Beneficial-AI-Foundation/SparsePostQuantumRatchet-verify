/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Crypto.Hkdf
import Spqr.Specs.Kdf.HkdfToSlice
import Spqr.Specs.Aeneas.CopyFromSlice
import Spqr.Specs.Aeneas.ArrayIndexRangeTo
import Spqr.Specs.Aeneas.ArrayIndexRangeFrom
import Spqr.Specs.Aeneas.TryFromSliceToArray
import Spqr.Specs.Aeneas.ResultExpect
import Spqr.Specs.Aeneas.SliceConcatListAux
import Spqr.Specs.Aeneas.SliceListToVec
import Spqr.Specs.Aeneas.SliceConcat
/-!
# Spec theorem for `spqr::chain::{spqr::chain::ChainEpochDirection}::next_key_internal`

Derives the next chain key by incrementing `ctr`, running HKDF (salt = 32 zero bytes,
ikm = current secret, info = `ctr.to_be_bytes() ++ "Signal PQ Ratchet V1 Chain Next"`)
to produce 64 bytes, then splitting: first 32 bytes become the new secret, last 32 are
the derived key. Returns `(ctr+1, derived_key)`.

**Source**: spqr/src/chain.rs (lines 228:4-245:5)
-/

open Aeneas Aeneas.Std Result spqr crypto

namespace spqr.chain.ChainEpochDirection

/-- **Spec theorem for `spqr.chain.ChainEpochDirection.next_key_internal`**:

Given 32-byte `next` and `ctr < U32.max`, returns `((ctr+1, key), next', ctr+1)` where
`okm = nextKeyHkdfOutput next (ctr+1)`, `next' = okm.take 32`, `key = okm.drop 32`,
and `next'.length = next.length`.

**Source**: spqr/src/chain.rs (lines 228:4-245:5)
-/
@[step]
theorem next_key_internal_spec (next : Slice U8) (ctr : U32)
    (h_next_len : next.length = 32)
    (h_ctr : ctr < U32.max) :
    next_key_internal next ctr ⦃ (result : (U32 × (Array U8 32#usize)) × (Slice U8) × U32) =>
      let ctr1 : U32 := ⟨ctr.val + 1, by scalar_tac⟩
      let okm := nextKeyHkdfOutput next ctr1
      result.2.2 = ctr.val + 1 ∧
      result.1.1 = ctr.val + 1 ∧
      result.1.1 = result.2.2 ∧
      result.2.1.length = next.length ∧
      result.2.1 = okm.take 32 ∧
      result.1.2 = okm.drop 32 ⦄ := by
  unfold chain.ChainEpochDirection.next_key_internal
  step*
  case hlen =>
    have : 35 ≤ Usize.max := by scalar_tac
    simp_all
  simp only [‹r = _›]
  step*
  simp only [nextKeyHkdfOutput, nextKeyInfo, chainNextLabel, zeroSalt32]
  simp_all [List.slice]
  have hbv : ctr1.bv = ⟨⟨ctr.val + 1, by scalar_tac⟩⟩ :=
    BitVec.eq_of_toNat_eq (by simpa using ‹ctr1.val = _›)
  simp [hbv, U8.ofUInt8]

end spqr.chain.ChainEpochDirection
