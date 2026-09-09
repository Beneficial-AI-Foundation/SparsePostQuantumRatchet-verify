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
  simp only [Slice.length] at h_next_len
  simp only [core.array.Array.as_slice, alloc.vec.Vec.as_slice, bind_tc_ok] at *
  step*
  simp only [alloc.slice.Slice.concat_eq, Slice.Insts.AllocSliceConcatTVec.concat_eq, liftFun1,
    core.clone.impls.CloneU8.clone, implies_true, Slice.concatListAux_shared_id_spec, bind_tc_ok,
    Subtype.coe_eta, Slice.length, UScalarTy.U32_numBits_eq, Nat.reducePow]
  step*
  · simp
    subst s3_post
    simp only [Array.to_slice, Array.make, List.map,
      Function.comp, List.sum_cons, List.sum_nil]
    simp only [a1_post, s2_post]
    simp only [Array.to_slice, Array.make, List.length_map, List.length_cons,
      List.length_nil]
    grind
  · simp only [Slice.length] at *
    scalar_tac
  · simp_all only
    step*
    constructor
    · grind
    · constructor
      · grind
      · constructor
        · grind
        · simp only [Slice.length] at *
          constructor
          · simp only [nextKeyHkdfOutput, nextKeyInfo, chainNextLabel, zeroSalt32]
            subst s5_post2
            simp only [s7_post1, s6_post, s5_post1, Nat.sub_zero, List.drop_zero, List.slice,
              Array.from_slice, Array.to_slice, Array.repeat, List.length_replicate]
            split
            · congr 1
              simp only [Array.make, List.map, List.flatten]
              congr 1
              · simp only [List.append_nil, List.append_eq]
                congr 1
                congr 1
                congr 1
                have h1 : ctr1.bv.toNat = ↑ctr + 1 := ctr1_post
                apply BitVec.eq_of_toNat_eq
                simp [BitVec.toNat_ofFin, h1]
            · next h =>
              exfalso
              apply h
              simp
          · simp only [nextKeyHkdfOutput, nextKeyInfo, chainNextLabel, zeroSalt32]
            subst s5_post2
            simp only [a2_post, r_post2, s6_post, s5_post1,
              Array.from_slice, Array.to_slice, Array.repeat,  List.length_replicate]
            split
            · congr 1
              simp only [Array.make, List.map, List.flatten]
              congr 1
              · congr 1
                congr 1
                congr 1
                have h1 : ctr1.bv.toNat = ↑ctr + 1 := ctr1_post
                apply BitVec.eq_of_toNat_eq
                simp [BitVec.toNat_ofFin, h1]
            · next h =>
              exfalso
              apply h
              simp

end spqr.chain.ChainEpochDirection
