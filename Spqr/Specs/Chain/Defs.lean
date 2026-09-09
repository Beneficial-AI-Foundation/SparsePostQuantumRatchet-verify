/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Chain.ChainEpochDirection.NextKeyInternal
/-!
# Definitions for `ChainEpochDirection` key-loop helpers

Reusable pure definitions used by the chain-key advancement loop and related specs.
-/

open Aeneas Aeneas.Std Result spqr crypto

namespace spqr.chain

/-- Pure version of `max_ooo_keys_or_default`: returns `params.max_ooo_keys` if positive,
    otherwise the default (2000). -/
noncomputable def maxOoo (params : proto.pq_ratchet.ChainParams) : U32 :=
  if params.max_ooo_keys > 0#u32 then params.max_ooo_keys
  else chain.DEFAULT_CHAIN_PARAMS.max_ooo_keys

/-- Pure version of `max_jump_or_default`: returns `params.max_jump` if positive,
    otherwise the default (25000). -/
noncomputable def maxJump (params : proto.pq_ratchet.ChainParams) : U32 :=
  if params.max_jump > 0#u32 then params.max_jump
  else chain.DEFAULT_CHAIN_PARAMS.max_jump

end spqr.chain

open spqr.chain
namespace spqr.chain.ChainEpochDirection

/-- The iterated chain secret: apply `nextKeyHkdfOutput … .take 32` exactly `n` times
    starting from `secret`.  `iterChainSecret secret base 0 = secret` and
    `iterChainSecret secret base (n+1) =
      (nextKeyHkdfOutput (iterChainSecret secret base n) ⟨base+n+1,…⟩).take 32`.

    Requires `base + n + 1 ≤ U32.max` for well-formedness of the counter;
    when `base + n + 1 > U32.max` the definition returns `[]` (junk). -/
noncomputable def iterChainSecret (secret : List U8) (base : Nat) : Nat → List U8
  | 0     => secret
  | n + 1 =>
    if h : base + n + 1 ≤ U32.max then
      let prev := iterChainSecret secret base n
      (nextKeyHkdfOutput prev ⟨base + n + 1, by scalar_tac⟩).take 32
    else []

/-- The iterated key history: accumulate keys that would be added during the loop.
    At each step `j` (0-indexed), the counter value is `base + j + 1`.  If
    `base + j + 1 + maxOoo params ≥ target` the derived key is added; otherwise it is
    skipped.  `iterKeyHistory … 0 = kh` (no iterations).

    Requires `base + n + 1 ≤ U32.max` for well-formedness; when out of range the
    definition returns the accumulated key history unchanged (junk). -/
noncomputable def iterKeyHistoryData
    (secret : List U8) (base : Nat) (target : Nat)
    (params : proto.pq_ratchet.ChainParams) (khData : List U8) : Nat → List U8
  | 0     => khData
  | n + 1 =>
    if h : base + n + 1 ≤ U32.max then
      let prev := iterKeyHistoryData secret base target params khData n
      let prev_secret := iterChainSecret secret base n
      let ctr1 : U32 := ⟨base + n + 1, by scalar_tac⟩
      let okm := nextKeyHkdfOutput prev_secret ctr1
      if (base + n + 1) + (maxOoo params).val ≥ target then
        prev ++ (core.num.U32.to_be_bytes ctr1).val ++ okm.drop 32
      else prev
    else khData

/-- The iterated key history: accumulate keys that would be added during the loop.
    At each step `j` (0-indexed), the counter value is `base + j + 1`.  If
    `base + j + 1 + maxOoo params ≥ target` the derived key is added; otherwise it is
    skipped.  `iterKeyHistory … 0 = kh` (no iterations).

    Requires `base + n + 1 ≤ U32.max` for well-formedness; when out of range the
    definition returns the accumulated key history data unchanged (junk).

    The result is a `chain.KeyHistory` whose `.data.val` equals
    `iterKeyHistoryData secret base target params kh.data.val n`. -/
noncomputable def iterKeyHistory
    (secret : List U8) (base : Nat) (target : Nat)
    (params : proto.pq_ratchet.ChainParams) (kh : chain.KeyHistory) (n : Nat) :
    chain.KeyHistory :=
  let d := iterKeyHistoryData secret base target params kh.data.val n
  if h : d.length ≤ Usize.max then { data := ⟨d, h⟩ }
  else kh

/-- Length bound for `iterKeyHistoryData`: each iteration adds at most 36 bytes
    (4 bytes for the big-endian counter plus 32 bytes for the derived key). -/
theorem iterKeyHistoryData_length_le
    (secret : List U8) (base target : Nat)
    (params : proto.pq_ratchet.ChainParams) (khData : List U8) (n : Nat) :
    (iterKeyHistoryData secret base target params khData n).length ≤ khData.length + 36 * n := by
  induction n with
  | zero => simp [iterKeyHistoryData]
  | succ m ih =>
    rw [iterKeyHistoryData]
    simp only []
    split
    · split
      · have h4 : ((core.num.U32.to_be_bytes
        (⟨base + m + 1, by scalar_tac⟩ : U32)).val).length = 4 := by
          simp [core.num.U32.to_be_bytes, BitVec.toBEBytes_length]
        have h64 : (nextKeyHkdfOutput (iterChainSecret secret base m)
            (⟨base + m + 1, by scalar_tac⟩ : U32)).length = 64 := by
          simp [nextKeyHkdfOutput, crypto.hkdf_length]
        simp only [List.length_append, h4, List.length_drop, h64]
        omega
      · omega
    · omega

/-- Alignment preservation for `iterKeyHistoryData`: if the initial data has length `% 36 = 0`,
    then so does the result after any number of iterations. -/
theorem iterKeyHistoryData_length_mod_36
    (secret : List U8) (base target : Nat)
    (params : proto.pq_ratchet.ChainParams) (khData : List U8) (n : Nat)
    (h_aligned : khData.length % 36 = 0) :
    (iterKeyHistoryData secret base target params khData n).length % 36 = 0 := by
  induction n with
  | zero => simp [iterKeyHistoryData, h_aligned]
  | succ m ih =>
    rw [iterKeyHistoryData]
    simp only []
    split
    · split
      · have h4 : ((core.num.U32.to_be_bytes
        (⟨base + m + 1, by scalar_tac⟩ : U32)).val).length = 4 := by
          simp [core.num.U32.to_be_bytes, BitVec.toBEBytes_length]
        have h64 : (nextKeyHkdfOutput (iterChainSecret secret base m)
            (⟨base + m + 1, by scalar_tac⟩ : U32)).length = 64 := by
          simp [nextKeyHkdfOutput, crypto.hkdf_length]
        simp only [List.length_append, h4, List.length_drop, h64]
        omega
      · exact ih
    · exact h_aligned

/-- Alignment preservation for `iterKeyHistory`: if the initial key history has aligned data,
    then so does the result. -/
theorem iterKeyHistory_data_length_mod_36
    (secret : List U8) (base target : Nat)
    (params : proto.pq_ratchet.ChainParams) (kh : chain.KeyHistory) (n : Nat)
    (h_aligned : kh.data.length % 36 = 0) :
    (iterKeyHistory secret base target params kh n).data.length % 36 = 0 := by
  simp only [iterKeyHistory, alloc.vec.Vec.length]
  split
  · exact iterKeyHistoryData_length_mod_36 secret base target params kh.data.val n h_aligned
  · exact h_aligned

end spqr.chain.ChainEpochDirection
