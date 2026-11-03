/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Lacramioara Astefanoaei
-/
module

public import SrcTranslated.Funs
public import Spqr.Specs.V1.Chunked.States.Serialize.DecodeChunk
public import Spqr.Specs.V1.Chunked.States.Serialize.EncodeChunk

/-!
# The bytes the encoders write form the blocks the decoders read

`encode_varint` writes `varintBytes a`, and `encode_chunk` writes `chunkBytes c`. The
decoders' completeness lemmas (`decode_varint_of_block`, `decode_chunk_of_block`) start from the
block predicates `varintBlockAt` and `chunkBlockAt`. The theorems below connect the two: bytes
whose values contain `varintBytes a` (for `a < 2 ^ 64`) or `chunkBytes c` at some index hold the
matching block there.

**Source**: src/lib.rs (lines 509-554), src/v1/chunked/states/serialize.rs (lines 135-153)
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace spqr.v1.chunked.states.serialize

/-- If the bytes at `start` are `varintBytes a`, their `varintVal` is `a`, the last byte is a
terminator and the others are continuation bytes. -/
theorem varintBytes_block (bytes : List Std.U8) : ∀ (a start : ℕ),
    (∀ k < (varintBytes a).length, bytes[start + k]!.val = (varintBytes a)[k]!) →
    varintVal bytes start (varintBytes a).length = a ∧
    bytes[start + (varintBytes a).length - 1]!.val < 128 ∧
    ∀ k < (varintBytes a).length - 1, 128 ≤ bytes[start + k]!.val
  | a, start, h => by
    by_cases ha : a < 128
    · have hv := varintBytes_of_lt ha
      have h0 := h 0 (by simp [hv])
      simp only [hv, List.length_singleton, List.getElem!_cons_zero, Nat.add_zero] at h0 ⊢
      refine ⟨?_, ?_, fun k hk => by omega⟩
      · simp only [varintVal, Nat.add_zero, Nat.mul_zero, pow_zero, mul_one, zero_add, h0,
          Nat.mod_eq_of_lt ha]
      · rw [Nat.add_sub_cancel, h0]; exact ha
    · have hv := varintBytes_of_ge (Nat.le_of_not_lt ha)
      have ih := varintBytes_block bytes (a / 128) (start + 1) (fun k hk => by
        have := h (k + 1) (by rw [hv]; simp; omega)
        rw [hv] at this
        simpa [Nat.add_assoc, Nat.add_comm 1 k] using this)
      have h0 := h 0 (by rw [hv]; simp)
      rw [hv] at h0
      simp only [Nat.add_zero, List.getElem!_cons_zero] at h0
      obtain ⟨ihv, iht, ihc⟩ := ih
      have hlen := varintBytes_length_pos (a / 128)
      rw [hv]
      simp only [List.length_cons]
      refine ⟨?_, ?_, ?_⟩
      · rw [varintVal_succ_left, ihv, h0]; omega
      · have : start + ((varintBytes (a / 128)).length + 1) - 1 =
            start + 1 + (varintBytes (a / 128)).length - 1 := by omega
        rw [this]; exact iht
      · intro k hk
        rcases k with _ | k
        · rw [Nat.add_zero, h0]; omega
        · have := ihc k (by omega)
          rwa [show start + (k + 1) = start + 1 + k by omega]
termination_by a _ _ => a
decreasing_by all_goals (exact Nat.div_lt_self (by omega) (by omega))

/-- The value of byte `j` of `bs` is entry `j` of the byte values of `bs`. -/
theorem getElem!_val_eq_map (bs : List Std.U8) (j : ℕ) :
    (bs[j]!).val = (bs.map UScalar.val)[j]! := by
  by_cases hj : j < bs.length
  · rw [getElem!_pos bs j hj, getElem!_pos _ j (by simpa using hj)]; simp
  · rw [getElem!_neg bs j hj, getElem!_neg _ j (by simpa using hj)]; rfl

/-- Assume `a < 2 ^ 64` and the byte values of `bs` are `pre ++ varintBytes a ++ post`. Then
`bs` holds the varint block of `a` at index `pre.length`. -/
theorem varintBlockAt_of_map (bs : List Std.U8) (pre post : List ℕ) (a : ℕ) (ha : a < 2 ^ 64)
    (h : bs.map UScalar.val = pre ++ varintBytes a ++ post) :
    varintBlockAt bs pre.length (varintBytes a).length a := by
  have hat : ∀ k < (varintBytes a).length,
      bs[pre.length + k]!.val = (varintBytes a)[k]! := by
    intro k hk
    rw [getElem!_val_eq_map, h, List.append_assoc,
      getElem!_pos _ _ (by simp; omega), getElem!_pos _ k hk]
    rw [List.getElem_append_right (by omega)]
    simp only [Nat.add_sub_cancel_left]
    rw [List.getElem_append_left hk]
  obtain ⟨hv, ht, hc⟩ := varintBytes_block bs a pre.length hat
  have hlen : bs.length = pre.length + (varintBytes a).length + post.length := by
    have := congrArg List.length h; simpa [Nat.add_assoc] using this
  refine ⟨varintBytes_length_pos a, varintBytes_length_le_ten ha, by omega, ?_, ht, hc⟩
  rw [hv, Nat.mod_eq_of_lt ha]

/-- If the byte values of `bs` are `pre ++ chunkBytes c ++ post`, then `bs` holds the chunk
block of `c` at index `pre.length`. -/
theorem chunkBlockAt_of_map (bs : List Std.U8) (pre post : List ℕ) (c : encoding.Chunk)
    (h : bs.map UScalar.val = pre ++ chunkBytes c ++ post) :
    chunkBlockAt bs pre.length (varintBytes c.index.val).length c := by
  have hdlen : c.data.val.length = 32 := by simp
  have hv := varintBlockAt_of_map bs pre (c.data.val.map UScalar.val ++ post) c.index.val
    (by scalar_tac) (by rw [h]; simp [chunkBytes])
  have hlen : bs.length = pre.length + (varintBytes c.index.val).length + 32 + post.length := by
    have := congrArg List.length h; simp [chunkBytes, hdlen] at this; omega
  refine ⟨hv, by omega, ?_⟩
  apply List.map_injective_iff.mpr (fun x y hxy => UScalar.eq_of_val_eq hxy)
  rw [List.slice, List.map_take, List.map_drop, h]
  simp [chunkBytes, hdlen, List.drop_append]

/-- If the byte values of `bs` are `k :: chunkBytes c ++ post`, then the chunk block of `c`
starts at index `1`. -/
theorem chunkBlockAt_of_map_cons (bs : List Std.U8) (k : ℕ) (post : List ℕ) (c : encoding.Chunk)
    (h : bs.map UScalar.val = k :: chunkBytes c ++ post) :
    chunkBlockAt bs 1 (varintBytes c.index.val).length c :=
  chunkBlockAt_of_map bs [k] post c (by rw [h]; simp)

end spqr.v1.chunked.states.serialize
