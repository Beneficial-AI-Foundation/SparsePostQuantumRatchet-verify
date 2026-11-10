/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

import Spqr.Specs.Encoding.Polynomial.PolyEncoder.ChunkAt
public import Spqr.Math.Poly.Lagrange.CompletePoints
public import Spqr.Specs.Encoding.Polynomial.PolyEncoder.Defs
import Mathlib.Order.Int.ConditionallyCompleteOrder
import Mathlib.Tactic.ComputeDegree

/-! # Spec theorem for `spqr::encoding::polynomial::{Encoder for PolyEncoder}::next_chunk`

Casts the `u32` counter `self.idx` to `u16`, calls `chunk_at` at that wire index, then
increments the counter modulo 2³². `next_chunk_spec` holds for every counter value.
`nextChunks_index` and `nextChunks_index_ne` describe a run of consecutive calls: the call
numbered `i` emits index `(idx₀ + i) mod 2¹⁶`, so calls fewer than 2¹⁶ apart emit distinct
indices.

**Source**: spqr/src/encoding/polynomial.rs -/

@[expose] public section

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf Polynomial

namespace spqr.encoding.polynomial.PolyEncoder.Insts.SpqrEncodingEncoder

/-- One `next_chunk` call satisfies `NextChunkPostCond`, for every value of the counter. -/
@[step]
theorem next_chunk_spec
    (self : encoding.polynomial.PolyEncoder)
    (h_admissible : ∀ pts, self.s = .Points pts →
        ∀ (j : Nat), j < 16 →
          let len := (pts[j]!).value.length
          len = 0 ∨ len = 1 ∨ len = 3 ∨ len = 5 ∨
          len = 30 ∨ len = 34 ∨ len = 36)
    (h_coeff_bound : ∀ polys, self.s = .Polys polys →
        ∀ (j : Nat), j < 16 →
          (polys[j]!).coefficients.length + 1 ≤ Usize.max) :
    next_chunk self ⦃ ((chunk, self') :
        encoding.Chunk × encoding.polynomial.PolyEncoder) =>
      NextChunkPostCond self self' chunk ⦄ := by
  unfold next_chunk
  step as ⟨i, h_i⟩
  have h_w : i.val = self.wireIndex := by
    rw [h_i, UScalar.cast_val_eq, UScalarTy.U16_numBits_eq, wireIndex]
  have h_i_lt : i.val < 2 ^ 16 := by
    rw [h_w, wireIndex]; exact Nat.mod_lt _ (by norm_num)
  step with chunk_at_spec self i (by scalar_tac) h_admissible h_coeff_bound
    as ⟨chunk, self1, h_post⟩
  obtain ⟨h_index, h_len, h_idx1, h_match⟩ := h_post
  step as ⟨i1, h_i1⟩
  rw [h_w] at h_match
  refine ⟨by rw [h_index, h_w], h_len, ?_, ?_⟩
  · rw [h_i1, core.num.U32.wrapping_add_val_eq, h_idx1, UScalar.size_UScalarTyU32]
    rfl
  · unfold chunkWord
    cases h_s : self.s with
    | Polys polys =>
      simp only [h_s] at h_match ⊢
      obtain ⟨h_eq, h_eval⟩ := h_match
      exact ⟨by rw [h_eq, h_s], h_eval⟩
    | Points pts =>
      simp only [h_s] at h_match ⊢
      rcases h_match with ⟨h_eq, h_cache⟩ | ⟨polys', h_polys', h_rest⟩
      · exact Or.inl ⟨by rw [h_eq, h_s], h_cache⟩
      · exact Or.inr ⟨polys', h_polys', h_rest⟩

/-- A `next_chunk` step preserves the premises of `next_chunk_spec`. -/
theorem nextChunkReady_of_postCond {self self' : PolyEncoder} {chunk : encoding.Chunk}
    (h_ready : NextChunkReady self) (h_post : NextChunkPostCond self self' chunk) :
    NextChunkReady self' := by
  obtain ⟨_, _, _, h_match⟩ := h_post
  obtain ⟨h_adm, h_coeff⟩ := h_ready
  cases h_s : self.s with
  | Polys polys =>
    simp only [h_s] at h_match
    refine ⟨fun pts h' => ?_, fun polys' h' => ?_⟩
    · rw [h_match.1] at h'; cases h'
    · rw [h_match.1] at h'; exact h_coeff polys' (h_s.trans h')
  | Points pts =>
    simp only [h_s] at h_match
    rcases h_match with ⟨h_eq, -⟩ | ⟨polys', h_polys', -, h_bound, -⟩
    · refine ⟨fun pts' h' => ?_, fun polys' h' => ?_⟩
      · rw [h_eq] at h'; exact h_adm pts' (h_s.trans h')
      · rw [h_eq] at h'; cases h'
    · refine ⟨fun pts' h' => ?_, fun polys'' h' => ?_⟩
      · rw [h_polys'] at h'; cases h'
      · rw [h_polys'] at h'; cases h'; exact h_bound

/-- Assume the encoder satisfies the premises of `next_chunk_spec`. Then `n` consecutive
calls succeed, the call numbered `i` from 0 emits index `(idx₀ + i) mod 2^16`, where `idx₀` is
the starting counter, the counter ends at `(idx₀ + n) mod 2^32`, and the final encoder
still satisfies the premises. -/
theorem nextChunks_index (n : Nat) (self : PolyEncoder) (h_ready : NextChunkReady self) :
    nextChunks n self ⦃ ((cs, self') : List encoding.Chunk × PolyEncoder) =>
      cs.length = n ∧
      (∀ (i : Nat) (hi : i < cs.length), cs[i].index.val = (self.idx.val + i) % 2 ^ 16) ∧
      self'.idx.val = (self.idx.val + n) % 2 ^ 32 ∧
      NextChunkReady self' ⦄ := by
  induction n generalizing self with
  | zero =>
    have h_lt : self.idx.val < 2 ^ 32 := by scalar_tac
    simp only [nextChunks, WP.spec_ok, List.length_nil, Nat.not_lt_zero, IsEmpty.forall_iff,
      implies_true, Nat.add_zero, Nat.mod_eq_of_lt h_lt, true_and]
    exact h_ready
  | succ n ih =>
    simp only [nextChunks]
    step with next_chunk_spec self h_ready.1 h_ready.2 as ⟨c, e₁, h_post⟩
    step with ih e₁ (nextChunkReady_of_postCond h_ready h_post)
      as ⟨cs, e₂, h_ih⟩
    obtain ⟨h_len, h_idx, h_final, h_ready'⟩ := h_ih
    obtain ⟨h_c, -, h_e₁, -⟩ := h_post
    have h_size : U32.size = 2 ^ 32 := by scalar_tac
    rw [h_size] at h_e₁
    refine ⟨by rw [List.length_cons, h_len], fun i hi => ?_, by rw [h_final, h_e₁]; omega,
      h_ready'⟩
    cases i with
    | zero => rw [List.getElem_cons_zero, h_c, wireIndex, Nat.add_zero]
    | succ k =>
      rw [List.length_cons] at hi
      rw [List.getElem_cons_succ, h_idx k (by omega), h_e₁]
      omega

/-- Assume the encoder satisfies the premises of `next_chunk_spec`. Then any two of `n`
consecutive calls that are fewer than 2^16 calls apart emit different indices. So any 2^16
consecutive calls emit pairwise distinct indices. -/
theorem nextChunks_index_ne (n : Nat) (self : PolyEncoder) (h_ready : NextChunkReady self) :
    nextChunks n self ⦃ ((cs, _) : List encoding.Chunk × PolyEncoder) =>
      ∀ (i j : Nat) (hij : i < j) (hj : j < cs.length), j - i < 2 ^ 16 →
        (cs[i]'(Nat.lt_trans hij hj)).index ≠ cs[j].index ⦄ := by
  apply WP.spec_mono (nextChunks_index n self h_ready)
  rintro ⟨cs, e⟩ ⟨-, h_idx, -, -⟩ i j hij hj h_gap h_eq
  have h_val := congrArg UScalar.val h_eq
  rw [h_idx i (Nat.lt_trans hij hj), h_idx j hj] at h_val
  omega

/-- Two calls from counter `2^16 - 1`: indices `65535` then `0`, counter `65537`. -/
example (s : EncoderState) (h_ready : NextChunkReady ⟨65535#u32, s⟩) :
    nextChunks 2 ⟨65535#u32, s⟩ ⦃ ((cs, e) : List encoding.Chunk × PolyEncoder) =>
      cs.map (·.index.val) = [65535, 0] ∧ e.idx.val = 65537 ⦄ := by
  apply WP.spec_mono (nextChunks_index 2 _ h_ready)
  rintro ⟨cs, e⟩ ⟨h_len, h_idx, h_final, -⟩
  match cs, h_len, h_idx with
  | [c₀, c₁], _, h_idx =>
    have h₀ := h_idx 0 (by simp only [List.length_cons, List.length_nil]; omega)
    have h₁ := h_idx 1 (by simp only [List.length_cons, List.length_nil]; omega)
    simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h₀ h₁
    simp only [List.map_cons, h₀, UScalar.ofNatCore_val_eq, add_zero, Nat.reducePow, Nat.mod_succ,
      h₁, Nat.reduceAdd, Nat.mod_self, List.map_nil, h_final, Nat.reduceMod, and_self]

/-- Two calls from counter `2^32 - 1`: indices `65535` then `0`, counter `1`. -/
example (s : EncoderState) (h_ready : NextChunkReady ⟨4294967295#u32, s⟩) :
    nextChunks 2 ⟨4294967295#u32, s⟩ ⦃ ((cs, e) : List encoding.Chunk × PolyEncoder) =>
      cs.map (·.index.val) = [65535, 0] ∧ e.idx.val = 1 ⦄ := by
  apply WP.spec_mono (nextChunks_index 2 _ h_ready)
  rintro ⟨cs, e⟩ ⟨h_len, h_idx, h_final, -⟩
  match cs, h_len, h_idx with
  | [c₀, c₁], _, h_idx =>
    have h₀ := h_idx 0 (by simp only [List.length_cons, List.length_nil]; omega)
    have h₁ := h_idx 1 (by simp only [List.length_cons, List.length_nil]; omega)
    simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h₀ h₁
    simp only [List.map_cons, h₀, UScalar.ofNatCore_val_eq, add_zero, Nat.reducePow, Nat.reduceMod,
      h₁, Nat.reduceAdd, List.map_nil, h_final, and_self]

end spqr.encoding.polynomial.PolyEncoder.Insts.SpqrEncodingEncoder
