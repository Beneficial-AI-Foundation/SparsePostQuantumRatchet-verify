/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs

/-!
# Spec theorem for `core::slice::{[@T]}::chunks_exact`
-/

open Aeneas Aeneas.Std Result

/-! ## Helper lemmas for `List.toChunksExact` -/

/-- Each chunk produced by `toChunksExact` has length exactly `n`. -/
theorem List.toChunksExact_chunk_exact_length'
    {T : Type} {n : Nat} (hn : 0 < n) (l : List T) :
    ∀ c ∈ (List.toChunksExact n hn l).1, c.length = n := by
  unfold List.toChunksExact
  split
  · simp
  · rename_i h
    simp only [List.mem_cons]
    intro c hc
    rcases hc with rfl | hc
    · rw [List.length_take]; exact Nat.min_eq_left (by omega)
    · exact List.toChunksExact_chunk_exact_length' hn (l.drop n) c hc
termination_by l.length
decreasing_by simp [List.length_drop]; omega

/-- The number of chunks is at most the length of the input list. -/
theorem List.toChunksExact_chunks_length_le'
    {T : Type} {n : Nat} (hn : 0 < n) (l : List T) :
    (List.toChunksExact n hn l).1.length ≤ l.length / n := by
  unfold List.toChunksExact
  split
  · simp
  · rename_i h
    simp only [not_lt] at h
    have ih := List.toChunksExact_chunks_length_le' hn (l.drop n)
    have h_drop : (l.drop n).length = l.length - n := List.length_drop
    rw [h_drop] at ih
    have hdiv : l.length / n = (l.length - n) / n + 1 := by
      rw [Nat.div_eq l.length n]
      simp [hn, h]
    simp only [List.length_cons]
    omega
termination_by l.length
decreasing_by simp [List.length_drop]; omega

/-- The remainder produced by `toChunksExact` has length at most `l.length % n`. -/
theorem List.toChunksExact_remainder_length_le_mod'
    {T : Type} {n : Nat} (hn : 0 < n) (l : List T) :
    (List.toChunksExact n hn l).2.length ≤ l.length % n := by
  unfold List.toChunksExact
  split
  · rename_i h
    simp [Nat.mod_eq_of_lt h]
  · rename_i h
    simp only [not_lt] at h
    simp only []
    have ih := List.toChunksExact_remainder_length_le_mod' hn (l.drop n)
    rw [List.length_drop] at ih
    rw [Nat.mod_eq_sub_mod h]
    exact ih
termination_by l.length
decreasing_by simp [List.length_drop]; omega

namespace Aeneas.Std.core.slice.Slice


/-! ## Spec theorem -/

@[step]
theorem chunks_exact_spec {T : Type} (s : Slice T) (chunk_size : Usize)
    (h : chunk_size.val > 0) :
    core.slice.Slice.chunks_exact s chunk_size ⦃ (result : core.slice.iter.ChunksExact T) =>
      (∀ c ∈ result.chunks, c.val.length = chunk_size.val) ∧
      result.chunks.length ≤ s.val.length / chunk_size.val ∧
      result.remainder.val.length ≤ s.val.length % chunk_size.val ⦄ := by
  unfold core.slice.Slice.chunks_exact
  simp only [dif_pos h, WP.spec_ok]
  refine ⟨?_, ?_, by have := List.toChunksExact_remainder_length_le_mod' h s.val; scalar_tac⟩
  · intro c hc
    simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists] at hc
    obtain ⟨c', hc', rfl⟩ := hc
    exact List.toChunksExact_chunk_exact_length' h s.val c' hc'
  · simp only [List.length_map, List.length_attach]
    exact List.toChunksExact_chunks_length_le' h s.val

end Aeneas.Std.core.slice.Slice
