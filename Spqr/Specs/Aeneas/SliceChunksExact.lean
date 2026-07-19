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

/-- The number of chunks is exactly `l.length / n`. -/
theorem List.toChunksExact_chunks_length_eq
    {T : Type} {n : Nat} (hn : 0 < n) (l : List T) :
    (List.toChunksExact n hn l).1.length = l.length / n := by
  unfold List.toChunksExact
  split
  · rename_i h
    simp [Nat.div_eq_of_lt h]
  · rename_i h
    simp only [not_lt] at h
    have ih := List.toChunksExact_chunks_length_eq hn (l.drop n)
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

/-- Content of the i-th chunk produced by `toChunksExact`:
    the i-th chunk equals `(l.drop (n * i)).take n`. -/
theorem toChunksExact_getElem_eq
    {T : Type} {n : Nat} (hn : 0 < n) (l : List T)
    (i : Nat) (hi : i < (List.toChunksExact n hn l).1.length) :
    (List.toChunksExact n hn l).1[i] = (l.drop (n * i)).take n := by
  revert i
  unfold List.toChunksExact
  split
  · intro i hi; simp at hi
  · rename_i h
    simp only [not_lt] at h
    intro i hi
    dsimp only [] at hi ⊢
    cases i with
    | zero => simp
    | succ i =>
      simp only [List.length_cons] at hi
      simp only [List.getElem_cons_succ]
      have h_bound : i < (List.toChunksExact n hn (l.drop n)).1.length := by omega
      rw [toChunksExact_getElem_eq hn (l.drop n) i h_bound, List.drop_drop]
      congr 1; grind
termination_by l.length
decreasing_by simp [List.length_drop]; omega

/-- For a list `l` and any function `f` wrapping elements as Slices while preserving `.val`,
    `getElem!` on the mapped-attached list has `.val` equal to `getElem!` on the original. -/
private theorem attach_map_getElem!_val {T : Type} [Inhabited T] [Inhabited (Slice T)]
    (l : List (List T))
    (f : {x // x ∈ l} → Slice T)
    (hf : ∀ x, (f x).val = x.val)
    (k : Nat) (hk : k < l.length) :
    (l.attach.map f)[k]!.val = l[k]! := by
  have hk' : k < (l.attach.map f).length := by
    simp only [List.length_map, List.length_attach]; exact hk
  have h1 : (l.attach.map f)[k]! = (l.attach.map f)[k]'hk' :=
    getElem!_pos (l.attach.map f) k hk'
  have h2 : (l[k]! : List T) = l[k]'hk :=
    getElem!_pos l k hk
  rw [h1, List.getElem_map, hf, h2]
  simp [List.getElem_attach]

/-- Stronger spec for `chunks_exact` including chunk content preservation. -/
@[step]
theorem chunks_exact_spec_with_content {T : Type} [Inhabited T]
    (s : Slice T) (chunk_size : Usize)
    (h : chunk_size.val > 0)
    [Inhabited (Slice T)] :
    core.slice.Slice.chunks_exact s chunk_size ⦃ (result : core.slice.iter.ChunksExact T) =>
      (∀ c ∈ result.chunks, c.val.length = chunk_size.val) ∧
      result.chunks.length = s.val.length / chunk_size.val ∧
      result.remainder.val.length ≤ s.val.length % chunk_size.val ∧
      (∀ j, j < result.chunks.length →
        result.chunks[j]!.val = (s.val.drop (chunk_size.val * j)).take chunk_size.val) ⦄ := by
  unfold core.slice.Slice.chunks_exact
  simp only [dif_pos h, WP.spec_ok]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c hc
    simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists] at hc
    obtain ⟨c', hc', rfl⟩ := hc
    exact List.toChunksExact_chunk_exact_length' h s.val c' hc'
  · simp only [List.length_map, List.length_attach]
    exact List.toChunksExact_chunks_length_eq h s.val
  · have := List.toChunksExact_remainder_length_le_mod' h s.val; scalar_tac
  · intro j hj
    simp only [List.length_map, List.length_attach] at hj
    rw [attach_map_getElem!_val _ _ (by intro ⟨c, hc⟩; rfl) j hj]
    let cl := (List.toChunksExact chunk_size.val h s.val).1
    have h_pos : cl[j]! = cl[j]'hj := getElem!_pos cl j hj
    rw [h_pos]
    exact toChunksExact_getElem_eq h s.val j hj

end Aeneas.Std.core.slice.Slice
