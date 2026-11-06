/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Lacramioara Astefanoaei
-/
module

public import SrcTranslated.Funs
public import Spqr.Specs.Aeneas.SliceChunksExact

/-!
# Spec theorems for `core::slice::{[@T]}::chunks` with chunk size 2

The file also shows that `u16::from_le_bytes` depends only on the two bytes of its array.
-/

@[expose] public section

open Aeneas Aeneas.Std Result

/-- On a list of even length, `toChunksExact 2` leaves no remainder. -/
theorem List.toChunksExact_two_remainder_nil {T : Type} (l : List T) (h_even : l.length % 2 = 0) :
    (List.toChunksExact 2 (by decide) l).2 = [] := by
  have := List.toChunksExact_remainder_length_le_mod' (n := 2) (by decide) l
  exact List.eq_nil_of_length_eq_zero (by omega)

/-- `chunks 2` on a slice of even length returns chunks of exactly 2 elements. -/
@[step]
theorem core.slice.Slice.chunks_two_spec {T : Type} (s : Slice T) (h_even : s.length % 2 = 0) :
    core.slice.Slice.chunks s 2#usize ⦃ (it : core.slice.iter.Chunks T) =>
      ∀ c ∈ it.chunks, c.length = 2 ⦄ := by
  have h_rem := List.toChunksExact_two_remainder_nil s.val h_even
  simp only [core.slice.Slice.chunks]
  simp only [show (2#usize : Usize).val > 0 by decide, _root_.dite_true, WP.spec_ok]
  intro c hc
  simp only [show (2#usize : Usize).val = 2 by rfl] at hc ⊢
  simp only [h_rem, ite_true, List.append_nil, List.mem_map, List.mem_attach, true_and,
    Subtype.exists] at hc
  obtain ⟨c', hc', rfl⟩ := hc
  simpa [Slice.length] using
    List.toChunksExact_chunk_exact_length' (n := 2) (by decide) s.val c' hc'

/-- Every chunk of `chunks 2` on a slice `s` of even length is `[s[2k], s[2k+1]]` for some `k`. -/
theorem core.slice.Slice.chunks_two_content {T : Type} [Inhabited T] (s : Slice T)
    (h_even : s.length % 2 = 0) :
    core.slice.Slice.chunks s 2#usize ⦃ (it : core.slice.iter.Chunks T) =>
      ∀ c ∈ it.chunks, ∃ k, 2 * k + 1 < s.length ∧
        c.val = [s.val[2 * k]!, s.val[2 * k + 1]!] ⦄ := by
  have h_rem := List.toChunksExact_two_remainder_nil s.val h_even
  simp only [core.slice.Slice.chunks]
  simp only [show (2#usize : Usize).val > 0 by decide, _root_.dite_true, WP.spec_ok]
  intro c hc
  simp only [show (2#usize : Usize).val = 2 by rfl] at hc ⊢
  simp only [h_rem, ite_true, List.append_nil, List.mem_map, List.mem_attach, true_and,
    Subtype.exists] at hc
  obtain ⟨c', hc', rfl⟩ := hc
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hc'
  have hlen : (List.toChunksExact (2#usize : Usize).val (by decide) s.val).1.length =
      s.val.length / 2 := List.toChunksExact_chunks_length_eq (n := 2) (by decide) s.val
  refine ⟨k, ?_, ?_⟩
  · simp only [Slice.length]; omega
  · rw [Slice.from_val, Aeneas.Std.core.slice.Slice.toChunksExact_getElem_eq _ s.val k hk]
    have h1 : 2 * k < s.val.length := by omega
    have h2 : 2 * k + 1 < s.val.length := by omega
    change (List.take 2 (List.drop (2 * k) s.val)) = _
    rw [List.drop_eq_getElem_cons h1, List.drop_eq_getElem_cons h2,
      getElem!_pos s.val (2 * k) h1, getElem!_pos s.val (2 * k + 1) h2]
    rfl

/-- `u16::from_le_bytes` depends only on the two bytes of its array. -/
theorem u16_from_le_bytes_of_val (a : Std.Array U8 2#usize) (x y : U8) (h : a.val = [x, y]) :
    core.num.U16.from_le_bytes a =
      core.num.U16.from_le_bytes (Std.Array.make 2#usize [x, y] (by simp)) := by
  congr 1
  exact Std.Array.ext _ _ (by simpa [Std.Array.make] using h)
