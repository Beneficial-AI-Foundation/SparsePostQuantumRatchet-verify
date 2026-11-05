/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Lacramioara Astefanoaei
-/
module
public import SrcTranslated.Funs
public import SrcTranslated.FunsExternal
public import Spqr.Specs.Aeneas.SliceChunksExact
public import Spqr.Specs.Aeneas.ResultExpect
public import Spqr.Specs.IncrementalMlkem768.FlipEndianness
/-! # Spec theorems for the libcrux 1275 endianness workaround

Rust: `spqr::incremental_mlkem768::potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275`
(`src/incremental_mlkem768.rs`, lines 92-138).

The function scans the `e₂` region `es[1536 .. 2048]` in 2-byte words and returns either `None`
or the byte-swapped state. This file proves its hax contract: on a 2080-byte state it succeeds,
and a returned state also has 2080 bytes. -/

@[expose] public section

open Aeneas Aeneas.Std Result

/-- `chunks 2` on a slice of even length returns chunks of exactly 2 elements. -/
@[step]
theorem core.slice.Slice.chunks_two_spec {T : Type} (s : Slice T) (h_even : s.length % 2 = 0) :
    core.slice.Slice.chunks s 2#usize ⦃ (it : core.slice.iter.Chunks T) =>
      ∀ c ∈ it.chunks, c.length = 2 ⦄ := by
  have h_rem : (List.toChunksExact 2 (by decide) s.val).2 = [] := by
    have := List.toChunksExact_remainder_length_le_mod' (n := 2) (by decide) s.val
    simp only [Slice.length] at h_even
    exact List.eq_nil_of_length_eq_zero (by omega)
  simp only [core.slice.Slice.chunks]
  simp only [show (2#usize : Usize).val > 0 by decide, _root_.dite_true, WP.spec_ok]
  intro c hc
  simp only [show (2#usize : Usize).val = 2 by rfl] at hc ⊢
  simp only [h_rem, ite_true, List.append_nil, List.mem_map, List.mem_attach, true_and,
    Subtype.exists] at hc
  obtain ⟨c', hc', rfl⟩ := hc
  simpa [Slice.length] using
    List.toChunksExact_chunk_exact_length' (n := 2) (by decide) s.val c' hc'

namespace spqr.incremental_mlkem768

/-- The scan loop succeeds on chunks of 2 bytes, and a returned state has the length of `es`. -/
theorem potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275_loop_spec
    (iter : core.slice.iter.Chunks U8) (es : alloc.vec.Vec U8)
    (h_chunks : ∀ c ∈ iter.chunks, c.length = 2)
    (h_even : es.length % 2 = 0) (h_gt : 32 < es.length) :
    potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275_loop iter es
      ⦃ (mf : Option (alloc.vec.Vec U8)) => ∀ v ∈ mf, v.length = es.length ⦄ := by
  unfold potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275_loop
  apply loop.spec_decr_nat
    (measure := fun (it : core.slice.iter.Chunks U8) => it.chunks.length)
    (inv := fun (it : core.slice.iter.Chunks U8) => ∀ c ∈ it.chunks, c.length = 2)
  · intro it h_it
    unfold potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275_loop.body
    unfold core.slice.iter.Chunks.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next
    rcases h_eq : it.chunks with _ | ⟨c, cs⟩
    · simp [WP.spec_ok]
    · have h_c : c.length = 2 := h_it c (by simp [h_eq])
      have h_cs : ∀ d ∈ cs, d.length = 2 := fun d hd => h_it d (by simp [h_eq, hd])
      step*
      cases r with
      | Err e => simp_all
      | Ok a =>
        simp only [core.result.Result.expect, lift, bind_ok]
        generalize core.num.U16.from_le_bytes a = i
        split
        all_goals first
          | (simp only [WP.spec_ok, List.length_cons]; exact ⟨h_cs, by omega⟩)
          | (simp [WP.spec_ok]; done)
          | step*
  · exact h_chunks

/-- The hax contract of the libcrux 1275 workaround (`src/incremental_mlkem768.rs`, lines
85-90). On a 2080-byte state the call succeeds, and a returned state also has 2080 bytes. -/
@[step]
theorem potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275_spec
    (es : alloc.vec.Vec U8) (h_es : es.length = 2080) :
    potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275 es
      ⦃ (mf : Option (alloc.vec.Vec U8)) => ∀ v ∈ mf, v.length = 2080 ⦄ := by
  unfold potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275
  step*
  simpa only [h_es] using
    potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275_loop_spec iter es iter_post
      (by omega) (by omega)

end spqr.incremental_mlkem768
