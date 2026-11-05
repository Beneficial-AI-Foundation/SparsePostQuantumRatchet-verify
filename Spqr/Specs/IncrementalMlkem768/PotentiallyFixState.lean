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
or the byte-swapped state. This file proves two things:

* its hax contract: on a 2080-byte state it succeeds, and a returned state also has 2080 bytes;
* on every state that the FIPS 203 model of `encapsulate1` writes, it returns `None`. The model
  stores each `e₂` coefficient, `-2 … 2` modulo `q`, as its value in `[0, q)` in two
  little-endian bytes, so every word of the region is `0`, `1`, `2`, `3327` or `3328`, and the
  scan never reaches a flip pattern. -/

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

/-- `chunks 2` on a slice of even length returns the pairs `[s[2k], s[2k+1]]`, in order. -/
theorem core.slice.Slice.chunks_two_content {T : Type} [Inhabited T] (s : Slice T)
    (h_even : s.length % 2 = 0) :
    core.slice.Slice.chunks s 2#usize ⦃ (it : core.slice.iter.Chunks T) =>
      ∀ c ∈ it.chunks, ∃ k, 2 * k + 1 < s.length ∧
        c.val = [s.val[2 * k]!, s.val[2 * k + 1]!] ⦄ := by
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

namespace Fips203.Refinement

/-- The five byte pairs that a CBD coefficient with `η = 2` serializes to. -/
def e2Pairs : List (U8 × U8) :=
  [(0#u8, 0#u8), (1#u8, 0#u8), (2#u8, 0#u8), (255#u8, 12#u8), (0#u8, 13#u8)]

/-- A CBD coefficient with `η = 2` is one of `-2 … 2` modulo `q`, so its two little-endian bytes
are one of `e2Pairs`. -/
theorem cbdCoeff_two_bytes (B : ℕ → UInt8) (i : ℕ) :
    (U8.ofUInt8 (coeffLo (cbdCoeff B 2 i)), U8.ofUInt8 (coeffHi (cbdCoeff B 2 i))) ∈ e2Pairs := by
  have h := cbdCoeff_abs_le B 2 i
  rw [abs_le] at h
  obtain ⟨d, h1, h2, hc⟩ : ∃ d : ℤ, -2 ≤ d ∧ d ≤ 2 ∧ cbdCoeff B 2 i = Zq.ofInt d :=
    ⟨_, by exact_mod_cast h.1, by exact_mod_cast h.2, rfl⟩
  rw [hc]
  interval_cases d <;> decide

/-- In every state that the model of `encapsulate1` writes, the bytes at `1536 + 2k` and
`1537 + 2k` encode `e₂[k]`, so they are one of `e2Pairs`. -/
theorem stateOut_e2_bytes (hdr : List U8) (h_hdr : 64 ≤ hdr.length) (m : Fin 32 → UInt8)
    (k : ℕ) (hk : k < 256) :
    ((toU8List (stateOut hdr h_hdr m))[1536 + 2 * k]!,
      (toU8List (stateOut hdr h_hdr m))[1536 + 2 * k + 1]!) ∈ e2Pairs := by
  have hl : (toU8List (stateOut hdr h_hdr m)).length = 2080 := by
    simp only [toU8List, List.length_ofFn, encapsStateSize]
  rw [getElem!_pos _ _ (by omega), getElem!_pos _ _ (by omega)]
  simp only [toU8List, List.getElem_ofFn, stateOut]
  have e0 := stateBytes_e2 (encaps1Output hdr h_hdr m).state ⟨2 * k, by omega⟩
    (by simp [encapsStateSize]; omega)
  have e1 := stateBytes_e2 (encaps1Output hdr h_hdr m).state ⟨2 * k + 1, by omega⟩
    (by simp [encapsStateSize]; omega)
  simp only [] at e0 e1
  simp only [Nat.add_assoc] at e1 ⊢
  simp only [e0, e1]
  simp only [polyBytes]
  have hk0 : (2 * k) / 2 = k := by omega
  have hk1 : (2 * k + 1) / 2 = k := by omega
  simp only [hk0, hk1, Nat.mul_mod_right, show (2 * k + 1) % 2 = 1 by omega, ite_true,
    one_ne_zero, ite_false]
  exact cbdCoeff_two_bytes _ k

end Fips203.Refinement

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

/-- If every chunk is one of `Fips203.Refinement.e2Pairs`, the scan loop returns `None`. The
word is `0`, which continues, or `1`, `2`, `3327` or `3328`, which stop with `None`. -/
theorem loop_none
    (iter : core.slice.iter.Chunks U8) (es : alloc.vec.Vec U8)
    (h_chunks : ∀ c ∈ iter.chunks, ∃ p ∈ Fips203.Refinement.e2Pairs, c.val = [p.1, p.2]) :
    potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275_loop iter es
      ⦃ (mf : Option (alloc.vec.Vec U8)) => mf = none ⦄ := by
  unfold potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275_loop
  apply loop.spec_decr_nat
    (measure := fun (it : core.slice.iter.Chunks U8) => it.chunks.length)
    (inv := fun (it : core.slice.iter.Chunks U8) =>
      ∀ c ∈ it.chunks, ∃ p ∈ Fips203.Refinement.e2Pairs, c.val = [p.1, p.2])
  · intro it h_it
    unfold potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275_loop.body
    unfold core.slice.iter.Chunks.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next
    rcases h_eq : it.chunks with _ | ⟨c, cs⟩
    · simp [WP.spec_ok]
    · have h_cs : ∀ d ∈ cs, ∃ p ∈ Fips203.Refinement.e2Pairs, d.val = [p.1, p.2] :=
        fun d hd => h_it d (by simp [h_eq, hd])
      obtain ⟨p, hp, hc⟩ := h_it c (by simp [h_eq])
      have h_c : c.length = 2 := by simp [Slice.length, hc]
      step*
      cases r with
      | Err e => simp_all
      | Ok a =>
        simp only [core.result.Result.expect, lift, bind_ok]
        have ha : a.val = [p.1, p.2] := by simp_all
        simp only [Fips203.Refinement.e2Pairs, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl
        all_goals rw [u16_from_le_bytes_of_val a _ _ ha]
        · rw [show core.num.U16.from_le_bytes
              (Std.Array.make 2#usize [0#u8, 0#u8] (by simp)) = 0#u16 by decide]
          split <;> first
            | (rename_i heq; exact absurd heq (by decide))
            | simp_all [WP.spec_ok]
        · rw [show core.num.U16.from_le_bytes
              (Std.Array.make 2#usize [1#u8, 0#u8] (by simp)) = 1#u16 by decide]
          split <;> first
            | (rename_i heq; exact absurd heq (by decide))
            | simp_all [WP.spec_ok]
        · rw [show core.num.U16.from_le_bytes
              (Std.Array.make 2#usize [2#u8, 0#u8] (by simp)) = 2#u16 by decide]
          split <;> first
            | (rename_i heq; exact absurd heq (by decide))
            | simp_all [WP.spec_ok]
        · rw [show core.num.U16.from_le_bytes
              (Std.Array.make 2#usize [255#u8, 12#u8] (by simp)) = 3327#u16 by decide]
          split <;> first
            | (rename_i heq; exact absurd heq (by decide))
            | simp_all [WP.spec_ok]
        · rw [show core.num.U16.from_le_bytes
              (Std.Array.make 2#usize [0#u8, 13#u8] (by simp)) = 3328#u16 by decide]
          split <;> first
            | (rename_i heq; exact absurd heq (by decide))
            | simp_all [WP.spec_ok]
  · exact h_chunks

/-- On every state that the FIPS 203 model of `encapsulate1` writes, the workaround returns
`None`. So `encaps2` uses the state of `encaps1` unchanged. -/
theorem potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275_stateOut
    (hdr : List U8) (h_hdr : 64 ≤ hdr.length) (m : Fin 32 → UInt8)
    (es : alloc.vec.Vec U8)
    (h_es : es.val = Fips203.Refinement.toU8List (Fips203.Refinement.stateOut hdr h_hdr m)) :
    potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275 es = ok none := by
  have h_len : es.val.length = 2080 := by
    simp only [h_es, Fips203.Refinement.toU8List, List.length_ofFn,
      Fips203.Refinement.encapsStateSize]
  have H : potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275 es
      ⦃ (mf : Option (alloc.vec.Vec U8)) => mf = none ⦄ := by
    unfold potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275
    step
    step
    step
    step with core.slice.Slice.chunks_two_content
    apply loop_none
    intro c hc
    obtain ⟨k, hk, hcv⟩ := iter_post c hc
    have hk' : k < 256 := by omega
    refine ⟨(s.val[2 * k]!, s.val[2 * k + 1]!), ?_, hcv⟩
    rw [s_post, List.getElem!_slice _ _ _ _ ⟨by omega, by omega⟩,
      List.getElem!_slice _ _ _ _ ⟨by omega, by omega⟩, h_es]
    simpa only [Nat.add_assoc] using Fips203.Refinement.stateOut_e2_bytes hdr h_hdr m k hk'
  obtain ⟨mf, h_eq, h_mf⟩ := WP.spec_imp_exists H
  rw [h_eq, h_mf]

end spqr.incremental_mlkem768
