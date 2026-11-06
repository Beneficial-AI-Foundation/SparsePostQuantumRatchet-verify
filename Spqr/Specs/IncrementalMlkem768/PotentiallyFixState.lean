/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Lacramioara Astefanoaei
-/
module
public import SrcTranslated.Funs
public import SrcTranslated.FunsExternal
public import Spqr.Specs.Aeneas.SliceChunks
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

namespace Fips203.Refinement

/-- The little-endian bytes of `-2 … 2` modulo `q`, each taken in `[0, q)`. This is the encoding
of the FIPS 203 model, not the encoding of libcrux. -/
def e2Pairs : List (U8 × U8) :=
  [(0#u8, 0#u8), (1#u8, 0#u8), (2#u8, 0#u8), (255#u8, 12#u8), (0#u8, 13#u8)]

/-- A CBD coefficient with `η = 2` is one of `-2 … 2` modulo `q`, so its two little-endian bytes in
the model's encoding are one of `e2Pairs`. -/
theorem cbdCoeff_two_bytes (B : ℕ → UInt8) (i : ℕ) :
    (U8.ofUInt8 (coeffLo (cbdCoeff B 2 i)), U8.ofUInt8 (coeffHi (cbdCoeff B 2 i))) ∈ e2Pairs := by
  have h := cbdCoeff_abs_le B 2 i
  rw [abs_le] at h
  obtain ⟨d, h1, h2, hc⟩ : ∃ d : ℤ, -2 ≤ d ∧ d ≤ 2 ∧ cbdCoeff B 2 i = Zq.ofInt d :=
    ⟨_, by exact_mod_cast h.1, by exact_mod_cast h.2, rfl⟩
  rw [hc]
  interval_cases d <;> decide

/-- For a pair in `e2Pairs`, the little-endian word of its two bytes is `0`, `1`, `2`, `3327` or
`3328`. -/
theorem e2Pairs_from_le_bytes (a : Std.Array U8 2#usize) (p : U8 × U8) (hp : p ∈ e2Pairs)
    (ha : a.val = [p.1, p.2]) :
    core.num.U16.from_le_bytes a = 0#u16 ∨ core.num.U16.from_le_bytes a = 1#u16 ∨
      core.num.U16.from_le_bytes a = 2#u16 ∨ core.num.U16.from_le_bytes a = 3327#u16 ∨
      core.num.U16.from_le_bytes a = 3328#u16 := by
  rw [u16_from_le_bytes_of_val a _ _ ha]
  clear ha
  revert p
  decide

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
    · simp only [bind_ok, uncurry_apply_pair, Option.mem_def, List.length_nil, not_lt_zero,
        and_false, WP.spec_ok, reduceCtorEq, IsEmpty.forall_iff, implies_true]
    · have h_c : c.length = 2 := h_it c (by simp only [h_eq, List.mem_cons, true_or])
      have h_cs : ∀ d ∈ cs, d.length = 2 :=
        fun d hd => h_it d (by simp only [h_eq, List.mem_cons, hd, or_true])
      step as ⟨r, r_post⟩
      rcases r with a | ⟨⟩
      · simp only [core.result.Result.expect, lift, bind_ok]
        generalize core.num.U16.from_le_bytes a = i
        split
        all_goals first
          | (simp only [WP.spec_ok, List.length_cons]; exact ⟨h_cs, by omega⟩)
          | (simp only [WP.spec_ok, Option.mem_def, reduceCtorEq, IsEmpty.forall_iff,
              implies_true]; done)
          | exact WP.spec_bind (flip_endianness_of_encapsulation_state_spec es h_even h_gt)
              fun v hv => by
                simp only [WP.spec_ok, Option.mem_def, Option.some.injEq]
                rintro _ rfl
                exact hv.1
      · exact absurd h_c r_post
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
word is `0`, which continues, `1` or `2`, which stop with `None`, or `3327` or `3328`, which reach
the fallback arm `_ =>` and stop with `None`. -/
theorem potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275_loop_none
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
    · simp only [bind_ok, uncurry_apply_pair, Prod.exists, List.length_nil, not_lt_zero,
        and_false, WP.spec_ok]
    · have h_cs : ∀ d ∈ cs, ∃ p ∈ Fips203.Refinement.e2Pairs, d.val = [p.1, p.2] :=
        fun d hd => h_it d (by simp only [h_eq, List.mem_cons, hd, or_true])
      obtain ⟨p, hp, hc⟩ := h_it c (by simp only [h_eq, List.mem_cons, true_or])
      have h_c : c.length = 2 := by
        simp only [Slice.length, hc, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd]
      step as ⟨r, r_post⟩
      rcases r with a | ⟨⟩
      · simp only [core.result.Result.expect, lift, bind_ok]
        have hw := Fips203.Refinement.e2Pairs_from_le_bytes a p hp (r_post.1.trans hc)
        generalize core.num.U16.from_le_bytes a = i at hw
        split
        all_goals first
          | (simp only [WP.spec_ok]; done)
          | (simp only [WP.spec_ok, List.length_cons]; exact ⟨h_cs, by omega⟩)
          | exact absurd hw (by decide)
      · exact absurd h_c r_post
  · exact h_chunks

/-- On every state that the FIPS 203 model of `encapsulate1` writes, the workaround returns
`None`. -/
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
    apply potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275_loop_none
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
