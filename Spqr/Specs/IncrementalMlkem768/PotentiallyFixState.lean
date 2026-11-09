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
or the byte-swapped state. It flips the state only on the words `0x0100`, `0x0200` and `0xFEFF`.
This file proves three things:

* its hax contract: on a 2080-byte state it succeeds, and a returned state also has 2080 bytes;
* on a state whose `e₂` words are signed 16-bit little-endian values in `-2 … 2`, it returns
  `None`. This is the encoding that libcrux-ml-kem 0.0.10 writes;
* on every state that the FIPS 203 model of `encapsulate1` writes, it returns `None`. The model
  stores each `e₂` coefficient, `-2 … 2` modulo `q`, as its value in `[0, q)`, so every word of
  the region is `0`, `1`, `2`, `3327` or `3328`. This is not the libcrux encoding (issue #800), so
  this result is about the model only.

Both `None` results follow from one theorem over any set of byte pairs that never forms a flip
word. -/

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

/-- The little-endian bytes of `-2 … 2` as signed 16-bit words. This is the encoding of
libcrux-ml-kem 0.0.10 (issue #800). -/
def signedE2Pairs : List (U8 × U8) :=
  [(0#u8, 0#u8), (1#u8, 0#u8), (2#u8, 0#u8), (255#u8, 255#u8), (254#u8, 255#u8)]

/-- The little-endian word of two bytes is not one of the three words on which the workaround
flips the state: `0x0100`, `0x0200` and `0xFEFF`. -/
def NoFlipPair (p : U8 × U8) : Prop :=
  core.num.U16.from_le_bytes (Std.Array.make 2#usize [p.1, p.2] (by simp)) ∉
    [256#u16, 512#u16, 65279#u16]

instance (p : U8 × U8) : Decidable (NoFlipPair p) := by
  unfold NoFlipPair; infer_instance

theorem e2Pairs_noFlip : ∀ p ∈ e2Pairs, NoFlipPair p := by decide

theorem signedE2Pairs_noFlip : ∀ p ∈ signedE2Pairs, NoFlipPair p := by decide

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

/-- If every chunk is a pair in `S`, and no pair in `S` forms a flip word, the scan loop returns
`None`. Each word continues the scan or stops it with `None`, either in an explicit arm or in the
fallback arm `_ =>`. -/
theorem potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275_loop_none
    (S : List (U8 × U8)) (hS : ∀ p ∈ S, Fips203.Refinement.NoFlipPair p)
    (iter : core.slice.iter.Chunks U8) (es : alloc.vec.Vec U8)
    (h_chunks : ∀ c ∈ iter.chunks, ∃ p ∈ S, c.val = [p.1, p.2]) :
    potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275_loop iter es
      ⦃ (mf : Option (alloc.vec.Vec U8)) => mf = none ⦄ := by
  unfold potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275_loop
  apply loop.spec_decr_nat
    (measure := fun (it : core.slice.iter.Chunks U8) => it.chunks.length)
    (inv := fun (it : core.slice.iter.Chunks U8) => ∀ c ∈ it.chunks, ∃ p ∈ S, c.val = [p.1, p.2])
  · intro it h_it
    unfold potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275_loop.body
    unfold core.slice.iter.Chunks.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next
    rcases h_eq : it.chunks with _ | ⟨c, cs⟩
    · simp only [bind_ok, uncurry_apply_pair, Prod.exists, List.length_nil, not_lt_zero,
        and_false, WP.spec_ok]
    · have h_cs : ∀ d ∈ cs, ∃ p ∈ S, d.val = [p.1, p.2] :=
        fun d hd => h_it d (by simp only [h_eq, List.mem_cons, hd, or_true])
      obtain ⟨p, hp, hc⟩ := h_it c (by simp only [h_eq, List.mem_cons, true_or])
      have h_c : c.length = 2 := by
        simp only [Slice.length, hc, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd]
      step as ⟨r, r_post⟩
      rcases r with a | ⟨⟩
      · simp only [core.result.Result.expect, lift, bind_ok]
        have hw := hS p hp
        rw [Fips203.Refinement.NoFlipPair, ← u16_from_le_bytes_of_val a _ _ (r_post.1.trans hc)]
          at hw
        generalize core.num.U16.from_le_bytes a = i at hw
        split
        all_goals first
          | (simp only [WP.spec_ok]; done)
          | (simp only [WP.spec_ok, List.length_cons]; exact ⟨h_cs, by omega⟩)
          | exact absurd hw (by decide)
      · exact absurd h_c r_post
  · exact h_chunks

/-- On a 2080-byte state whose `e₂` words are all pairs in `S`, the workaround returns `None` when
no pair in `S` forms a flip word. -/
theorem potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275_none
    (S : List (U8 × U8)) (hS : ∀ p ∈ S, Fips203.Refinement.NoFlipPair p)
    (es : alloc.vec.Vec U8) (h_len : es.val.length = 2080)
    (h_e2 : ∀ k < 256, (es.val[1536 + 2 * k]!, es.val[1536 + 2 * k + 1]!) ∈ S) :
    potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275 es = ok none := by
  have H : potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275 es
      ⦃ (mf : Option (alloc.vec.Vec U8)) => mf = none ⦄ := by
    unfold potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275
    step
    step
    step
    step with core.slice.Slice.chunks_two_content
    apply potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275_loop_none S hS
    intro c hc
    obtain ⟨k, hk, hcv⟩ := iter_post c hc
    have hk' : k < 256 := by omega
    refine ⟨(s.val[2 * k]!, s.val[2 * k + 1]!), ?_, hcv⟩
    rw [s_post, List.getElem!_slice _ _ _ _ ⟨by omega, by omega⟩,
      List.getElem!_slice _ _ _ _ ⟨by omega, by omega⟩]
    simpa only [Nat.add_assoc] using h_e2 k hk'
  obtain ⟨mf, h_eq, h_mf⟩ := WP.spec_imp_exists H
  rw [h_eq, h_mf]

/-- On a 2080-byte state whose `e₂` words are signed 16-bit little-endian values in `-2 … 2`, the
workaround returns `None`. This is the encoding that libcrux-ml-kem 0.0.10 writes (issue #800). -/
theorem potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275_signedE2
    (es : alloc.vec.Vec U8) (h_len : es.val.length = 2080)
    (h_e2 : ∀ k < 256,
      (es.val[1536 + 2 * k]!, es.val[1536 + 2 * k + 1]!) ∈ Fips203.Refinement.signedE2Pairs) :
    potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275 es = ok none :=
  potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275_none _
    Fips203.Refinement.signedE2Pairs_noFlip es h_len h_e2

/-- On every state that the FIPS 203 model of `encapsulate1` writes, the workaround returns
`None`. The model stores `e₂` in `[0, q)`, not in the signed encoding of libcrux-ml-kem 0.0.10, so
the real buffer does not satisfy `h_es` (issue #800). For the bytes that libcrux writes, see
`potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275_signedE2`. -/
theorem potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275_stateOut
    (hdr : List U8) (h_hdr : 64 ≤ hdr.length) (m : Fin 32 → UInt8)
    (es : alloc.vec.Vec U8)
    (h_es : es.val = Fips203.Refinement.toU8List (Fips203.Refinement.stateOut hdr h_hdr m)) :
    potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275 es = ok none := by
  refine potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275_none _
    Fips203.Refinement.e2Pairs_noFlip es ?_ fun k hk => ?_
  · simp only [h_es, Fips203.Refinement.toU8List, List.length_ofFn,
      Fips203.Refinement.encapsStateSize]
  · rw [h_es]
    exact Fips203.Refinement.stateOut_e2_bytes hdr h_hdr m k hk

end spqr.incremental_mlkem768
