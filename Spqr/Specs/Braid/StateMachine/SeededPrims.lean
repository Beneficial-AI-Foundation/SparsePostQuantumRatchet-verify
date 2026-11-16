/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Lacramioara Astefanoaei
-/
module

public import Spqr.Specs.Braid.StateMachine.Refinement
public import Spqr.Specs.IncrementalMlkem768.Generate
public import Spqr.Specs.IncrementalMlkem768.Encaps1
import all SrcTranslated.Funs
import all SrcTranslated.FunsExternal

/-! # A primitive instance with `KeyGen` and `Encaps1` on the bytes that `fill_bytes` returned

`CodeAgrees P` says that every output of the code's `generate` and `encaps1` is an output of
`KeyGen` and `Encaps1` for some randomness. `SeededAgrees P` fixes the randomness: it is the
buffer that the one `fill_bytes` call of `generate` or `encaps1` returned. `seededPrims` is an
instance with `KeyGen` = libcrux `from_seed` and `Encaps1` = libcrux `encapsulate1`, through
the FIPS 203 models, and `seededAgrees` proves `SeededAgrees seededPrims`.

**Source**: ML-KEM Braid Rev. 1, §1.2; spqr/src/incremental_mlkem768.rs:32-66 -/

@[expose] public section

open Aeneas Aeneas.Std Result spqr

namespace spqr.v1.chunked.states

open BraidModel

/-- The 64-byte seed read from the bytes `r`: byte `i` is `r[i]`, or 0 past the end of `r`. -/
def seedOfBytes (r : Bytes) : Fin 64 → UInt8 := fun i => (r.getD i.val 0#u8).toUInt8

/-- The 32-byte message read from the bytes `r`: byte `i` is `r[i]`, or 0 past the end of `r`. -/
def msgOfBytes (r : Bytes) : Fin 32 → UInt8 := fun i => (r.getD i.val 0#u8).toUInt8

/-- `KeyGen(randomness)` of §1.2 as libcrux `from_seed` on the 64-byte seed `randomness`,
through the FIPS 203 model: `(dk, ek_header, ek_vector)` = (`sk`, `pk1`, `pk2`). -/
noncomputable def fipsKeyGen (r : Bytes) : Bytes × Bytes × Bytes :=
  (Fips203.Refinement.keyPairList (seedOfBytes r),
    Fips203.Refinement.toU8List (Fips203.Refinement.pk1Bytes (seedOfBytes r)),
    Fips203.Refinement.toU8List (Fips203.Refinement.pk2Bytes (seedOfBytes r)))

/-- `Encaps1(ek_header, randomness)` of §1.2 as libcrux `encapsulate1` on the 32-byte message
`randomness`, through the FIPS 203 model: `(encaps_secret, ct1, shared_secret)`. A header of
fewer than 64 bytes gives three empty strings: libcrux rejects it and the code panics. -/
noncomputable def fipsEncaps1 (hdr r : Bytes) : Bytes × Bytes × Bytes :=
  if h : 64 ≤ hdr.length then
    (Fips203.Refinement.toU8List (Fips203.Refinement.stateOut hdr h (msgOfBytes r)),
      Fips203.Refinement.ct1List hdr h (msgOfBytes r),
      Fips203.Refinement.toU8List (Fips203.Refinement.ssOut hdr h (msgOfBytes r)))
  else ([], [], [])

/-- `CodeAgrees P`, and `KeyGen` and `Encaps1` of `P` are the code's `generate` and `encaps1` on
the bytes that their `fill_bytes` call returned, for a generator of any type. -/
structure SeededAgrees (P : CodePrims) : Prop extends CodeAgrees P where
  keyGen_seed : ∀ {R : Type} (i₁ : rand_1.rng.Rng R) (i₂ : rand_core_1.CryptoRng R)
    (rng rng₁ rng' : R) (buf : Slice Std.U8) (k : incremental_mlkem768.Keys),
    i₁.rand_core_1RngCoreInst.fill_bytes rng (Array.repeat 64#usize 0#u8).to_slice =
      ok (rng₁, buf) →
    buf.length = 64 →
    incremental_mlkem768.generate i₁ i₂ rng = ok (k, rng') →
    P.keyGen buf.val = (k.dk.val, k.hdr.val, k.ek.val)
  encaps1_seed : ∀ {R : Type} (i₁ : rand_1.rng.Rng R) (i₂ : rand_core_1.CryptoRng R)
    (rng rng₁ rng' : R) (buf : Slice Std.U8) (hdr ct1 es ss : alloc.vec.Vec Std.U8),
    i₁.rand_core_1RngCoreInst.fill_bytes rng (Array.repeat 32#usize 0#u8).to_slice =
      ok (rng₁, buf) →
    buf.length = 32 →
    incremental_mlkem768.encaps1 i₁ i₂ hdr rng = ok ((ct1, es, ss), rng') →
    P.encaps1 hdr.val buf.val = (es.val, ct1.val, ss.val)

/-- The seeded instance: `KeyGen` is `fipsKeyGen`, `Encaps1` is `fipsEncaps1`, and every other
primitive is that of a fixed instance that agrees with the code (`codeAgrees_exists`). -/
noncomputable def seededPrims : CodePrims :=
  { Classical.choose codeAgrees_exists with keyGen := fipsKeyGen, encaps1 := fipsEncaps1 }

/-! ## `generate` and `encaps1` on the buffer that `fill_bytes` returned -/

/-- If `fill_bytes` on the 64 zero bytes returns `(rng₁, b)`, then `generate` returns the FIPS
203 key pair of the seed that `generate` reads back from `b`, and the generator state
`rng₁`. -/
theorem generate_fill_spec {R : Type} (i₁ : rand_1.rng.Rng R) (i₂ : rand_core_1.CryptoRng R)
    (rng rng₁ : R) (b : Slice Std.U8)
    (hf : i₁.rand_core_1RngCoreInst.fill_bytes rng (Array.repeat 64#usize 0#u8).to_slice =
      ok (rng₁, b)) :
    incremental_mlkem768.generate i₁ i₂ rng ⦃ (r : incremental_mlkem768.Keys × R) =>
      let seed := Fips203.Refinement.seedOfArray (Array.from_slice (Array.repeat 64#usize 0#u8) b)
      r.2 = rng₁ ∧
      r.1.dk.val = Fips203.Refinement.keyPairList seed ∧
      r.1.hdr.val = Fips203.Refinement.toU8List (Fips203.Refinement.pk1Bytes seed) ∧
      r.1.ek.val = Fips203.Refinement.toU8List (Fips203.Refinement.pk2Bytes seed) ⦄ := by
  unfold incremental_mlkem768.generate
  simp only [lift, Array.to_slice_mut, uncurry_apply_pair, hf, bind_ok]
  step*
  have hv : v.val = a.val := by rw [alloc.vec.Vec.val, ← v_post, Array.val_to_slice]
  have hv1 : v1.val = a1.val := by rw [alloc.vec.Vec.val, ← v1_post, Array.val_to_slice]
  have hv2 : v2.val = a2.val := by rw [alloc.vec.Vec.val, ← v2_post, Array.val_to_slice]
  have henc : Spqr.Mlkem.mlkem768Params.encapsulationKeyBytes = 1152 := by decide
  have hhdr : Spqr.Mlkem.headerBytes = 64 := by decide
  refine ⟨?_, ?_, ?_⟩
  · rw [hv2, a2_post1, k_post1]
  · rw [hv, a_post, k_post1]
    simp only [henc, hhdr, Nat.reduceMul, Nat.reduceAdd]
    exact Fips203.Refinement.keyPairList_slice_pk1 _
  · rw [hv1, a1_post1, k_post1]
    simp only [henc, Nat.reduceMul]
    exact Fips203.Refinement.keyPairList_slice_pk2 _

/-- If `fill_bytes` on the 32 zero bytes returns `(rng₁, b)` and `hdr` has at least 64 bytes,
then `encaps1` returns the FIPS 203 round 1 values of the message that `encaps1` reads back from
`b`, and the generator state `rng₁`. -/
theorem encaps1_fill_spec {R : Type} (i₁ : rand_1.rng.Rng R) (i₂ : rand_core_1.CryptoRng R)
    (hdr : alloc.vec.Vec Std.U8) (rng rng₁ : R) (b : Slice Std.U8)
    (hf : i₁.rand_core_1RngCoreInst.fill_bytes rng (Array.repeat 32#usize 0#u8).to_slice =
      ok (rng₁, b))
    (h_hdr : 64 ≤ hdr.val.length) :
    incremental_mlkem768.encaps1 i₁ i₂ hdr rng ⦃ (r :
        ((alloc.vec.Vec Std.U8) × (alloc.vec.Vec Std.U8) × (alloc.vec.Vec Std.U8)) × R) =>
      let m := Fips203.Refinement.msgOfArray (Array.from_slice (Array.repeat 32#usize 0#u8) b)
      r.2 = rng₁ ∧
      r.1.1.val = Fips203.Refinement.ct1List hdr.val h_hdr m ∧
      r.1.2.1.val = Fips203.Refinement.toU8List (Fips203.Refinement.stateOut hdr.val h_hdr m) ∧
      r.1.2.2.val = Fips203.Refinement.toU8List (Fips203.Refinement.ssOut hdr.val h_hdr m) ⦄ := by
  unfold incremental_mlkem768.encaps1
  simp only [lift, Array.to_slice_mut, uncurry_apply_pair, hf, bind_ok]
  step*
  simp only [alloc.vec.Vec.deref_mut]
  have h_s2 : 64 ≤ s2.length := by simp only [Slice.length, s2_post]; exact h_hdr
  have h_state : Fips203.Refinement.encapsStateSize ≤ state.slice.length := by
    change Fips203.Refinement.encapsStateSize ≤ state.val.length; scalar_tac
  have h_ss : (32 : ℕ) ≤ ss.slice.length := by
    change (32 : ℕ) ≤ ss.val.length; scalar_tac
  step*
  subst ct1_post
  step*
  have h_state_len : state.slice.val.length = Fips203.Refinement.encapsStateSize := by
    change state.val.length = _
    simp only [state_post, List.length_replicate, «Fips203.Refinement.encapsStateSize_post»]
  have h_ss_len : ss.slice.val.length = (32 : ℕ) := by
    change ss.val.length = _
    simp only [ss_post, List.length_replicate, i1_post]
  have h_hdr' : (64 : ℕ) ≤ s2.val.length := h_s2
  refine ⟨?_, ?_, ?_⟩
  · change v.slice.val = _
    rw [← v_post, c_post, Array.val_to_slice, Fips203.Refinement.ct1Array, Array.make_val]
    exact Fips203.Refinement.ct1List_congr s2_post h_hdr' h_hdr _
  · change s5.val = _
    rw [ct1_post1, Fips203.Refinement.overwritePrefix_of_length_eq _ _ h_state_len,
      Fips203.Refinement.stateOut_congr s2_post h_hdr' h_hdr]
  · change s6.val = _
    rw [ct1_post2, Fips203.Refinement.overwritePrefix_of_length_eq _ _ h_ss_len,
      Fips203.Refinement.ssOut_congr s2_post h_hdr' h_hdr]

/-! ## Reading the seed and the message back -/

/-- Reading a 64-byte array through its list is `seedOfArray`. -/
theorem seedOfBytes_val (a : Array Std.U8 64#usize) :
    seedOfBytes a.val = Fips203.Refinement.seedOfArray a := by
  funext i
  have hi : i.val < a.val.length := by rw [Array.length_eq]; exact i.isLt
  simp only [seedOfBytes, Fips203.Refinement.seedOfArray, List.getD_eq_getElem _ _ hi]

/-- Reading a 32-byte array through its list is `msgOfArray`. -/
theorem msgOfBytes_val (a : Array Std.U8 32#usize) :
    msgOfBytes a.val = Fips203.Refinement.msgOfArray a := by
  funext i
  have hi : i.val < a.val.length := by rw [Array.length_eq]; exact i.isLt
  simp only [msgOfBytes, Fips203.Refinement.msgOfArray, List.getD_eq_getElem _ _ hi]

/-- On a buffer of the right length, `from_slice` returns the buffer's bytes. -/
theorem from_slice_val_of_length {n : Std.Usize} (a : Array Std.U8 n) (b : Slice Std.U8)
    (h : b.length = n.val) : (Array.from_slice a b).val = b.val :=
  Array.from_slice_val a b h

/-! ## Successful calls -/

/-- A successful `generate` made a successful `fill_bytes` call on the 64 zero bytes, and
returned the FIPS 203 key pair of the seed it read back from the returned buffer. -/
theorem generate_ok_fill {R : Type} (i₁ : rand_1.rng.Rng R) (i₂ : rand_core_1.CryptoRng R)
    (rng rng' : R) (k : incremental_mlkem768.Keys)
    (h : incremental_mlkem768.generate i₁ i₂ rng = ok (k, rng')) :
    ∃ b : Slice Std.U8,
      i₁.rand_core_1RngCoreInst.fill_bytes rng (Array.repeat 64#usize 0#u8).to_slice =
        ok (rng', b) ∧
      fipsKeyGen (Array.from_slice (Array.repeat 64#usize 0#u8) b).val =
        (k.dk.val, k.hdr.val, k.ek.val) := by
  have h0 := h
  simp only [incremental_mlkem768.generate, lift, Array.to_slice_mut, bind_ok,
    uncurry_apply_pair, Result.bind_eq_ok] at h0
  obtain ⟨⟨r1, b⟩, hf, -⟩ := h0
  obtain ⟨hr, hdk, hhdr, hek⟩ := WP.post_of_ok (generate_fill_spec i₁ i₂ rng r1 b hf) h
  simp only at hr
  subst hr
  refine ⟨b, hf, ?_⟩
  simp only [fipsKeyGen, seedOfBytes_val, hdk, hhdr, hek]

/-- A successful `encaps1` had a header of at least 64 bytes: `encapsulate1` rejects shorter
ones, and `encaps1` panics on the rejection. -/
theorem encaps1_ok_hdr {R : Type} (i₁ : rand_1.rng.Rng R) (i₂ : rand_core_1.CryptoRng R)
    (hdr : alloc.vec.Vec Std.U8) (rng rng' : R) (ct1 es ss : alloc.vec.Vec Std.U8)
    (h : incremental_mlkem768.encaps1 i₁ i₂ hdr rng = ok ((ct1, es, ss), rng')) :
    64 ≤ hdr.val.length := by
  simp only [incremental_mlkem768.encaps1, lift, Array.to_slice_mut, bind_ok,
    uncurry_apply_pair, Result.bind_eq_ok] at h
  obtain ⟨⟨r1, s1⟩, -, h1⟩ := h
  simp only [uncurry_apply_pair, alloc.vec.Vec.deref_mut, Result.bind_eq_ok] at h1
  obtain ⟨_, -, _, -, _, -, _, -, s2, hs2, ⟨c1, s5, s6⟩, he, h2⟩ := h1
  simp only [uncurry_apply_pair, Result.bind_eq_ok] at h2
  obtain ⟨c, hc, -⟩ := h2
  simp only [alloc.vec.Vec.as_slice, Result.ok.injEq] at hs2
  subst hs2
  by_contra hlt
  rw [Fips203.Refinement.encapsulate1_short_header _ _ _ _ (by
    simp only [Slice.length, Slice.from_val]; omega)] at he
  simp only [Result.ok.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, -, -⟩ := he
  simp only [core.result.Result.expect] at hc
  exact fail_not_ok hc

/-- A successful `encaps1` made a successful `fill_bytes` call on the 32 zero bytes, and
returned the FIPS 203 round 1 values of the message it read back from the returned buffer. -/
theorem encaps1_ok_fill {R : Type} (i₁ : rand_1.rng.Rng R) (i₂ : rand_core_1.CryptoRng R)
    (hdr : alloc.vec.Vec Std.U8) (rng rng' : R) (ct1 es ss : alloc.vec.Vec Std.U8)
    (h : incremental_mlkem768.encaps1 i₁ i₂ hdr rng = ok ((ct1, es, ss), rng')) :
    ∃ b : Slice Std.U8,
      i₁.rand_core_1RngCoreInst.fill_bytes rng (Array.repeat 32#usize 0#u8).to_slice =
        ok (rng', b) ∧
      fipsEncaps1 hdr.val (Array.from_slice (Array.repeat 32#usize 0#u8) b).val =
        (es.val, ct1.val, ss.val) := by
  have h64 := encaps1_ok_hdr i₁ i₂ hdr rng rng' ct1 es ss h
  have h0 := h
  simp only [incremental_mlkem768.encaps1, lift, Array.to_slice_mut, bind_ok,
    uncurry_apply_pair, Result.bind_eq_ok] at h0
  obtain ⟨⟨r1, b⟩, hf, -⟩ := h0
  obtain ⟨hr, hct1, hes, hss⟩ :=
    WP.post_of_ok (encaps1_fill_spec i₁ i₂ hdr rng r1 b hf h64) h
  simp only at hr
  subst hr
  refine ⟨b, hf, ?_⟩
  simp only at hct1 hes hss
  rw [fipsEncaps1, dite_eq_left h64, msgOfBytes_val, hct1, hes, hss]

/-! ## The seeded instance agrees with the code -/

/-- Replacing `KeyGen` and `Encaps1` of an instance that agrees with the code by functions that
reach every output of `generate` and `encaps1` gives an instance that agrees with the code. -/
theorem codeAgrees_with (P : CodePrims) (hP : CodeAgrees P) (kg : Bytes → Bytes × Bytes × Bytes)
    (e1 : Bytes → Bytes → Bytes × Bytes × Bytes)
    (hkg : ∀ {R : Type} (i₁ : rand_1.rng.Rng R) (i₂ : rand_core_1.CryptoRng R) (rng rng' : R)
      (k : incremental_mlkem768.Keys),
      incremental_mlkem768.generate i₁ i₂ rng = ok (k, rng') →
      ∃ r, kg r = (k.dk.val, k.hdr.val, k.ek.val))
    (he1 : ∀ {R : Type} (i₁ : rand_1.rng.Rng R) (i₂ : rand_core_1.CryptoRng R) (rng rng' : R)
      (hdr ct1 es ss : alloc.vec.Vec Std.U8),
      incremental_mlkem768.encaps1 i₁ i₂ hdr rng = ok ((ct1, es, ss), rng') →
      ∃ r, e1 hdr.val r = (es.val, ct1.val, ss.val)) :
    CodeAgrees { P with keyGen := kg, encaps1 := e1 } :=
  { hP with keyGen := hkg, encaps1 := he1 }

/-- The seeded instance agrees with the code, with `KeyGen` and `Encaps1` on the bytes that
`fill_bytes` returned. -/
theorem seededAgrees : SeededAgrees seededPrims := by
  refine ⟨codeAgrees_with _ (Classical.choose_spec codeAgrees_exists) _ _ ?_ ?_, ?_, ?_⟩
  · intro R i₁ i₂ rng rng' k h
    obtain ⟨b, -, hk⟩ := generate_ok_fill i₁ i₂ rng rng' k h
    exact ⟨_, hk⟩
  · intro R i₁ i₂ rng rng' hdr ct1 es ss h
    obtain ⟨b, -, he⟩ := encaps1_ok_fill i₁ i₂ hdr rng rng' ct1 es ss h
    exact ⟨_, he⟩
  · intro R i₁ i₂ rng rng₁ rng' buf k hf hlen h
    obtain ⟨b, hf', hk⟩ := generate_ok_fill i₁ i₂ rng rng' k h
    rw [hf, Result.ok.injEq, Prod.mk.injEq] at hf'
    obtain ⟨-, rfl⟩ := hf'
    rw [from_slice_val_of_length _ _ hlen] at hk
    exact hk
  · intro R i₁ i₂ rng rng₁ rng' buf hdr ct1 es ss hf hlen h
    obtain ⟨b, hf', he⟩ := encaps1_ok_fill i₁ i₂ hdr rng rng' ct1 es ss h
    rw [hf, Result.ok.injEq, Prod.mk.injEq] at hf'
    obtain ⟨-, rfl⟩ := hf'
    rw [from_slice_val_of_length _ _ hlen] at he
    exact he

end spqr.v1.chunked.states
