/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Basic
import Spqr.Specs.Encoding.Gf.Reduce.ReduceFromByte
import Spqr.Specs.Encoding.Gf.Unaccelerated.PolyMul
import Mathlib.RingTheory.Polynomial.Basic

open Aeneas Aeneas.Std Result
open Polynomial spqr.encoding.gf.unaccelerated

namespace spqr.encoding.gf.reduce




open Polynomial spqr.encoding.gf.unaccelerated in
/-- The natural-number encoding of the irreducible polynomial
    POLY = 0x1100b corresponds to `POLY_GF2` in GF(2)[X].

    `natToGF2Poly 0x1100b = X¹⁶ + X¹² + X³ + X + 1 = POLY_GF2` -/
private lemma natToGF2Poly_POLY :
    natToGF2Poly 0x1100b = POLY_GF2 := by
  ext m
  simp only [natToGF2Poly_coeff]
  unfold POLY_GF2
  simp only [coeff_add, coeff_X_pow, coeff_X, coeff_one]
  rcases Nat.lt_or_ge m 17 with hlt | hge
  · interval_cases m <;> decide
  · have htb : Nat.testBit (0x1100b : Nat) m = false := by
      apply Nat.testBit_eq_false_of_lt
      exact lt_of_lt_of_le (by norm_num : (0x1100b : Nat) < 2 ^ 17)
        (Nat.pow_le_pow_right (by norm_num) hge)
    simp only [htb, ↓reduceIte, show m ≠ 16 from by omega, show m ≠ 12 from by omega,
               show m ≠ 3 from by omega, show (1 : ℕ) ≠ m from by omega, show m ≠ 0 from by omega,
               add_zero]
    simp


/-- Array indexing is unchanged after `set` at a different position. -/
private lemma index_usize_set_ne
    {α : Type} {n : Std.Usize}
    (v : Array α n) (i j : Std.Usize) (x : α)
    (hne : Nat.not_eq i.val j.val) :
    Array.index_usize (v.set i x) j = Array.index_usize v j := by
  unfold Array.index_usize
  simp only [Array.getElem?_Usize_eq, Array.set_val_eq]
  have hne' : i.val ≠ j.val := Nat.not_eq_imp_not_eq hne
  congr 1
  exact List.getElem?_set_ne hne'

/-- Array indexing at the `set` position returns the new value. -/
private lemma index_usize_set_eq_of_val_eq
    {α : Type} {n : Std.Usize}
    (v : Array α n) (i j : Std.Usize) (x : α)
    (hji : j.val = i.val) (hi : i.val < n.val) :
    Array.index_usize (v.set i x) j = ok x := by
  unfold Array.index_usize
  simp only [Array.getElem?_Usize_eq, Array.set_val_eq]
  have hlen : j.val < v.val.length := by
    have := Array.length_eq v; omega
  rw [show i.val = j.val from hji.symm]
  rw [List.getElem?_set_self hlen]

@[step]
theorem reduce_bytes_loop_spec
    (out : Array Std.U16 256#usize) (i : Std.Usize)
    (hi : i.val ≤ 256)
    (h_inv : ∀ j : Std.Usize, j.val < i.val →
      ∃ v : Std.U16,
        Array.index_usize out j = ok v ∧
          v.val = reduceByteTable j.val) :
    reduce_bytes_loop out i ⦃ result =>
      ∀ j : Std.Usize, j.val < 256 →
        ∃ v : Std.U16,
          Array.index_usize result j = ok v ∧
            v.val = reduceByteTable j.val ⦄ := by
  unfold reduce_bytes_loop
  apply loop.spec_decr_nat
    (measure := fun (p : (Array Std.U16 256#usize) × Std.Usize) => 256 - p.2.val)
    (inv := fun (p : (Array Std.U16 256#usize) × Std.Usize) =>
      p.2.val ≤ 256 ∧
      ∀ j : Std.Usize, j.val < p.2.val →
        ∃ v : Std.U16,
          Array.index_usize p.1 j = ok v ∧
            v.val = reduceByteTable j.val)
  · intro ⟨out', i'⟩ ⟨hi'_bound, h_inv'⟩
    simp only []
    unfold reduce_bytes_loop.body
    by_cases hLt : i' < 256#usize
    · simp only [hLt, ↓reduceIte]
      step*
      refine ⟨by scalar_tac, fun j hj => ?_, by scalar_tac⟩
      by_cases hjne : j.val = i'.val
      · exact ⟨i3,
          by rw [a_post];
             exact index_usize_set_eq_of_val_eq out' i' j _ hjne (by scalar_tac),
          by simp_all [UScalar.cast_val_eq]⟩
      · obtain ⟨v, hv_idx, hv_val⟩ := h_inv' j (by scalar_tac)
        exact ⟨v,
          by rw [a_post];
             rw [index_usize_set_ne out' i' j _ (by scalar_tac)];
             exact hv_idx,
          hv_val⟩
    · simp only [hLt, ↓reduceIte]
      intro j hj
      exact h_inv' j (by scalar_tac)
  · exact ⟨hi, h_inv⟩

@[step]
theorem reduce_bytes_spec :
    reduce_bytes ⦃ result =>
      ∀ j : Std.Usize, j.val < 256 →
        ∃ v : Std.U16,
          Array.index_usize result j = ok v ∧
            v.val = reduceByteTable j.val ⦄ := by
  unfold reduce_bytes
  apply WP.spec_mono (reduce_bytes_loop_spec _ 0#usize (by scalar_tac)
    (fun j hj => by scalar_tac))
  intro result hres
  exact hres

/-! ## Full-range polynomial correctness of the reduction table -/

/-- Combined high-to-low loop function tracking both `a` (byte) and `out` (accumulator). -/
private def reduceByteLoopFull (a out : Nat) : (n : Nat) → Nat × Nat
  | 0     => (a, out)
  | n + 1 =>
    if a.testBit n then
      let ps := 0x1100b <<< n
      reduceByteLoopFull ((a ^^^ (ps >>> 16)) % 256) (out ^^^ ps) n
    else
      reduceByteLoopFull a out n

/-- The second component of `reduceByteLoopFull` agrees with `reduceFromByteLoopSpec`. -/
private lemma reduceByteLoopFull_snd_eq (a out n : Nat) :
    (reduceByteLoopFull a out n).2 = reduceFromByteLoopSpec a out n := by
  induction n generalizing a out with
  | zero => rfl
  | succ n ih =>
    simp only [reduceByteLoopFull, reduceFromByteLoopSpec]
    split <;> exact ih _ _

/-- Helper: XOR of two values < 2^8 is < 2^8. -/
private lemma xor_lt_256 (a b : Nat) (ha : a < 256) (hb : b < 256) : a ^^^ b < 256 := by
  apply Nat.lt_of_testBit 8
  · simp only [Nat.testBit_xor]
    have h1 : a.testBit 8 = false :=
      Nat.testBit_eq_false_of_lt (by linarith)
    have h2 : b.testBit 8 = false :=
      Nat.testBit_eq_false_of_lt (by linarith)
    simp [h1, h2]
  · decide
  · intro j hj
    have h1 : Nat.testBit (a ^^^ b) j = false := by
      simp only [Nat.testBit_xor]
      have ha' : a.testBit j = false := Nat.testBit_eq_false_of_lt
        (calc a < 256 := ha
          _ = 2^8 := by norm_num
          _ ≤ 2^j := by apply Nat.pow_le_pow_right (by norm_num : 0 < 2); omega)
      have hb' : b.testBit j = false := Nat.testBit_eq_false_of_lt
        (calc b < 256 := hb
          _ = 2^8 := by norm_num
          _ ≤ 2^j := by apply Nat.pow_le_pow_right (by norm_num : 0 < 2); omega)
      simp [ha', hb']
    have h2 : Nat.testBit 256 j = false := by
      apply Nat.testBit_eq_false_of_lt
      calc (256 : Nat) = 2^8 := by norm_num
        _ < 2^j := by apply Nat.pow_lt_pow_right (by norm_num : 1 < 2); omega
    rw [h1, h2]


/-- The algebraic invariant for `reduceByteLoopFull` (for `a < 256`). -/
private lemma reduceByteLoopFull_inv (a out : Nat) (n : Nat) (ha : a < 256) :
    (natToGF2Poly ((reduceByteLoopFull a out n).2 % 2 ^ 16) +
     natToGF2Poly (reduceByteLoopFull a out n).1 * X ^ 16) %ₘ POLY_GF2 =
    (natToGF2Poly (out % 2 ^ 16) + natToGF2Poly a * X ^ 16) %ₘ POLY_GF2 := by
  induction n generalizing a out with
  | zero => simp [reduceByteLoopFull]
  | succ n ih =>
    simp only [reduceByteLoopFull]
    split_ifs with htb
    · -- Bit n is set: htb : a.testBit n = true
      -- Since a < 256, bits ≥ 8 are zero, so n ≤ 7
      have hn_le : n ≤ 7 := by
        by_contra hlt
        push_neg at hlt  -- hlt : 7 < n
        have hfail : a.testBit n = false := Nat.testBit_eq_false_of_lt
          (calc a < 256 := ha
            _ = 2 ^ 8 := by norm_num
            _ ≤ 2 ^ n := by
              apply Nat.pow_le_pow_right (by norm_num : 0 < 2)
              omega)
        simp [hfail] at htb
      set ps := 0x1100b <<< n with hps_def
      -- ps >>> 16 < 256 for n ≤ 7
      have hps_hi_lt : ps >>> 16 < 256 := by
        unfold ps
        interval_cases n <;> decide
      -- New a' is < 256
      have ha'_lt : a ^^^ (ps >>> 16) < 256 :=
        xor_lt_256 a (ps >>> 16) ha hps_hi_lt
      have ha'_eq : (a ^^^ (ps >>> 16)) % 256 = a ^^^ (ps >>> 16) :=
        Nat.mod_eq_of_lt ha'_lt
      -- Helpers (defined before the rewrites so they're all available)
      have hmonic : POLY_GF2.Monic := by
        unfold POLY_GF2 Polynomial.Monic Polynomial.leadingCoeff
        have hnd : (X ^ 16 + X ^ 12 + X ^ 3 + X + (1 : (ZMod 2)[X])).natDegree = 16 := by
          compute_degree!
        rw [hnd]; simp [coeff_add, coeff_X_pow, coeff_X, coeff_one]
      have hpoly_ps : natToGF2Poly ps = POLY_GF2 * X ^ n := by
        unfold ps
        simp [natToGF2Poly_shiftLeft, natToGF2Poly_POLY]
      have hps_split : natToGF2Poly (ps % 2 ^ 16) + natToGF2Poly (ps >>> 16) * X ^ 16 =
                       natToGF2Poly ps := by
        ext m
        simp only [natToGF2Poly_coeff, coeff_add, coeff_mul_X_pow',
                   Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
        by_cases hm : 16 ≤ m
        · simp only [hm, ↓reduceIte, show ¬ m < 16 from by omega, zero_add]
          congr 1
          grind
        · push_neg at hm
          simp only [show ¬ 16 ≤ m from by omega, ↓reduceIte, hm, ↓reduceIte, add_zero]
          congr 1
      have hxor_mod : ∀ p q : Nat, (p ^^^ q) % 2 ^ 16 = p % 2 ^ 16 ^^^ q % 2 ^ 16 := by
        intro p q; apply Nat.eq_of_testBit_eq; intro i
        simp only [Nat.testBit_xor, Nat.testBit_mod_two_pow]
        by_cases hi : i < 16 <;> simp [hi]
      -- The XOR step adds POLY_GF2 * X^n to the combined representation
      have hrw : natToGF2Poly ((out ^^^ ps) % 2 ^ 16) +
                 natToGF2Poly (a ^^^ ps >>> 16) * X ^ 16 =
                 (natToGF2Poly (out % 2 ^ 16) + natToGF2Poly a * X ^ 16) +
                 POLY_GF2 * X ^ n := by
        rw [hxor_mod, natToGF2Poly_xor, natToGF2Poly_xor, add_mul,
            ← hpoly_ps, ← hps_split]
        ring
      -- Substitute (a ^^^ (ps >>> 16)) % 256 → a ^^^ (ps >>> 16) using simp,
      -- then apply IH, then use hrw to close.
      simp only [ha'_eq]
      rw [ih _ _ ha'_lt, hrw, Polynomial.add_modByMonic,
          (Polynomial.modByMonic_eq_zero_iff_dvd hmonic).mpr (dvd_mul_right POLY_GF2 _), add_zero]
    · -- Bit n is not set: htb : ¬a.testBit n = true
      exact ih a out ha

/-- The carry register vanishes after 8 steps for all byte values k < 256. -/
private lemma reduceByteLoopFull_carry_zero (k : Nat) (hk : k < 256) :
    (reduceByteLoopFull k 0 8).1 = 0 := by
  have h : ∀ k' : Fin 256, (reduceByteLoopFull k'.val 0 8).1 = 0 := by native_decide
  exact h ⟨k, hk⟩

/-- **(a) Full-range table polynomial correctness (spec-level).**

For any byte value `k < 256`:
  `natToGF2Poly (reduceByteTable k) = (natToGF2Poly k * X ^ 16) %ₘ POLY_GF2` -/
theorem reduceByteTable_eq_poly_full (k : Nat) (hk : k < 256) :
    natToGF2Poly (reduceByteTable k) =
      (natToGF2Poly k * X ^ 16) %ₘ POLY_GF2 := by
  unfold reduceByteTable
  rw [← reduceByteLoopFull_snd_eq]
  have hmonic : POLY_GF2.Monic := by
    unfold POLY_GF2 Polynomial.Monic Polynomial.leadingCoeff
    have hnd : (X ^ 16 + X ^ 12 + X ^ 3 + X + (1 : (ZMod 2)[X])).natDegree = 16 := by
      compute_degree!
    rw [hnd]; simp [coeff_add, coeff_X_pow, coeff_X, coeff_one]
  have hPOLYdeg : POLY_GF2.natDegree = 16 := by unfold POLY_GF2; compute_degree!
  have hne1 : POLY_GF2 ≠ 1 := by
    intro heq
    have : (POLY_GF2 : (ZMod 2)[X]).coeff 16 = (1 : (ZMod 2)[X]).coeff 16 := by rw [heq]
    simp [POLY_GF2, coeff_add, coeff_X_pow, coeff_X, coeff_one] at this
  have hinv := reduceByteLoopFull_inv k 0 8 hk
  simp only [Nat.zero_mod, natToGF2Poly_zero, zero_add] at hinv
  have hcarry := reduceByteLoopFull_carry_zero k hk
  simp only [hcarry, natToGF2Poly_zero, zero_mul, add_zero] at hinv
  -- hinv : natToGF2Poly ((reduceByteLoopFull k 0 8).2 % 2^16) %ₘ POLY = (k * X^16) %ₘ POLY
  -- The LHS has degree < 16, so %ₘ POLY is identity
  set A := natToGF2Poly ((reduceByteLoopFull k 0 8).2 % 2 ^ 16)
  have hA_deg : A.natDegree < 16 := by
    rcases eq_or_ne A 0 with heq | hne
    · simp [heq]
    · rw [Polynomial.natDegree_lt_iff_degree_lt hne, Polynomial.degree_lt_iff_coeff_zero]
      intro m hm
      simp only [A, natToGF2Poly_coeff]
      exact if_neg (Bool.not_eq_true _ ▸ Nat.testBit_eq_false_of_lt
        (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (Nat.pow_le_pow_right (by norm_num) hm)))
  -- A %ₘ POLY_GF2 = A
  have hA_self : A %ₘ POLY_GF2 = A := by
    have hA_eq := Polynomial.modByMonic_add_div A hmonic
    -- hA_eq : A %ₘ POLY_GF2 + A /ₘ POLY_GF2 * POLY_GF2 = A
    suffices hdivz : A /ₘ POLY_GF2 = 0 by
      rw [hdivz, mul_zero, add_zero] at hA_eq
      exact hA_eq
    by_contra hne
    have hprod_deg : (A /ₘ POLY_GF2 * POLY_GF2).natDegree ≥ 16 := by
      have hmul := Polynomial.natDegree_mul hne hmonic.ne_zero
      rw [hPOLYdeg] at hmul
      linarith [Nat.zero_le (A /ₘ POLY_GF2).natDegree]
    have hmod_lt : (A %ₘ POLY_GF2).natDegree < 16 := by
      rw [← hPOLYdeg]; exact Polynomial.natDegree_modByMonic_lt A hmonic hne1
    have hrearr : A = A %ₘ POLY_GF2 + A /ₘ POLY_GF2 * POLY_GF2 := by grind
    have hge : A.natDegree ≥ 16 := by
      rw [hrearr]
      apply le_trans hprod_deg
      apply Polynomial.le_natDegree_of_ne_zero
      intro hzero
      have hlt_deg : (A %ₘ POLY_GF2).natDegree < (A /ₘ POLY_GF2 * POLY_GF2).natDegree :=
        by linarith
      rw [Polynomial.coeff_add,
          Polynomial.coeff_eq_zero_of_natDegree_lt hlt_deg,
          zero_add] at hzero
      have hprod_ne : A /ₘ POLY_GF2 * POLY_GF2 ≠ 0 := by
        intro h; simp [h] at hprod_deg
      exact absurd hzero (by
        have hlc := Polynomial.leadingCoeff_ne_zero.mpr hprod_ne
        simp only [Polynomial.leadingCoeff] at hlc
        exact hlc)
    linarith [hA_deg, hge]
  rw [hA_self] at hinv
  exact hinv

/-- **GF(2)[X] polynomial specification for `reduce_bytes`** -/
@[step]
theorem reduce_byte_poly_spec :
    reduce_bytes ⦃ result =>
      ∀ j : Std.Usize, j.val < 256 →
        ∃ v : Std.U16,
          Array.index_usize result j = ok v ∧
            natToGF2Poly v.val =
              (natToGF2Poly j.val * X ^ 16) %ₘ POLY_GF2 ⦄ := by
  apply WP.spec_mono reduce_bytes_spec
  intro result hres j hj
  obtain ⟨v, hv_idx, hv_val⟩ := hres j hj
  refine ⟨v, hv_idx, ?_⟩
  rw [hv_val]
  exact reduceByteTable_eq_poly_full j.val hj

end spqr.encoding.gf.reduce
