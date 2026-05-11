/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Data.Nat.BitIndices
import Mathlib.Data.Nat.Bits

/-! # GF(2)[X] Polynomial API

The bridge `natToGF2Poly : ℕ → (ZMod 2)[X]` that interprets a natural
number's binary representation as the coefficient vector of a polynomial
over GF(2), together with its basic algebraic properties.

Conventions:
- XOR (`^^^`) on `Nat` corresponds to polynomial addition (`+`) over GF(2).
- Shift-left (`<<< n`) corresponds to multiplication by `X ^ n`.
- `Nat.testBit n` corresponds to checking whether the n-th coefficient
  is non-zero.
-/

open Polynomial

abbrev GF2Poly := (ZMod 2)[X]

namespace spqr.math.gf

/-! ## Core definitions -/

/-- Convert a natural number to a GF(2) polynomial by interpreting
its binary representation as polynomial coefficients.

For example, `natToGF2Poly 0b1011 = X³ + X + 1` since bits 0, 1,
and 3 are set. -/
noncomputable def natToGF2Poly (n : ℕ) : (ZMod 2)[X] :=
  (n.bitIndices.map (X ^ ·)).sum

/-! ## Helper lemma relating `bitIndices` to `testBit` -/

/-- Membership in `n.bitIndices` is equivalent to `n.testBit m = true`.
prepare and upstream to Mathlib/Data/Nat/BitIndices.lean.
-/
private lemma mem_bitIndices_iff_testBit {n m : ℕ} :
    m ∈ n.bitIndices ↔ n.testBit m := by
  induction n using Nat.binaryRec generalizing m with
  | zero => simp
  | bit b n ih =>
    cases m with
    | zero => rw [Nat.testBit_bit_zero]; cases b <;> simp
    | succ m => rw [Nat.testBit_bit_succ]; cases b <;> simp [ih]

/-! ## Coefficient characterization and basic lemmas of `natToGF2Poly` -/

/-- The coefficient of `natToGF2Poly n` at position `m` is `1` when bit `m`
of `n` is set, and `0` otherwise. -/
lemma natToGF2Poly_coeff (n : Nat) (m : Nat) :
    (natToGF2Poly n).coeff m = if n.testBit m then (1 : ZMod 2) else 0 := by
  unfold natToGF2Poly
  have hdist : (n.bitIndices.map (X ^ ·)).sum.coeff m =
      ((n.bitIndices.map (X ^ ·)).map (fun p => p.coeff m)).sum :=
    map_list_sum (Polynomial.lcoeff (ZMod 2) m) _
  rw [hdist, List.map_map]
  simp only [Function.comp_def, coeff_X_pow]
  by_cases hm : n.testBit m = true
  · simp only [hm, ↓reduceIte]
    rw [List.sum_map_eq_nsmul_single _ _ fun _ ha _ => if_neg ha.symm]
    simp [mem_bitIndices_iff_testBit.mpr hm]
  · push_neg at hm
    simp only [hm, ↓reduceIte, Bool.false_eq_true]
    exact List.sum_eq_zero (fun x hx => by
      simp only [List.mem_map] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      have hmi : m ≠ i := fun h => by
        subst h; exact absurd (mem_bitIndices_iff_testBit.mp hi) (by simp [hm])
      simp [hmi])

/-- `natToGF2Poly 0 = 0`. -/
@[simp]
lemma natToGF2Poly_zero : natToGF2Poly 0 = 0 := by
  ext m
  simp [natToGF2Poly_coeff]

/-- XOR of natural numbers corresponds to addition of GF(2) polynomials. -/
lemma natToGF2Poly_xor (a b : Nat) :
    natToGF2Poly (a ^^^ b) = natToGF2Poly a + natToGF2Poly b := by
  ext m
  simp only [natToGF2Poly_coeff, coeff_add, Nat.testBit_xor]
  cases a.testBit m <;> cases b.testBit m <;> decide

/-- Left-shift on naturals corresponds to multiplication by `X ^ k` over GF(2). -/
lemma natToGF2Poly_shiftLeft (a k : Nat) :
    natToGF2Poly (a <<< k) = natToGF2Poly a * X ^ k := by
  ext m
  simp only [natToGF2Poly_coeff, coeff_mul_X_pow', Nat.testBit_shiftLeft,
    Bool.and_eq_true, decide_eq_true_eq]
  by_cases hkm : k ≤ m <;> simp [hkm]

/-- **Natural-number polynomial decomposition at an arbitrary bit boundary.**

For any natural number `v` and bit position `n`:

  `natToGF2Poly v = natToGF2Poly (v % 2^n) + natToGF2Poly (v >>> n) * X^n`

This decomposes a GF(2) polynomial into its lower `n` coefficients
and its upper coefficients shifted down. -/
theorem natToGF2Poly_split (v n : Nat) :
    natToGF2Poly v =
      natToGF2Poly (v % 2 ^ n) + natToGF2Poly (v >>> n) * X ^ n := by
  ext m
  simp only [natToGF2Poly_coeff, coeff_add, coeff_mul_X_pow',
             Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  by_cases hm : n ≤ m
  · simp only [hm, ↓reduceIte, show ¬ m < n from by omega]
    grind
  · push_neg at hm
    simp only [show ¬ n ≤ m from by omega, ↓reduceIte, hm, ↓reduceIte, add_zero]
    congr 1

/-- **Injectivity of `natToGF2Poly` on naturals.**

If two natural numbers map to the same GF(2) polynomial, they are equal.
This is because the coefficient of `natToGF2Poly n` at position `m` is
`1` iff bit `m` of `n` is set, so equal polynomials force equal bit
patterns. -/
lemma natToGF2Poly_inj (a b : Nat)
    (h : natToGF2Poly a = natToGF2Poly b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro m
  have hcoeff : (natToGF2Poly a).coeff m = (natToGF2Poly b).coeff m :=
    congrArg (fun p => p.coeff m) h
  simp only [natToGF2Poly_coeff] at hcoeff
  by_cases ha : a.testBit m
  · by_cases hb : b.testBit m
    · exact ha.trans hb.symm
    · simp [ha, hb] at hcoeff
  · by_cases hb : b.testBit m
    · simp [ha, hb] at hcoeff
    · exact (Bool.eq_false_iff.mpr ha).trans (Bool.eq_false_iff.mpr hb).symm

lemma natToGF2Poly_one : natToGF2Poly 1 = 1 := by
  ext m; simp only [natToGF2Poly_coeff, coeff_one]
  cases m with
  | zero => decide
  | succ n =>
    have htb : Nat.testBit 1 (n + 1) = false :=
      Nat.testBit_eq_false_of_lt (Nat.one_lt_pow (by omega) (by norm_num))
    simp [htb]

/-! ## Characteristic-2 facts in `GF2Poly` -/

lemma zmod2_poly_neg_eq (a : GF2Poly) : -a = a := by
  have h : a + a = 0 := by
    ext n; simp only [coeff_add, coeff_zero]
    have h2 : (2 : ZMod 2) = 0 := by decide
    calc (a.coeff n) + (a.coeff n) = 2 * (a.coeff n) := by ring
      _ = 0 * (a.coeff n) := by rw [h2]
      _ = 0 := by ring
  exact neg_eq_of_add_eq_zero_left h

lemma zmod2_poly_sub_eq_add (a b : GF2Poly) : a - b = a + b := by
  rw [sub_eq_add_neg, zmod2_poly_neg_eq]

end spqr.math.gf
