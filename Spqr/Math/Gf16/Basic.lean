/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Math.Gf2Poly.Basic
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.IntervalCases
import Mathlib.Algebra.Polynomial.Div

/-! # The SPQR irreducible polynomial POLY_GF2

Definition of `POLY_GF2 = X¹⁶ + X¹² + X³ + X + 1` in `(ZMod 2)[X]`,
its basic properties (monic, degree 16, ≠ 1), and the bridge lemma
`natToGF2Poly 0x1100b = POLY_GF2`.
-/

open Polynomial

namespace spqr.math.gf

/-- The irreducible polynomial used for GF(2¹⁶) reduction:
    POLY = X¹⁶ + X¹² + X³ + X + 1   (0x1100b in hex).

    GF(2¹⁶) ≅ GF(2)[X] / (POLY). -/
noncomputable def POLY_GF2 : GF2Poly :=
  X ^ 16 + X ^ 12 + X ^ 3 + X + 1

@[simp]
lemma natToGF2Poly_POLY :
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

/-! ## Properties of `POLY_GF2` -/

/-- **`POLY_GF2` is monic** (leading coefficient is 1). -/
theorem POLY_GF2_monic : POLY_GF2.Monic := by
  unfold POLY_GF2; monicity!

/-- **`POLY_GF2` has degree 16.** -/
theorem POLY_GF2_natDegree : POLY_GF2.natDegree = 16 := by
  unfold POLY_GF2; compute_degree!

/-- **`POLY_GF2 ≠ 1`** (its degree is 16, not 0). -/
theorem POLY_GF2_ne_one : POLY_GF2 ≠ 1 := by
  intro h; have := congr_arg Polynomial.natDegree h
  simp [POLY_GF2_natDegree] at this

/-! ## Modular-reduction utilities for `POLY_GF2` -/

lemma POLY_GF2_dvd_modByMonic_sub (p : GF2Poly) :
    POLY_GF2 ∣ (p %ₘ POLY_GF2 - p) := by
  have hadd := Polynomial.modByMonic_add_div p POLY_GF2_monic
  refine ⟨-(p /ₘ POLY_GF2), ?_⟩
  linear_combination hadd

lemma modByMonic_modByMonic_self (p : GF2Poly) :
    (p %ₘ POLY_GF2) %ₘ POLY_GF2 = p %ₘ POLY_GF2 :=
  Polynomial.modByMonic_eq_of_dvd_sub POLY_GF2_monic
    (POLY_GF2_dvd_modByMonic_sub p)

end spqr.math.gf
