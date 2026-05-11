/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Math.Gf2Poly.Basic
import Mathlib.Tactic.IntervalCases

/-! # Computable Nat-level representation of GF(2)[X]

Bit-pattern arithmetic on `Nat` (`gf2ModAux`, `gf2Mod`,
`gf2NoDivisorOfDeg`) together with round-trip lemmas tying the Nat
representation to `natToGF2Poly`.

This module provides the computational backbone for verifying
irreducibility of specific GF(2) polynomials: the `decide`-friendly
functions operate on natural numbers, and the bridge lemmas connect
their results back to the abstract polynomial ring `(ZMod 2)[X]`.
-/

open Polynomial

namespace spqr.math.gf

/-! ### Computable GF(2) polynomial arithmetic -/

/-- One step of GF(2) polynomial long-division: if the leading term of `a`
    can be cancelled by a shift of `b`, XOR to cancel it. -/
private def gf2ModAux (b : Nat) : Nat → Nat → Nat
  | a, 0       => a
  | a, fuel + 1 =>
    if b ≤ 1 then (if b = 1 then 0 else a)
    else if a.log2 < b.log2 then a
    else gf2ModAux b (a ^^^ (b <<< (a.log2 - b.log2))) fuel

/-- GF(2) polynomial remainder: `gf2Mod a b` computes `a mod b` where
    `a` and `b` are natural-number encodings of GF(2) polynomials. -/
def gf2Mod (a b : Nat) : Nat := gf2ModAux b a (a + 1)

private def gf2NoDivisorOfDeg (n d : Nat) : Bool :=
  (List.range (2 ^ d)).all fun lower => gf2Mod n (2 ^ d + lower) != 0

/-! ### Bridge lemmas between Nat arithmetic and natToGF2Poly -/

private lemma gf2ModAux_preserves_dvd (b a fuel : Nat) (hb : b ≥ 2) :
    natToGF2Poly b ∣ natToGF2Poly a - natToGF2Poly (gf2ModAux b a fuel) := by
  induction fuel generalizing a with
  | zero => simp [gf2ModAux, sub_self]
  | succ n ih =>
    simp only [gf2ModAux, show ¬(b ≤ 1) from by omega, ↓reduceIte]
    split
    · simp [sub_self]
    · rename_i hlog
      push_neg at hlog
      set shift := a.log2 - b.log2
      set a' := a ^^^ (b <<< shift)
      have hstep : natToGF2Poly a - natToGF2Poly a' =
          natToGF2Poly b * X ^ shift := by
        have h1 : natToGF2Poly a' = natToGF2Poly a + natToGF2Poly b * X ^ shift := by
          change natToGF2Poly (a ^^^ (b <<< shift)) = _
          rw [natToGF2Poly_xor, natToGF2Poly_shiftLeft]
        have haa : ∀ (p : GF2Poly), p + p = 0 := fun p =>
          (zmod2_poly_sub_eq_add p p).symm.trans (sub_self p)
        calc natToGF2Poly a - natToGF2Poly a'
            = natToGF2Poly a + natToGF2Poly a' := zmod2_poly_sub_eq_add ..
          _ = natToGF2Poly a + (natToGF2Poly a + natToGF2Poly b * X ^ shift) := by rw [h1]
          _ = (natToGF2Poly a + natToGF2Poly a) + natToGF2Poly b * X ^ shift := by ring
          _ = 0 + natToGF2Poly b * X ^ shift := by rw [haa]
          _ = natToGF2Poly b * X ^ shift := by ring
      have ih' := ih a'
      have htelescope : natToGF2Poly a - natToGF2Poly (gf2ModAux b a' n) =
          (natToGF2Poly a - natToGF2Poly a') +
          (natToGF2Poly a' - natToGF2Poly (gf2ModAux b a' n)) := by ring
      rw [htelescope, hstep]
      exact dvd_add (dvd_mul_right _ _) ih'

private lemma gf2ModAux_log2_lt (b a fuel : Nat) (hb : b ≥ 2)
    (hfuel : a.log2 + 1 ≤ b.log2 + fuel) :
    gf2ModAux b a fuel = 0 ∨ (gf2ModAux b a fuel).log2 < b.log2 := by
  induction fuel generalizing a with
  | zero =>
    simp [gf2ModAux]
    omega
  | succ n ih =>
    simp only [gf2ModAux, show ¬(b ≤ 1) from by omega, ↓reduceIte]
    split
    · rename_i hlt
      rcases Nat.eq_zero_or_pos a with rfl | ha
      · left
        rfl
      · right
        exact hlt
    · rename_i hlog
      push_neg at hlog
      set shift := a.log2 - b.log2
      set a' := a ^^^ (b <<< shift)
      have ha_pos : a ≥ 2 := by
        have hb_log2 : 1 ≤ b.log2 := (Nat.le_log2 (by omega)).mpr (by omega)
        have h1 : 1 ≤ a.log2 := le_trans hb_log2 hlog
        have ha_ne : a ≠ 0 := by
          intro heq
          subst heq
          simp [Nat.log2_zero] at h1
        exact (Nat.le_log2 ha_ne).mp h1
      have hlog2_lt : a'.log2 < a.log2 := by
        by_cases ha'_zero : a' = 0
        · simp [ha'_zero, Nat.log2_zero]
          have : 1 ≤ a.log2 := (Nat.le_log2 (by omega)).mpr (by omega)
          omega
        · rw [Nat.log2_lt ha'_zero]
          apply Nat.lt_of_testBit a.log2
          · change (a ^^^ (b <<< shift)).testBit a.log2 = false
            rw [Nat.testBit_xor, Nat.testBit_shiftLeft]
            have h1 : a.testBit a.log2 = true := Nat.testBit_log2 (by omega)
            have h2 : decide (shift ≤ a.log2) = true := decide_eq_true_eq.mpr (by omega)
            have h3 : a.log2 - shift = b.log2 := by omega
            have h4 : b.testBit b.log2 = true := Nat.testBit_log2 (by omega)
            simp [h1, h2, h3, h4]
          · rw [← Nat.one_shiftLeft, Nat.testBit_shiftLeft]
            simp
          · intro j hj
            change (a ^^^ (b <<< shift)).testBit j = (2 ^ a.log2).testBit j
            rw [Nat.testBit_xor, Nat.testBit_shiftLeft,
                ← Nat.one_shiftLeft, Nat.testBit_shiftLeft]
            have haj : a.testBit j = false :=
              Nat.testBit_eq_false_of_lt ((Nat.log2_lt (show a ≠ 0 by omega)).mp (by omega))
            have hbsj : b.testBit (j - shift) = false :=
              Nat.testBit_eq_false_of_lt ((Nat.log2_lt (show b ≠ 0 by omega)).mp (by omega))
            have h1j : (1 : Nat).testBit (j - a.log2) = false :=
              Nat.testBit_eq_false_of_lt (Nat.one_lt_pow (by omega) (by norm_num))
            simp [haj, show shift ≤ j from by omega, hbsj,
                  show a.log2 ≤ j from by omega, h1j]
      apply ih
      omega

/-! ### Degree and monicity of `natToGF2Poly` -/

lemma natToGF2Poly_natDegree_eq_log2 (b : Nat) (hb : b ≥ 2) :
    (natToGF2Poly b).natDegree = b.log2 := by
  have hb_ne : b ≠ 0 := by omega
  apply le_antisymm
  · apply Polynomial.natDegree_le_of_degree_le
    rw [Polynomial.degree_le_iff_coeff_zero]
    intro m hm
    rw [natToGF2Poly_coeff]
    have hm' : b.log2 < m := by exact_mod_cast hm
    simp [Nat.testBit_eq_false_of_lt ((Nat.log2_lt hb_ne).mp hm')]
  · apply Polynomial.le_natDegree_of_ne_zero
    rw [natToGF2Poly_coeff]
    simp [Nat.testBit_log2 hb_ne]

private lemma natToGF2Poly_monic_of_ge_two (b : Nat) (hb : b ≥ 2) :
    (natToGF2Poly b).Monic := by
  unfold Polynomial.Monic Polynomial.leadingCoeff
  rw [natToGF2Poly_natDegree_eq_log2 b hb, natToGF2Poly_coeff]
  simp [Nat.testBit_log2 (show b ≠ 0 by omega)]

/-! ### Non-divisibility from `gf2Mod` -/

lemma gf2Mod_ne_zero_of_not_dvd (a b : Nat) (hb : b ≥ 2)
    (hmod : gf2Mod a b ≠ 0) : ¬ (natToGF2Poly b ∣ natToGF2Poly a) := by
  intro ⟨q, hq⟩
  set r := gf2Mod a b with hr_def
  have hdvd_diff := gf2ModAux_preserves_dvd b a (a + 1) hb
  have hdvd_r : natToGF2Poly b ∣ natToGF2Poly r := by
    have : natToGF2Poly b ∣ natToGF2Poly a := ⟨q, hq⟩
    have : natToGF2Poly b ∣ natToGF2Poly a - natToGF2Poly r := hdvd_diff
    exact (dvd_add_right this).mp ⟨q, by rw [hq]; ring⟩
  obtain ⟨s, hs⟩ := hdvd_r
  have hr_ne : natToGF2Poly r ≠ 0 := by
    intro h
    have := natToGF2Poly_inj r 0 (by rw [h, natToGF2Poly_zero])
    exact hmod this
  have hs_ne : s ≠ 0 := by
    rintro rfl
    simp only [mul_zero] at hs
    exact hr_ne hs
  have hmonic_b : (natToGF2Poly b).Monic := natToGF2Poly_monic_of_ge_two b hb
  have hdeg : (natToGF2Poly b * s).natDegree = (natToGF2Poly b).natDegree + s.natDegree :=
    hmonic_b.natDegree_mul' hs_ne
  have hdeg_b : (natToGF2Poly b).natDegree = b.log2 :=
    natToGF2Poly_natDegree_eq_log2 b hb
  have hlower : b.log2 ≤ (natToGF2Poly r).natDegree := by
    rw [hs, hdeg, hdeg_b]
    omega
  have hupper : (natToGF2Poly r).natDegree ≤ r.log2 := by
    apply Polynomial.natDegree_le_of_degree_le
    rw [Polynomial.degree_le_iff_coeff_zero]
    intro m hm
    rw [natToGF2Poly_coeff]
    have hm' : r.log2 < m := by exact_mod_cast hm
    simp [Nat.testBit_eq_false_of_lt ((Nat.log2_lt hmod).mp hm')]
  have hlog2_lt : r.log2 < b.log2 := by
    have hfuel : a.log2 + 1 ≤ b.log2 + (a + 1) := by
      have hb_log2 : 1 ≤ b.log2 := (Nat.le_log2 (by omega)).mpr (by omega)
      suffices a.log2 ≤ a by omega
      rcases Nat.eq_zero_or_pos a with rfl | ha_pos
      · simp
      · suffices a < 2 ^ (a + 1) by
          have := (Nat.log2_lt (by omega)).mpr this
          omega
        suffices ∀ n : Nat, n < 2 ^ (n + 1) from this a
        intro n
        induction n with
        | zero => norm_num
        | succ k ih =>
          calc k + 1 ≤ 2 ^ (k + 1) := ih
            _ < 2 ^ (k + 1) + 2 ^ (k + 1) :=
              lt_add_of_pos_right _ (pos_of_gt ih)
            _ = 2 ^ (k + 2) := by ring
    have hbound := gf2ModAux_log2_lt b a (a + 1) hb hfuel
    change r = 0 ∨ r.log2 < b.log2 at hbound
    rcases hbound with h | h
    · exact absurd h hmod
    · exact h
  omega

/-! ### Surjectivity and monic representation -/

private lemma natToGF2Poly_pow2 (k : Nat) : natToGF2Poly (2 ^ k) = X ^ k := by
  rw [show (2 : Nat) ^ k = 1 <<< k from (Nat.one_shiftLeft k).symm,
      natToGF2Poly_shiftLeft, natToGF2Poly_one, one_mul]

lemma natToGF2Poly_surj (q : GF2Poly) : ∃ n, natToGF2Poly n = q := by
  induction q using Polynomial.induction_on' with
  | add p r ih_p ih_r =>
    obtain ⟨np, rfl⟩ := ih_p
    obtain ⟨nr, rfl⟩ := ih_r
    exact ⟨np ^^^ nr, natToGF2Poly_xor np nr⟩
  | monomial n a =>
    fin_cases a
    · exact ⟨0, by simp [natToGF2Poly_zero]⟩
    · refine ⟨2 ^ n, ?_⟩
      rw [natToGF2Poly_pow2]
      simp [X_pow_eq_monomial]

lemma monic_eq_natToGF2Poly (q : GF2Poly)
    (hd : 1 ≤ q.natDegree) : ∃ b, b ≥ 2 ∧ natToGF2Poly b = q := by
  obtain ⟨n, hn⟩ := natToGF2Poly_surj q
  refine ⟨n, ?_, hn⟩
  by_contra h
  push_neg at h
  interval_cases n
  · simp only [natToGF2Poly_zero] at hn
    rw [← hn] at hd
    simp at hd
  · rw [← hn] at hd; simp [natToGF2Poly_one] at hd

/-! ### No small divisors of `0x1100b` -/

private lemma gf2NoDivisorOfDeg_POLY (d : Nat) (hd : 1 ≤ d) (hd8 : d ≤ 8) :
    gf2NoDivisorOfDeg 0x1100b d = true := by
  interval_cases d <;> decide

lemma gf2_no_divisor_all (d : Nat) (hd : 1 ≤ d) (hd8 : d ≤ 8)
    (lower : Nat) (hlower : lower < 2 ^ d) :
    gf2Mod 0x1100b (2 ^ d + lower) ≠ 0 := by
  have hstep := gf2NoDivisorOfDeg_POLY d hd hd8
  simp only [gf2NoDivisorOfDeg, List.all_eq_true, List.mem_range, bne_iff_ne, ne_eq] at hstep
  exact hstep lower hlower

end spqr.math.gf
