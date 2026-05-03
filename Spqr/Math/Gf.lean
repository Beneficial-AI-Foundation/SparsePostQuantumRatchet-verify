/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.Polynomial.Basic

/-! # GF(2)[X] Polynomial Library

Consolidated definitions, lemmas, and theorems about the function
`natToGF2Poly : Nat → (ZMod 2)[X]` (which interprets a natural number's
binary representation as the coefficient vector of a polynomial over
GF(2)) and about the irreducible polynomial
`POLY_GF2 = X¹⁶ + X¹² + X³ + X + 1` used to model `GF(2¹⁶)` as
`(ZMod 2)[X] / (POLY_GF2)`.

Conventions:
- XOR (`^^^`) on `Nat` corresponds to polynomial addition (`+`) over GF(2).
- Shift-left (`<<< n`) corresponds to multiplication by `X ^ n`.
- `Nat.testBit n` corresponds to checking whether the n-th coefficient
  is non-zero.
-/

open Aeneas Aeneas.Std Result
open Polynomial

abbrev GF216 := GaloisField 2 16

namespace spqr.encoding.gf.unaccelerated


/-! ## Constants -/

/-! ## Core definitions -/

/-- Convert a natural number to a GF(2) polynomial by interpreting
its binary representation as polynomial coefficients.

For example, `natToGF2Poly 0b1011 = X³ + X + 1` since bits 0, 1,
and 3 are set. -/
noncomputable def natToGF2Poly (n : Nat) : (ZMod 2)[X] :=
  ∑ i ∈ Finset.range (n.log2 + 1),
    if n.testBit i then (X : (ZMod 2)[X]) ^ i else 0

/-- The irreducible polynomial used for GF(2¹⁶) reduction:
    POLY = X¹⁶ + X¹² + X³ + X + 1   (0x1100b in hex).

    GF(2¹⁶) ≅ GF(2)[X] / (POLY). -/
noncomputable def POLY_GF2 : (ZMod 2)[X] :=
  X ^ 16 + X ^ 12 + X ^ 3 + X + 1

/-! ## Coefficient characterization and basic lemmas of `natToGF2Poly` -/

/-- The coefficient of `natToGF2Poly n` at position `m` is `1` when bit `m`
of `n` is set, and `0` otherwise. -/
lemma natToGF2Poly_coeff (n : Nat) (m : Nat) :
    (natToGF2Poly n).coeff m = if n.testBit m then (1 : ZMod 2) else 0 := by
  unfold natToGF2Poly
  simp only [finset_sum_coeff]
  simp_rw [apply_ite (fun (p : (ZMod 2)[X]) => p.coeff m), coeff_X_pow, coeff_zero]
  cases htb : n.testBit m with
  | false =>
    exact Finset.sum_eq_zero fun i _ => by
      by_cases him : m = i
      · subst him; simp [htb]
      · simp [him]
  | true =>
    have hne : n ≠ 0 := by rintro rfl; simp at htb
    have hm : m ∈ Finset.range (n.log2 + 1) := by
      rw [Finset.mem_range]
      have := (Nat.le_log2 hne).mpr (Nat.ge_two_pow_of_testBit htb)
      omega
    rw [Finset.sum_eq_single_of_mem m hm (fun j _ hjm => by simp [Ne.symm hjm])]
    simp [htb]

/-- `natToGF2Poly 0 = 0`. -/
lemma natToGF2Poly_zero : natToGF2Poly 0 = 0 := by
  ext m; simp [natToGF2Poly_coeff]

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

/-- The natural-number encoding of the irreducible polynomial
    POLY = 0x1100b corresponds to `POLY_GF2` in GF(2)[X]:

    `natToGF2Poly 0x1100b = X¹⁶ + X¹² + X³ + X + 1 = POLY_GF2`. -/
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

/-- **Truncation to `n` bits is the identity for values `< 2^n`.**

If `v < 2^n`, then `v % 2^n = v`, so
`natToGF2Poly (v % 2^n) = natToGF2Poly v`. -/
theorem natToGF2Poly_mod_eq_of_lt (v n : Nat) (hv : v < 2 ^ n) :
    natToGF2Poly (v % 2 ^ n) = natToGF2Poly v := by
  congr 1; exact Nat.mod_eq_of_lt hv

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

/-! ## Properties of `POLY_GF2` -/

/-- **`POLY_GF2` is monic** (leading coefficient is 1). -/
theorem POLY_GF2_monic : POLY_GF2.Monic := by
  unfold POLY_GF2 Polynomial.Monic Polynomial.leadingCoeff
  have hnd : (X ^ 16 + X ^ 12 + X ^ 3 + X + (1 : (ZMod 2)[X])).natDegree = 16 := by
    compute_degree!
  rw [hnd]
  simp [coeff_add, coeff_X_pow, coeff_X, coeff_one]

/-- **`POLY_GF2` has degree 16.** -/
theorem POLY_GF2_natDegree : POLY_GF2.natDegree = 16 := by
  unfold POLY_GF2; compute_degree!

/-- **`POLY_GF2 = X¹⁶ + X¹² + X³ + X + 1` is irreducible over `GF(2) = ZMod 2`.**

Since `POLY_GF2` is a polynomial of degree 16 over the finite field `GF(2)`,
its irreducibility is a finite, decidable property: a polynomial of degree
`d` over a finite field is irreducible iff it has no factor of degree
`≤ d / 2`, and there are only finitely many such polynomials to test.

The most natural Lean proof would be `by native_decide`, but Mathlib does
not (yet) provide a `Decidable (Irreducible p)` instance for
`p : (ZMod q)[X]`.  Producing a fully computational proof therefore
requires either:

1. building such a decidability instance (e.g. via the explicit factor
   enumeration above), or
2. exhibiting a degree-16 element of `GF(2¹⁶)` whose minimal polynomial
   is `POLY_GF2` (using `minpoly.unique` or `IsPrimitiveRoot`).

Both approaches are non-trivial in Lean 4 / Mathlib.  For the purposes
of the rest of this development we record the theorem statement now and
defer the proof; it is the key fact that makes the quotient
`(ZMod 2)[X] / (POLY_GF2)` a field — namely `GF(2¹⁶)`. -/
theorem POLY_GF2_irreducible : Irreducible POLY_GF2 := by
  sorry




/-! ## Characteristic-2 facts in `(ZMod 2)[X]` -/

/-- **In `(ZMod 2)[X]`, every element is its own negation.**

This is a consequence of characteristic 2: `a + a = 0` implies `-a = a`. -/
lemma zmod2_poly_neg_eq (a : (ZMod 2)[X]) : -a = a := by
  have h : a + a = 0 := by
    ext n; simp only [coeff_add, coeff_zero]
    have h2 : (2 : ZMod 2) = 0 := by decide
    calc (a.coeff n) + (a.coeff n) = 2 * (a.coeff n) := by ring
      _ = 0 * (a.coeff n) := by rw [h2]
      _ = 0 := by ring
  exact neg_eq_of_add_eq_zero_left h

/-- **In `(ZMod 2)[X]`, subtraction equals addition.**

Direct consequence of `zmod2_poly_neg_eq`: `a - b = a + (-b) = a + b`. -/
lemma zmod2_poly_sub_eq_add (a b : (ZMod 2)[X]) : a - b = a + b := by
  rw [sub_eq_add_neg, zmod2_poly_neg_eq]

/-! ## Modular-reduction utilities for `POLY_GF2` -/

/-- **`p %ₘ POLY_GF2 - p` is divisible by `POLY_GF2`.**

A direct consequence of the division identity
`p %ₘ POLY_GF2 + (p /ₘ POLY_GF2) * POLY_GF2 = p`. -/
lemma POLY_GF2_dvd_modByMonic_sub (p : (ZMod 2)[X]) :
    POLY_GF2 ∣ (p %ₘ POLY_GF2 - p) := by
  have hadd := Polynomial.modByMonic_add_div p POLY_GF2_monic
  refine ⟨-(p /ₘ POLY_GF2), ?_⟩
  linear_combination hadd

/-- **Idempotence of `%ₘ POLY_GF2`**: applying the reduction twice is
the same as applying it once. -/
lemma modByMonic_modByMonic_self (p : (ZMod 2)[X]) :
    (p %ₘ POLY_GF2) %ₘ POLY_GF2 = p %ₘ POLY_GF2 :=
  Polynomial.modByMonic_eq_of_dvd_sub POLY_GF2_monic
    (POLY_GF2_dvd_modByMonic_sub p)

/-- **Bridge lemma**: any monic polynomial `P` and ring-homomorphism `φ`
that vanishes at `P` makes the residue `p %ₘ P` φ-equal to `p` itself.

This is the standard "transport along the quotient map" identity:
if `φ : (ZMod 2)[X] →+* R` factors through `(ZMod 2)[X] ⧸ (P)` (i.e.
`φ P = 0`), then `φ p = φ (p %ₘ P)`.  Multiplying through by the
quotient identity `p = P * (p /ₘ P) + (p %ₘ P)`, the `P · q` term is
killed by `φ P = 0`.
-/
lemma ringHom_modByMonic
    {R : Type*} [CommRing R]
    (φ : (ZMod 2)[X] →+* R)
    (P : (ZMod 2)[X]) (hMonic : P.Monic) (hφ : φ P = 0)
    (p : (ZMod 2)[X]) :
    φ (p %ₘ P) = φ p := by
  -- `modByMonic_add_div p hMonic : p %ₘ P + P * (p /ₘ P) = p`
  have heq : p %ₘ P + P * (p /ₘ P) = p :=
    Polynomial.modByMonic_add_div p hMonic
  have h1 : φ p = φ (p %ₘ P + P * (p /ₘ P)) := by rw [heq]
  have h2 :
      φ (p %ₘ P + P * (p /ₘ P)) = φ (p %ₘ P) + φ P * φ (p /ₘ P) := by
    simp [map_add, map_mul]
  rw [h1, h2, hφ]; ring

/-- **Multiplicativity of `%ₘ POLY_GF2` (compatibility with the quotient ring

multiplication).**

For any two natural numbers `p` and `q`, reducing the product of their
`natToGF2Poly` encodings modulo `POLY_GF2` is the same as first reducing
each factor modulo `POLY_GF2`, multiplying the residues, and reducing the
result again.  This is the algebraic statement that the quotient map
`(ZMod 2)[X] → (ZMod 2)[X] ⧸ (POLY_GF2)` is a ring homomorphism.

**Mathematical note.** The "naive" identity without the outer `%ₘ POLY_GF2`,
i.e.
  `(natToGF2Poly p %ₘ POLY_GF2) * (natToGF2Poly q %ₘ POLY_GF2)
     = (natToGF2Poly p * natToGF2Poly q) %ₘ POLY_GF2`,
is **false in general**.  Counter-example: take `p = q = 2 ^ 15` so that
`natToGF2Poly p = natToGF2Poly q = X ^ 15`.  Both factors already have
degree `< 16`, so `%ₘ POLY_GF2` is the identity on each.  The LHS is
`X ^ 30` (degree 30), while the RHS, being a residue, has degree `< 16`.
Hence the two sides cannot be equal.  The correct statement, proved
below, requires an outer `%ₘ POLY_GF2` on the LHS — exactly Mathlib's
`Polynomial.mul_modByMonic`. -/
lemma natToGF2Poly_modByMonic_eq (p q : Nat) :
    ((natToGF2Poly p %ₘ POLY_GF2) * (natToGF2Poly q %ₘ POLY_GF2)) %ₘ POLY_GF2 =
      (natToGF2Poly p * natToGF2Poly q) %ₘ POLY_GF2 :=
  (Polynomial.mul_modByMonic _ _ _).symm

/- **Existence of a ring homomorphism from `(ZMod 2)[X]` to `GF216`
that vanishes on `POLY_GF2`.**

Concretely, since `POLY_GF2` is irreducible of degree `16` over `ZMod 2`,
the quotient `AdjoinRoot POLY_GF2 = (ZMod 2)[X] ⧸ (POLY_GF2)` is a field
with `2 ^ 16` elements, hence (non-canonically) isomorphic — as a
`ZMod 2`-algebra — to `GF216 = GaloisField 2 16` via
`GaloisField.algEquivGaloisFieldOfFintype`.  Composing the canonical
quotient map `AdjoinRoot.mk POLY_GF2` with this isomorphism gives a
ring homomorphism `(ZMod 2)[X] →+* GF216` which sends `POLY_GF2` to
`0` (because `AdjoinRoot.mk_self` says `AdjoinRoot.mk POLY_GF2 POLY_GF2 = 0`).
-/

lemma exists_ringHom_modByMonic :
    ∃ φ : (ZMod 2)[X] →+* GF216,
      φ POLY_GF2 = 0 := by
  -- The quotient map `(ZMod 2)[X] → (ZMod 2)[X] ⧸ (P)` is a ring homomorphism that vanishes at `P`.
  classical
  have hmonic : POLY_GF2.Monic := POLY_GF2_monic
  have hne : POLY_GF2 ≠ 0 := hmonic.ne_zero
  -- POLY_GF2 = X^16 + X^12 + X^3 + X + 1 is irreducible over `ZMod 2`.
  have hirr : Irreducible POLY_GF2 := POLY_GF2_irreducible
  haveI : Fact (Irreducible POLY_GF2) := ⟨hirr⟩
  -- The power basis of `AdjoinRoot POLY_GF2` over `ZMod 2`.
  let pb := AdjoinRoot.powerBasis hne
  -- Hence `AdjoinRoot POLY_GF2` is a finite-dimensional `ZMod 2`-vector space.
  haveI : Module.Finite (ZMod 2) (AdjoinRoot POLY_GF2) := pb.finite
  haveI : Fintype (AdjoinRoot POLY_GF2) := Module.fintypeOfFintype pb.basis
  -- It has dimension `natDegree POLY_GF2 = 16`.
  have hdim : Module.finrank (ZMod 2) (AdjoinRoot POLY_GF2) = 16 := by
    rw [pb.finrank, AdjoinRoot.powerBasis_dim, POLY_GF2_natDegree]
  -- Hence its cardinality is `2 ^ 16`.
  have hcard : Fintype.card (AdjoinRoot POLY_GF2) = 2 ^ 16 := by
    rw [Module.card_fintype pb.basis, ZMod.card, Fintype.card_fin,
        AdjoinRoot.powerBasis_dim, POLY_GF2_natDegree]
  -- Identify `AdjoinRoot POLY_GF2` with `GF216`.
  let e : AdjoinRoot POLY_GF2 ≃ₐ[ZMod 2] GF216 :=
    GaloisField.algEquivGaloisFieldOfFintype 2 16 hcard
  -- The composite ring homomorphism.
  have hmk : (AdjoinRoot.mk POLY_GF2) POLY_GF2 = 0 := AdjoinRoot.mk_self
  refine ⟨(e : AdjoinRoot POLY_GF2 →+* GF216).comp (AdjoinRoot.mk POLY_GF2), ?_⟩
  rw [RingHom.comp_apply, hmk, map_zero]

/-- A chosen ring homomorphism `(ZMod 2)[X] →+* GF216` that vanishes on
`POLY_GF2`.  We pick one provided by `exists_ringHom_modByMonic`. -/
noncomputable def φ : (ZMod 2)[X] →+* GF216 :=
  Classical.choose exists_ringHom_modByMonic

/-- The chosen ring homomorphism `φ` sends `POLY_GF2` to `0`. -/
lemma hφ : φ POLY_GF2 = 0 :=
  Classical.choose_spec exists_ringHom_modByMonic

/-- Interpret a natural number as an element of `GF216 = GF(2¹⁶)`,
using the canonical chain
`Nat → (ZMod 2)[X] → GF216`
where the first arrow is `natToGF2Poly` (binary expansion as a
GF(2)-polynomial) and the second arrow is the chosen ring homomorphism
`φ` (which factors through `(ZMod 2)[X] / (POLY_GF2)`). -/
noncomputable def _root_.Nat.toGF216 (n : Nat) : GF216 :=
  φ (natToGF2Poly n)

end spqr.encoding.gf.unaccelerated
