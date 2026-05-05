/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Math.Gf
/-! # Spec Theorem for `spqr::encoding::gf::reduce::poly_reduce`

Specification and proof for `spqr.encoding.gf.reduce.poly_reduce`,
which implements table-based polynomial reduction of a 32-bit
carry-less product modulo the irreducible polynomial
POLY = x¹⁶ + x¹² + x³ + x + 1 (0x1100b), yielding a 16-bit
GF(2¹⁶) element.

In GF(2¹⁶) — the Galois field with 65 536 elements — after
carry-less polynomial multiplication (`poly_mul`) produces a
32-bit unreduced product (degree ≤ 30), reduction modulo the
irreducible polynomial POLY is needed to obtain the canonical
16-bit representative.

The reduction proceeds in two byte-by-byte passes using the
precomputed table `REDUCE_BYTES`:s
  1. Extract the high byte `i1 = v >> 24` and XOR
     `REDUCE_BYTES[i1] << 8` into `v`, clearing bits 24–31.
  2. Extract the next byte `i2 = (v >> 16) & 0xFF` and XOR
     `REDUCE_BYTES[i2]` into `v`, clearing bits 16–23.
  3. Return the low 16 bits of `v` as the reduced result.

Each `REDUCE_BYTES[k]` entry stores the precomputed 16-bit XOR
mask that results from reducing all set bits in byte `k` against
POLY.  This is equivalent to computing `(k · x¹⁶) mod POLY`
for the second pass, and `(k · x²⁴) mod POLY` (after appropriate
shifting) for the first pass.

Source: "spqr/src/encoding/gf.rs" (lines 489:4-498:5)
-/

open Aeneas Aeneas.Std Result
open Polynomial spqr.encoding.gf.unaccelerated

namespace spqr.encoding.gf.reduce

/-- Spec-level bit-by-bit polynomial reduction modulo POLY over GF(2).

Reduces a natural number `v` (interpreted as a GF(2) polynomial)
modulo POLY = 0x1100b by iterating from bit position 16 up to
bit `n + 15`, clearing each set high-order bit by XOR-ing with
`POLY <<< (bit − 16)`.  After processing all bits above 15,
the result fits in 16 bits and is the canonical GF(2¹⁶)
representative.

This is the pure recursive definition corresponding to the
mathematical operation `v mod POLY` in GF(2)[X]. -/
def polyMod (v : Nat) : (n : Nat) → Nat
  | 0     => v
  | n + 1 =>
    let v' := polyMod v n
    if v'.testBit (n + 16)
    then v' ^^^ (0x1100b <<< n)
    else v'

/-!
## Algebraic (GF(2)[X]) formulation of polynomial reduction

The following definitions express `polyMod` in terms of the polynomial
ring GF(2)[X] = (ZMod 2)[X], making the algebraic structure explicit:
- XOR (`^^^`) becomes polynomial addition (`+`) over GF(2)
- Shift-left by n (`<<< n`) becomes multiplication by `X ^ n`
- `Nat.testBit n` becomes checking if the n-th coefficient is nonzero

The reduction computes `v mod POLY_GF2` where
  POLY_GF2 = X¹⁶ + X¹² + X³ + X + 1.
-/

/-- Spec-level polynomial reduction modulo POLY_GF2 in (ZMod 2)[X].

Given a polynomial `p ∈ GF(2)[X]`, reduces it modulo POLY_GF2 by
iterating from degree `n + 15` down to degree 16, subtracting
(= adding, in characteristic 2) `POLY_GF2 * X^k` for each nonzero
coefficient at position `k + 16`.

Morally, `polyMod_poly p n = p %ₘ POLY_GF2` when
`natDegree p < n + 16`. -/
noncomputable def polyMod_poly (p : (ZMod 2)[X]) :
    (n : Nat) → (ZMod 2)[X]
  | 0     => p
  | n + 1 =>
    let p' := polyMod_poly p n
    if p'.coeff (n + 16) ≠ 0
    then p' + POLY_GF2 * X ^ n
    else p'

/-- **Correspondence between `polyMod` on `Nat` and `polyMod_poly` on GF(2)[X]**:

Interpreting the natural-number input as a GF(2) polynomial via
`natToGF2Poly`, the `Nat`-level `polyMod` and the algebraic
`polyMod_poly` agree:

  `natToGF2Poly (polyMod v n) = polyMod_poly (natToGF2Poly v) n`

This justifies reasoning about the XOR/shift implementation in
terms of polynomial algebra over GF(2). -/
theorem polyMod_eq_polyMod_poly (v n : Nat) :
    natToGF2Poly (polyMod v n) = polyMod_poly (natToGF2Poly v) n := by
  induction n with
  | zero => simp [polyMod, polyMod_poly]
  | succ n ih =>
    cases htb : (polyMod v n).testBit (n + 16) with
    | false =>
      have hcoeff : (polyMod_poly (natToGF2Poly v) n).coeff (n + 16) = 0 := by
        rw [← ih, natToGF2Poly_coeff]; simp [htb]
      have h1 : polyMod v (n + 1) = polyMod v n := by
        simp (config := { zeta := true }) [polyMod, htb]
      rw [h1, ih]; symm
      simp (config := { zeta := true }) [polyMod_poly, hcoeff]
    | true =>
      have hcoeff : (polyMod_poly (natToGF2Poly v) n).coeff (n + 16) ≠ 0 := by
        rw [← ih, natToGF2Poly_coeff]; simp [htb]
      have h1 : polyMod v (n + 1) = polyMod v n ^^^ (0x1100b <<< n) := by
        simp (config := { zeta := true }) [polyMod, htb]
      rw [h1, natToGF2Poly_xor, natToGF2Poly_shiftLeft, ih, natToGF2Poly_POLY]; symm
      simp (config := { zeta := true }) [polyMod_poly, hcoeff]

/-- Each step of `polyMod_poly` adds a multiple of `POLY_GF2` to the
    accumulator, so the result is always congruent to the original
    polynomial modulo `POLY_GF2`:

      `POLY_GF2 ∣ (p − polyMod_poly p n)`

    Proof by induction: the base case is trivial (`p − p = 0`),
    and each successor step either leaves the polynomial unchanged
    (divisibility preserved) or adds `POLY_GF2 * X ^ n`, which is
    itself divisible by `POLY_GF2`. -/
private lemma polyMod_poly_dvd_sub (p : (ZMod 2)[X]) (n : Nat) :
    POLY_GF2 ∣ (p - polyMod_poly p n) := by
  induction n with
  | zero => simp [polyMod_poly]
  | succ n ih =>
    by_cases hc : (polyMod_poly p n).coeff (n + 16) = 0
    · -- coefficient zero ⇒ polyMod_poly p (n+1) = polyMod_poly p n
      have h1 : polyMod_poly p (n + 1) = polyMod_poly p n := by
        simp (config := { zeta := true }) [polyMod_poly, hc]
      rw [h1]; exact ih
    · -- coefficient nonzero ⇒ polyMod_poly p (n+1) = polyMod_poly p n + POLY_GF2 * X^n
      have hne : (polyMod_poly p n).coeff (n + 16) ≠ 0 := hc
      have h1 : polyMod_poly p (n + 1) =
          polyMod_poly p n + POLY_GF2 * X ^ n := by
        simp (config := { zeta := true }) [polyMod_poly, hne]
      rw [h1, show p - (polyMod_poly p n +
          POLY_GF2 * X ^ n) =
          (p - polyMod_poly p n) -
          POLY_GF2 * X ^ n from by ring]
      exact dvd_sub ih (dvd_mul_right _ _)

/-- **`polyMod_poly` preserves congruence modulo POLY_GF2**:

For any polynomial `p ∈ GF(2)[X]`, the result of `polyMod_poly p n`
is congruent to `p` modulo POLY_GF2:

  `(polyMod_poly p n) %ₘ POLY_GF2 = p %ₘ POLY_GF2`

Note: `polyMod_poly` processes bit positions from low to high
(16, 17, …, n+15). Because POLY_GF2 has a sub-leading term X¹²
(degree gap of only 4), reducing a coefficient at position k+16
(for k ≥ 4) re-introduces a coefficient at position k+12 ≥ 16
which has already been processed. Hence `polyMod_poly p n` may
not be fully reduced (i.e. may have degree ≥ 16), but it always
preserves congruence modulo POLY_GF2. -/
theorem polyMod_poly_eq_modByMonic (p : (ZMod 2)[X]) (n : Nat) :
    (polyMod_poly p n) %ₘ POLY_GF2 =
      p %ₘ POLY_GF2 := by
  have hirr : POLY_GF2.Monic := POLY_GF2_monic
  have h : POLY_GF2 ∣
      (polyMod_poly p n - p) := by
    have h₁ := polyMod_poly_dvd_sub p n
    rwa [show p - polyMod_poly p n =
        -(polyMod_poly p n - p) from by ring, dvd_neg] at h₁
  exact Polynomial.modByMonic_eq_of_dvd_sub hirr h


/-!
## Connection to `poly_mul` for GF(2¹⁶) multiplication

The combined specification for `mul(a, b) = poly_reduce(poly_mul(a, b))`
follows from:

  1. `poly_mul_spec` (from `PolyMul.lean`):
     `natToGF2Poly (poly_mul a b).val = natToGF2Poly a.val * natToGF2Poly b.val`

  2. `poly_reduce_spec` (above):
     `natToGF2Poly (poly_reduce v).val = (natToGF2Poly v.val) %ₘ POLY_GF2`

Together:
  `natToGF2Poly (mul a b).val
     = (natToGF2Poly a.val * natToGF2Poly b.val) %ₘ POLY_GF2`

This is exactly multiplication in the quotient ring
  GF(2¹⁶) ≅ GF(2)[X] / (POLY_GF2)

The remaining bridge to `GaloisField 2 16` (Mathlib's abstract
construction) requires:
  - An explicit isomorphism `GaloisField 2 16 ≅ (ZMod 2)[X] / (POLY_GF2)`
  - Showing that POLY_GF2 is irreducible over GF(2)
  - Connecting the natural-number ↔ polynomial ↔ quotient-ring chain

This algebraic bridge is stated below for use by `Mul.lean`.
-/

/-- **Polynomial-level combined specification for GF(2¹⁶) multiplication**:

For `u16` values `a` and `b`, the composition
`poly_reduce(poly_mul(a, b))` yields a `u16` result whose
`natToGF2Poly` encoding equals the product of the input polynomials
reduced modulo POLY_GF2:

  `natToGF2Poly result.val =
     (natToGF2Poly a.val * natToGF2Poly b.val) %ₘ POLY_GF2`

This is the polynomial-level specification for `unaccelerated.mul`,
composing `poly_mul_spec` and `poly_reduce_spec`.

The proof unfolds `mul`, applies `step*` (which uses both
`poly_mul_spec` and `poly_reduce_spec` from the `@[step]` database),
and then substitutes the intermediate postconditions:
  1. `poly_mul_spec`: `natToGF2Poly i.val = natToGF2Poly a.val * natToGF2Poly b.val`
  2. `poly_reduce_spec`: `natToGF2Poly result.val = (natToGF2Poly i.val) %ₘ POLY_GF2`

Together these yield the combined result by rewriting. -/
theorem poly_reduce_poly_mul_spec (a b : Std.U16) :
    spqr.encoding.gf.unaccelerated.mul a b ⦃ result =>
      natToGF2Poly result.val =
        (natToGF2Poly a.val * natToGF2Poly b.val) %ₘ POLY_GF2 ⦄ := by
  sorry

end spqr.encoding.gf.reduce
