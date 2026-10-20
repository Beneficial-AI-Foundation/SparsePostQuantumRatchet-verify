/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.IsAdjoinRoot
public import Spqr.Crypto.Fips203.Params
/-!
# FIPS 203 Polynomial Ring `R_q`

NIST FIPS 203 (ML-KEM) defines all lattice operations over the quotient ring

  `R_q = ℤ_q[X] / (X²⁵⁶ + 1)`

where `q = 3329` and the polynomial degree bound is `n = 256`.  The coefficient ring is
`ℤ_q = ℤ / 3329ℤ`, which is a finite field since `q` is prime.

This file provides:

1. **`Zq`** — the coefficient ring `ZMod 3329`, a field of 3329 elements.
2. **`cycloPoly`** — the polynomial `X²⁵⁶ + 1 ∈ ℤ_q[X]`.
3. **`Rq`** — the quotient ring `ℤ_q[X] / (X²⁵⁶ + 1)`.
4. **`Rq.ofCoeffs`** / **`Rq.toCoeffs`** — round-tripping between coefficient vectors
   and ring elements.
5. Vector / matrix types and operations for the module-LWE structure.
6. Compress / decompress maps (FIPS 203, Algorithms 11–12).

**Source**: NIST FIPS 203, § 2.4 (Algebraic Background)
-/

@[expose] public section

open Polynomial


noncomputable section

namespace Fips203


/-! ## Coefficient ring `ℤ_q` -/

/-- The coefficient ring `ℤ_q = ℤ / 3329ℤ`. -/
abbrev Zq : Type := ZMod q

instance : Fact (Nat.Prime q) := ⟨q_prime⟩

instance : Field Zq := inferInstance

instance : Fintype Zq := ZMod.fintype q

/-- Canonical coercion `ℕ → ℤ_q`. -/
abbrev Zq.ofNat (a : ℕ) : Zq := (a : ZMod q)

/-- Canonical coercion `ℤ → ℤ_q`. -/
abbrev Zq.ofInt (a : ℤ) : Zq := (a : ZMod q)

/-! ## The cyclotomic-like polynomial `X²⁵⁶ + 1` -/

/-- `cycloPoly = X²⁵⁶ + 1 ∈ ℤ_q[X]`, the reduction polynomial for `R_q`. -/
def cycloPoly : Polynomial Zq := X ^ n + 1

/-- `cycloPoly` is monic. -/
theorem cycloPoly_monic : (cycloPoly).Monic := by
  unfold cycloPoly n
  have : (1 : Polynomial Zq) = C 1 := by simp [map_one]
  rw [this]
  exact monic_X_pow_add_C 1 (by omega)

/-- `cycloPoly` has degree `n = 256`. -/
theorem cycloPoly_natDegree : (cycloPoly).natDegree = n := by
  unfold cycloPoly n
  have : (1 : Polynomial Zq) = C 1 := by simp [map_one]
  rw [this, natDegree_X_pow_add_C]

/-- `cycloPoly` is non-zero. -/
theorem cycloPoly_ne_zero : cycloPoly ≠ 0 :=
  cycloPoly_monic.ne_zero


/-! ## Quotient ring `R_q` -/

/-- `R_q = ℤ_q[X] / (X²⁵⁶ + 1)`.  Every element is uniquely represented by a polynomial
of degree < 256 with coefficients in `ℤ_q`. -/
abbrev Rq : Type := AdjoinRoot cycloPoly

instance : CommRing Rq := AdjoinRoot.instCommRing cycloPoly

instance : Inhabited Rq := ⟨0⟩

/-! ## Canonical element `x` -/

/-- The image of `X` in `R_q`.  Satisfies `x²⁵⁶ = −1`. -/
def Rq.x : Rq := AdjoinRoot.root cycloPoly

/-! ## Coefficient representation -/

/-- Lift `Fin 256 → ℤ_q` into `R_q` via `∑ᵢ cᵢ · Xⁱ`. -/
def Rq.ofCoeffs (c : Fin n → Zq) : Rq :=
  AdjoinRoot.mk cycloPoly (∑ i : Fin n, Polynomial.C (c i) * X ^ (i : ℕ))

/-- Project an element of `R_q` to its coefficient representation `Fin 256 → ℤ_q`. -/
def Rq.toCoeffs (r : Rq) : Fin n → Zq := fun i =>
  (AdjoinRoot.isAdjoinRootMonic cycloPoly cycloPoly_monic).coeff r (i : ℕ)

/-! ## Ring operations -/

/-- Addition in `R_q`. -/
def Rq.add (a b : Rq) : Rq := a + b

/-- Subtraction in `R_q`. -/
def Rq.sub (a b : Rq) : Rq := a - b

/-- Multiplication in `R_q` (polynomial multiplication mod `X²⁵⁶ + 1`). -/
def Rq.mul (a b : Rq) : Rq := a * b

/-- The zero element. -/
def Rq.zero : Rq := 0

/-- The identity element. -/
def Rq.one : Rq := 1

/-! ## Vector and matrix types (module rank `k`) -/

/-- A vector of `k` polynomials in `R_q`. -/
abbrev RqVec (p : ParamSet) : Type := Fin p.k → Rq

/-- A `k × k` matrix of polynomials in `R_q`. -/
abbrev RqMatrix (p : ParamSet) : Type := Fin p.k → Fin p.k → Rq

/-- Inner product `⟨u, v⟩ = ∑ᵢ uᵢ · vᵢ`. -/
def RqVec.innerProd {p : ParamSet} (u v : RqVec p) : Rq :=
  ∑ i : Fin p.k, u i * v i

/-- Matrix-vector product `(A · v)ⱼ = ∑ᵢ Aⱼᵢ · vᵢ`. -/
def RqMatrix.mulVec {p : ParamSet} (A : RqMatrix p) (v : RqVec p) : RqVec p :=
  fun j => ∑ i : Fin p.k, A j i * v i

/-- Matrix transpose. -/
def RqMatrix.transpose {p : ParamSet} (A : RqMatrix p) : RqMatrix p :=
  fun i j => A j i

/-- Vector addition. -/
def RqVec.add {p : ParamSet} (u v : RqVec p) : RqVec p :=
  fun i => u i + v i

/-- Vector subtraction. -/
def RqVec.sub {p : ParamSet} (u v : RqVec p) : RqVec p :=
  fun i => u i - v i

/-! ## Compression / decompression (FIPS 203, Algorithms 11–12) -/

/-- `Compress_d(x)` — rounds `(2^d / q) · x` to the nearest integer mod `2^d`. -/
def compress (d : ℕ) (x : Zq) : ℕ :=
  ((2 ^ d * (x : ZMod q).val + (q / 2)) / q) % (2 ^ d)

/-- `Decompress_d(y)` — maps `y ∈ {0,…,2^d−1}` back to `⌈(q / 2^d) · y⌋ ∈ ℤ_q`. -/
def decompress (d : ℕ) (y : ℕ) : Zq :=
  Zq.ofNat (((q * y) + (1 <<< (d - 1))) >>> d)

/-! ## Elementary identities -/

theorem Rq.add_comm (a b : Rq) : Rq.add a b = Rq.add b a :=
  _root_.add_comm a b

theorem Rq.mul_comm (a b : Rq) : Rq.mul a b = Rq.mul b a :=
  _root_.mul_comm a b

theorem Rq.add_zero (a : Rq) : Rq.add a Rq.zero = a :=
  _root_.add_zero a

theorem Rq.mul_one (a : Rq) : Rq.mul a Rq.one = a :=
  _root_.mul_one a

end Fips203
