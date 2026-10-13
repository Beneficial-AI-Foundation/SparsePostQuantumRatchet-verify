/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Crypto.Fips203.NTT.BaseCaseMultiply
/-!
# FIPS 203 Algorithm 9 — MultiplyNTTs (Componentwise NTT Multiplication)

NIST FIPS 203 (ML-KEM, August 2024), § 4.3, defines `MultiplyNTTs` as the componentwise
multiplication of two NTT-domain polynomials.  Given `f̂, ĝ : Fin 256 → ℤ_q` in NTT
representation, the product `ĥ = MultiplyNTTs(f̂, ĝ)` is computed by applying
`BaseCaseMultiply` (Algorithm 10) independently to each of the 128 coefficient pairs
`(f̂[2i], f̂[2i+1])` and `(ĝ[2i], ĝ[2i+1])` with the twiddle factor
`γᵢ = ζ^{2·BitRev₇(i)+1}`.

The NTT decomposes the ring `R_q = ℤ_q[X]/(X²⁵⁶ + 1)` as a product of 128 quadratic
quotient rings:

  `R_q ≅ ∏ᵢ₌₀¹²⁷ ℤ_q[X] / (X² − γᵢ)`

Under this isomorphism, multiplication in `R_q` corresponds to the 128 independent
`BaseCaseMultiply` operations that `MultiplyNTTs` performs.

**Pseudocode** (FIPS 203, Algorithm 9):

```
MultiplyNTTs(f̂, ĝ):
  for i from 0 to 127:
    (ĥ[2i], ĥ[2i+1]) ← BaseCaseMultiply(f̂[2i], f̂[2i+1], ĝ[2i], ĝ[2i+1], γᵢ)
  return ĥ
```

**Source**: NIST FIPS 203, § 4.3 (Algorithm 9)
-/

noncomputable section

namespace Fips203

/-! ## Structural properties of MultiplyNTTs -/

/-- **Right annihilation**: `MultiplyNTTs(f̂, 0) = 0`. -/
theorem multiplyNTTs_zero_right (fh : Fin n → Zq) :
    multiplyNTTs fh (fun _ => 0) = fun _ => 0 := by
  rw [multiplyNTTs_comm]
  exact multiplyNTTs_zero_left fh

/-- **Left distributivity**:
`MultiplyNTTs(f̂, ĝ + ĥ) = MultiplyNTTs(f̂, ĝ) + MultiplyNTTs(f̂, ĥ)`. -/
theorem multiplyNTTs_add_right (fh gh hh : Fin n → Zq) :
    multiplyNTTs fh (fun i => gh i + hh i) =
      fun i => multiplyNTTs fh gh i + multiplyNTTs fh hh i := by
  ext idx
  simp only [multiplyNTTs, baseCaseMultiply]
  split <;> ring

/-- **Right distributivity**:
`MultiplyNTTs(f̂ + ĝ, ĥ) = MultiplyNTTs(f̂, ĥ) + MultiplyNTTs(ĝ, ĥ)`. -/
theorem multiplyNTTs_add_left (fh gh hh : Fin n → Zq) :
    multiplyNTTs (fun i => fh i + gh i) hh =
      fun i => multiplyNTTs fh hh i + multiplyNTTs gh hh i := by
  ext idx
  simp only [multiplyNTTs, baseCaseMultiply]
  split <;> ring

/-- **Subtraction on the right**:
`MultiplyNTTs(f̂, ĝ − ĥ) = MultiplyNTTs(f̂, ĝ) − MultiplyNTTs(f̂, ĥ)`. -/
theorem multiplyNTTs_sub_right (fh gh hh : Fin n → Zq) :
    multiplyNTTs fh (fun i => gh i - hh i) =
      fun i => multiplyNTTs fh gh i - multiplyNTTs fh hh i := by
  ext idx
  simp only [multiplyNTTs, baseCaseMultiply]
  split <;> ring

/-- **Subtraction on the left**:
`MultiplyNTTs(f̂ − ĝ, ĥ) = MultiplyNTTs(f̂, ĥ) − MultiplyNTTs(ĝ, ĥ)`. -/
theorem multiplyNTTs_sub_left (fh gh hh : Fin n → Zq) :
    multiplyNTTs (fun i => fh i - gh i) hh =
      fun i => multiplyNTTs fh hh i - multiplyNTTs gh hh i := by
  ext idx
  simp only [multiplyNTTs, baseCaseMultiply]
  split <;> ring

/-- **Negation on the right**: `MultiplyNTTs(f̂, −ĝ) = −MultiplyNTTs(f̂, ĝ)`. -/
theorem multiplyNTTs_neg_right (fh gh : Fin n → Zq) :
    multiplyNTTs fh (fun i => -gh i) =
      fun i => -multiplyNTTs fh gh i := by
  ext idx
  simp only [multiplyNTTs, baseCaseMultiply]
  split <;> ring

/-- **Negation on the left**: `MultiplyNTTs(−f̂, ĝ) = −MultiplyNTTs(f̂, ĝ)`. -/
theorem multiplyNTTs_neg_left (fh gh : Fin n → Zq) :
    multiplyNTTs (fun i => -fh i) gh =
      fun i => -multiplyNTTs fh gh i := by
  ext idx
  simp only [multiplyNTTs, baseCaseMultiply]
  split <;> ring


/-! ## Coefficient-level access

The following theorems expose the even/odd coefficient structure of
`MultiplyNTTs`, making explicit the connection to `BaseCaseMultiply` at
each pair index `i ∈ {0, …, 127}`. -/

/-- **Even coefficient**: `MultiplyNTTs(f̂, ĝ)[2i] = BaseCaseMultiply(…).1`. -/
theorem multiplyNTTs_even (fh gh : Fin n → Zq) (i : Fin 128)
    (h2i : 2 * i.val < n := by omega)
    (h2i1 : 2 * i.val + 1 < n := by omega) :
    multiplyNTTs fh gh ⟨2 * i.val, h2i⟩ =
      (baseCaseMultiply
        (fh ⟨2 * i.val, h2i⟩) (fh ⟨2 * i.val + 1, h2i1⟩)
        (gh ⟨2 * i.val, h2i⟩) (gh ⟨2 * i.val + 1, h2i1⟩)
        (gammaForPair i)).1 := by
  simp only [multiplyNTTs]
  have h_mod : 2 * i.val % 2 = 0 := by omega
  have h_div : 2 * i.val / 2 = i.val := by omega
  simp only [h_mod, h_div, ite_true]

/-- **Odd coefficient**: `MultiplyNTTs(f̂, ĝ)[2i+1] = BaseCaseMultiply(…).2`. -/
theorem multiplyNTTs_odd (fh gh : Fin n → Zq) (i : Fin 128)
    (h2i : 2 * i.val < n := by omega)
    (h2i1 : 2 * i.val + 1 < n := by omega) :
    multiplyNTTs fh gh ⟨2 * i.val + 1, h2i1⟩ =
      (baseCaseMultiply
        (fh ⟨2 * i.val, h2i⟩) (fh ⟨2 * i.val + 1, h2i1⟩)
        (gh ⟨2 * i.val, h2i⟩) (gh ⟨2 * i.val + 1, h2i1⟩)
        (gammaForPair i)).2 := by
  simp only [multiplyNTTs]
  have h_mod : (2 * i.val + 1) % 2 = 1 := by omega
  have h_div : (2 * i.val + 1) / 2 = i.val := by omega
  simp only [h_mod, h_div]
  simp only [show (1 = 0) = False from by decide, ite_false]

/-! ## Identity element

The NTT-domain multiplicative identity is `e` with `e[2i] = 1` and
`e[2i+1] = 0` for all `i`, corresponding to the constant polynomial
`1 ∈ R_q` mapped into each quadratic quotient as `(1, 0)`. -/

/-- The NTT-domain multiplicative identity. -/
def nttOne : Fin n → Zq := fun idx =>
  if idx.val % 2 = 0 then 1 else 0

/-- **Left identity**: `MultiplyNTTs(nttOne, f̂) = f̂`. -/
theorem multiplyNTTs_one_left (fh : Fin n → Zq) :
    multiplyNTTs nttOne fh = fh := by
  ext idx
  unfold multiplyNTTs nttOne baseCaseMultiply
  simp only
  split <;> ring_nf  <;> exact Fin.ext (by grind)

/-- **Right identity**: `MultiplyNTTs(f̂, nttOne) = f̂`. -/
theorem multiplyNTTs_one_right (fh : Fin n → Zq) :
    multiplyNTTs fh nttOne = fh := by
  rw [multiplyNTTs_comm]
  exact multiplyNTTs_one_left fh

end Fips203
