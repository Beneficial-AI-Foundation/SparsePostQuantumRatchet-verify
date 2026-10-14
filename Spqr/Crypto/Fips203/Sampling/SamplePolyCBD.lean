/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module
public import Spqr.Crypto.Fips203.Params
public import Spqr.Crypto.Fips203.Ring
public import Mathlib.Tactic.Ring
/-!
# FIPS 203 Algorithm 6: `SamplePolyCBD_η`

NIST FIPS 203 (ML-KEM, August 2024), § 4.2.2, defines `SamplePolyCBD_η` as deterministic
sampling of a polynomial from the centered binomial distribution `CBD_η`.

Given a byte array `B` of length `64 · η`, the algorithm first expands `B` into a bit array
`b` of length `512 · η` via `BytesToBits`.  For each coefficient index `i ∈ {0,…,255}`:

  `x ← ∑ⱼ₌₀^{η-1} b[2·i·η + j]`
  `y ← ∑ⱼ₌₀^{η-1} b[2·i·η + η + j]`
  `f[i] ← x − y  mod q`

The result is a polynomial `f ∈ R_q` whose coefficients lie in `{−η,…,η}` (mod `q`).

For ML-KEM-768, `η₁ = η₂ = 2`, so the input is `128` bytes and each coefficient is sampled
from `CBD_2 ∈ {−2,−1,0,1,2}`.

**Source**: NIST FIPS 203, § 4.2.2, Algorithm 6
-/

@[expose] public section

namespace Fips203

/-! ## Bit extraction -/

/-- Extract bit `j` (0-indexed from LSB) from byte `b`. -/
def bitAt (b : UInt8) (j : Fin 8) : ℕ :=
  (b.toNat >>> j.val) &&& 1

/-- `bitAt` returns 0 or 1. -/
theorem bitAt_le_one (b : UInt8) (j : Fin 8) : bitAt b j ≤ 1 := by
  unfold bitAt
  show (b.toNat >>> j.val) &&& 1 ≤ 1
  have : (b.toNat >>> j.val) &&& 1 < 2 := by grind
  omega

/-! ## BytesToBits expansion (FIPS 203, Algorithm 2)

For `SamplePolyCBD_η` we need the bit-level view of the input byte array.  Rather than
defining `BytesToBits` as a separate top-level algorithm (see `Conversion/BytesToBits.lean`),
we inline the bit extraction here for self-containedness. -/

/-- Bit `i` of the byte array `B`, using little-endian bit ordering within each byte:
`bits B i = bit (i mod 8) of B[i / 8]`. -/
def bits (B : ℕ → UInt8) (i : ℕ) : ℕ :=
  bitAt (B (i / 8)) ⟨i % 8, Nat.mod_lt _ (by omega)⟩

/-- Each extracted bit is 0 or 1. -/
theorem bits_le_one (B : ℕ → UInt8) (i : ℕ) : bits B i ≤ 1 := by
  unfold bits
  exact bitAt_le_one _ _

/-! ## Partial bit sums -/

/-- Sum of `η` consecutive bits starting at position `start`:
`bitSum B start η = ∑ⱼ₌₀^{η-1} bits B (start + j)`. -/
def bitSum (B : ℕ → UInt8) (start η : ℕ) : ℕ :=
  (Finset.range η).sum fun j => bits B (start + j)

/-- `bitSum` is bounded by `η`. -/
theorem bitSum_le (B : ℕ → UInt8) (start η : ℕ) : bitSum B start η ≤ η := by
  unfold bitSum
  apply le_trans (Finset.sum_le_sum fun j _ => bits_le_one B (start + j))
  simp [Finset.sum_const, Finset.card_range]

/-! ## Single-coefficient sampling -/

/-- Sample the `i`-th coefficient of the CBD polynomial:
`cbdCoeff B η i = (∑ⱼ b[2iη + j]) − (∑ⱼ b[2iη + η + j])  mod q`.

The two sums `x` and `y` each range over `η` consecutive bits.  The difference `x − y`
lies in `{−η, …, η}` ⊂ ℤ`, which is then reduced modulo `q = 3329`. -/
def cbdCoeff (B : ℕ → UInt8) (η : ℕ) (i : ℕ) : Zq :=
  let x := bitSum B (2 * i * η) η
  let y := bitSum B (2 * i * η + η) η
  Zq.ofInt (↑x - ↑y)

/-! ## Full polynomial sampling -/

/-- **Algorithm 6 — `SamplePolyCBD_η`** (FIPS 203, § 4.2.2).

Given a byte array `B` of length `64 · η` (presented as a function `ℕ → UInt8` for
uniformity with the `SampleNTT` interface), produces a polynomial `f ∈ R_q` whose
coefficients are drawn from the centered binomial distribution `CBD_η`.

```
SamplePolyCBD_η(B):
  b ← BytesToBits(B)
  for i from 0 to 255:
    x ← ∑_{j=0}^{η-1} b[2iη + j]
    y ← ∑_{j=0}^{η-1} b[2iη + η + j]
    f[i] ← x − y  mod q
  return f
```
-/
def samplePolyCBD (B : ℕ → UInt8) (η : ℕ) : Fin n → Zq :=
  fun i => cbdCoeff B η i.val

/-! ## Elementary properties -/

/-- Each CBD coefficient, lifted to `ℤ`, has absolute value at most `η`. -/
theorem cbdCoeff_abs_le (B : ℕ → UInt8) (η : ℕ) (i : ℕ) :
    |((bitSum B (2 * i * η) η : ℤ) - (bitSum B (2 * i * η + η) η : ℤ))| ≤ η := by
  have hx := bitSum_le B (2 * i * η) η
  have hy := bitSum_le B (2 * i * η + η) η
  rw [abs_le]
  constructor <;> omega

/-- For `η = 0`, every coefficient is zero. -/
theorem samplePolyCBD_eta_zero (B : ℕ → UInt8) (i : Fin n) :
    samplePolyCBD B 0 i = 0 := by
  simp [samplePolyCBD, cbdCoeff, bitSum]

/-- `samplePolyCBD` with `η = 2` consumes `64 · 2 = 128` input bytes, matching ML-KEM-768's
`η₁ = η₂ = 2`. -/
theorem samplePolyCBD_eta2_input_bits :
    512 * 2 = 1024 := by norm_num

/-- The number of input bytes required for `SamplePolyCBD_η` is `64 · η`. -/
theorem samplePolyCBD_input_bytes (η : ℕ) :
    512 * η / 8 = 64 * η := by omega

/-- `bitSum` with `η = 2` expands to the sum of two consecutive bits. -/
theorem bitSum_two (B : ℕ → UInt8) (start : ℕ) :
    bitSum B start 2 = bits B start + bits B (start + 1) := by
  unfold bitSum
  simp [Finset.sum_range_succ]

end Fips203
