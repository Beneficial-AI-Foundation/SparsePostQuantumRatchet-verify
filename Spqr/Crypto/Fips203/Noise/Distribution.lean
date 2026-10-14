/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module
public import Mathlib.Probability.Distributions.Uniform
public import Spqr.Crypto.Fips203.Sampling.SamplePolyCBD
/-!
# Centered Binomial Distribution `CBD_η` as a `PMF` (FIPS 203, § 4.2.2)

FIPS 203 Algorithm 6 (`SamplePolyCBD_η`, see `Sampling/SamplePolyCBD.lean`) derives each
polynomial coefficient from `2·η` pseudorandom bits `b` as `(∑_{j<η} b_j) − (∑_{j<η} b_{η+j})`.
When the input bits are uniform, the resulting integer follows the **centered binomial
distribution** `CBD_η` on `{−η, …, η}`.

This file is the first step of the probabilistic noise analysis (plan.md, Phase 8): it models
`CBD_η` as a Mathlib `PMF ℤ`, the pushforward of the uniform distribution on bit tuples under
the Algorithm 6 bit-sum map, and proves

* `cbdPMF_apply` — the exact counting formula `cbdPMF η x = #{b | cbdVal η b = x} / 2^(2η)`;
* `cbdVal_abs_le` / `abs_le_of_mem_support_cbdPMF` — the support is contained in `[−η, η]`;
* the five concrete probabilities of `CBD_2` (the ML-KEM-768 case `η₁ = η₂ = 2`):
  `P(0) = 6/16`, `P(±1) = 4/16`, `P(±2) = 1/16`;
* `cbdCoeff_eq_ofInt_cbdVal` — the deterministic sampler `cbdCoeff` of Algorithm 6 is exactly
  `Zq.ofInt ∘ cbdVal` applied to the relevant input bits, connecting the probabilistic model to
  the spec-layer definition used by `samplePolyCBD`.

Future steps (plan.md, Phase 8) build on this to bound the total decryption-noise polynomial of
`PKE/RoundTrip.lean` (`noiseBoundedAt`) with high probability.

**Source**: NIST FIPS 203, § 4.2.2 (Algorithm 6), § 3.3 (decryption failure)
-/

@[expose] public section

namespace Fips203

open scoped ENNReal

/-! ## Bit tuples and the CBD value map -/

/-- The `2·η` input bits consumed per coefficient by `SamplePolyCBD_η`. -/
abbrev CbdBits (η : ℕ) : Type := Fin (2 * η) → Fin 2

/-- The **CBD value** of a bit tuple: `(∑_{j<η} b_j) − (∑_{j<η} b_{η+j})`, the integer computed
by step `f[i] ← x − y` of FIPS 203 Algorithm 6 before reduction mod `q`. -/
def cbdVal (η : ℕ) (b : CbdBits η) : ℤ :=
  (∑ j : Fin η, ((b ⟨j.val, by have := j.isLt; omega⟩ : Fin 2).val : ℤ)) -
    ∑ j : Fin η, ((b ⟨η + j.val, by have := j.isLt; omega⟩ : Fin 2).val : ℤ)

/-- Each of the two bit sums lies in `[0, η]`, so `|cbdVal η b| ≤ η`. -/
theorem cbdVal_abs_le (η : ℕ) (b : CbdBits η) : |cbdVal η b| ≤ (η : ℤ) := by
  have hx : (∑ j : Fin η, ((b ⟨j.val, by have := j.isLt; omega⟩ : Fin 2).val : ℤ)) ≤ η := by
    calc (∑ j : Fin η, ((b ⟨j.val, by have := j.isLt; omega⟩ : Fin 2).val : ℤ))
        ≤ ∑ _j : Fin η, (1 : ℤ) :=
          Finset.sum_le_sum fun j _ => by
            have := (b ⟨j.val, by have := j.isLt; omega⟩).isLt
            omega
      _ = η := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hy : (∑ j : Fin η, ((b ⟨η + j.val, by have := j.isLt; omega⟩ : Fin 2).val : ℤ)) ≤ η := by
    calc (∑ j : Fin η, ((b ⟨η + j.val, by have := j.isLt; omega⟩ : Fin 2).val : ℤ))
        ≤ ∑ _j : Fin η, (1 : ℤ) :=
          Finset.sum_le_sum fun j _ => by
            have := (b ⟨η + j.val, by have := j.isLt; omega⟩).isLt
            omega
      _ = η := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hx0 : (0 : ℤ) ≤ ∑ j : Fin η, ((b ⟨j.val, by have := j.isLt; omega⟩ : Fin 2).val : ℤ) :=
    Finset.sum_nonneg fun j _ => Int.natCast_nonneg _
  have hy0 : (0 : ℤ) ≤
      ∑ j : Fin η, ((b ⟨η + j.val, by have := j.isLt; omega⟩ : Fin 2).val : ℤ) :=
    Finset.sum_nonneg fun j _ => Int.natCast_nonneg _
  rw [cbdVal, abs_le]
  omega

/-! ## The centered binomial distribution as a `PMF` -/

/-- **`CBD_η`**: the distribution of `cbdVal η` applied to `2·η` uniform bits. -/
noncomputable def cbdPMF (η : ℕ) : PMF ℤ :=
  (PMF.uniformOfFintype (CbdBits η)).map (cbdVal η)

/-- There are `2^(2·η)` bit tuples. -/
theorem card_cbdBits (η : ℕ) : Fintype.card (CbdBits η) = 2 ^ (2 * η) := by
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

/-- **Counting formula** for `CBD_η`: the probability of the value `x` is the number of bit
tuples mapping to `x`, divided by `2^(2·η)`. -/
theorem cbdPMF_apply (η : ℕ) (x : ℤ) :
    cbdPMF η x =
      ((Finset.univ.filter fun b : CbdBits η => x = cbdVal η b).card : ℝ≥0∞) / 2 ^ (2 * η) := by
  rw [cbdPMF, PMF.map_apply, tsum_fintype]
  simp only [PMF.uniformOfFintype_apply]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, card_cbdBits, div_eq_mul_inv]
  norm_cast

/-- Every point of the support of `CBD_η` has absolute value at most `η`. -/
theorem abs_le_of_mem_support_cbdPMF {η : ℕ} {x : ℤ} (hx : x ∈ (cbdPMF η).support) :
    |x| ≤ (η : ℤ) := by
  rw [cbdPMF, PMF.support_map] at hx
  obtain ⟨b, _, rfl⟩ := hx
  exact cbdVal_abs_le η b

/-! ## Concrete probabilities for `η = 2` (ML-KEM-768)

For `η₁ = η₂ = 2` the distribution on `{−2, −1, 0, 1, 2}` is `(1, 4, 6, 4, 1) / 16`.  The fiber
cardinalities are settled by kernel computation over the `16` bit tuples. -/

/-- `P(CBD_2 = 0) = 6/16`. -/
theorem cbdPMF_two_zero : cbdPMF 2 0 = 6 / 16 := by
  rw [cbdPMF_apply]
  norm_num [show (Finset.univ.filter fun b : CbdBits 2 => (0 : ℤ) = cbdVal 2 b).card = 6
    from by decide]

/-- `P(CBD_2 = 1) = 4/16`. -/
theorem cbdPMF_two_one : cbdPMF 2 1 = 4 / 16 := by
  rw [cbdPMF_apply]
  norm_num [show (Finset.univ.filter fun b : CbdBits 2 => (1 : ℤ) = cbdVal 2 b).card = 4
    from by decide]

/-- `P(CBD_2 = −1) = 4/16`. -/
theorem cbdPMF_two_neg_one : cbdPMF 2 (-1) = 4 / 16 := by
  rw [cbdPMF_apply]
  norm_num [show (Finset.univ.filter fun b : CbdBits 2 => (-1 : ℤ) = cbdVal 2 b).card = 4
    from by decide]

/-- `P(CBD_2 = 2) = 1/16`. -/
theorem cbdPMF_two_two : cbdPMF 2 2 = 1 / 16 := by
  rw [cbdPMF_apply]
  norm_num [show (Finset.univ.filter fun b : CbdBits 2 => (2 : ℤ) = cbdVal 2 b).card = 1
    from by decide]

/-- `P(CBD_2 = −2) = 1/16`. -/
theorem cbdPMF_two_neg_two : cbdPMF 2 (-2) = 1 / 16 := by
  rw [cbdPMF_apply]
  norm_num [show (Finset.univ.filter fun b : CbdBits 2 => (-2 : ℤ) = cbdVal 2 b).card = 1
    from by decide]

/-! ## Connection with the deterministic sampler `cbdCoeff` (Algorithm 6) -/

/-- The `2·η` bits of the byte stream `B` consumed for coefficient `i`, as a `CbdBits η`
tuple: bit `j` is `bits B (2·i·η + j)`. -/
def coeffBits (B : ℕ → UInt8) (η i : ℕ) : CbdBits η :=
  fun j => ⟨bits B (2 * i * η + j.val),
    Nat.lt_succ_of_le (bits_le_one B (2 * i * η + j.val))⟩

/-- `bitSum` over `Finset.range` equals the sum over `Fin η`. -/
theorem bitSum_eq_sum_fin (B : ℕ → UInt8) (start η : ℕ) :
    bitSum B start η = ∑ j : Fin η, bits B (start + j.val) := by
  rw [bitSum, Finset.sum_range fun j => bits B (start + j)]

/-- **Bridge to Algorithm 6**: the deterministic coefficient sampler `cbdCoeff` is the mod-`q`
reduction of `cbdVal` applied to the input bits of coefficient `i`.  Hence, when the input bits
are uniform, coefficient `i` of `samplePolyCBD` is distributed as `Zq.ofInt ∘ CBD_η`. -/
theorem cbdCoeff_eq_ofInt_cbdVal (B : ℕ → UInt8) (η i : ℕ) :
    cbdCoeff B η i = Zq.ofInt (cbdVal η (coeffBits B η i)) := by
  rw [cbdCoeff, cbdVal]
  congr 1
  rw [bitSum_eq_sum_fin, bitSum_eq_sum_fin]
  push_cast
  congr 1
  all_goals exact Finset.sum_congr rfl fun j _ => by simp only [coeffBits, Nat.add_assoc]

end Fips203
