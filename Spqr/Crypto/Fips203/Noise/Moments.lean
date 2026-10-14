/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module
public import Spqr.Crypto.Fips203.Noise.Distribution
/-!
# Moments of the Centered Binomial Distribution `CBD_η`

For the `PMF` model
`cbdPMF η` of `Noise/Distribution.lean` we establish:

* **Symmetry** (`cbdPMF_neg`): `CBD_η(−x) = CBD_η(x)`, via the involution `swapHalves` that
  exchanges the two bit halves and negates `cbdVal`; consequently the distribution has
  **mean zero** (`sum_cbdVal_eq_zero` at the counting level).
* **Second moment** for the concrete FIPS 203 parameters, by kernel computation over all bit
  tuples: `∑_b (cbdVal η b)² = η · 2^(2η−1)` for `η = 2` (`16` tuples, ML-KEM-768/1024, variance
  `1`) and `η = 3` (`64` tuples, ML-KEM-512's `η₁`, variance `3/2`): `sum_cbdVal_sq_two`,
  `sum_cbdVal_sq_three`, and the `PMF`-level form `cbdPMF_two_secondMoment`.

**Source**: NIST FIPS 203, § 4.2.2; the variance of `CBD_η` is `η/2` (standard fact).
-/

@[expose] public section

namespace Fips203

open scoped ENNReal

/-! ## The halves-swapping involution -/

/-- Swap the two halves of a bit tuple: bit `j` of the first half becomes bit `j + η` and vice
versa.  Under `cbdVal` this exchanges the positive and negative sums, negating the value. -/
def swapHalves {η : ℕ} (b : CbdBits η) : CbdBits η :=
  fun j => b ⟨if j.val < η then j.val + η else j.val - η, by have := j.isLt; split <;> omega⟩

/-- `swapHalves` is an involution. -/
theorem swapHalves_involutive (η : ℕ) : Function.Involutive (swapHalves (η := η)) := by
  intro b
  funext j
  have hj := j.isLt
  simp only [swapHalves]
  exact congrArg b (Fin.ext (by dsimp only; split <;> split <;> omega))

/-- `cbdVal` is negated by `swapHalves`. -/
theorem cbdVal_swapHalves (η : ℕ) (b : CbdBits η) :
    cbdVal η (swapHalves b) = -cbdVal η b := by
  rw [cbdVal, cbdVal, neg_sub]
  congr 1
  · exact Finset.sum_congr rfl fun j _ => by
      have hj := j.isLt
      simp only [swapHalves]
      exact congrArg (fun i => ((b i : Fin 2).val : ℤ))
        (Fin.ext (by dsimp only; split <;> omega))
  · exact Finset.sum_congr rfl fun j _ => by
      have hj := j.isLt
      simp only [swapHalves]
      exact congrArg (fun i => ((b i : Fin 2).val : ℤ))
        (Fin.ext (by dsimp only; split <;> omega))

/-! ## Symmetry and mean zero -/

/-- **Symmetry of `CBD_η`**: `cbdPMF η (−x) = cbdPMF η x`. -/
theorem cbdPMF_neg (η : ℕ) (x : ℤ) : cbdPMF η (-x) = cbdPMF η x := by
  rw [cbdPMF_apply, cbdPMF_apply]
  congr 2
  exact Finset.card_nbij' swapHalves swapHalves
    (fun b hb => by
      have hb' := (Finset.mem_filter.mp hb).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [cbdVal_swapHalves, ← hb', neg_neg]⟩)
    (fun b hb => by
      have hb' := (Finset.mem_filter.mp hb).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [cbdVal_swapHalves, ← hb']⟩)
    (fun b _ => swapHalves_involutive η b)
    (fun b _ => swapHalves_involutive η b)

/-- **Mean zero** at the counting level: the values `cbdVal η b` sum to `0` over all bit
tuples.  Dividing by `2^(2η)` this is `E[CBD_η] = 0`. -/
theorem sum_cbdVal_eq_zero (η : ℕ) : ∑ b : CbdBits η, cbdVal η b = 0 := by
  have h : ∑ b : CbdBits η, cbdVal η b = ∑ b : CbdBits η, cbdVal η (swapHalves b) :=
    (Fintype.sum_equiv (Function.Involutive.toPerm _ (swapHalves_involutive η)).symm _ _
      fun b => rfl).symm
  have h' : ∑ b : CbdBits η, cbdVal η (swapHalves b) = -∑ b : CbdBits η, cbdVal η b := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun b _ => cbdVal_swapHalves η b
  omega

/-! ## Second moment for the FIPS 203 parameters

`Var(CBD_η) = η/2`.  The two parameter values used by FIPS 203 (`η = 2` for ML-KEM-768/1024 and
both CBDs of ML-KEM-768; `η = 3` for ML-KEM-512's `η₁`) are settled by kernel computation over
the `2^(2η)` bit tuples, matching this directory's verified-computation strategy. -/

/-- `∑_b (cbdVal 2 b)² = 16 = 2 · 2³`: the second moment of `CBD_2` is `16/16 = 1 = η/2`. -/
theorem sum_cbdVal_sq_two : ∑ b : CbdBits 2, cbdVal 2 b ^ 2 = 16 := by decide

/-- `∑_b (cbdVal 3 b)² = 96 = 3 · 2⁵`: the second moment of `CBD_3` is `96/64 = 3/2 = η/2`. -/
theorem sum_cbdVal_sq_three : ∑ b : CbdBits 3, cbdVal 3 b ^ 2 = 96 := by decide

/-- **Second moment of `CBD_2` at the `PMF` level**: `E[X²] = 1`, written as the weighted sum
over the support `{−2, −1, 0, 1, 2}` using the point probabilities of `Distribution.lean`. -/
theorem cbdPMF_two_secondMoment :
    cbdPMF 2 (-2) * 4 + cbdPMF 2 (-1) * 1 + cbdPMF 2 1 * 1 + cbdPMF 2 2 * 4 = 1 := by
  rw [cbdPMF_two_neg_two, cbdPMF_two_neg_one, cbdPMF_two_one, cbdPMF_two_two]
  rw [show ((16 : ℝ≥0∞)) = (16 : ℕ) by norm_num] at *
  norm_num [ENNReal.div_eq_inv_mul]
  rw [← ENNReal.inv_mul_cancel (a := 16) (by norm_num) (by norm_num)]
  ring

end Fips203
