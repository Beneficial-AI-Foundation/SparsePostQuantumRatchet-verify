/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Crypto.Fips203.Noise.Moments
/-!
# Tail Bounds for the Centered Binomial Distribution (counting level)

Step 8.4 of the probabilistic noise analysis (plan.md, Phase 8).  Following the counting-level
style of `Noise/Distribution.lean` and `Noise/Moments.lean` (probabilities are fiber
cardinalities over the uniform bit tuples, divided by `2^(2η)`), this file provides the generic
tail machinery needed to bound the total decryption noise:

* **Chebyshev at the counting level** (`sq_mul_card_filter_abs_le`): for any `f : α → ℤ` on a
  fintype and `t > 0`, `t² · #{a | t ≤ |f a|} ≤ ∑_a f(a)²` — dividing by `|α|` this is
  `P[|X| ≥ t] ≤ E[X²] / t²`;
* its instantiation to `CBD_η` via the second moments of `Noise/Moments.lean`
  (`card_cbdVal_tail_two/three`);
* **exact tail counts** for `CBD_2` (the ML-KEM-768 case) by kernel computation:
  `#{|X| ≥ 1} = 10` (`P = 10/16`), `#{|X| ≥ 2} = 2` (`P = 2/16`), `#{|X| ≥ 3} = 0`;
* **union bound** (`card_filter_exists_le`): the count of tuples violating *some* event in a
  finite family is at most the sum of the per-event counts — the tool used in step 8.5 to pass
  from one noise coefficient to all `256`.

**Source**: NIST FIPS 203, § 3.3 (decryption failure rate)
-/

namespace Fips203

/-! ## Counting-level Chebyshev inequality -/

/-- **Chebyshev / Markov at the counting level**: for `f : α → ℤ` on a fintype and `t > 0`,
`t² · #{a | t ≤ |f a|} ≤ ∑_a f(a)²`.  Dividing both sides by `|α|` gives the familiar
`P[|X| ≥ t] ≤ E[X²] / t²` for the uniform distribution on `α`. -/
theorem sq_mul_card_filter_abs_le {α : Type*} [Fintype α]
    (f : α → ℤ) (t : ℤ) (ht : 0 ≤ t) :
    t ^ 2 * ((Finset.univ.filter fun a => t ≤ |f a|).card : ℤ) ≤ ∑ a : α, f a ^ 2 := by
  calc t ^ 2 * ((Finset.univ.filter fun a => t ≤ |f a|).card : ℤ)
      = ∑ _a ∈ Finset.univ.filter fun a => t ≤ |f a|, t ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ a ∈ Finset.univ.filter fun a => t ≤ |f a|, f a ^ 2 := by
        refine Finset.sum_le_sum fun a ha => ?_
        have h := (Finset.mem_filter.mp ha).2
        calc t ^ 2 ≤ |f a| ^ 2 := pow_le_pow_left₀ ht h 2
          _ = f a ^ 2 := sq_abs (f a)
    _ ≤ ∑ a : α, f a ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun a _ _ => sq_nonneg (f a)

/-! ## Chebyshev tails for `CBD_η` -/

/-- Chebyshev tail for `CBD_2`: `t² · #{b | t ≤ |cbdVal 2 b|} ≤ 16`, i.e.
`P[|X| ≥ t] ≤ 1/t²` (variance `1`). -/
theorem card_cbdVal_tail_two (t : ℤ) (ht : 0 ≤ t) :
    t ^ 2 * ((Finset.univ.filter fun b : CbdBits 2 => t ≤ |cbdVal 2 b|).card : ℤ) ≤ 16 := by
  calc t ^ 2 * ((Finset.univ.filter fun b : CbdBits 2 => t ≤ |cbdVal 2 b|).card : ℤ)
      ≤ ∑ b : CbdBits 2, cbdVal 2 b ^ 2 := sq_mul_card_filter_abs_le _ t ht
    _ = 16 := sum_cbdVal_sq_two

/-- Chebyshev tail for `CBD_3`: `t² · #{b | t ≤ |cbdVal 3 b|} ≤ 96`, i.e.
`P[|X| ≥ t] ≤ (3/2)/t²` (variance `3/2`). -/
theorem card_cbdVal_tail_three (t : ℤ) (ht : 0 ≤ t) :
    t ^ 2 * ((Finset.univ.filter fun b : CbdBits 3 => t ≤ |cbdVal 3 b|).card : ℤ) ≤ 96 := by
  calc t ^ 2 * ((Finset.univ.filter fun b : CbdBits 3 => t ≤ |cbdVal 3 b|).card : ℤ)
      ≤ ∑ b : CbdBits 3, cbdVal 3 b ^ 2 := sq_mul_card_filter_abs_le _ t ht
    _ = 96 := sum_cbdVal_sq_three

/-! ## Exact tail counts for `CBD_2` (ML-KEM-768)

Kernel computation over the `16` bit tuples gives the exact tails, sharper than Chebyshev. -/

/-- `#{b | 1 ≤ |cbdVal 2 b|} = 10`: `P[|X| ≥ 1] = 10/16`. -/
theorem card_cbdVal_two_ge_one :
    (Finset.univ.filter fun b : CbdBits 2 => 1 ≤ |cbdVal 2 b|).card = 10 := by decide

/-- `#{b | 2 ≤ |cbdVal 2 b|} = 2`: `P[|X| ≥ 2] = 2/16`. -/
theorem card_cbdVal_two_ge_two :
    (Finset.univ.filter fun b : CbdBits 2 => 2 ≤ |cbdVal 2 b|).card = 2 := by decide

/-- `#{b | 3 ≤ |cbdVal 2 b|} = 0`: the support of `CBD_2` is contained in `[−2, 2]`. -/
theorem card_cbdVal_two_ge_three :
    (Finset.univ.filter fun b : CbdBits 2 => 3 ≤ |cbdVal 2 b|).card = 0 := by decide

/-! ## Union bound -/

/-- **Union bound at the counting level**: the number of elements violating *some* event of a
finite family is at most the sum of the per-event violation counts.  Step 8.5 applies this with
`ι = Fin 256` to pass from a single noise coefficient to the whole polynomial. -/
theorem card_filter_exists_le {α ι : Type*} [Fintype α]
    (s : Finset ι) (p : ι → α → Prop) [∀ i, DecidablePred (p i)]
    [DecidablePred fun a => ∃ i ∈ s, p i a] :
    (Finset.univ.filter fun a => ∃ i ∈ s, p i a).card ≤
      ∑ i ∈ s, (Finset.univ.filter (p i)).card := by
  classical
  refine le_trans (Finset.card_le_card ?_) (Finset.card_biUnion_le)
  intro a ha
  obtain ⟨i, hi, hpi⟩ := (Finset.mem_filter.mp ha).2
  exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_filter.mpr ⟨Finset.mem_univ a, hpi⟩⟩

end Fips203
