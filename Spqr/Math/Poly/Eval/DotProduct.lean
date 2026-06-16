/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Math.Poly.CharTwo.ToGF216
import Spqr.Math.Poly.Eval

/-!
# Dot-product to evaluation bridge

Connecting the dot product of coefficient and power vectors to
polynomial evaluation, and related Aeneas-level utility lemmas.

## Main statements

* `dot_product_eq_eval` — dot product of coefficient and power vectors
  equals polynomial evaluation.
* `zero_toGF216_eq_empty_sum` — `GF16.ZERO.toGF216` equals an empty sum.
* `max_two_succ_le_usize_max` — `max 2 n + 1 ≤ Usize.max` when
  `n + 1 ≤ Usize.max`.
-/

open Aeneas Aeneas.Std Result Polynomial
open spqr.math.gf spqr.encoding.gf spqr.encoding.polynomial

namespace spqr.encoding.polynomial

/-! ## Dot-product to evaluation bridge -/

/--
Dot-product to polynomial evaluation bridge.

When the power vector `xs` satisfies `xs[j].toGF216 = x.toGF216 ^ j` for
all `j < xs.length`, and `n = v.length ≤ xs.length`, the dot product
`∑ j ∈ Finset.range n, v[j]!.toGF216 * xs[j]!.toGF216` equals the
polynomial evaluation `(listToGF216Poly v).eval (x.toGF216)`.
-/
theorem dot_product_eq_eval
    (x : GF16) (v : List GF16) (xs : List GF16)
    (h_pow : ∀ j, j < xs.length → (xs[j]!).toGF216 = x.toGF216 ^ j)
    (h_len : v.length ≤ xs.length) :
    (∑ j ∈ Finset.range v.length,
      (v[j]!).toGF216 * (xs[j]!).toGF216) =
    (listToGF216Poly v).eval (x.toGF216) := by
  have h_sub : ∀ j ∈ Finset.range v.length,
      (v[j]!).toGF216 * (xs[j]!).toGF216 =
      (v[j]!).toGF216 * x.toGF216 ^ j := by
    intro j hj; rw [Finset.mem_range] at hj
    congr 1; exact h_pow j (by omega)
  rw [Finset.sum_congr rfl h_sub]
  have h_coeff : ∀ j ∈ Finset.range v.length,
      (v[j]!).toGF216 * x.toGF216 ^ j =
      (listToGF216Poly v).coeff j * x.toGF216 ^ j := by
    intro j hj
    congr 1; exact getElem!_toGF216_eq_coeff v j
  rw [Finset.sum_congr rfl h_coeff]
  exact (eval_eq_range_sum (listToGF216Poly v) (x.toGF216) v.length
    (fun j hj => listToGF216Poly_coeff_eq_zero v j hj)).symm

/-! ## Zero accumulator -/

/--
Zero accumulator equals empty sum.
`GF16.ZERO.toGF216 = ∑ j ∈ Finset.range 0, f j` for any `f`.
-/
theorem zero_toGF216_eq_empty_sum
    (v xs : alloc.vec.Vec GF16) :
    GF16.ZERO.toGF216 = ∑ j ∈ Finset.range 0,
      (v.val[j]!).toGF216 * (xs.val[j]!).toGF216 := by
  simp [GF16.ZERO, GF16.toGF216, Nat.toGF216, natToBinaryPoly_zero, map_zero]

/-! ## Usize bound utility -/

/--
Max-2 length bound.
If `n + 1 ≤ Usize.max`, then `max 2 n + 1 ≤ Usize.max`.
-/
theorem max_two_succ_le_usize_max (n : Nat) (h : n + 1 ≤ Usize.max) :
    Nat.max 2 n + 1 ≤ Usize.max := by
  simp only [Nat.max_def]
  split_ifs
  · exact h
  · scalar_tac

end spqr.encoding.polynomial
