/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Math.Poly.Lagrange.DenomProd
import Spqr.Math.Poly.Lagrange.CondProdLinearFactors

/-!
# Complete evaluation points and scaled Lagrange basis

This file defines the "complete points" array and the scaled Lagrange basis polynomial
for Lagrange interpolation over `0, 1, …, N−1` in `GF(2¹⁶)`.

## Main definitions

* `completePoints` — the array of evaluation points `⟨GF16.ofNat j, GF16.ONE⟩` for `j < N`.
* `scaledLagrangeBasis` — the `j`-th scaled Lagrange basis polynomial combining
  the Fermat-inverse scaling factor with the conditional product of linear factors.

## Auxiliary lemmas

* `pt_ext` — structure extensionality for `Pt`.
* `gf16_ext` — extensionality for `GF16`.
-/

open Aeneas Aeneas.Std Polynomial
open spqr.encoding.gf
open spqr.encoding.polynomial.PolyConst.lagrange_interpolate_pt_loop

namespace spqr.encoding.polynomial

/-- Structure extensionality for `Pt`: two points are equal iff their fields agree. -/
theorem pt_ext {a b : Pt} (hx : a.x = b.x) (hy : a.y = b.y) : a = b := by
  cases a; cases b; simp_all

/-- GF16 extensionality: two GF16 values are equal iff their `value` fields agree. -/
theorem gf16_ext {a b : GF16} (h : a.value = b.value) : a = b := by
  cases a; cases b; simpa using h

/-- The "complete points" array for size `N`: evaluation points `0, 1, …, N−1` in GF(2¹⁶) with
`y = GF16.ONE`. Each entry `j` has `x.value.val = j` and `y = GF16.ONE`. -/
@[global_simps, irreducible]
def completePoints (N : Usize) : Array Pt N :=
  ⟨(List.finRange N.val).map (fun j =>
    ⟨⟨⟨BitVec.ofNat 16 j.val⟩⟩, GF16.ONE⟩),
  by simp⟩

/-- The `j`-th scaled Lagrange basis polynomial for the complete-points array of size `N`:
`C(completePoints(N)[j].y · (lagrangeDenomProd …)^(2¹⁶−2)) · condProdLinearFactors …`.
This is the `j`-th term of the Lagrange interpolation formula, combining the Fermat-inverse
scaling factor with the conditional product of linear factors. -/
@[global_simps, irreducible]
noncomputable def scaledLagrangeBasis (N : Usize) (j : Nat) :
    Polynomial GF216 :=
  C (((completePoints N).val[j]!).y.toGF216 *
    (lagrangeDenomProd ((completePoints N)[j]!).x
      ((completePoints N).val.take N.val) 0) ^ (2 ^ 16 - 2)) *
    condProdLinearFactors ((completePoints N)[j]!).x
      ((completePoints N).val.take N.val) 0

end spqr.encoding.polynomial
