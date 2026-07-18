/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Encoding.Polynomial.LagrangePolysForCompletePoints
import Spqr.Math.Poly.Lagrange.CompletePoints

/-! # Spec theorem for `spqr::encoding::polynomial::COMPLETE_POINTS_POLYS_3`

`COMPLETE_POINTS_POLYS_3` (line 501) specialises `lagrange_polys_for_complete_points` to `N = 3`,
precomputing the Lagrange basis polynomials for evaluation points `0, 1, 2` in GF(2¹⁶) with
`y = GF16::ONE`.

The postcondition is inherited from `lagrange_polys_for_complete_points_spec`: there exists
`ones1` of size 3 with `ones1[j].x.toGF216 = Nat.toGF216 j`, `ones1[j].y = GF16::ONE`, and
each `result[j]` equals the standard Lagrange basis polynomial for these points.

In GF(2¹⁶) the points `0, 1, 2` are pairwise distinct, so the Fermat-inverse scaling yields
`ones1[j].y / ∏_{k ≠ j} (ones1[j].x − ones1[k].x)`, and subtraction coincides with XOR.

**Source**: spqr/src/encoding/polynomial.rs (line 501)-/

open Aeneas Aeneas.Std Result spqr.encoding.gf Polynomial
open spqr.encoding.polynomial.PolyConst.lagrange_interpolate_pt_loop

namespace spqr.encoding.polynomial

/-- **Spec theorem for `encoding.polynomial.COMPLETE_POINTS_POLYS_3`**:

Evaluates successfully (specialisation of `lagrange_polys_for_complete_points` at `N = 3`).
Each `result[j]` is the `j`-th scaled Lagrange basis polynomial for the complete points
`0, 1, 2` with `y = GF16.ONE`.  Instantiates
`lagrange_polys_for_complete_points_scaled_spec` at `N = 3`. -/
@[step]
theorem COMPLETE_POINTS_POLYS_3_spec :
    COMPLETE_POINTS_POLYS_3 ⦃ (result) =>
      ∀ (j : Nat) (_ : j < 3),
        listToGF216Poly (result.val[j]!).coefficients.val = scaledLagrangeBasis 3#usize j ⦄ := by
  unfold COMPLETE_POINTS_POLYS_3
  have h3 : (3#usize).val = 3 := by scalar_tac
  simpa [h3] using
    lagrange_polys_for_complete_points_scaled_spec 3#usize (by scalar_tac) (by scalar_tac)

end spqr.encoding.polynomial
