/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Encoding.Polynomial.LagrangePolysForCompletePoints
import Spqr.Math.Poly.Lagrange.CompletePoints

/-!
# Spec theorem for `spqr::encoding::polynomial::COMPLETE_POINTS_POLYS_5`

Specialises `lagrange_polys_for_complete_points` to `N = 5`: Lagrange basis polynomials
for points `0..4` in GF(2¹⁶) with `y = GF16::ONE`.

**Source**: spqr/src/encoding/polynomial.rs -/

open Aeneas Aeneas.Std spqr.encoding.gf spqr.math.gf

namespace spqr.encoding.polynomial

/-- **Spec theorem for `encoding.polynomial.COMPLETE_POINTS_POLYS_5`**:

Each `result[j]` is the `j`-th scaled Lagrange basis polynomial for points `0..4`.
Instantiates `lagrange_polys_for_complete_points_scaled_spec` at `N = 5`. -/
@[step]
theorem COMPLETE_POINTS_POLYS_5_spec :
    COMPLETE_POINTS_POLYS_5 ⦃ (result) =>
      ∀ (j : Nat) (_ : j < 5),
        listToGF216Poly (result.val[j]!).coefficients.val =
          scaledLagrangeBasis 5#usize j ⦄ := by
  unfold COMPLETE_POINTS_POLYS_5
  have h5 : (5#usize).val = 5 := by scalar_tac
  simpa [h5] using
    lagrange_polys_for_complete_points_scaled_spec 5#usize (by scalar_tac) (by scalar_tac)

end spqr.encoding.polynomial
