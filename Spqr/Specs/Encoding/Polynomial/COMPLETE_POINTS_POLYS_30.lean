/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Encoding.Polynomial.LagrangePolysForCompletePoints
import Spqr.Math.Poly.Lagrange.CompletePoints

/-!
# Spec theorem for `spqr::encoding::polynomial::COMPLETE_POINTS_POLYS_30`

Specialises `lagrange_polys_for_complete_points` to `N = 30`: Lagrange basis polynomials
for points `0..29` in GF(2¹⁶) with `y = GF16::ONE`.

**Source**: spqr/src/encoding/polynomial.rs -/

open Aeneas Aeneas.Std spqr.encoding.gf spqr.math.gf

namespace spqr.encoding.polynomial

/-- **Spec theorem for `encoding.polynomial.COMPLETE_POINTS_POLYS_30`**:

Each `result[j]` is the `j`-th scaled Lagrange basis polynomial for points `0..29`.
Instantiates `lagrange_polys_for_complete_points_scaled_spec` at `N = 30`. -/
@[step]
theorem COMPLETE_POINTS_POLYS_30_spec :
    COMPLETE_POINTS_POLYS_30 ⦃ (result) =>
      ∀ (j : Nat) (_ : j < 30),
        listToGF216Poly (result.val[j]!).coefficients.val =
          scaledLagrangeBasis 30#usize j ⦄ := by
  unfold COMPLETE_POINTS_POLYS_30
  have h30 : (30#usize).val = 30 := by scalar_tac
  simpa [h30] using
    lagrange_polys_for_complete_points_scaled_spec 30#usize (by scalar_tac) (by scalar_tac)

end spqr.encoding.polynomial
