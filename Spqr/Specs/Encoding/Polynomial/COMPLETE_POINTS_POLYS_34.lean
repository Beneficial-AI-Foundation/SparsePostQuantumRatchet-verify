/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Encoding.Polynomial.LagrangePolysForCompletePoints
import Spqr.Math.Poly.Lagrange.CompletePoints

/-! # Spec theorem for `spqr::encoding::polynomial::COMPLETE_POINTS_POLYS_34`

Specialises `lagrange_polys_for_complete_points` to `N = 34`, precomputing the Lagrange basis
polynomials for the distinct points `0, 1, …, 33` in GF(2¹⁶) with `y = GF16::ONE`.

**Source**: spqr/src/encoding/polynomial.rs -/

open Aeneas Aeneas.Std spqr.encoding.gf spqr.math.gf

namespace spqr.encoding.polynomial

/-- **Spec theorem for `encoding.polynomial.COMPLETE_POINTS_POLYS_34`**:

Each `result[j]` is the `j`-th scaled Lagrange basis polynomial for points `0, 1, …, 33`
with `y = GF16.ONE`.  Instantiates `lagrange_polys_for_complete_points_scaled_spec`
at `N = 34`. -/
@[step]
theorem COMPLETE_POINTS_POLYS_34_spec :
    COMPLETE_POINTS_POLYS_34 ⦃ (result) =>
      ∀ (j : Nat) (_ : j < 34),
        listToGF216Poly (result.val[j]!).coefficients.val =
          scaledLagrangeBasis 34#usize j ⦄ := by
  unfold COMPLETE_POINTS_POLYS_34
  have h34 : (34#usize).val = 34 := by scalar_tac
  simpa [h34] using
    lagrange_polys_for_complete_points_scaled_spec 34#usize (by scalar_tac) (by scalar_tac)

end spqr.encoding.polynomial
