/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Encoding.Polynomial.LagrangePolysForCompletePoints
import Spqr.Math.Poly.Lagrange.CompletePoints

/-!
# Spec theorem for `spqr::encoding::polynomial::COMPLETE_POINTS_POLYS_36`

Specialises `lagrange_polys_for_complete_points` to `N = 36`: Lagrange basis polynomials
for points `0, …, 35` in GF(2¹⁶) with `y = GF16::ONE`.

**Source**: spqr/src/encoding/polynomial.rs -/

open Aeneas Aeneas.Std spqr.encoding.gf spqr.math.gf

namespace spqr.encoding.polynomial

instance instInhabitedPolyConst36 : Inhabited (PolyConst 36#usize) := ⟨PolyConst.ZEROS 36#usize⟩

/-- **Spec theorem for `encoding.polynomial.COMPLETE_POINTS_POLYS_36`**:

Each `result[j]` is the `j`-th scaled Lagrange basis polynomial for points `0, …, 35`. -/
@[step]
theorem COMPLETE_POINTS_POLYS_36_spec :
    COMPLETE_POINTS_POLYS_36 ⦃ (result ) =>
      ∀ (j : Nat) (_ : j < 36),
        listToGF216Poly (result.val[j]!).coefficients.val =
          scaledLagrangeBasis 36#usize j ⦄ := by
  unfold COMPLETE_POINTS_POLYS_36
  have h36 : (36#usize).val = 36 := by scalar_tac
  simpa [h36] using
    lagrange_polys_for_complete_points_scaled_spec 36#usize (by scalar_tac) (by scalar_tac)

end spqr.encoding.polynomial
