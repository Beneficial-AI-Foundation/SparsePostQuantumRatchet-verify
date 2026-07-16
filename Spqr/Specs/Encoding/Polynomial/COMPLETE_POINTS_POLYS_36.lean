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
  step*
  have h_eq : result = completePoints 36#usize := by
    simp only [global_simps]
    apply Subtype.ext
    apply List.ext_getElem (by simp)
    intro n h1' h2'
    obtain ⟨hx, hy⟩ := result_post1 n (by grind)
    simp only [Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD,
      List.getElem?_eq_getElem h1', Option.getD_some] at hx hy
    simp only [List.getElem_map, List.getElem_finRange] at h2' ⊢
    apply pt_ext
    · apply gf16_ext
      apply UScalar.eq_of_val_eq
      trans n
      · exact hx
      · change n = (⟨BitVec.ofNat 16 n⟩ : UScalar .U16).bv.toNat
        simp [BitVec.toNat_ofNat]
        grind
    · exact hy.trans (gf16_ext GF16.ONE_value)
  have h := result_post2 _ result_post3 (by grind) (by grind)
  rw [h_eq] at h
  simp only [global_simps] at h ⊢
  have h36 : (↑(36#usize) : Nat) = 36 := by scalar_tac
  simp only [h36] at h ⊢
  simp only [List.getElem!_eq_getElem?_getD] at ⊢
  grind

end spqr.encoding.polynomial
