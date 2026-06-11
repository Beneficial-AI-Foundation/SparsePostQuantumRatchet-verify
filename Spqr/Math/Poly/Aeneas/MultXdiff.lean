/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Math.List

/-! # Polynomial identity for `mult_xdiff_assign_trailing`

Closed-form identity for the in-place recurrence `v[i−1] −= v[i] * d`
used by `mult_xdiff_assign_trailing`.

`listToGF216Poly rs = listToGF216Poly cs − C(d.toGF216) · X^(s−1) · listToGF216Poly (cs.drop s)`. -/

open Polynomial spqr.encoding.gf

namespace spqr.encoding.polynomial

theorem mult_xdiff_poly_identity
    (cs rs : List GF16) (s : Nat) (d : GF16)
    (h_s_pos : 1 ≤ s) (h_s_le : s ≤ cs.length)
    (h_len : rs.length = cs.length)
    (h_mod : ∀ j, s ≤ j + 1 → j + 1 < cs.length → ∀ hj : j < rs.length,
      (rs.get ⟨j, hj⟩).toGF216 = (cs[j]!).toGF216 - (cs[j + 1]!).toGF216 * d.toGF216)
    (h_same : ∀ j, ¬(s ≤ j + 1 ∧ j + 1 < cs.length) → rs[j]? = cs[j]?) :
    listToGF216Poly rs =
      listToGF216Poly cs - C d.toGF216 * X ^ (s - 1) * listToGF216Poly (cs.drop s) := by
  ext m
  rw [coeff_sub, listToGF216Poly_coeff, listToGF216Poly_coeff,
      show C d.toGF216 * X ^ (s - 1) * listToGF216Poly (cs.drop s) =
        C d.toGF216 * (listToGF216Poly (cs.drop s) * X ^ (s - 1)) by ring,
      coeff_C_mul, coeff_mul_X_pow']
  by_cases hm : m < cs.length
  · rw [dif_pos (show m < rs.length by omega), dif_pos hm]
    by_cases hs : s - 1 ≤ m
    · rw [if_pos hs, listToGF216Poly_coeff]
      by_cases hd : m - (s - 1) < (cs.drop s).length
      · rw [dif_pos hd]
        have h2 : m + 1 < cs.length := by rw [List.length_drop] at hd; omega
        have hmod := h_mod m (by omega) h2 (by omega)
        simp only [List.get_eq_getElem] at hmod ⊢
        rw [hmod, getElem!_pos cs m hm, getElem!_pos cs (m + 1) h2]
        have h_drop := list_get_drop_eq cs s (m - (s - 1)) hd
        simp only [List.get_eq_getElem] at h_drop
        rw [h_drop]; simp only [show s + (m - (s - 1)) = m + 1 from by omega]; ring
      · rw [dif_neg hd, mul_zero, sub_zero]
        have h_not : ¬(s ≤ m + 1 ∧ m + 1 < cs.length) := by
          rw [List.length_drop] at hd; push Not at hd ⊢; intro h1; omega
        exact congr_arg GF16.toGF216
          (list_get_of_getElem?_eq (h_same m h_not) (by omega) hm)
    · rw [if_neg hs, mul_zero, sub_zero]
      exact congr_arg GF16.toGF216
        (list_get_of_getElem?_eq (h_same m (by push Not; intro h1; omega)) (by omega) hm)
  · push Not at hm
    rw [dif_neg (by omega), dif_neg (by omega)]
    by_cases hs : s - 1 ≤ m
    · rw [if_pos hs, listToGF216Poly_coeff,
          dif_neg (by rw [List.length_drop]; omega), mul_zero]; ring
    · rw [if_neg hs]; ring

end spqr.encoding.polynomial
