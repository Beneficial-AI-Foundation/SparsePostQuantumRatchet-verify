/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong, Lacramioara Astefanoaei
-/
import Spqr.Specs.Aeneas.SliceIter
import Spqr.Specs.Encoding.Polynomial.PolyConst.ToPoly

/-!
# Spec theorem for `spqr::encoding::polynomial::const_polys_to_polys`

`const_polys_to_polys` maps a fixed-size array `[PolyConst<N>; N]` into a
`Vec<Poly>` via a `while i < N` loop pushing `cps[i].to_poly()`. This is a pure
element-wise map: each output element is `PolyConst.to_poly` of the input, a
verbatim coefficient copy that preserves the `GF216[X]` interpretation. It is
used in `from_complete_points` to convert the `COMPLETE_POINTS_POLYS_N` arrays
into the `Vec<Poly>` expected by `Poly.lagrange_sum`.

**Source**: spqr/src/encoding/polynomial.rs -/

open Aeneas Aeneas.Std Result

namespace spqr.encoding.polynomial.const_polys_to_polys_loop

/-- **Spec theorem for `encoding.polynomial.const_polys_to_polys_loop.body`**:

One step of the loop. If `i < N`, pushes `cps[i].to_poly()` onto `polys` and increments `i`;
otherwise returns `polys` unchanged. -/
@[step]
theorem body_spec {N : Usize} (cps : Array (PolyConst N) N)
    (polys : alloc.vec.Vec Poly) (i : Usize) (h_len : polys.length = i.val) :
    body cps polys i ⦃ cf =>
      match cf with
      | ControlFlow.done polys' => polys' = polys ∧ N.val ≤ i.val
      | ControlFlow.cont (polys1, i1) =>
          i.val < N.val ∧ i1.val = i.val + 1 ∧
          ∃ p : Poly, polys1.val = polys.val ++ [p] ∧
            p.coefficients.val = (cps.val.map (fun c => c.coefficients.val))[i.val]! ⦄ := by
  unfold body
  step*
  have : i.val < cps.val.length := by scalar_tac
  refine ⟨by scalar_tac, by simp [*], p, by simp [*], ?_⟩
  simp [*, List.getElem?_eq_getElem this]

/-- **Spec theorem for `encoding.polynomial.const_polys_to_polys_loop`**:

Starting from `polys` holding the converted coefficients of `cps[0..i]`, the loop terminates
with a vector whose coefficient lists are exactly those of `cps`. Proved via
`loop.spec_decr_nat` with measure `N - i`. -/
@[step]
theorem loop_spec {N : Usize} (cps : Array (PolyConst N) N)
    (polys : alloc.vec.Vec Poly) (i : Usize) (h_le : i.val ≤ N.val)
    (h_pre : polys.val.map (fun p => p.coefficients.val) =
      (cps.val.take i.val).map (fun c => c.coefficients.val)) :
    const_polys_to_polys_loop cps polys i ⦃ (result : alloc.vec.Vec Poly) =>
      result.val.map (fun p => p.coefficients.val) =
        cps.val.map (fun c => c.coefficients.val) ⦄ := by
  unfold const_polys_to_polys_loop
  apply loop.spec_decr_nat
    (measure := fun (q : alloc.vec.Vec Poly × Usize) => N.val - q.2.val)
    (inv := fun (q : alloc.vec.Vec Poly × Usize) =>
      q.2.val ≤ N.val ∧
      q.1.val.map (fun p => p.coefficients.val) =
        (cps.val.take q.2.val).map (fun c => c.coefficients.val))
  · rintro ⟨polys', i'⟩ ⟨h_le', h_inv'⟩
    simp only at h_le' h_inv'
    have h_cps_len : cps.val.length = N.val := by simp
    have h_len : polys'.length = i'.val := by
      have := congrArg List.length h_inv'
      simp only [List.length_map, List.length_take, h_cps_len] at this
      simp [this]; omega
    apply WP.spec_mono (body_spec cps polys' i' h_len)
    rintro (⟨polys1, i1⟩ | r) h
    · obtain ⟨h_lt, h_i1, p, h_p, h_coef⟩ := h
      simp only
      refine ⟨⟨by omega, ?_⟩, by omega⟩
      have h_lt' : i'.val < (cps.val.map (fun c => c.coefficients.val)).length := by simp; omega
      rw [h_p, List.map_append, h_inv', h_i1, List.map_take, List.map_take, List.take_add_one,
        List.getElem?_eq_getElem h_lt']
      simp [h_coef, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h_lt']
    · obtain ⟨rfl, h_ge⟩ := h
      simp only
      have : i'.val = N.val := by omega
      rw [h_inv', this, List.take_of_length_le (by omega)]
  · exact ⟨h_le, h_pre⟩

end spqr.encoding.polynomial.const_polys_to_polys_loop

namespace spqr.encoding.polynomial
/--
**Spec theorem for `encoding.polynomial.const_polys_to_polys`**:

The function always succeeds and, for each index `j < N`:
  - **Length**: `result.val.length = N.val`.
  - **Coefficients**: `result[j].coefficients.val = cps[j].coefficients.val`.
  - **Polynomial identity in `GF216[X]`**:
      `result[j].toGF216Poly = listToGF216Poly cps[j].coefficients.val`. -/
@[step]
theorem const_polys_to_polys_spec {N : Usize} (cps : Array (PolyConst N) N) :
    const_polys_to_polys cps ⦃ (result : alloc.vec.Vec Poly) =>
      result.length = N.val ∧
      (∀ j < N.val,
        ∀ (hj : j < result.length) (hjc : j < cps.length),
          result[j].coefficients.val = cps[j].coefficients ∧
          result[j].toGF216Poly = listToGF216Poly cps[j].coefficients) ⦄ := by
  unfold const_polys_to_polys
  apply WP.spec_mono (const_polys_to_polys_loop.loop_spec cps _ 0#usize (by simp)
    (by simp [alloc.vec.Vec.with_capacity]))
  intro result h_map
  have h_len := congrArg List.length h_map
  simp only [List.length_map] at h_len
  refine ⟨by simp [h_len], fun j _ hj hjc => ?_⟩
  have h_j := List.getElem_of_eq h_map (by simpa using hj)
  simp only [List.getElem_map] at h_j
  have h_coef : result[j].coefficients.val = cps[j].coefficients.val := by
    exact h_j
  exact ⟨h_coef, by rw [Poly.toGF216Poly, h_coef]⟩

end spqr.encoding.polynomial
