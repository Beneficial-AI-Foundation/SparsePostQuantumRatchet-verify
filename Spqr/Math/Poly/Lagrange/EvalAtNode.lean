/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Alessandro D'Angelo
-/
module

public import Spqr.Math.Gf16.Equiv
public import Spqr.Math.Poly.Lagrange.CompletePoints
import Mathlib.FieldTheory.Finite.Basic

/-!
# Evaluation of the scaled Lagrange basis at the interpolation nodes

`scaledLagrangeBasis N j` takes the value `1` at node `j` and `0` at every other node below `N`.
So the interpolant `∑ k, C (y k) * scaledLagrangeBasis N k` takes the value `y m` at node `m`.
-/

@[expose] public section

open Aeneas Aeneas.Std Polynomial
open spqr.encoding.gf
open spqr.encoding.polynomial.PolyConst.lagrange_interpolate_pt_loop
open spqr.math.gf

namespace spqr.encoding.polynomial

private lemma GF16.toGF216_ne_of_value_ne {a b : GF16} (h : a.value ≠ b.value) :
    a.toGF216 ≠ b.toGF216 := by
  intro hab
  apply h
  apply UScalar.eq_of_val_eq
  unfold GF16.toGF216 at hab
  exact Nat.toGF216_injOn a.value.hBounds b.value.hBounds hab

private theorem eval_condProdLinearFactors_eq_lagrangeDenomProd
    (pi : GF16) (pts : List Pt) (start : Nat) :
    (condProdLinearFactors pi pts start).eval pi.toGF216 =
      lagrangeDenomProd pi pts start := by
  by_cases hstart : start < pts.length
  · by_cases heq : pi.value = (pts[start]).x.value
    · rw [condProdLinearFactors_skip pi pts start hstart heq,
          lagrangeDenomProd_skip pi pts start hstart heq]
      exact eval_condProdLinearFactors_eq_lagrangeDenomProd pi pts (start + 1)
    · rw [condProdLinearFactors_accum pi pts start hstart heq,
          lagrangeDenomProd_accum pi pts start hstart heq,
          eval_mul, eval_sub, eval_X, eval_C,
          eval_condProdLinearFactors_eq_lagrangeDenomProd]
      simp only [List.get_eq_getElem]
  · rw [condProdLinearFactors_ge pi pts start (by omega),
        lagrangeDenomProd_eq_one_of_le pi pts start (by omega), eval_one]
termination_by pts.length - start
decreasing_by all_goals omega

private theorem lagrangeDenomProd_ne_zero
    (pi : GF16) (pts : List Pt) (start : Nat) :
    lagrangeDenomProd pi pts start ≠ 0 := by
  by_cases hstart : start < pts.length
  · by_cases heq : pi.value = (pts[start]).x.value
    · rw [lagrangeDenomProd_skip pi pts start hstart heq]
      exact lagrangeDenomProd_ne_zero pi pts (start + 1)
    · rw [lagrangeDenomProd_accum pi pts start hstart heq]
      exact mul_ne_zero (sub_ne_zero.mpr (GF16.toGF216_ne_of_value_ne heq))
        (lagrangeDenomProd_ne_zero pi pts (start + 1))
  · rw [lagrangeDenomProd_eq_one_of_le pi pts start (by omega)]
    exact one_ne_zero
termination_by pts.length - start
decreasing_by all_goals omega

private theorem eval_condProdLinearFactors_eq_zero_of_value_ne
    (pi : GF16) (pts : List Pt) (start m : Nat)
    (hstart : start ≤ m) (hm : m < pts.length)
    (hne : pi.value ≠ (pts[m]).x.value) :
    (condProdLinearFactors pi pts start).eval (pts[m]).x.toGF216 = 0 := by
  have hstart_lt : start < pts.length := by omega
  by_cases hsm : start = m
  · subst m
    rw [condProdLinearFactors_accum pi pts start hm hne, eval_mul, eval_sub, eval_X, eval_C,
      sub_self, zero_mul]
  · by_cases heq : pi.value = (pts[start]).x.value
    · rw [condProdLinearFactors_skip pi pts start hstart_lt heq]
      exact eval_condProdLinearFactors_eq_zero_of_value_ne pi pts (start + 1) m
        (by omega) hm hne
    · rw [condProdLinearFactors_accum pi pts start hstart_lt heq, eval_mul,
          eval_condProdLinearFactors_eq_zero_of_value_ne pi pts (start + 1) m
            (by omega) hm hne, mul_zero]
termination_by pts.length - start
decreasing_by all_goals omega

private lemma eval_condProdLinearFactors_eq_zero_of_value_ne_bang
    (pi : GF16) (pts : List Pt) (start m : Nat)
    (hstart : start ≤ m) (hm : m < pts.length)
    (hne : pi.value ≠ (pts[m]!).x.value) :
    (condProdLinearFactors pi pts start).eval (pts[m]!).x.toGF216 = 0 := by
  rw [← List.Inhabited_getElem_eq_getElem! pts m hm] at hne ⊢
  exact eval_condProdLinearFactors_eq_zero_of_value_ne pi pts start m hstart hm hne

private lemma completePoints_take (N : Usize) :
    (completePoints N).val.take N.val = (completePoints N).val := by
  apply List.take_of_length_le
  exact (completePoints N).property.le

private lemma completePoints_x_value {N : Usize} (hN : N.val ≤ 2 ^ 16)
    {i : Nat} (hi : i < N.val) :
    ((completePoints N).val[i]!).x.value.val = i := by
  simp only [global_simps, Array.from_val]
  rw [← List.Inhabited_getElem_eq_getElem! _ i
    (by simp only [List.length_map, List.length_finRange]; exact hi)]
  simp only [List.getElem_map, List.getElem_finRange]
  change (BitVec.ofNat 16 i).toNat = i
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_of_lt_of_le hi hN)]

private lemma completePoints_x_toGF216 {N : Usize} (hN : N.val ≤ 2 ^ 16)
    {i : Nat} (hi : i < N.val) :
    ((completePoints N).val[i]!).x.toGF216 = Nat.toGF216 i := by
  unfold GF16.toGF216
  rw [completePoints_x_value hN hi]

private lemma completePoints_y_toGF216 {N : Usize} {i : Nat} (hi : i < N.val) :
    ((completePoints N).val[i]!).y.toGF216 = 1 := by
  simp only [global_simps, Array.from_val]
  simp only [GF16.toGF216, Nat.toGF216, List.length_map, List.length_finRange, hi, getElem!_pos,
    List.getElem_map, List.getElem_finRange, Fin.cast_mk, UScalar.ofNatCore_val_eq,
    natToBinaryPoly_one, map_one]

/-- The scaled Lagrange basis polynomial `j` for the nodes `0, …, N - 1` takes the value `1` at
node `j` and `0` at every other node. -/
theorem scaledLagrangeBasis_eval_node {N : Std.Usize} (hN : N.val ≤ 2 ^ 16)
    {j m : ℕ} (hj : j < N.val) (hm : m < N.val) :
    (scaledLagrangeBasis N j).eval (Nat.toGF216 m) = if j = m then 1 else 0 := by
  classical
  unfold scaledLagrangeBasis
  simp only [Array.getElem!_Nat_eq, completePoints_take, eval_mul, eval_C]
  by_cases hjm : j = m
  · subst m
    rw [ite_eq_left rfl]
    rw [← completePoints_x_toGF216 hN hj,
        eval_condProdLinearFactors_eq_lagrangeDenomProd,
        completePoints_y_toGF216 hj, one_mul]
    let d := lagrangeDenomProd ((completePoints N).val[j]!).x
      (completePoints N).val 0
    have hd : d ≠ 0 := lagrangeDenomProd_ne_zero _ _ _
    calc
      d ^ (2 ^ 16 - 2) * d = d ^ (2 ^ 16 - 2 + 1) := (pow_succ d _).symm
      _ = d ^ (2 ^ 16 - 1) :=
        congrArg (fun n : Nat => d ^ n) (by norm_num)
      _ = 1 := by
        simpa only [GF216.card_eq] using FiniteField.pow_card_sub_one_eq_one d hd
  · rw [ite_eq_right hjm]
    rw [← completePoints_x_toGF216 hN hm]
    have hvalue : ((completePoints N).val[j]!).x.value ≠
        ((completePoints N).val[m]!).x.value := by
      intro h
      have := congrArg UScalar.val h
      rw [completePoints_x_value hN hj, completePoints_x_value hN hm] at this
      exact hjm this
    have hm_pts : m < (completePoints N).val.length := by
      simpa only [(completePoints N).property] using hm
    rw [eval_condProdLinearFactors_eq_zero_of_value_ne_bang _ _ 0 m (by omega)
      hm_pts hvalue, mul_zero]

/-- The interpolant built from the scaled Lagrange basis takes the value `y m` at node `m`. -/
theorem eval_sum_scaledLagrangeBasis_node {N : Std.Usize} (hN : N.val ≤ 2 ^ 16)
    (y : ℕ → GF216) {m : ℕ} (hm : m < N.val) :
    (∑ k ∈ Finset.range N.val, C (y k) * scaledLagrangeBasis N k).eval (Nat.toGF216 m) =
      y m := by
  rw [eval_finsetSum, Finset.sum_eq_single m]
  · rw [eval_mul, eval_C, scaledLagrangeBasis_eval_node hN hm hm, ite_eq_left rfl, mul_one]
  · intro k hk hkm
    rw [eval_mul, eval_C, scaledLagrangeBasis_eval_node hN (Finset.mem_range.mp hk) hm,
      ite_eq_right hkm, mul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr hm) h

end spqr.encoding.polynomial
