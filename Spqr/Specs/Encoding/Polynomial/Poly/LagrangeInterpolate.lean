/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

import Spqr.Specs.Encoding.Polynomial.Poly.Clone
import Spqr.Specs.Encoding.Polynomial.Poly.LagrangeInterpolatePrepare
import Spqr.Specs.Encoding.Polynomial.Poly.LagrangeInterpolateComplete
public import Spqr.Math.Poly.Eval
public import Spqr.Math.Poly.Lagrange.InterpolantSum
public import SrcTranslated.Funs
import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Tactic.ComputeDegree
import Spqr.Math.Poly.LinearFactors.Degree
import Spqr.Specs.Encoding.Polynomial.Poly.AddAssign
import Spqr.Specs.Encoding.Polynomial.Poly.Zero
import Spqr.Specs.Encoding.Gf.GF16.AddAssign
import Spqr.Specs.Encoding.Polynomial.Poly.Serialize
import Spqr.Specs.Aeneas.RangeIteratorNext
import Spqr.Specs.Aeneas.VecExtendFromSlice
import Spqr.Math.Poly.Identities.Basic
import Spqr.Math.Poly.CharTwo.ToGF216
import Spqr.Math.Poly.Coeff.Basic

/-! # Spec theorem for `lagrange_interpolate`: loop body 1

One step of the inner loop `out.coefficients[j] += working.coefficients[j + 1]`.
The body retrieves the next index `j`; if exhausted returns `done (v, working)` unchanged,
otherwise performs the GF(2¹⁶) addition and returns `cont (iter1, v1)`.

**Source**: spqr/src/encoding/polynomial.rs -/

@[expose] public section

open Aeneas Aeneas.Std Result  spqr.encoding.gf Polynomial

namespace spqr.encoding.polynomial.Poly.lagrange_interpolate_loop0_loop0
/-- **Spec theorem for `encoding.polynomial.Poly.lagrange_interpolate_loop0_loop0.body`**:

One step of the inner accumulation `v[j] += working.coefficients[j+1]`.

• `done`: `v` and `working` unchanged, `¬ (iter.start < iter.end)`.
• `cont`: iterator advances by 1, `v` length preserved, position `j` updated with
  `v1[j].toGF216 = v[j].toGF216 + working.coefficients[j+1].toGF216`,
  all other positions unchanged.

Preconditions: `iter.end ≤ v.length` and `iter.end < working.coefficients.length`. -/
@[step]
theorem body_spec
    (working : Poly)
    (iter : core.ops.range.Range Usize)
    (v : alloc.vec.Vec GF16)
    (h_end_le_v : iter.end ≤ v.length)
    (h_end_lt_working : iter.end < working.degree) :
    body working iter v ⦃ cf =>
      match cf with
      | ControlFlow.done (v', working') => v' = v ∧ working' = working ∧ ¬ (iter.start < iter.end)
      | ControlFlow.cont (iter1, v1) =>
          iter.start < iter.end ∧
          iter1.start = iter.start.val + 1 ∧
          iter1.end = iter.end ∧
          v1.val.length = v.length ∧
          v1[iter.start]!.toGF216 = v[iter.start]!.toGF216 +
            (working.coefficients[iter.start.val + 1]!).toGF216 ∧
          (∀ (k : Nat), k ≠ iter.start → v1[k]! = v[k]!) ⦄ := by
  unfold body
  step with core.iter.range.IteratorRange.next_Usize_spec' iter as
    ⟨opt, iter1', h_none, h_some⟩
  by_cases h_lt : iter.start.val < iter.end.val
  · obtain ⟨h_opt_eq, h_start1, h_end1⟩ := h_some h_lt
    rw [h_opt_eq]
    have h_end_v : iter.end.val ≤ v.val.length := h_end_le_v
    have h_end_w : iter.end.val < working.coefficients.val.length := h_end_lt_working
    have h_j_lt_v : iter.start.val < v.val.length := by omega
    step as ⟨g, index_mut_back, h_g, h_imb⟩
    step as ⟨i, h_i⟩
    step as ⟨g1, h_g1⟩
    step as ⟨g2, h_g2⟩
    have h_set : (index_mut_back g2).val = v.val.set iter.start.val g2 := by
      rw [h_imb, alloc.vec.Vec.set_val_eq]
    have h_vg : v[iter.start]! = g := by
      rw [alloc.vec.Vec.getElem!_Usize_eq, h_g, getElem!_pos v.val _ h_j_lt_v]
    have h_wg : working.coefficients[iter.start.val + 1]! = g1 := by
      rw [alloc.vec.Vec.getElem!_Nat_eq, h_g1, ← h_i, getElem!_pos _ _ (by omega)]
    refine ⟨h_lt, h_start1, h_end1, by rw [h_set, List.length_set], ?_, fun k hk => ?_⟩
    · rw [h_vg, h_wg, ← h_g2, alloc.vec.Vec.getElem!_Usize_eq, h_set,
        List.getElem!_eq_getElem?_getD, List.getElem?_set_self h_j_lt_v]
      rfl
    · rw [alloc.vec.Vec.getElem!_Nat_eq, alloc.vec.Vec.getElem!_Nat_eq, h_set,
        List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD,
        List.getElem?_set_ne (Ne.symm hk)]
  · obtain ⟨h_opt_eq, rfl⟩ := h_none h_lt
    rw [h_opt_eq]
    exact (WP.spec_ok _).mpr ⟨rfl, rfl, h_lt⟩

/-! # Spec theorem for `lagrange_interpolate`: loop 1

Full inner loop executing `out.coefficients[j] += working.coefficients[j+1]` for all
`j ∈ 0..out.coefficients.len()`. Provides a closed-form postcondition over all iterations.
Per-step spec is in `LagrangeInterpolateLoop1`.

**Source**: spqr/src/encoding/polynomial.rs -/
@[step]
theorem loop_spec
    (working : Poly) (iter : core.ops.range.Range Usize) (v : alloc.vec.Vec GF16)
    (h_end_le_v : iter.end ≤ v.length)
    (h_end_lt_working : iter.end < working.degree)
    (h_le : iter.start ≤ iter.end) :
    Poly.lagrange_interpolate_loop0_loop0 iter v working ⦃ (result : (alloc.vec.Vec GF16) × Poly) =>
      result.2 = working ∧
      result.1.length = v.length ∧
      (∀ (j : Nat), iter.start ≤ j → j < iter.end →
          result.1[j]!.toGF216 = v[j]!.toGF216 + (working.coefficients[j + 1]!).toGF216) ∧
      (∀ (j : Nat), ¬(iter.start ≤ j ∧ j < iter.end) → result.1[j]! = v[j]!) ⦄ := by
  unfold Poly.lagrange_interpolate_loop0_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : core.ops.range.Range Usize × alloc.vec.Vec GF16) => p.1.end - p.1.start)
    (inv := fun (p : core.ops.range.Range Usize × alloc.vec.Vec GF16) =>
        p.1.end = iter.end ∧
        iter.start ≤ p.1.start ∧
        p.1.start ≤ iter.end ∧
        p.2.length = v.length ∧
        (∀ (j : Nat), iter.start ≤ j → j < p.1.start →
            p.2[j]!.toGF216 = v[j]!.toGF216 + working.coefficients[j + 1]!.toGF216) ∧
        (∀ (j : Nat), ¬(iter.start ≤ j ∧ j < p.1.start) → p.2[j]! = v[j]!))
  · rintro ⟨iter', v'⟩ hinv
    dsimp only at hinv
    obtain ⟨h_end', h_ge', h_le', h_len', h_processed, h_unchanged⟩ := hinv
    have h_end_val : iter'.end.val = iter.end.val := by rw [h_end']
    have h_ge'' : iter.start.val ≤ iter'.start.val := h_ge'
    have h_le'' : iter'.start.val ≤ iter.end.val := h_le'
    apply WP.spec_mono (body_spec working iter' v'
      (show iter'.end.val ≤ v'.length by rw [h_len', h_end_val]; exact h_end_le_v)
      (show iter'.end.val < working.degree by rw [h_end_val]; exact h_end_lt_working))
    rintro (⟨iter'', v''⟩ | ⟨v'', w''⟩) h_cf
    · obtain ⟨h_lt, h_start1, h_end1, h_len1, h_upd, h_keep⟩ := h_cf
      have h_lt' : iter'.start.val < iter'.end.val := h_lt
      have h_end1' : iter''.end.val = iter'.end.val := by rw [h_end1]
      dsimp only
      refine ⟨⟨h_end1.trans h_end', show iter.start.val ≤ iter''.start.val by omega,
        show iter''.start.val ≤ iter.end.val by omega, h_len1.trans h_len', fun j hj1 hj2 => ?_,
        fun j hj => ?_⟩, show iter''.end.val - iter''.start.val < iter'.end.val - iter'.start.val
          by omega⟩
      · by_cases hj : j < iter'.start.val
        · rw [h_keep j (by omega)]
          exact h_processed j hj1 hj
        · obtain rfl : j = iter'.start.val := by omega
          rw [alloc.vec.Vec.getElem!_Usize_eq, alloc.vec.Vec.getElem!_Usize_eq,
            ← alloc.vec.Vec.getElem!_Nat_eq, ← alloc.vec.Vec.getElem!_Nat_eq] at h_upd
          rw [h_upd, h_unchanged _ (by omega)]
      · rw [h_keep j (by omega)]
        exact h_unchanged j (by omega)
    · obtain ⟨rfl, rfl, h_nlt⟩ := h_cf
      have h_nlt' : ¬iter'.start.val < iter'.end.val := h_nlt
      have h_eq : iter'.start.val = iter.end.val := by omega
      refine ⟨rfl, h_len', fun j hj1 hj2 => h_processed j hj1 (by omega),
        fun j hj => h_unchanged j (by omega)⟩
  · exact ⟨rfl, le_refl _, h_le, rfl, fun j hj1 hj2 => absurd hj2 (by dsimp only; omega),
      fun j _ => rfl⟩

end spqr.encoding.polynomial.Poly.lagrange_interpolate_loop0_loop0

/-! # Spec theorem for `lagrange_interpolate`: loop body 0

One step of the outer loop: resets `working` from `template`, calls
`lagrange_interpolate_complete` for the `i`-th point, then XOR-adds
`working.coefficients[j+1]` into `out.coefficients[j]` via the inner loop.

**Source**: spqr/src/encoding/polynomial.rs -/

namespace spqr.encoding.polynomial.Poly.lagrange_interpolate_loop0

/-- **Spec theorem for `encoding.polynomial.Poly.lagrange_interpolate_loop0.body`**:

One step of the outer loop processing point index `i = iter.start.val`.

• `done`: `v` unchanged, `¬ (iter.start < iter.end)`.
• `cont`: iterator advances by 1, `v₂.length = v.length`,
  `working₂.coefficients.length = template.coefficients.length`,
  `working₂` satisfies `working₂.toGF216Poly · (X − C(pts[i].x)) =
    X · C(lagrangeScaleGF216 pts[i] pts) · template.toGF216Poly`,
  and `v₂[j].toGF216 = v[j].toGF216 + working₂.coefficients[j+1].toGF216` for all `j`.

Preconditions: `iter.end ≤ pts.length`, `0 < template.coefficients.length`,
`v.length < template.coefficients.length`, matching template/working lengths,
and `template.evalAt pts[i].x = 0` when the iterator is active. -/
@[step]
theorem body_spec
    (pts : Slice Pt) (template : Poly) (iter : core.ops.range.Range Usize)
    (v : alloc.vec.Vec GF16) (working : Poly)
    (h_end_le_pts : iter.end ≤ pts.length)
    (h_template_pos : 0 < template.degree)
    (h_v_lt : v.val.length < template.degree)
    (h_wt : template.degree = working.degree)
    (h_eval : iter.start < iter.end →
        ∀ (_ : iter.start < pts.length),
          template.evalAt (pts[iter.start]!).x = 0) :
    body pts template iter v working ⦃ cf =>
      match cf with
      | ControlFlow.done v' => v' = v ∧ ¬ (iter.start < iter.end)
      | ControlFlow.cont (iter1, v₂, working₂) =>
          iter.start < iter.end ∧
          iter1.start = iter.start.val + 1 ∧
          iter1.end = iter.end ∧
          v₂.length = v.length ∧
          working₂.degree = template.degree ∧
          (∀ (hi : iter.start < pts.length),
            working₂.toGF216Poly * (X - C (GF16.toGF216 (pts[iter.start]).x)) =
              X * C (lagrangeScaleGF216 (pts[iter.start]) pts) * template.toGF216Poly) ∧
          (∀ j < v₂.length,
            (v₂[j]!).toGF216 = (v[j]!).toGF216 + (working₂.coefficients[j + 1]!).toGF216) ⦄ := by
  unfold body
  step with core.iter.range.IteratorRange.next_Usize_spec' iter as
    ⟨opt, iter1', h_none, h_some⟩
  by_cases h_lt : iter.start < iter.end
  · obtain ⟨h_opt_eq, h_start1, h_end1⟩ := h_some h_lt
    rw [h_opt_eq]
    have hW : ({coefficients := {slice := template.coefficients.deref}} : Poly) = template := by
      obtain ⟨⟨s⟩⟩ := template
      simp [alloc.vec.Vec.deref, alloc.vec.Vec.val]
    simp only [lift, bind_ok, alloc.vec.Vec.deref_mut]
    have h_lt' : iter.start.val < iter.end.val := h_lt
    have h_end_pts : iter.end.val ≤ pts.val.length := h_end_le_pts
    have hi : iter.start.val < pts.val.length := by omega
    step as ⟨s2, h_s2⟩
    · simpa [degree, alloc.vec.Vec.deref, alloc.vec.Vec.val] using h_wt.symm
    rw [h_s2, hW]
    step with lagrange_interpolate_complete_spec template pts iter.start hi h_template_pos
      (h_eval h_lt hi) as ⟨working1, h_w1_len, h_w1_id⟩
    step with lagrange_interpolate_loop0_loop0.loop_spec as ⟨v2, w2, h_w2, h_len2, h_proc, _⟩
    subst h_w2
    have hpi : pts[iter.start] = pts[iter.start]! := by
      rw [Slice.getElem!_Usize_eq, getElem!_pos pts.val iter.start.val hi]
      rfl
    have h_vlen : (alloc.vec.Vec.len v).val = v.length := alloc.vec.Vec.len_val v
    refine ⟨h_lt, h_start1, h_end1, h_len2, h_w1_len, fun _ => hpi ▸ h_w1_id,
      fun j hj => h_proc j (Nat.zero_le _) (by omega)⟩
  · obtain ⟨h_opt_eq, rfl⟩ := h_none h_lt
    rw [h_opt_eq]
    exact (WP.spec_ok _).mpr ⟨rfl, h_lt⟩

/-! # Spec theorem for `lagrange_interpolate`: loop 0

Full outer loop over `iter.start..iter.end`. At each iteration: resets `working` from `template`,
calls `lagrange_interpolate_complete`, and XOR-adds contributions into `out`.

Postcondition: length preserved, and there exist witness polynomials `ws` (one per iteration)
satisfying the Lagrange polynomial identity and cumulative XOR-accumulation of coefficients
at positions `j+1` (the "divide by X" trick).

**Source**: spqr/src/encoding/polynomial.rs -/
@[step]
theorem loop_spec
    (pts : Slice Pt) (template : Poly) (iter : core.ops.range.Range Usize)
    (v : alloc.vec.Vec GF16) (working : Poly)
    (h_end_le_pts : iter.end ≤ pts.length)
    (h_template_pos : 0 < template.degree)
    (h_v_lt : v.length < template.degree)
    (h_wt : template.degree = working.degree)
    (h_le : iter.start ≤ iter.end)
    (h_eval_all : ∀ (i : Nat), iter.start ≤ i → i < iter.end → template.evalAt (pts[i]!).x = 0) :
    Poly.lagrange_interpolate_loop0 iter pts v template working ⦃ (result : alloc.vec.Vec GF16) =>
      result.length = v.length ∧
      ∃ ws : List Poly,
        ws.length = iter.end - iter.start ∧
        (∀ (k : Nat) (hk : k < ws.length) (hi : iter.start + k < pts.length),
          (ws[k]).toGF216Poly * (X - C (GF16.toGF216 (pts[iter.start + k]).x)) =
            X * C (lagrangeScaleGF216 (pts[iter.start + k]) pts.val) * template.toGF216Poly) ∧
        (∀ (j : Nat) (_ : j < result.length),
          (result.val[j]!).toGF216 =
            (v[j]!).toGF216 + (ws.map (fun w => (w.coefficients[j + 1]!).toGF216)).sum) ⦄ := by
  unfold Poly.lagrange_interpolate_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : core.ops.range.Range Usize × alloc.vec.Vec GF16 × Poly) =>
                  p.1.end - p.1.start)
    (inv := fun (p : core.ops.range.Range Usize × alloc.vec.Vec GF16 × Poly) =>
        p.1.end = iter.end ∧
        iter.start ≤ p.1.start ∧
        p.1.start ≤ iter.end ∧
        p.2.1.length = v.length ∧
        p.2.2.degree = template.degree ∧
        ∃ ws : List Poly,
          ws.length = p.1.start - iter.start ∧
          (∀ (k : Nat) (hk : k < ws.length) (hi : iter.start + k < pts.length),
            (ws[k]!).toGF216Poly * (X - C (GF16.toGF216 (pts[iter.start + k]!).x)) =
              X * C (lagrangeScaleGF216 (pts[iter.start + k]!) pts) * template.toGF216Poly) ∧
          (∀ (j : Nat) (hj : j < p.2.1.length),
            (p.2.1[j]!).toGF216 = (v[j]!).toGF216 +
            (ws.map (fun w => (w.coefficients[j + 1]!).toGF216)).sum))
  · rintro ⟨iter', v', working'⟩ hinv
    dsimp only at hinv
    obtain ⟨h_end', h_ge', h_le', h_len', h_wt', ws, h_ws_len, h_ws_id, h_ws_sum⟩ := hinv
    have h_end_val : iter'.end.val = iter.end.val := by rw [h_end']
    have h_ge'' : iter.start.val ≤ iter'.start.val := h_ge'
    have h_le'' : iter'.start.val ≤ iter.end.val := h_le'
    have h_end_pts : iter.end.val ≤ pts.length := h_end_le_pts
    apply WP.spec_mono (body_spec pts template iter' v' working'
      (show iter'.end.val ≤ pts.length by omega) h_template_pos
      (show v'.length < template.degree by rw [h_len']; exact h_v_lt) (h_wt'.symm)
      (fun h_lt _ => h_eval_all iter'.start.val h_ge''
        (by have : iter'.start.val < iter'.end.val := h_lt; omega)))
    rintro (⟨iter'', v'', w''⟩ | v'') h_cf
    · obtain ⟨h_lt, h_start1, h_end1, h_v2len, h_w2len, h_poly_id, h_coord⟩ := h_cf
      have h_lt' : iter'.start.val < iter'.end.val := h_lt
      have h_end1' : iter''.end.val = iter'.end.val := by rw [h_end1]
      dsimp only
      refine ⟨⟨h_end1.trans h_end', show iter.start.val ≤ iter''.start.val by omega,
        show iter''.start.val ≤ iter.end.val by omega, h_v2len.trans h_len', h_w2len,
        ws ++ [w''], by rw [List.length_append, List.length_singleton, h_ws_len]; omega,
        fun k hk hi => ?_, fun j hj => ?_⟩,
        show iter''.end.val - iter''.start.val < iter'.end.val - iter'.start.val by omega⟩
      · rw [List.length_append, List.length_singleton] at hk
        by_cases hk' : k < ws.length
        · rw [List.getElem!_append_left _ _ _ hk']
          exact h_ws_id k hk' hi
        · obtain rfl : k = ws.length := by omega
          have hi' : iter'.start.val < pts.length := by omega
          have hpi : pts[iter'.start] = pts[iter.start.val + ws.length]! := by
            rw [Slice.getElem!_Nat_eq, show iter.start.val + ws.length = iter'.start.val by omega,
              getElem!_pos pts.val _ hi']
            rfl
          rw [List.getElem!_append_right _ _ _ (le_refl _), Nat.sub_self,
            List.getElem!_cons_zero, ← hpi]
          exact h_poly_id hi'
      · have hj' : j < v'.length := by rw [h_v2len] at hj; exact hj
        rw [h_coord j hj, h_ws_sum j hj', List.map_append, List.sum_append, List.map_singleton,
          List.sum_singleton, add_assoc]
    · obtain ⟨rfl, h_nlt⟩ := h_cf
      have h_nlt' : ¬iter'.start.val < iter'.end.val := h_nlt
      have h_eq : iter'.start.val = iter.end.val := by omega
      refine ⟨h_len', ws, by omega, fun k hk hi => ?_, h_ws_sum⟩
      have hpi : pts[iter.start.val + k] = pts[iter.start.val + k]! := by
        rw [Slice.getElem!_Nat_eq, getElem!_pos pts.val _ hi]
        rfl
      rw [hpi, ← getElem!_pos ws k hk]
      exact h_ws_id k hk hi
  · exact ⟨rfl, le_refl _, h_le, rfl, h_wt.symm, [], (Nat.sub_self _).symm,
      fun k hk => absurd hk (Nat.not_lt_zero _),
      fun j _ => by rw [List.map_nil, List.sum_nil, add_zero]⟩

end spqr.encoding.polynomial.Poly.lagrange_interpolate_loop0

/-! # Spec theorem for
`spqr::encoding::polynomial::{spqr::encoding::polynomial::Poly}::lagrange_interpolate`

Computes the unique polynomial of degree `< pts.len()` over GF(2¹⁶) interpolating `pts`.
Prepares `template = ∏_j (X − pts[j].x)`, then for each point index `i`, calls
`lagrange_interpolate_complete` and XOR-accumulates `working.coefficients[j+1]` into
`out.coefficients[j]` (the "divide by X" trick). The result is the classical Lagrange interpolant.

**Source**: spqr/src/encoding/polynomial.rs -/

namespace spqr.encoding.polynomial.Poly

private lemma slice_is_empty_spec {T : Type} (s : Slice T) :
    core.slice.Slice.is_empty s ⦃ (b : Bool) =>
      b = (s.val.length = 0) ⦄ := by
  unfold core.slice.Slice.is_empty
  simp only [WP.spec_ok]
  rcases h : s.val.length with _ | n
  all_goals simp [h]

theorem lagrange_interpolate_formula
    (pts : Slice Pt)
    (h_len : pts.length + 1 ≤ Usize.max) :
    lagrange_interpolate pts ⦃ (result : Poly) =>
      result.degree = pts.length ∧
      (pts.length = 0 → result.toGF216Poly = 0) ∧
      (0 < pts.length →
        ∃ ws : List Poly,
          ws.length = pts.length ∧
          (∀ (i : Nat) (hi : i < ws.length) (hpi : i < pts.length),
            (ws[i]).toGF216Poly * (X - C (GF16.toGF216 (pts[i]).x)) =
              X * C (lagrangeScaleGF216 (pts[i]) pts) * (prodLinearFactors pts 0 pts.length)) ∧
          (∀ (j : Nat) (_ : j < result.degree),
            (result.coefficients.val[j]!).toGF216 =
            (ws.map (fun w => (w.coefficients.val[j + 1]!).toGF216)).sum)) ⦄ := by
  unfold lagrange_interpolate
  step with zero_spec pts.len as ⟨out, h_out_len, h_out_zero⟩
  step with slice_is_empty_spec pts as ⟨b, hb_eq⟩
  split
  next hb_true =>
    have h0 : pts.length = 0 := cast hb_eq hb_true
    refine (WP.spec_ok _).mpr ⟨?_, fun _ => h_out_zero, fun h => absurd h (by omega)⟩
    change out.coefficients.val.length = pts.val.length
    rw [h_out_len]
    exact h0.symm
  next hb_false =>
    have h_nonempty : 0 < pts.val.length :=
      Nat.pos_of_ne_zero fun h => hb_false (cast hb_eq.symm h)
    step with lagrange_interpolate_prepare_spec pts h_len as
      ⟨template, h_template_len, _, _,  h_template_eq⟩
    step with clone_spec template as ⟨working, h_working_eq⟩
    rw [h_working_eq]
    have h_root : ∀ i, i < pts.val.length → template.evalAt (pts[i]!).x = 0 := by
      intro i hi
      unfold Poly.evalAt
      rw [h_template_eq, Slice.getElem!_Nat_eq]
      exact prodLinearFactors_eval_root pts.val 0 pts.val.length i (Nat.zero_le _) hi hi
    have h_tdeg : template.coefficients.val.length = pts.val.length + 1 := h_template_len
    step with lagrange_interpolate_complete_spec template pts 0#usize
      h_nonempty (show 0 < template.coefficients.val.length by omega) (h_root 0 h_nonempty) as
      ⟨working1, h_w1_len, h_w1_id⟩
    have h_w1deg : working1.coefficients.val.length = pts.val.length + 1 := by
      change working1.coefficients.val.length = template.coefficients.val.length at h_w1_len
      omega
    step as ⟨s0, h_s0⟩
    step as ⟨s, h_s_val, h_s_len⟩
    rw [h_s0] at h_s_val
    have h_s_len' : s.val.length = pts.val.length := by
      rw [h_s_val, List.length_drop]; omega
    have h_out0 : out.coefficients.val = [] := List.length_eq_zero_iff.mp h_out_len
    have h_plen : pts.val.length + 1 ≤ Usize.max := h_len
    step with alloc.vec.Vec.extend_from_slice_GF16_spec out.coefficients s
      (show out.coefficients.val.length + s.val.length ≤ Usize.max by omega) as ⟨v, h_v_val⟩
    have h_v_val' : v.val = s.val := by rw [h_v_val, h_out0, List.nil_append]
    have h_v_len : v.val.length = pts.val.length := by rw [h_v_val', h_s_len']
    have h_v_coeff : ∀ (j : Nat), j < v.val.length →
        v[j]! = working1.coefficients.val[j + 1]! := by
      intro j hj
      rw [alloc.vec.Vec.getElem!_Nat_eq, h_v_val', h_s_val,
        getElem!_pos _ _ (by rw [List.length_drop]; omega), getElem!_pos _ _ (by omega),
        List.getElem_drop]
      congr 1
      omega
    have h_end : (Slice.len pts).val = pts.val.length := Slice.len_val pts
    step with lagrange_interpolate_loop0.loop_spec pts template
      ({ start := 1#usize, «end» := Slice.len pts } : core.ops.range.Range Usize)
      v working1 (le_of_eq h_end) (show 0 < template.coefficients.val.length by omega)
      (show v.val.length < template.coefficients.val.length by omega) (h_w1_len.symm)
      (show 1 ≤ (Slice.len pts).val by omega)
      (fun i _ hi => h_root i (by dsimp only at hi; omega)) as
      ⟨v1, h_v1_len, ws', h_ws'_len, h_ws'_id, h_v1_coeff⟩
    have h_v1_pts_len : v1.val.length = pts.val.length := h_v1_len.trans h_v_len
    have h_ne : pts.length ≠ 0 := by change pts.val.length ≠ 0; omega
    refine ⟨h_v1_pts_len, fun h => absurd h h_ne, fun _ => ⟨working1 :: ws', ?_, ?_, ?_⟩⟩
    · change ws'.length + 1 = pts.val.length
      omega
    · intro i hi hpi
      rw [← h_template_eq]
      cases i with
      | zero =>
        have hp : pts[(0 : Nat)] = pts[0#usize]! := by
          rw [Slice.getElem!_Usize_eq, show (0#usize).val = 0 from rfl,
            getElem!_pos pts.val 0 hpi]
          rfl
        rw [List.getElem_cons_zero, hp]
        exact h_w1_id
      | succ k =>
        rw [List.length_cons] at hi
        have := h_ws'_id k (by omega) (by omega)
        simp only [Nat.add_comm 1 k] at this
        exact this
    · intro j hj
      have hj' : j < v1.val.length := hj
      rw [h_v1_coeff j hj', h_v_coeff j (by omega), List.map_cons, List.sum_cons]
      simp only [alloc.vec.Vec.getElem!_Nat_eq]

/-- **Spec theorem for `spqr.encoding.polynomial.Poly.lagrange_interpolate`**:

Returns `result` with `result.coefficients.length = pts.length`. When empty, `result = 0`.
Otherwise, witness polynomials `ws` exist (one per point) satisfying the Lagrange polynomial
identity and `result.coefficients[j] = ∑_i ws[i].coefficients[j+1]` in GF(2¹⁶),
recovering the classical Lagrange interpolation formula.

**Source**: spqr/src/encoding/polynomial.rs -/
@[step]
theorem lagrange_interpolate_spec
    (pts : Slice Pt)
    (h_len : pts.length + 1 ≤ Usize.max) :
    lagrange_interpolate pts ⦃ (result : Poly) =>
      result.degree = pts.length ∧
      (pts.length = 0 → result.toGF216Poly = 0) ∧
      result.toGF216Poly = lagrangeInterpolantSum pts pts.length ⦄ := by
  apply WP.spec_mono (lagrange_interpolate_formula pts h_len)
  intro result ⟨h_rlen, h_empty, h_nonempty⟩
  refine ⟨h_rlen, h_empty, ?_⟩
  set n := pts.length with hn_def
  by_cases h0 : n = 0
  · rw [h_empty h0, h0]
    rfl
  · have hpos : 0 < n := Nat.pos_of_ne_zero h0
    obtain ⟨ws, hws_len, hws_id, hws_coeff⟩ := h_nonempty hpos
    have hws_poly : ∀ (i : Nat) (hi : i < ws.length) (hpi : i < n),
        (ws[i]!).toGF216Poly =
          X * C (lagrangeScaleGF216 (pts[i]!) pts) * lagrangeBasisPoly pts i := by
      intro i hi hpi
      have h_id := hws_id i hi hpi
      rw [prodLinearFactors_eq_X_sub_C_mul pts.val i hpi,
          show prodLinearFactors pts.val 0 i *
              prodLinearFactors pts.val (i + 1) pts.val.length =
              lagrangeBasisPoly pts.val i from by
            unfold lagrangeBasisPoly; rw [if_pos hpi]] at h_id
      have hne : (X : GF216[X]) - C (GF16.toGF216 (pts.val.get ⟨i, hpi⟩).x) ≠ 0 :=
        (Polynomial.monic_X_sub_C _).ne_zero
      have hp : pts[i]! = pts.val.get ⟨i, hpi⟩ := by
        rw [Slice.getElem!_Nat_eq, getElem!_pos pts.val i hpi, List.get_eq_getElem]
      apply mul_right_cancel₀ hne
      rw [getElem!_pos ws i hi, hp]
      change ws[i].toGF216Poly * (X - C (GF16.toGF216 (pts.val.get ⟨i, hpi⟩).x)) =
        X * C (lagrangeScaleGF216 (pts.val.get ⟨i, hpi⟩) pts.val) *
        ((X - C (GF16.toGF216 (pts.val.get ⟨i, hpi⟩).x)) * lagrangeBasisPoly pts.val i) at h_id
      rw [h_id]
      ring
    have h_term_eq : ∀ (m : ℕ) (i : Fin ws.length),
        ((ws.get i).coefficients.val[m + 1]!).toGF216 =
          (C (lagrangeScaleGF216 (pts[i]!) pts.val) * lagrangeBasisPoly pts i).coeff m := by
      intro m ⟨i, hi⟩
      rw [getElem!_toGF216_eq_coeff]
      change (ws.get ⟨i, hi⟩ ).toGF216Poly.coeff (m + 1) = _
      rw [List.get_eq_getElem, ← getElem!_pos ws i hi, hws_poly i hi (by omega), mul_assoc,
        Polynomial.coeff_X_mul]
      rfl
    unfold Poly.toGF216Poly
    ext m
    rw [listToGF216Poly_coeff]
    by_cases hm : m < result.degree
    · rw [degree] at hm
      have : (result.coefficients.val).get ⟨m, hm⟩ = (result.coefficients.val)[m]! := by
        rw [List.get_eq_getElem, getElem!_pos _ m hm]
      rw [dif_pos hm, this, hws_coeff m hm, List.map_sum_eq_Finset_sum]
      rw [Finset.sum_congr rfl (fun i _ => h_term_eq m i)]
      rw [lagrangeInterpolantSum_eq_finset_sum pts.val n (le_refl _)]
      rw [Polynomial.finsetSum_coeff]
      apply Finset.sum_bij (fun (a : Fin ws.length) _ => a.val)
        (fun a _ => by
          have := a.isLt
          rw [Finset.mem_range]
          change _ < pts.val.length
          change ws.length = pts.val.length at hws_len
          omega)
        (fun a₁ _ a₂ _ h => Fin.val_injective h)
        (fun b hb => by
          rw [Finset.mem_range] at hb
          exact ⟨⟨b, by rw [hws_len]; exact hb⟩, Finset.mem_univ _, rfl⟩)
        (fun a _ => ?_)
      have ha : a.val < pts.val.length := by
        have := a.isLt
        change ws.length = pts.val.length at hws_len
        omega
      change (C (lagrangeScaleGF216 pts[a.val]! pts.val) * _).coeff m = _
      rw [dif_pos ha, Slice.getElem!_Nat_eq, getElem!_pos pts.val a.val ha, List.get_eq_getElem]
    · rw [degree] at hm
      rw [dif_neg hm]
      exact (lagrangeInterpolantSum_coeff_high pts n m (le_refl _)
        (by rw [degree] at h_rlen; rw [h_rlen] at hm; push Not at hm; omega)).symm

end spqr.encoding.polynomial.Poly
