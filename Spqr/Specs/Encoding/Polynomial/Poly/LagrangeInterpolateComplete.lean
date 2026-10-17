/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import Spqr.Math.List
import Spqr.Math.Poly.Aeneas.PolyIdentity
import Spqr.Specs.Encoding.Gf.GF16.Sub
import Spqr.Specs.Encoding.Gf.GF16.Div
import Spqr.Specs.Encoding.Gf.GF16.Eq
public import Spqr.Specs.Encoding.Gf.GF16.ZERO
import Spqr.Specs.Encoding.Gf.GF16.ONE
import Spqr.Specs.Encoding.Gf.GF16.AddAssign
public import Spqr.Specs.Aeneas.RangeIteratorNext
public import Spqr.Specs.Aeneas.SliceIteratorNext
import Spqr.Specs.Aeneas.FmtArgumentsFromStr
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Spqr.Math.Poly.Eval
public import Spqr.Math.Poly.Horner.Defs
public import Spqr.Math.Poly.Lagrange.BasisPoly
public import SrcTranslated.Funs
import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Tactic.ComputeDegree
import Spqr.Specs.Encoding.Gf.GF16.Mul
import Spqr.Specs.Encoding.Gf.GF16.MulAssign
import Spqr.Math.Poly.Horner.Eval
import Spqr.Math.Poly.CharTwo.ToGF216
import Spqr.Auxiliary.Aeneas.StdNextStepUsize
/-!
# Spec Theorem for `lagrange_interpolate_complete`: loop body 0

One iteration of the denominator accumulation loop. Retrieves the next point `pj`:
- exhausted → `done` with current `(pi, denominator)`;
- `pi.x = pj.x` → `cont`, denominator unchanged (skip self);
- `pi.x ≠ pj.x` → `cont`, `denominator ← denominator * (pi.x - pj.x)`.

In GF(2¹⁶), subtraction = addition = XOR.

**Source**: spqr/src/encoding/polynomial.rs (lines 202:8-207:9)
-/

@[expose] public section

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf  Polynomial

namespace spqr.encoding.polynomial.Poly.lagrange_interpolate_complete_loop0

/--
**Spec theorem for `encoding.polynomial.Poly.lagrange_interpolate_complete_loop0.body`**:

Postcondition: `done` ⇒ denominator unchanged and `pi' = pi`;
`cont` ⇒ denominator unchanged (skip) or multiplied by `(pi.x - pj.x)` (accumulate). -/
@[step]
theorem body_spec (pi : Pt)
    (iter : core.slice.iter.Iter Pt)
    (denominator : GF16) :
    body pi iter denominator ⦃ result =>
      match result with
      | ControlFlow.done (pi', denom') =>
          denom'.toGF216 = denominator.toGF216 ∧ pi' = pi
      | ControlFlow.cont (_, denom') =>
          denom'.toGF216 = denominator.toGF216 ∨
          ∃ (pj_x : GF216),
            denom'.toGF216 =
              denominator.toGF216 *
                (pi.x.toGF216 - pj_x)
      ⦄ := by
  unfold body
  step*

end spqr.encoding.polynomial.Poly.lagrange_interpolate_complete_loop0

/-! # Spec Theorem for `lagrange_interpolate_complete`: loop 0

Iterates `loop0.body` over all remaining points to compute
`denominator_final = denominator_init * ∏_{j, pj.x ≠ pi.x} (pi.x - pj.x)`.
The Lagrange scaling factor is then `scale = pi.y / denominator_final`.

**Source**: spqr/src/encoding/polynomial.rs (lines 202:8-207:9)
-/

namespace spqr.encoding.polynomial.Poly.lagrange_interpolate_complete_loop0
/-- One step of the denominator loop, phrased as preservation of
`denominator * lagrangeDenomProd pi.x slice i`. -/
private lemma body_denom_spec (pi : Pt) (iter : core.slice.iter.Iter Pt) (denominator : GF16) :
    body pi iter denominator ⦃ result =>
      match result with
      | ControlFlow.done (pi', denom') =>
          pi' = pi ∧ denom' = denominator ∧ iter.slice.val.length ≤ iter.i
      | ControlFlow.cont (iter1, denom') =>
          iter1.slice = iter.slice ∧ iter1.i = iter.i + 1 ∧ iter.i < iter.slice.val.length ∧
          denom'.toGF216 * lagrangeDenomProd pi.x iter.slice.val (iter.i + 1) =
            denominator.toGF216 * lagrangeDenomProd pi.x iter.slice.val iter.i ⦄ := by
  unfold body
  simp only [core.slice.iter.IteratorSliceIter.next]
  split
  next h_lt =>
    have h_len := Slice.len_val iter.slice
    change _ = iter.slice.val.length at h_len
    have h_lt' : iter.i < iter.slice.val.length := by omega
    simp only [bind_ok]
    step as ⟨b, h_b⟩
    split
    next hb =>
      refine (WP.spec_ok _).mpr ⟨rfl, rfl, h_lt', ?_⟩
      rw [lagrangeDenomProd_skip pi.x iter.slice.val iter.i h_lt' (h_b.mp hb)]
    next hb =>
      step as ⟨g, h_g⟩
      step as ⟨d1, h_d1⟩
      refine ⟨h_lt', ?_⟩
      change g.toGF216 = pi.x.toGF216 - (iter.slice.val.get ⟨iter.i, h_lt'⟩).x.toGF216 at h_g
      rw [lagrangeDenomProd_accum pi.x iter.slice.val iter.i h_lt' (fun h => hb (h_b.mpr h)),
        h_d1, h_g]
      ring
  next h_ge =>
    have h_len := Slice.len_val iter.slice
    change _ = iter.slice.val.length at h_len
    have h_ge' : iter.slice.val.length ≤ iter.i := by omega
    simp only [bind_ok]
    exact (WP.spec_ok _).mpr ⟨rfl, rfl, h_ge'⟩

/-- **Spec theorem for `encoding.polynomial.Poly.lagrange_interpolate_complete_loop0`**:

Always succeeds. Returns `pi' = pi` and
`denominator'.toGF216 = denominator.toGF216 * lagrangeDenomProd pi.x iter.slice.val iter.i`.
With `iter.i = 0` and `denominator = ONE`, this yields the full Lagrange denominator product. -/
@[step]
theorem loop0_spec
    (iter : core.slice.iter.Iter Pt)
    (pi : Pt)
    (denominator : GF16) :
    lagrange_interpolate_complete_loop0 iter pi denominator ⦃ (result : Pt × GF16) =>
      result.1 = pi ∧
      result.2.toGF216 = denominator.toGF216 *
        lagrangeDenomProd pi.x iter.slice.val iter.i ⦄ := by
  unfold lagrange_interpolate_complete_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : core.slice.iter.Iter Pt × GF16) =>
      p.1.slice.len - p.1.i)
    (inv := fun (p : core.slice.iter.Iter Pt × GF16) =>
      p.1.slice = iter.slice ∧
      iter.i ≤ p.1.i ∧
      p.2.toGF216 * lagrangeDenomProd pi.x
          iter.slice.val p.1.i =
        denominator.toGF216 *
          lagrangeDenomProd pi.x
            iter.slice.val iter.i)
  · rintro ⟨iter', denom'⟩ hinv
    dsimp only at hinv
    obtain ⟨hslice, hge, hinv⟩ := hinv
    apply WP.spec_mono (body_denom_spec pi iter' denom')
    rintro (⟨iter'', denom''⟩ | ⟨pi', denom''⟩) h_cf
    · obtain ⟨hslice', hi', hlt, hstep⟩ := h_cf
      have h_len := Slice.len_val iter'.slice
      change _ = iter'.slice.val.length at h_len
      dsimp only
      rw [hslice] at hstep
      refine ⟨⟨hslice'.trans hslice, by omega, by rw [hi', hstep, hinv]⟩, ?_⟩
      rw [hslice', hi']
      omega
    · obtain ⟨h_pi, h_d, hge'⟩ := h_cf
      rw [hslice] at hge'
      refine ⟨h_pi, ?_⟩
      rw [h_d, ← hinv, lagrangeDenomProd_eq_one_of_le pi.x iter.slice.val iter'.i hge', mul_one]
  · exact ⟨rfl, le_refl _, rfl⟩

end spqr.encoding.polynomial.Poly.lagrange_interpolate_complete_loop0

namespace spqr.encoding.polynomial.Poly.lagrange_interpolate_complete_loop1

@[step]
theorem body_spec
    (g scale : GF16)
    (iter' : core.ops.range.Range Usize)
    (v' : alloc.vec.Vec GF16)
    (h_start_ge : 1 ≤ iter'.start.val)
    (h_end_eq : iter'.«end».val = v'.val.length) :
    body g scale iter' v' ⦃ cf =>
      match cf with
      | ControlFlow.done r =>
          r = v' ∧ ¬ (iter'.start.val < iter'.«end».val)
      | ControlFlow.cont (iter1, v2) =>
          iter'.start.val < iter'.«end».val ∧
          iter1.start.val = iter'.start.val + 1 ∧
          iter1.«end» = iter'.«end» ∧
          v2.val.length = v'.val.length ∧
          (∀ (h_idx : v'.val.length - iter'.start.val < v2.val.length),
            (v2.val.get ⟨v'.val.length - iter'.start.val, h_idx⟩).toGF216 =
              (v'.val[v'.val.length - iter'.start.val]!).toGF216 *
                scale.toGF216) ∧
          (∀ (h_idx : v'.val.length - iter'.start.val - 1 < v2.val.length),
            (v2.val.get ⟨v'.val.length - iter'.start.val - 1, h_idx⟩).toGF216 =
              (v'.val[v'.val.length - iter'.start.val - 1]!).toGF216 +
              (v'.val[v'.val.length - iter'.start.val]!).toGF216 *
                g.toGF216) ∧
          (∀ (j : Nat),
            j ≠ v'.val.length - iter'.start.val ∧
            j ≠ v'.val.length - iter'.start.val - 1 →
            v2.val[j]? = v'.val[j]?) ⦄ := by
  unfold body
  step with core.iter.range.IteratorRange.next_Usize_spec' iter' as
    ⟨opt, iter1', h_none, h_some⟩
  by_cases h_lt : iter'.start.val < iter'.end.val
  · obtain ⟨h_opt, h_start1, h_end1⟩ := h_some h_lt
    rw [h_opt]
    have h_vlen : (alloc.vec.Vec.len v').val = v'.val.length := alloc.vec.Vec.len_val v'
    step as ⟨i1, h_i1, _⟩
    step as ⟨g1, h_g1⟩
    step as ⟨nd, h_nd⟩
    step as ⟨g2, imb, h_g2, h_imb⟩
    step as ⟨g3, h_g3⟩
    step as ⟨i2, h_i2, _⟩
    have h_set1 : (imb g3).val = v'.val.set i1.val g3 := by
      rw [h_imb, alloc.vec.Vec.set_val_eq]
    have h_len1 : (imb g3).val.length = v'.val.length := by rw [h_set1, List.length_set]
    step as ⟨g4, imb1, h_g4, h_imb1⟩
    step as ⟨g5, h_g5⟩
    have h_end' : iter'.end.val = v'.val.length := h_end_eq
    have hi1 : i1.val = v'.val.length - iter'.start.val := by omega
    have hi2 : i2.val = v'.val.length - iter'.start.val - 1 := by omega
    have h_c : v'.val.length - iter'.start.val < v'.val.length := by omega
    have h_c1 : 1 ≤ v'.val.length - iter'.start.val := by omega
    have h_set2 : (imb1 g5).val =
        (v'.val.set (v'.val.length - iter'.start.val) g3).set
          (v'.val.length - iter'.start.val - 1) g5 := by
      rw [h_imb1, alloc.vec.Vec.set_val_eq, h_set1, hi1, hi2]
    have h_v1 : g1 = v'.val[v'.val.length - iter'.start.val]! := by
      rw [h_g1, getElem!_pos v'.val _ h_c]
      simp only [hi1]
    have h_v2 : g2 = v'.val[v'.val.length - iter'.start.val]! := by
      rw [h_g2, getElem!_pos v'.val _ h_c]
      simp only [hi1]
    have h_v4 : g4 = v'.val[v'.val.length - iter'.start.val - 1]! := by
      rw [h_g4, getElem!_pos v'.val _ (by omega)]
      simp only [hi2, h_set1, hi1]
      rw [List.getElem_set_ne (by omega)]
    refine ⟨h_lt, h_start1, h_end1, by rw [h_set2, List.length_set, List.length_set],
      fun h_idx => ?_, fun h_idx => ?_, fun j hj1 hj2 => ?_⟩
    · have h_some : (imb1 g5).val[v'.val.length - iter'.start.val]? = some g3 := by
        rw [h_set2, List.getElem?_set_ne (by omega), List.getElem?_set_self h_c]
      rw [List.getElem?_eq_getElem h_idx] at h_some
      rw [List.get_eq_getElem, Option.some.inj h_some, h_g3, h_v2]
    · have h_some : (imb1 g5).val[v'.val.length - iter'.start.val - 1]? = some g5 := by
        rw [h_set2, List.getElem?_set_self (by rw [List.length_set]; omega)]
      rw [List.getElem?_eq_getElem h_idx] at h_some
      rw [List.get_eq_getElem, Option.some.inj h_some, h_g5, h_nd, h_v1, h_v4]
    · rw [h_set2, List.getElem?_set_ne (Ne.symm hj2), List.getElem?_set_ne (Ne.symm hj1)]
  · obtain ⟨h_opt, rfl⟩ := h_none h_lt
    rw [h_opt]
    exact (WP.spec_ok _).mpr ⟨rfl, h_lt⟩

@[step]
theorem loop1_spec
    (iter : core.ops.range.Range Usize)
    (v : alloc.vec.Vec GF16)
    (g : GF16)
    (scale : spqr.encoding.gf.GF16)
    (h_start : iter.start.val = 1)
    (h_end : iter.«end».val = v.val.length) :
    lagrange_interpolate_complete_loop1 iter v g scale ⦃ (result : alloc.vec.Vec GF16) =>
      result.val.length = v.val.length ∧
      (∀ k (hk : k < result.val.length),
        0 < k →
          (result.val.get ⟨k, hk⟩).toGF216 =
            scale.toGF216 * hornerAccum g v.val k) ∧
      (∀ (h0 : 0 < result.val.length),
      (result.val.get ⟨0, h0⟩).toGF216 = hornerAccum g v.val 0) ⦄ := by
  unfold lagrange_interpolate_complete_loop1
  apply loop.spec_decr_nat
    (measure := fun (p : core.ops.range.Range Std.Usize ×
                        alloc.vec.Vec spqr.encoding.gf.GF16) =>
      p.1.«end».val - p.1.start.val)
    (inv := fun (p : core.ops.range.Range Std.Usize ×
                      alloc.vec.Vec spqr.encoding.gf.GF16) =>
      p.2.val.length = v.val.length ∧
      p.1.«end».val = v.val.length ∧
      1 ≤ p.1.start.val ∧
      (∀ k (hk : k < p.2.val.length),
        v.val.length - p.1.start.val < k →
          (p.2.val.get ⟨k, hk⟩).toGF216 =
            scale.toGF216 * hornerAccum g v.val k) ∧
      (∀ (hcur : v.val.length - p.1.start.val < p.2.val.length),
          (p.2.val.get ⟨v.val.length - p.1.start.val,
            hcur⟩).toGF216 =
            hornerAccum g v.val (v.val.length - p.1.start.val)) ∧
      (∀ k, k < v.val.length - p.1.start.val →
        p.2.val[k]? = v.val[k]?))
  · rintro ⟨iter', v'⟩ hinv
    dsimp only at hinv
    obtain ⟨hlen, hend, hstart_ge, hscaled, hcursor, hunchanged⟩ := hinv
    apply WP.spec_mono (body_spec g scale iter' v' hstart_ge (by rw [hend, hlen]))
    rintro (⟨iter'', v''⟩ | v'') h_cf
    · obtain ⟨h_lt, h_start1, h_end1, h_v2len, h_scaled_pos, h_carry_pos, h_frame⟩ := h_cf
      have h_end1' : iter''.end.val = iter'.end.val := by rw [h_end1]
      rw [hlen] at h_scaled_pos h_carry_pos h_frame
      have hc : v.val.length - iter'.start.val < v.val.length := by omega
      have hc1 : 1 ≤ v.val.length - iter'.start.val := by omega
      have h_v'c : (v'.val[v.val.length - iter'.start.val]!).toGF216 =
          hornerAccum g v.val (v.val.length - iter'.start.val) := by
        rw [getElem!_pos v'.val _ (by omega)]
        exact hcursor (by omega)
      -- positions other than the two touched ones are unchanged
      have h_keep : ∀ k (h1 : k < v''.val.length) (h2 : k < v'.val.length),
          k ≠ v.val.length - iter'.start.val → k ≠ v.val.length - iter'.start.val - 1 →
          v''.val.get ⟨k, h1⟩ = v'.val.get ⟨k, h2⟩ := by
        intro k h1 h2 hk1 hk2
        have := h_frame k ⟨hk1, hk2⟩
        rw [List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2] at this
        exact Option.some.inj this
      dsimp only
      refine ⟨⟨h_v2len.trans hlen, h_end1'.trans hend, by omega, fun k hk hk_gt => ?_,
        fun hcur => ?_, fun k hk => ?_⟩, by omega⟩
      · by_cases hk_eq : k = v.val.length - iter'.start.val
        · subst hk_eq
          rw [h_scaled_pos hk, h_v'c, mul_comm]
        · rw [h_keep k hk (by omega) hk_eq (by omega)]
          exact hscaled k (by omega) (by omega)
      · have h_idx : v.val.length - iter'.start.val - 1 < v''.val.length := by omega
        have h_eq : v.val.length - iter''.start.val = v.val.length - iter'.start.val - 1 := by
          omega
        simp only [h_eq]
        rw [h_carry_pos h_idx, h_v'c, getElem!_pos v'.val _ (by omega),
          hornerAccum_unfold g v.val (v.val.length - iter'.start.val - 1) (by omega),
          Nat.sub_add_cancel hc1]
        have := hunchanged (v.val.length - iter'.start.val - 1) (by omega)
        rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at this
        rw [Option.some.inj this, mul_comm]
        rfl
      · rw [h_frame k ⟨by omega, by omega⟩]
        exact hunchanged k (by omega)
    · obtain ⟨rfl, h_nlt⟩ := h_cf
      have h0 : v.val.length - iter'.start.val = 0 := by omega
      refine ⟨hlen, fun k hk hk0 => hscaled k hk (by omega), fun h0' => ?_⟩
      have := hcursor (by omega)
      simp only [h0] at this
      exact this
  · dsimp only [Prod.fst, Prod.snd]
    simp only [h_start]
    refine ⟨trivial, h_end, le_refl 1, ?_, ?_, ?_⟩
    · intro k hk hgt; omega
    · intro hcur
      rw [hornerAccum_unfold g v.val (v.val.length - 1) hcur]
      have hlen_eq : v.val.length - 1 + 1 = v.val.length := by omega
      rw [hlen_eq, hornerAccum_eq_zero_of_le g v.val v.val.length (le_refl _)]
      simp [mul_zero, add_zero]
    · intro _ _; trivial

end spqr.encoding.polynomial.Poly.lagrange_interpolate_complete_loop1

namespace spqr.encoding.polynomial.Poly

/-! ## Spec theorem for `spqr.encoding.polynomial.Poly.lagrange_interpolate_complete`

Top-level correctness spec for `Poly::lagrange_interpolate_complete`
(`src/encoding/polynomial.rs`, lines 197–223).

The function takes a polynomial `self` (typically `∏ⱼ (X − pⱼ.x)`), a point slice `pts`, and an
index `i`, then:
1. Computes `denominator = ∏_{j≠i} (pᵢ.x − pⱼ.x)` (loop 0).
2. Computes `scale = pᵢ.y / denominator` via Fermat inversion in GF(2¹⁶).
3. Divides out `(X − pᵢ.x)` by Horner-style synthetic division, scaling each coefficient by
   `scale` (loop 1). The result is shifted up by one degree (multiplied by `X`).
4. Asserts `coefficients[0] == ZERO` (exact division check). -/
@[step]
theorem lagrange_interpolate_complete_spec
    (self : Poly) (pts : Slice Pt) (i : Usize)
    (hi : i.val < pts.val.length)
    (hlen : 0 < self.degree)
    (heval : self.evalAt (pts[i]!).x = 0) :
    lagrange_interpolate_complete self pts i ⦃ (result : Poly) =>
      result.degree = self.degree ∧
      result.toGF216Poly * (X - C (GF16.toGF216 (pts[i]!).x)) =
        X * C (lagrangeScaleGF216 (pts[i]!) pts) * self.toGF216Poly ⦄ := by
  unfold lagrange_interpolate_complete
  step as ⟨pi, h_pi⟩
  step as ⟨iter, h_iter_sl, h_iter_i⟩
  step as ⟨pi1, denominator, h_pi1, h_den⟩
  step as ⟨scale, h_scale⟩
  step as ⟨v, h_vlen, h_vk, h_v0⟩
  have h_slen : 0 < self.coefficients.val.length := hlen
  have h_v_pos : 0 < v.val.length := by omega
  step as ⟨left_val, h_lv⟩
  step as ⟨b, h_b⟩
  have hpi : pi = pts[i]! := by
    rw [h_pi, Slice.getElem!_Usize_eq, getElem!_pos pts.val i.val hi]
  have hpi1 : pi1 = pts[i]! := h_pi1.trans hpi
  -- `pts[i].x` is a root of `self`, so the Horner value at position 0 vanishes
  have hH0 : hornerAccum (pts[i]!).x self.coefficients.val 0 = 0 := by
    rw [hornerAccum_zero_eq_eval]
    exact heval
  have h_v0' : ∀ (h0 : 0 < v.val.length), (v.val.get ⟨0, h0⟩).toGF216 = 0 := by
    intro h0
    rw [h_v0 h0, hpi1, hH0]
  have h_lv0 : left_val.value.val = 0 :=
    GF16_toGF216_eq_zero_imp left_val (by rw [h_lv]; exact h_v0' h_v_pos)
  have h_bt : b = true := h_b.mpr (UScalar.eq_of_val_eq (by
    rw [h_lv0]
    simp only [GF16.ZERO, UScalar.ofNatCore_val_eq]))
  rw [if_pos h_bt]
  have hscale_eq : scale.toGF216 = lagrangeScaleGF216 (pts[i]!) pts.val := by
    unfold lagrangeScaleGF216
    rw [h_scale, h_den, h_iter_sl, h_iter_i, GF16.ONE_toGF216, one_mul, hpi1, hpi]
  refine (WP.spec_ok _).mpr ⟨h_vlen, ?_⟩
  change listToGF216Poly v.val * _ = _ * listToGF216Poly self.coefficients.val
  rw [← hscale_eq]
  apply poly_identity_from self.coefficients.val v.val (pts[i]!).x scale.toGF216 h_vlen hlen
    h_v0' hH0
  intro k hk hk0
  rw [h_vk k hk hk0, hpi1]

end spqr.encoding.polynomial.Poly
