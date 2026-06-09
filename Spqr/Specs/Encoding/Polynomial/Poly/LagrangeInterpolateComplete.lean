/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Math.List
import Spqr.Math.Poly.Aeneas.PolyIdentity
import Spqr.Specs.Encoding.Gf.GF16.Sub
import Spqr.Specs.Encoding.Gf.GF16.Div
import Spqr.Specs.Encoding.Gf.GF16.Eq
import Spqr.Specs.Encoding.Gf.GF16.ZERO
import Spqr.Specs.Encoding.Gf.GF16.ONE
import Spqr.Specs.Encoding.Gf.GF16.AddAssign
import Spqr.Specs.Aeneas.RangeIteratorNext
import Spqr.Specs.Aeneas.SliceIteratorNext
import Spqr.Specs.Aeneas.FmtArgumentsFromStr
import Mathlib.RingTheory.DedekindDomain.Basic
/-!
# Spec Theorem for `lagrange_interpolate_complete`: loop body 0

Given a distinguished point `pi = pts[i]` and a running accumulator `denominator`, the full loop 0
computes the product
  `denominator_final = ∏_{j : pts[j].x ≠ pi.x} (pi.x - pts[j].x)`
by iterating over all points `pj` in `pts`.  This denominator is then used to form the Lagrange
scaling factor
  `scale = pi.y / denominator_final`
which ensures that the interpolating polynomial `f` satisfies `f(pi.x) = pi.y` for the distinguished
point and `f(pj.x) = 0` for all other points.

Each step of the loop body:

1. Retrieves the next point `pj` from the slice iterator.
2. If the iterator is exhausted (`none`), returns `done` with the current `(pi, denominator)` pair —
   the accumulation is complete.
3. If `pi.x = pj.x`, returns `cont` with the denominator unchanged — this is the `i = j` case where
   the point is skipped.
4. If `pi.x ≠ pj.x`, computes `g = pi.x - pj.x` and updates `denominator ← denominator * g`, then
   returns `cont` with the updated denominator.

In GF(2¹⁶) (characteristic 2), subtraction coincides with addition:
  `pi.x - pj.x = pi.x + pj.x = pi.x ⊕ pj.x`

**Source**: spqr/src/encoding/polynomial.rs (lines 202:8-207:9)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf spqr.math.gf

namespace spqr.encoding.polynomial.Poly.lagrange_interpolate_complete_loop0

/--
**Spec theorem for `encoding.polynomial.Poly.lagrange_interpolate_complete_loop0.body`**:

One step of the denominator accumulation for Lagrange interpolation. Given a distinguished point
`pi`, an iterator over the point set, and the current denominator accumulator, the body processes
the next point from the iterator:

• If the iterator is exhausted, returns `done` with the unchanged `(pi, denominator)` pair.
• If the next point `pj` has `pi.x = pj.x` (self-point), returns `cont` with the denominator
  unchanged.
• If `pi.x ≠ pj.x`, returns `cont` with the denominator updated to `denominator * (pi.x - pj.x)` in
  GF(2¹⁶).

The postcondition captures the mathematical invariant:

  In the **`done`** branch:
    `denom'.toGF216 = denominator.toGF216 ∧ pi' = pi`

  In the **`cont`** branch (disjunction over skip / accumulate):
    `denom'.toGF216 = denominator.toGF216`
    ∨ `∃ pj_x : GF216, denom'.toGF216 =
        denominator.toGF216 * (pi.x.toGF216 - pj_x)`

**Source**: spqr/src/encoding/polynomial.rs (lines 202:8-207:9)
-/
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
  obtain ⟨o, iter1, hnext⟩ := core.slice.iter.IteratorSliceIter.next_ok iter
  rw [hnext]
  simp only [bind_tc_ok]
  cases o with
  | none =>
    simp [WP.spec_ok]
  | some pj =>
    simp only [GF16.Insts.CoreCmpPartialEqGF16.eq, bind_tc_ok, decide_eq_true_eq,
      uncurry_apply_pair]
    split
    · simp only [WP.spec_ok]
      grind
    · step
      step
      right
      exact ⟨pj.x.toGF216, by rw [denominator1_post, g_post]⟩

end spqr.encoding.polynomial.Poly.lagrange_interpolate_complete_loop0

/-!
# Spec Theorem for `lagrange_interpolate_complete`: loop 0

Given a distinguished point `pi = pts[i]`, an iterator over the full point set, and an initial
`denominator` (typically `GF16::ONE`), the loop computes the product
  `denominator_final = denominator_init *
      ∏_{j ∈ remaining, pts[j].x ≠ pi.x} (pi.x - pts[j].x)`
by repeatedly invoking `lagrange_interpolate_complete_loop0.body`, which processes one point per
iteration.  This denominator is then used to form the Lagrange scaling factor
  `scale = pi.y / denominator_final`
which ensures that the interpolating polynomial `f` satisfies `f(pi.x) = pi.y` for the distinguished
point and `f(pj.x) = 0` for all other points.

The loop is an Aeneas-extracted `loop` fixed-point: it calls the body function `body pi iter₁
denominator₁` at each step, threading the `(iter, denominator)` state through the `cont`
control-flow arm until the iterator is exhausted (`done`).

Each iteration (handled by the body spec in `LagrangeInterpolateCompleteLoopBody0.lean`):

1. Retrieves the next point `pj` from the slice iterator.
2. If the iterator is exhausted (`none`), returns `done` with the current `(pi, denominator)` pair —
   the accumulation is complete.
3. If `pi.x = pj.x`, returns `cont` with the denominator unchanged — this is the `i = j` case where
   the point is skipped.
4. If `pi.x ≠ pj.x`, computes `g = pi.x - pj.x` and updates `denominator ← denominator * g`, then
   returns `cont` with the updated denominator.

In GF(2¹⁶) (characteristic 2), subtraction coincides with addition:
  `pi.x - pj.x = pi.x + pj.x = pi.x ⊕ pj.x`

**Source**: spqr/src/encoding/polynomial.rs (lines 202:8-207:9)
-/

namespace spqr.encoding.polynomial.Poly.lagrange_interpolate_complete_loop0

open spqr.encoding.polynomial (lagrangeDenomProd lagrangeDenomProd_ge
  lagrangeDenomProd_skip lagrangeDenomProd_accum)

/-! ### Helper lemma for element access across equal slices -/

private lemma slice_get_eq_of_eq {T : Type} {s₁ s₂ : Slice T} (h : s₁ = s₂)
    (i : Nat) (h₁ : i < s₁.val.length) (h₂ : i < s₂.val.length) :
    s₁.val.get ⟨i, h₁⟩ = s₂.val.get ⟨i, h₂⟩ := by
  subst h
  rfl

/--
**Spec theorem for `encoding.polynomial.Poly.lagrange_interpolate_complete_loop0`**:

• The function always succeeds (no panic) for any valid inputs, since the underlying operations
  (`PartialEq<GF16>`, `Sub<GF16>`, `MulAssign<GF16>`, and iterator `next`) are all total on bounded
  integers.
• The returned point is unchanged: `pi' = pi`.
• The returned denominator satisfies the GF(2¹⁶)-level identity:
    `denominator'.toGF216 =
        denominator.toGF216 *
          lagrangeDenomProd pi.x
            iter.slice.val iter.i`
  i.e. the final denominator is the initial denominator multiplied
  by the product of `(pi.x - pj.x)` for all remaining points
  `pj` in the iterator where `pj.x ≠ pi.x`.
• When the loop is called at the top level with `iter.i = 0` and
  `denominator = GF16::ONE`, the result specialises to:
    `denominator'.toGF216 =
        lagrangeDenomProd pi.x
          iter.slice.val 0`
  which is the full Lagrange denominator product over all points.

**Source**: spqr/src/encoding/polynomial.rs (lines 202:8-207:9)
-/
@[step]
theorem loop0_spec
    (iter : core.slice.iter.Iter Pt)
    (pi : Pt)
    (denominator : GF16) :
    lagrange_interpolate_complete_loop0 iter pi denominator ⦃ (result : Pt × GF16) =>
        result.1 = pi ∧
        result.2.toGF216 =
          denominator.toGF216 *
            lagrangeDenomProd pi.x
              iter.slice.val iter.i ⦄ := by
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
  · rintro ⟨iter', denom'⟩ ⟨hslice, hge, hinv⟩
    simp only [] at hslice hge hinv ⊢
    unfold body
    simp only [core.slice.iter.IteratorSliceIter.next]
    split
    · rename_i hlt
      simp only [bind_tc_ok]
      step*
      · have hlt_list : iter'.i < iter.slice.val.length := by
          simp only [Slice.len_val, hslice] at hlt; exact hlt
        have hval_eq : pi.x.value = (iter.slice.val.get ⟨iter'.i, hlt_list⟩).x.value := by
          have h1 := b_post.mp ‹b = true›
          simp only [hslice] at h1
          exact h1
        refine ⟨hslice, by omega, ?_, by (simp only [Slice.len_val]; grind)⟩
        rw [← lagrangeDenomProd_skip pi.x iter.slice.val iter'.i hlt_list hval_eq]
        exact hinv
      · have hlt_list : iter'.i < iter.slice.val.length := by
          simp only [Slice.len_val, hslice] at hlt; exact hlt
        have hval_ne : pi.x.value ≠ (iter.slice.val.get ⟨iter'.i, hlt_list⟩).x.value := by
          have h1 := mt b_post.mpr ‹¬b = true›
          simp only [hslice] at h1
          exact h1
        refine ⟨hslice, by omega, ?_, by (simp only [Slice.len_val]; grind)⟩
        rw [lagrangeDenomProd_accum pi.x iter.slice.val iter'.i hlt_list hval_ne] at hinv
        simp only [hslice] at g_post
        simp only [List.get_eq_getElem] at hinv
        rw [denominator1_post, g_post]
        ring_nf
        ring_nf at hinv
        exact hinv
    · rename_i hnlt
      simp only [bind_tc_ok]
      have hge' : iter.slice.val.length ≤ iter'.i := by
        simp only [Slice.len_val, hslice] at hnlt; grind
      rw [lagrangeDenomProd_eq_one_of_le pi.x iter.slice.val iter'.i hge', mul_one] at hinv
      grind
  · grind

end spqr.encoding.polynomial.Poly.lagrange_interpolate_complete_loop0


/-! # Spec Theorem for `lagrange_interpolate_complete`: loop 1 -/

namespace spqr.encoding.polynomial.Poly.lagrange_interpolate_complete_loop1

open spqr.encoding.polynomial (hornerAccum hornerAccum_ge hornerAccum_unfold)

instance : Inhabited spqr.encoding.gf.GF16 := ⟨⟨⟨0, by scalar_tac⟩⟩⟩

@[step]
theorem body_spec
    (g scale : spqr.encoding.gf.GF16)
    (iter' : core.ops.range.Range Std.Usize)
    (v' : alloc.vec.Vec spqr.encoding.gf.GF16)
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
            j ≠ v'.val.length - iter'.start.val →
            j ≠ v'.val.length - iter'.start.val - 1 →
            v2.val[j]? = v'.val[j]?) ⦄ := by
  unfold body
  obtain ⟨opt, iter1, hnext, h_none, h_some⟩ := core.iter.range.IteratorRange.next_Usize_spec iter'
  rw [hnext]; simp only [bind_tc_ok]
  by_cases h_lt : iter'.start.val < iter'.«end».val
  · obtain ⟨h_opt_eq, h_start1, h_end1⟩ := h_some h_lt
    rw [h_opt_eq]
    have h_start_lt_len : iter'.start.val < v'.val.length := by omega
    have h_start_le_len : iter'.start.val ≤ v'.val.length := by omega
    have h_cursor_lt_len : v'.val.length - iter'.start.val < v'.val.length := by omega
    have h_cursor_ge1 : 1 ≤ v'.val.length - iter'.start.val := by omega
    step*
    · simp_all
      grind
    · simp_all




  · obtain ⟨h_opt_eq, h_range_eq⟩ := h_none (by omega)
    rw [h_opt_eq]
    grind

@[step]
theorem loop1_spec
    (iter : core.ops.range.Range Std.Usize)
    (v : alloc.vec.Vec spqr.encoding.gf.GF16)
    (g : spqr.encoding.gf.GF16)
    (scale : spqr.encoding.gf.GF16)
    (h_start : iter.start.val = 1)
    (h_end : iter.«end».val = v.val.length) :
    lagrange_interpolate_complete_loop1 iter v g scale
      ⦃ (result : alloc.vec.Vec spqr.encoding.gf.GF16) =>
        result.val.length = v.val.length ∧
        (∀ k (hk : k < result.val.length),
          0 < k →
            (result.val.get ⟨k, hk⟩).toGF216 =
              scale.toGF216 * hornerAccum g v.val k) ∧
        (∀ (h0 : 0 < result.val.length),
            (result.val.get ⟨0, h0⟩).toGF216 =
              hornerAccum g v.val 0) ⦄ := by
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
  · rintro ⟨iter', v'⟩ ⟨hlen, hend, hstart_ge, hscaled, hcursor, hunchanged⟩
    simp only [] at hlen hend hstart_ge hscaled hcursor hunchanged ⊢
    have h_end_eq : iter'.«end».val = v'.val.length := by omega
    step*
    split
    · rename_i r_post
      simp only [] at r_post
      obtain ⟨h_eq, h_nlt⟩ := r_post
      constructor
      · simp_all
      constructor
      · intro k hk hk_pos
        subst h_eq
        exact hscaled k hk (by omega)
      · intro h0
        simp_all only [List.get_eq_getElem, tsub_lt_self_iff, and_self,
        forall_and_index, not_lt, Nat.sub_eq_zero_of_le,
        not_lt_zero, IsEmpty.forall_iff, implies_true]
        have hcz : v.val.length - iter'.start.val = 0 := by omega
        have hc := hcursor (by grind)
        convert hc using 2
        simp_all
        grind
    · rename_i r_post
      simp only [] at r_post
      obtain ⟨h_lt, h_start1, h_end1, h_v2len, h_scaled_pos, h_carry_pos, h_frame⟩ := r_post
      set cursor := v.val.length - iter'.start.val with hcursor_def
      have hcge1 : cursor ≥ 1 := by omega
      have hcur_v' : cursor < v'.val.length := by omega
      have h_new_start_eq : v.val.length - (iter'.start.val + 1) = cursor - 1 := by omega
      have h_new_cursor_eq : v.val.length - (Prod.fst r_post).start.val = cursor - 1 := by
        omega
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · omega
      · have : (Prod.fst r_post).«end».val = iter'.«end».val := by
          rw [h_end1]
        omega
      · omega
      · intro k hk hk_gt
        rw [h_new_cursor_eq] at hk_gt
        by_cases hk_eq : k = cursor
        · subst hk_eq
          rw [hlen] at h_scaled_pos
          have h_idx : cursor < (Prod.snd r_post).val.length := by omega
          specialize h_scaled_pos h_idx
          simp only [GF16.toGF216] at h_scaled_pos hcursor ⊢
          rw [h_scaled_pos]
          have hbang : v'.val[cursor]! = v'.val.get ⟨cursor, hcur_v'⟩ :=
            getElem!_pos v'.val cursor hcur_v'
          rw [hbang]
          specialize hcursor hcur_v'
          rw [hcursor]; ring
        · have hk_gt' : cursor < k := by omega
          have hk_v' : k < v'.val.length := by omega
          have h_inv := hscaled k hk_v' (by omega)
          have h_fr := h_frame k (by omega) (by omega)
          simp only [GF16.toGF216] at h_inv ⊢
          have h_get := list_get_of_getElem?_eq h_fr (by omega) hk_v'
          simp only [List.get_eq_getElem] at h_get
          grind
      · intro hcur
        rw [h_new_cursor_eq] at hcur
        have hcm1_v' : cursor - 1 < v'.val.length := by omega
        have hcm1_v : cursor - 1 < v.val.length := by omega
        rw [hlen] at h_carry_pos
        have h_idx : cursor - 1 < (Prod.snd r_post).val.length := by omega
        specialize h_carry_pos h_idx
        have h_idx_eq : v.val.length - (Prod.fst r_post).start.val = cursor - 1 :=
          h_new_cursor_eq
        suffices hsuff :
            ((Prod.snd r_post).val.get ⟨cursor - 1, h_idx⟩).toGF216 =
              hornerAccum g v.val (cursor - 1) by
          exact hornerAccum_eq_of_idx_eq h_idx_eq hsuff
        rw [h_carry_pos]
        rw [hornerAccum_unfold g v.val (cursor - 1) hcm1_v]
        have h_succ : cursor - 1 + 1 = cursor := by omega
        rw [h_succ]
        have hbang_cm1 : v'.val[cursor - 1]! = v'.val.get ⟨cursor - 1, hcm1_v'⟩ :=
          getElem!_pos v'.val (cursor - 1) hcm1_v'
        have hbang_c : v'.val[cursor]! = v'.val.get ⟨cursor, hcur_v'⟩ :=
          getElem!_pos v'.val cursor hcur_v'
        rw [hbang_cm1, hbang_c]
        have h_unch := hunchanged (cursor - 1) (by omega)
        have h_get_cm1 := list_get_of_getElem?_eq h_unch hcm1_v' hcm1_v
        rw [h_get_cm1]
        specialize hcursor hcur_v'
        rw [hcursor]
        ring
      · intro k hk_lt
        rw [h_new_cursor_eq] at hk_lt
        have h_fr := h_frame k (by omega) (by omega)
        have h_unch := hunchanged k (by omega)
        rw [h_fr, h_unch]
      · have : (Prod.fst r_post).«end».val = iter'.«end».val := by
          rw [h_end1]
        omega
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


/-! # Spec theorem for `spqr.encoding.polynomial.Poly.lagrange_interpolate_complete` -/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf Polynomial
open spqr.encoding.gf.GF16.Insts.CoreOpsArithDivShared0GF16GF16

namespace spqr.encoding.polynomial.Poly

open spqr.encoding.polynomial (lagrangeScaleGF216 lagrangeDenomProd)


/-!
## Spec theorem for `spqr.encoding.polynomial.Poly.lagrange_interpolate_complete`

The theorem `lagrange_interpolate_complete_spec` is the top-level correctness specification for the
Rust function `Poly::lagrange_interpolate_complete` (`src/encoding/polynomial.rs`, lines 197–223).

**What the Rust function does:**

Given a polynomial `self` (whose coefficients represent the product `∏ⱼ (X − pⱼ.x)` over all
points), a point slice `pts`, and an index `i`, the function:

1. **Loop 0 (denominator accumulation):** Iterates over `pts` to compute `denominator = ∏_{j ≠ i}
   (pᵢ.x − pⱼ.x)`, the Lagrange basis denominator for the i-th point.

2. **Scaling:** Computes `scale = pᵢ.y / denominator`. In GF(2¹⁶), division by `d` is multiplication
   by `d^(2¹⁶ − 2)` (Fermat's little theorem), so `scale = pᵢ.y · denominator^(2¹⁶ − 2)`.

3. **Loop 1 (polynomial long division + scaling):** Divides out the factor `(X − pᵢ.x)` from `self`
   using synthetic/Horner-style long division (processing coefficients from high to low degree), and
   simultaneously scales each coefficient by `scale`. Due to the little-endian coefficient
   representation, the result is implicitly multiplied by `X` (the leading zero coefficient is left
   in place).

4. **Debug assertion:** Asserts `self.coefficients[0] == GF16::ZERO`, confirming the division was
   exact (i.e., `pᵢ.x` was indeed a root).

The net effect is to produce a new polynomial `result` such that:
  `result(X) · (X − pᵢ.x) = X · scale · self(X)`

**Parameters:**
- `self : Poly` — The input polynomial, stored as a `Vec<GF16>` of coefficients in ascending degree
  order. Typically this is the product polynomial `∏ⱼ (X − pⱼ.x)` over all interpolation points.
- `pts : Slice Pt` — A slice of `Pt` values, where each `Pt` has fields `x : GF16` (evaluation
  point) and `y : GF16` (desired value).
- `i : Std.Usize` — Index of the distinguished point `pᵢ = pts[i]` for which we are building the
  Lagrange basis polynomial.

```
    (hi : i.val < pts.val.length)
```

**Precondition 1 — Index in bounds:** `i` is a valid index into the points slice. This mirrors the
Rust `#[hax_lib::requires(i < pts.len())]` annotation.

```
    (hlen : 0 < self.coefficients.val.length)
```

**Precondition 2 — Non-empty polynomial:** The polynomial has at least one coefficient. This ensures
that the long-division loop (loop 1, which iterates `1..coefficients.len()`) and the debug assertion
(`coefficients[0]`) are well-defined.

```
    (heval : self.evalAt (pts.val.get ⟨i.val, hi⟩).x = 0)
```

**Precondition 3 — Root condition:** The polynomial `self` evaluates to zero at `pᵢ.x`.
Mathematically, `self.toGF216Poly.eval(GF16.toGF216(pᵢ.x)) = 0`, meaning `(X − pᵢ.x)` divides `self`
in `GF(2¹⁶)[X]`. This is the crucial algebraic precondition that guarantees the long division in
loop 1 is exact (no remainder), which is what the `debug_assert_eq!` checks at runtime.

Without this precondition, the division would leave a non-zero remainder in `coefficients[0]`, and
the polynomial identity in the postcondition would not hold.


**Postcondition — a weakest-precondition (WP) spec:** The function succeeds (no panic) and produces
a `result : Poly` satisfying two properties:

```
        result.coefficients.val.length =
          self.coefficients.val.length ∧
```

**Postcondition Part 1 — Length preservation:** The output polynomial has the same number of
coefficients as the input. This is because the function modifies coefficients in-place (synthetic
division + scaling) without adding or removing entries. The `X`-scaling artifact means `result` has
an extra leading zero at position 0, but the vector length is unchanged.

```
        result.toGF216Poly *
          (X - C (GF16.toGF216
            (pts.val.get ⟨i.val, hi⟩).x)) =
          X * C (lagrangeScaleGF216
            (pts.val.get ⟨i.val, hi⟩) pts.val) *
            self.toGF216Poly ⦄
```

**Postcondition Part 2 — Polynomial identity:** The core mathematical content. In `GF(2¹⁶)[X]`:

  `result(X) · (X − pᵢ.x) = X · lagrangeScale(pᵢ, pts) · self(X)`

where:
- `result.toGF216Poly` is the mathematical polynomial corresponding to the output coefficient
  vector.
- `(X − C(GF16.toGF216(pᵢ.x)))` is the linear factor that was divided out by the long-division loop.
- `lagrangeScaleGF216(pᵢ, pts)` is the Lagrange scaling factor defined as:
  ```
  lagrangeScaleGF216(pᵢ, pts) =
    GF16.toGF216(pᵢ.y) · (∏_{j, pⱼ.x ≠ pᵢ.x} (pᵢ.x − pⱼ.x))^(2¹⁶ − 2)
  ```
  This equals `pᵢ.y / ∏_{j≠i}(pᵢ.x − pⱼ.x)` using Fermat inversion in
  GF(2¹⁶).
- `X · C(scale) · self.toGF216Poly` captures the `X`-scaling artifact: the result is the quotient
  `self / (X − pᵢ.x)` scaled by `lagrangeScale`, but shifted up by one degree (multiplied by `X`).

**Why the `X` factor?**  The Rust code processes coefficients in-place starting from the high end,
and the quotient naturally lands one position higher than expected in the little-endian vector.
Rather than shifting all coefficients down (which would be O(n) extra work), the function leaves the
zero at `coefficients[0]` and lets the caller remove it via `coefficients.remove(0)` (see
`lagrange_interpolate_pt`).

**Algebraic meaning:**  If we define `Q(X) = self(X) / (X − pᵢ.x)` (the exact polynomial quotient,
which exists by the root precondition), then the identity says:
  `result(X) = X · lagrangeScale(pᵢ, pts) · Q(X)`
After the caller strips the leading zero (divides by `X`), the final polynomial is
`lagrangeScale(pᵢ, pts) · Q(X)`, which is exactly the i-th Lagrange basis polynomial scaled to
produce `pᵢ.y` at `pᵢ.x`.
-/

@[step]
theorem lagrange_interpolate_complete_spec
    (self : Poly) (pts : Slice Pt) (i : Usize)
    (hi : i.val < pts.val.length)
    (hlen : 0 < self.coefficients.val.length)
    (heval : self.evalAt (pts.val.get ⟨i.val, hi⟩).x = 0) :
    lagrange_interpolate_complete self pts i
      ⦃ (result : Poly) =>
        result.coefficients.val.length =
          self.coefficients.val.length ∧
        result.toGF216Poly *
          (X - C (GF16.toGF216
            (pts.val.get ⟨i.val, hi⟩).x)) =
          X * C (lagrangeScaleGF216
            (pts.val.get ⟨i.val, hi⟩) pts.val) *
            self.toGF216Poly ⦄ := by
  unfold lagrange_interpolate_complete
  step*
  · -- success path (b = true)
    rename_i _ _ _ _ _ _ hb
    have hpi_eq : pi = pts.val.get ⟨i.val, hi⟩ := by
      rw [List.get_eq_getElem, List.Inhabited_getElem_eq_getElem!]
      · grind
      · grind
    have hlv_zero := b_post.mp hb
    have hH0 : hornerAccum
        pi1.x self.coefficients.val 0 = 0 := by
      have h0 : 0 < v.val.length := by omega
      rw [← v_post3 h0]
      have hlv_get : left_val = v.val.get ⟨0, h0⟩ := by
        rw [List.get_eq_getElem, List.Inhabited_getElem_eq_getElem!]
        · grind
        · grind
      rw [← hlv_get]
      have hval_zero : left_val.value.val = 0 := by
        have := congr_arg UScalar.val hlv_zero
        simp only [gf.GF16.ZERO, UScalar.ofNatCore_val_eq] at this
        exact this
      exact spqr.encoding.gf.GF16.toGF216_eq_zero left_val hval_zero
    have hscale_eq : scale.toGF216 =
        lagrangeScaleGF216 (pts.val.get ⟨i.val, hi⟩)
          pts.val := by
      unfold lagrangeScaleGF216
      rw [pi1_post1] at scale_post
      rw [scale_post]
      rw [iter_post1, iter_post2] at pi1_post2
      simp only [spqr.encoding.gf.GF16.ONE_toGF216,
        one_mul] at pi1_post2
      rw [pi1_post2, hpi_eq]
    rw [pi1_post1] at v_post2 v_post3 hH0
    rw [hpi_eq] at v_post2 v_post3 hH0
    constructor
    · exact v_post1
    · unfold Poly.toGF216Poly
      apply poly_identity_from_loop1
        self.coefficients.val v.val
        (pts.val.get ⟨i.val, hi⟩).x
        (lagrangeScaleGF216
          (pts.val.get ⟨i.val, hi⟩) pts.val)
      · exact v_post1
      · exact hlen
      · intro h0; rw [v_post3 h0, hH0]
      · exact hH0
      · intro k hk hk_pos
        rw [v_post2 k hk hk_pos, hscale_eq]
  · -- panic path (¬b = true): derive contradiction
    simp only [WP.spec_fail]
    have hpi_eq : pi = pts.val.get ⟨i.val, hi⟩ := by
      rw [List.get_eq_getElem, List.Inhabited_getElem_eq_getElem!]
      · grind
      · grind
    have hH0 : hornerAccum
        (pts.val.get ⟨i.val, hi⟩).x self.coefficients.val 0 = 0 := by
      rw [hornerAccum_zero_eq_eval]
      unfold Poly.evalAt Poly.toGF216Poly at heval
      exact heval
    have h0_len : 0 < v.val.length := by omega
    have hv0_zero : (v.val.get ⟨0, h0_len⟩).toGF216 = 0 := by
      rw [v_post3 h0_len]
      rw [pi1_post1, hpi_eq]
      exact hH0
    have hlv_get : left_val = v.val.get ⟨0, h0_len⟩ := by
      rw [List.get_eq_getElem, List.Inhabited_getElem_eq_getElem!]
      · grind
      · grind
    have hlv_val_zero : left_val.value.val = 0 :=
      GF16_toGF216_eq_zero_imp left_val (by rw [hlv_get]; exact hv0_zero)
    have hlv_eq_zero : left_val.value = spqr.encoding.gf.GF16.ZERO.value :=
      UScalar.eq_of_val_eq (by simp only [spqr.encoding.gf.GF16.ZERO]; exact hlv_val_zero)
    exact absurd (b_post.mpr hlv_eq_zero) ‹¬b = true›

end spqr.encoding.polynomial.Poly
