/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

import Spqr.Specs.Encoding.Polynomial.PolyDecoder.NecessaryPoints
import Spqr.Specs.Aeneas.GF16New
import Spqr.Specs.Encoding.Polynomial.Pt.Cmp
import Spqr.Specs.Encoding.Polynomial.Poly.LagrangeInterpolate
import Spqr.Specs.Encoding.Polynomial.Poly.ComputeAt
import Spqr.Auxiliary.Aeneas.Vec
public import Spqr.Math.Poly.Basic.Defs
public import Spqr.Specs.Encoding.Polynomial.PolyDecoder.DecodedMessage.Defs
public import SrcTranslated.Funs

/-!
# Spec theorem for `spqr::encoding::polynomial::
{impl spqr::encoding::Decoder for spqr::encoding::polynomial::PolyDecoder}::decoded_message`

The top-level `decoded_message` function attempts to reconstruct the original plaintext
from the evaluation points collected by the `PolyDecoder`.

The function proceeds in three stages:

  1. **Completeness check**: if `self.is_complete` is `true`, the decoder has already been
     fully consumed and the function returns `none` immediately.
  2. **Sufficiency check** (loop 0): iterates over the 16 polynomial slots (`0..16`) and
     verifies that each slot has accumulated at least `necessary_points(self, i)` evaluation
     points.  If any slot is short, `ret_none` is set to `true` and the function returns
     `none`.
  3. **Reconstruction** (loop 1): iterates over `0..pts_needed`, and for each index
     reconstructs a 16-bit GF(2¹⁶) value (either by direct lookup or by Lagrange
     interpolation), splits it into two bytes (high then low), and appends them to the
     output vector.  The final output has length `2 * pts_needed`.

The function always succeeds (returns `ok`).  The result is:
  • `none` when `self.is_complete` or when some polynomial slot has insufficient points.
  • `some out` where `out.length = 2 * self.pts_needed` otherwise, and the bytes are
    functionally characterised by `BytesDecode self.pts self.pts_needed out.val 0`: for every
    `k < pts_needed`, `(out[2k] * 256 + out[2k+1]).toGF216 = decodedValue self.pts pts_needed k`,
    where `decodedValue` (see `Defs.lean`) is the stored ordinate at abscissa `k / 16` in slot
    `k % 16` if present, and otherwise the Lagrange interpolant through the first
    `necessary_points(k % 16)` stored points of that slot evaluated at `k / 16`.

This file is organised bottom-up:

  1. `decoded_message_loop0.body_spec` — one iteration of the sufficiency check.
  2. `decoded_message_loop0_spec` — the full sufficiency-check loop (with `someIncomplete`).
  3. `decoded_message_loop1.body_spec` — one iteration of the reconstruction loop.
  4. `decoded_message_loop1_spec` — the full reconstruction loop.
  5. `decoded_message_spec` — the top-level theorem.

**Source**: spqr/src/encoding/polynomial.rs, lines 924:4-971:5
-/

@[expose] public section

open Aeneas Aeneas.Std Result spqr.encoding.polynomial

/-! ## Loop body 0: sufficiency check, one iteration

The first loop in `decoded_message` iterates over polynomial indices `0..16` and checks
whether each polynomial slot has enough points to reconstruct the message.  At each step
it examines `pts[i1]` (a `SortedSet<Pt>`) and compares its length against
`necessary_points(self, i1)`:

  • If `pts[i1].len() < necessary_points(self, i1)`, the polynomial is incomplete, so
    `ret_none` is set to `true` (signalling that decoding should return `None`).
  • Otherwise `ret_none` is left unchanged.

When the iterator is exhausted the body returns `done ret_none`.

**Source**: spqr/src/encoding/polynomial.rs, lines 929:8-934:9 -/

namespace spqr.encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.decoded_message_loop0

/-- **Spec theorem for `decoded_message_loop0.body`**:

One iteration of the completeness-check loop.

- **Done case** (iterator exhausted, `next` returns `none`): returns `done ret_none`
  with `ret_none` unchanged.
- **Cont case** (`next` returns `some i1`):
    • Let `np := pts_needed / 16 + (if i1 < pts_needed % 16 then 1 else 0)` be
      the number of points required for polynomial `i1`.
    • Let `len` be the length of `pts[i1]` (the sorted set of received points for
      that polynomial).
    • If `len < np`, the polynomial is incomplete and `ret_none'` is set to `true`.
    • Otherwise `ret_none'` is left equal to the incoming `ret_none`.
    • The iterator advances to `iter'` and the body returns `cont (iter', ret_none')`. -/
@[step]
theorem body_spec
    (i : Usize)
    (a : Array (sorted_vec.SortedSet Pt) 16#usize)
    (b : Bool) (iter : core.ops.range.Range Usize) (ret_none : Bool)
    (h_start_bound : iter.start.val < 16 := by scalar_tac) :
    body i a b iter ret_none ⦃ cf =>
      match cf with
      | ControlFlow.done ret_none' =>
          ret_none' = ret_none ∧ ¬(iter.start < iter.end)
      | ControlFlow.cont (iter', ret_none') =>
          iter.start < iter.end ∧
          iter'.start.val = iter.start.val + 1 ∧
          iter'.end = iter.end ∧
          (let np := i.val / 16 + if iter.start.val < i.val % 16 then 1 else 0
           if (a.val[iter.start.val]'(by simp; omega)).length < np then
             ret_none' = true
           else
             ret_none' = ret_none) ⦄ := by
  unfold body
  step*
  all_goals (first | simp_all only [Option.some.injEq, reduceCtorEq, false_and, ite_false_right,
    Array.length, Array.property, UScalar.ofNatCore_val_eq] <;> scalar_tac | scalar_tac | grind)

end spqr.encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.decoded_message_loop0

/-! ## Loop 0: sufficiency check, full loop

The result is `true` iff the incoming `ret_none` is `true` or some polynomial slot in
`[iter.start, 16)` has fewer evaluation points than `necessary_points` requires.

The proof lifts `body_spec` via `loop.spec_decr_nat` with measure `16 - iter.start`.

**Source**: spqr/src/encoding/polynomial.rs, lines 929:8-934:9 -/

namespace spqr.encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder

/-- Predicate: some polynomial in `[lo, hi)` has fewer points than needed. -/
def someIncomplete
    (a : Array (sorted_vec.SortedSet Pt) 16#usize)
    (pts_needed : Usize) (lo hi : Nat) : Prop :=
  ∃ j, ∃ (_ : j < 16), lo ≤ j ∧ j < hi ∧
    (a.val[j]'(by simp; omega)).length <
      pts_needed.val / 16 + if j < pts_needed.val % 16 then 1 else 0

/-- **Spec theorem for `decoded_message_loop0`**:

The full loop over `iter = { start, end }` with `end = 16`.  Each iteration examines
polynomial slot `iter.start` and sets `ret_none` to `true` if that slot has fewer
evaluation points than `necessary_points` requires.

The result satisfies:

  `result = true ↔ ret_none = true ∨
      ∃ j, iter.start.val ≤ j ∧ j < 16 ∧
        (a.val[j]).length <
          i.val / 16 + if j < i.val % 16 then 1 else 0`

When the range is empty (`iter.start ≥ iter.end`) the result is just `ret_none`. -/
@[step]
theorem decoded_message_loop0_spec
    (iter : core.ops.range.Range Usize)
    (i : Usize)
    (a : Array (sorted_vec.SortedSet Pt) 16#usize)
    (b : Bool) (ret_none : Bool)
    (h_end : iter.end = 16#usize)
    (h_start_le : iter.start.val ≤ 16) :
    decoded_message_loop0 iter i a b ret_none ⦃ (result : Bool) =>
      result = true ↔ ret_none = true ∨
        someIncomplete a i iter.start.val 16 ⦄ := by
  unfold decoded_message_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : core.ops.range.Range Usize × Bool) => 16 - p.1.start.val)
    (inv := fun (p : core.ops.range.Range Usize × Bool) =>
      p.1.start.val ≤ 16 ∧
      p.1.end = 16#usize ∧
      iter.start.val ≤ p.1.start.val ∧
      (p.2 = true ↔ ret_none = true ∨
        someIncomplete a i iter.start.val p.1.start.val))
  · intro p hinv
    obtain ⟨h_le, h_end', h_iter_le, h_inv⟩ := hinv
    by_cases hLt : p.1.start.val < 16
    · -- Iterator not exhausted: use body_spec
      have hspec := decoded_message_loop0.body_spec i a b p.1 p.2 hLt
      apply WP.spec_mono hspec
      intro cf hcf
      match cf with
      | .done r =>
        simp only at hcf
        obtain ⟨hr, hne⟩ := hcf
        subst hr
        have h_ge : p.1.start.val ≥ 16 := by
          simp [UScalar.lt_equiv, h_end'] at hne; omega
        omega
      | .cont x' =>
        simp only at hcf
        obtain ⟨_, hstart1, hend1, hbody⟩ := hcf
        refine ⟨⟨by omega, hend1 ▸ h_end', by omega, ?_⟩, by omega⟩
        simp only [hstart1]
        simp only [someIncomplete] at h_inv ⊢
        constructor
        · intro hr
          by_cases hc : (a.val[p.1.start.val]'(by simp; omega)).length <
              i.val / 16 + if p.1.start.val < i.val % 16 then 1 else 0
          · exact Or.inr ⟨p.1.start.val, hLt, by omega, by omega, hc⟩
          · simp only [hc, ↓reduceIte] at hbody
            rw [hbody] at hr
            cases h_inv.mp hr with
            | inl h => exact Or.inl h
            | inr h =>
              obtain ⟨j, hj16, hj1, hj2, hj3⟩ := h
              exact Or.inr ⟨j, hj16, hj1, by omega, hj3⟩
        · intro hr
          by_cases hc : (a.val[p.1.start.val]'(by simp; omega)).length <
              i.val / 16 + if p.1.start.val < i.val % 16 then 1 else 0
          · simp only [hc, ↓reduceIte] at hbody; exact hbody ▸ rfl
          · simp only [hc, ↓reduceIte] at hbody; rw [hbody]
            apply h_inv.mpr
            cases hr with
            | inl h => exact Or.inl h
            | inr h =>
              obtain ⟨j, hj16, hj1, hj2, hj3⟩ := h
              by_cases hj : j = p.1.start.val
              · subst hj; exact absurd hj3 hc
              · exact Or.inr ⟨j, hj16, hj1, by omega, hj3⟩
    · -- Iterator exhausted (start = 16 = end): body returns done p.2
      have h_eq : p.1.start.val = 16 := by omega
      -- The body calls IteratorRange.next, which returns none since start ≥ end,
      -- then returns done p.2. We need to show the postcondition.
      -- Since someIncomplete ... 16 ↔ someIncomplete ... p.1.start.val (as p.1.start.val = 16),
      -- and h_inv already gives us the iff for p.1.start.val, the postcondition follows.
      unfold decoded_message_loop0.body
      step*
  · refine ⟨h_start_le, h_end, le_refl _, ?_⟩
    simp only [someIncomplete]
    constructor
    · intro h; exact Or.inl h
    · intro h; cases h with
      | inl h => exact h
      | inr h => obtain ⟨j, _, _, hj2, _⟩ := h; omega

end spqr.encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder

/-! ## Loop body 1: reconstruction, one iteration

The second loop in `decoded_message` iterates over `0..pts_needed` and reconstructs
the encoded message two bytes at a time.  At each step the body:

  1. Computes `poly = i1 % 16` (the polynomial index) and `poly_idx = i1 / 16`
     (the evaluation point index).
  2. Constructs a GF(2¹⁶) element `g = GF16::new(poly_idx as u16)`.
  3. Performs a binary search for the point `(g, GF16::ZERO)` in the sorted set
     `pts[poly]` to check whether an evaluation at `g` was already received.

     • **Found case** (`Ok i3`): the y-coordinate of the stored point `pts[poly][i3].y`
       is used directly.
     • **Not-found case** (`Err _`): the polynomial for slot `poly` is lazily
       constructed via `Poly::lagrange_interpolate` (if not already cached in `polys`)
       and then evaluated at `g` via `Poly::compute_at`.

  4. Splits the resulting 16-bit GF16 value `y` into two bytes:
       `(y.value >> 8) as u8` (high byte) and `y.value as u8` (low byte),
     and pushes both onto the output vector `out`.
  5. Returns `cont (iter', polys', out')` to continue looping, or `done out`
     when the iterator is exhausted.

**Source**: spqr/src/encoding/polynomial.rs, lines 944:8-969:9 -/

namespace spqr.encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.decoded_message_loop1

/-- **Spec theorem for `decoded_message_loop1.body`**:

One iteration of the message-reconstruction loop.

- **Done case** (iterator exhausted, `next` returns `none`): returns `done out`
  with the output vector unchanged.
- **Cont case** (`next` returns `some i1`):
    • Let `poly := i1 % 16` and `poly_idx := i1 / 16`.
    • Constructs `g := GF16.new (poly_idx.cast .U16)`.
    • Performs a binary search for `{ x := g, y := GF16.ZERO }` in `pts[poly]`.
    • Determines the GF16 value `y` either from the stored point (found case) or
      by lazily computing the Lagrange interpolation polynomial and evaluating it
      (not-found case).
    • Appends the high byte `(y.value >>> 8).cast .U8` and the low byte
      `y.value.cast .U8` to `out`.
    • The iterator advances to `iter'` and the body returns
      `cont (iter', polys', out')`.

**Functional correctness.**  Besides the length bookkeeping, the postcondition states:
    • `out'.val = out.val ++ [hi, lo]` where
      `(hi * 256 + lo).toGF216 = decodedValue a i iter.start` — the two appended bytes are
      the big-endian encoding of the model value `decodedValue` (see `Defs.lean`);
    • the lazy cache stays consistent (`CacheOk a i polys'`): every cached polynomial is the
      Lagrange interpolant of the first `necessaryPoints` points of its slot.

The proof unfolds `body`, replaces the generic `binary_search` spec by the `lookupY`
characterisation (`binary_search_Pt_spec`), and discharges the found / not-found branches. -/
@[step]
theorem body_spec
    (i : Usize)
    (a : Array (sorted_vec.SortedSet Pt) 16#usize)
    (b : Bool) (iter : core.ops.range.Range Usize)
    (polys : Array (Option Poly) 16#usize)
    (out : alloc.vec.Vec U8)
    (h_i_bound : i.val ≤ Usize.max := by scalar_tac)
    (h_poly_bound : iter.start.val % 16 < 16 := by omega)
    (h_out_cap : out.length + 2 ≤ Usize.max := by scalar_tac)
    (h_enough : ∀ j (hj : j < 16),
      i.val / 16 + (if j < i.val % 16 then 1 else 0) ≤
        (a.val[j]'(by simp; omega)).length)
    (h_polys : ∀ j (hj : j < 16) (p : Poly),
      polys.val[j]'(by simp; omega) = some p → p.degree + 1 ≤ Usize.max)
    (h_cache : CacheOk a i polys) :
    body i a b iter polys out ⦃ cf =>
      match cf with
      | ControlFlow.done out' =>
          out' = out ∧ ¬(iter.start < iter.end)
      | ControlFlow.cont (iter', polys', out') =>
          iter.start < iter.end ∧
          iter'.start.val = iter.start.val + 1 ∧
          iter'.end = iter.end ∧
          out'.length = out.length + 2 ∧
          (∀ j (hj : j < 16) (p : Poly),
            polys'.val[j]'(by simp; omega) = some p → p.degree + 1 ≤ Usize.max) ∧
          CacheOk a i polys' ∧
          (∃ hi lo : U8, out'.val = out.val ++ [hi, lo] ∧
            (hi.val * 256 + lo.val).toGF216 = decodedValue a i iter.start.val) ⦄ := by
  have h_cmp : ∀ a b : Pt, ∃ o, Pt.Insts.CoreCmpOrd.cmp a b = ok o := fun a b =>
    let ⟨o, h, _⟩ := WP.spec_imp_exists (Pt.Insts.CoreCmpOrd.cmp_spec a b)
    ⟨o, h⟩
  unfold body
  step
  split
  · -- iterator exhausted: `o = none`
    rename_i h_none
    simp only [WP.spec_ok, true_and]
    intro h
    simp only [UScalar.lt_equiv] at h
    simp only [h, ite_true] at o_post
    simp_all
  rename_i i1
  step; step; step; step; step; step; step
  step with binary_search_Pt_spec v.deref g as ⟨r, r_post⟩
  -- The iterator produced `some i1`, hence the range was non-empty and `i1 = iter.start`.
  have h_iter : iter.start.val < iter.end.val := by
    by_contra h
    simp only [h, ite_false] at o_post
    simp_all
  have h_i1 : i1 = iter.start := by
    simp only [h_iter, ite_true] at o_post
    simp_all
  have h_iter1 : iter1.start.val = iter.start.val + 1 := by
    simp only [h_iter, ite_true] at o_post
    exact o_post.2
  subst h_i1 sv_post v_post ss_post
  -- Bounds on the stored point set for slot `poly`.
  have h_poly16 : poly.val < 16 := by scalar_tac
  have h_len : (a.val[poly.val]'(by simp; omega)).length ≤ Usize.max :=
    (a.val[poly.val]'(by simp; omega)).property
  have h_need : i.val / 16 + (if poly.val < i.val % 16 then 1 else 0) ≤
      (a.val[poly.val]'(by simp; omega)).length := h_enough poly.val h_poly16
  have h_need_lt : i.val / 16 + (if poly.val < i.val % 16 then 1 else 0) < Usize.max := by
    split <;> omega
  -- The abscissa searched for is `(iter.start / 16) % 2^16`.
  have h_gval : g.value.val = (iter.start.val / 16) % 2 ^ 16 := by
    rename_i i2_post'
    simp only [i2_post, i2_post', UScalar.cast_val_eq, UScalarTy.U16_numBits_eq, poly_idx_post]
  -- Unfold the model once, specialised to this iteration.
  have h_model : decodedValue a i iter.start.val =
      match lookupY (a.val[poly.val]'(by simp; omega)).val g.value.val with
      | some y => y.toGF216
      | none =>
        (lagrangeInterpolantSum ((a.val[poly.val]'(by simp; omega)).val.take
            (necessaryPoints i poly.val)) (necessaryPoints i poly.val)).eval
          g.value.val.toGF216 := by
    simp only [decodedValue, h_gval, poly_post]
    rfl
  -- Main step: the computed `y` satisfies `y.toGF216 = decodedValue …`, the cache stays OK.
  have h_y : (match r with
      | core.result.Result.Ok i3 => do
        let sv1 ← sorted_vec.SortedSet.Insts.CoreOpsDerefDerefSortedVec.deref
          Pt.Insts.CoreCmpOrd (a.val[poly.val]'(by simp; omega))
        let v1 ← sorted_vec.SortedVec.Insts.CoreOpsDerefDerefVec.deref Pt.Insts.CoreCmpOrd sv1
        let p ← alloc.vec.Vec.index_usize v1 i3
        ok (polys, p.y)
      | core.result.Result.Err _ => do
        let o1 ← Array.index_usize polys poly
        if o1.isNone = true then do
          let sv1 ← sorted_vec.SortedSet.Insts.CoreOpsDerefDerefSortedVec.deref
            Pt.Insts.CoreCmpOrd (a.val[poly.val]'(by simp; omega))
          let v1 ← sorted_vec.SortedVec.Insts.CoreOpsDerefDerefVec.deref Pt.Insts.CoreCmpOrd sv1
          let s1 ← alloc.vec.Vec.as_slice Global v1
          let i3 ← encoding.polynomial.PolyDecoder.necessary_points
            { pts_needed := i, pts := a, is_complete := b } poly
          let points ← core.slice.index.SliceIndexRangeToUsizeSlice.index { «end» := i3 } s1
          let p ← encoding.polynomial.Poly.lagrange_interpolate points
          massert (poly < 16#usize)
          let (o2, index_mut_back) ← Array.index_mut_usize polys poly
          let polys3 ← Array.update (index_mut_back o2) poly (some p)
          let o3 ← Array.index_usize polys3 poly
          let o4 ← core.option.Option.as_ref o3
          let p1 ← core.option.Option.expect o4 (toStr "already computed lazily")
          let y1 ← encoding.polynomial.Poly.compute_at p1 g
          ok (polys3, y1)
        else do
          let o2 ← core.option.Option.as_ref o1
          let p ← core.option.Option.expect o2 (toStr "already computed lazily")
          let y1 ← encoding.polynomial.Poly.compute_at p g
          ok (polys, y1)) ⦃ (res : Array (Option Poly) 16#usize × spqr.encoding.gf.GF16) =>
        (∀ j (hj : j < 16) (p : Poly),
          res.1.val[j]'(by simp; omega) = some p → p.degree + 1 ≤ Usize.max) ∧
        CacheOk a i res.1 ∧
        res.2.toGF216 = decodedValue a i iter.start.val ⦄ := by
    rw [h_model]
    rcases r with i3 | i3
    · -- found case: `pts[poly][i3].y` is used directly
      obtain ⟨hi3, hl⟩ := r_post
      simp only [alloc.vec.Vec.deref, Slice.from_val] at hi3 hl
      rw [hl]
      step*
    · -- not-found case: lazily interpolate (if needed) and evaluate
      simp only [alloc.vec.Vec.deref, Slice.from_val] at r_post
      rw [r_post]
      step with Array.index_usize_spec polys poly as ⟨o1, o1_post⟩
      split
      · -- polynomial not yet cached: interpolate, store, evaluate
        rename_i h_none
        step*
        -- the slot was just written, so `expect` finds `some p`
        have h_polys3 : polys3.val[poly.val]'(by simp; omega) = some p := by
          rw [polys3_post, index_mut_back_post]
          simp only [Array.set_val_eq, List.getElem_set_self]
        have h_o4 : o4.isSome := by rw [o4_post, o3_post, h_polys3]; rfl
        step with core.option.Option.expect.spec o4 _ h_o4 as ⟨p1, hp1⟩
        have hp1' : p1 = p := by
          rw [o4_post, o3_post, h_polys3] at hp1
          exact (Option.some.injEq _ _).mp hp1 |>.symm
        subst hp1'
        have h_p_deg : p1.degree + 1 ≤ Usize.max := by
          rw [p_post, points_post1]; omega
        step with Poly.compute_at_spec p1 g as ⟨y, hy⟩
        -- the interpolated points are exactly the first `necessaryPoints` points of slot `poly`
        have h_pts : points.val = (a.val[poly.val]'(by simp; omega)).val.take
            (necessaryPoints i poly.val) := by
          rw [points_post, s1_post, v1_post, sv1_post, List.slice_zero_j, i3_post]
          rfl
        have h_np_len : points.length = necessaryPoints i poly.val := by
          rw [points_post1, i3_post]; rfl
        refine ⟨?_, ?_, ?_⟩
        · intro j hj q hq
          rw [polys3_post, index_mut_back_post] at hq
          simp only [Array.set_val_eq, List.getElem_set] at hq
          by_cases hjp : poly.val = j
          · simp only [hjp, ite_true, Option.some.injEq] at hq
            subst hq
            exact h_p_deg
          · simp only [hjp, ite_false] at hq
            exact h_polys j hj q hq
        · intro j hj q hq
          rw [polys3_post, index_mut_back_post] at hq
          simp only [Array.set_val_eq, List.getElem_set] at hq
          by_cases hjp : poly.val = j
          · simp only [hjp, ite_true, Option.some.injEq] at hq
            subst hq
            rw [p_post2, h_pts, h_np_len]
            subst hjp
            rfl
          · simp only [hjp, ite_false] at hq
            exact h_cache j hj q hq
        · rw [hy, Poly.evalAt, p_post2, h_pts, h_np_len]
          rfl
      · -- polynomial already cached: evaluate directly
        rename_i h_some
        step with core.option.Option.as_ref_spec o1 as ⟨o2, o2_post⟩
        step with core.option.Option.expect.spec o2 _ as ⟨p, hp⟩
        · simp_all [Option.isSome_iff_ne_none]
        have hp_eq : polys.val[poly.val]'(by simp; omega) = some p := by
          rw [← o1_post, ← o2_post]; exact hp
        have h_deg : p.degree + 1 ≤ Usize.max := h_polys poly.val h_poly16 p hp_eq
        step with Poly.compute_at_spec p g as ⟨y, hy⟩
        refine ⟨h_polys, h_cache, ?_⟩
        rw [hy, Poly.evalAt, h_cache poly.val h_poly16 p hp_eq]
        rfl
  apply WP.spec_bind h_y
  rintro ⟨polys1, y⟩ ⟨h_polys1, h_cache1, h_yval⟩
  simp only at h_polys1 h_cache1 h_yval
  step*
  · scalar_tac
  refine ⟨by scalar_tac, h_iter1, o_post1, by simp_all, h_polys1, h_cache1, i4, i5, ?_, ?_⟩
  · simp only [out2_post, out1_post, List.append_assoc, List.singleton_append]
  · rw [← h_yval]
    unfold spqr.encoding.gf.GF16.toGF216
    congr 1
    have hyb : y.value.val < 2 ^ 16 := by scalar_tac
    simp only [i5_post, i4_post, i3_post, UScalar.cast_val_eq, UScalarTy.U8_numBits_eq,
      Nat.shiftRight_eq_div_pow]
    omega

end spqr.encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.decoded_message_loop1

/-! ## Loop 1: reconstruction, full loop

The proof lifts `body_spec` via `loop.spec_decr_nat` with measure
`iter.end.val - iter.start.val`.

**Source**: spqr/src/encoding/polynomial.rs, lines 944:8-969:9 -/

namespace spqr.encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder

/-- **Spec theorem for `decoded_message_loop1`**:

The full loop over `iter = { start, end }` with `end = pts_needed`.  Each iteration
reconstructs two bytes of the message from the corresponding polynomial evaluation
point and appends them to the output vector `out`.

The result satisfies:

  `result.length = out.length + 2 * (pts_needed.val - iter.start.val)`

and, functionally, `result.val = out.val ++ bs` where `bs` has exactly
`2 * (pts_needed - iter.start)` bytes and `BytesDecode a pts_needed bs iter.start`:
the byte pair `(bs[2k], bs[2k+1])` is the big-endian encoding of
`decodedValue a pts_needed (iter.start + k)`.

The precondition `CacheOk a pts_needed polys` requires every polynomial already cached in
`polys` to be the Lagrange interpolant of the first `necessaryPoints` points of its slot
(trivially true for the all-`none` initial cache).

When the range is empty (`iter.start ≥ iter.end`) the result is just `out`. -/
@[step]
theorem decoded_message_loop1_spec
    (iter : core.ops.range.Range Usize)
    (i : Usize)
    (a : Array (sorted_vec.SortedSet Pt) 16#usize)
    (b : Bool) (polys : Array (Option Poly) 16#usize)
    (out : alloc.vec.Vec U8)
    (h_end : iter.end = i)
    (h_start_le : iter.start.val ≤ i.val)
    (h_out_cap : out.length + 2 * (i.val - iter.start.val) ≤ Usize.max)
    (h_enough : ∀ j (hj : j < 16),
      i.val / 16 + (if j < i.val % 16 then 1 else 0) ≤
        (a.val[j]'(by simp; omega)).length)
    (h_polys : ∀ j (hj : j < 16) (p : Poly),
      polys.val[j]'(by simp; omega) = some p →
        p.degree + 1 ≤ Usize.max)
    (h_cache : CacheOk a i polys) :
    decoded_message_loop1 iter i a b polys out ⦃ (result : alloc.vec.Vec U8) =>
      result.length = out.length + 2 * (i.val - iter.start.val) ∧
      ∃ bs : List U8, result.val = out.val ++ bs ∧
        bs.length = 2 * (i.val - iter.start.val) ∧
        BytesDecode a i bs iter.start.val ⦄ := by
  unfold decoded_message_loop1
  apply loop.spec_decr_nat
    (measure := fun (p : core.ops.range.Range Usize × Array (Option Poly) 16#usize ×
      alloc.vec.Vec U8) => i.val - p.1.start.val)
    (inv := fun (p : core.ops.range.Range Usize × Array (Option Poly) 16#usize ×
      alloc.vec.Vec U8) =>
      p.1.start.val ≤ i.val ∧
      p.1.end = i ∧
      iter.start.val ≤ p.1.start.val ∧
      p.2.2.length = out.length + 2 * (p.1.start.val - iter.start.val) ∧
      p.2.2.length + 2 * (i.val - p.1.start.val) ≤ Usize.max ∧
      (∀ j (hj : j < 16) (q : Poly),
        p.2.1.val[j]'(by simp; omega) = some q →
          q.degree + 1 ≤ Usize.max) ∧
      CacheOk a i p.2.1 ∧
      (∃ bs : List U8, p.2.2.val = out.val ++ bs ∧
        bs.length = 2 * (p.1.start.val - iter.start.val) ∧
        BytesDecode a i bs iter.start.val))
  · intro ⟨iter', polys', out'⟩ hinv
    obtain ⟨h_le, h_end', h_iter_le, h_len, h_cap, h_polys', h_cache', bs, h_bs, h_bs_len,
      h_bs_dec⟩ := hinv
    simp only at h_le h_end' h_iter_le h_len h_cap h_polys' h_cache' h_bs h_bs_len h_bs_dec ⊢
    by_cases hLt : iter'.start.val < i.val
    · have h_out_cap' : out'.length + 2 ≤ Usize.max := by
        have h1 : 2 * (i.val - iter'.start.val) ≥ 2 := by omega
        linarith
      have hspec := decoded_message_loop1.body_spec i a b iter' polys' out'
        (by scalar_tac) (by omega) h_out_cap' h_enough h_polys' h_cache'
      apply WP.spec_mono hspec
      intro cf hcf
      match cf with
      | .done r =>
        simp only at hcf
        obtain ⟨hr, hne⟩ := hcf
        subst hr
        have h_ge : iter'.start.val ≥ i.val := by
          simp [UScalar.lt_equiv] at hne; grind
        omega
      | .cont ⟨iter1, polys1, out1⟩ =>
        simp only at hcf
        obtain ⟨_, hstart1, hend1, hout1_len', h_polys1, h_cache1, hi, lo, hout1_val, h_pair⟩ :=
          hcf
        have hstart1_val : iter1.start.val = iter'.start.val + 1 := hstart1
        have hend1_eq : iter1.end = i := hend1 ▸ h_end'
        refine ⟨⟨by grind, hend1_eq, by grind, ?_, ?_, h_polys1, h_cache1, bs ++ [hi, lo],
          ?_, ?_, ?_⟩, by grind⟩
        · -- out1.length = out.length + 2 * (iter1.start.val - iter.start.val)
          have h2 : iter1.start.val - iter.start.val = (iter'.start.val - iter.start.val) + 1 :=
            by omega
          rw [hout1_len', h_len, h2]; ring
        · -- out1.length + 2 * (i.val - iter1.start.val) ≤ Usize.max
          have h2 : 2 * (i.val - iter'.start.val) =
            2 + 2 * (i.val - iter1.start.val) := by omega
          linarith
        · rw [hout1_val, h_bs, List.append_assoc]
        · simp only [List.length_append, List.length_cons, List.length_nil, h_bs_len]; omega
        · have h_n : iter'.start.val = iter.start.val + (iter'.start.val - iter.start.val) := by
            omega
          rw [h_n] at h_pair
          exact BytesDecode_append a i bs iter.start.val (iter'.start.val - iter.start.val)
            hi lo h_bs_len h_bs_dec h_pair
    · have h_eq : iter'.start.val ≥ i.val := by omega
      unfold decoded_message_loop1.body
      step*
  · refine ⟨h_start_le, h_end, le_refl _, ?_, h_out_cap, h_polys, h_cache, [], by simp, by simp,
      BytesDecode_nil a i iter.start.val⟩
    simp only; omega

end spqr.encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder

/-! ## Top-level theorem

**Source**: spqr/src/encoding/polynomial.rs, lines 924:4-971:5 -/

namespace spqr.encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder

/-- **Spec theorem for `spqr.encoding.polynomial.PolyDecoder.Insts.
SpqrEncodingDecoder.decoded_message`**:

• If `self.is_complete = true`, the result is `none`.
• If any polynomial slot `j ∈ [0, 16)` has fewer evaluation points than
  `pts_needed / 16 + (if j < pts_needed % 16 then 1 else 0)`, the result is `none`.
• Otherwise the result is `some out` where `out.length = 2 * self.pts_needed.val` and
  `BytesDecode self.pts self.pts_needed out.val 0` (each big-endian byte pair is the decoded
  GF(2¹⁶) value `decodedValue self.pts self.pts_needed k`).

The proof unfolds `decoded_message`, dispatches the completeness guard, applies
`decoded_message_loop0_spec` for the sufficiency check, handles the `from_fn` initialisation
of the lazy polynomial cache, and applies `decoded_message_loop1_spec` for the reconstruction
loop.

**Source**: spqr/src/encoding/polynomial.rs, lines 924:4-971:5
-/
@[step]
theorem decoded_message_spec (self : encoding.polynomial.PolyDecoder)
    (h_out_cap : 2 * self.pts_needed.val ≤ Usize.max) :
    decoded_message self ⦃ (result : Option (alloc.vec.Vec U8)) =>
      match result with
      | none => self.is_complete = true ∨
          someIncomplete self.pts self.pts_needed 0 16
      | some out => self.is_complete = false ∧
          ¬someIncomplete self.pts self.pts_needed 0 16 ∧
          out.length = 2 * self.pts_needed.val ∧
          BytesDecode self.pts self.pts_needed out.val 0 ⦄ := by
  unfold decoded_message
  step*
  case l => exact List.replicate 16 none
  case hl =>
    apply core.array.from_fn_loop_replicate_default
    · intro i
      open DecoderPolyDecoder.decoded_message.closure.Insts in
      simp [CoreOpsFunctionFnMutTupleUsizeOptionPoly.call_mut]
      rfl
    · scalar_tac
  case hlen => simp
  -- Remaining: reconstruction via loop 1
  step
  rename_i i1 i1_post
  have h_not_inc : ¬someIncomplete self.pts self.pts_needed 0 16 := by simp_all
  have h_enough' : ∀ j (hj : j < 16),
      self.pts_needed.val / 16 + (if j < self.pts_needed.val % 16 then 1 else 0) ≤
        (self.pts.val[j]'(by simp; omega)).length := by
    intro j hj
    by_contra hlt
    exact h_not_inc ⟨j, hj, by omega, hj, by omega⟩
  have h_cap0 : (alloc.vec.Vec.with_capacity U8 i1).length = 0 := by
    simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new]
  have h_val0 : (alloc.vec.Vec.with_capacity U8 i1).val = [] := by
    simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new]
  have h_polys_none : ∀ j (hj : j < 16) (p : Poly),
      polys.val[j]'(by simp; omega) = some p → False := by
    intro j hj p hp; simp only [polys_post, List.getElem_replicate] at hp; cases hp
  have hspec := decoded_message_loop1_spec
    { start := 0#usize, «end» := self.pts_needed } self.pts_needed self.pts false polys
    (alloc.vec.Vec.with_capacity U8 i1) rfl (by simp) (by rw [h_cap0]; simp; omega) h_enough'
    (fun j hj p hp => (h_polys_none j hj p hp).elim)
    (fun j hj p hp => (h_polys_none j hj p hp).elim)
  apply WP.spec_bind hspec
  rintro out1 ⟨hout1, bs, hbs, _, hdec⟩
  simp only [h_val0, alloc.vec.Vec.length, List.nil_append] at hout1 hbs
  subst hbs
  step*

end spqr.encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder
