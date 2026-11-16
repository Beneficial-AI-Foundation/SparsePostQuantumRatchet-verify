/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Lacramioara Astefanoaei
-/
module

public import SrcTranslated.Funs
public import Spqr.Math.Poly.Basic.Defs
public import Spqr.Math.Poly.Identities.Basic
public import Spqr.Specs.Encoding.Polynomial.PolyEncoder.Defs
import Spqr.Auxiliary.Aeneas.Loop
import Spqr.Auxiliary.Aeneas.EnumerateNext
import Spqr.Auxiliary.Aeneas.Vec
import Spqr.Auxiliary.Aeneas.SpecImpExists
import Spqr.Specs.Aeneas.RangeIteratorNext
import Spqr.Specs.Encoding.Polynomial.Poly.AddAssign
import Spqr.Specs.Encoding.Polynomial.Poly.MultAssign
import Spqr.Specs.Encoding.Polynomial.Poly.Clone
import Spqr.Specs.Encoding.Polynomial.Poly.Zero
import Spqr.Specs.Encoding.Polynomial.ConstPolysToPolys
import Spqr.Specs.Aeneas.ResultExpect
import Spqr.Specs.Encoding.Polynomial.NUM_POLYS

/-! # Slot sizes of a polynomial encoder

The first `next_chunk` call that runs past the stored points of a `PolyEncoder` replaces every
slot by the polynomial that `Poly::from_complete_points` interpolates through it. This module
proves that the polynomial has as many coefficients as the slot had points, so that the slot
size of an encoder is the same before and after the switch.

**Source**: spqr/src/encoding/polynomial.rs:282-332, spqr/src/encoding/polynomial.rs:645-763 -/

@[expose] public section

open Aeneas Aeneas.Std Result WP


namespace spqr.encoding.polynomial.Poly

/-- If `lagrange_sum pts polys` returns `p`, and the first `pts.length` polynomials of `polys`
have `n` coefficients each, then `p` has `n` coefficients, or none when `pts` is empty. -/
theorem lagrange_sum_degree {pts : Slice Pt} {polys : Slice Poly} {p : Poly} {n : Nat}
    (hle : pts.length ≤ polys.length) (hn : n + 2 ≤ Usize.max)
    (hdeg : ∀ i < pts.length, (polys[i]!).degree = n)
    (h : lagrange_sum pts polys = ok p) :
    p.degree = if pts.length = 0 then 0 else n := by
  simp only [lagrange_sum, Result.bind_eq_ok] at h
  obtain ⟨out, hout, h⟩ := h
  have h0 : out.degree = 0 := (post_of_ok (zero_spec _) hout).1
  unfold lagrange_sum_loop at h
  refine loop_ok_post (fun x => x.1.end.val - x.1.start.val)
    (fun x => x.1.end.val = pts.length ∧ x.1.start.val ≤ x.1.end.val ∧
      x.2.degree = if x.1.start.val = 0 then 0 else n)
    (fun y => y.degree = if pts.length = 0 then 0 else n) _ ?_ _ _ ?_ h
  · rintro ⟨it, o⟩ r ⟨hend, hse, hd⟩ hb
    dsimp only at hend hse hd ⊢
    simp only [lagrange_sum_loop.body, Result.bind_eq_ok] at hb
    obtain ⟨⟨op, it1⟩, hnx, hb⟩ := hb
    have hns := post_of_ok (core.iter.range.IteratorRange.next_Usize_spec' it) hnx
    by_cases hlt : it.start.val < it.end.val
    · obtain ⟨hi, hs1, he1⟩ := hns.2 hlt
      subst hi
      simp only [uncurry_apply_pair] at hb
      simp only [Result.bind_eq_ok] at hb
      obtain ⟨q, hq, q1, hq1, q2, hq2, q3, hq3, o1, ho1, hb⟩ := hb
      simp only [ok.injEq] at hb; subst hb
      have hqv : q = polys[it.start.val]! := by
        have := post_of_ok (Slice.index_usize_spec polys it.start (by scalar_tac)) hq
        rw [Slice.getElem!_Nat_eq, getElem!_pos polys.val _ (by scalar_tac)]; exact this
      have hq1v : q1 = q := by have := post_of_ok (clone_spec q) hq1; exact this
      have hqd : q.degree = n := by rw [hqv]; exact hdeg _ (by omega)
      have hq3d : q3.degree = n := by
        rw [(post_of_ok (mult_assign_spec q1 q2.y (by rw [hq1v, hqd]; exact hn)) hq3).1,
          hq1v, hqd]
      have ho1d : o1.degree = max o.degree q3.degree := by
        refine (post_of_ok (add_assign_spec o q3 ?_) ho1).1
        rw [hd, hq3d]; split <;> omega
      dsimp only
      refine ⟨⟨by rw [he1]; exact hend, by rw [he1]; omega, ?_⟩, by rw [he1]; omega⟩
      rw [ho1d, hd, hq3d, hs1]; split <;> simp
    · obtain ⟨rfl, -⟩ := hns.1 hlt
      simp only [uncurry_apply_pair, ok.injEq] at hb; subst hb
      have hse' : it.start.val = it.end.val := by omega
      simp only [hd, hse', hend]
  · refine ⟨by simp [Slice.len], by simp, by simp [h0]⟩

/-- One arm of `from_complete_points`: converting a precomputed basis of `N` polynomials, each with
`N` coefficients, and taking the Lagrange sum over `N` points gives `N` coefficients. -/
theorem arm_degree {N : Usize} {pts : Slice Pt} {a : Std.Array (PolyConst N) N}
    {r : ControlFlow (core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter Pt))
      (core.result.Result Poly Unit)}
    (hN : pts.length = N.val) (hN36 : N.val ≤ 36)
    (h : (do
      let polys ← const_polys_to_polys a
      let p ← lagrange_sum pts (alloc.vec.Vec.deref polys)
      ok (ControlFlow.done (core.result.Result.Ok p))) = ok r) :
    ∃ q, r = .done (.Ok q) ∧ q.degree = pts.length := by
  simp only [Result.bind_eq_ok] at h
  obtain ⟨polys, hp, q, hq, h⟩ := h
  simp only [ok.injEq] at h; subst h
  refine ⟨q, rfl, ?_⟩
  obtain ⟨hlen, hcoef⟩ := post_of_ok (const_polys_to_polys_spec a) hp
  have hdv : (alloc.vec.Vec.deref polys).val = polys.val := by
    simp only [alloc.vec.Vec.deref, Slice.from_val]
  have hd := lagrange_sum_degree (n := N.val) (pts := pts) (polys := alloc.vec.Vec.deref polys)
    (by
      have := hN
      simp only [Slice.length, hdv] at this ⊢
      simp only [alloc.vec.Vec.length] at hlen
      omega)
    (by scalar_tac)
    (fun i hi => by
      have hiN : i < N.val := by omega
      have hil : i < polys.length := by omega
      obtain ⟨hc, -⟩ := hcoef i hiN hil (by simpa using hiN)
      simp only [degree, Slice.getElem!_Nat_eq, hdv]
      rw [getElem!_pos polys.val i (by simpa using hil)]
      simp only [alloc.vec.Vec.length]
      rw [show polys.val[i].coefficients.val.length = _ from congrArg List.length hc]
      simp) hq
  rw [hd]; split <;> omega

/-- If `from_complete_points pts` returns a polynomial, it has `pts.length` coefficients. -/
theorem from_complete_points_degree {pts : Slice Pt} {p : Poly}
    (h : from_complete_points pts = ok (.Ok p)) : p.degree = pts.length := by
  simp only [from_complete_points, core.slice.Slice.iter,
    core.iter.traits.iterator.Iterator.enumerate.trait_default,
    core.iter.traits.iterator.Iterator.enumerate.default, bind_ok] at h
  unfold from_complete_points_loop at h
  refine loop_ok_post (fun x => x.iter.slice.length - x.iter.i) (fun _ => True)
    (fun y => ∀ p, y = .Ok p → p.degree = pts.length) _ ?_ _ _ trivial h p rfl
  rintro it r - hb
  simp only [from_complete_points_loop.body, Result.bind_eq_ok] at hb
  obtain ⟨⟨o, it1⟩, hnx, hb⟩ := hb
  obtain ⟨hsl, hnone, hsome⟩ :=
    Aeneas.Std.core.iter.adapters.enumerate.IteratorEnumerate.next_slice_ok hnx
  cases o with
  | some q =>
    obtain ⟨hlt, hi⟩ := hsome (by simp)
    obtain ⟨k, pt⟩ := q
    simp only [uncurry_apply_pair, Result.bind_eq_ok] at hb
    obtain ⟨i1, -, hb⟩ := hb
    split at hb
    · simp only [ok.injEq] at hb; subst hb; rintro p ⟨⟩
    · simp only [ok.injEq] at hb; subst hb
      refine ⟨trivial, ?_⟩
      rw [hsl, hi]; omega
  | none =>
    simp only [uncurry_apply_pair, Result.bind_eq_ok] at hb
    obtain ⟨i1, hi1, hb⟩ := hb
    have hi1v : i1.val = pts.length := by
      simp only [lift, ok.injEq] at hi1; subst hi1
      rw [UScalar.cast_val_eq, UScalarTy.U64_numBits_eq]
      have hb : (Slice.len pts).val < 2 ^ 64 := by
        have := (Slice.len pts).hBounds
        simp only [UScalarTy.Usize_numBits_eq] at this
        rcases System.Platform.numBits_eq with h | h <;> rw [h] at this <;> omega
      rw [Nat.mod_eq_of_lt hb]; simp [Slice.len, Slice.length]
    split at hb
    · simp only [Result.bind_eq_ok] at hb
      obtain ⟨q, hq, hb⟩ := hb
      simp only [ok.injEq] at hb; subst hb; rintro p ⟨⟩
      have h0 : pts.length = 0 := by rw [← hi1v]; rfl
      rw [lagrange_sum_degree (n := 0) (by simp [h0]) (by scalar_tac)
        (fun i hi => by omega) hq, h0]; rfl
    rotate_left 6
    · simp only [Result.bind_eq_ok] at hb
      obtain ⟨_, -, _, -, hb⟩ := hb
      simp at hb
    all_goals
      obtain ⟨a, -, hb⟩ := Result.bind_eq_ok.mp hb
      obtain ⟨q, rfl, hq⟩ :=
        arm_degree (by rw [← hi1v]; simp only [UScalar.val]; rfl) (by decide) hb
      rintro p ⟨⟩; exact hq

end spqr.encoding.polynomial.Poly

namespace spqr.encoding.polynomial.PolyEncoder

/-- The inner loop of `point_at` pushes one point for every value left in the slice. -/
theorem point_at_loop0_loop0_length
    {it : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter encoding.gf.GF16)}
    {v w : alloc.vec.Vec Pt} (h : point_at_loop0_loop0 it v = ok w) :
    w.length = v.length + (it.iter.slice.length - it.iter.i) := by
  unfold point_at_loop0_loop0 at h
  refine loop_ok_post (fun x => x.1.iter.slice.length - x.1.iter.i)
    (fun x => x.1.iter.slice = it.iter.slice ∧
      x.2.length + (x.1.iter.slice.length - x.1.iter.i) =
        v.length + (it.iter.slice.length - it.iter.i))
    (fun y => y.length = v.length + (it.iter.slice.length - it.iter.i)) _ ?_ _ _
    ⟨rfl, rfl⟩ h
  rintro ⟨it0, v0⟩ r ⟨hs0, hl0⟩ hb
  dsimp only at hs0 hl0 ⊢
  simp only [point_at_loop0_loop0.body, Result.bind_eq_ok] at hb
  obtain ⟨⟨o, it1⟩, hnx, hb⟩ := hb
  obtain ⟨hsl, hnone, hsome⟩ :=
    Aeneas.Std.core.iter.adapters.enumerate.IteratorEnumerate.next_slice_ok hnx
  cases o with
  | none =>
    simp only [uncurry_apply_pair, ok.injEq] at hb; subst hb
    have := hnone rfl
    simp only [Slice.length] at this hl0 ⊢
    omega
  | some q =>
    obtain ⟨hlt, hi⟩ := hsome (by simp)
    obtain ⟨k, y⟩ := q
    simp only [uncurry_apply_pair, Result.bind_eq_ok] at hb
    obtain ⟨i, -, g, -, v1, hv1, hb⟩ := hb
    simp only [ok.injEq] at hb; subst hb
    have hv := alloc.vec.Vec.push_ok_length hv1
    dsimp only
    refine ⟨⟨hsl.trans hs0, ?_⟩, ?_⟩
    · simp only [alloc.vec.Vec.length, hv] at hl0 ⊢
      rw [hsl, hi]; simp only [Slice.length] at hlt hl0 ⊢; omega
    · rw [hsl, hi]; simp only [Slice.length] at hlt ⊢; omega

/-- The loop of `point_at` that interpolates every slot: after it, slot `j` of the result has
as many coefficients as slot `j` of `pts` has points, for every slot the loop visited. -/
theorem point_at_loop0_degree {it : core.ops.range.Range Usize} {pts : Std.Array Point 16#usize}
    {polys polys' : Std.Array Poly 16#usize} (hend : it.end.val = 16)
    (h : point_at_loop0 it pts polys = ok polys') :
    ∀ j, it.start.val ≤ j → j < 16 → (polys'.val[j]!).degree = (pts.val[j]!).value.length := by
  unfold point_at_loop0 at h
  refine loop_ok_post (fun x => x.1.end.val - x.1.start.val)
    (fun x => x.1.end.val = 16 ∧ it.start.val ≤ x.1.start.val ∧
      ∀ j, it.start.val ≤ j → j < x.1.start.val → j < 16 →
        (x.2.val[j]!).degree = (pts.val[j]!).value.length)
    (fun y => ∀ j, it.start.val ≤ j → j < 16 → (y.val[j]!).degree = (pts.val[j]!).value.length)
    _ ?_ _ _ ⟨hend, le_refl _, fun j h1 h2 _ => absurd h2 (by dsimp only; omega)⟩ h
  rintro ⟨it0, ps0⟩ r ⟨he0, hs0, hd0⟩ hb
  dsimp only at he0 hs0 hd0 ⊢
  simp only [point_at_loop0.body, Result.bind_eq_ok] at hb
  obtain ⟨⟨o, it1⟩, hnx, hb⟩ := hb
  have hns := post_of_ok (core.iter.range.IteratorRange.next_Usize_spec' it0) hnx
  by_cases hlt : it0.start.val < it0.end.val
  · obtain ⟨hi, hs1, he1⟩ := hns.2 hlt
    subst hi
    simp only [uncurry_apply_pair] at hb
    simp only [core.slice.Slice.iter, core.iter.traits.iterator.Iterator.enumerate.trait_default,
      core.iter.traits.iterator.Iterator.enumerate.default, bind_ok, Result.bind_eq_ok] at hb
    obtain ⟨pt, hpt, v, hv, res, hres, p1, hp1, -, -, ⟨p2, bk⟩, hbk, hb⟩ := hb
    simp only [uncurry_apply_pair, Result.bind_eq_ok] at hb
    obtain ⟨a, ha, hb⟩ := hb
    simp only [ok.injEq] at hb; subst hb
    have hptv : pt = pts.val[it0.start.val]! := by
      have := post_of_ok (Array.index_usize_spec pts it0.start (by scalar_tac)) hpt
      rw [this, getElem!_pos pts.val _ (by scalar_tac)]
    have hvl := point_at_loop0_loop0_length hv
    obtain rfl := core.result.Result.eq_Ok_of_expect_eq_ok hp1
    have hp1d := Poly.from_complete_points_degree hres
    obtain ⟨-, hbk'⟩ := post_of_ok (Array.index_mut_usize_spec ps0 it0.start (by scalar_tac)) hbk
    subst hbk'
    have hav := post_of_ok (Array.update_spec _ it0.start p1 (by scalar_tac)) ha
    subst hav
    have hp1d' : p1.degree = (pts.val[it0.start.val]!).value.length := by
      rw [hp1d]
      simp only [Slice.length, alloc.vec.Vec.deref, Slice.from_val]
      have := hvl
      simp only [alloc.vec.Vec.length, alloc.vec.Vec.with_capacity, alloc.vec.Vec.new,
        Slice.length, alloc.vec.Vec.deref, Slice.from_val,
        Nat.sub_zero] at this
      rw [this, hptv]
      simp [alloc.vec.Vec.length]
    dsimp only
    refine ⟨⟨by rw [he1]; exact he0, by omega, fun j h1 h2 h3 => ?_⟩, by rw [he1]; omega⟩
    simp only [Array.set_val_eq]
    by_cases hj : j = it0.start.val
    · subst hj
      have hl : it0.start.val < (ps0.val.set it0.start.val p2).length := by
        rw [List.length_set]; scalar_tac
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_set_self hl]; exact hp1d'
    · rw [List.getElem!_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hj),
        List.getElem?_set_ne (Ne.symm hj), ← List.getElem!_eq_getElem?_getD]
      exact hd0 j h1 (by omega) h3
  · obtain ⟨rfl, -⟩ := hns.1 hlt
    simp only [uncurry_apply_pair, ok.injEq] at hb; subst hb
    intro j h1 h2
    exact hd0 j h1 (by omega) h2

/-- Every slot of `e` has `n` entries: `n` points in the `Points` phase, `n` coefficients in the
`Polys` phase. -/
def SlotSize (n : Nat) (e : PolyEncoder) : Prop :=
  (∀ pts, e.s = .Points pts → ∀ j < 16, (pts[j]!).value.length = n) ∧
  (∀ polys, e.s = .Polys polys → ∀ j < 16, (polys[j]!).coefficients.length = n)

/-- A successful `point_at` keeps the slot size. -/
theorem point_at_slotSize {n : Nat} {e e' : PolyEncoder} {poly idx : Usize} {g : encoding.gf.GF16}
    (h : SlotSize n e) (hp : point_at e poly idx = ok (g, e')) : SlotSize n e' := by
  obtain ⟨hpts, hpolys⟩ := h
  unfold point_at at hp
  split at hp
  · rename_i pts hs
    simp only [Result.bind_eq_ok] at hp
    obtain ⟨p, -, hp⟩ := hp
    split at hp
    · simp only [Result.bind_eq_ok] at hp
      obtain ⟨_, -, hp⟩ := hp
      simp only [ok.injEq, Prod.mk.injEq] at hp
      obtain ⟨-, rfl⟩ := hp
      exact ⟨hpts, hpolys⟩
    · simp only [Result.bind_eq_ok] at hp
      obtain ⟨ps, -, k, hk, ps1, hps1, _, -, _, -, _, -, _, -, hp⟩ := hp
      simp only [ok.injEq, Prod.mk.injEq] at hp
      obtain ⟨-, rfl⟩ := hp
      have hk16 : k.val = 16 := by have := post_of_ok NUM_POLYS_spec hk; exact this
      have hd := point_at_loop0_degree (by simpa using hk16) hps1
      refine ⟨fun _ h' => (by cases h'), fun polys' h' j hj => ?_⟩
      cases h'
      have := hd j (by simp) hj
      simp only [Poly.degree] at this
      rw [Array.getElem!_Nat_eq, this, ← Array.getElem!_Nat_eq]
      exact hpts pts hs j hj
  · rename_i polys hs
    simp only [Result.bind_eq_ok] at hp
    obtain ⟨_, -, _, -, _, -, _, -, hp⟩ := hp
    simp only [ok.injEq, Prod.mk.injEq] at hp
    obtain ⟨-, rfl⟩ := hp
    exact ⟨hpts, hpolys⟩

/-- A successful `chunk_at` keeps the slot size. -/
theorem chunk_at_slotSize {n : Nat} {e e' : PolyEncoder} {idx : Std.U16} {c : encoding.Chunk}
    (h : SlotSize n e) (hc : chunk_at e idx = ok (c, e')) : SlotSize n e' := by
  simp only [chunk_at, Result.bind_eq_ok] at hc
  obtain ⟨⟨e1, out⟩, hl, hc⟩ := hc
  simp only [uncurry_apply_pair, Result.bind_eq_ok] at hc
  obtain ⟨_, -, _, -, _, -, hc⟩ := hc
  simp only [ok.injEq, Prod.mk.injEq] at hc
  obtain ⟨-, rfl⟩ := hc
  unfold chunk_at_loop at hl
  refine loop_ok_post (fun x => x.1.end.val - x.1.start.val) (fun x => SlotSize n x.2.1)
    (fun y => SlotSize n y.1) _ ?_ _ _ h hl
  rintro ⟨it0, e0, o0⟩ r h0 hb
  dsimp only at h0 ⊢
  simp only [chunk_at_loop.body, Result.bind_eq_ok] at hb
  obtain ⟨⟨o, it1⟩, hnx, hb⟩ := hb
  have hns := post_of_ok (core.iter.range.IteratorRange.next_Usize_spec' it0) hnx
  by_cases hlt : it0.start.val < it0.end.val
  · obtain ⟨hi, hs1, he1⟩ := hns.2 hlt
    subst hi
    simp only [uncurry_apply_pair, Result.bind_eq_ok] at hb
    obtain ⟨_, -, _, -, _, -, _, -, _, -, ⟨g, e1'⟩, hpa, hb⟩ := hb
    simp only [uncurry_apply_pair, Result.bind_eq_ok] at hb
    obtain ⟨_, -, _, -, _, -, _, -, _, -, hb⟩ := hb
    simp only [ok.injEq] at hb; subst hb
    exact ⟨point_at_slotSize h0 hpa, by rw [he1, hs1]; omega⟩
  · obtain ⟨rfl, -⟩ := hns.1 hlt
    simp only [uncurry_apply_pair, ok.injEq] at hb; subst hb
    exact h0

/-- A successful `next_chunk` keeps the slot size. -/
theorem next_chunk_slotSize {n : Nat} {e e' : PolyEncoder} {c : encoding.Chunk}
    (h : SlotSize n e) (hc : Insts.SpqrEncodingEncoder.next_chunk e = ok (c, e')) :
    SlotSize n e' := by
  simp only [Insts.SpqrEncodingEncoder.next_chunk, Result.bind_eq_ok] at hc
  obtain ⟨_, -, ⟨c1, e1⟩, hca, hc⟩ := hc
  simp only [uncurry_apply_pair, Result.bind_eq_ok] at hc
  obtain ⟨_, -, hc⟩ := hc
  simp only [ok.injEq, Prod.mk.injEq] at hc
  obtain ⟨-, rfl⟩ := hc
  have h1 := chunk_at_slotSize h hca
  exact h1

end spqr.encoding.polynomial.PolyEncoder
