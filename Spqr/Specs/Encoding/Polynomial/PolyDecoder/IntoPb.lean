/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import Spqr.Math.Poly.ModByMonic
public import Spqr.Specs.Aeneas.SliceIteratorNext
import Spqr.Specs.Encoding.Polynomial.Pt.Serialize
import Spqr.Specs.Aeneas.RangeIteratorNext
import Spqr.Specs.Aeneas.VecExtendFromSlice
public import Spqr.Specs.Encoding.Polynomial.PolyDecoder.NewWithPolyCount
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Order.Int.ConditionallyCompleteOrder
import Spqr.Specs.Aeneas.IndexRangeFull

/-! # Spec theorem for `PolyDecoder::into_pb`: loop body 1

One step of the inner point-serialization loop. Given `pts : SortedSet<Pt>`, a range iterator
`iter`, and byte accumulator `v`, either returns `v` unchanged (range exhausted) or serializes
`pts[iter.start]` into 4 big-endian bytes and appends them to `v`.

**Source**: spqr/src/encoding/polynomial.rs -/

@[expose] public section

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf

instance instInhabitedPt : Inhabited Pt := ⟨{ x := ⟨0#u16⟩, y := ⟨0#u16⟩ }⟩

namespace spqr.encoding.polynomial.PolyDecoder.into_pb_loop0_loop0

/-- **Spec theorem for `encoding.polynomial.PolyDecoder.into_pb_loop0_loop0.body`**:

One step of the inner loop: terminates if the range is exhausted, otherwise serializes
`pts[iter.start]` as 4 big-endian bytes (`b0·256+b1 = x`, `b2·256+b3 = y`) and appends to `v`.

Succeeds when `iter.end ≤ pts.val.length` and `v.length + 4 ≤ Usize.max`.

**Source**: spqr/src/encoding/polynomial.rs -/
@[step]
theorem body_spec
    (pts : sorted_vec.SortedSet Pt)
    (iter : core.ops.range.Range Usize)
    (v : alloc.vec.Vec U8)
    (h_end_le : iter.end ≤ pts.length)
    (h_out_overflow : v.length + 4 ≤ Usize.max) :
    body pts iter v ⦃ cf =>
      match cf with
      | ControlFlow.done v' =>
          v' = v ∧ ¬(iter.start < iter.end)
      | ControlFlow.cont (iter1, v1) =>
          iter.start < iter.end ∧
          iter1.start = iter.start.val + 1 ∧
          iter1.end = iter.end ∧
          ∃ (b0 b1 b2 b3 : U8),
            v1 = v ++ [b0, b1, b2, b3] ∧
            256 * b0 + b1.val = (pts.val[iter.start.val]!).x.value.val ∧
            256 * b2 + b3.val = (pts.val[iter.start.val]!).y.value.val ⦄ := by
  unfold body
  step with core.iter.range.IteratorRange.next_Usize_spec' iter as
    ⟨opt, iter1', h_none, h_some⟩
  by_cases h_lt : iter.start.val < iter.end.val
  · obtain ⟨h_opt, h_start1, h_end1⟩ := h_some h_lt
    subst h_opt
    step as ⟨sv, h_sv⟩
    step as ⟨v1, h_v1⟩
    step as ⟨pt, h_pt⟩
    step as ⟨a, h_x, h_y⟩
    step as ⟨v2, h_v2⟩
    obtain ⟨b0, b1, b2, b3, h_a_eq⟩ : ∃ b0 b1 b2 b3, a.val = [b0, b1, b2, b3] :=
      match a.val, a.property with | [b0, b1, b2, b3], _ => ⟨b0, b1, b2, b3, rfl⟩
    have h_get : pts.val[iter.start.val]! = pt := by
      have : iter.start.val < pts.val.length := by
        have : iter.end.val ≤ pts.val.length := h_end_le
        omega
      subst h_pt h_v1 h_sv
      exact (List.Inhabited_getElem_eq_getElem! (hi := this)).symm
    simp only [Array.getElem!_Nat_eq, h_a_eq] at h_x h_y
    refine ⟨h_lt, h_start1, h_end1, b0, b1, b2, b3, ?_, ?_, ?_⟩
    · rw [h_v2, Array.val_to_slice, h_a_eq]
    · rw [h_get, ← h_x]; simp only [List.getElem!_cons_zero, List.getElem!_cons_succ]; ring
    · rw [h_get, ← h_y]; simp only [List.getElem!_cons_zero, List.getElem!_cons_succ]; ring
  · obtain ⟨h_opt, _⟩ := h_none (by omega)
    subst h_opt
    exact (WP.spec_ok _).mpr ⟨rfl, by omega⟩

/-- Appending four bytes keeps the prefix and places the bytes at `v.length + 0..3`. -/
private lemma vec_append_quad {v v1 : alloc.vec.Vec U8} {b0 b1 b2 b3 : U8}
    (h : v1 = v ++ [b0, b1, b2, b3]) :
    v1.length = v.length + 4 ∧ (∀ p < v.length, v1[p]! = v[p]!) ∧
      v1[v.length]! = b0 ∧ v1[v.length + 1]! = b1 ∧
      v1[v.length + 2]! = b2 ∧ v1[v.length + 3]! = b3 := by
  have h : v1.val = v.val ++ [b0, b1, b2, b3] := h
  simp only [alloc.vec.Vec.getElem!_Nat_eq, alloc.vec.Vec.length, h, List.length_append,
    List.getElem!_eq_getElem?_getD]
  refine ⟨by simp, fun p hp => by rw [List.getElem?_append_left hp], by simp, by simp,
    by simp, by simp⟩

/-- **Spec theorem for `encoding.polynomial.PolyDecoder.into_pb_loop0_loop0`**:

Full inner loop: serializes all points in `pts` into consecutive 4-byte big-endian encodings.

Postcondition: `result.length = 4 * iter.end` and for every `j < iter.end`,
`256 * result[4·j] + result[4·j+1] = pts[j].x.value` and
`256 * result[4·j+2] + result[4·j+3] = pts[j].y.value`.

**Source**: spqr/src/encoding/polynomial.rs -/
@[step]
theorem loop_spec
    (pts : sorted_vec.SortedSet Pt)
    (iter : core.ops.range.Range Usize)
    (v : alloc.vec.Vec U8)
    (h_end_le : iter.end ≤ pts.length)
    (h_out_len : v.length = 4 * iter.start)
    (h_start_le : iter.start ≤ iter.end)
    (h_overflow : 4 * pts.length + 4 ≤ Usize.max)
    (h_pre : ∀ (j : Nat), j < iter.start →
          256 * (v[4 * j]!) + (v[4 * j + 1]!).val = (pts.val[j]!).x.value.val ∧
          256 * (v[4 * j + 2]!) + (v[4 * j + 3]!).val = (pts.val[j]!).y.value.val) :
    into_pb_loop0_loop0 iter pts v ⦃ (result : alloc.vec.Vec U8) =>
      result.length = 4 * iter.end ∧
      ∀ (j : Nat), j < iter.end →
          256 * (result[4 * j]!) + (result[4 * j + 1]!).val = (pts.val[j]!).x.value.val ∧
          256 * (result[4 * j + 2]!) + (result[4 * j + 3]!).val = (pts.val[j]!).y.value.val ⦄ := by
  unfold into_pb_loop0_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : core.ops.range.Range Usize × alloc.vec.Vec U8) =>
                  p.1.end - p.1.start)
    (inv := fun (p : core.ops.range.Range Usize × alloc.vec.Vec U8) =>
        p.1.end = iter.end ∧
        p.1.start ≤ p.1.end ∧
        p.2.length = 4 * p.1.start ∧
        (∀ (j : Nat), j < p.1.start →
            256 * (p.2[4 * j]!) + (p.2[4 * j + 1]!).val = (pts.val[j]!).x.value.val ∧
            256 * (p.2[4 * j + 2]!) + (p.2[4 * j + 3]!).val = (pts.val[j]!).y.value.val))
  · rintro ⟨iter', out'⟩ hinv
    dsimp only at hinv
    obtain ⟨h_end', h_start_le', h_out_len', h_pre'⟩ := hinv
    have h_end_val : iter'.end.val = iter.end.val := by rw [h_end']
    have h_end_le' : iter.end.val ≤ pts.val.length := h_end_le
    have h_out_len'' : out'.val.length = 4 * iter'.start.val := h_out_len'
    have h_ovf : 4 * pts.val.length + 4 ≤ Usize.max := h_overflow
    have h_start_le'' : iter'.start.val ≤ iter'.end.val := h_start_le'
    apply WP.spec_mono (body_spec pts iter' out' (by rw [h_end']; exact h_end_le)
      (show out'.val.length + 4 ≤ Usize.max by omega))
    rintro (⟨iter'', out''⟩ | out'') h_cf
    · obtain ⟨h_lt, h_start1, h_end1, b0, b1, b2, b3, h_out_eq, h_x_eq, h_y_eq⟩ := h_cf
      have h_lt' : iter'.start.val < iter'.end.val := h_lt
      obtain ⟨h_len, h_keep, h_0, h_1, h_2, h_3⟩ := vec_append_quad h_out_eq
      have h_len' : out''.val.length = out'.val.length + 4 := h_len
      have h_end1' : iter''.end.val = iter'.end.val := by rw [h_end1]
      dsimp only
      refine ⟨⟨h_end1.trans h_end', show iter''.start.val ≤ iter''.end.val by omega,
        show out''.val.length = 4 * iter''.start.val by omega, fun j hj => ?_⟩,
        show iter''.end.val - iter''.start.val < iter'.end.val - iter'.start.val by omega⟩
      by_cases hj_lt : j < iter'.start.val
      · rw [h_keep _ (by omega), h_keep _ (by omega), h_keep _ (by omega),
          h_keep _ (by omega)]
        exact h_pre' j hj_lt
      · obtain rfl : j = iter'.start.val := by omega
        rw [← h_out_len'', h_0, h_1, h_2, h_3]
        exact ⟨h_x_eq, h_y_eq⟩
    · obtain ⟨rfl, h_nlt⟩ := h_cf
      have : ¬iter'.start.val < iter'.end.val := h_nlt
      have h_eq : iter'.start.val = iter.end.val := by omega
      refine ⟨by rw [h_out_len', h_eq], fun j hj => h_pre' j (by omega)⟩
  · exact ⟨rfl, h_start_le, h_out_len, h_pre⟩

end spqr.encoding.polynomial.PolyDecoder.into_pb_loop0_loop0

/-! # Spec theorem for `PolyDecoder::into_pb`: loop body 0

One step of the outer loop. Given a `Range<usize>` iterator over the indices of the array
`a : [SortedSet<Pt>; 16]` and output accumulator `v : Vec<Vec<u8>>`, either returns `v`
unchanged (iterator exhausted) or serializes all points in `a[i]` into a byte vector and pushes
it onto `v`.

**Source**: spqr/src/encoding/polynomial.rs -/

namespace spqr.encoding.polynomial.PolyDecoder.into_pb_loop0

/-- **Spec theorem for `encoding.polynomial.PolyDecoder.into_pb_loop0.body`**:

One step of the outer loop: terminates if the iterator is exhausted, otherwise serializes all
points in `a[iter.start]` into 4-byte big-endian encodings and pushes the result onto `v`.

Succeeds when `v.length + 1 ≤ Usize.max` and inner loops won't overflow. -/
@[step]
theorem body_spec
    (a : Array (sorted_vec.SortedSet Pt) 16#usize)
    (iter : core.ops.range.Range Usize)
    (v : alloc.vec.Vec (alloc.vec.Vec U8))
    (h_end_le : iter.end ≤ a.val.length)
    (h_out_overflow : v.length + 1 ≤ Usize.max)
    (h_inner_overflow : ∀ j < a.length, 4 * (a.val[j]!).length + 4 ≤ Usize.max) :
    body a iter v ⦃ cf =>
      match cf with
      | ControlFlow.done v' =>
          v' = v ∧ ¬(iter.start < iter.end)
      | ControlFlow.cont (iter1, v1) =>
          iter.start < iter.end ∧
          iter1.start = iter.start.val + 1 ∧
          iter1.end = iter.end ∧
          ∃ (serialized : alloc.vec.Vec U8),
            v1 = v ++ [serialized] ∧
            serialized.length = 4 * (a.val[iter.start.val]!).length ∧
            ∀ (j : Nat), j < (a.val[iter.start.val]!).length →
                256 * (serialized[4 * j]!) + serialized[4 * j + 1]! =
                  ((a.val[iter.start.val]!).val[j]!).x.value.val ∧
                256 * (serialized[4 * j + 2]!) + serialized[4 * j + 3]! =
                  ((a.val[iter.start.val]!).val[j]!).y.value.val ⦄ := by
  unfold body
  step with core.iter.range.IteratorRange.next_Usize_spec' iter as
    ⟨opt, iter1', h_none, h_some⟩
  by_cases h_lt : iter.start.val < iter.end.val
  · obtain ⟨h_opt_eq, h_start1, h_end1⟩ := h_some h_lt
    rw [h_opt_eq]
    have h_j_lt : iter.start.val < a.val.length := by omega
    have h_inner := h_inner_overflow iter.start.val h_j_lt
    have h_getelem : (a.val[iter.start.val]! : sorted_vec.SortedSet Pt) =
        a.val[iter.start.val]'h_j_lt := by
      rw [← List.Inhabited_getElem_eq_getElem! (hi := h_j_lt)]
    step as ⟨pts, h_pts⟩
    rw [← h_getelem] at h_pts
    subst h_pts
    step as ⟨sv, h_sv⟩
    subst h_sv
    -- `SortedSet`/`SortedVec`/`Vec` are plain `def` synonyms: pass the argument explicitly
    step with sorted_vec.SortedVec.Insts.CoreOpsDerefDerefVec.deref_spec _
      a.val[iter.start.val]! as ⟨v1, h_v1⟩
    subst h_v1
    step as ⟨i2, h_i2⟩
    step with sorted_vec.SortedVec.Insts.CoreOpsDerefDerefVec.deref_spec _
      a.val[iter.start.val]! as ⟨v3, h_v3⟩
    subst h_v3
    step with into_pb_loop0_loop0.loop_spec as ⟨v4, h_v4_len, h_v4⟩
    · rfl
    step as ⟨v5, h_v5⟩
    exact ⟨h_lt, h_start1, h_end1, v4, h_v5, h_v4_len, h_v4⟩
  · obtain ⟨h_opt_eq, _⟩ := h_none h_lt
    rw [h_opt_eq]
    exact (WP.spec_ok _).mpr ⟨rfl, h_lt⟩

/-- Pushing `x` keeps the prefix and places `x` at index `v.length`. -/
private lemma vec_push {α : Type} [Inhabited α] {v v1 : alloc.vec.Vec α} {x : α}
    (h : v1.val = v.val ++ [x]) :
    v1.val.length = v.val.length + 1 ∧ (∀ j < v.val.length, v1.val[j]! = v.val[j]!) ∧
      v1.val[v.val.length]! = x := by
  simp only [h, List.length_append, List.length_singleton, List.getElem!_eq_getElem?_getD]
  exact ⟨trivial, fun j hj => by rw [List.getElem?_append_left hj], by simp⟩

/-- **Spec theorem for `encoding.polynomial.PolyDecoder.into_pb_loop0`**:

Full outer loop: serializes the sorted sets `a[iter.start..iter.end]` into byte vectors in the
output accumulator.

Postcondition: `result.length = iter.end` and for every `j < iter.end`,
`(result[j]).length = 4 * (a[j]).length` with each 4-byte chunk encoding the
corresponding point's `(x, y)` in big-endian format.

**Source**: spqr/src/encoding/polynomial.rs -/
@[step]
theorem loop_spec
    (a : Array (sorted_vec.SortedSet Pt) 16#usize)
    (iter : core.ops.range.Range Usize)
    (v : alloc.vec.Vec (alloc.vec.Vec U8))
    (h_end_le : iter.end ≤ a.length)
    (h_start_le : iter.start ≤ iter.end.val)
    (h_out_len : v.length = iter.start)
    (h_out_overflow : a.length + 1 ≤ Usize.max)
    (h_inner_overflow : ∀ j < a.length, 4 * (a.val[j]!).length + 4 ≤ Usize.max)
    (h_pre : ∀ (j : Nat), j < iter.start.val →
          (v[j]!).length = 4 * (a.val[j]!).length ∧
          ∀ (k : Nat), k < (a.val[j]!).length →
              256 * ((v[j]!)[4 * k]!) + ((v[j]!)[4 * k + 1]!) =
                ((a.val[j]!).val[k]!).x.value.val ∧
              256 * ((v[j]!)[4 * k + 2]!) + ((v[j]!)[4 * k + 3]!) =
                ((a.val[j]!).val[k]!).y.value.val) :
    into_pb_loop0 iter a v ⦃ (result : alloc.vec.Vec (alloc.vec.Vec U8)) =>
      result.length = iter.end ∧
      ∀ (j : Nat), j < iter.end.val →
          (result[j]!).length = 4 * (a.val[j]!).length ∧
          ∀ (k : Nat), k < (a.val[j]!).length →
              256 * ((result[j]!)[4 * k]!) + ((result[j]!)[4 * k + 1]!) =
                ((a.val[j]!).val[k]!).x.value.val ∧
              256 * ((result[j]!)[4 * k + 2]!) + ((result[j]!)[4 * k + 3]!) =
                ((a.val[j]!).val[k]!).y.value.val ⦄ := by
  unfold into_pb_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : core.ops.range.Range Usize ×
                       alloc.vec.Vec (alloc.vec.Vec U8)) =>
                  p.1.end - p.1.start)
    (inv := fun (p : core.ops.range.Range Usize ×
                      alloc.vec.Vec (alloc.vec.Vec U8)) =>
        p.1.end = iter.end ∧
        p.1.start ≤ p.1.end ∧
        p.2.length = p.1.start ∧
        (∀ (j : Nat), j < p.1.start.val →
            (p.2[j]!).length = 4 * (a.val[j]!).length ∧
            ∀ (k : Nat), k < (a.val[j]!).length →
                256 * ((p.2[j]!)[4 * k]!) + ((p.2[j]!)[4 * k + 1]!) =
                  ((a.val[j]!).val[k]!).x.value.val ∧
                256 * ((p.2[j]!)[4 * k + 2]!) + ((p.2[j]!)[4 * k + 3]!) =
                  ((a.val[j]!).val[k]!).y.value.val))
  · rintro ⟨iter', v'⟩ hinv
    dsimp only at hinv
    obtain ⟨h_end', h_start_le', h_out_len', h_pre'⟩ := hinv
    have h_end_val : iter'.end.val = iter.end.val := by rw [h_end']
    have h_end_le' : iter.end.val ≤ a.val.length := h_end_le
    have h_start_le'' : iter'.start.val ≤ iter'.end.val := h_start_le'
    have h_out_len'' : v'.val.length = iter'.start.val := h_out_len'
    have h_alen : a.val.length + 1 ≤ Usize.max := h_out_overflow
    apply WP.spec_mono (body_spec a iter' v' (by omega)
      (show v'.val.length + 1 ≤ Usize.max by omega) h_inner_overflow)
    rintro (⟨iter'', v''⟩ | v'') h_cf
    · obtain ⟨h_lt, h_start1, h_end1, serialized, h_v_eq, h_ser_len, h_ser_enc⟩ := h_cf
      have h_lt' : iter'.start.val < iter'.end.val := h_lt
      have h_end1' : iter''.end.val = iter'.end.val := by rw [h_end1]
      obtain ⟨h_len, h_keep, h_last⟩ := vec_push h_v_eq
      dsimp only
      refine ⟨⟨h_end1.trans h_end', show iter''.start.val ≤ iter''.end.val by omega,
        show v''.val.length = iter''.start.val by omega, fun j hj => ?_⟩,
        show iter''.end.val - iter''.start.val < iter'.end.val - iter'.start.val by omega⟩
      by_cases hj_lt : j < iter'.start.val
      · have h_get : v''[j]! = v'[j]! := h_keep j (by omega)
        rw [h_get]
        exact h_pre' j hj_lt
      · obtain rfl : j = iter'.start.val := by omega
        have h_get : v''[v'.val.length]! = serialized := h_last
        rw [h_out_len''] at h_get
        rw [h_get]
        exact ⟨h_ser_len, h_ser_enc⟩
    · obtain ⟨rfl, h_nlt⟩ := h_cf
      have : ¬iter'.start.val < iter'.end.val := h_nlt
      have h_eq : iter'.start.val = iter.end.val := by omega
      refine ⟨by rw [h_out_len', h_eq], fun j hj => h_pre' j (by omega)⟩
  · exact ⟨rfl, h_start_le, h_out_len, h_pre⟩

end spqr.encoding.polynomial.PolyDecoder.into_pb_loop0

/-! # Spec theorem for `spqr::encoding::polynomial::{PolyDecoder}::into_pb`

Serializes a `PolyDecoder` (with `pts_needed`, `pts : [SortedSet<Pt>; 16]`, `is_complete`)
into its protobuf representation. Casts `pts_needed` to `U32`, then serializes all 16 sorted
sets into `Vec<Vec<u8>>` where each point occupies 4 big-endian bytes.

**Source**: spqr/src/encoding/polynomial.rs -/

namespace spqr.encoding.polynomial.PolyDecoder

/-- **Spec theorem for `encoding.polynomial.PolyDecoder.into_pb`** (byte-level):

Serializes a `PolyDecoder` into a `proto.pq_ratchet.PolynomialDecoder`. The result preserves
`pts_needed`, sets `polys = 16`, preserves `is_complete`, and contains 16 byte vectors each
faithfully encoding their sorted set's points in 4-byte big-endian format. -/
@[step]
theorem into_pb_spec
    (self : encoding.polynomial.PolyDecoder)
    (h_cast : self.pts_needed.val ≤ U32.max)
    (h_inner_overflow : ∀ (j : Nat), j < 16 →
        4 * (self.pts.val[j]!).length + 4 ≤ Usize.max) :
    into_pb self ⦃ (result : proto.pq_ratchet.PolynomialDecoder) =>
      result.pts_needed.val = self.pts_needed.val ∧
      result.polys = 16#u32 ∧
      result.is_complete = self.is_complete ∧
      result.pts.length = 16 ∧
      ∀ (j : Nat), j < 16 →
          (result.pts[j]!).length = 4 * (self.pts.val[j]!).length ∧
          ∀ (k : Nat), k < (self.pts.val[j]!).length →
              256 * ((result.pts[j]!)[4 * k]!) + ((result.pts[j]!)[4 * k + 1]!) =
                ((self.pts.val[j]!).val[k]!).x.value.val ∧
              256 * ((result.pts[j]!)[4 * k + 2]!) + ((result.pts[j]!)[4 * k + 3]!) =
                ((self.pts.val[j]!).val[k]!).y.value.val ⦄ := by
  unfold into_pb
  have h_slen : (Slice.len self.pts.to_slice).val = 16 := by
    simp only [Slice.len_val, Array.length_to_slice]; rfl
  step as ⟨i, h_i⟩
  simp only [lift, bind_ok]
  step with into_pb_loop0.loop_spec as ⟨v1, h_len, h_enc⟩
  · rfl
  have h_u32 : U32.max = 4294967295 := U32.max_eq
  refine ⟨?_, by rw [h_len, h_slen], fun j hj => h_enc j (by omega)⟩
  rw [h_i, UScalar.cast_val_eq]
  exact Nat.mod_eq_of_lt (by change _ < 2 ^ 32; omega)

end spqr.encoding.polynomial.PolyDecoder
