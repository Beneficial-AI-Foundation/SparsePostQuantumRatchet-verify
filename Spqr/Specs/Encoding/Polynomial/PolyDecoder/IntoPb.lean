/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import Spqr.Math.Poly.ModByMonic
public import Spqr.Specs.Aeneas.SliceIteratorNext
public import Spqr.Specs.Encoding.Polynomial.Pt.Serialize
public import Spqr.Specs.Aeneas.RangeIteratorNext
public import Spqr.Specs.Aeneas.VecExtendFromSlice
public import Spqr.Specs.Encoding.Polynomial.PolyDecoder.NewWithPolyCount

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
    step*
    obtain ⟨b0, b1, b2, b3, h_a_eq⟩ : ∃ b0 b1 b2 b3, a.val = [b0, b1, b2, b3] :=
      match a.val, a.property with | [b0, b1, b2, b3], _ => ⟨b0, b1, b2, b3, rfl⟩
    refine ⟨by omega, h_start1, h_end1, b0, b1, b2, b3, ?_, ?_, ?_⟩
    · simp_all [Array.to_slice]
    · simp_all
      grind
    · simp_all
      grind
  · obtain ⟨h_opt, _⟩ := h_none (by omega)
    subst h_opt
    exact (WP.spec_ok _).mpr ⟨rfl, by omega⟩

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
  · rintro ⟨iter', out'⟩ ⟨h_end', h_start_le', h_out_len', h_pre'⟩
    simp only [] at h_end' h_start_le' h_out_len' h_pre' ⊢
    have h_end_val : iter'.end = iter.end := by rw [h_end']
    have h_body := body_spec pts iter' out' (by rw [h_end']; exact h_end_le) (by grind)
    apply WP.spec_mono h_body
    intro cf h_cf
    match cf with
    | ControlFlow.done out'' => grind
    | ControlFlow.cont (iter'', out'') =>
      simp only [] at h_cf ⊢
      obtain ⟨h_lt, h_start1, h_end1, b0, b1, b2, b3, h_out_eq, h_x_eq, h_y_eq⟩ := h_cf
      have h_val : out''.val = out'.val ++ [b0, b1, b2, b3] := h_out_eq
      have h_len : out'.val.length = 4 * iter'.start.val := h_out_len'
      refine ⟨⟨by grind, by grind, by grind, fun j hj => ?_⟩, by grind⟩
      by_cases hj_lt : j < iter'.start.val
      · grind
      · have hj_eq : j = iter'.start.val := by omega
        subst hj_eq
        simp only [alloc.vec.Vec.getElem!_Nat_eq, h_val]
        rw [List.getElem!_append_right _ _ _ (by grind),
          List.getElem!_append_right _ _ _ (by grind),
          List.getElem!_append_right _ _ _ (by grind),
          List.getElem!_append_right _ _ _ (by grind)]
        simp [h_len, h_x_eq, h_y_eq]
  · grind

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
    step*
    · simp_all [alloc.vec.Vec.with_capacity]
    · simp_all
  · obtain ⟨h_opt_eq, _⟩ := h_none (by omega)
    simp [h_opt_eq, WP.spec_ok, h_lt]

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
  · rintro ⟨iter', v'⟩ ⟨h_end', h_start_le', h_out_len', h_pre'⟩
    simp only [] at h_end' h_start_le' h_out_len' h_pre' ⊢
    have h_end_val : iter'.end.val = iter.end.val := by rw [h_end']
    have h_body := body_spec a iter' v' (by grind) (by grind) h_inner_overflow
    apply WP.spec_mono h_body
    intro cf h_cf
    match cf with
    | ControlFlow.done v'' => grind
    | ControlFlow.cont (iter'', v'') =>
      simp only [] at h_cf ⊢
      obtain ⟨h_lt, h_start1, h_end1, serialized, h_v_eq, h_ser_len, h_ser_enc⟩ := h_cf
      have h_end1_val : iter''.end.val = iter'.end.val := by rw [h_end1]
      have h_val : v''.val = v'.val ++ [serialized] := h_v_eq
      have h_len : v'.val.length = iter'.start.val := h_out_len'
      refine ⟨⟨by grind, by grind, by grind, fun j hj => ?_⟩, by grind⟩
      by_cases hj_lt : j < iter'.start.val
      · grind
      · have hj_eq : j = iter'.start.val := by omega
        subst hj_eq
        have h_get : v''[iter'.start.val]! = serialized := by grind
        rw [h_get]
        exact ⟨h_ser_len, h_ser_enc⟩
  · grind

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
  simp only [alloc.vec.Vec.with_capacity]
  step*
  have h_len : (s1.len : Usize).val = 16 := by simp [*]
  have h_enc : ∀ j < (s1.len : Usize).val,
      (v1[j]!).length = 4 * (self.pts.val[j]!).length ∧
      ∀ k < (self.pts.val[j]!).length,
        256 * ((v1[j]!)[4 * k]!) + ((v1[j]!)[4 * k + 1]!) =
          ((self.pts.val[j]!).val[k]!).x.value.val ∧
        256 * ((v1[j]!)[4 * k + 2]!) + ((v1[j]!)[4 * k + 3]!) =
          ((self.pts.val[j]!).val[k]!).y.value.val := by
    assumption
  refine ⟨?_, by omega, fun j hj => h_enc j (by omega)⟩
  simp only [UScalar.cast_val_eq, *]
  scalar_tac

end spqr.encoding.polynomial.PolyDecoder
