/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Math.Poly.ModByMonic
import Spqr.Specs.Aeneas.SliceIteratorNext
import Spqr.Specs.Encoding.Polynomial.Pt.Serialize
import Spqr.Specs.Aeneas.RangeIteratorNext
import Spqr.Specs.Aeneas.VecExtendFromSlice

/-! # Spec theorem for `PolyDecoder::into_pb`: loop body 1

One step of the inner point-serialization loop. Given `pts : SortedSet<Pt>`, a range iterator
`iter`, and byte accumulator `v`, either returns `v` unchanged (range exhausted) or serializes
`pts[iter.start]` into 4 big-endian bytes and appends them to `v`.

**Source**: spqr/src/encoding/polynomial.rs -/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf

instance : Inhabited (sorted_vec.SortedSet Pt) :=   ⟨alloc.vec.Vec.new _⟩

private instance : Inhabited Pt := ⟨{ x := ⟨0#u16⟩, y := ⟨0#u16⟩ }⟩

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
  obtain ⟨⟨opt, iter1'⟩, hnext, h_none, h_some⟩ :=
    WP.spec_imp_exists (core.iter.range.IteratorRange.next_Usize_spec' iter)
  rw [hnext]; simp only [bind_tc_ok]
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
    exact ⟨rfl, by omega⟩

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
      · have mk : ∀ {k} {bk : U8}, k ≤ 3 →
            [b0, b1, b2, b3][k]? = some bk →
            out''[4 * iter'.start.val + k]! = bk := by grind
        grind [mk (k := 1) (by omega) rfl, mk (k := 2) (by omega) rfl, mk (k := 3) (by omega) rfl]
  · grind

end spqr.encoding.polynomial.PolyDecoder.into_pb_loop0_loop0

/-! # Spec theorem for `PolyDecoder::into_pb`: loop body 0

One step of the outer loop. Given a slice iterator over `SortedSet<Pt>` arrays and output
accumulator `v : Vec<Vec<u8>>`, either returns `v` unchanged (iterator exhausted) or serializes
all points in the next sorted set into a byte vector and pushes it onto `v`.

**Source**: spqr/src/encoding/polynomial.rs -/

namespace spqr.encoding.polynomial.PolyDecoder.into_pb_loop0

/-- **Spec theorem for `encoding.polynomial.PolyDecoder.into_pb_loop0.body`**:

One step of the outer loop: terminates if the iterator is exhausted, otherwise serializes all
points in `iter.slice[iter.i]` into 4-byte big-endian encodings and pushes the result onto `v`.

Succeeds when `v.length + 1 ≤ Usize.max` and inner loops won't overflow. -/
@[step]
theorem body_spec
    (iter : core.slice.iter.Iter (sorted_vec.SortedSet Pt))
    (v : alloc.vec.Vec (alloc.vec.Vec U8))
    (h_out_overflow : v.length + 1 ≤ Usize.max)
    (h_inner_overflow : ∀ j < iter.slice.length, 4 * (iter.slice[j]!).length + 4 ≤ Usize.max) :
    body iter v ⦃ cf =>
      match cf with
      | ControlFlow.done v' =>
          v' = v ∧ ¬(iter.i < iter.slice.length)
      | ControlFlow.cont (iter1, v1) =>
          iter.i < iter.slice.length ∧
          iter1.i = iter.i + 1 ∧
          iter1.slice = iter.slice ∧
          ∃ (serialized : alloc.vec.Vec U8),
            v1 = v ++ [serialized] ∧
            serialized.length = 4 * (iter.slice[iter.i]!).length ∧
            ∀ (j : Nat), j < (iter.slice[iter.i]!).length →
                256 * (serialized[4 * j]!) + serialized[4 * j + 1]! =
                  ((iter.slice[iter.i]!).val[j]!).x.value.val ∧
                256 * (serialized[4 * j + 2]!) + serialized[4 * j + 3]! =
                  ((iter.slice[iter.i]!).val[j]!).y.value.val ⦄ := by
  unfold body
  obtain ⟨opt, iter1', hnext, h_none, h_some⟩ :=
    core.slice.iter.IteratorSliceIter.next_post iter
  rw [hnext]
  simp only [bind_tc_ok]
  by_cases h_lt : iter.i < iter.slice.length
  · obtain ⟨h_opt_eq, h_i1, h_slice1⟩ := h_some h_lt
    rw [h_opt_eq]
    have h_inner := h_inner_overflow iter.i h_lt
    have h_getelem : (iter.slice.val[iter.i]! : sorted_vec.SortedSet Pt) =
        iter.slice.val[iter.i]'h_lt := by
      rw [← List.Inhabited_getElem_eq_getElem! (hi := h_lt)]
    step*
    · simp_all [alloc.vec.Vec.with_capacity]
    · simp_all
  · obtain ⟨h_opt_eq, _⟩ := h_none (by omega)
    rw [h_opt_eq]
    exact ⟨rfl, h_lt⟩

/-- **Spec theorem for `encoding.polynomial.PolyDecoder.into_pb_loop0`**:

Full outer loop: serializes all sorted sets into byte vectors in the output accumulator.

Postcondition: `result.length = iter.slice.length` and for every `j < iter.slice.length`,
`(result[j]).length = 4 * (iter.slice[j]).length` with each 4-byte chunk encoding the
corresponding point's `(x, y)` in big-endian format.

**Source**: spqr/src/encoding/polynomial.rs -/
@[step]
theorem loop_spec
    (iter : core.slice.iter.Iter (sorted_vec.SortedSet Pt))
    (v : alloc.vec.Vec (alloc.vec.Vec U8))
    (h_start_le : iter.i ≤ iter.slice.length)
    (h_out_len : v.length = iter.i)
    (h_out_overflow : iter.slice.length + 1 ≤ Usize.max)
    (h_inner_overflow : ∀ j < iter.slice.length, 4 * (iter.slice[j]!).length + 4 ≤ Usize.max)
    (h_pre : ∀ (j : Nat), j < iter.i →
          (v[j]!).length = 4 * (iter.slice[j]!).length ∧
          ∀ (k : Nat), k < (iter.slice[j]!).length →
              256 * ((v[j]!)[4 * k]!) + ((v[j]!)[4 * k + 1]!) =
                ((iter.slice[j]!).val[k]!).x.value.val ∧
              256 * ((v[j]!)[4 * k + 2]!) + ((v[j]!)[4 * k + 3]!) =
                ((iter.slice[j]!).val[k]!).y.value.val) :
    into_pb_loop0 iter v ⦃ (result : alloc.vec.Vec (alloc.vec.Vec U8)) =>
      result.length = iter.slice.length ∧
      ∀ (j : Nat), j < iter.slice.length →
          (result[j]!).length = 4 * (iter.slice[j]!).length ∧
          ∀ (k : Nat), k < (iter.slice[j]!).length →
              256 * ((result[j]!)[4 * k]!) + ((result[j]!)[4 * k + 1]!) =
                ((iter.slice[j]!).val[k]!).x.value.val ∧
              256 * ((result[j]!)[4 * k + 2]!) + ((result[j]!)[4 * k + 3]!) =
                ((iter.slice[j]!).val[k]!).y.value.val ⦄ := by
  unfold into_pb_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : core.slice.iter.Iter (sorted_vec.SortedSet Pt) ×
                       alloc.vec.Vec (alloc.vec.Vec U8)) =>
                  p.1.slice.length - p.1.i)
    (inv := fun (p : core.slice.iter.Iter (sorted_vec.SortedSet Pt) ×
                      alloc.vec.Vec (alloc.vec.Vec U8)) =>
        p.1.slice = iter.slice ∧
        p.1.i ≤ p.1.slice.length ∧
        p.2.length = p.1.i ∧
        (∀ (j : Nat), j < p.1.i →
            (p.2[j]!).length = 4 * (iter.slice[j]!).length ∧
            ∀ (k : Nat), k < (iter.slice[j]!).length →
                256 * ((p.2[j]!)[4 * k]!) + ((p.2[j]!)[4 * k + 1]!) =
                  ((iter.slice[j]!).val[k]!).x.value.val ∧
                256 * ((p.2[j]!)[4 * k + 2]!) + ((p.2[j]!)[4 * k + 3]!) =
                  ((iter.slice[j]!).val[k]!).y.value.val))
  · rintro ⟨iter', v'⟩ ⟨h_slice', h_i_le', h_out_len', h_pre'⟩
    simp only [] at h_slice' h_i_le' h_out_len' h_pre' ⊢
    have h_body := body_spec iter' v'
      (by rw [h_out_len']; rw [h_slice'] at h_i_le'; omega)
      (by rw [h_slice']; exact h_inner_overflow)
    apply WP.spec_mono h_body
    intro cf h_cf
    match cf with
    | ControlFlow.done v'' => grind
    | ControlFlow.cont (iter'', v'') =>
      simp only [] at h_cf ⊢
      obtain ⟨h_lt, h_i1, h_slice1, serialized, h_v_eq, h_ser_len, h_ser_enc⟩ := h_cf
      have h_val : v''.val = v'.val ++ [serialized] := h_v_eq
      have h_len : v'.val.length = iter'.i := h_out_len'
      refine ⟨⟨by grind, by grind, by grind, fun j hj => ?_⟩, by grind⟩
      by_cases hj_lt : j < iter'.i
      · grind
      · have hj_eq : j = iter'.i := by omega
        subst hj_eq
        have h_get : v''[iter'.i]! = serialized := by grind
        rw [h_get]
        rw [h_slice'] at h_ser_len h_ser_enc
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
  unfold core.slice.Slice.iter
  step
  · intro j hj
    simp_all [Array.to_slice]
  · constructor
    · simp_all only [alloc.vec.Vec.length, List.Vector.length_val, UScalar.ofNatCore_val_eq,
      getElem!_pos, Array.to_slice, Slice.length, alloc.vec.Vec.getElem!_Nat_eq,
      Slice.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, UScalar.cast_val_eq,
      UScalarTy.U32_numBits_eq, Nat.reducePow, Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one,
      Nat.reduceAdd]
      scalar_tac
    · grind

end spqr.encoding.polynomial.PolyDecoder
