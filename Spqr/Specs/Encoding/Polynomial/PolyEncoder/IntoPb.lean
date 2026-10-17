/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong, Markus Dablander
-/
module

public import SrcTranslated.Funs
public import Spqr.Math.Poly.ModByMonic
public import Spqr.Math.Poly.Identities.Basic
import Spqr.Auxiliary.Aeneas.Scalar
import Spqr.Specs.Encoding.Polynomial.Poly.Serialize
public import Spqr.Specs.Aeneas.SliceIteratorNext
import Spqr.Specs.Encoding.Polynomial.Pt.Serialize
import Spqr.Specs.Aeneas.RangeIteratorNext
import Spqr.Specs.Aeneas.VecExtendFromSlice
public import Spqr.Specs.Encoding.Polynomial.PolyEncoder.Defs
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Tactic.ComputeDegree
import Spqr.Specs.Aeneas.IndexRangeFull

/-! # Spec theorem for `PolyEncoder::into_pb`: loop body 1

One step of the inner coefficient-serialization loop. Calls `next` on a `Range<usize>` iterator
and either returns `v` unchanged (done) or appends the 2-byte big-endian encoding of `pts[i]` to
`v` (continue). Invariant: `v.len() == 2 * i` with `v[2*k]*256 + v[2*k+1] = pts[k].value.val`.

**Source**: spqr/src/encoding/polynomial.rs -/

@[expose] public section

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf spqr.math.gf

namespace spqr.encoding.polynomial.PolyEncoder.into_pb_loop0_loop0

/-- Appending a byte pair `[hi, lo]`: earlier bytes are unchanged and the pair sits at the end. -/
private lemma vec_append_pair {v v1 : alloc.vec.Vec U8} {hi lo : U8}
    (h : v1.val = v.val ++ [hi, lo]) :
    v1.length = v.length + 2 ∧ (∀ p < v.length, v1[p]! = v[p]!) ∧
      v1[v.length]! = hi ∧ v1[v.length + 1]! = lo := by
  simp only [alloc.vec.Vec.getElem!_Nat_eq, alloc.vec.Vec.length, h, List.length_append,
    List.getElem!_eq_getElem?_getD]
  refine ⟨by simp, fun p hp => by rw [List.getElem?_append_left hp], by simp, by simp⟩

/-- **Spec theorem for `encoding.polynomial.PolyEncoder.into_pb_loop0_loop0.body`**:

One step of the inner serialization loop. Retrieves index `i` from the range iterator and either
returns `v` unchanged (done, `¬(iter.start < iter.end)`) or appends `[hi, lo]` — the big-endian
bytes of `pts[i].value` — to `v` (continue, with iterator advanced by one). -/
@[step]
theorem body_spec
    (pts : alloc.vec.Vec GF16)
    (iter : core.ops.range.Range Usize)
    (v : alloc.vec.Vec U8)
    (h_end_le : iter.end ≤ pts.length)
    (h_out_overflow : v.length + 2 ≤ Usize.max) :
    body pts iter v ⦃ cf =>
      match cf with
      | ControlFlow.done v' =>
          v' = v ∧ ¬(iter.start < iter.end)
      | ControlFlow.cont (iter1, v1) =>
          iter.start < iter.end ∧
          iter1.start = iter.start.val + 1 ∧
          iter1.end = iter.end ∧
          ∃ (hi lo : U8),
            v1 = v ++ [hi, lo] ∧
            256 * hi  + lo = (pts[iter.start]!).value.val ⦄ := by
  unfold body
  step with core.iter.range.IteratorRange.next_Usize_spec' iter as
    ⟨opt, iter1', h_none, h_some⟩
  by_cases h_lt : iter.start < iter.end
  · obtain ⟨h_opt_eq, h_start1, h_end1⟩ := h_some h_lt
    rw [h_opt_eq]
    step as ⟨pt, h_pt⟩
    -- the two big-endian bytes of `pt.value`
    obtain ⟨b0, b1, h_bytes⟩ : ∃ b0 b1, (core.num.U16.to_be_bytes pt.value).val = [b0, b1] :=
      match (core.num.U16.to_be_bytes pt.value).val,
        (core.num.U16.to_be_bytes pt.value).property with
      | [b0, b1], _ => ⟨b0, b1, rfl⟩
    have h_be : (core.num.U16.to_be_bytes pt.value).val =
        pt.value.bv.toBEBytes.map (UScalar.mk (ty := .U8)) := by
      simpa only [lift, WP.spec_ok] using core.num.U16.to_be_bytes.step_spec pt.value
    have h_enc : 256 * b0 + b1 = pt.value.val :=
      U16.toBEBytes_pair_val pt.value b0 b1 (by rw [← h_bytes, h_be])
    simp only [lift, bind_ok]
    step as ⟨v1, h_v1⟩
    refine ⟨h_lt, h_start1, h_end1, b0, b1, by rw [h_v1, Array.val_to_slice, h_bytes], ?_⟩
    rw [h_enc, h_pt, alloc.vec.Vec.getElem!_Usize_eq]
    exact congrArg (fun g : GF16 => g.value.val)
      (List.Inhabited_getElem_eq_getElem! _ _ (by scalar_tac))
  · obtain ⟨h_opt_eq, _⟩ := h_none h_lt
    rw [h_opt_eq, WP.spec_ok]
    exact ⟨rfl, h_lt⟩

/-!# Spec theorem for `PolyEncoder::into_pb`: loop 1

Full inner coefficient-serialization loop. Iterates over `pts` via a range iterator, appending
2-byte big-endian encodings to the output. Postcondition: `out.len = 2 * iter.end` with each
pair `(hi, lo)` satisfying `hi*256 + lo = pts[j].value.val`. Proof via `loop.spec_decr_nat`.

**Source**: spqr/src/encoding/polynomial.rs-/
@[step]
theorem loop_spec
    (pts : alloc.vec.Vec GF16)
    (iter : core.ops.range.Range Usize)
    (v : alloc.vec.Vec U8)
    (h_end_le : iter.end ≤ pts.length)
    (h_out_len : v.length = 2 * iter.start)
    (h_start_le : iter.start ≤ iter.end)
    (h_overflow : 2 * pts.length + 2 ≤ Usize.max)
    (h_pre : ∀ (j : Nat), j < iter.start →
          256 * v[2 * j]! + v[2 * j + 1]! = (pts[j]!).value.val) :
    into_pb_loop0_loop0 iter pts v ⦃ (result : alloc.vec.Vec U8) =>
      result.length = 2 * iter.end ∧
      ∀ (j : Nat), j < iter.end →
          256 * result[2 * j]! + result[2 * j + 1]! = (pts[j]!).value.val ⦄ := by
  unfold into_pb_loop0_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : core.ops.range.Range Usize × alloc.vec.Vec U8) => p.1.end - p.1.start)
    (inv := fun (p : core.ops.range.Range Usize × alloc.vec.Vec U8) =>
        p.1.end = iter.end ∧
        p.1.start ≤ p.1.end ∧
        p.2.length = 2 * p.1.start ∧
        (∀ (j : Nat), j < p.1.start →
            256 * p.2[2 * j]! + p.2[2 * j + 1]! = (pts[j]!).value.val))
  · rintro ⟨iter', out'⟩ hinv
    dsimp only at hinv
    obtain ⟨h_end', h_start_le', h_out_len', h_pre'⟩ := hinv
    have h_end_val : iter'.end.val = iter.end.val := by rw [h_end']
    have h_sl : iter'.start.val ≤ iter'.end.val := h_start_le'
    have h_end_le' : iter.end.val ≤ pts.val.length := h_end_le
    have h_overflow' : 2 * pts.val.length + 2 ≤ Usize.max := h_overflow
    have h_out_len'' : out'.val.length = 2 * iter'.start.val := h_out_len'
    apply WP.spec_mono (body_spec pts iter' out' (show iter'.end.val ≤ pts.val.length by omega)
      (show out'.val.length + 2 ≤ Usize.max by omega))
    rintro (⟨iter'', out''⟩ | out'') h_cf
    · -- one more point serialized
      obtain ⟨h_lt, h_start1, h_end1, hi, lo, h_out_eq, h_enc⟩ := h_cf
      have h_lt' : iter'.start.val < iter'.end.val := h_lt
      have h_start1' : iter''.start.val = iter'.start.val + 1 := h_start1
      have h_end1' : iter''.end.val = iter'.end.val := by rw [h_end1]
      obtain ⟨h_len, h_keep, h_hi, h_lo⟩ := vec_append_pair h_out_eq
      have h_len' : out''.val.length = out'.val.length + 2 := h_len
      dsimp only
      refine ⟨⟨h_end1.trans h_end', show iter''.start.val ≤ iter''.end.val by omega,
        show out''.val.length = 2 * iter''.start.val by omega, fun j hj => ?_⟩,
        show iter''.end.val - iter''.start.val < iter'.end.val - iter'.start.val by omega⟩
      by_cases hj_lt : j < iter'.start.val
      · rw [h_keep _ (by omega), h_keep _ (by omega)]
        exact h_pre' j hj_lt
      · obtain rfl : j = iter'.start.val := by omega
        rw [← h_out_len'', h_hi, h_lo]
        exact h_enc
    · -- range exhausted
      obtain ⟨rfl, h_nlt⟩ := h_cf
      have h_eq : iter'.start.val = iter.end.val := by
        have : ¬ iter'.start.val < iter'.end.val := h_nlt
        omega
      exact ⟨by omega, fun j hj => h_pre' j (by omega)⟩
  · exact ⟨rfl, h_start_le, h_out_len, h_pre⟩

end spqr.encoding.polynomial.PolyEncoder.into_pb_loop0_loop0

/-! # Spec theorem for `PolyEncoder::into_pb`: loop body 0

One step of the outer point-serialization loop. Calls `next` on a range iterator over `points`
and either returns `v` unchanged (done) or serializes `points[j].value` via the inner loop
(`into_pb_loop0_loop0`) and pushes the resulting byte vector onto `v` (continue).
Invariant: `v.val.length == iter.start.val`.

**Source**: spqr/src/encoding/polynomial.rs -/

namespace spqr.encoding.polynomial.PolyEncoder.into_pb_loop0

/-- **Spec theorem for `encoding.polynomial.PolyEncoder.into_pb_loop0.body`**:

One step of the outer serialization loop. Retrieves index `j` from the range iterator, serializes
`points[j].value` into a big-endian byte vector via the inner loop, and pushes it onto `v`.
Done case returns `v` unchanged; cont case appends one serialized entry with iterator advanced. -/
@[step]
theorem body_spec
    (points : Array Point 16#usize)
    (iter : core.ops.range.Range Usize)
    (v : alloc.vec.Vec (alloc.vec.Vec U8))
    (h_end_le : iter.end ≤ points.val.length)
    (h_out_overflow : v.length + 1 ≤ Usize.max)
    (h_inner_overflow : ∀ (j : Nat), j < points.length →
        2 * (points.val[j]!).value.length + 2 ≤ Usize.max) :
    body points iter v ⦃ cf =>
      match cf with
      | ControlFlow.done v' => v' = v ∧ ¬(iter.start < iter.end)
      | ControlFlow.cont (iter1, v1) =>
          iter.start < iter.end ∧
          iter1.start = iter.start.val + 1 ∧
          iter1.end = iter.end ∧
          ∃ (serialized : alloc.vec.Vec U8),
            v1 = v ++ [serialized] ∧
            serialized.length = 2 * (points[iter.start]!).value.val.length ∧
            ∀ (k : Nat),
              k < (points.val[iter.start.val]!).value.length →
                256 * (serialized[2 * k]!) + serialized[2 * k + 1]! =
                  ((points[iter.start]!).value.val[k]!).value.val ⦄ := by
  unfold body
  step with core.iter.range.IteratorRange.next_Usize_spec' iter as
    ⟨opt, iter1', h_none, h_some⟩
  by_cases h_lt : iter.start.val < iter.end.val
  · obtain ⟨h_opt_eq, h_start1, h_end1⟩ := h_some h_lt
    rw [h_opt_eq]
    have h_j_lt : iter.start.val < points.val.length := by omega
    have h_inner := h_inner_overflow iter.start.val h_j_lt
    step as ⟨p, h_p⟩
    have h_p' : p = points.val[iter.start.val]! :=
      h_p.trans (List.Inhabited_getElem_eq_getElem! _ _ h_j_lt)
    step as ⟨i1, h_i1⟩
    have h_wc : (alloc.vec.Vec.with_capacity U8 i1).length = 0 := by
      simp [alloc.vec.Vec.with_capacity, alloc.vec.Vec.new]
    subst h_p'
    step with into_pb_loop0_loop0.loop_spec as ⟨v2, h_v2_len, h_v2⟩
    step as ⟨v3, h_v3⟩
    refine ⟨h_lt, h_start1, h_end1, v2, h_v3, ?_, fun k hk => ?_⟩
    · simpa [Array.getElem!_Usize_eq, alloc.vec.Vec.len] using h_v2_len
    · simpa [Array.getElem!_Usize_eq, alloc.vec.Vec.len, alloc.vec.Vec.getElem!_Nat_eq] using
        h_v2 k (by simpa [alloc.vec.Vec.len] using hk)
  · obtain ⟨h_opt_eq, _⟩ := h_none (by omega)
    simp [h_opt_eq, WP.spec_ok, h_lt]

end spqr.encoding.polynomial.PolyEncoder.into_pb_loop0

/-! # Spec theorem for `PolyEncoder::into_pb`: loop 0

Full outer point-serialization loop. Iterates over `points[0..iter.end]`, serializing each
point's GF(2¹⁶) coefficients into a byte vector. Postcondition: `result.len = iter.end` with
each entry encoding the corresponding point's coefficients in big-endian.

**Source**: spqr/src/encoding/polynomial.rs -/

namespace spqr.encoding.polynomial.PolyEncoder.into_pb_loop0

/-- Pushing `x`: earlier entries are unchanged and `x` sits at the end. -/
private lemma vec_push {α : Type} [Inhabited α] {v v1 : alloc.vec.Vec α} {x : α}
    (h : v1.val = v.val ++ [x]) :
    v1.val.length = v.val.length + 1 ∧ (∀ j < v.val.length, v1.val[j]! = v.val[j]!) ∧
      v1.val[v.val.length]! = x := by
  simp only [h, List.length_append, List.length_singleton, List.getElem!_eq_getElem?_getD]
  exact ⟨trivial, fun j hj => by rw [List.getElem?_append_left hj], by simp⟩

/-- **Spec theorem for `encoding.polynomial.PolyEncoder.into_pb_loop0`**:

Full outer serialization loop. Drives the body to completion, producing a vector of byte vectors
with `result.len = iter.end`, one serialized entry per point. -/
@[step]
theorem loop_spec
    (points : Array Point 16#usize)
    (iter : core.ops.range.Range Usize)
    (v : alloc.vec.Vec (alloc.vec.Vec U8))
    (h_end_le : iter.end ≤ points.length)
    (h_out_len : v.length = iter.start)
    (h_start_le : iter.start ≤ iter.end.val)
    (h_overflow : points.length + 1 ≤ Usize.max)
    (h_inner_overflow : ∀ (j : Nat), j < points.length →
        2 * (points.val[j]!).value.length + 2 ≤ Usize.max)
    (h_pre : ∀ (j : Nat), j < iter.start →
          (v.val[j]!).length = 2 * (points[j]!).value.length ∧
          ∀ (k : Nat), k < (points[j]!).value.length →
              256 * ((v[j]!)[2 * k]!) + (v[j]!)[2 * k + 1]! = ((points[j]!).value[k]!).value.val) :
    into_pb_loop0 iter points v ⦃ (result : alloc.vec.Vec (alloc.vec.Vec U8)) =>
      result.length = iter.end ∧
      ∀ (j : Nat), j < iter.end →
          (result[j]!).length = 2 * (points[j]!).value.length ∧
          ∀ (k : Nat), k < (points[j]!).value.length →
              256 * ((result[j]!)[2 * k]!)  + (result[j]!)[2 * k + 1]! =
                ((points[j]!).value[k]!).value.val ⦄ := by
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
        (∀ (j : Nat), j < p.1.start →
            (p.2.val[j]!).length = 2 * (points[j]!).value.length ∧
            ∀ (k : Nat),
              k < (points[j]!).value.length →
                256 * (p.2.val[j]!)[2 * k]!  + (p.2.val[j]!)[2 * k + 1]! =
                  ((points[j]!).value.val[k]!).value.val))
  · rintro ⟨iter', out'⟩ hinv
    dsimp only at hinv
    obtain ⟨h_end', h_start_le', h_out_len', h_pre'⟩ := hinv
    have h_end_val : iter'.end.val = iter.end.val := by rw [h_end']
    have h_sl : iter'.start.val ≤ iter'.end.val := h_start_le'
    have h_end_le' : iter.end.val ≤ points.val.length := h_end_le
    have h_ov : points.val.length + 1 ≤ Usize.max := h_overflow
    have h_len' : out'.val.length = iter'.start.val := h_out_len'
    apply WP.spec_mono (body_spec points iter' out'
      (show iter'.end.val ≤ points.val.length by omega)
      (show out'.val.length + 1 ≤ Usize.max by omega) h_inner_overflow)
    rintro (⟨iter'', out''⟩ | out'') h_cf
    · -- one more point serialized
      obtain ⟨h_lt, h_start1, h_end1, serialized, h_out_eq, h_ser_len, h_ser_encode⟩ := h_cf
      have h_lt' : iter'.start.val < iter'.end.val := h_lt
      have h_start1' : iter''.start.val = iter'.start.val + 1 := h_start1
      have h_end1' : iter''.end.val = iter'.end.val := by rw [h_end1]
      obtain ⟨h_len, h_keep, h_last⟩ := vec_push h_out_eq
      dsimp only
      refine ⟨⟨h_end1.trans h_end', show iter''.start.val ≤ iter''.end.val by omega,
        show out''.val.length = iter''.start.val by omega, fun j hj => ?_⟩,
        show iter''.end.val - iter''.start.val < iter'.end.val - iter'.start.val by omega⟩
      by_cases hj_lt : j < iter'.start.val
      · rw [h_keep j (by omega)]
        exact h_pre' j hj_lt
      · obtain rfl : j = iter'.start.val := by omega
        rw [h_len'] at h_last
        rw [h_last]
        exact ⟨by simpa [Array.getElem!_Nat_eq] using h_ser_len,
          by simpa [Array.getElem!_Nat_eq] using h_ser_encode⟩
    · -- range exhausted
      obtain ⟨rfl, h_nlt⟩ := h_cf
      have : ¬ iter'.start.val < iter'.end.val := h_nlt
      exact ⟨by omega, fun j hj => h_pre' j (by omega)⟩
  · exact ⟨rfl, h_start_le, h_out_len, h_pre⟩

end spqr.encoding.polynomial.PolyEncoder.into_pb_loop0

/-! # Spec theorem for `PolyEncoder::into_pb`: loop body 2

One step of the polynomial-serialization loop (the `EncoderState::Polys` branch). Calls `next`
on a `Range<usize>` iterator over the indices of `polys` and either returns `v` unchanged (done)
or serializes `polys[i]` via `Poly::serialize` and pushes the result onto `v` (continue).

**Source**: spqr/src/encoding/polynomial.rs -/

namespace spqr.encoding.polynomial.PolyEncoder.into_pb_loop1

/-- **Spec theorem for `encoding.polynomial.PolyEncoder.into_pb_loop1.body`**:

One step of the polynomial-serialization loop. Retrieves index `i` from the range iterator,
serializes `polys[i]` via `Poly::serialize`, and pushes the result onto `v`. Done case
returns `v` unchanged; cont case appends one serialized entry with iterator advanced. -/
@[step]
theorem body_spec
    (polys : Array Poly 16#usize)
    (iter : core.ops.range.Range Usize)
    (v : alloc.vec.Vec (alloc.vec.Vec U8))
    (h_end_le : iter.end ≤ polys.val.length)
    (h_out_overflow : v.length + 1 ≤ Usize.max)
    (h_ser_overflow : ∀ j < polys.length,
        2 * (polys.val[j]!).degree + 2 ≤ Usize.max) :
    body polys iter v ⦃ cf =>
      match cf with
      | ControlFlow.done v' =>
          v' = v ∧ ¬(iter.start < iter.end)
      | ControlFlow.cont (iter1, v1) =>
          iter.start < iter.end ∧
          iter1.start = iter.start.val + 1 ∧
          iter1.end = iter.end ∧
          ∃ (serialized : alloc.vec.Vec U8),
            v1 = v ++ [serialized] ∧
            serialized.length = 2 * (polys.val[iter.start.val]!).degree ∧
            ∀ k < (polys.val[iter.start.val]!).degree,
                256 * serialized[2 * k]! + serialized[2 * k +1]! =
                  ((polys.val[iter.start.val]!).coefficients[k]!).value.val ⦄ := by
  unfold body
  step with core.iter.range.IteratorRange.next_Usize_spec' iter as
    ⟨opt, iter1', h_none, h_some⟩
  by_cases h_lt : iter.start.val < iter.end.val
  · obtain ⟨h_opt_eq, h_start1, h_end1⟩ := h_some h_lt
    rw [h_opt_eq]
    have h_j_lt : iter.start.val < polys.val.length := by omega
    have h_getelem : (polys.val[iter.start.val]! : Poly) =
        polys.val[iter.start.val]'h_j_lt := by
      rw [← List.Inhabited_getElem_eq_getElem! (hi := h_j_lt)]
    have h_ser := h_ser_overflow iter.start.val h_j_lt
    step*
  · obtain ⟨h_opt_eq, _⟩ := h_none (by omega)
    simp [h_opt_eq, WP.spec_ok, h_lt]

end spqr.encoding.polynomial.PolyEncoder.into_pb_loop1

/-! # Spec theorem for `PolyEncoder::into_pb`: loop 2

Full polynomial-serialization loop (the `EncoderState::Polys` branch). Iterates over the
indices `iter.start..iter.end` of `polys`, serializing each polynomial's coefficients into a
byte vector. Postcondition: `result.len = iter.end` with each entry encoding the corresponding
polynomial's coefficients in big-endian. Proof via `loop.spec_decr_nat`.

**Source**: spqr/src/encoding/polynomial.rs -/

namespace spqr.encoding.polynomial.PolyEncoder.into_pb_loop1

/-- **Spec theorem for `encoding.polynomial.PolyEncoder.into_pb_loop1`**:

Full polynomial-serialization loop. Drives the body to completion, producing a vector of byte
vectors with `result.len = iter.end`, one serialized entry per polynomial. -/
@[step]
theorem loop_spec
    (polys : Array Poly 16#usize)
    (iter : core.ops.range.Range Usize)
    (v : alloc.vec.Vec (alloc.vec.Vec U8))
    (h_end_le : iter.end ≤ polys.length)
    (h_out_len : v.length = iter.start)
    (h_start_le : iter.start ≤ iter.end.val)
    (h_overflow : polys.length + 1 ≤ Usize.max)
    (h_ser_overflow : ∀ j < polys.length,
        2 * (polys.val[j]!).degree + 2 ≤ Usize.max)
    (h_pre : ∀ j < iter.start.val,
          (v[j]!).length = 2 * (polys.val[j]!).degree ∧
          ∀ k < (polys.val[j]!).degree,
              256 * (v[j]!)[2 * k]! + (v[j]!)[2 * k + 1]! =
                ((polys.val[j]!).coefficients[k]!).value.val) :
    into_pb_loop1 iter polys v ⦃ (result : alloc.vec.Vec (alloc.vec.Vec U8)) =>
      result.length = iter.end ∧
      ∀ j < iter.end.val,
          (result[j]!).length = 2 * (polys.val[j]!).degree ∧
          ∀ k < (polys.val[j]!).degree,
              256 * (result[j]!)[2 * k]! + (result[j]!)[2 * k + 1]! =
                ((polys.val[j]!).coefficients[k]!).value.val ⦄ := by
  unfold into_pb_loop1
  apply loop.spec_decr_nat
    (measure := fun (p : core.ops.range.Range Usize ×
                       alloc.vec.Vec (alloc.vec.Vec U8)) => p.1.end - p.1.start)
    (inv := fun (p : core.ops.range.Range Usize × alloc.vec.Vec (alloc.vec.Vec U8)) =>
        p.1.end = iter.end ∧
        p.1.start ≤ p.1.end ∧
        p.2.length = p.1.start ∧
        (∀ j < p.1.start.val, (p.2[j]!).length = 2 * (polys.val[j]!).degree ∧
          ∀ k < (polys.val[j]!).degree,
            256 * (p.2[j]!)[2 * k]! + (p.2[j]!)[2 * k + 1]! =
            ((polys.val[j]!).coefficients[k]!).value.val))
  · rintro ⟨iter', out'⟩ hinv
    dsimp only at hinv
    obtain ⟨h_end', h_start_le', h_out_len', h_pre'⟩ := hinv
    have h_end_val : iter'.end.val = iter.end.val := by rw [h_end']
    have h_sl : iter'.start.val ≤ iter'.end.val := h_start_le'
    have h_end_le' : iter.end.val ≤ polys.val.length := h_end_le
    have h_ov : polys.val.length + 1 ≤ Usize.max := h_overflow
    have h_len' : out'.val.length = iter'.start.val := h_out_len'
    apply WP.spec_mono (body_spec polys iter' out' (show iter'.end.val ≤ polys.val.length by omega)
      (show out'.val.length + 1 ≤ Usize.max by omega) h_ser_overflow)
    rintro (⟨iter'', out''⟩ | out'') h_cf
    · -- one more polynomial serialized
      obtain ⟨h_lt, h_start1, h_end1, serialized, h_out_eq, h_ser_len, h_ser_encode⟩ := h_cf
      have h_lt' : iter'.start.val < iter'.end.val := h_lt
      have h_start1' : iter''.start.val = iter'.start.val + 1 := h_start1
      have h_end1' : iter''.end.val = iter'.end.val := by rw [h_end1]
      obtain ⟨h_len, h_keep, h_last⟩ := into_pb_loop0.vec_push h_out_eq
      dsimp only
      refine ⟨⟨h_end1.trans h_end', show iter''.start.val ≤ iter''.end.val by omega,
        show out''.val.length = iter''.start.val by omega, fun j hj => ?_⟩,
        show iter''.end.val - iter''.start.val < iter'.end.val - iter'.start.val by omega⟩
      simp only [alloc.vec.Vec.getElem!_Nat_eq] at h_pre' ⊢
      by_cases hj_lt : j < iter'.start.val
      · rw [h_keep j (by omega)]
        exact h_pre' j hj_lt
      · obtain rfl : j = iter'.start.val := by omega
        rw [h_len'] at h_last
        rw [h_last]
        exact ⟨h_ser_len, by simpa [alloc.vec.Vec.getElem!_Nat_eq] using h_ser_encode⟩
    · -- range exhausted
      obtain ⟨rfl, h_nlt⟩ := h_cf
      have : ¬ iter'.start.val < iter'.end.val := h_nlt
      exact ⟨by omega, fun j hj => h_pre' j (by omega)⟩
  · exact ⟨rfl, h_start_le, h_out_len, h_pre⟩

end spqr.encoding.polynomial.PolyEncoder.into_pb_loop1

/-! # Spec theorem for `spqr::encoding::polynomial::{PolyEncoder}::into_pb`

Converts a `PolyEncoder` (chunk index `idx` + `EncoderState`) into its protobuf representation.
For `Points`: serializes each point's GF(2¹⁶) coefficients into `result.pts` (big-endian).
For `Polys`: serializes each polynomial's coefficients into `result.polys` via `Poly::serialize`.

**Source**: spqr/src/encoding/polynomial.rs -/

namespace spqr.encoding.polynomial.PolyEncoder

/-- **Spec theorem for `encoding.polynomial.PolyEncoder.into_pb`** (byte-level)

Byte-level postcondition for serializing a `PolyEncoder` into its protobuf representation. -/
theorem into_pb_spec_bytes
    (self : PolyEncoder)
    (h_overflow_points : ∀ points,
      self.s = .Points points →
        ∀ j < points.length, 2 * (points[j]!).value.length + 2 ≤ Usize.max)
    (h_overflow_polys : ∀ polys,
      self.s = .Polys polys →
        ∀ j < polys.length, 2 * (polys[j]!).degree + 2 ≤ Usize.max) :
    into_pb self ⦃ (result : proto.pq_ratchet.PolynomialEncoder) =>
      result.idx = self.idx ∧
      match self.s with
      | .Points points =>
        result.polys.val = [] ∧
        result.pts.length = points.length ∧
        ∀ j < points.length,
            (result.pts[j]!).length = 2 * (points[j]!).value.length ∧
            ∀ k < (points[j]!).value.length,
              256 * (result.pts[j]!)[2 * k]! + (result.pts[j]!)[2 * k + 1]!  =
                  ((points[j]!).value[k]!).value.val
      | .Polys polys =>
        result.pts.val = [] ∧
        result.polys.length = polys.length ∧
        ∀ j < polys.length,
          result.polys[j]!.length = 2 * (polys.val[j]!).degree ∧
          ∀ k < (polys.val[j]!).degree,
            256 * (result.polys[j]!)[2 * k ]! + (result.polys[j]!)[2 * k + 1]! =
              ((polys[j]!).coefficients[k]!).value.val ⦄ := by
  unfold into_pb
  simp only [alloc.vec.Vec.with_capacity, lift, bind_ok]
  have h_slen : ∀ {α : Type} (a : Std.Array α 16#usize), (Slice.len a.to_slice).val = 16 := by
    intro α a; simp
  cases h : self.s with
  | Points points =>
    have h_overflow := h_overflow_points points h
    step with into_pb_loop0.loop_spec as ⟨v2, h_len, h_v2⟩
    refine ⟨by simp [alloc.vec.Vec.new], by rw [h_len, h_slen]; simp, fun j hj => ?_⟩
    exact h_v2 j (by rw [h_slen]; simpa using hj)
  | Polys polys =>
    have h_overflow := h_overflow_polys polys h
    step with into_pb_loop1.loop_spec as ⟨v2, h_len, h_v2⟩
    refine ⟨by simp [alloc.vec.Vec.new], by rw [h_len, h_slen]; simp, fun j hj => ?_⟩
    simpa [Array.getElem!_Nat_eq] using h_v2 j (by rw [h_slen]; simpa using hj)

/-- **Spec theorem for `spqr::encoding::polynomial::PolyEncoder::into_pb`**
• The call always succeeds (no panic) under the sole hypothesis `2 * len + 2 ≤ Usize.max` on
  each element's coefficient count `len`.
• Serialization is faithful, as spelled out by `PolyEncoder.IntoPbPostCond`.
-/
@[step]
theorem into_pb_spec
    (self : PolyEncoder)
    (h_overflow_points : ∀ points,
      self.s = .Points points →
        ∀ j < points.length, 2 * (points[j]!).value.length + 2 ≤ Usize.max)
    (h_overflow_polys : ∀ polys, self.s = .Polys polys →
        ∀ j < polys.length, 2 * (polys[j]!).degree + 2 ≤ Usize.max) :
    into_pb self ⦃ (result : proto.pq_ratchet.PolynomialEncoder) =>
      IntoPbPostCond self result ⦄ := by
  have h_raw := into_pb_spec_bytes self h_overflow_points h_overflow_polys
  apply WP.spec_mono h_raw
  intro result h_post
  obtain ⟨h_idx, h_data⟩ := h_post
  refine ⟨h_idx, ?_⟩
  -- the value equation, plus its images under `toGF216` and `natToBinaryPoly`
  cases h : self.s with
  | Points points =>
    simp only [h] at h_data ⊢
    obtain ⟨h_polys, h_len, h_pts⟩ := h_data
    refine ⟨h_polys, h_len, fun j hj => ⟨(h_pts j hj).1, fun k hk => ?_⟩⟩
    have e := (h_pts j hj).2 k hk
    exact ⟨e, by rw [e], by rw [e]⟩
  | Polys polys =>
    simp only [h] at h_data ⊢
    obtain ⟨h_pts, h_len, h_polys⟩ := h_data
    refine ⟨h_pts, h_len, fun j hj => ?_⟩
    simp only [Array.getElem!_Nat_eq] at h_polys ⊢
    refine ⟨(h_polys j hj).1, fun k hk => ?_⟩
    have e := (h_polys j hj).2 k hk
    exact ⟨e, by rw [e], by rw [e]⟩

end spqr.encoding.polynomial.PolyEncoder
