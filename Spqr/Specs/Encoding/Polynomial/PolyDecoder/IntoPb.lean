/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong, Markus Dablander
-/
module

public import SrcTranslated.Funs
import Spqr.Specs.Encoding.Polynomial.Pt.Serialize
import Spqr.Specs.Aeneas.RangeIteratorNext
import Spqr.Specs.Aeneas.VecExtendFromSlice
import Spqr.Specs.Aeneas.IndexRangeFull
public import Spqr.Specs.Encoding.Polynomial.PolyDecoder.FunctionalModels

/-!
# Spec theorems for `spqr::encoding::polynomial::PolyDecoder::into_pb`

A `PolyDecoder` keeps the points it has received so far in 16 lists, called slots, one per
polynomial it is reconstructing. `into_pb` saves this state as a protobuf message, so that it can
be stored and later restored with `from_pb`.

The points are saved slot by slot. Each point becomes 4 bytes (2 for its `x` coordinate, 2 for
its `y` coordinate), the bytes of all points in a slot are joined into one byte string, and the
16 byte strings go into the message. `pts_needed` is cast to a 32-bit number, `polys` is set to
`16` and `is_complete` is copied.

The theorems below build up to the main result in three steps:

• `into_pb_loop0_loop0.loop_spec`: the inner loop produces the bytes of one slot.

• `into_pb_loop0.loop_spec`: the outer loop produces the byte strings of all 16 slots.

• `into_pb_spec`: as long as the byte count of every slot fits into a `usize`, which holds for
  every sorted slot, `into_pb` never panics and returns exactly its functional model `intoPb` in
  `FunctionalModels.lean`.

Both loops add a fixed number of items per step, so one shared lemma, `loop_append_spec`, covers
them.

**Source**: spqr/src/encoding/polynomial.rs
-/

@[expose] public section

open Aeneas Aeneas.Std

/-- The default point, which lets point lists be indexed with `!`. -/
instance instInhabitedPt : Inhabited spqr.encoding.polynomial.Pt := ⟨{ x := ⟨0#u16⟩, y := ⟨0#u16⟩ }⟩

namespace spqr.encoding.polynomial.PolyDecoder
open FunctionalModels

/-- **Range loops that append a fixed number of elements per index**
• A loop over `iter` whose body appends the `c` elements `g l[i]` to the accumulator `v` at every
  index `i` appends `g` of every element of `l` with index in `[iter.start, iter.end)`.
• Succeeds when `iter.end ≤ l.length`, `v` has room for `c` elements per index and the body
  succeeds under these two conditions. -/
private theorem loop_append_spec {α β : Type} [Inhabited β] (l : List β) (g : β → List α)
    (c : Nat) (h_g : ∀ x, (g x).length = c)
    (body : core.ops.range.Range Usize × alloc.vec.Vec α →
      Result (ControlFlow (core.ops.range.Range Usize × alloc.vec.Vec α) (alloc.vec.Vec α)))
    (iter : core.ops.range.Range Usize) (v : alloc.vec.Vec α)
    (h_end_le : iter.end ≤ l.length)
    (h_room : v.length + c * (iter.end - iter.start) ≤ Usize.max)
    (h_body : ∀ iter' (v' : alloc.vec.Vec α), iter'.end ≤ l.length →
      v'.length + c * (iter'.end - iter'.start) ≤ Usize.max →
      body (iter', v') ⦃ cf =>
        match cf with
        | ControlFlow.done v'' => v'' = v' ∧ ¬iter'.start < iter'.end
        | ControlFlow.cont (iter'', v'') => iter'.start < iter'.end ∧
            iter''.start.val = iter'.start.val + 1 ∧ iter''.end = iter'.end ∧
            v''.val = v'.val ++ g l[iter'.start.val]! ⦄) :
    loop body (iter, v) ⦃ r => r.val = v.val ++ (l.extract iter.start iter.end).flatMap g ⦄ := by
  have h_len (s : Nat) :
      ((l.extract s iter.end.val).flatMap g).length = c * (iter.end.val - s) := by
    simp only [List.length_flatMap, h_g, List.map_const', List.sum_replicate, smul_eq_mul,
      List.extract_eq_take_drop, List.length_take, List.length_drop]
    rw [Nat.min_eq_left (Nat.sub_le_sub_right h_end_le s), Nat.mul_comm]
  apply loop.spec_decr_nat (measure := fun p => iter.end.val - p.1.start.val)
    (inv := fun p => p.1.end = iter.end ∧
      p.2.val ++ (l.extract p.1.start.val iter.end.val).flatMap g =
        v.val ++ (l.extract iter.start.val iter.end.val).flatMap g)
  · rintro ⟨⟨s, _⟩, v'⟩ ⟨rfl, h_v'⟩
    have h_len' := congrArg List.length h_v'
    rw [List.length_append, List.length_append, h_len, h_len] at h_len'
    apply WP.spec_mono (h_body ⟨s, iter.end⟩ v' h_end_le (h_len'.trans_le h_room))
    rintro (⟨iter'', v''⟩ | v'') h_cf <;> dsimp only at h_cf ⊢
    · obtain ⟨h_lt, h_start1, h_end1, h_v''⟩ := h_cf
      have h_lt' : s.val < iter.end.val := h_lt
      have h_sl : s.val < l.length := h_lt'.trans_le h_end_le
      have h_sub : iter.end.val - s.val = iter.end.val - (s.val + 1) + 1 := by
        rw [← Nat.sub_sub, Nat.sub_add_cancel (Nat.sub_pos_of_lt h_lt')]
      refine ⟨⟨h_end1, ?_⟩, by rw [h_start1]; exact Nat.sub_lt_sub_left h_lt' (Nat.lt_succ_self _)⟩
      rw [← h_v', h_v'', List.append_assoc, h_start1, List.extract_eq_take_drop,
        List.extract_eq_take_drop, List.drop_eq_getElem_cons h_sl, h_sub, List.take_succ_cons,
        List.flatMap_cons, getElem!_pos l _ h_sl]
    · obtain ⟨rfl, h_nlt⟩ := h_cf
      rw [← h_v', List.extract_eq_take_drop, Nat.sub_eq_zero_of_le (Nat.le_of_not_lt h_nlt),
        List.take_zero, List.flatMap_nil, List.append_nil]
  · exact ⟨rfl, rfl⟩

namespace into_pb_loop0_loop0

/-- **Spec theorem for `encoding.polynomial.PolyDecoder.into_pb_loop0_loop0.body`**
• One step of the inner loop: if the range is exhausted, `v` is returned unchanged; otherwise the
  four big-endian bytes `bytesOfPts` of the point `pts[iter.start]` are appended to `v` and the
  range advances by one.
• Succeeds under the hypotheses of `loop_spec`. -/
@[step]
theorem body_spec
    (pts : sorted_vec.SortedSet Pt) (iter : core.ops.range.Range Usize) (v : alloc.vec.Vec U8)
    (h_end_le : iter.end ≤ pts.length)
    (h_out_overflow : v.length + 4 * (iter.end - iter.start) ≤ Usize.max) :
    body pts iter v ⦃ cf =>
      match cf with
      | ControlFlow.done v' => v' = v ∧ ¬iter.start < iter.end
      | ControlFlow.cont (iter1, v1) => iter.start < iter.end ∧
          iter1.start.val = iter.start.val + 1 ∧ iter1.end = iter.end ∧
          v1.val = v.val ++ bytesOfPts [pts.val[iter.start.val]!] ⦄ := by
  unfold body
  refine WP.spec_bind (core.iter.range.IteratorRange.next_Usize_spec' iter) ?_
  rintro ⟨opt, iter1'⟩ ⟨h_none, h_some⟩
  by_cases h_lt : iter.start.val < iter.end.val
  · obtain ⟨rfl, h_start1, h_end1⟩ := h_some h_lt
    have h_j : iter.start.val < pts.val.length := h_lt.trans_le h_end_le
    refine WP.spec_bind (sorted_vec.SortedSet.Insts.CoreOpsDerefDerefSortedVec.deref_spec _ _) ?_
    rintro pts rfl
    refine WP.spec_bind (sorted_vec.SortedVec.Insts.CoreOpsDerefDerefVec.deref_spec _ _) ?_
    rintro pts rfl
    refine WP.spec_bind (alloc.vec.Vec.index_usize_spec _ _ h_j) ?_
    rintro pt pt_post
    refine WP.spec_bind (Pt.serialize_spec pt) ?_
    rintro a ⟨a_post, a_post1⟩
    rw [Aeneas.Std.Array.index_RangeFull, bind_ok]
    refine WP.spec_bind (alloc.vec.Vec.extend_from_slice_U8_spec v a.to_slice (by
      rw [Array.length_to_slice]
      exact (Nat.add_le_add_left (Nat.mul_le_mul_left 4 (Nat.sub_pos_of_lt h_lt)) _).trans
        h_out_overflow)) ?_
    rintro v2 v2_post
    refine (WP.spec_ok _).mpr ⟨h_lt, h_start1, h_end1, ?_⟩
    obtain ⟨b0, b1, b2, b3, h_a⟩ := List.length_eq_four.mp a.property
    simp only [Array.getElem!_Nat_eq, h_a, List.getElem!_cons_zero, List.getElem!_cons_succ]
      at a_post a_post1
    have hx : Poly.FunctionalModels.gf16OfBytes b0 b1 = pt.x := congrArg encoding.gf.GF16.mk
      (UScalar.eq_of_val_eq (by rw [U16.ofNatCore_val_eq, Nat.mul_comm]; exact a_post))
    have hy : Poly.FunctionalModels.gf16OfBytes b2 b3 = pt.y := congrArg encoding.gf.GF16.mk
      (UScalar.eq_of_val_eq (by rw [U16.ofNatCore_val_eq, Nat.mul_comm]; exact a_post1))
    rw [v2_post, Array.val_to_slice, h_a, getElem!_pos pts.val _ h_j, ← pt_post]
    exact congrArg (v.val ++ ·)
      ((Poly.FunctionalModels.bytesOfCoeffs_coeffsOfBytes [b0, b1, b2, b3] (by simp)).symm.trans
        (congrArg Poly.FunctionalModels.bytesOfCoeffs (congrArg₂ (fun x y => [x, y]) hx hy)))
  · obtain ⟨rfl, _⟩ := h_none h_lt
    exact (WP.spec_ok _).mpr ⟨rfl, h_lt⟩

/-- **Spec theorem for `encoding.polynomial.PolyDecoder.into_pb_loop0_loop0`**
• The inner loop run to completion: the bytes `bytesOfPts` of the points of `pts` with indices in
  `[iter.start, iter.end)` are appended to `v`.
• Succeeds when `iter.end ≤ pts.length` and `v` has room for the four bytes of every point still
  to come, the exact bound. -/
@[step]
theorem loop_spec
    (pts : sorted_vec.SortedSet Pt) (iter : core.ops.range.Range Usize) (v : alloc.vec.Vec U8)
    (h_end_le : iter.end ≤ pts.length)
    (h_out_overflow : v.length + 4 * (iter.end - iter.start) ≤ Usize.max) :
    into_pb_loop0_loop0 iter pts v ⦃ (result : alloc.vec.Vec U8) =>
      result.val = v.val ++ bytesOfPts (pts.val.extract iter.start iter.end) ⦄ := by
  unfold into_pb_loop0_loop0
  exact loop_append_spec pts.val (bytesOfPts [·]) 4 (fun _ => rfl) _ iter v h_end_le h_out_overflow
    fun iter' v' h_end h_room => WP.spec_mono (body_spec pts iter' v' h_end h_room)
      fun cf => ControlFlow.rec (fun _ h => h) (fun _ h => h) cf

end into_pb_loop0_loop0

namespace into_pb_loop0

/-- **Spec theorem for `encoding.polynomial.PolyDecoder.into_pb_loop0.body`**
• One step of the outer loop: if the range is exhausted, `v` is returned unchanged; otherwise the
  byte vector `bytesOfSlot` of the slot `a[iter.start]` is pushed onto `v` and the range advances
  by one.
• Succeeds under the hypotheses of `loop_spec`. -/
@[step]
theorem body_spec
    (a : Array (sorted_vec.SortedSet Pt) 16#usize) (iter : core.ops.range.Range Usize)
    (v : alloc.vec.Vec (alloc.vec.Vec U8))
    (h_end_le : iter.end ≤ a.length)
    (h_overflow : ∀ s ∈ a.val, 4 * s.length ≤ Usize.max)
    (h_out_overflow : v.length + (iter.end - iter.start) ≤ Usize.max) :
    body a iter v ⦃ cf =>
      match cf with
      | ControlFlow.done v' => v' = v ∧ ¬iter.start < iter.end
      | ControlFlow.cont (iter1, v1) => iter.start < iter.end ∧
          iter1.start.val = iter.start.val + 1 ∧ iter1.end = iter.end ∧
          v1.val = v.val ++ [bytesOfSlot a[iter.start]!] ⦄ := by
  unfold body
  refine WP.spec_bind (core.iter.range.IteratorRange.next_Usize_spec' iter) ?_
  rintro ⟨opt, iter1'⟩ ⟨h_none, h_some⟩
  by_cases h_lt : iter.start.val < iter.end.val
  · obtain ⟨rfl, h_start1, h_end1⟩ := h_some h_lt
    have h_j : iter.start.val < a.val.length := h_lt.trans_le h_end_le
    have h_inner := h_overflow _ (List.getElem_mem h_j)
    refine WP.spec_bind (Array.index_usize_spec a iter.start h_j) ?_
    rintro _ rfl
    refine WP.spec_bind (sorted_vec.SortedSet.Insts.CoreOpsDerefDerefSortedVec.deref_spec _ _) ?_
    rintro _ rfl
    refine WP.spec_bind (sorted_vec.SortedVec.Insts.CoreOpsDerefDerefVec.deref_spec _ _) ?_
    rintro _ rfl
    refine WP.spec_bind (Usize.mul_spec h_inner) ?_
    rintro i2 -
    refine WP.spec_bind (sorted_vec.SortedVec.Insts.CoreOpsDerefDerefVec.deref_spec _ _) ?_
    rintro _ rfl
    refine WP.spec_bind (into_pb_loop0_loop0.loop_spec _ _ _ (Nat.le_refl _)
      ((Nat.zero_add _).trans_le h_inner)) ?_
    rintro v4 v4_post
    refine WP.spec_bind (alloc.vec.Vec.push_spec _ _
      ((Nat.add_le_add_left (Nat.sub_pos_of_lt h_lt) _).trans h_out_overflow)) ?_
    rintro v5 v5_post
    refine (WP.spec_ok _).mpr ⟨h_lt, h_start1, h_end1, ?_⟩
    rw [v5_post, Array.getElem!_Usize_eq, getElem!_pos a.val _ h_j]
    refine congrArg (v.val ++ [·]) (alloc.vec.Vec.ext _ _ ?_)
    simp [v4_post, bytesOfSlot_val _ h_inner, alloc.vec.Vec.with_capacity]
  · obtain ⟨rfl, _⟩ := h_none h_lt
    exact (WP.spec_ok _).mpr ⟨rfl, h_lt⟩

/-- **Spec theorem for `encoding.polynomial.PolyDecoder.into_pb_loop0`**
• The outer loop run to completion: the byte vectors `bytesOfSlot` of the slots of `a` with
  indices in `[iter.start, iter.end)` are pushed onto `v`.
• Succeeds when `iter.end ≤ a.length`, every slot satisfies `4 * len ≤ Usize.max` and `v` has
  room for one more vector per slot still to come. -/
@[step]
theorem loop_spec
    (a : Array (sorted_vec.SortedSet Pt) 16#usize) (iter : core.ops.range.Range Usize)
    (v : alloc.vec.Vec (alloc.vec.Vec U8))
    (h_end_le : iter.end ≤ a.length)
    (h_overflow : ∀ s ∈ a.val, 4 * s.length ≤ Usize.max)
    (h_out_overflow : v.length + (iter.end - iter.start) ≤ Usize.max) :
    into_pb_loop0 iter a v ⦃ (result : alloc.vec.Vec (alloc.vec.Vec U8)) =>
      result.val = v.val ++ (a.val.extract iter.start iter.end).map bytesOfSlot ⦄ := by
  unfold into_pb_loop0
  rw [List.map_eq_flatMap]
  exact loop_append_spec a.val (fun s => [bytesOfSlot s]) 1 (fun _ => rfl) _ iter v h_end_le
    (by rwa [Nat.one_mul]) fun iter' v' h_end h_room =>
      WP.spec_mono (body_spec a iter' v' h_end h_overflow (by rwa [Nat.one_mul] at h_room))
        fun cf => ControlFlow.rec (fun _ h => by rwa [Array.getElem!_Usize_eq] at h)
          (fun _ h => h) cf

end into_pb_loop0

/-- **Spec theorem for `spqr::encoding::polynomial::PolyDecoder::into_pb`**
• The call always succeeds (no panic) under the sole hypothesis `4 * len ≤ Usize.max` on the
  point count `len` of every slot, the exact bound on the byte count of a slot. Every
  well-formed state satisfies it, since a sorted slot holds at most 65536 points. The Rust code
  `hax_lib::assume!`s the stronger bound `pts.len() <= 2 * MAX_STORED_POLYNOMIAL_DEGREE_V1 + 1`.
• The extracted function agrees with its associated high-level functional model
  `FunctionalModels.intoPb` (see def).
-/
@[step]
theorem into_pb_spec (self : PolyDecoder)
    (h_overflow : ∀ s ∈ self.pts.val, 4 * s.length ≤ Usize.max) :
    into_pb self ⦃ (result : proto.pq_ratchet.PolynomialDecoder) =>
      result = FunctionalModels.intoPb self ⦄ := by
  unfold into_pb
  refine WP.spec_bind (UScalar.cast.step_spec _ _) ?_
  rintro _ rfl
  refine WP.spec_bind (Array.to_slice.step_spec _) ?_
  rintro _ rfl
  refine WP.spec_bind (Array.to_slice.step_spec _) ?_
  rintro _ rfl
  have h_len : (Slice.len self.pts.to_slice).val = 16 := Array.length_to_slice _
  refine WP.spec_bind (into_pb_loop0.loop_spec self.pts _ _
    (h_len.trans (Array.length_eq self.pts).symm).le h_overflow (by
      rw [h_len]
      exact (UScalar.hrBounds 16#usize).trans_eq
        ((UScalar.rMax_eq_max _).trans UScalar.max_USize_eq)))
    ?_
  rintro v1 v1_post
  refine (WP.spec_ok _).mpr ?_
  simp only [intoPb, proto.pq_ratchet.PolynomialDecoder.mk.injEq, true_and, and_true]
  rw [← alloc.vec.Vec.val_ofList v1, v1_post]
  exact congrArg alloc.vec.Vec.ofList ((List.nil_append _).trans (congrArg (List.map bytesOfSlot)
    (List.take_of_length_le (Nat.le_of_eq ((Array.length_eq self.pts).trans h_len.symm)))))

end spqr.encoding.polynomial.PolyDecoder
