/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong, Markus Dablander
-/
module

public import SrcTranslated.Funs
import Spqr.Auxiliary.Aeneas.Slice
import Spqr.Specs.Aeneas.RangeIteratorNext
import Spqr.Specs.Aeneas.SliceChunksExact
import Spqr.Specs.Encoding.Polynomial.Pt.Deserialize
public import Spqr.Specs.Encoding.Polynomial.PolyDecoder.FunctionalModels

/-!
# Spec theorems for `spqr::encoding::polynomial::PolyDecoder::from_pb`

`from_pb` turns the stored (protobuf) form of a `PolyDecoder` back into the in-memory form.

The stored form holds one byte string per slot, with four bytes per point. `from_pb` first checks
that there are exactly 16 byte strings and that the length of each is divisible by four, and
returns an error otherwise. It then rebuilds each slot from scratch: starting from an empty slot,
it reads the points four bytes at a time and puts each one in its place, so that the slot stays
ordered by `x`. A point whose `x` is already in the slot replaces the old one. `pts_needed` is
cast back to a `usize`, `is_complete` is copied and `polys` is ignored.

The main results:

• `from_pb_spec`: `from_pb` always finishes without crashing, and its result is exactly what its
  functional model `fromPb` in `FunctionalModels.lean` computes.

• `from_pb_spec_valid`: whenever decoding succeeds, every slot is ordered by `x` with no repeats.

The proof builds up in three steps, from the smallest piece to the whole function:

• `push_spec_insertPt`: adding one point to an ordered slot gives the same slot as the model's
  `insertPt`.

• `from_pb_loop0_loop0.loop_spec` (the inner loop): reading all points of one byte string gives
  the slot `slotOfBytes` of the model.

• `from_pb_loop0.loop_spec` (the outer loop): doing this for all 16 byte strings gives `fromPb`.

The reverse direction, from in-memory form to stored form, is `into_pb`.

**Source**: spqr/src/encoding/polynomial.rs
-/

@[expose] public section

open Aeneas Aeneas.Std

namespace spqr.encoding.polynomial.PolyDecoder
open FunctionalModels

/-- `sortedInsert` with `Pt.Insts.CoreCmpOrd` computes `insertPt` on a sorted slot. -/
private theorem sortedInsert_eq_insertPt (list : List Pt) (x : Pt) (i : Nat)
    (hs : SlotSorted list) :
    ∃ idx opt, sorted_vec.SortedSet.sortedInsert Pt.Insts.CoreCmpOrd list x i =
      .ok (idx, opt, insertPt list x) := by
  induction list generalizing i with
  | nil => exact ⟨i, none, rfl⟩
  | cons a rest ih =>
    obtain ⟨ha, hrest⟩ := List.pairwise_cons.mp hs
    have h1 (hle : x.x.value.val ≤ a.x.value.val) :
        rest.filter (·.x.value.val < x.x.value.val) = [] :=
      List.filter_eq_nil_iff.mpr fun r hr h => Nat.lt_irrefl _
        (Nat.lt_of_lt_of_le (of_decide_eq_true h) (Nat.le_trans hle (Nat.le_of_lt (ha r hr))))
    have h2 (hle : x.x.value.val ≤ a.x.value.val) :
        rest.filter (x.x.value.val < ·.x.value.val) = rest :=
      List.filter_eq_self.mpr fun r hr => decide_eq_true (Nat.lt_of_le_of_lt hle (ha r hr))
    simp only [sorted_vec.SortedSet.sortedInsert, Pt.Insts.CoreCmpOrd.cmp_eq_compare, bind_ok]
    rcases hc : compare a.x.value.val x.x.value.val
    · have hlt := Nat.compare_eq_lt.mp hc
      obtain ⟨idx', opt', h_rec⟩ := ih (i + 1) hrest
      simp only [h_rec, bind_ok]
      exact ⟨idx', opt', by simp [insertPt, hlt, Nat.lt_asymm hlt]⟩
    · have heq := Nat.compare_eq_eq.mp hc
      have hle := Nat.le_of_eq heq.symm
      exact ⟨i, some a, by simp [insertPt, heq, h1 hle, h2 hle]⟩
    · have hgt := Nat.compare_eq_gt.mp hc
      have hle := Nat.le_of_lt hgt
      exact ⟨i, none, by simp [insertPt, hgt, Nat.lt_asymm hgt, h1 hle, h2 hle]⟩

/-- Inserting a point with a larger abscissa than the last point of a sorted slot appends it: the
shape of `push_spec_gt`. -/
private theorem insertPt_eq_append_of_getLast (l : List Pt) (p last : Pt) (hs : SlotSorted l)
    (hl : l.getLast? = some last) (hlt : last.x.value.val < p.x.value.val) :
    insertPt l p = l ++ [p] := by
  obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.mp hl
  exact insertPt_eq_append fun q hq => (List.mem_append.mp hq).elim
    (fun hq => lt_trans ((List.pairwise_append.mp hs).2.2 q hq last (.head _)) hlt)
    fun hq => List.mem_singleton.mp hq ▸ hlt

/-- Inserting a point with the same abscissa as the last point of a sorted slot replaces that
point: the shape of `push_spec_eq`. -/
private theorem insertPt_eq_dropLast_append (l : List Pt) (p last : Pt) (hs : SlotSorted l)
    (hl : l.getLast? = some last) (he : p.x.value.val = last.x.value.val) :
    insertPt l p = l.dropLast ++ [p] := by
  obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.mp hl
  have hl1 : ¬ last.x.value.val < p.x.value.val := he ▸ Nat.lt_irrefl _
  have hl2 : ¬ p.x.value.val < last.x.value.val := he ▸ Nat.lt_irrefl _
  rw [List.dropLast_concat, ← insertPt_eq_append (p := p) fun q hq =>
    he ▸ (List.pairwise_append.mp hs).2.2 q hq last (.head _)]
  simp [insertPt, List.filter_append, hl1, hl2]

/-- **`SortedSet::push` computes `insertPt` on a sorted slot**
• Succeeds on every sorted slot without a capacity hypothesis, since a sorted slot holds at
  most 65536 points. -/
theorem push_spec_insertPt (v : sorted_vec.SortedSet Pt) (p : Pt) (h_sorted : SlotSorted v.val) :
    sorted_vec.SortedSet.push Pt.Insts.CoreCmpOrd v p ⦃ r =>
      r.2.val = insertPt v.val p ⦄ := by
  have h_max : 65537 ≤ Usize.max := le_trans (by decide) Usize.cMax_bound_concrete.1
  have h_push_cap : v.length + 1 ≤ Usize.max := (Nat.succ_le_succ h_sorted.length_le).trans h_max
  rcases hL : v.val.getLast? with _ | last
  · apply WP.spec_mono (sorted_vec.SortedSet.push_spec_empty Pt.Insts.CoreCmpOrd v p h_push_cap hL)
    rintro ⟨⟨_, _⟩, _⟩ ⟨_, _, h⟩
    rw [h, List.getLast?_eq_none_iff.mp hL]
    rfl
  · have hcmp := Pt.Insts.CoreCmpOrd.cmp_eq_compare p last
    rcases hc : compare p.x.value.val last.x.value.val
    · obtain ⟨idx, opt, h_si⟩ := sortedInsert_eq_insertPt v.val p 0 h_sorted
      have hbnd : (insertPt v.val p).length ≤ Usize.max ∧ idx ≤ Usize.max := by
        obtain ⟨k, rfl, hk_le, -⟩ :=
          sorted_vec.SortedSet.sortedInsert_spec Pt.Insts.CoreCmpOrd v.val p 0 h_si
        exact ⟨(slotSorted_insertPt _ p h_sorted).length_le.trans (Nat.le_of_succ_le h_max),
          (Nat.zero_add k).trans_le
            ((hk_le.trans h_sorted.length_le).trans (Nat.le_of_succ_le h_max))⟩
      apply WP.spec_mono (sorted_vec.SortedSet.push_spec_lt Pt.Insts.CoreCmpOrd v p h_push_cap
        last hL (hc ▸ hcmp) idx opt _ h_si hbnd)
      rintro ⟨⟨_, _⟩, _⟩ ⟨_, _, h⟩
      rw [h]
    · apply WP.spec_mono (sorted_vec.SortedSet.push_spec_eq Pt.Insts.CoreCmpOrd v p h_push_cap
        last hL (hc ▸ hcmp))
      rintro ⟨⟨_, _⟩, _⟩ ⟨_, _, h⟩
      rw [h, ← insertPt_eq_dropLast_append v.val p last h_sorted hL
        (Nat.compare_eq_eq.mp hc)]
    · apply WP.spec_mono (sorted_vec.SortedSet.push_spec_gt Pt.Insts.CoreCmpOrd v p h_push_cap
        last hL (hc ▸ hcmp))
      rintro ⟨⟨_, _⟩, _⟩ ⟨_, _, h⟩
      rw [h, ← insertPt_eq_append_of_getLast v.val p last h_sorted hL
        (Nat.compare_eq_gt.mp hc)]

namespace from_pb_loop0_loop0

/-- **Spec theorem for `encoding.polynomial.PolyDecoder.from_pb_loop0_loop0.body`**
• One step of the inner loop: if no chunk is left, `v` is returned unchanged; otherwise the point
  `ptsOfBytes` of the next chunk is pushed onto `v` with `insertPt`.
• Succeeds when every chunk holds four bytes and `v` is sorted. -/
@[step]
theorem body_spec
    (iter : core.slice.iter.ChunksExact U8) (v : sorted_vec.SortedSet Pt)
    (h_chunks : ∀ c ∈ iter.chunks, c.length = 4)
    (h_sorted : SlotSorted v.val) :
    body iter v ⦃ cf =>
      match cf with
      | ControlFlow.done v' => v' = v ∧ iter.chunks = []
      | ControlFlow.cont (iter1, v1) =>
          ∃ c, iter.chunks = c :: iter1.chunks ∧
            v1.val = (ptsOfBytes c.val).foldl insertPt v.val ⦄ := by
  unfold body core.slice.iter.IteratorChunksExact.next
  rcases h : iter.chunks with _ | ⟨c, rest⟩
  · rw [bind_ok]
    exact (WP.spec_ok _).mpr ⟨rfl, rfl⟩
  · have hc : c.val.length = 4 := h_chunks c (h ▸ List.mem_cons_self)
    obtain ⟨c0, c1, c2, c3, hc4⟩ := List.length_eq_four.mp hc
    rw [bind_ok, uncurry_apply_pair]
    refine WP.spec_bind (Pt.try_from_spec 4#usize core.marker.CopyU8 c (fun _ _ => rfl) hc) ?_
    rintro _ ⟨a0, rfl, ha0⟩
    refine WP.spec_bind (core.result.Result.unwrap.step_spec _ _ ⟨a0, rfl⟩) ?_
    rintro _ ha
    obtain rfl := core.result.Result.Ok.inj ha
    refine WP.spec_bind (Pt.deserialize_spec _) ?_
    rintro ⟨⟨px⟩, ⟨py⟩⟩ ⟨hpx, hpy⟩
    refine WP.spec_bind (push_spec_insertPt v _ h_sorted) ?_
    rintro ⟨_, v1⟩ (h_v1 : v1.val = _)
    refine (WP.spec_ok _).mpr ⟨c, rfl, ?_⟩
    simp only [Array.getElem!_Nat_eq, ha0, hc4, List.getElem!_cons_zero, List.getElem!_cons_succ]
      at hpx hpy
    rw [h_v1, hc4]
    exact congrArg (insertPt v.val) (congrArg₂ Pt.mk
      (congrArg _ (UScalar.eq_of_val_eq (by rw [U16.ofNatCore_val_eq, Nat.mul_comm]; exact hpx)))
      (congrArg _ (UScalar.eq_of_val_eq (by rw [U16.ofNatCore_val_eq, Nat.mul_comm]; exact hpy))))

/-- **Spec theorem for `encoding.polynomial.PolyDecoder.from_pb_loop0_loop0`**
• The inner loop run to completion: the points `ptsOfBytes` of the bytes of all chunks are
  pushed onto `v`, in order, with `insertPt`.
• Succeeds when every chunk holds four bytes and `v` is sorted. -/
@[step]
theorem loop_spec
    (iter : core.slice.iter.ChunksExact U8) (v : sorted_vec.SortedSet Pt)
    (h_chunks : ∀ c ∈ iter.chunks, c.length = 4)
    (h_sorted : SlotSorted v.val) :
    from_pb_loop0_loop0 iter v ⦃ (result : sorted_vec.SortedSet Pt) =>
      result.val = (ptsOfBytes (iter.chunks.flatMap (·.val))).foldl insertPt v.val ⦄ := by
  unfold from_pb_loop0_loop0
  apply loop.spec_decr_nat (measure := fun x => x.1.chunks.length)
    (inv := fun x => (∀ c ∈ x.1.chunks, c.length = 4) ∧ SlotSorted x.2.val ∧
      (ptsOfBytes (x.1.chunks.flatMap (·.val))).foldl insertPt x.2.val =
        (ptsOfBytes (iter.chunks.flatMap (·.val))).foldl insertPt v.val)
  · rintro ⟨iter', v'⟩ ⟨h_chunks', h_sorted', h_fold⟩
    apply WP.spec_mono (body_spec iter' v' h_chunks' h_sorted')
    rintro (⟨iter1, v1⟩ | v_final) h_cf
    · obtain ⟨c, h_cons, h_v1⟩ := h_cf
      rw [h_cons, List.forall_mem_cons] at h_chunks'
      refine ⟨⟨h_chunks'.2, h_v1 ▸ slotSorted_foldl_insertPt _ _ h_sorted', ?_⟩,
        by rw [h_cons]; exact Nat.lt_succ_self _⟩
      rw [← h_fold, h_cons, List.flatMap_cons,
        ptsOfBytes_append _ _ (congrArg (· % 4) h_chunks'.1), List.foldl_append, h_v1]
    · obtain ⟨rfl, h_nil⟩ := h_cf
      rwa [h_nil] at h_fold
  · exact ⟨h_chunks, h_sorted, rfl⟩

end from_pb_loop0_loop0

/-- Chunks holding the consecutive `n`-blocks of a list `l` of length `n * chunks.length`
concatenate to `l`: the chunks of `chunks_exact` on a slice whose length is a multiple of `n`
carry the whole slice (`chunks_exact_spec_with_content`). -/
private theorem flatMap_val_eq_of_chunks {T : Type} [Inhabited (Slice T)] (l : List T) (n : Nat)
    (chunks : List (Slice T)) (h_len : l.length = n * chunks.length)
    (h_content : ∀ j < chunks.length, chunks[j]!.val = (l.drop (n * j)).take n) :
    chunks.flatMap (·.val) = l := by
  induction chunks generalizing l with
  | nil => exact (List.eq_nil_of_length_eq_zero h_len).symm
  | cons c rest ih =>
    have hc : c.val = l.take n := h_content 0 (Nat.succ_pos _)
    rw [List.flatMap_cons, hc, ih (l.drop n) (by
        rw [List.length_drop, h_len, List.length_cons, Nat.mul_succ, Nat.add_sub_cancel])
      fun j hj => ?_, List.take_append_drop]
    have h := h_content (j + 1) (Nat.succ_lt_succ hj)
    rwa [List.getElem!_cons_succ, Nat.mul_succ, Nat.add_comm (n * j) n, ← List.drop_drop] at h

namespace from_pb_loop0

/-- **Spec theorem for `encoding.polynomial.PolyDecoder.from_pb_loop0.body`**
• One step of the outer loop: if the range is exhausted, the loop returns `Ok` with the slots
  `out_pts`; if the length of the next byte string is not a multiple of four, it returns
  `Err SerializationInvalid`; otherwise the slot `slotOfBytes` of the byte string is stored and
  the range advances by one.
• Succeeds when `v` holds 16 byte strings and `iter.end = 16`. -/
@[step]
theorem body_spec
    (i : U32) (v : alloc.vec.Vec (alloc.vec.Vec U8)) (b : Bool)
    (iter : core.ops.range.Range Usize)
    (out_pts : Array (sorted_vec.SortedSet Pt) 16#usize)
    (h_v : v.length = 16) (h_end : iter.end = 16#usize) :
    body i v b iter out_pts ⦃ cf =>
      match cf with
      | ControlFlow.done r =>
          if iter.start < iter.end then
            v[iter.start]!.length % 4 ≠ 0 ∧ r = .Err .SerializationInvalid
          else r = .Ok { pts_needed := i.cast .Usize, pts := out_pts, is_complete := b }
      | ControlFlow.cont (iter1, out_pts') => iter.start < iter.end ∧
          v[iter.start]!.length % 4 = 0 ∧
          iter1.start.val = iter.start.val + 1 ∧ iter1.end = iter.end ∧
          out_pts' = out_pts.set iter.start (slotOfBytes v[iter.start]!) ⦄ := by
  unfold body
  refine WP.spec_bind (core.iter.range.IteratorRange.next_Usize_spec' iter) ?_
  rintro ⟨opt, iter1'⟩ ⟨h_none, h_some⟩
  by_cases h_lt : iter.start < iter.end
  · obtain ⟨rfl, h_start1, h_end1⟩ := h_some h_lt
    have h_lt16 : iter.start < 16#usize := h_end ▸ h_lt
    have h_j : iter.start.val < v.val.length :=
      (show iter.start.val < 16 from h_lt16).trans_eq h_v.symm
    refine WP.spec_bind (alloc.vec.Vec.index_usize_spec v iter.start h_j) ?_
    rintro pts h_pts
    have h_pts' : v[iter.start]! = pts := by
      rw [h_pts, alloc.vec.Vec.getElem!_Usize_eq, getElem!_pos v.val _ h_j]
    rw [h_pts']
    refine WP.spec_bind (Usize.rem_spec _ (by decide : (4#usize).val ≠ 0)) ?_
    rintro i3 h_i3
    rw [alloc.vec.Vec.len_val] at h_i3
    split
    next h_ne =>
      exact (WP.spec_ok _).mpr
        ⟨fun h => bne_iff_ne.mp h_ne (UScalar.eq_of_val_eq (h_i3.trans h)), rfl⟩
    next h_ne =>
      have h_mod : pts.val.length % 4 = 0 :=
        h_i3.symm.trans (congrArg UScalar.val (not_not.mp (mt bne_iff_ne.mpr h_ne)))
      have h_bnd (w : Array (sorted_vec.SortedSet Pt) 16#usize) :
          iter.start.val < w.length :=
        (show iter.start.val < (16#usize).val from h_lt16).trans_eq (Array.length_eq w).symm
      refine WP.spec_bind (Usize.div_spec _ (by decide : (4#usize).val ≠ 0)) ?_
      rintro _ -
      refine WP.spec_bind (sorted_vec.SortedSet.with_capacity_spec _ _) ?_
      rintro _ rfl
      refine WP.spec_bind (core.slice.Slice.chunks_exact_spec_with_content _ _
        (by decide : (4#usize).val > 0)) ?_
      rintro iter2 ⟨iter2_post, iter2_post1, -, iter2_post3⟩
      refine WP.spec_bind (from_pb_loop0_loop0.loop_spec iter2 _ iter2_post .nil) ?_
      rintro v2 v2_post
      refine WP.spec_bind (massert_spec _ h_lt16) ?_
      rintro - -
      refine WP.spec_bind (Array.index_mut_usize_spec out_pts iter.start (h_bnd out_pts)) ?_
      rintro ⟨ss, _⟩ ⟨-, rfl⟩
      refine WP.spec_bind (Array.update_spec _ iter.start v2 (h_bnd _)) ?_
      rintro _ rfl
      simp only [alloc.vec.Vec.deref, Slice.from_val] at iter2_post1 iter2_post3
      have h_v2 : v2 = slotOfBytes pts := alloc.vec.Vec.ext _ _ (by
        rw [v2_post, flatMap_val_eq_of_chunks pts.val 4 _ (by
          rw [iter2_post1]; exact (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h_mod)).symm)
          iter2_post3, slotOfBytes_val]; rfl)
      exact (WP.spec_ok _).mpr ⟨h_lt, h_mod, h_start1, h_end1,
        Aeneas.Std.Array.ext _ _ (by simp [h_v2])⟩
  · obtain ⟨rfl, -⟩ := h_none h_lt
    refine WP.spec_bind (UScalar.cast.step_spec _ _) ?_
    rintro _ rfl
    exact (WP.spec_ok _).mpr ((iff_of_eq (ite_eq_right h_lt)).mpr rfl)

/-- **Spec theorem for `encoding.polynomial.PolyDecoder.from_pb_loop0`**
• The outer loop run to completion on the fields of `pb`: if the slots before `iter.start` are
  decoded with `slotOfBytes` from byte strings whose lengths are multiples of four, the result
  is `fromPb pb`.
• Succeeds when `pb.pts` holds 16 byte strings and `iter.end = 16`. -/
@[step]
theorem loop_spec
    (iter : core.ops.range.Range Usize)
    (pb : proto.pq_ratchet.PolynomialDecoder)
    (out_pts : Array (sorted_vec.SortedSet Pt) 16#usize)
    (h_v : pb.pts.length = 16) (h_end : iter.end = 16#usize)
    (h_pre : ∀ j < iter.start.val,
      pb.pts[j]!.length % 4 = 0 ∧ out_pts[j]! = slotOfBytes pb.pts[j]!) :
    from_pb_loop0 iter pb.pts_needed pb.pts pb.is_complete out_pts ⦃ (result : core.result.Result
        PolyDecoder PolynomialError) =>
      result = fromPb pb ⦄ := by
  obtain ⟨i, _polys, v, b⟩ := pb
  unfold from_pb_loop0
  apply loop.spec_decr_nat (measure := fun x => x.1.end.val - x.1.start.val)
    (inv := fun x => x.1.end = 16#usize ∧
      ∀ j < x.1.start.val, v[j]!.length % 4 = 0 ∧ x.2[j]! = slotOfBytes v[j]!)
  · rintro ⟨iter', out_pts'⟩ ⟨h_end', h_inv'⟩
    have h_end16 : iter'.end.val = 16 := congrArg UScalar.val h_end'
    apply WP.spec_mono (body_spec i v b iter' out_pts' h_v h_end')
    rintro (⟨iter'', out_pts''⟩ | r) h_cf
    · simp only at h_cf ⊢
      obtain ⟨h_lt, h_mod_s, h_start1, h_end1, rfl⟩ := h_cf
      have h_lt' : iter'.start.val < iter'.end.val := h_lt
      refine ⟨⟨h_end1.trans h_end', fun j hj => ?_⟩, by
        rw [h_end1, h_start1]; exact Nat.sub_lt_sub_left h_lt' (Nat.lt_succ_self _)⟩
      rw [h_start1] at hj
      by_cases hj_lt : j < iter'.start.val
      · rw [Array.getElem!_Nat_set_ne _ _ _ _ (Nat.ne_of_gt hj_lt)]
        exact h_inv' j hj_lt
      · obtain rfl : j = iter'.start.val :=
          Nat.le_antisymm (Nat.le_of_lt_succ hj) (Nat.le_of_not_lt hj_lt)
        rw [Array.getElem!_Nat_set_eq _ _ _ _
          ⟨rfl, (h_lt'.trans_eq h_end16).trans_eq (Array.length_eq out_pts').symm⟩]
        exact ⟨h_mod_s, rfl⟩
    · dsimp only [fromPb] at h_cf ⊢
      by_cases h_lt : iter'.start < iter'.end
      · obtain ⟨h_bad, rfl⟩ := (ite_eq_left h_lt).mp h_cf
        have hj : iter'.start.val < v.val.length :=
          (show iter'.start.val < iter'.end.val from h_lt).trans_eq (h_end16.trans h_v.symm)
        rw [dite_eq_right fun h => h_bad (h.2 _ (by
          rw [alloc.vec.Vec.getElem!_Usize_eq, getElem!_pos v.val _ hj]
          exact List.getElem_mem hj))]
      · obtain rfl := (ite_eq_right h_lt).mp h_cf
        have h_ge : 16 ≤ iter'.start.val := h_end16.symm.trans_le (Nat.le_of_not_lt h_lt)
        rw [dite_eq_left ⟨h_v, List.forall_mem_iff_getElem.mpr fun j hj => by
          have h := (h_inv' j (Nat.lt_of_lt_of_le (hj.trans_eq h_v) h_ge)).1
          rwa [alloc.vec.Vec.getElem!_Nat_eq, getElem!_pos v.val j hj] at h⟩]
        refine congrArg _ (congrArg (PolyDecoder.mk _ · b) (Aeneas.Std.Array.ext _ _ ?_))
        rw [Array.from_val]
        refine (List.eq_iff_forall_eq_getElem! _ _).mpr
          ⟨(Array.length_eq _).trans ((List.length_map _).trans h_v).symm, fun j hj => ?_⟩
        have hj16 : j < 16 := hj.trans_eq (Array.length_eq _)
        rw [List.getElem!_map_eq _ _ _ (hj16.trans_eq h_v.symm), ← Array.getElem!_Nat_eq,
          (h_inv' j (Nat.lt_of_lt_of_le hj16 h_ge)).2, alloc.vec.Vec.getElem!_Nat_eq]
  · exact ⟨h_end, h_pre⟩

end from_pb_loop0

/-- **Spec theorem for `spqr::encoding::polynomial::PolyDecoder::from_pb`**
• The call always succeeds (no panic).
• The extracted function agrees with its associated high-level functional model
  `FunctionalModels.fromPb` (see def).
-/
@[step]
theorem from_pb_spec (pb : proto.pq_ratchet.PolynomialDecoder) :
    from_pb pb ⦃ (result : core.result.Result PolyDecoder PolynomialError) =>
      result = FunctionalModels.fromPb pb ⦄ := by
  unfold from_pb
  simp only [alloc.vec.Vec.len, bne_iff_ne, ne_eq, UScalar.neq_to_neq_val,
    Usize.ofNatCore_val_eq, UScalar.ofNatCore_val_eq]
  split
  next h16 =>
    cases pb
    exact (WP.spec_ok _).mpr (by rw [fromPb, dite_eq_right fun h => h16 h.1])
  next h16 =>
    refine WP.spec_bind (core.array.from_fn_spec 16#usize _ () _ (core.array.from_fn_loop_const
      from_pb.closure.Insts.CoreOpsFunctionFnMutTupleUsizeSortedSetPt (alloc.vec.Vec.new Pt)
      (fun _ _ => bind_ok _ _) _ _ _ ((UScalar.hrBounds 16#usize).trans_eq
        ((UScalar.rMax_eq_max _).trans UScalar.max_USize_eq))) rfl) ?_
    exact fun _ _ => from_pb_loop0.loop_spec _ pb _ (not_not.mp h16) rfl
      fun j hj => (Nat.not_lt_zero j hj).elim

/-- **`from_pb` establishes `PointsValid`**
• Whenever deserialisation succeeds, every slot of the resulting decoder has strictly increasing
  abscissae. -/
theorem from_pb_spec_valid (pb : proto.pq_ratchet.PolynomialDecoder) :
    from_pb pb ⦃ (result : core.result.Result PolyDecoder PolynomialError) =>
      match result with
      | core.result.Result.Ok decoder => PointsValid decoder.pts
      | core.result.Result.Err _ => True ⦄ :=
  WP.spec_mono (from_pb_spec pb) fun
    | .Ok d, h => (wellFormed_of_fromPb pb d h.symm).2
    | .Err _, _ => trivial

end spqr.encoding.polynomial.PolyDecoder
