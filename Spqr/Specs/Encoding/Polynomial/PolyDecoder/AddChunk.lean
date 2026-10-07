/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Aeneas.GF16New
import Spqr.Specs.Aeneas.RangeIteratorNext
import Spqr.Specs.Encoding.Polynomial.PolyDecoder.NecessaryPoints
import Spqr.Specs.Encoding.Polynomial.Pt.Cmp
import Spqr.Specs.Encoding.Polynomial.PolyDecoder.FromPb

/-! # Spec theorem for `spqr::encoding::polynomial::PolyDecoder::add_chunk` — loop body 0

Each iteration builds an evaluation point from a two-byte pair and inserts it into the
polynomial's sorted set. Routing: `(chunk_index * 16 + i) % 16 = i` selects the polynomial,
`(chunk_index * 16 + i) / 16 = chunk_index` gives the x-coordinate. After all chunks,
each polynomial holds the `completePoints` format for Lagrange interpolation.

The postcondition is **conditional**: when `poly_idx < np ∨ pts[poly].len() < np` (where
`np = necessary_points(poly)`), the point is inserted; otherwise the state is unchanged.
This enables compositional reasoning over sequences of `add_chunk` calls.

**Source**: spqr/src/encoding/polynomial.rs (lines 879:4–904:5)
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf

namespace spqr.encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk_loop

private theorem u8_shl8_mod_u16_size (b : U8) :
    b.val <<< 8 % U16.size = b.val * 256 := by
  have hb : b.val ≤ 255 := by scalar_tac
  rw [Nat.shiftLeft_eq]
  simp only [Nat.reducePow]
  apply Nat.mod_eq_of_lt
  have : U16.size = 65536 := by scalar_tac
  omega

/-- Helper: prove `if a ∨ b then P else Q` from `¬a`, `¬b` and `Q`.
    Used for the "state unchanged" branch of the loop body, where neither
    `poly_idx < np` nor `pts[poly].len() < np` holds. -/
private theorem ite_or_of_neg_neg {a b : Prop} [Decidable a] [Decidable b] {P Q : Prop}
    (ha : ¬a) (hb : ¬b) (hq : Q) :
    (if a ∨ b then P else Q) :=
  Eq.mpr (if_neg (by tauto)) hq


end spqr.encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk_loop

namespace spqr.encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder

/-- The unified postcondition for a `SortedSet.push` call: the result list is obtained
    by either inserting or replacing at some position `j`. This abstracts over the
    `getLast?`/`compare` case analysis inside `SortedSet.push`. -/
def IsSortedPushResult {α : Type*} (old new_ : List α) (p : α) : Prop :=
  ∃ (j : Nat),
    j ≤ old.length ∧
    (new_ = old.take j ++ [p] ++ old.drop j ∨
     (j < old.length ∧
      new_ = old.take j ++ [p] ++ old.drop (j + 1)))

/-- `IsSortedPushResult` implies length bound: new length ≤ old length + 1. -/
theorem IsSortedPushResult.length_le {α : Type*} {old new_ : List α} {p : α}
    (h : IsSortedPushResult old new_ p) :
    new_.length ≤ old.length + 1 := by
  obtain ⟨j, hj, h_ins | ⟨hlt, h_rep⟩⟩ := h
  · rw [h_ins]; simp [List.length_append, List.length_take, List.length_drop]; omega
  · rw [h_rep]; simp [List.length_append, List.length_take, List.length_drop]; omega

end spqr.encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder

namespace spqr.encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk_loop

/-- All branches of `SortedSet.push` (empty/gt/eq/lt) satisfy `IsSortedPushResult`. -/
private theorem push_match_to_sorted_push_result
    {old new_ : List Pt} {p : Pt}
    (h : match old.getLast? with
         | none => new_ = old ++ [p]
         | some last =>
           match compare p.x.value.val last.x.value.val with
           | Ordering.gt => new_ = old ++ [p]
           | Ordering.eq => new_ = old.dropLast ++ [p]
           | Ordering.lt =>
             ∃ (j : Nat), j ≤ old.length ∧
               (new_ = old.take j ++ [p] ++ old.drop j ∨
                (j < old.length ∧
                 new_ = old.take j ++ [p] ++ old.drop (j + 1)))) :
    IsSortedPushResult old new_ p := by
  unfold IsSortedPushResult
  split at h
  · exact ⟨old.length, le_refl _, Or.inl (by grind)⟩
  · rename_i last _
    split at h
    · exact ⟨old.length, le_refl _, Or.inl (by grind)⟩
    · have hne : old ≠ [] := by intro h'; simp [h'] at *
      have hlen : 0 < old.length := by cases old <;> simp_all
      refine ⟨old.length - 1, by omega, Or.inr ⟨by omega, ?_⟩⟩
      rw [h, List.dropLast_eq_take]; simp; omega
    · exact h

/-- Helper: `getElem!` after `List.set` at the same (in-bounds) index returns
    the newly written element. -/
private theorem list_getElem!_set_self {α : Type*} [Inhabited α]
    (l : List α) (i : Nat) (a : α) (h : i < l.length) :
    (l.set i a)[i]! = a := by
  rw [getElem!_pos (h := by simpa using h)]
  simp

/-- Helper: appending `p` at the end of a list (i.e. `old ++ [p]`, the
    `Ordering.gt`/empty branches of `SortedSet.push`) is a valid
    `IsSortedPushResult` (witnessed by `j = old.length`). -/
private theorem isSortedPushResult_append {α : Type*}
    (old : List α) (p : α) :
    IsSortedPushResult old (old ++ [p]) p := by
  refine ⟨old.length, le_refl _, Or.inl ?_⟩
  simp

/-- Helper: replacing the last element of a nonempty list by `p`
    (i.e. `old.dropLast ++ [p]`, the `Ordering.eq` branch of `SortedSet.push`)
    is a valid `IsSortedPushResult`. -/
private theorem isSortedPushResult_dropLast_append {α : Type*}
    (old : List α) (p : α) (hne : old ≠ []) :
    IsSortedPushResult old (old.dropLast ++ [p]) p := by
  have hlen : 0 < old.length := by cases old <;> simp_all
  refine ⟨old.length - 1, by omega, Or.inr ⟨by omega, ?_⟩⟩
  rw [List.dropLast_eq_take]; simp; omega

/-- Packaged spec for `sortedInsert` on `Pt`: it always succeeds, the returned index
    and list satisfy the `Usize` bounds (given capacity), and the result is an
    `IsSortedPushResult`. Bundles `sortedInsert_always_ok` and `sortedInsert_spec`. -/
private theorem sortedInsert_push_result (l : List Pt) (p : Pt)
    (h_cap : l.length + 1 ≤ Usize.max) :
    ∃ idx opt newList,
      sorted_vec.SortedSet.sortedInsert Pt.Insts.CoreCmpOrd l p 0 = ok (idx, opt, newList) ∧
      (newList.length ≤ Usize.max ∧ idx ≤ Usize.max) ∧
      IsSortedPushResult l newList p := by
  obtain ⟨idx, opt, newList, h_si⟩ :=
    spqr.encoding.polynomial.PolyDecoder.from_pb_loop0_loop0.sortedInsert_always_ok l p 0
  obtain ⟨k, hk_idx, hk_le, hk_prop⟩ :=
    sorted_vec.SortedSet.sortedInsert_spec Pt.Insts.CoreCmpOrd l p 0 h_si
  have h_res : IsSortedPushResult l newList p := ⟨k, hk_le, hk_prop⟩
  exact ⟨idx, opt, newList, h_si,
    ⟨by have := h_res.length_le; omega, by omega⟩, h_res⟩

/-- `SortedSet.push` on `Pt` (with capacity) always succeeds and yields an
    `IsSortedPushResult`, whichever `getLast?`/`compare` branch is taken. -/
private theorem push_sorted_result (ss : sorted_vec.SortedSet Pt) (p : Pt)
    (h_cap : ss.val.length + 1 ≤ Usize.max) :
    sorted_vec.SortedSet.push Pt.Insts.CoreCmpOrd ss p ⦃ r =>
      IsSortedPushResult ss.val r.2.val p ⦄ := by
  rcases hL : ss.val.getLast? with _ | last
  · apply WP.spec_mono (sorted_vec.SortedSet.push_spec_empty _ ss p h_cap hL)
    rintro ⟨⟨_, _⟩, _⟩ ⟨_, _, h⟩
    rw [h]; exact isSortedPushResult_append _ _
  · have hne : ss.val ≠ [] := by intro h'; simp [h'] at hL
    rcases hc : compare p.x.value.val last.x.value.val
    · obtain ⟨idx, opt, newList, h_si, hbnd, h_res⟩ := sortedInsert_push_result ss.val p h_cap
      apply WP.spec_mono (sorted_vec.SortedSet.push_spec_lt _ ss p h_cap last hL
        (by rw [← hc]; exact PolyDecoder.from_pb_loop0_loop0.cmp_eq p last)
        idx opt newList h_si hbnd)
      rintro ⟨⟨_, _⟩, _⟩ ⟨_, _, h⟩
      rw [h]; exact h_res
    · apply WP.spec_mono (sorted_vec.SortedSet.push_spec_eq _ ss p h_cap last hL
        (by rw [← hc]; exact PolyDecoder.from_pb_loop0_loop0.cmp_eq p last))
      rintro ⟨⟨_, _⟩, _⟩ ⟨_, _, h⟩
      rw [h]; exact isSortedPushResult_dropLast_append _ _ hne
    · apply WP.spec_mono (sorted_vec.SortedSet.push_spec_gt _ ss p h_cap last hL
        (by rw [← hc]; exact PolyDecoder.from_pb_loop0_loop0.cmp_eq p last))
      rintro ⟨⟨_, _⟩, _⟩ ⟨_, _, h⟩
      rw [h]; exact isSortedPushResult_append _ _

/-- **Spec theorem for `body` (Lagrange-enriched)**:

Strengthens `body_spec_base` with `poly < 16` and `poly_idx = chunk.index.val` via
`chunk_point_routing`, and collapses the `getLast?`/`compare` branches into
`IsSortedPushResult`. Downstream Lagrange identities are proved in the interpolation modules.

**Source**: spqr/src/encoding/polynomial.rs (lines 882:12–903:13)
-/
@[step]
theorem body_spec
    (chunk : encoding.Chunk)
    (iter : core.ops.range.Range Usize)
    (self : PolyDecoder)
    (h_end_le_16 : iter.end.val ≤ 16)
    (h_overflow : chunk.index.val * 16 + 16 ≤ Usize.max)
    (h_push_cap : ∀ (k : Nat), k < 16 →
        (self.pts.val[k]!).val.length + 1 ≤ Usize.max) :
    body chunk iter self ⦃ cf =>
      match cf with
      | ControlFlow.done self' =>
          self' = self ∧ ¬(iter.start < iter.end)
      | ControlFlow.cont (iter1, self1) =>
          iter.start < iter.end ∧
          iter1.start.val = iter.start.val + 1 ∧
          iter1.end = iter.end ∧
          self1.pts_needed = self.pts_needed ∧
          self1.is_complete = self.is_complete ∧
          let i := iter.start.val
          let total_idx := chunk.index.val * 16 + i
          let poly := total_idx % 16
          let poly_idx := total_idx / 16
          let np := self.pts_needed.val / 16 +
            (if poly < self.pts_needed.val % 16 then 1 else 0)
          -- Lagrange polynomial identity properties:
          poly < 16 ∧
          poly_idx = chunk.index.val ∧
          ∃ (p : Pt),
            p.x.value.val = poly_idx ∧
            p.y.value.val = (chunk.data.val[i * 2]!).val * 256 + (chunk.data.val[i * 2 + 1]!).val ∧
            (if poly_idx < np ∨ (self.pts.val[poly]!).val.length < np
             then
               (∀ (k : Nat), k ≠ poly → self1.pts.val[k]! = self.pts.val[k]!) ∧
               IsSortedPushResult (self.pts.val[poly]!).val (self1.pts.val[poly]!).val p
             else
               self1 = self) ⦄ := by
  unfold body
  obtain ⟨⟨opt, iter1'⟩, hnext, h_none, h_some⟩ :=
    WP.spec_imp_exists (core.iter.range.IteratorRange.next_Usize_spec' iter)
  rw [hnext]
  simp only [bind_ok]
  by_cases h_lt : iter.start.val < iter.end.val
  · obtain ⟨h_opt_eq, h_start1, h_end1⟩ := h_some h_lt
    rw [h_opt_eq]
    step as ⟨i1, h_i1⟩
    step as ⟨i2, h_i2⟩
    step as ⟨total_idx, h_total⟩
    step as ⟨poly, h_poly⟩
    step as ⟨poly_idx, h_pidx⟩
    step as ⟨i3, h_i3⟩
    step as ⟨x, h_x⟩
    step as ⟨i4, h_i4⟩
    step as ⟨i5, h_i5⟩
    step as ⟨y1, h_y1⟩
    step as ⟨i6, h_i6⟩
    step as ⟨i7, h_i7⟩
    step as ⟨y2, h_y2⟩
    step as ⟨i8, h_i8, _⟩
    step as ⟨i9, h_i9⟩
    step as ⟨y, h_y⟩
    step as ⟨i10, h_i10⟩
    have h_i_lt_16 : iter.start.val < 16 := by omega
    have h_i1v : i1.val = chunk.index.val := by rw [h_i1]; exact U16.cast_Usize_val_eq chunk.index
    have h_poly' : poly.val = iter.start.val := by rw [h_poly, h_total, h_i2]; omega
    have h_pidx' : poly_idx.val = chunk.index.val := by rw [h_pidx, h_total, h_i2]; omega
    have h_px : x.value.val = chunk.index.val := by
      rw [h_x, h_i3]; simp [UScalar.cast_val_eq, h_pidx']
    have h_py : y.value.val =
        (chunk.data.val[iter.start.val * 2]!).val * 256 +
        (chunk.data.val[iter.start.val * 2 + 1]!).val := by
      simp [h_y, h_i9, h_i8, h_y1, h_y2, h_i5, h_i7, h_i4, h_i6, UScalar.cast_val_eq]
      grind [u8_shl8_mod_u16_size]
    have h_mod : (chunk.index.val * 16 + iter.start.val) % 16 = iter.start.val := by omega
    have h_div : (chunk.index.val * 16 + iter.start.val) / 16 = chunk.index.val := by omega
    have h_plt : poly.val < self.pts.val.length := by simp; omega
    have h_cap : ((self.pts.val)[poly.val]!).val.length + 1 ≤ Usize.max :=
      h_push_cap _ (by omega)
    have h_ss_eq : (self.pts.val)[poly.val]'(by omega) = (self.pts.val)[poly.val]! := by
      rw [getElem!_pos (h := by omega)]
    simp only [h_mod, h_div]
    split
    · rename_i h_c
      have h_c' : chunk.index.val < self.pts_needed.val / 16 +
          (if iter.start.val < self.pts_needed.val % 16 then 1 else 0) := by
        rw [← h_pidx', ← h_i10]; exact h_c
      step as ⟨ss, back, h_ss, h_back⟩
      step with push_sorted_result as ⟨_, ss1, h_r⟩
      subst h_back
      refine ⟨by scalar_tac, h_start1, h_end1, by omega, { x := x, y := y }, h_px, h_py, ?_⟩
      rw [if_pos (Or.inl h_c')]
      refine ⟨fun k hk => ?_, ?_⟩
      · simp only [Array.set_val_eq]; grind
      · simp only [Array.set_val_eq]
        rw [← h_poly', list_getElem!_set_self _ _ _ h_plt, ← h_ss_eq, ← h_ss]; exact h_r
    · rename_i h_c
      have h_c' : ¬ chunk.index.val < self.pts_needed.val / 16 +
          (if iter.start.val < self.pts_needed.val % 16 then 1 else 0) := by
        rw [← h_pidx', ← h_i10]; exact h_c
      step as ⟨ss0, h_ss0⟩
      step as ⟨sv, h_sv⟩
      step as ⟨v, h_v⟩
      step as ⟨i12, h_i12⟩
      have h_vlen : v.len.val = ((self.pts.val)[iter.start.val]!).val.length := by
        rw [h_v, h_sv, h_ss0, h_ss_eq, h_poly']; simp
      split
      · rename_i h_c2
        have h_c2' : ((self.pts.val)[iter.start.val]!).val.length < self.pts_needed.val / 16 +
            (if iter.start.val < self.pts_needed.val % 16 then 1 else 0) := by
          rw [← h_vlen, ← h_i12]; exact h_c2
        step as ⟨ss, back, h_ss, h_back⟩
        step with push_sorted_result as ⟨_, ss1, h_r⟩
        subst h_back
        refine ⟨by scalar_tac, h_start1, h_end1, by omega, { x := x, y := y }, h_px, h_py, ?_⟩
        rw [if_pos (Or.inr h_c2')]
        refine ⟨fun k hk => ?_, ?_⟩
        · simp only [Array.set_val_eq]; grind
        · simp only [Array.set_val_eq]
          rw [← h_poly', list_getElem!_set_self _ _ _ h_plt, ← h_ss_eq, ← h_ss]; exact h_r
      · rename_i h_c2
        have h_c2' : ¬ ((self.pts.val)[iter.start.val]!).val.length < self.pts_needed.val / 16 +
            (if iter.start.val < self.pts_needed.val % 16 then 1 else 0) := by
          rw [← h_vlen, ← h_i12]; exact h_c2
        simp only [WP.spec_ok]
        refine ⟨by scalar_tac, h_start1, h_end1, trivial, trivial, by omega, { x := x, y := y },
          h_px, h_py, ?_⟩
        exact ite_or_of_neg_neg h_c' h_c2' trivial
  · obtain ⟨h_opt_eq, _⟩ := h_none (by omega)
    simp [h_opt_eq, WP.spec_ok, h_lt]

private theorem body_pts_length_le
    (self1 self' : PolyDecoder) (p : Pt) (poly : Nat)
    (cond : Prop) [Decidable cond]
    (h_update :
      if cond then
        (∀ (k : Nat), k ≠ poly →
            self1.pts.val[k]! = self'.pts.val[k]!) ∧
        IsSortedPushResult (self'.pts.val[poly]!).val (self1.pts.val[poly]!).val p
      else
        self1 = self')
    (k : Nat) :
    (self1.pts.val[k]!).val.length ≤
      (self'.pts.val[k]!).val.length + 1 := by
  by_cases hc : cond
  · rw [if_pos hc] at h_update
    obtain ⟨h_frame, h_push⟩ := h_update
    by_cases hk : k = poly
    · subst hk; exact h_push.length_le
    · rw [h_frame k hk]; omega
  · rw [if_neg hc] at h_update
    subst h_update
    omega

/-- **Spec theorem for `PolyDecoder::add_chunk_loop`** (loop 0):

Iterates over `[iter.start, iter.end)` with `iter.end ≤ 16`, preserving `pts_needed` and
`is_complete`. Witnesses via a chain `selfs 0 = self, …, selfs n = result` where each step
builds a point and conditionally pushes it onto the appropriate sorted set. The insertion
condition `poly_idx < np ∨ pts[poly].len() < np` pins down exactly when each push occurs.

**Source**: spqr/src/encoding/polynomial.rs -/
@[step]
theorem loop_spec
    (chunk : encoding.Chunk)
    (iter : core.ops.range.Range Usize)
    (self : PolyDecoder)
    (h_end_le_16 : iter.end.val ≤ 16)
    (h_start_le : iter.start ≤ iter.end)
    (h_overflow : chunk.index.val * 16 + 16 ≤ Usize.max)
    (h_push_cap : ∀ (k : Nat), k < 16 →
        (self.pts[k]!).length + (iter.end - iter.start) + 1 ≤ Usize.max) :
    add_chunk_loop iter self chunk ⦃ (result : PolyDecoder) =>
      result.pts_needed = self.pts_needed ∧
      result.is_complete = self.is_complete ∧
      ∃ (selfs : Nat → PolyDecoder),
        selfs 0 = self ∧
        selfs (iter.end - iter.start) = result ∧
        iter.end - iter.start = iter.end - iter.start ∧
        ∀ (j : Nat), j < iter.end - iter.start →
          let i := iter.start + j
          let total_idx := chunk.index.val * 16 + i
          let poly := total_idx % 16
          let poly_idx := total_idx / 16
          let np := self.pts_needed.val / 16 +
            (if poly < self.pts_needed.val % 16 then 1 else 0)
          (selfs (j + 1)).pts_needed = self.pts_needed ∧
          (selfs (j + 1)).is_complete = self.is_complete ∧
          poly < 16 ∧
          poly_idx = chunk.index.val ∧
          ∃ (p : Pt),
            p.x.value.val = poly_idx ∧
            p.y.value.val = (chunk.data[i * 2]!) * 256 + (chunk.data[i * 2 + 1]!) ∧
            (if poly_idx < np ∨ ((selfs j).pts.val[poly]!).val.length < np
             then
               (∀ (k : Nat), k ≠ poly → (selfs (j + 1)).pts[k]! = (selfs j).pts.val[k]!) ∧
               IsSortedPushResult ((selfs j).pts.val[poly]!).val
                 ((selfs (j + 1)).pts.val[poly]!).val p
             else
               selfs (j + 1) = selfs j) ⦄ := by
  unfold add_chunk_loop
  apply loop.spec_decr_nat
    (measure := fun (p : core.ops.range.Range Usize × PolyDecoder) => p.1.end - p.1.start)
    (inv := fun (p : core.ops.range.Range Usize × PolyDecoder) =>
      p.1.end = iter.end ∧
      iter.start ≤ p.1.start ∧
      p.1.start.val ≤ p.1.end.val ∧
      p.2.pts_needed = self.pts_needed ∧
      p.2.is_complete = self.is_complete ∧
      (∀ (k : Nat), k < 16 →
          (p.2.pts.val[k]!).val.length +
            (p.1.end.val - p.1.start.val) + 1 ≤ Usize.max) ∧
      ∃ (n : Nat) (selfs : Nat → PolyDecoder),
        selfs 0 = self ∧ selfs n = p.2 ∧
        n = p.1.start.val - iter.start.val ∧
        ∀ (j : Nat), j < n →
          let i := iter.start.val + j
          let total_idx := chunk.index.val * 16 + i
          let poly := total_idx % 16
          let poly_idx := total_idx / 16
          let np := self.pts_needed.val / 16 +
            (if poly < self.pts_needed.val % 16 then 1 else 0)
          (selfs (j + 1)).pts_needed = self.pts_needed ∧
          (selfs (j + 1)).is_complete = self.is_complete ∧
          poly < 16 ∧
          poly_idx = chunk.index.val ∧
          ∃ (p : Pt),
            p.x.value.val = poly_idx ∧
            p.y.value.val =
              (chunk.data.val[i * 2]!).val * 256 +
              (chunk.data.val[i * 2 + 1]!).val ∧
            (if poly_idx < np ∨
                ((selfs j).pts.val[poly]!).val.length < np
             then
               (∀ (k : Nat), k ≠ poly →
                   (selfs (j + 1)).pts.val[k]! = (selfs j).pts.val[k]!) ∧
               IsSortedPushResult ((selfs j).pts.val[poly]!).val
                 ((selfs (j + 1)).pts.val[poly]!).val p
             else
               selfs (j + 1) = selfs j))
  · rintro ⟨iter', self'⟩ ⟨h_end', h_orig_le, h_le', h_pn', h_ic', h_cap',
            n, selfs', h_s0, h_sn, h_n, h_chain⟩
    simp only [] at h_end' h_orig_le h_le' h_pn' h_ic' h_cap' h_s0 h_sn h_n h_chain ⊢
    have h_end_val : iter'.end.val = iter.end.val := by rw [h_end']
    have h_push_cap' : ∀ k, k < 16 →
        (self'.pts.val[k]!).val.length + 1 ≤ Usize.max := by
      intro k hk; have := h_cap' k hk; omega
    have h_body := body_spec chunk iter' self'
      (by rw [h_end_val]; exact h_end_le_16) h_overflow h_push_cap'
    apply WP.spec_mono h_body
    intro cf h_cf
    match cf with
    | ControlFlow.done self_final =>
      simp only [] at h_cf ⊢
      obtain ⟨h_eq, h_not_lt⟩ := h_cf
      subst h_eq
      have h_eq_n : iter.end.val - iter.start.val = n := by
        have : ¬ iter'.start.val < iter'.end.val := h_not_lt
        omega
      refine ⟨h_pn', h_ic', selfs', h_s0, by rw [h_eq_n]; exact h_sn, trivial, fun j hj => ?_⟩
      simpa only [Array.getElem!_Nat_eq] using h_chain j (by omega)
    | ControlFlow.cont (iter1, self1) =>
      simp only [] at h_cf ⊢
      obtain ⟨h_lt, h_start1, h_end1, h_pn1, h_ic1, h_poly_lt, h_poly_idx_eq,
              p, h_px, h_py, h_update⟩ := h_cf
      refine ⟨⟨by rw [h_end1]; exact h_end',
              by grind, by grind,
              by rw [h_pn1]; exact h_pn',
              by rw [h_ic1]; exact h_ic', ?_,
              n + 1, Function.update selfs' (n + 1) self1,
              ?_, ?_, ?_, ?_⟩, by grind⟩
      · intro k hk
        have h_old := h_cap' k hk
        have h_len_le := body_pts_length_le self1 self' p
          ((chunk.index.val * 16 + iter'.start.val) % 16) _ h_update k
        rw [h_start1, h_end1, h_end_val]
        rw [h_end_val] at h_old
        grind
      · have h0 : (0 : Nat) ≠ n + 1 := by omega
        simp [h_s0]
      · simp [Function.update_self]
      · grind
      · intro j hj
        by_cases hj_lt : j < n
        · obtain ⟨pn_j, ic_j, h_poly_lt', h_poly_idx_eq', p', h_px', h_py', h_upd'⟩ :=
            h_chain j hj_lt
          have h1 : j ≠ n + 1 := by omega
          have h2 : j + 1 ≠ n + 1 := by omega
          simp only [Function.update_of_ne h1, Function.update_of_ne h2]
          exact ⟨pn_j, ic_j, h_poly_lt', h_poly_idx_eq', p', h_px', h_py', h_upd'⟩
        · have hj_eq : j = n := by omega
          subst hj_eq
          have hne : j ≠ j + 1 := by omega
          simp only [Function.update_of_ne hne, Function.update_self, h_sn]
          have h_i_eq : iter.start.val + j = iter'.start.val := by grind
          simp only [h_i_eq]
          refine ⟨by rw [h_pn1]; exact h_pn',
                  by rw [h_ic1]; exact h_ic',
                  h_poly_lt, h_poly_idx_eq,
                  p, h_px, h_py, (by grind)⟩
  · refine ⟨rfl, le_refl _, h_start_le, rfl, rfl, ?_,
            0, fun _ => self, rfl, rfl, by dsimp; omega, fun j hj => by omega⟩
    intro k hk
    have := h_push_cap k hk
    simp only [Array.getElem!_Nat_eq, alloc.vec.Vec.length] at this
    omega

end spqr.encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk_loop

/-! # Spec theorem for `spqr::encoding::polynomial::{impl Decoder for PolyDecoder}::add_chunk`

Processes a 32-byte `Chunk` by iterating its 16 two-byte pairs, building points and
conditionally pushing them onto `pts[poly]`. Delegates to `add_chunk_loop` with range `0..16`.
Preserves `pts_needed` and `is_complete`.

**Source**: spqr/src/encoding/polynomial.rs -/

namespace spqr.encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder

open add_chunk_loop in
/-- **Spec theorem for `encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk`**:

Delegates to `add_chunk_loop` with range `0..16`. Preserves `pts_needed` and `is_complete`.
Witnessed by 16 intermediate states, each building a point and conditionally pushing it onto
the appropriate sorted set. The insertion condition pins down when each push occurs. -/
@[step]
theorem add_chunk_spec
    (self : PolyDecoder) (chunk : encoding.Chunk)
    (h_overflow : chunk.index * 16 + 16 ≤ Usize.max)
    (h_push_cap : ∀ (k : Nat), k < 16 → (self.pts[k]!).length + 17 ≤ Usize.max) :
    add_chunk self chunk ⦃ (result : PolyDecoder) =>
      result.pts_needed = self.pts_needed ∧
      result.is_complete = self.is_complete ∧
      ∃ (selfs : Nat → PolyDecoder),
        selfs 0 = self ∧
        selfs 16 = result ∧
        ∀ (j : Nat), j < 16 →
          let total_idx := chunk.index.val * 16 + j
          let poly := total_idx % 16
          let poly_idx := total_idx / 16
          let np := self.pts_needed.val / 16 +
            (if poly < self.pts_needed.val % 16 then 1 else 0)
          (selfs (j + 1)).pts_needed = self.pts_needed ∧
          (selfs (j + 1)).is_complete = self.is_complete ∧
          poly < 16 ∧
          poly_idx = chunk.index.val ∧
          ∃ (p : Pt),
            p.x.value.val = poly_idx ∧
            p.y.value.val = (chunk.data[j * 2]!) * 256 + (chunk.data[j * 2 + 1]!) ∧
            (if poly_idx < np ∨ ((selfs j).pts.val[poly]!).val.length < np
             then
               (∀ (k : Nat), k ≠ poly → (selfs (j + 1)).pts[k]! = (selfs j).pts.val[k]!) ∧
               IsSortedPushResult ((selfs j).pts.val[poly]!).val
                 ((selfs (j + 1)).pts.val[poly]!).val p
             else
               selfs (j + 1) = selfs j) ⦄ := by
  unfold add_chunk
  apply WP.spec_mono (add_chunk_loop.loop_spec chunk
    { start := 0#usize, «end» := 16#usize } self
    (by scalar_tac) (by scalar_tac) h_overflow
    (by intro k hk; have := h_push_cap k hk; grind))
  intro r ⟨h1, h2, s, h3, h4, _, h5⟩
  refine ⟨h1, h2, s, h3, h4, fun j hj => ?_⟩
  have h := h5 j hj
  simp only [show (0#usize : Usize).val = 0 from rfl, Nat.zero_add] at h
  exact h

end spqr.encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder
