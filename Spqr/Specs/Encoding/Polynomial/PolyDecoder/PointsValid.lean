/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import SrcTranslated.Funs
import Spqr.Specs.Encoding.Polynomial.Pt.Cmp
public import Spqr.Specs.Encoding.Polynomial.PolyDecoder.NewWithPolyCount

/-!
# The `PolyDecoder` point-set invariant

Rust stores the received evaluation points of each polynomial slot in a `SortedSet<Pt>`,
whose `Ord` instance compares abscissae only.  The Lean model represents a `SortedSet<Pt>` as a
plain `Vec Pt`, so neither sortedness nor uniqueness of abscissae is enforced by the type.

This file makes the invariant explicit:

* `SlotSorted l` — the abscissae of `l` are strictly increasing (hence pairwise distinct);
* `PointsValid pts` — every one of the 16 slots is `SlotSorted`.

It also proves that `SortedSet::push` (the only way points are ever added) preserves
`SlotSorted` (`push_spec_sorted`), which is what `new`, `from_pb` and `add_chunk` need to
establish / preserve `PointsValid`.  Under this invariant a `binary_search` match is unique,
which justifies the `lookupY` characterisation used by `decoded_message` (see
`DecodedMessage/Defs.lean`).
-/

@[expose] public section

open Aeneas Aeneas.Std Result spqr.encoding.polynomial

namespace spqr.encoding.polynomial.Pt.Insts.CoreCmpOrd

/-- `Pt.Insts.CoreCmpOrd.cmp` always succeeds, comparing x-coordinates. -/
theorem cmp_eq_compare (a b : Pt) :
    cmp a b = ok (compare a.x.value.val b.x.value.val) := by
  have h := cmp_spec a b
  cases hm : cmp a b with
  | ret r => rw [hm, WP.spec_ok] at h; rw [h]
  | vis e k => rw [hm] at h; exact ((WP.spec_vis e k).mp h).elim
  | div => rw [hm] at h; exact (WP.spec_div.mp h).elim

end spqr.encoding.polynomial.Pt.Insts.CoreCmpOrd

namespace spqr.encoding.polynomial.PolyDecoder

/-! ## Definitions -/

/-- A slot's point list has strictly increasing abscissae: this is what Rust's
`SortedSet<Pt>` guarantees (sorted, no two points with the same `x`). -/
def SlotSorted (l : List Pt) : Prop :=
  l.Pairwise (fun p q => p.x.value.val < q.x.value.val)

/-- Every one of the 16 slots of a decoder's point array is `SlotSorted`. -/
def PointsValid (pts : Array (sorted_vec.SortedSet Pt) 16#usize) : Prop :=
  ∀ slot ∈ pts.val, SlotSorted slot.val

/-! ## Basic lemmas -/

theorem SlotSorted.nil : SlotSorted [] := List.Pairwise.nil

theorem SlotSorted.singleton (p : Pt) : SlotSorted [p] := List.pairwise_singleton _ _

theorem PointsValid.slot {pts : Array (sorted_vec.SortedSet Pt) 16#usize}
    (h : PointsValid pts) (j : Nat) (hj : j < 16) :
    SlotSorted (pts.val[j]'(by simp; omega)).val :=
  h _ (List.getElem_mem _)

theorem PointsValid.slot! {pts : Array (sorted_vec.SortedSet Pt) 16#usize}
    (h : PointsValid pts) (j : Nat) (hj : j < 16) :
    SlotSorted (pts.val[j]!).val := by
  rw [getElem!_pos pts.val j (by simp; omega)]
  exact h.slot j hj

theorem PointsValid_of_slots {pts : Array (sorted_vec.SortedSet Pt) 16#usize}
    (h : ∀ j (hj : j < 16), SlotSorted (pts.val[j]'(by simp; omega)).val) :
    PointsValid pts := by
  intro s hs
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hs
  exact h j (by simpa using hj)

theorem PointsValid_of_slots! {pts : Array (sorted_vec.SortedSet Pt) 16#usize}
    (h : ∀ j, j < 16 → SlotSorted (pts.val[j]!).val) :
    PointsValid pts := by
  apply PointsValid_of_slots
  intro j hj
  have := h j hj
  rwa [getElem!_pos pts.val j (by simp; omega)] at this

/-- Overwriting one slot with a sorted slot preserves the invariant. -/
theorem PointsValid.set {pts : Array (sorted_vec.SortedSet Pt) 16#usize}
    (h : PointsValid pts) (i : Usize) (s : sorted_vec.SortedSet Pt) (hs : SlotSorted s.val) :
    PointsValid (pts.set i s) := by
  intro t ht
  rw [Array.set_val_eq] at ht
  rcases List.mem_or_eq_of_mem_set ht with h1 | rfl
  · exact h t h1
  · exact hs

/-- An array whose slots are all the empty set is valid. -/
theorem PointsValid_of_forall_nil {pts : Array (sorted_vec.SortedSet Pt) 16#usize}
    (h : ∀ slot ∈ pts.val, slot.val = []) : PointsValid pts := by
  intro s hs
  rw [SlotSorted, h s hs]
  exact List.Pairwise.nil

/-! ## `sortedInsert` and `push` preserve sortedness -/

/-- `sortedInsert` with `Pt.Insts.CoreCmpOrd` always returns `ok`, because
    `Pt.Insts.CoreCmpOrd.cmp` always succeeds. -/
theorem sortedInsert_Pt_ok (list : List Pt) (x : Pt) (i : Nat) :
    ∃ idx opt newList,
      sorted_vec.SortedSet.sortedInsert Pt.Insts.CoreCmpOrd list x i =
      ok (idx, opt, newList) := by
  induction list generalizing i with
  | nil => exact ⟨i, none, [x], rfl⟩
  | cons a rest ih =>
    simp only [sorted_vec.SortedSet.sortedInsert, Pt.Insts.CoreCmpOrd.cmp_eq_compare, bind_ok]
    split
    · exact ⟨i, none, x :: a :: rest, rfl⟩
    · exact ⟨i, some a, x :: rest, rfl⟩
    · obtain ⟨idx', opt', newList', h_rec⟩ := ih (i + 1)
      simp only [h_rec, bind_ok]
      exact ⟨idx', opt', a :: newList', rfl⟩

/-- `sortedInsert` into a `SlotSorted` list yields a `SlotSorted` list whose elements are
either old elements or the inserted point. -/
theorem sortedInsert_Pt_sorted (list : List Pt) (x : Pt) (i : Nat) (hs : SlotSorted list)
    {idx : Nat} {opt : Option Pt} {newList : List Pt}
    (h : sorted_vec.SortedSet.sortedInsert Pt.Insts.CoreCmpOrd list x i =
      ok (idx, opt, newList)) :
    SlotSorted newList ∧ ∀ q ∈ newList, q ∈ list ∨ q = x := by
  induction list generalizing i idx opt newList with
  | nil =>
    simp only [sorted_vec.SortedSet.sortedInsert, ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨SlotSorted.singleton x, by simp⟩
  | cons a rest ih =>
    simp only [sorted_vec.SortedSet.sortedInsert, Pt.Insts.CoreCmpOrd.cmp_eq_compare,
      bind_ok] at h
    rw [SlotSorted, List.pairwise_cons] at hs
    obtain ⟨ha, hrest⟩ := hs
    rcases Nat.lt_trichotomy a.x.value.val x.x.value.val with hlt | heq | hgt
    · rw [Nat.compare_eq_lt.mpr hlt] at h
      obtain ⟨idx', opt', rest', hrec⟩ := sortedInsert_Pt_ok rest x (i + 1)
      simp only [hrec, bind_ok, uncurry_apply_pair, ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      obtain ⟨ih1, ih2⟩ := ih (i + 1) hrest hrec
      refine ⟨List.pairwise_cons.mpr ⟨fun q hq => ?_, ih1⟩, fun q hq => ?_⟩
      · rcases ih2 q hq with h1 | rfl
        · exact ha q h1
        · exact hlt
      · simp only [List.mem_cons] at hq ⊢
        rcases hq with rfl | hq
        · exact Or.inl (Or.inl rfl)
        · rcases ih2 q hq with h1 | h1
          · exact Or.inl (Or.inr h1)
          · exact Or.inr h1
    · rw [Nat.compare_eq_eq.mpr heq] at h
      simp only [ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨List.pairwise_cons.mpr ⟨fun q hq => ?_, hrest⟩, fun q hq => ?_⟩
      · rw [← heq]; exact ha q hq
      · simp only [List.mem_cons] at hq ⊢
        rcases hq with rfl | hq
        · exact Or.inr rfl
        · exact Or.inl (Or.inr hq)
    · rw [Nat.compare_eq_gt.mpr hgt] at h
      simp only [ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨List.pairwise_cons.mpr ⟨fun q hq => ?_, List.pairwise_cons.mpr ⟨ha, hrest⟩⟩,
        fun q hq => ?_⟩
      · simp only [List.mem_cons] at hq
        rcases hq with rfl | hq
        · exact hgt
        · exact lt_trans hgt (ha q hq)
      · simp only [List.mem_cons] at hq ⊢
        tauto

/-- **`SortedSet::push` preserves `SlotSorted`** (for the `Pt` ordering), whichever
`getLast?`/`compare` branch is taken. -/
theorem push_spec_sorted (s : sorted_vec.SortedSet Pt) (x : Pt)
    (h_cap : s.val.length + 1 ≤ Usize.max) :
    sorted_vec.SortedSet.push Pt.Insts.CoreCmpOrd s x ⦃ r =>
      SlotSorted s.val → SlotSorted r.2.val ⦄ := by
  rcases hL : s.val.getLast? with _ | last
  · apply WP.spec_mono (sorted_vec.SortedSet.push_spec_empty _ s x h_cap hL)
    rintro ⟨⟨_, _⟩, _⟩ ⟨_, _, h⟩ _
    rw [h, List.getLast?_eq_none_iff.mp hL]
    exact SlotSorted.singleton x
  · obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hL
    rcases hc : compare x.x.value.val last.x.value.val
    · -- `x < last`: fall back to `sortedInsert`
      obtain ⟨idx, opt, newList, h_si⟩ := sortedInsert_Pt_ok s.val x 0
      obtain ⟨k, _, hk_le, hk_prop⟩ :=
        sorted_vec.SortedSet.sortedInsert_spec Pt.Insts.CoreCmpOrd s.val x 0 h_si
      have hbnd : newList.length ≤ Usize.max ∧ idx ≤ Usize.max := by
        constructor
        · rcases hk_prop with h_ins | ⟨_, h_rep⟩
          · rw [h_ins]; simp only [List.length_append, List.length_take, List.length_drop]
            grind
          · rw [h_rep]; simp only [List.length_append, List.length_take, List.length_drop]
            grind
        · grind
      apply WP.spec_mono (sorted_vec.SortedSet.push_spec_lt Pt.Insts.CoreCmpOrd s x h_cap
        last hL (by rw [← hc]; exact Pt.Insts.CoreCmpOrd.cmp_eq_compare x last) idx opt newList
        h_si hbnd)
      rintro ⟨⟨_, _⟩, _⟩ ⟨_, _, h⟩ hs
      rw [h]
      exact (sortedInsert_Pt_sorted s.val x 0 hs h_si).1
    · -- `x = last`: replace the last element
      apply WP.spec_mono (sorted_vec.SortedSet.push_spec_eq Pt.Insts.CoreCmpOrd s x h_cap
        last hL (by rw [← hc]; exact Pt.Insts.CoreCmpOrd.cmp_eq_compare x last))
      rintro ⟨⟨_, _⟩, _⟩ ⟨_, _, h⟩ hs
      have heq := Nat.compare_eq_eq.mp hc
      rw [h, hys, List.dropLast_concat]
      rw [hys] at hs
      unfold SlotSorted at hs ⊢
      rw [List.pairwise_append] at hs ⊢
      refine ⟨hs.1, List.pairwise_singleton _ _, fun p hp q hq => ?_⟩
      simp only [List.mem_singleton] at hq
      subst hq
      rw [heq]
      exact hs.2.2 p hp last (by simp)
    · -- `x > last`: append
      apply WP.spec_mono (sorted_vec.SortedSet.push_spec_gt Pt.Insts.CoreCmpOrd s x h_cap
        last hL (by rw [← hc]; exact Pt.Insts.CoreCmpOrd.cmp_eq_compare x last))
      rintro ⟨⟨_, _⟩, _⟩ ⟨_, _, h⟩ hs
      have hgt := Nat.compare_eq_gt.mp hc
      rw [h]
      unfold SlotSorted at hs ⊢
      rw [List.pairwise_append]
      refine ⟨hs, List.pairwise_singleton _ _, fun p hp q hq => ?_⟩
      simp only [List.mem_singleton] at hq
      subst hq
      rw [hys] at hp hs
      rw [List.pairwise_append] at hs
      simp only [List.mem_append, List.mem_singleton] at hp
      rcases hp with hp | rfl
      · exact lt_trans (hs.2.2 p hp last (by simp)) hgt
      · exact hgt

end spqr.encoding.polynomial.PolyDecoder
