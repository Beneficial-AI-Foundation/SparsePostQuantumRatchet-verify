/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import Spqr.Math.Poly.ModByMonic
import Spqr.Auxiliary.Aeneas.Result
import Spqr.Specs.Aeneas.RangeIteratorNext
import Spqr.Specs.Aeneas.SliceChunksExact
public import Spqr.Math.List
public import Spqr.Math.Gf16.Field
import Spqr.Specs.Encoding.Polynomial.Pt.Deserialize
public import Spqr.Specs.Encoding.Polynomial.PolyDecoder.IntoPb
import Spqr.Specs.Encoding.Polynomial.Pt.Cmp
public import Spqr.Specs.Encoding.Polynomial.PolyDecoder.PointsValid
public import Spqr.Auxiliary.Aeneas.Slice
public import Spqr.Specs.Encoding.Polynomial.PolyDecoder.NewWithPolyCount
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Order.Int.ConditionallyCompleteOrder
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.Tactic.ComputeDegree
import Spqr.Auxiliary.Aeneas.StdNextStepUsize
import Spqr.Math.Gf16.Irreducible
import Spqr.Math.Poly.Basic.Zero
import Spqr.Math.Poly.LinearFactors.Degree
import Spqr.Specs.Aeneas.VecExtendFromSlice
import Spqr.Specs.Encoding.EncodingError.From
import Spqr.Specs.Encoding.Polynomial.PolyDecoder.CallMut
import Spqr.Specs.Encoding.Polynomial.Pt.PartialCmp
import Spqr.Specs.Encoding.Polynomial.Pt.Serialize

/-! # Spec theorem for `PolyDecoder::from_pb`: loop body 1

One step of the inner point-deserialization loop `for pt in pts.chunks_exact(4)`. Given a
`ChunksExact<u8>` iterator and a sorted set `v`, the body either terminates (no chunks left) or
pops the next 4-byte chunk, deserializes it (big-endian) into a `Pt` over GF(2¹⁶), and pushes
the point onto `v`.

**Source**: spqr/src/encoding/polynomial.rs -/

@[expose] public section

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf

namespace spqr.encoding.polynomial.PolyDecoder.from_pb_loop0_loop0

/-- `Pt.Insts.CoreCmpOrd.cmp` always succeeds, comparing x-coordinates. -/
theorem cmp_eq (a b : Pt) :
    Pt.Insts.CoreCmpOrd.cmp a b = ok (compare a.x.value.val b.x.value.val) := by
  obtain ⟨r, h, hr⟩ := WP.spec_imp_exists (Pt.Insts.CoreCmpOrd.cmp_spec a b)
  rw [h, hr]

/-- `sortedInsert` with `Pt.Insts.CoreCmpOrd` always returns `ok`, because
    `Pt.Insts.CoreCmpOrd.cmp` always succeeds. -/
theorem sortedInsert_always_ok (list : List Pt) (x : Pt) (i : Nat) :
    ∃ idx opt newList,
      sorted_vec.SortedSet.sortedInsert Pt.Insts.CoreCmpOrd list x i =
      ok (idx, opt, newList) := by
  induction list generalizing i with
  | nil => exact ⟨i, none, [x], rfl⟩
  | cons a rest ih =>
    simp only [sorted_vec.SortedSet.sortedInsert, cmp_eq, bind_ok]
    split
    · -- gt
      exact ⟨i, none, x :: a :: rest, rfl⟩
    · -- eq
      exact ⟨i, some a, x :: rest, rfl⟩
    · -- lt: recursive
      obtain ⟨idx', opt', newList', h_rec⟩ := ih (i + 1)
      simp only [h_rec, bind_ok]
      exact ⟨idx', opt', a :: newList', rfl⟩

/-- The postcondition of one `SortedSet::push` of the point `p` onto `v`, yielding `v1`,
    as a case split mirroring the `SortedSet.push` definition. -/
theorem push_chain_spec (v : sorted_vec.SortedSet Pt) (p : Pt)
    (h_push_cap : v.length + 1 ≤ Usize.max) :
    sorted_vec.SortedSet.push Pt.Insts.CoreCmpOrd v p ⦃ r =>
      match v.val.getLast? with
      | none => r.2.val = v.val ++ [p]
      | some last =>
        match (Pt.Insts.CoreCmpOrd.cmp p last).match with
        | .ok Ordering.gt => r.2.val = v.val ++ [p]
        | .ok Ordering.eq => r.2.val = v.val.dropLast ++ [p]
        | .ok Ordering.lt =>
            ∃ (i : Nat),
              i ≤ v.val.length ∧
              (r.2.val = v.val.take i ++ [p] ++ v.val.drop i ∨
               (i < v.val.length ∧
                r.2.val = v.val.take i ++ [p] ++ v.val.drop (i + 1)))
        | _ => False ⦄ := by
  rcases hL : v.val.getLast? with _ | last
  · apply WP.spec_mono (sorted_vec.SortedSet.push_spec_empty Pt.Insts.CoreCmpOrd v p h_push_cap hL)
    rintro ⟨⟨_, _⟩, _⟩ h
    simp only at h ⊢
    exact h.2.2
  · rcases hc : compare p.x.value.val last.x.value.val
    · obtain ⟨idx, opt, newList, h_si⟩ := sortedInsert_always_ok v.val p 0
      obtain ⟨k, hk_idx, hk_le, hk_prop⟩ :=
        sorted_vec.SortedSet.sortedInsert_spec Pt.Insts.CoreCmpOrd v.val p 0 h_si
      have hbnd : newList.length ≤ Usize.max ∧ idx ≤ Usize.max := by
        constructor
        · rcases hk_prop with h_ins | ⟨_, h_rep⟩
          · rw [h_ins]; simp only [List.length_append, List.length_take, List.length_drop]
            grind
          · rw [h_rep]; simp only [List.length_append, List.length_take, List.length_drop]
            grind
        · grind
      apply WP.spec_mono (sorted_vec.SortedSet.push_spec_lt Pt.Insts.CoreCmpOrd v p h_push_cap
        last hL (by rw [← hc]; exact cmp_eq p last) idx opt newList h_si hbnd)
      rintro ⟨⟨_, _⟩, _⟩ h
      simp only [cmp_eq, hc, Result.match.ok] at h ⊢
      grind
    · apply WP.spec_mono (sorted_vec.SortedSet.push_spec_eq Pt.Insts.CoreCmpOrd v p h_push_cap
        last hL (by rw [← hc]; exact cmp_eq p last))
      rintro ⟨⟨_, _⟩, _⟩ h
      simp only [cmp_eq, hc, Result.match.ok] at h ⊢
      exact h.2.2
    · apply WP.spec_mono (sorted_vec.SortedSet.push_spec_gt Pt.Insts.CoreCmpOrd v p h_push_cap
        last hL (by rw [← hc]; exact cmp_eq p last))
      rintro ⟨⟨_, _⟩, _⟩ h
      simp only [cmp_eq, hc, Result.match.ok] at h ⊢
      exact h.2.2

/-- **Spec theorem for `encoding.polynomial.PolyDecoder.from_pb_loop0_loop0.body`**:

• Takes a `ChunksExact<u8>` iterator `iter` (all of whose chunks have length 4) and a sorted
  set accumulator `v : SortedSet<Pt>` of already-deserialized points.
• If the iterator is exhausted: returns `done v` — the set is unchanged.
• Otherwise pops the next 4-byte chunk `c`, converts it to a `[u8; 4]`, calls
  `Pt::deserialize` to reconstruct the GF(2¹⁶) point `p`, and pushes `p` onto `v`.

The update to the sorted set mirrors the `SortedSet.push` definition:
  - **Empty** (`v.val.getLast? = none`): `v₁.val = v.val ++ [p]`
  - **Greater** (`cmp p last = .gt`): `v₁.val = v.val ++ [p]`
  - **Equal** (`cmp p last = .eq`): `v₁.val = v.val.dropLast ++ [p]`
  - **Less** (`cmp p last = .lt`): sorted-insert at position `i`, either
    inserting (`v₁.val = v.val.take i ++ [p] ++ v.val.drop i`) or
    replacing (`v₁.val = v.val.take i ++ [p] ++ v.val.drop (i + 1)`) -/
@[step]
theorem body_spec
    (iter : core.slice.iter.ChunksExact U8)
    (v : sorted_vec.SortedSet Pt)
    (h_chunks : ∀ c ∈ iter.chunks, c.val.length = 4)
    (h_push_cap : v.length + 1 ≤ Usize.max) :
    body iter v ⦃ cf =>
      match cf with
      | ControlFlow.done v' =>
          v' = v ∧ iter.chunks = []
      | ControlFlow.cont (iter1, v1) =>
          ∃ (c : Slice U8), iter.chunks = c :: iter1.chunks ∧
          ∃ (p : Pt),
            p.x.value.val = (c.val[0]!).val * 256 + (c.val[1]!).val ∧
            p.y.value.val = (c.val[2]!).val * 256 + (c.val[3]!).val ∧
            match v.val.getLast? with
            | none => v1.val = v.val ++ [p]
            | some last =>
              match (Pt.Insts.CoreCmpOrd.cmp p last).match with
              | .ok Ordering.gt => v1.val = v.val ++ [p]
              | .ok Ordering.eq => v1.val = v.val.dropLast ++ [p]
              | .ok Ordering.lt =>
                  ∃ (i : Nat),
                    i ≤ v.val.length ∧
                    (v1.val = v.val.take i ++ [p] ++ v.val.drop i ∨
                     (i < v.val.length ∧
                      v1.val = v.val.take i ++ [p] ++ v.val.drop (i + 1)))
              | _ => False ⦄ := by
  unfold body core.slice.iter.IteratorChunksExact.next
  rcases h : iter.chunks with _ | ⟨c, rest⟩
  · simp
  · have hc : c.val.length = 4 := h_chunks c (by simp [h])
    step as ⟨r, a0, hr0, ha0⟩
    step as ⟨a, ha⟩
    step as ⟨p, hpx, hpy⟩
    step with push_chain_spec v p h_push_cap
    have hac : a.val = c.val := by
      rw [hr0] at ha
      cases ha
      exact ha0
    refine ⟨c, rfl, p, ?_, ?_, ‹_›⟩
    · simp [hpx, Array.getElem!_Nat_eq, hac]
    · simp [hpy, Array.getElem!_Nat_eq, hac]

/-- **Spec theorem for `encoding.polynomial.PolyDecoder.from_pb_loop0_loop0`**:

• Takes a `ChunksExact<u8>` iterator `iter` (all of whose chunks have length 4) and a sorted
  set accumulator `v : SortedSet<Pt>`.
• For each remaining chunk, deserializes it into a `Pt` and pushes it onto the set.
• Returns the final sorted set.

The postcondition witnesses an intermediate sequence `vs : Nat → SortedSet Pt` with
`vs 0 = v` and `vs n = v_result`, where `n = iter.chunks.length`, and for each `k < n` the
point decoded from chunk `k` (big-endian) and the push step from `vs k` to `vs (k+1)`.

**Source**: spqr/src/encoding/polynomial.rs (lines 859:12-861:13)
-/
@[step]
theorem loop_spec
    (iter : core.slice.iter.ChunksExact U8)
    (v : sorted_vec.SortedSet Pt)
    (h_chunks : ∀ c ∈ iter.chunks, c.val.length = 4)
    (h_v_room : v.length + iter.chunks.length + 1 ≤ Usize.max) :
    from_pb_loop0_loop0 iter v ⦃ (v_result : sorted_vec.SortedSet Pt) =>
      ∃ (vs : Nat → sorted_vec.SortedSet Pt),
        vs 0 = v ∧ vs iter.chunks.length = v_result ∧
        ∀ (k : Nat), k < iter.chunks.length →
          ∃ (p : Pt),
            p.x.value.val = 256 * ((iter.chunks[k]!).val[0]!).val +
              ((iter.chunks[k]!).val[1]!).val ∧
            p.y.value.val = 256 * ((iter.chunks[k]!).val[2]!).val +
              ((iter.chunks[k]!).val[3]!).val ∧
            match (vs k).val.getLast? with
            | none => (vs (k + 1)).val = (vs k).val ++ [p]
            | some last =>
              match (Pt.Insts.CoreCmpOrd.cmp p last).match with
              | .ok Ordering.gt => (vs (k + 1)).val = (vs k).val ++ [p]
              | .ok Ordering.eq => (vs (k + 1)).val = (vs k).val.dropLast ++ [p]
              | .ok Ordering.lt =>
                  ∃ (i : Nat),
                    i ≤ (vs k).val.length ∧
                    ((vs (k + 1)).val = (vs k).val.take i ++ [p] ++ (vs k).val.drop i ∨
                     (i < (vs k).val.length ∧
                      (vs (k + 1)).val =
                        (vs k).val.take i ++ [p] ++ (vs k).val.drop (i + 1)))
              | _ => False ⦄ := by
  unfold from_pb_loop0_loop0
  apply loop.spec_decr_nat
    (measure := fun (x : core.slice.iter.ChunksExact U8 × sorted_vec.SortedSet Pt) =>
                  x.1.chunks.length)
    (inv := fun (x : core.slice.iter.ChunksExact U8 × sorted_vec.SortedSet Pt) =>
        ∃ (n : Nat) (vs : Nat → sorted_vec.SortedSet Pt),
          n ≤ iter.chunks.length ∧
          x.1.chunks = iter.chunks.drop n ∧
          vs 0 = v ∧ vs n = x.2 ∧
          x.2.val.length ≤ v.val.length + n ∧
          ∀ (k : Nat), k < n →
            ∃ (p : Pt),
              p.x.value.val = 256 * ((iter.chunks[k]!).val[0]!).val +
                ((iter.chunks[k]!).val[1]!).val ∧
              p.y.value.val = 256 * ((iter.chunks[k]!).val[2]!).val +
                ((iter.chunks[k]!).val[3]!).val ∧
              match (vs k).val.getLast? with
              | none => (vs (k + 1)).val = (vs k).val ++ [p]
              | some last =>
                match (Pt.Insts.CoreCmpOrd.cmp p last).match with
                | .ok Ordering.gt => (vs (k + 1)).val = (vs k).val ++ [p]
                | .ok Ordering.eq => (vs (k + 1)).val = (vs k).val.dropLast ++ [p]
                | .ok Ordering.lt =>
                    ∃ (i : Nat),
                      i ≤ (vs k).val.length ∧
                      ((vs (k + 1)).val = (vs k).val.take i ++ [p] ++ (vs k).val.drop i ∨
                       (i < (vs k).val.length ∧
                        (vs (k + 1)).val =
                          (vs k).val.take i ++ [p] ++ (vs k).val.drop (i + 1)))
                | _ => False)
  · rintro ⟨iter', v'⟩ ⟨n, vs, h_n_le, h_drop, h_v0, h_vn, h_len, h_chain⟩
    simp only at h_n_le h_drop h_v0 h_vn h_len h_chain ⊢
    have h_chunks' : ∀ c ∈ iter'.chunks, c.val.length = 4 := by
      rw [h_drop]
      exact fun c hc => h_chunks c (List.mem_of_mem_drop hc)
    apply WP.spec_mono
      (body_spec iter' v' h_chunks' (by simp only [alloc.vec.Vec.length] at *; omega))
    intro cf h_cf
    match cf with
    | ControlFlow.done v_final =>
      obtain ⟨rfl, h_nil⟩ := h_cf
      have hn : n = iter.chunks.length := by
        rw [h_nil] at h_drop
        have := congrArg List.length h_drop
        simp only [List.length_nil, List.length_drop] at this
        omega
      subst hn
      exact ⟨vs, h_v0, h_vn, h_chain⟩
    | ControlFlow.cont (iter1, v1) =>
      obtain ⟨c, h_cons, p, h_px, h_py, h_push⟩ := h_cf
      rw [h_drop] at h_cons
      have h_nlt : n < iter.chunks.length := by
        have := congrArg List.length h_cons
        simp only [List.length_drop, List.length_cons] at this
        omega
      have h_c : iter.chunks[n]! = c := by
        rw [getElem!_pos iter.chunks n h_nlt]
        have := congrArg (·[0]?) h_cons
        simp only [List.getElem?_drop, Nat.add_zero, List.getElem?_cons_zero,
          List.getElem?_eq_getElem h_nlt, Option.some.injEq] at this
        exact this
      have h_drop1 : iter1.chunks = iter.chunks.drop (n + 1) := by
        rw [← List.drop_drop, h_cons]
        rfl
      refine ⟨⟨n + 1, Function.update vs (n + 1) v1, by omega, h_drop1, ?_, by simp, ?_, ?_⟩, ?_⟩
      · rw [Function.update_of_ne (by omega)]
        exact h_v0
      · have h_len1 : v1.val.length ≤ v'.val.length + 1 := by
          split at h_push
          · simp [h_push]
          · split at h_push
            · simp [h_push]
            · simp only [h_push, List.length_append, List.length_dropLast,
                List.length_singleton]
              omega
            · obtain ⟨i, hi, h | ⟨_, h⟩⟩ := h_push <;>
                simp only [h, List.length_append, List.length_take, List.length_drop,
                  List.length_singleton] <;> omega
            · exact absurd h_push id
        simp only
        omega
      · intro k hk
        by_cases hk_lt : k < n
        · obtain ⟨p', h_px', h_py', h_vpush'⟩ := h_chain k hk_lt
          refine ⟨p', h_px', h_py', ?_⟩
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact h_vpush'
        · have hk_eq : k = n := by omega
          subst hk_eq
          refine ⟨p, by rw [h_c]; omega, by rw [h_c]; omega, ?_⟩
          rw [Function.update_of_ne (by omega), Function.update_self, h_vn]
          exact h_push
      · simp only
        rw [h_drop, h_cons]
        simp
  · exact ⟨0, fun _ => v, by omega, rfl, rfl, rfl, by simp, fun k hk => absurd hk (by omega)⟩

end spqr.encoding.polynomial.PolyDecoder.from_pb_loop0_loop0

/-! # Spec theorem for `PolyDecoder::from_pb`: loop body 0

One step of the outer loop. Given `v : Vec<Vec<u8>>`, a range iterator over slot indices, and
`out_pts : [SortedSet<Pt>; 16]`, the body advances the iterator and either terminates (done)
or deserializes slot `i` by allocating a fresh `SortedSet`, running the inner 4-byte loop on
`v[i]`, and storing the result into `out_pts[i]`.

**Source**: spqr/src/encoding/polynomial.rs -/

namespace spqr.encoding.polynomial.PolyDecoder.from_pb_loop0

/-- Byte `r < 4` of the `k`-th 4-byte chunk `(l.drop (4 * k)).take 4` is `l[4 * k + r]!`. -/
theorem chunk_getElem! (l : List U8) (k r : Nat) (hr : r < 4) :
    ((l.drop (4 * k)).take 4)[r]! = l[4 * k + r]! := by
  simp [List.getElem!_eq_getElem?_getD, hr, List.getElem?_drop]

/-- **Spec theorem for `encoding.polynomial.PolyDecoder.from_pb_loop0.body`**:

One step of the outer loop. Either terminates — because the iterator is exhausted (returning
`Ok` of the decoder built from `out_pts`, `pts_needed` and `is_complete`) or because slot `i`
has a length that is not a multiple of 4 (returning `Err SerializationInvalid`) — or
deserializes `v[i]` via the inner 4-byte chunk loop and stores the result into `out_pts[i]`.

The cont case provides a chain of push operations for the decoded points from
`v[i]`, with big-endian 4-byte decoding of each `Pt`. -/
@[step]
theorem body_spec
    (i : U32) (v : alloc.vec.Vec (alloc.vec.Vec U8)) (b : Bool)
    (iter : core.ops.range.Range Usize)
    (out_pts : Array (sorted_vec.SortedSet Pt) 16#usize)
    (h_end_le_v : iter.end ≤ v.length)
    (h_end_le_16 : iter.end.val ≤ 16)
    (h_pts_overflow : ∀ (j : Nat), j < v.length → (v[j]!).length + 4 ≤ Usize.max) :
    body i v b iter out_pts ⦃ cf =>
      match cf with
      | ControlFlow.done r =>
          (iter.start < iter.end →
            (v[iter.start.val]!).length % 4 ≠ 0 ∧
            r = core.result.Result.Err
              encoding.polynomial.PolynomialError.SerializationInvalid) ∧
          (¬(iter.start < iter.end) →
            ∃ (d : PolyDecoder), r = core.result.Result.Ok d ∧
              d.pts_needed.val = i.val ∧ d.pts = out_pts ∧ d.is_complete = b)
      | ControlFlow.cont (iter1, out_pts') =>
          iter.start < iter.end ∧
          (v[iter.start.val]!).length % 4 = 0 ∧
          iter1.start.val = iter.start.val + 1 ∧
          iter1.end = iter.end ∧
          (∀ (k : Nat), k ≠ iter.start →
            out_pts'.val[k]! = out_pts.val[k]!) ∧
          ∃ (v_final : sorted_vec.SortedSet Pt) (n : Nat)
            (vs : Nat → sorted_vec.SortedSet Pt),
            out_pts'.val[iter.start.val]! = v_final ∧
            vs n = v_final ∧
            (vs 0).val = [] ∧
            4 * n ≤ (v[iter.start.val]!).length ∧
            (v[iter.start.val]!).length < 4 * (n + 1) ∧
            ∀ (k : Nat), k < n →
              ∃ (p : Pt),
                p.x.value.val =
                  (v[iter.start.val]!)[4 * k]! * 256 + (v[iter.start.val]!)[4 * k + 1]! ∧
                p.y.value.val =
                  (v[iter.start.val]!)[4 * k + 2]! * 256 + (v[iter.start.val]!)[4 * k + 3]! ∧
                match (vs k).val.getLast? with
                | none => (vs (k + 1)).val = (vs k).val ++ [p]
                | some last =>
                  match (Pt.Insts.CoreCmpOrd.cmp p last).match with
                  | .ok Ordering.gt => (vs (k + 1)).val = (vs k).val ++ [p]
                  | .ok Ordering.eq => (vs (k + 1)).val = (vs k).val.dropLast ++ [p]
                  | .ok Ordering.lt =>
                      ∃ (i : Nat),
                        i ≤ (vs k).val.length ∧
                        ((vs (k + 1)).val = (vs k).val.take i ++ [p] ++ (vs k).val.drop i ∨
                        (i < (vs k).val.length ∧
                          (vs (k + 1)).val =
                            (vs k).val.take i ++ [p] ++ (vs k).val.drop (i + 1)))
                  | _ => False ⦄ := by
  unfold body
  step with core.iter.range.IteratorRange.next_Usize_spec' iter as
    ⟨opt, iter1', h_none, h_some⟩
  by_cases h_lt : iter.start.val < iter.end.val
  · obtain ⟨h_opt_eq, h_start1, h_end1⟩ := h_some h_lt
    rw [h_opt_eq]
    have h_i_lt_v : iter.start.val < v.val.length := by
      simp only [alloc.vec.Vec.length] at h_end_le_v; omega
    have h_i_lt_16 : iter.start.val < 16 := by omega
    have h_pts_ov := h_pts_overflow iter.start.val h_i_lt_v
    simp only [sorted_vec.SortedSet.with_capacity, alloc.vec.Vec.len]
    step as ⟨pts, h_pts⟩
    have h_pts' : v[iter.start.val]! = pts := by
      rw [h_pts, alloc.vec.Vec.getElem!_Nat_eq, getElem!_pos v.val _ h_i_lt_v]
    step as ⟨i3, h_i3⟩
    split
    · simp only [WP.spec_ok]
      refine ⟨fun _ => ⟨?_, trivial⟩, fun h => (h h_lt).elim⟩
      rw [h_pts']
      simp only [bne_iff_ne, ne_eq, UScalar.neq_to_neq_val] at *
      scalar_tac
    · step as ⟨i5, h_i5⟩
      apply WP.spec_bind_ok
      step with core.slice.Slice.chunks_exact_spec_with_content (alloc.vec.Vec.deref pts) 4#usize
        (by decide) as ⟨iter2, h_c4, h_cn, _, h_content⟩
      have h_mod : pts.val.length % 4 = 0 := by
        simp only [bne_iff_ne, ne_eq, UScalar.neq_to_neq_val, not_not] at *
        scalar_tac
      have h_deref : (alloc.vec.Vec.deref pts).val = pts.val := by simp [alloc.vec.Vec.deref]
      rw [h_deref] at h_cn h_content
      have h_pts_ov' : pts.val.length + 4 ≤ Usize.max := by
        rw [← h_pts']; exact h_pts_ov
      step with from_pb_loop0_loop0.loop_spec iter2 (alloc.vec.Vec.new Pt) h_c4
        (by rw [h_cn]; simp [alloc.vec.Vec.new]; omega) as ⟨v2, vs, h_vs0, h_vsn, h_chain⟩
      step*
      rw [h_pts']
      have h_len16 : out_pts.val.length = 16 := by simp
      have h_a : a.val = out_pts.val.set iter.start.val v2 := by
        rw [‹a = _›, ‹index_mut_back = _›]
        simp
      refine ⟨h_lt, h_mod, h_start1, h_end1, ?_, v2, iter2.chunks.length, vs, ?_, h_vsn,
        by rw [h_vs0]; rfl, by rw [h_cn]; simp only [alloc.vec.Vec.length]; omega,
        by rw [h_cn]; simp only [alloc.vec.Vec.length]; omega, ?_⟩
      · intro k hk
        rw [h_a, List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD,
          List.getElem?_set_ne (Ne.symm hk)]
      · rw [h_a, List.getElem!_eq_getElem?_getD, List.getElem?_set_self (by omega)]
        rfl
      · intro k hk
        obtain ⟨p, hx, hy, hm⟩ := h_chain k hk
        refine ⟨p, ?_, ?_, hm⟩
        · rw [hx, h_content k hk, chunk_getElem! _ _ 0 (by omega),
            chunk_getElem! _ _ 1 (by omega)]
          simp only [alloc.vec.Vec.getElem!_Nat_eq, Nat.add_zero]
          omega
        · rw [hy, h_content k hk, chunk_getElem! _ _ 2 (by omega),
            chunk_getElem! _ _ 3 (by omega)]
          simp only [alloc.vec.Vec.getElem!_Nat_eq]
          omega
  · obtain ⟨h_opt_eq, _⟩ := h_none (by omega)
    rw [h_opt_eq]
    step*

/-- **Spec theorem for `encoding.polynomial.PolyDecoder.from_pb_loop0`**:

Full outer loop. If some slot `j ∈ [iter.start, iter.end)` has a length that is not a
multiple of 4 the result is `Err SerializationInvalid`; otherwise the result is `Ok decoder`
where, for every slot `j < iter.end.val`, `decoder.pts[j]` is a sorted set produced by a
chain of `n` decode-and-push steps consuming all complete 4-byte chunks from `v[j]`.

**Source**: spqr/src/encoding/polynomial.rs -/
@[step]
theorem loop_spec
    (iter : core.ops.range.Range Usize)
    (i : U32) (v : alloc.vec.Vec (alloc.vec.Vec U8)) (b : Bool)
    (out_pts : Array (sorted_vec.SortedSet Pt) 16#usize)
    (h_end_le_v : iter.end ≤ v.length)
    (h_end_le_16 : iter.end.val ≤ 16)
    (h_start_le : iter.start ≤ iter.end)
    (h_pts_overflow : ∀ (j : Nat), j < v.length → (v[j]!).length + 4 ≤ Usize.max)
    (h_pre : ∀ (j : Nat), j < iter.start →
        ∃ (v_final : sorted_vec.SortedSet Pt) (n : Nat)
          (vs : Nat → sorted_vec.SortedSet Pt),
          out_pts.val[j]! = v_final ∧
          vs n = v_final ∧
          (vs 0).val = [] ∧
          4 * n ≤ (v[j]!).length ∧
          (v[j]!).length < 4 * (n + 1) ∧
          ∀ (k : Nat), k < n →
            ∃ (p : Pt),
              p.x.value.val = (v[j]!)[4 * k]! * 256 + (v[j]!)[4 * k + 1]! ∧
              p.y.value.val = (v[j]!)[4 * k + 2]! * 256 + (v[j]!)[4 * k + 3]! ∧
              match (vs k).val.getLast? with
              | none => (vs (k + 1)).val = (vs k).val ++ [p]
              | some last =>
                match (Pt.Insts.CoreCmpOrd.cmp p last).match with
                | .ok Ordering.gt => (vs (k + 1)).val = (vs k).val ++ [p]
                | .ok Ordering.eq => (vs (k + 1)).val = (vs k).val.dropLast ++ [p]
                | .ok Ordering.lt =>
                    ∃ (i : Nat),
                      i ≤ (vs k).val.length ∧
                      ((vs (k + 1)).val = (vs k).val.take i ++ [p] ++ (vs k).val.drop i ∨
                      (i < (vs k).val.length ∧
                        (vs (k + 1)).val =
                          (vs k).val.take i ++ [p] ++ (vs k).val.drop (i + 1)))
                | _ => False) :
    from_pb_loop0 iter i v b out_pts ⦃ (result : core.result.Result PolyDecoder
        encoding.polynomial.PolynomialError) =>
      match result with
      | core.result.Result.Ok d =>
        d.pts_needed.val = i.val ∧ d.is_complete = b ∧
        (∀ (j : Nat), iter.start ≤ j → j < iter.end → (v[j]!).length % 4 = 0) ∧
        ∀ (j : Nat), j < iter.end →
          ∃ (v_final : sorted_vec.SortedSet Pt) (n : Nat)
            (vs : Nat → sorted_vec.SortedSet Pt),
            d.pts.val[j]! = v_final ∧
            vs n = v_final ∧
            (vs 0).val = [] ∧
            4 * n ≤ (v[j]!).length ∧
            (v[j]!).length < 4 * (n + 1) ∧
            ∀ (k : Nat), k < n →
              ∃ (p : Pt),
                p.x.value.val = (v[j]!)[4 * k]! * 256 + (v[j]!)[4 * k + 1]! ∧
                p.y.value.val = (v[j]!)[4 * k + 2]! * 256 + (v[j]!)[4 * k + 3]! ∧
                match (vs k).val.getLast? with
                | none => (vs (k + 1)).val = (vs k).val ++ [p]
                | some last =>
                  match (Pt.Insts.CoreCmpOrd.cmp p last).match with
                  | .ok Ordering.gt => (vs (k + 1)).val = (vs k).val ++ [p]
                  | .ok Ordering.eq => (vs (k + 1)).val = (vs k).val.dropLast ++ [p]
                  | .ok Ordering.lt =>
                      ∃ (i : Nat),
                        i ≤ (vs k).val.length ∧
                        ((vs (k + 1)).val = (vs k).val.take i ++ [p] ++ (vs k).val.drop i ∨
                        (i < (vs k).val.length ∧
                          (vs (k + 1)).val =
                            (vs k).val.take i ++ [p] ++ (vs k).val.drop (i + 1)))
                  | _ => False
      | core.result.Result.Err e =>
        e = encoding.polynomial.PolynomialError.SerializationInvalid ∧
        ∃ (j : Nat), iter.start ≤ j ∧ j < iter.end ∧ (v[j]!).length % 4 ≠ 0 ⦄ := by
  unfold from_pb_loop0
  apply loop.spec_decr_nat
    (measure := fun (x : core.ops.range.Range Usize ×
                       Array (sorted_vec.SortedSet Pt) 16#usize) => x.1.end - x.1.start)
    (inv := fun (x : core.ops.range.Range Usize ×
                     Array (sorted_vec.SortedSet Pt) 16#usize) =>
        x.1.end = iter.end ∧
        iter.start.val ≤ x.1.start.val ∧
        x.1.start.val ≤ x.1.end.val ∧
        (∀ (j : Nat), iter.start.val ≤ j → j < x.1.start.val → (v[j]!).length % 4 = 0) ∧
        (∀ (j : Nat), j < x.1.start.val →
            ∃ (v_final : sorted_vec.SortedSet Pt) (n : Nat)
              (vs : Nat → sorted_vec.SortedSet Pt),
              x.2.val[j]! = v_final ∧
              vs n = v_final ∧
              (vs 0).val = [] ∧
              4 * n ≤ (v[j]!).length ∧
              (v[j]!).length < 4 * (n + 1) ∧
              ∀ (k : Nat), k < n →
                ∃ (p : Pt),
                  p.x.value.val = (v[j]!)[4 * k]! * 256 + (v[j]!)[4 * k + 1]! ∧
                  p.y.value.val = (v[j]!)[4 * k + 2]! * 256 + (v[j]!)[4 * k + 3]! ∧
                  match (vs k).val.getLast? with
                  | none => (vs (k + 1)).val = (vs k).val ++ [p]
                  | some last =>
                    match (Pt.Insts.CoreCmpOrd.cmp p last).match with
                    | .ok Ordering.gt => (vs (k + 1)).val = (vs k).val ++ [p]
                    | .ok Ordering.eq => (vs (k + 1)).val = (vs k).val.dropLast ++ [p]
                    | .ok Ordering.lt =>
                        ∃ (i : Nat),
                          i ≤ (vs k).val.length ∧
                          ((vs (k + 1)).val = (vs k).val.take i ++ [p] ++ (vs k).val.drop i ∨
                          (i < (vs k).val.length ∧
                            (vs (k + 1)).val =
                              (vs k).val.take i ++ [p] ++ (vs k).val.drop (i + 1)))
                    | _ => False))
  · rintro ⟨iter', out_pts'⟩ ⟨h_end', h_orig_le, h_start_le', h_mod', h_inv'⟩
    simp only at h_end' h_orig_le h_start_le' h_mod' h_inv' ⊢
    have h_end_val : iter'.end.val = iter.end.val := by rw [h_end']
    have h_body := body_spec i v b iter' out_pts' (by rw [h_end']; exact h_end_le_v)
      (by omega) h_pts_overflow
    apply WP.spec_mono h_body
    intro cf h_cf
    match cf with
    | ControlFlow.done r =>
      simp only at h_cf ⊢
      obtain ⟨h_err, h_ok⟩ := h_cf
      by_cases h_lt : iter'.start < iter'.end
      · obtain ⟨h_bad, rfl⟩ := h_err h_lt
        refine ⟨rfl, iter'.start.val, h_orig_le, ?_, h_bad⟩
        have : iter'.start.val < iter'.end.val := h_lt
        omega
      · obtain ⟨d, rfl, h_pn, h_pts, h_ic⟩ := h_ok h_lt
        have h_ge : iter'.end.val ≤ iter'.start.val := by
          have : ¬ iter'.start.val < iter'.end.val := h_lt
          omega
        refine ⟨h_pn, h_ic, fun j hj1 hj2 => h_mod' j hj1 (by omega), fun j hj => ?_⟩
        rw [h_pts]
        exact h_inv' j (by omega)
    | ControlFlow.cont (iter'', out_pts'') =>
      simp only at h_cf ⊢
      obtain ⟨h_lt, h_mod_s, h_start1, h_end1, h_other, v_final, n, vs,
              h_slot, h_vs_n, h_vs0, h_n_lo, h_n_hi, h_chain⟩ := h_cf
      have h_lt' : iter'.start.val < iter'.end.val := h_lt
      have h_end1_val : iter''.end.val = iter'.end.val := by rw [h_end1]
      refine ⟨⟨by rw [h_end1]; exact h_end', by omega, by omega, ?_, fun j hj => ?_⟩,
              by omega⟩
      · intro j hj1 hj2
        by_cases hj : j < iter'.start.val
        · exact h_mod' j hj1 hj
        · have : j = iter'.start.val := by omega
          subst this
          exact h_mod_s
      · by_cases hj_lt : j < iter'.start.val
        · obtain ⟨vf, nn, vss, h_slot', h_rest⟩ := h_inv' j hj_lt
          refine ⟨vf, nn, vss, ?_, h_rest⟩
          rw [h_other j (by omega)]
          exact h_slot'
        · have hj_eq : j = iter'.start.val := by omega
          subst hj_eq
          exact ⟨v_final, n, vs, h_slot, h_vs_n, h_vs0, h_n_lo, h_n_hi, h_chain⟩
  · exact ⟨rfl, le_refl _, h_start_le, fun j hj1 hj2 => absurd hj2 (by simp only; omega), h_pre⟩

end spqr.encoding.polynomial.PolyDecoder.from_pb_loop0

/-! # Spec theorem for `spqr::encoding::polynomial::{PolyDecoder}::from_pb`

Reconstructs a `PolyDecoder` from its protobuf representation. Validates `pb.pts.len() == 16`
and `len() % 4 == 0` for each slot, then deserializes all 16 slots of big-endian 4-byte chunks
into `[SortedSet<Pt>; 16]`, and casts `pb.pts_needed : u32` to `usize`.

**Source**: spqr/src/encoding/polynomial.rs -/

namespace spqr.encoding.polynomial.PolyDecoder

/-- **Spec theorem for `encoding.polynomial.PolyDecoder.from_pb`** (byte-level):

Tri-branch postcondition: (1) bad length → `Err`, (2) bad chunking → `Err`, (3) valid →
`Ok decoder` with `pts_needed`, `is_complete` preserved and per-slot chain witnesses for the
decoded points.

`SortedSet.with_capacity` is now a concrete definition (returns empty set). -/
@[step]
theorem from_pb_spec
    (pb : proto.pq_ratchet.PolynomialDecoder)
    (h_pts_overflow : ∀ (j : Nat), j < pb.pts.length →
        (pb.pts[j]!).length + 4 ≤ Usize.max) :
    from_pb pb ⦃ (result : core.result.Result
        encoding.polynomial.PolyDecoder
        encoding.polynomial.PolynomialError) =>
      -- Bad length: returns Err
      (pb.pts.val.length ≠ 16 →
        result = core.result.Result.Err
          encoding.polynomial.PolynomialError.SerializationInvalid) ∧
      -- Bad chunking: some slot has length not a multiple of 4
      (pb.pts.val.length = 16 →
        (∃ (j : Nat), j < 16 ∧ (pb.pts.val[j]!).val.length % 4 ≠ 0) →
        result = core.result.Result.Err
          encoding.polynomial.PolynomialError.SerializationInvalid) ∧
      -- Valid: every slot has length a multiple of 4, result is Ok with chain witnesses
      (pb.pts.val.length = 16 →
        (∀ (j : Nat), j < 16 → (pb.pts.val[j]!).val.length % 4 = 0) →
        match result with
        | core.result.Result.Ok decoder =>
          decoder.pts_needed.val = pb.pts_needed.val ∧
          decoder.is_complete = pb.is_complete ∧
          decoder.pts.val.length = 16 ∧
          ∀ (j : Nat), j < 16 →
            ∃ (v_final : sorted_vec.SortedSet Pt) (n : Nat)
              (vs : Nat → sorted_vec.SortedSet Pt),
              decoder.pts.val[j]! = v_final ∧
              vs n = v_final ∧
              (vs 0).val = [] ∧
              4 * n ≤ (pb.pts[j]!).length ∧
              (pb.pts[j]!).length < 4 * (n + 1) ∧
              ∀ (k : Nat), k < n →
                ∃ (p : Pt),
                  p.x.value.val = (pb.pts[j]!)[4 * k]! * 256 + (pb.pts.val[j]!)[4 * k + 1]! ∧
                  p.y.value.val = (pb.pts[j]!)[4 * k + 2]!* 256 + (pb.pts[j]!)[4 * k + 3]! ∧
                  match (vs k).val.getLast? with
                  | none => (vs (k + 1)).val = (vs k).val ++ [p]
                  | some last =>
                    match (Pt.Insts.CoreCmpOrd.cmp p last).match with
                    | .ok Ordering.gt => (vs (k + 1)).val = (vs k).val ++ [p]
                    | .ok Ordering.eq => (vs (k + 1)).val = (vs k).val.dropLast ++ [p]
                    | .ok Ordering.lt =>
                        ∃ (i : Nat),
                          i ≤ (vs k).val.length ∧
                          ((vs (k + 1)).val = (vs k).val.take i ++ [p] ++ (vs k).val.drop i ∨
                          (i < (vs k).val.length ∧
                            (vs (k + 1)).val =
                              (vs k).val.take i ++ [p] ++ (vs k).val.drop (i + 1)))
                    | _ => False
        | core.result.Result.Err _ => False) ⦄ := by
  unfold from_pb
  simp only [alloc.vec.Vec.len, bne_iff_ne, ne_eq, UScalar.neq_to_neq_val,
    Usize.ofNatCore_val_eq, UScalar.ofNatCore_val_eq]
  split
  · simp only [WP.spec_ok]
    exact ⟨fun _ => trivial, fun h => absurd h ‹_›, fun h => absurd h ‹_›⟩
  · have h16 : pb.pts.val.length = 16 := by simpa using ‹¬¬_›
    step as ⟨out_pts, h_out⟩
    case l => exact List.replicate 16 (alloc.vec.Vec.new Pt)
    case hl =>
      apply core.array.from_fn_loop_const
      · intro g i
        simp only [from_pb.closure.Insts.CoreOpsFunctionFnMutTupleUsizeSortedSetPt.call_mut,
          sorted_vec.SortedSet.new]
        exact bind_ok _ _
      · scalar_tac
    case hlen => rfl
    step with from_pb_loop0.loop_spec { start := 0#usize, «end» := 16#usize } pb.pts_needed
      pb.pts pb.is_complete out_pts (by simp [h16]) (by simp) (by simp) h_pts_overflow
      (fun j hj => absurd hj (by simp)) as ⟨r, h_r⟩
    simp only [alloc.vec.Vec.getElem!_Nat_eq] at h_r ⊢
    rcases r with d | e
    · obtain ⟨h_pn, h_ic, h_mod, h_ch⟩ := h_r
      exact ⟨fun h => absurd h16 h, fun _ j hj hbad => absurd (h_mod j (Nat.zero_le _) hj) hbad,
        fun _ _ => ⟨h_pn, h_ic, by simp, h_ch⟩⟩
    · obtain ⟨rfl, j, _, hj, hbad⟩ := h_r
      exact ⟨fun _ => rfl, fun _ _ _ _ => rfl, fun _ hall => absurd (hall j hj) hbad⟩

end spqr.encoding.polynomial.PolyDecoder

/-! # `from_pb` establishes the `PointsValid` invariant

Each slot is rebuilt from scratch (starting from the empty set) by a chain of
`SortedSet::push` calls, each of which preserves `SlotSorted`
(`PolyDecoder.push_spec_sorted`).  Hence every slot of the resulting decoder is
`SlotSorted`, i.e. `PointsValid` holds. -/

namespace spqr.encoding.polynomial.PolyDecoder.from_pb_loop0_loop0

/-- One step of the inner loop preserves `SlotSorted`. -/
theorem body_spec_sorted
    (iter : core.slice.iter.ChunksExact U8)
    (v : sorted_vec.SortedSet Pt)
    (h_chunks : ∀ c ∈ iter.chunks, c.val.length = 4)
    (h_push_cap : v.length + 1 ≤ Usize.max)
    (h_sorted : SlotSorted v.val) :
    body iter v ⦃ cf =>
      match cf with
      | ControlFlow.done v' => SlotSorted v'.val
      | ControlFlow.cont (_, v1) => SlotSorted v1.val ⦄ := by
  unfold body core.slice.iter.IteratorChunksExact.next
  rcases h : iter.chunks with _ | ⟨c, rest⟩
  · simpa
  · have hc : c.val.length = 4 := h_chunks c (by simp [h])
    step as ⟨r, a0, hr0, ha0⟩
    step as ⟨a, ha⟩
    step as ⟨p, hpx, hpy⟩
    step with PolyDecoder.push_spec_sorted v p h_push_cap as ⟨_, v1, h_v1⟩
    exact h_v1 h_sorted

/-- The inner loop preserves `SlotSorted`. -/
theorem loop_spec_sorted
    (iter : core.slice.iter.ChunksExact U8)
    (v : sorted_vec.SortedSet Pt)
    (h_chunks : ∀ c ∈ iter.chunks, c.val.length = 4)
    (h_v_room : v.length + iter.chunks.length + 1 ≤ Usize.max)
    (h_sorted : SlotSorted v.val) :
    from_pb_loop0_loop0 iter v ⦃ (v_result : sorted_vec.SortedSet Pt) =>
      SlotSorted v_result.val ⦄ := by
  unfold from_pb_loop0_loop0
  apply loop.spec_decr_nat
    (measure := fun (x : core.slice.iter.ChunksExact U8 × sorted_vec.SortedSet Pt) =>
                  x.1.chunks.length)
    (inv := fun (x : core.slice.iter.ChunksExact U8 × sorted_vec.SortedSet Pt) =>
        ∃ (n : Nat), n ≤ iter.chunks.length ∧
          x.1.chunks = iter.chunks.drop n ∧
          x.2.val.length ≤ v.val.length + n ∧
          SlotSorted x.2.val)
  · rintro ⟨iter', v'⟩ ⟨n, h_n_le, h_drop, h_len, h_sorted'⟩
    simp only at h_n_le h_drop h_len h_sorted' ⊢
    have h_chunks' : ∀ c ∈ iter'.chunks, c.val.length = 4 := by
      rw [h_drop]
      exact fun c hc => h_chunks c (List.mem_of_mem_drop hc)
    have h_cap' : v'.length + 1 ≤ Usize.max := by
      simp only [alloc.vec.Vec.length] at *; omega
    apply WP.spec_mono (WP.spec_and (body_spec iter' v' h_chunks' h_cap')
      (body_spec_sorted iter' v' h_chunks' h_cap' h_sorted'))
    rintro (⟨iter1, v1⟩ | v_final) ⟨h_cf, h_s⟩
    · obtain ⟨c, h_cons, p, _, _, h_push⟩ := h_cf
      rw [h_drop] at h_cons
      have h_nlt : n < iter.chunks.length := by
        have := congrArg List.length h_cons
        simp only [List.length_drop, List.length_cons] at this
        omega
      have h_drop1 : iter1.chunks = iter.chunks.drop (n + 1) := by
        rw [← List.drop_drop, h_cons]
        rfl
      have h_len1 : v1.val.length ≤ v'.val.length + 1 := by
        split at h_push
        · simp [h_push]
        · split at h_push
          · simp [h_push]
          · simp only [h_push, List.length_append, List.length_dropLast,
              List.length_singleton]
            omega
          · obtain ⟨i, hi, h | ⟨_, h⟩⟩ := h_push <;>
              simp only [h, List.length_append, List.length_take, List.length_drop,
                List.length_singleton] <;> omega
          · exact absurd h_push id
      simp only at h_s ⊢
      refine ⟨⟨n + 1, by omega, h_drop1, by omega, h_s⟩, ?_⟩
      rw [h_drop, h_cons]
      simp
    · exact h_s
  · exact ⟨0, by omega, rfl, by simp, h_sorted⟩

end spqr.encoding.polynomial.PolyDecoder.from_pb_loop0_loop0

namespace spqr.encoding.polynomial.PolyDecoder.from_pb_loop0

/-- One step of the outer loop preserves `PointsValid` (the freshly decoded slot is
`SlotSorted` because it is built from the empty set by pushes). -/
theorem body_spec_valid
    (i : U32) (v : alloc.vec.Vec (alloc.vec.Vec U8)) (b : Bool)
    (iter : core.ops.range.Range Usize)
    (out_pts : Array (sorted_vec.SortedSet Pt) 16#usize)
    (h_end_le_v : iter.end ≤ v.length)
    (h_end_le_16 : iter.end.val ≤ 16)
    (h_pts_overflow : ∀ (j : Nat), j < v.length → (v[j]!).length + 4 ≤ Usize.max)
    (h_valid : PointsValid out_pts) :
    body i v b iter out_pts ⦃ cf =>
      match cf with
      | ControlFlow.done r =>
          match r with
          | core.result.Result.Ok d => PointsValid d.pts
          | core.result.Result.Err _ => True
      | ControlFlow.cont (_, out_pts') => PointsValid out_pts' ⦄ := by
  unfold body
  step with core.iter.range.IteratorRange.next_Usize_spec' iter as
    ⟨opt, iter1', h_none, h_some⟩
  by_cases h_lt : iter.start.val < iter.end.val
  · obtain ⟨h_opt_eq, _, _⟩ := h_some h_lt
    rw [h_opt_eq]
    have h_i_lt_v : iter.start.val < v.val.length := by
      simp only [alloc.vec.Vec.length] at h_end_le_v; omega
    have h_pts_ov := h_pts_overflow iter.start.val h_i_lt_v
    simp only [sorted_vec.SortedSet.with_capacity, alloc.vec.Vec.len]
    step as ⟨pts, h_pts⟩
    have h_pts' : v[iter.start.val]! = pts := by
      rw [h_pts, alloc.vec.Vec.getElem!_Nat_eq, getElem!_pos v.val _ h_i_lt_v]
    step as ⟨i3, _⟩
    split
    · exact (WP.spec_ok _).mpr trivial
    · step as ⟨i5, _⟩
      apply WP.spec_bind_ok
      step with core.slice.Slice.chunks_exact_spec_with_content (alloc.vec.Vec.deref pts) 4#usize
        (by decide) as ⟨iter2, h_c4, h_cn, _, _⟩
      have h_deref : (alloc.vec.Vec.deref pts).val = pts.val := by simp [alloc.vec.Vec.deref]
      rw [h_deref] at h_cn
      have h_pts_ov' : pts.val.length + 4 ≤ Usize.max := by
        rw [← h_pts']; exact h_pts_ov
      step with from_pb_loop0_loop0.loop_spec_sorted iter2 (alloc.vec.Vec.new Pt) h_c4
        (by rw [h_cn]; simp [alloc.vec.Vec.new]; omega) SlotSorted.nil as ⟨v2, h_v2⟩
      step*
      rw [‹a = _›, ‹index_mut_back = _›]
      have h_ss_sorted : SlotSorted ss.val := by
        rw [‹ss = _›]; exact h_valid.slot _ (by scalar_tac)
      exact (h_valid.set _ _ h_ss_sorted).set _ v2 h_v2
  · obtain ⟨h_opt_eq, rfl⟩ := h_none h_lt
    rw [h_opt_eq]
    step*

/-- The outer loop preserves `PointsValid`. -/
theorem loop_spec_valid
    (iter : core.ops.range.Range Usize)
    (i : U32) (v : alloc.vec.Vec (alloc.vec.Vec U8)) (b : Bool)
    (out_pts : Array (sorted_vec.SortedSet Pt) 16#usize)
    (h_end_le_v : iter.end ≤ v.length)
    (h_end_le_16 : iter.end.val ≤ 16)
    (h_start_le : iter.start ≤ iter.end)
    (h_pts_overflow : ∀ (j : Nat), j < v.length → (v[j]!).length + 4 ≤ Usize.max)
    (h_valid : PointsValid out_pts) :
    from_pb_loop0 iter i v b out_pts ⦃ (result : core.result.Result PolyDecoder
        encoding.polynomial.PolynomialError) =>
      match result with
      | core.result.Result.Ok d => PointsValid d.pts
      | core.result.Result.Err _ => True ⦄ := by
  unfold from_pb_loop0
  apply loop.spec_decr_nat
    (measure := fun (x : core.ops.range.Range Usize ×
                       Array (sorted_vec.SortedSet Pt) 16#usize) => x.1.end - x.1.start)
    (inv := fun (x : core.ops.range.Range Usize ×
                     Array (sorted_vec.SortedSet Pt) 16#usize) =>
        x.1.end = iter.end ∧ x.1.start.val ≤ x.1.end.val ∧ PointsValid x.2)
  · rintro ⟨iter', out_pts'⟩ ⟨h_end', h_le', h_valid'⟩
    simp only at h_end' h_le' h_valid' ⊢
    apply WP.spec_mono (WP.spec_and
      (body_spec i v b iter' out_pts' (by rw [h_end']; exact h_end_le_v)
        (by rw [h_end']; exact h_end_le_16) h_pts_overflow)
      (body_spec_valid i v b iter' out_pts' (by rw [h_end']; exact h_end_le_v)
        (by rw [h_end']; exact h_end_le_16) h_pts_overflow h_valid'))
    rintro (⟨iter1, out_pts1⟩ | r) ⟨h_cf, h_v⟩
    · obtain ⟨h_lt, _, h_start1, h_end1, _⟩ := h_cf
      have h_lt' : iter'.start.val < iter'.end.val := h_lt
      have h_end1' : iter1.end.val = iter'.end.val := by rw [h_end1]
      simp only at h_v ⊢
      exact ⟨⟨h_end1.trans h_end', by omega, h_v⟩, by omega⟩
    · exact h_v
  · exact ⟨rfl, h_start_le, h_valid⟩

end spqr.encoding.polynomial.PolyDecoder.from_pb_loop0

namespace spqr.encoding.polynomial.PolyDecoder

/-- **`from_pb` establishes `PointsValid`**: whenever deserialisation succeeds, every slot
of the resulting decoder has strictly increasing abscissae. -/
theorem from_pb_spec_valid
    (pb : proto.pq_ratchet.PolynomialDecoder)
    (h_pts_overflow : ∀ (j : Nat), j < pb.pts.length →
        (pb.pts[j]!).length + 4 ≤ Usize.max) :
    from_pb pb ⦃ (result : core.result.Result
        encoding.polynomial.PolyDecoder
        encoding.polynomial.PolynomialError) =>
      match result with
      | core.result.Result.Ok decoder => PointsValid decoder.pts
      | core.result.Result.Err _ => True ⦄ := by
  unfold from_pb
  simp only [alloc.vec.Vec.len, bne_iff_ne, ne_eq, UScalar.neq_to_neq_val,
    Usize.ofNatCore_val_eq, UScalar.ofNatCore_val_eq]
  split
  · exact (WP.spec_ok _).mpr trivial
  · have h16 : pb.pts.val.length = 16 := by simpa using ‹¬¬_›
    step as ⟨out_pts, h_out⟩
    case l => exact List.replicate 16 (alloc.vec.Vec.new Pt)
    case hl =>
      apply core.array.from_fn_loop_const
      · intro g i
        simp only [from_pb.closure.Insts.CoreOpsFunctionFnMutTupleUsizeSortedSetPt.call_mut,
          sorted_vec.SortedSet.new]
        exact bind_ok _ _
      · scalar_tac
    case hlen => rfl
    have h_valid0 : PointsValid out_pts := by
      apply PointsValid_of_forall_nil
      intro s hs
      rw [h_out] at hs
      obtain ⟨_, rfl⟩ := List.mem_replicate.mp hs
      rfl
    exact from_pb_loop0.loop_spec_valid { start := 0#usize, «end» := 16#usize } pb.pts_needed
      pb.pts pb.is_complete out_pts (by simp [h16]) (by simp) (by simp) h_pts_overflow h_valid0

end spqr.encoding.polynomial.PolyDecoder
