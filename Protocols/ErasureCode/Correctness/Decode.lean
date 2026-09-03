/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Alessandro D'Angelo
-/
import Protocols.ErasureCode.Correctness.Encode
import Spqr.Specs.Encoding.Polynomial.PolyDecoder.New
import Spqr.Specs.Encoding.Polynomial.PolyDecoder.AddChunk

/-! # Concrete decoder and its model correspondence -/

open Aeneas Aeneas.Std Result Polynomial
open ErasureCode.SPQRReedSolomon
open spqr encoding.polynomial

namespace Protocols.ErasureCode

private theorem ptCmp_eq (a b : Pt) :
    Pt.Insts.CoreCmpOrd.cmp a b =
      .ok (compare a.x.value.val b.x.value.val) := by
  obtain ⟨r, hcall, hr⟩ := WP.spec_imp_exists (Pt.Insts.CoreCmpOrd.cmp_spec a b)
  rw [hr] at hcall
  exact hcall

private theorem sortedInsert_fresh
    (l : List Pt) (p : Pt) (i : ℕ)
    (hsorted : SortedStore l)
    (hfresh : ∀ q ∈ l, q.x.value.val ≠ p.x.value.val) :
    ∃ idx newList,
      sorted_vec.SortedSet.sortedInsert Pt.Insts.CoreCmpOrd l p i =
        .ok (idx, none, newList) ∧
      SortedStore newList ∧
      newList.length = l.length + 1 ∧
      ∀ q, q ∈ newList ↔ q ∈ l ∨ q = p := by
  induction l generalizing i with
  | nil =>
      exact ⟨i, [p], rfl, by simp [SortedStore], by simp, fun q => by simp [eq_comm]⟩
  | cons a rest ih =>
      have hs := List.pairwise_cons.mp hsorted
      have hfa := hfresh a (by simp)
      have hfr : ∀ q ∈ rest, q.x.value.val ≠ p.x.value.val := by
        intro q hq
        exact hfresh q (by simp [hq])
      simp only [sorted_vec.SortedSet.sortedInsert, ptCmp_eq]
      by_cases hap : a.x.value.val < p.x.value.val
      · rw [(Nat.compare_eq_lt).2 hap]
        obtain ⟨idx, newList, hcall, hsorted', hlength, hmem⟩ :=
          ih (i + 1) hs.2 hfr
        rw [hcall]
        refine ⟨idx, a :: newList, rfl,
          List.Pairwise.cons (fun q hq => ?_) hsorted', by simp [hlength],
          fun q => by simp only [List.mem_cons, hmem]; tauto⟩
        rcases (hmem q).mp hq with hq | rfl
        · exact hs.1 q hq
        · exact hap
      · have hpa : p.x.value.val < a.x.value.val := by omega
        rw [(Nat.compare_eq_gt).2 hpa]
        refine ⟨i, p :: a :: rest, rfl,
          List.Pairwise.cons (fun q hq => ?_) hsorted, by simp,
          fun q => by simp only [List.mem_cons]; tauto⟩
        rcases List.mem_cons.mp hq with rfl | hq
        · exact hpa
        · exact lt_trans hpa (hs.1 q hq)

@[step]
private theorem sortedSet_push_fresh_spec
    (s : sorted_vec.SortedSet Pt) (p : Pt)
    (hroom : s.val.length + 1 ≤ Usize.max)
    (hsorted : SortedStore s.val)
    (hfresh : ∀ q ∈ s.val, q.x.value.val ≠ p.x.value.val) :
    sorted_vec.SortedSet.push Pt.Insts.CoreCmpOrd s p
      ⦃ ((_, displaced), s') =>
      displaced = none ∧
      SortedStore s'.val ∧
      s'.val.length = s.val.length + 1 ∧
      ∀ q, q ∈ s'.val ↔ q ∈ s.val ∨ q = p ⦄ := by
  unfold sorted_vec.SortedSet.push
  rw [dif_pos hroom]
  split
  · rename_i hlast
    have hs_nil := List.getLast?_eq_none_iff.mp hlast
    simp [hs_nil, SortedStore]
  · rename_i last hlast
    have hlast_mem : last ∈ s.val := by
      obtain ⟨pre, hpref⟩ := List.getLast?_eq_some_iff.mp hlast
      rw [hpref]
      simp
    have hlast_ne := hfresh last hlast_mem
    have hcmp := ptCmp_eq p last
    simp only [hcmp, bind_tc_ok]
    by_cases hgt : last.x.value.val < p.x.value.val
    · rw [(Nat.compare_eq_gt).2 hgt]
      simp only [WP.spec_ok]
      have hmax : ∀ q ∈ s.val, q.x.value.val < p.x.value.val := by
        intro q hq
        obtain ⟨pre, hpref⟩ := List.getLast?_eq_some_iff.mp hlast
        have hcross := (List.pairwise_append.mp (hpref ▸ hsorted)).2.2
        rw [hpref] at hq
        rcases List.mem_append.mp hq with hq | hq
        · exact lt_trans (hcross q hq last (by simp)) hgt
        · exact (List.mem_singleton.mp hq).symm ▸ hgt
      refine ⟨rfl, ?_, by simp, fun q => by simp⟩
      exact List.pairwise_append.mpr ⟨hsorted, by simp, fun q hq r hr =>
        (List.mem_singleton.mp hr).symm ▸ hmax q hq⟩
    · have hlt : p.x.value.val < last.x.value.val := by omega
      rw [(Nat.compare_eq_lt).2 hlt]
      obtain ⟨idx, newList, hcall, hsorted', hlength, hmem⟩ :=
        sortedInsert_fresh s.val p 0 hsorted hfresh
      obtain ⟨pos, hidx, hpos_le, _⟩ :=
        sorted_vec.SortedSet.sortedInsert_spec Pt.Insts.CoreCmpOrd
          s.val p 0 hcall
      have hbnd : newList.length ≤ Usize.max ∧ idx ≤ Usize.max := by
        constructor
        · omega
        · have hs_bound := s.property
          omega
      simp only [hcall, dif_pos hbnd, WP.spec_ok]
      exact ⟨rfl, hsorted', hlength, hmem⟩

private def StoreInv (l : List Pt) (P : Polynomial GF216)
    (seen : Finset ℕ) (n k : ℕ) : Prop :=
  SortedStore l ∧
  StoreOn l P ∧
  (∀ p ∈ l, p.x.value.val ∈ seen) ∧
  Nat.min n k ≤ l.length ∧
  l.length ≤ n

private theorem StoreInv.promote
    {l : List Pt} {P : Polynomial GF216} {seen : Finset ℕ}
    {n k x : ℕ}
    (hinv : StoreInv l P seen n k) (hfull : k ≤ l.length) :
    StoreInv l P (insert x seen) (n + 1) k := by
  refine ⟨hinv.1, hinv.2.1, ?_, ?_, ?_⟩
  · intro p hp
    exact Finset.mem_insert_of_mem (hinv.2.2.1 p hp)
  · exact (Nat.min_le_right (n + 1) k).trans hfull
  · exact hinv.2.2.2.2.trans (Nat.le_succ n)

private theorem u8_shl8_mod_u16_size (b : U8) :
    b.val <<< 8 % U16.size = b.val * 256 := by
  have hb : b.val ≤ 255 := by scalar_tac
  rw [Nat.shiftLeft_eq]
  simp only [Nat.reducePow]
  apply Nat.mod_eq_of_lt
  have : U16.size = 65536 := by scalar_tac
  omega

@[step]
private theorem push_storeInv_spec
    (s : sorted_vec.SortedSet Pt) (p : Pt)
    (P : Polynomial GF216) (seen : Finset ℕ) (n k x : ℕ)
    (hinv : StoreInv s.val P seen n k)
    (hx : x ∉ seen)
    (hpx : p.x.value.val = x)
    (hpon : P.eval p.x.toGF216 = p.y.toGF216)
    (hroom : s.val.length + 1 ≤ Usize.max) :
    sorted_vec.SortedSet.push Pt.Insts.CoreCmpOrd s p
      ⦃ ((_, _), s') => StoreInv s'.val P (insert x seen) (n + 1) k ⦄ := by
  have hfresh : ∀ q ∈ s.val, q.x.value.val ≠ p.x.value.val := by
    intro q hq heq
    apply hx
    have hq_seen := hinv.2.2.1 q hq
    simpa only [hpx, heq] using hq_seen
  apply WP.spec_mono
    (sortedSet_push_fresh_spec s p hroom hinv.1 hfresh)
  rintro ⟨⟨_, _⟩, s'⟩ ⟨_, hsorted, hlength, hmem⟩
  refine ⟨hsorted, ?_, ?_, ?_, ?_⟩
  · intro q hq
    rcases (hmem q).mp hq with hq | rfl
    · exact hinv.2.1 q hq
    · exact hpon
  · intro q hq
    rcases (hmem q).mp hq with hq | rfl
    · exact Finset.mem_insert_of_mem (hinv.2.2.1 q hq)
    · simpa only [hpx] using Finset.mem_insert_self x seen
  · rw [hlength]
    have hlower := hinv.2.2.2.1
    have hmin : Nat.min (n + 1) k ≤ Nat.min n k + 1 := by
      change (if n + 1 ≤ k then n + 1 else k) ≤
        (if n ≤ k then n else k) + 1
      split <;> split <;> omega
    omega
  · rw [hlength]
    have hupper := hinv.2.2.2.2
    omega

/-- Each byte pair of `chunk` stores the evaluation of the matching polynomial at the
chunk index. -/
private abbrev ChunkStores (P : ℕ → Polynomial GF216) (chunk : encoding.Chunk) : Prop :=
  ∀ j, j < 16 →
    (P j).eval chunk.index.val.toGF216 =
      Nat.toGF216
        (256 * (chunk.data.val[2 * j]!).val + (chunk.data.val[2 * j + 1]!).val)

private def DecoderLoopInv (pd : PolyDecoder) (P : ℕ → Polynomial GF216)
    (seen : Finset ℕ) (n k x t : ℕ) : Prop :=
  pd.pts_needed.val = 16 * k ∧
  pd.is_complete = false ∧
  ∀ j, j < 16 →
    if j < t then
      StoreInv (pd.pts[j]!).val (P j) (insert x seen) (n + 1) k
    else
      StoreInv (pd.pts[j]!).val (P j) seen n k

set_option maxHeartbeats 1000000 in
-- `step*` elaborates both push branches of the extracted loop body; the index bookkeeping
-- shared by every obligation is discharged once, and the obligations (which the two
-- branches duplicate) are then closed by shape.
@[step]
private theorem body_decoderLoopInv_spec
    (chunk : encoding.Chunk) (iter : core.ops.range.Range Usize)
    (pd : PolyDecoder) (P : ℕ → Polynomial GF216)
    (seen : Finset ℕ) (n k : ℕ)
    (h_end : iter.end.val = 16)
    (h_start : iter.start.val ≤ 16)
    (hinv : DecoderLoopInv pd P seen n k chunk.index.val iter.start.val)
    (hfresh : chunk.index.val ∉ seen)
    (h_on : ChunkStores P chunk)
    (h_overflow : chunk.index.val * 16 + 16 ≤ Usize.max)
    (h_push_cap : ∀ j, j < 16 →
      (pd.pts[j]!).val.length + 1 ≤ Usize.max) :
    PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk_loop.body chunk iter pd
      ⦃ cf =>
        match cf with
        | ControlFlow.done pd' =>
          pd' = pd ∧ iter.start.val = 16
        | ControlFlow.cont (iter', pd') =>
          iter.start.val < 16 ∧
          iter'.start.val = iter.start.val + 1 ∧
          iter'.end = iter.end ∧
          DecoderLoopInv pd' P seen n k chunk.index.val
            (iter.start.val + 1) ⦄ := by
  unfold PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk_loop.body
  step*
  · exact P iter.start.val
  · exact n
  · exact k
  · exact P iter.start.val
  · exact n
  · exact k
  all_goals
    have h_iter_lt : iter.start.val < iter.end.val := by
      by_contra h
      have ho_none := (o_post1 (by omega)).1
      have hbad := ho_none.symm.trans ‹o = some i›
      simp at hbad
    have h_i_eq : i = iter.start := by
      have hi := ‹o = some i›
      rw [(o_post2 h_iter_lt).1] at hi
      exact (Option.some.inj hi).symm
    have h_lt : iter.start.val < 16 := by omega
    have h_i1_val : i1.val = chunk.index.val := by
      rw [i1_post]
      exact U16.cast_Usize_val_eq chunk.index
    have h_total : total_idx.val = chunk.index.val * 16 + i.val := by
      rw [total_idx_post, i2_post, h_i1_val]
    try
      have h_poly_val : poly.val = iter.start.val := by
        rw [poly_post, h_total, h_i_eq]
        omega
    try
      have h_ss_eq : ss = pd.pts.val[poly.val]! := by
        rw [ss_post1]
        rw [getElem!_pos (h := by simp; omega)]
  all_goals
    first
    | -- the selected store satisfies the per-store invariant
      (rw [h_ss_eq, h_poly_val]
       simpa [DecoderLoopInv] using hinv.2.2 iter.start.val h_lt)
    | -- the selected store has room for one more point
      (rw [h_ss_eq, h_poly_val]
       simpa only [Aeneas.Std.Array.getElem!_Nat_eq] using
         h_push_cap iter.start.val (by omega))
    | -- continuation invariant after a successful push
      (obtain ⟨-, h_start1, h_end1⟩ := o_post2 h_iter_lt
       refine ⟨by omega, h_start1, h_end1, hinv.1, hinv.2.1, ?_⟩
       intro j hj
       have hold := hinv.2.2 j hj
       rcases Nat.lt_trichotomy j iter.start.val with hj_lt | hj_eq | hj_gt
       · have hframe : (index_mut_back ss1)[j]! = pd.pts[j]! := by
           rw [ss_post2]
           apply Aeneas.Std.Array.getElem!_Nat_set_ne
           omega
         rw [if_pos (by omega), hframe]
         simpa [hj_lt] using hold
       · subst hj_eq
         have hselected : (index_mut_back ss1)[iter.start.val]! = ss1 := by
           rw [ss_post2]
           apply Aeneas.Std.Array.getElem!_Nat_set_eq
           exact ⟨h_poly_val, by simpa using hj⟩
         rw [if_pos (by omega), hselected]
         exact __post
       · have hframe : (index_mut_back ss1)[j]! = pd.pts[j]! := by
           rw [ss_post2]
           apply Aeneas.Std.Array.getElem!_Nat_set_ne
           omega
         rw [if_neg (by omega), hframe]
         simpa [Nat.not_lt.mpr hj_gt.le] using hold)
    | -- continuation invariant on the full-store skip path
      (obtain ⟨-, h_start1, h_end1⟩ := o_post2 h_iter_lt
       have h_v_eq : v = pd.pts.val[poly.val]! := by
         rw [v_post, sv_post, ss_post]
         rw [getElem!_pos (h := by simp; omega)]
       have h_needed : i12.val = k := by
         rw [i12_post, hinv.1, h_i_eq]
         simp [Nat.mul_comm]
       have h_full : k ≤ (pd.pts[iter.start.val]!).val.length := by
         have h_len : i12.val ≤ v.val.length := by
           have hnot := ‹¬ v.len < i12›
           simp only [UScalar.lt_equiv, alloc.vec.Vec.len_val,
             alloc.vec.Vec.length] at hnot
           omega
         rw [h_needed, h_v_eq, h_poly_val] at h_len
         simpa only [Aeneas.Std.Array.getElem!_Nat_eq] using h_len
       have h_promoted :
           StoreInv (pd.pts[iter.start.val]!).val (P iter.start.val)
             (insert chunk.index.val seen) (n + 1) k :=
         StoreInv.promote
           (by simpa [DecoderLoopInv] using hinv.2.2 iter.start.val h_lt) h_full
       refine ⟨by omega, h_start1, h_end1, hinv.1, hinv.2.1, ?_⟩
       intro j hj
       have hold := hinv.2.2 j hj
       rcases Nat.lt_trichotomy j iter.start.val with hj_lt | hj_eq | hj_gt
       · rw [if_pos (by omega)]
         simpa [hj_lt] using hold
       · subst hj_eq
         rw [if_pos (by omega)]
         exact h_promoted
       · rw [if_neg (by omega)]
         simpa [Nat.not_lt.mpr hj_gt.le] using hold)
    | -- the pushed point lies on the selected polynomial
      (have h_i_lt : i.val < 16 := by
         rw [h_i_eq]
         exact h_lt
       have h_poly_idx_val : poly_idx.val = chunk.index.val := by
         rw [poly_idx_post, h_total, h_i_eq]
         omega
       have h_x_val : x.value.val = chunk.index.val := by
         simp [x_post, i3_post]
         grind
       have h_y_val : y.value.val =
           256 * (chunk.data.val[2 * iter.start.val]!).val +
             (chunk.data.val[2 * iter.start.val + 1]!).val := by
         simp [y_post, i9_post, i8_post1, y1_post, y2_post, i5_post,
           i7_post, i4_post, i6_post, UScalar.cast_val_eq, h_i_eq]
         grind [u8_shl8_mod_u16_size]
       simpa only [spqr.encoding.gf.GF16.toGF216, h_x_val, h_y_val] using
         h_on iter.start.val h_lt)

private def DecoderInv (pd : PolyDecoder) (P : ℕ → Polynomial GF216)
    (seen : Finset ℕ) (n k : ℕ) : Prop :=
  pd.pts_needed.val = 16 * k ∧
  pd.is_complete = false ∧
  ∀ j, j < 16 → StoreInv (pd.pts[j]!).val (P j) seen n k

@[step]
private theorem add_chunk_loop_decoderInv_spec
    (chunk : encoding.Chunk) (iter : core.ops.range.Range Usize)
    (pd : PolyDecoder) (P : ℕ → Polynomial GF216)
    (seen : Finset ℕ) (n k : ℕ)
    (h_end : iter.end.val = 16)
    (h_start : iter.start.val ≤ 16)
    (hinv : DecoderLoopInv pd P seen n k chunk.index.val iter.start.val)
    (hfresh : chunk.index.val ∉ seen)
    (h_on : ChunkStores P chunk)
    (hn : n < 2 ^ 16) :
    PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk_loop iter pd chunk
      ⦃ pd' => DecoderInv pd' P (insert chunk.index.val seen) (n + 1) k ⦄ := by
  unfold PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk_loop
  apply loop.spec_decr_nat
    (measure := fun p : core.ops.range.Range Usize × PolyDecoder =>
      p.1.end.val - p.1.start.val)
    (inv := fun p : core.ops.range.Range Usize × PolyDecoder =>
      p.1.end.val = 16 ∧ p.1.start.val ≤ 16 ∧
      DecoderLoopInv p.2 P seen n k chunk.index.val p.1.start.val)
  · rintro ⟨iter', pd'⟩ ⟨h_end', h_start', hinv'⟩
    have h_overflow : chunk.index.val * 16 + 16 ≤ Usize.max := by
      have hidx : chunk.index.val < 2 ^ 16 := by scalar_tac
      have hmax := Usize.cMax_bound_concrete
      omega
    have h_push_cap : ∀ j, j < 16 →
        (pd'.pts[j]!).val.length + 1 ≤ Usize.max := by
      intro j hj
      have hstore := hinv'.2.2 j hj
      simp only [Aeneas.Std.Array.getElem!_Nat_eq] at hstore ⊢
      split at hstore
      · have hupper := hstore.2.2.2.2
        have hmax := Usize.cMax_bound_concrete
        omega
      · have hupper := hstore.2.2.2.2
        have hmax := Usize.cMax_bound_concrete
        omega
    apply WP.spec_mono
      (body_decoderLoopInv_spec chunk iter' pd' P seen n k h_end'
        h_start' hinv' hfresh h_on h_overflow h_push_cap)
    intro cf hcf
    match cf with
    | ControlFlow.done pdFinal =>
      obtain ⟨rfl, h_at_end⟩ := hcf
      refine ⟨hinv'.1, hinv'.2.1, ?_⟩
      intro j hj
      have hstore := hinv'.2.2 j hj
      simpa [h_at_end, hj] using hstore
    | ControlFlow.cont (iterNext, pdNext) =>
      obtain ⟨h_lt, h_start_next, h_end_next, hinv_next⟩ := hcf
      refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      · rw [h_end_next]
        exact h_end'
      · rw [h_start_next]
        omega
      · rw [h_start_next]
        exact hinv_next
      · change iterNext.end.val - iterNext.start.val <
          iter'.end.val - iter'.start.val
        rw [h_end_next, h_start_next]
        have h_end_val : iter'.end.val = 16 := h_end'
        omega
  · exact ⟨h_end, h_start, hinv⟩

@[step]
private theorem add_chunk_decoderInv_spec
    (chunk : encoding.Chunk) (pd : PolyDecoder)
    (P : ℕ → Polynomial GF216) (seen : Finset ℕ) (n k : ℕ)
    (hinv : DecoderInv pd P seen n k)
    (hfresh : chunk.index.val ∉ seen)
    (h_on : ChunkStores P chunk)
    (hn : n < 2 ^ 16) :
    PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk pd chunk
      ⦃ pd' => DecoderInv pd' P (insert chunk.index.val seen) (n + 1) k ⦄ := by
  unfold PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk
  apply add_chunk_loop_decoderInv_spec chunk
    { start := 0#usize, «end» := 16#usize } pd P seen n k
  · rfl
  · norm_num
  · refine ⟨hinv.1, hinv.2.1, ?_⟩
    intro j hj
    simpa using hinv.2.2 j hj
  · exact hfresh
  · exact h_on
  · exact hn

private def ChunkOn (P : ℕ → Polynomial GF216)
    (c : Fin (2 ^ 16) × Chunk GF16) : Prop :=
  ∀ j : Fin 16, (P j.val).eval c.1.val.toGF216 = c.2 j

private theorem toSpqrChunk_on
    (P : ℕ → Polynomial GF216)
    (c : Fin (2 ^ 16) × Chunk GF16) (hon : ChunkOn P c) :
    ChunkStores P (toSpqrChunk c) := by
  intro j hj
  rw [toSpqrChunk_index]
  have hround := congrFun (ofSpqrChunk_toSpqrChunk c) ⟨j, hj⟩
  exact (hon ⟨j, hj⟩).trans hround.symm

private theorem foldlM_decoderInv_exists
    (chunks : List (Fin (2 ^ 16) × Chunk GF16))
    (pd : PolyDecoder) (P : ℕ → Polynomial GF216)
    (seen : Finset ℕ) (n k : ℕ)
    (hinv : DecoderInv pd P seen n k)
    (hnodup : (chunks.map fun c => c.1.val).Nodup)
    (hfresh : ∀ c ∈ chunks, c.1.val ∉ seen)
    (hon : ∀ c ∈ chunks, ChunkOn P c)
    (hbound : n + chunks.length ≤ 2 ^ 16) :
    ∃ pd' seen',
      chunks.foldlM
          (fun d c =>
            PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk d (toSpqrChunk c)) pd =
        .ok pd' ∧
      DecoderInv pd' P seen' (n + chunks.length) k := by
  induction chunks generalizing pd seen n with
  | nil =>
      exact ⟨pd, seen, rfl, by simpa using hinv⟩
  | cons c rest ih =>
      simp only [List.map_cons, List.nodup_cons] at hnodup
      have hc_fresh := hfresh c (by simp)
      have hrest_fresh : ∀ d ∈ rest, d.1.val ∉ insert c.1.val seen := by
        intro d hd
        have hd_not_seen := hfresh d (by simp [hd])
        have hd_ne : d.1.val ≠ c.1.val := by
          intro heq
          apply hnodup.1
          exact List.mem_map.mpr ⟨d, hd, heq⟩
        simpa [Finset.mem_insert, hd_ne] using hd_not_seen
      have hc_on := toSpqrChunk_on P c (hon c (by simp))
      obtain ⟨pd1, hadd, hinv1⟩ := WP.spec_imp_exists
        (add_chunk_decoderInv_spec (toSpqrChunk c) pd P seen n k hinv
          (by simpa [toSpqrChunk_index] using hc_fresh) hc_on (by
            simp only [List.length_cons] at hbound
            omega))
      obtain ⟨pd2, seen2, hrest, hinv2⟩ :=
        ih pd1 (insert c.1.val seen) (n + 1) hinv1 hnodup.2
          hrest_fresh (fun d hd => hon d (by simp [hd])) (by
            simp only [List.length_cons] at hbound
            omega)
      refine ⟨pd2, seen2, ?_, ?_⟩
      · simp only [List.foldlM_cons, hadd, bind_tc_ok]
        exact hrest
      · simpa only [List.length_cons,
          show n + (rest.length + 1) = n + 1 + rest.length from by omega] using hinv2

private noncomputable def messagePolynomials
    (k : ℕ) (hk : k ≤ 2 ^ 16) (hk_pos : 0 < k)
    (M : Fin k → Chunk GF16) (j : ℕ) : Polynomial GF216 :=
  if hj : j < 16 then
    (concreteParams k hk hk_pos).encodingPolynomial
      (fun m => M m ⟨j, hj⟩)
  else
    0

private theorem messagePolynomials_eval_encode
    (k : ℕ) (hk : k ≤ 2 ^ 16) (hk_pos : 0 < k)
    (M : Fin k → Chunk GF16) (i : Fin (2 ^ 16)) (j : Fin 16) :
    (messagePolynomials k hk hk_pos M j.val).eval i.val.toGF216 =
      (modelEC k hk hk_pos).encode M i j := by
  simp [messagePolynomials, modelEC, concreteParams,
    ErasureCode.SPQRReedSolomon.parallelErasureCode,
    ErasureCode.SPQRReedSolomon.encode,
    ErasureCode.ReedSolomon.Parameters.encode]

private theorem messagePolynomials_degree
    (k : ℕ) (hk : k ≤ 2 ^ 16) (hk_pos : 0 < k)
    (M : Fin k → Chunk GF16) (j : Fin 16) :
    (messagePolynomials k hk hk_pos M j.val).degree < k := by
  simpa [messagePolynomials, concreteParams] using
    (concreteParams k hk hk_pos).degree_encodingPolynomial_lt
      (fun m => M m j)

private theorem messagePolynomials_source
    (k : ℕ) (hk : k ≤ 2 ^ 16) (hk_pos : 0 < k)
    (M : Fin k → Chunk GF16) (m : Fin k) (j : Fin 16) :
    (messagePolynomials k hk hk_pos M j.val).eval m.val.toGF216 = M m j := by
  simpa [messagePolynomials, concreteParams,
    ErasureCode.ReedSolomon.Parameters.sourcePoint,
    ErasureCode.ReedSolomon.Parameters.sourceIndex] using
    (concreteParams k hk hk_pos).eval_encodingPolynomial_source
      (fun i => M i j) m

private theorem decoderLength_bound (k : ℕ) (hk : k ≤ 2 ^ 16) :
    32 * k < 2 ^ UScalarTy.Usize.numBits := by
  rw [UScalarTy.Usize_numBits_eq]
  have hmax := Usize.cMax_bound_concrete
  omega

private theorem new_decoderInv_exists
    (k : ℕ) (hk : k ≤ 2 ^ 16) (P : ℕ → Polynomial GF216) :
    ∃ pd,
      PolyDecoder.Insts.SpqrEncodingDecoder.new
          (Usize.ofNatCore (32 * k) (decoderLength_bound k hk)) =
        .ok (.Ok pd) ∧
      DecoderInv pd P ∅ 0 k := by
  let len : Usize :=
    Usize.ofNatCore (32 * k) (decoderLength_bound k hk)
  obtain ⟨r, hcall, hpost⟩ := WP.spec_imp_exists
    (PolyDecoder.Insts.SpqrEncodingDecoder.new_spec len)
  have hlen : len.val = 32 * k := by simp [len]
  have heven : len.val % 2 = 0 := by omega
  rw [if_pos heven] at hpost
  match r with
  | .Ok pd =>
    refine ⟨pd, by simpa [len] using hcall, ?_⟩
    have hneeded : pd.pts_needed.val = 16 * k := by
      rw [hpost.1]
      change len.val / 2 = 16 * k
      omega
    refine ⟨hneeded, hpost.2.2, ?_⟩
    intro j hj
    have hget : pd.pts[j]! =
        (default : sorted_vec.SortedSet Pt) := by
      simp only [Aeneas.Std.Array.getElem!_Nat_eq, hpost.2.1]
      rw [getElem!_pos (h := by simp [hj])]
      rw [List.getElem_replicate]
    have hstore : (pd.pts[j]!).val = [] := by
      rw [hget]
      rfl
    rw [hstore]
    simp [StoreInv, SortedStore, StoreOn]
  | .Err e =>
    exact hpost.elim

noncomputable def decodeConcrete (k : ℕ) (hk : k ≤ 2 ^ 16)
    (L : Finset (Fin (2 ^ 16) × Chunk GF16)) : Option (Fin k → Chunk GF16) :=
  match spqr.encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.new
      (Usize.ofNatCore (32 * k) (decoderLength_bound k hk)) with
  | .ok (.Ok d0) =>
      match L.toList.foldlM
          (fun d c =>
            spqr.encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk
              d (toSpqrChunk c)) d0 with
      | .ok d =>
          match
              spqr.encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.decoded_message d with
          | .ok (some b) => messageOfBytes k b
          | _ => none
      | _ => none
  | _ => none

private theorem decodeConcrete_eq (k : ℕ) (hk : k ≤ 2 ^ 16)
    {L : Finset (Fin (2 ^ 16) × Chunk GF16)} {d0 d : PolyDecoder}
    {r : Option (alloc.vec.Vec U8)}
    (hnew : PolyDecoder.Insts.SpqrEncodingDecoder.new
        (Usize.ofNatCore (32 * k) (decoderLength_bound k hk)) = .ok (.Ok d0))
    (hfold : L.toList.foldlM
        (fun d c =>
          PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk d (toSpqrChunk c)) d0 =
      .ok d)
    (hdec : PolyDecoder.Insts.SpqrEncodingDecoder.decoded_message d = .ok r) :
    decodeConcrete k hk L = r.bind (messageOfBytes k) := by
  unfold decodeConcrete
  simp only [hnew, hfold, hdec]
  cases r <;> rfl

theorem decode_toModel (k : ℕ) (hk : k ≤ 2 ^ 16) (hk_pos : 0 < k)
    (M : Fin k → Chunk GF16) (I : Finset (Fin (2 ^ 16))) :
    decodeConcrete k hk ((modelEC k hk hk_pos).encodeChunks M I) =
      (modelEC k hk hk_pos).decode ((modelEC k hk hk_pos).encodeChunks M I) := by
  classical
  let P := messagePolynomials k hk hk_pos M
  let chunks : List (Fin (2 ^ 16) × Chunk GF16) :=
    ((modelEC k hk hk_pos).encodeChunks M I).toList
  obtain ⟨d0, hnew, hd0⟩ := new_decoderInv_exists k hk P
  have hmem : ∀ c, c ∈ chunks ↔
      c.1 ∈ I ∧ c.2 = (modelEC k hk hk_pos).encode M c.1 := fun c =>
    Finset.mem_toList.trans ((modelEC k hk hk_pos).mem_encodeChunks M I c)
  have hchunks_length : chunks.length = I.card :=
    (Finset.length_toList _).trans ((modelEC k hk hk_pos).card_encodeChunks M I)
  have hindices : (chunks.map fun c => c.1.val).Nodup := by
    refine (Finset.nodup_toList _).map_on ?_
    intro a ha b hb hab
    have ha_enc := (hmem a).mp ha
    have hb_enc := (hmem b).mp hb
    have hindex : a.1 = b.1 := Fin.ext hab
    exact Prod.ext hindex (by rw [ha_enc.2, hb_enc.2, hindex])
  have hchunks_on : ∀ c ∈ chunks, ChunkOn P c := by
    intro c hc j
    rw [((hmem c).mp hc).2]
    simpa [P] using messagePolynomials_eval_encode k hk hk_pos M c.1 j
  obtain ⟨d, seen, hfold, hdinv⟩ :=
    foldlM_decoderInv_exists chunks d0 P ∅ 0 k hd0 hindices (by simp) hchunks_on
      (by simpa [hchunks_length] using Finset.card_le_univ I)
  have hdinv' : DecoderInv d P seen I.card k := by
    simpa only [Nat.zero_add, hchunks_length] using hdinv
  have hneeded : ∀ j, j < 16 → neededPoints d j = k := by
    intro j hj
    unfold neededPoints
    rw [hdinv'.1]
    simp [Nat.mul_comm]
  by_cases hcard : k ≤ I.card
  · -- enough chunks: both decoders recover `M`
    have hdegree : ∀ j, j < 16 →
        (P j).degree < (neededPoints d j : WithBot ℕ) := fun j hj => by
      simpa [P, hneeded j hj] using messagePolynomials_degree k hk hk_pos M ⟨j, hj⟩
    have hlength : ∀ j, j < 16 →
        neededPoints d j ≤ (d.pts[j]!).val.length := fun j hj => by
      have hlower := (hdinv'.2.2 j hj).2.2.2.1
      have hmin : I.card.min k = k := Nat.min_eq_right hcard
      rw [hmin] at hlower
      simpa [hneeded j hj] using hlower
    obtain ⟨r, hdecoded, hpost⟩ := WP.spec_imp_exists
      (decoded_message_spec_complete d P hdinv'.2.1
        (fun j hj => (hdinv'.2.2 j hj).1) (fun j hj => (hdinv'.2.2 j hj).2.1)
        hdegree hlength)
    obtain ⟨out, rfl, hout_length, hout_pairs⟩ := hpost
    rw [((modelEC_correct k hk hk_pos) M I).1 hcard,
      decodeConcrete_eq k hk hnew hfold hdecoded, Option.bind_some]
    apply messageOfBytes_eq_some_of_pairs
    · simpa [hdinv'.1] using hout_length
    · intro m c
      have hp := hout_pairs (16 * m.val + c.val) (by rw [hdinv'.1]; omega)
      have hmod : (16 * m.val + c.val) % 16 = c.val := by omega
      have hdiv : (16 * m.val + c.val) / 16 = m.val := by omega
      rw [hmod, hdiv] at hp
      exact hp.trans (by simpa [P] using messagePolynomials_source k hk hk_pos M m c)
  · -- not enough chunks: both decoders fail
    have hshort : ∃ j, j < 16 ∧ (d.pts[j]!).val.length < neededPoints d j := by
      refine ⟨0, by omega, ?_⟩
      have hupper := (hdinv'.2.2 0 (by omega)).2.2.2.2
      rw [hneeded 0 (by omega)]
      omega
    obtain ⟨r, hdecoded, hr⟩ := WP.spec_imp_exists
      (decoded_message_spec_short d hshort)
    subst hr
    rw [((modelEC_correct k hk hk_pos) M I).2 (show I.card < k by omega),
      decodeConcrete_eq k hk hnew hfold hdecoded]
    rfl

end Protocols.ErasureCode
