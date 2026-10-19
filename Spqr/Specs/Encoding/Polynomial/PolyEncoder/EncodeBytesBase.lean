/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

import Spqr.Specs.Encoding.Polynomial.NUM_POLYS
import Spqr.Specs.Aeneas.SliceChunksExact
import Spqr.Specs.Encoding.Gf.GF16.New
public import Spqr.Specs.Encoding.Polynomial.PolyEncoder.IntoPb
public import Spqr.Auxiliary.Aeneas.Slice
public import Spqr.Specs.Encoding.Polynomial.PolyEncoder.Defs
public import SrcTranslated.Funs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Tactic.ComputeDegree
import Spqr.Math.Gf16.Irreducible
import Spqr.Math.Poly.LinearFactors.Degree
import Spqr.Specs.Aeneas.VecExtendFromSlice
import Spqr.Specs.Encoding.Polynomial.Poly.Serialize

/-! # Spec theorem for `PolyEncoder::encode_bytes_base`: loop body 0

One iteration pops the head chunk `chd`, increments count, appends a GF16 element
with `g.toGF216 = (256 * chd[0]! + chd[1]!).toGF216` to `pts[count % 16].value`,
and leaves other slots unchanged. -/

@[expose] public section

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf spqr.math.gf

namespace spqr.encoding.polynomial.PolyEncoder.encode_bytes_base_loop

private lemma getElem!_of_drop_cons {l : List (Slice U8)} {n : Nat}
    {hd : Slice U8} {tl : List (Slice U8)} (h : l.drop n = hd :: tl) :
    l[n]! = hd := by
  have h1 : l[n]! = (l.drop n)[0]! := by rw [List.getElem!_drop]; simp
  rw [h1, h]
  simp

private lemma drop_succ_of_drop_cons {α : Type*} {l : List α} {n : Nat}
    {hd : α} {tl : List α} (h : l.drop n = hd :: tl) :
    l.drop (n + 1) = tl := by
  rw [← List.drop_drop, h]; rfl

/-- Pops head chunk `chd`, advances chunks to `ctl`, increments count, appends
`g` with `g.toGF216 = (256 * chd[0]! + chd[1]!).toGF216` to `pts[count % 16].value`,
and preserves other slots. -/
private theorem body_spec_chunk
    (iter' : core.iter.adapters.enumerate.Enumerate
      (core.slice.iter.ChunksExact U8))
    (pts' : Array Point 16#usize)
    (chd : Slice U8) (ctl : List (Slice U8))
    (h_chunks : iter'.iter.chunks = chd :: ctl)
    (h_push_ok : ∀ (j : Nat), j < 16 → (pts'[j]!).value.length + 1 ≤ Usize.max)
    (h_chunks_len : ∀ c ∈ iter'.iter.chunks, c.length = 2)
    (h_count_bound : iter'.count.val + 1 ≤ Usize.max) :
    body iter' pts' ⦃ cf =>
      match cf with
      | ControlFlow.done _ => False
      | ControlFlow.cont (iter'', pts'') =>
          iter''.iter.chunks = ctl ∧
          iter''.count.val = iter'.count.val + 1 ∧
          ∃ (g : GF16),
            g.toGF216 = (256 * chd[0]! + chd[1]!).toGF216 ∧
            pts''[iter'.count.val % 16]!.value =
              (pts'[iter'.count.val % 16]!).value ++ [g] ∧
            (∀ k, k ≠ iter'.count.val % 16 → pts''[k]! = pts'[k]!) ⦄ := by
  unfold body
  simp only [
    core.iter.adapters.enumerate.IteratorEnumerate.next,
    core.slice.iter.IteratorChunksExact.next]
  split
  next h_nil => rw [h_chunks] at h_nil; exact absurd h_nil (List.cons_ne_nil _ _)
  next hd tl rest =>
    have h_hd : hd = chd := by have h := rest.symm.trans h_chunks; injection h
    have h_tl : tl = ctl := by have h := rest.symm.trans h_chunks; injection h
    subst h_hd; subst h_tl
    have h_hd_len : hd.length = 2 := h_chunks_len hd (by rw [h_chunks]; exact List.mem_cons_self ..)
    simp only [bind_tc_eq, Std.bind_assoc, bind_ok]
    step as ⟨count1, h_count1⟩
    simp only [lift, bind_ok]
    step as ⟨poly, h_poly⟩
    step as ⟨p1, index_mut_back, h_p1, h_back⟩
    step as ⟨i2, h_i2⟩
    step as ⟨i4, h_i4, _⟩
    step as ⟨i5, h_i5⟩
    step as ⟨i7, h_i7⟩
    step as ⟨g, h_g⟩
    have h_poly_val : poly.val = iter'.count.val % 16 := by rw [h_poly]; simp
    have h_poly_lt : poly.val < (pts' : List Point).length := by
      rw [h_poly_val, pts'.property]; exact Nat.mod_lt _ (by norm_num)
    have h_p1' : p1 = pts'[iter'.count.val % 16]! := by
      rw [h_p1, Array.getElem!_Nat_eq, ← h_poly_val]
      exact List.Inhabited_getElem_eq_getElem! _ _ h_poly_lt
    have : p1.value.val.length < Usize.max := by
      have := h_push_ok (iter'.count.val % 16) (Nat.mod_lt _ (by norm_num))
      rw [← h_p1'] at this; simp only [alloc.vec.Vec.length] at this; omega
    step as ⟨v, h_v⟩
    have h_arr : (index_mut_back { value := v } : Std.Array Point 16#usize).val =
        (pts' : List Point).set (iter'.count.val % 16) { value := v } := by
      rw [h_back, Array.set_val_eq, h_poly_val]
    have h_mod_lt : iter'.count.val % 16 < (pts' : List Point).length := h_poly_val ▸ h_poly_lt
    refine ⟨h_count1, g, ?_, ?_, fun k hk => ?_⟩
    · -- `g = 256 * hd[0] + hd[1]`
      rw [h_g]
      congr 1
      have hi2 : i2.val < 256 := i2.hBounds
      have hi5 : i5.val < 256 := i5.hBounds
      have h_len' : (hd : List U8).length = 2 := h_hd_len
      have h_hd0 : (hd[0]! : U8) = i2 := by
        rw [h_i2, Slice.getElem!_Nat_eq]
        exact (List.Inhabited_getElem_eq_getElem! (hd : List U8) 0 (by omega)).symm
      have h_hd1 : (hd[1]! : U8) = i5 := by
        rw [h_i5, Slice.getElem!_Nat_eq]
        exact (List.Inhabited_getElem_eq_getElem! (hd : List U8) 1 (by omega)).symm
      rw [h_hd0, h_hd1, h_i7, h_i4, Nat.shiftLeft_eq]
      scalar_tac
    · simp only [Array.getElem!_Nat_eq, h_arr, List.getElem!_eq_getElem?_getD,
        List.getElem?_set_self h_mod_lt, Option.getD_some, h_v, h_p1']
    · simp only [Array.getElem!_Nat_eq, h_arr, List.getElem!_eq_getElem?_getD,
        List.getElem?_set_ne (Ne.symm hk)]

/-! # Spec theorem for `PolyEncoder::encode_bytes_base`: loop 0

Starting from `count = 0`, the loop produces `pts'[j]!.value = pts[j]!.value ++ suffix` where
`suffix.length = chunks.length / 16 + (if j < chunks.length % 16 then 1 else 0)` and
`suffix[m]!.toGF216 = (256 * chunks[j + 16*m]![0]! + chunks[j + 16*m]![1]!).toGF216`. -/
@[step]
theorem loop_spec
    (iter : core.iter.adapters.enumerate.Enumerate
      (core.slice.iter.ChunksExact U8))
    (pts : Array Point 16#usize)
    (h_count_zero : iter.count.val = 0)
    (h_push_ok : ∀ (j : Nat), j < 16 →
        (pts[j]!).value.length + iter.iter.chunks.length ≤ Usize.max)
    (h_chunks_len : ∀ c ∈ iter.iter.chunks, c.length = 2)
    (h_count_chunks : iter.count + iter.iter.chunks.length ≤ Usize.max) :
    encode_bytes_base_loop iter pts ⦃ (pts' : Array Point 16#usize) =>
      ∀ (j : Nat), j < 16 →
        ∃ (suffix : List GF16),
          pts'[j]!.value = pts[j]!.value ++ suffix ∧
          suffix.length = iter.iter.chunks.length / 16 +
            (if j < iter.iter.chunks.length % 16 then 1 else 0) ∧
          ∀ (m : Nat), m < suffix.length →
            j + 16 * m < iter.iter.chunks.length ∧
            suffix[m]!.toGF216 =
              (256 * (iter.iter.chunks[j + 16 * m]!)[0]! +
               (iter.iter.chunks[j + 16 * m]!)[1]!).toGF216 ⦄ := by
  unfold encode_bytes_base_loop
  set chunks := iter.iter.chunks with h_chunks_def
  apply loop.spec_decr_nat
    (measure := fun (p : core.iter.adapters.enumerate.Enumerate
      (core.slice.iter.ChunksExact U8) × Array Point 16#usize) =>
      p.1.iter.chunks.length)
    (inv := fun (p : core.iter.adapters.enumerate.Enumerate
      (core.slice.iter.ChunksExact U8) × Array Point 16#usize) =>
      let it := p.1
      let ps := p.2
      it.iter.chunks = chunks.drop it.count.val ∧
      it.count.val ≤ chunks.length ∧
      (∀ c ∈ it.iter.chunks, c.length = 2) ∧
      (it.count.val + it.iter.chunks.length ≤ Usize.max) ∧
      (∀ j, j < 16 → (ps[j]! : Point).value.length + it.iter.chunks.length ≤ Usize.max) ∧
      (∀ j, j < 16 → ∃ sfx : List GF16,
        (ps[j]! : Point).value = (pts[j]! : Point).value ++ sfx ∧
        sfx.length = it.count.val / 16 +
          (if j < it.count.val % 16 then 1 else 0) ∧
        ∀ m, m < sfx.length →
          j + 16 * m < chunks.length ∧
          sfx[m]!.toGF216 =
            (256 * ((chunks[j + 16 * m]!)[0]!).val +
             ((chunks[j + 16 * m]!)[1]!).val).toGF216))
  · rintro ⟨it, ps⟩ ⟨h_drop, h_le, h_clen, h_cbound, h_pbnd, h_sinv⟩
    simp only [] at h_drop h_le h_clen h_cbound h_pbnd h_sinv
    cases h_ch : it.iter.chunks with
    | nil =>
      have h_cnt_eq : it.count.val = chunks.length := by
        have h1 := congrArg List.length h_drop
        rw [h_ch, List.length_drop] at h1
        simp only [List.length_nil] at h1
        omega
      rw [h_cnt_eq] at h_sinv
      unfold body
      simpa [core.iter.adapters.enumerate.IteratorEnumerate.next,
        core.slice.iter.IteratorChunksExact.next, h_ch] using h_sinv
    | cons hd tl =>
      have h_push' : ∀ j, j < 16 → (ps[j]! : Point).value.length + 1 ≤ Usize.max := by
        intro j hj
        have h := h_pbnd j hj
        rw [h_ch, List.length_cons] at h; omega
      have h_cnt_ok : it.count.val + 1 ≤ Usize.max := by
        rw [h_ch] at h_cbound; simp at h_cbound; omega
      have h_clen' : ∀ c ∈ it.iter.chunks, c.length = 2 := h_clen
      have h_body := body_spec_chunk it ps hd tl h_ch h_push' h_clen' h_cnt_ok
      apply WP.spec_mono h_body
      intro cf h_cf
      match cf with
      | ControlFlow.done _ => exact h_cf.elim
      | ControlFlow.cont ⟨it'', ps''⟩ =>
        obtain ⟨h_tl, h_cnt, g, h_g, h_slot, h_other⟩ := h_cf
        set k := it.count.val with hk_def
        have h_concat : chunks.drop k = hd :: tl := by rw [← h_ch, h_drop]
        have h_k_lt : k < chunks.length := by
          have := congr_arg List.length h_concat
          simp only [List.length_drop, List.length_cons] at this; omega
        have h_hd_eq : chunks[k]! = hd := getElem!_of_drop_cons h_concat
        have h_drop_succ : chunks.drop (k + 1) = tl := drop_succ_of_drop_cons h_concat
        constructor
        · simp only []
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [h_tl, h_cnt, h_drop_succ]
          · rw [h_cnt]; omega
          · rw [h_tl]; intro c hc
            exact h_clen c (by rw [h_ch]; exact List.mem_cons_of_mem _ hc)
          · have h_cb : it.count.val + (hd :: tl).length ≤ Usize.max := by
              rw [← h_ch]; exact h_cbound
            rw [h_cnt, h_tl]; simp at h_cb ⊢; omega
          · intro j hj
            by_cases heq : j = k % 16
            · subst heq
              have hlen : (ps''[k % 16]! : Point).value.length =
                  (ps[k % 16]! : Point).value.length + 1 := by
                have := congrArg List.length h_slot
                simpa only [List.length_append, List.length_singleton] using this
              rw [hlen, h_tl]
              have h := h_pbnd (k % 16) (by omega)
              rw [h_ch, List.length_cons] at h; omega
            · rw [h_other j heq, h_tl]
              have h := h_pbnd j hj
              rw [h_ch, List.length_cons] at h; omega
          · intro j hj
            obtain ⟨sfx, h_sfx_eq, h_sfx_len, h_sfx_cont⟩ := h_sinv j hj
            by_cases heq : j = k % 16
            · subst heq
              refine ⟨sfx ++ [g], ?_, ?_, ?_⟩
              · rw [h_slot, h_sfx_eq, List.append_assoc]
              · rw [List.length_append, List.length_cons, List.length_nil,
                    h_sfx_len, h_cnt]
                have h16 : k % 16 < 16 := Nat.mod_lt _ (by norm_num)
                split_ifs <;> omega
              · intro m hm
                rw [List.length_append, List.length_cons, List.length_nil,
                    h_sfx_len] at hm
                simp only [Nat.lt_succ_iff] at hm
                by_cases hm_old : m < sfx.length
                · have h_get : (sfx ++ [g])[m]! = sfx[m]! := by
                    simp only [List.getElem!_eq_getElem?_getD]
                    rw [getElem?_append_of_lt sfx [g] hm_old]
                  rw [h_get]
                  exact h_sfx_cont m hm_old
                · push Not at hm_old
                  have h_m_eq : m = sfx.length := by omega
                  subst h_m_eq
                  constructor
                  · have h_sfx_len' : sfx.length = k / 16 := by
                      rw [h_sfx_len]; simp
                    rw [h_sfx_len']
                    omega
                  · have h_get : (sfx ++ [g])[sfx.length]! = g := by
                      simp only [List.getElem!_eq_getElem?_getD]
                      rw [List.getElem?_append_right (by omega)]
                      simp
                    rw [h_get, h_g]
                    have h_sfx_len' : sfx.length = k / 16 := by
                      rw [h_sfx_len]; simp
                    have hk : k % 16 + 16 * (k / 16) = k := Nat.mod_add_div k 16
                    rw [h_sfx_len', hk, h_hd_eq]
            · refine ⟨sfx, ?_, ?_, h_sfx_cont⟩
              · rw [h_other j heq, h_sfx_eq]
              · rw [h_sfx_len, h_cnt]
                split_ifs <;> omega
        · change it''.iter.chunks.length < (hd :: tl).length
          rw [h_tl, List.length_cons]; omega
  · simp only []
    refine ⟨?_, ?_, h_chunks_len, ?_, ?_, ?_⟩
    · rw [h_count_zero, List.drop_zero]
    · rw [h_count_zero]; omega
    · rw [h_count_zero] at h_count_chunks ⊢
      simp only [zero_add] at h_count_chunks ⊢
      exact h_count_chunks
    · exact h_push_ok
    · intro j hj
      exact ⟨[], by simp, by simp [h_count_zero], fun m hm => by simp at hm⟩

end spqr.encoding.polynomial.PolyEncoder.encode_bytes_base_loop

/-! # Spec theorem for `spqr::encoding::polynomial::{PolyEncoder}::encode_bytes_base`

For even-length `msg` with `msg.length ≤ 2 ^ 16 * 16`, returns `Ok(⟨0#u32, Points pts⟩)`.
Each `pts[j]!.value` has length `msg.length / 2 / 16 + (1 if j < (msg.length / 2) % 16)`,
and `(listToGF216Poly pts[j]!.value).coeff k =
(256 * msg[2 * (j + 16 * k)]! + msg[2 * (j + 16 * k) + 1]!.val).toGF216`. -/

namespace spqr.encoding.polynomial.PolyEncoder

/-- `2 ^ 16 * 16` fits in `usize` on every platform. -/
private lemma pow16_mul16_le_usize_max : (2 : Nat) ^ 16 * 16 ≤ Usize.max := by
  simp only [Usize.max, Usize.numBits]
  cases System.Platform.numBits_eq <;> simp_all

/-- `1 <<< 16 = 65536` as a `usize` value on every platform. -/
private lemma shift16_mod_usize_size : (1 <<< 16) % Usize.size = 65536 := by
  rw [show (1 : Nat) <<< 16 = 65536 by norm_num [Nat.shiftLeft_eq]]
  apply Nat.mod_eq_of_lt
  simp only [Usize.size, Usize.numBits]
  cases System.Platform.numBits_eq <;> simp_all

private theorem call_mut_ok
    (c : PolyEncoder.encode_bytes_base.closure) (i : Usize) :
    PolyEncoder.encode_bytes_base.closure.Insts.CoreOpsFunctionFnMutTupleUsizePoint.call_mut
      c i = ok (⟨alloc.vec.Vec.new encoding.gf.GF16⟩, c) := by
  unfold
    PolyEncoder.encode_bytes_base.closure.Insts.CoreOpsFunctionFnMutTupleUsizePoint.call_mut
  have h_div : ∃ z, (Slice.len c) / 2#usize = ok z := by
    obtain ⟨z, hz, _⟩ := UScalar.div_spec (Slice.len c) (y := 2#usize) (by decide)
    exact ⟨z, hz⟩
  obtain ⟨z, hz⟩ := h_div
  simp only [hz, bind_ok, alloc.vec.Vec.with_capacity]

private theorem chunks_exact_content (msg : Slice U8)
    (ce : core.slice.iter.ChunksExact U8)
    (h_content : ∀ j, j < ce.chunks.length →
        ce.chunks[j]!.val = (msg.val.drop (2 * j)).take 2)
    (i : Nat) (hi : i < ce.chunks.length) :
    (ce.chunks[i]!)[0]! = msg[2 * i]! ∧
    (ce.chunks[i]!)[1]! = msg[2 * i + 1]! := by
  have h_ci := h_content i hi
  simp only [Slice.getElem!_Nat_eq] at *
  rw [h_ci]
  constructor
  · rw [List.getElem!_take_of_lt 2 0 _ (by omega), List.getElem!_drop]; simp
  · rw [List.getElem!_take_of_lt 2 1 _ (by omega), List.getElem!_drop]


/-- **Spec theorem for `encoding.polynomial.PolyEncoder.encode_bytes_base`** (nat-level):

For even `msg` with `msg.length ≤ 2 ^ 16 * 16`, returns `Ok(⟨0#u32, Points pts⟩)` where:
  • `pts[j]!.value.length = msg.length / 2 / 16 + (1 if j < (msg.length / 2) % 16)`,
  • `(listToGF216Poly pts[j]!.value).coeff k =
    (256 * msg[2 * (j + 16 * k)]! + msg[2 * (j + 16 * k) + 1]!.val).toGF216`. -/
@[step]
theorem encode_bytes_base_spec (msg : Slice U8)
    (h_even : msg.length % 2 = 0)
    (h_len : msg.length ≤ 2 ^ 16 * 16) :
    encode_bytes_base msg ⦃ (result : core.result.Result PolyEncoder encoding.EncodingError) =>
      match result with
      | core.result.Result.Ok ⟨idx, EncoderState.Points pts⟩ =>
        idx = 0#u32 ∧
        (∀ (j : Nat), j < 16 →
          pts[j]!.value.length =
            if j < (msg.length / 2) % 16
            then msg.length / 2 / 16 + 1
            else msg.length / 2 / 16) ∧
        (∀ (j : Nat), j < 16 →
          ∀ (k : Nat), k < pts[j]!.value.length →
            2 * (j + 16 * k) + 1 < msg.length ∧
            (listToGF216Poly pts[j]!.value).coeff k =
            (256 * msg[2 * (j + 16 * k)]! + (msg[2 * (j + 16 * k) + 1]!).val).toGF216)
      | _ => False ⦄ := by
  unfold encode_bytes_base
  step*
  case hl =>
    refine core.array.from_fn_loop_const _
      (⟨alloc.vec.Vec.new encoding.gf.GF16⟩ : Point)
      call_mut_ok msg 0#usize (16#usize).val ?_
    simp only [show (16#usize).val = 16 from rfl, show (0#usize : Usize).val = 0 from rfl,
      Nat.zero_add]
    exact Nat.le_trans (by norm_num) pow16_mul16_le_usize_max
  case hlen =>
    simp only [show (16#usize).val = 16 from rfl, List.length_replicate]
  case hy => cases System.Platform.numBits_eq <;> simp_all
  case hmax =>
    have h3 : i3.val = 65536 := by rw [← shift16_mod_usize_size]; assumption
    rw [h3]
    have := pow16_mul16_le_usize_max
    omega
  · -- `msg.len() > 2 ^ 16 * 16` contradicts `h_len`
    exfalso
    have h_i5 : i5.val = 65536 * 16 := by
      rw [‹i5.val = _›, ‹i4.val = _›, ‹i3.val = _›, shift16_mod_usize_size]
    have h_gt' : msg.len.val > i5.val := by scalar_tac
    have h_msglen : msg.len.val = (msg.val).length := by scalar_tac
    have h_len' : msg.val.length ≤ 65536 * 16 := h_len
    omega
  · have h_pts_empty : ∀ (j : Nat), j < 16 → pts.val[j]!.value.val = [] := by
      intro j hj
      rw [pts_post]
      interval_cases j <;> rfl
    have h_msglen : msg.len.val = (msg.val).length := by scalar_tac
    have h_len_bound : (msg.val).length ≤ Usize.max :=
      Nat.le_trans h_len pow16_mul16_le_usize_max
    apply WP.spec_bind (core.slice.Slice.chunks_exact_spec_with_content msg 2#usize (by decide))
    intro ce h_ce
    obtain ⟨h_ce_len, h_ce_count, h_ce_rem, h_ce_content⟩ := h_ce
    simp only [core.iter.traits.iterator.Iterator.enumerate.trait_default,
      core.iter.traits.iterator.Iterator.enumerate.default, bind_ok]
    apply WP.spec_bind
      (encode_bytes_base_loop.loop_spec
        ({ iter := ce, count := 0#usize } :
          core.iter.adapters.enumerate.Enumerate (core.slice.iter.ChunksExact U8))
        pts
        (by rfl)
        (fun j hj => by
          -- `pts[j]` is still empty, and there are `msg.len() / 2` chunks
          have h0 : (pts[j]! : Point).value.length = 0 := by
            simpa [Array.getElem!_Nat_eq, alloc.vec.Vec.length] using
              congrArg List.length (h_pts_empty j hj)
          rw [h0, zero_add, h_ce_count]
          exact Nat.le_trans (Nat.div_le_self _ _) h_len_bound)
        (fun c hc => h_ce_len c hc)
        (by
          simp only [show (0#usize : Usize).val = 0 from rfl, Nat.zero_add]
          rw [h_ce_count]
          exact Nat.le_trans (Nat.div_le_self _ _) h_len_bound))
    intro pts1 h_pts1
    simp only [WP.spec_ok]
    simp only [alloc.vec.Vec.length, Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD,
      Slice.length, Slice.getElem!_Nat_eq, true_and]
    have h_suffix : ∀ (j : Nat), j < 16 →
        ∃ (suffix : List GF16),
          pts1[j]!.value = pts[j]!.value ++ suffix ∧
          suffix.length = ce.chunks.length / 16 +
            (if j < ce.chunks.length % 16 then 1 else 0) ∧
          ∀ (m : Nat), m < suffix.length →
            j + 16 * m < ce.chunks.length ∧
            suffix[m]!.toGF216 =
              (256 * (ce.chunks[j + 16 * m]!)[0]! +
               (ce.chunks[j + 16 * m]!)[1]!).toGF216 := by
      intro j hj
      exact h_pts1 j hj
    constructor
    · intro j hj
      obtain ⟨suffix, h_eq, h_len_suf, _⟩ := h_suffix j hj
      have h_empty := h_pts_empty j hj
      have h_empty' : (pts[j]!).value.val = [] := by
        rw [Array.getElem!_Nat_eq]; exact h_empty
      have h_val_eq : pts1[j]!.value.val = suffix := by
        rw [h_eq, h_empty', List.nil_append]
      change pts1[j]!.value.val.length = _
      rw [h_val_eq, h_len_suf, h_ce_count]
      simp only [show (2#usize).val = 2 from rfl]
      split <;> rfl
    · intro j hj k hk
      obtain ⟨suffix, h_eq, h_len_suf, h_content⟩ := h_suffix j hj
      have h_empty := h_pts_empty j hj
      have h_empty' : (pts[j]!).value.val = [] := by
        rw [Array.getElem!_Nat_eq]; exact h_empty
      have h_val_eq : pts1[j]!.value.val = suffix := by
        rw [h_eq, h_empty', List.nil_append]
      have hk' : k < suffix.length := by
        rw [← h_val_eq]; exact hk
      obtain ⟨h_chunk_bound, h_enc⟩ := h_content k hk'
      have h_bound : 2 * (j + 16 * k) + 1 < msg.val.length := by
        have h_even' : msg.val.length % 2 = 0 := by
          have := h_even; simp only [Slice.length] at this; exact this
        have h_cb : j + 16 * k < msg.val.length / 2 := by
          have := h_ce_count; simp only [show (2#usize).val = 2 from rfl] at this; omega
        omega
      refine ⟨h_bound, ?_⟩
      simp only [← List.getElem!_eq_getElem?_getD]
      simp only [Array.getElem!_Nat_eq] at h_val_eq
      simp only [h_val_eq, ← getElem!_toGF216_eq_coeff]
      rw [h_enc]
      have h_bytes := chunks_exact_content msg ce h_ce_content (j + 16 * k) h_chunk_bound
      simp only [Slice.getElem!_Nat_eq] at h_bytes ⊢
      rw [h_bytes.1, h_bytes.2]

end spqr.encoding.polynomial.PolyEncoder
