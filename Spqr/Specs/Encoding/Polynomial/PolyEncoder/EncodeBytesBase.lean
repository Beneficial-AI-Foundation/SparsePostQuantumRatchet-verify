/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Encoding.Polynomial.NUM_POLYS
import Spqr.Specs.Aeneas.SliceChunksExact
import Spqr.Specs.Encoding.Gf.GF16.New
import Spqr.Specs.Encoding.Polynomial.PolyEncoder.IntoPb

/-! # Spec theorem for `PolyEncoder::encode_bytes_base`: loop body 0

Each iteration consumes one 2-byte chunk `c` from `Enumerate<ChunksExact<u8>>`,
decodes it as `GF16::new((c[0] << 8) | c[1])`, and pushes the result onto
`pts[count % 16].value`, leaving other slots unchanged.

**Source**: spqr/src/encoding/polynomial.rs -/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf spqr.math.gf

private noncomputable instance instInhabitedSliceU8 : Inhabited (Slice U8) := ⟨⟨[], by scalar_tac⟩⟩

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
  have key : (l.drop n).drop 1 = l.drop (n + 1) := List.drop_drop
  simp only [← key, h]
  grind

/-- Body spec: consuming head chunk `chd` advances chunks to `ctl`, increments count,
pushes `GF16(256 · chd[0] + chd[1])` onto `pts[count % 16]`, and preserves other slots. -/
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
  · rename_i h_nil
    rw [h_chunks] at h_nil; exact absurd h_nil (List.cons_ne_nil _ _)
  · rename_i hd tl rest
    have h_hd : hd = chd := by have h := rest.symm.trans h_chunks; injection h
    have h_tl : tl = ctl := by have h := rest.symm.trans h_chunks; injection h
    subst h_hd; subst h_tl
    simp only [bind_tc_ok]
    step*
    · simp_all
    · simp_all
    · conv_lhs =>
        simp[i4_post1,i6_post, i3_post, i2_post, i5_post]
      rw[Nat.shiftLeft_eq]
      simp only [Nat.reducePow]
      have :((hd)[0]! * 256) < U16.size := by scalar_tac
      have := Nat.mod_eq_of_lt this
      grind
    · simp_all; grind
    · simp_all only [alloc.vec.Vec.length, Array.getElem!_Nat_eq, List.Vector.length_val,
      UScalar.ofNatCore_val_eq, getElem!_pos, Order.add_one_le_iff, Usize.ofNatCore_val_eq,
      Array.val_to_slice, UScalarTy.U8_numBits_eq, UScalarTy.U16_numBits_eq, Nat.reduceLeDiff,
      UScalar.cast_val_mod_pow_greater_numBits_eq, Bvify.U16.UScalar_bv, Bvify.UScalar.cast_bv,
      Bvify.U8.UScalar_bv, Slice.getElem!_Nat_eq, List.mem_cons, true_or,
      Order.lt_two_iff, zero_le, Std.le_refl, Array.set_val_eq, List.getElem!_eq_getElem?_getD,
      ne_eq, Nat.not_eq, not_false_eq_true, lt_or_lt_iff_ne, or_true, List.set_getElem?_neq,
      implies_true, and_true, true_and]
      use g
      simp_all only
      constructor
      · congr 1
        rw [Nat.shiftLeft_eq]
        simp only [Nat.reducePow]
        have : (↑(hd.val)[0]! : Nat) * 256 < U16.size := by scalar_tac
        grind [Nat.mod_eq_of_lt this]
      · have h_len : (↑pts' : List Point).length = 16 := by scalar_tac
        simp_all
        grind

/-! # Spec theorem for `PolyEncoder::encode_bytes_base`: loop 0

After the full loop, each `pts[j].value` gains a suffix of length
`⌊n/16⌋ + (1 if j < n%16)` (where `n` is the chunk count), whose `m`-th element
is the big-endian GF(2¹⁶) decode of chunk `j + 16·m`.

**Source**: spqr/src/encoding/polynomial.rs -/
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
      (∀ j, j < 16 → (ps[j]!).value.length + it.iter.chunks.length ≤ Usize.max) ∧
      (∀ j, j < 16 → ∃ sfx : List GF16,
        ps[j]!.value = pts[j]!.value ++ sfx ∧
        sfx.length = it.count.val / 16 +
          (if j < it.count.val % 16 then 1 else 0) ∧
        ∀ m, m < sfx.length →
          j + 16 * m < chunks.length ∧
          sfx[m]!.toGF216 =
            (256 * (chunks[j + 16 * m]!)[0]! +
             (chunks[j + 16 * m]!)[1]!).toGF216))
  · rintro ⟨it, ps⟩ ⟨h_drop, h_le, h_clen, h_cbound, h_pbnd, h_sinv⟩
    simp only [] at h_drop h_le h_clen h_cbound h_pbnd h_sinv
    cases h_ch : it.iter.chunks with
    | nil =>
      unfold body
      simp only [
        core.iter.adapters.enumerate.IteratorEnumerate.next,
        core.slice.iter.IteratorChunksExact.next,
        h_ch, bind_tc_ok]
      have h_cnt_eq : it.count.val = chunks.length := by
        have h1 : (chunks.drop it.count.val).length = chunks.length - it.count.val :=
          List.length_drop
        grind
      intro j hj
      obtain ⟨sfx, h_eq, h_len, h_cont⟩ := h_sinv j hj
      exact ⟨sfx, h_eq, by rw [h_cnt_eq] at h_len; exact h_len, h_cont⟩
    | cons hd tl =>
      have h_push' : ∀ j, j < 16 → (ps[j]!).value.length + 1 ≤ Usize.max := by
        intro j hj
        have h := h_pbnd j hj
        rw [h_ch] at h; simp at h; grind
      have h_cnt_ok : it.count.val + 1 ≤ Usize.max := by
        rw [h_ch] at h_cbound; simp at h_cbound; omega
      have h_clen' : ∀ c ∈ it.iter.chunks, c.length = 2 := h_clen
      have h_body := body_spec_chunk it ps hd tl h_ch h_push'
        (by rw [h_ch] at h_clen'; grind) h_cnt_ok
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
              have hlen : (ps''[k % 16]!).value.length = (ps[k % 16]!).value.length + 1 := by
                have := congr_arg (fun v => v.length) h_slot
                simp only [ Array.getElem!_Nat_eq,
                  List.getElem!_eq_getElem?_getD] at this
                grind
              rw [hlen, h_tl]
              have h := h_pbnd (k % 16) (by omega)
              rw [h_ch] at h; simp at h; grind
            · rw [h_other j heq, h_tl]
              have h := h_pbnd j hj
              rw [h_ch] at h; simp at h; grind
          · intro j hj
            obtain ⟨sfx, h_sfx_eq, h_sfx_len, h_sfx_cont⟩ := h_sinv j hj
            by_cases heq : j = k % 16
            · subst heq
              refine ⟨sfx ++ [g], ?_, ?_, ?_⟩
              · rw [h_slot, h_sfx_eq, List.append_assoc]
              · rw [List.length_append, List.length_cons, List.length_nil,
                    h_sfx_len, h_cnt]
                grind
              · intro m hm
                rw [List.length_append, List.length_cons, List.length_nil,
                    h_sfx_len] at hm
                simp at hm
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
                    congr 1; congr 1
                    · congr 1
                      · grind
                    · grind
            · refine ⟨sfx, ?_, ?_, h_sfx_cont⟩
              · rw [h_other j heq, h_sfx_eq]
              · rw [h_sfx_len, h_cnt]; grind
        · grind
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

Validates that `msg.len()` is even and ≤ `2¹⁶ · 16`, then distributes big-endian–decoded
GF(2¹⁶) elements round-robin across 16 empty `Point` arrays via `chunks_exact(2).enumerate()`,
returning `Ok(PolyEncoder { idx: 0, s: Points(pts) })`.

**Source**: spqr/src/encoding/polynomial.rs -/

namespace spqr.encoding.polynomial.PolyEncoder

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
  simp only [hz, bind_tc_ok, alloc.vec.Vec.with_capacity]

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

Given even-length `msg` with `msg.length ≤ 2¹⁶ · 16`, returns `Ok(PolyEncoder)` with `idx = 0`
in `Points` state, where for each `j < 16`:
  • `pts[j].value.length = ⌊n/16⌋ + (1 if j < n%16)` with `n = msg.length / 2`,
  • the `k`-th coefficient of `pts[j]` equals `(256 · msg[2(j+16k)] + msg[2(j+16k)+1]).toGF216`. -/
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
    simp only [Usize.max, Usize.numBits]
    cases System.Platform.numBits_eq <;> simp_all
  case hlen =>
    simp only [show (16#usize).val = 16 from rfl, List.length_replicate]
  case hy =>
    cases System.Platform.numBits_eq <;> simp_all
  case hmax =>
    rw [i4_post, i3_post1]
    have h_pow : (1 : Nat) <<< 16 = 65536 := by
      norm_num [Nat.shiftLeft_eq]
    have h_shift : (1 <<< 16) % Usize.size = 65536 := by
      rw [h_pow]
      apply Nat.mod_eq_of_lt
      simp only [Usize.size, Usize.numBits]
      cases System.Platform.numBits_eq <;> simp_all
    rw [h_shift]
    have h_max : (65536 : Nat) * 16 ≤ Usize.max := by
      simp only [Usize.max, Usize.numBits]
      cases System.Platform.numBits_eq <;> simp_all
    omega
  · exfalso
    have h_pow : (1 : Nat) <<< 16 = 65536 := by norm_num [Nat.shiftLeft_eq]
    have h_shift : (1 <<< 16) % Usize.size = 65536 := by
      rw [h_pow]
      apply Nat.mod_eq_of_lt
      simp only [Usize.size, Usize.numBits]
      cases System.Platform.numBits_eq <;> simp_all
    have h_i5 : i5.val = 65536 * 16 := by rw [i5_post, i3_post1, i4_post, h_shift]
    have h_gt' : msg.len.val > i5.val := by scalar_tac
    have h_msglen : msg.len.val = (msg.val).length := by scalar_tac
    grind
  · have h_pts_empty : ∀ (j : Nat), j < 16 → pts.val[j]!.value.val = [] := by
      intro j hj
      rw [pts_post]
      interval_cases j <;> rfl
    have h_msglen : msg.len.val = (msg.val).length := by scalar_tac
    have h_len_bound : (msg.val).length ≤ Usize.max := by
      have h_max : (2 : Nat) ^ 16 * 16 ≤ Usize.max := by
        simp only [Usize.max, Usize.numBits]
        cases System.Platform.numBits_eq <;> simp_all
      grind
    apply WP.spec_bind (core.slice.Slice.chunks_exact_spec_with_content msg 2#usize (by decide))
    intro ce h_ce
    obtain ⟨h_ce_len, h_ce_count, h_ce_rem, h_ce_content⟩ := h_ce
    simp only [core.iter.traits.iterator.Iterator.enumerate.trait_default,
      core.iter.traits.iterator.Iterator.enumerate.default, bind_tc_ok]
    apply WP.spec_bind
      (encode_bytes_base_loop.loop_spec
        ({ iter := ce, count := 0#usize } :
          core.iter.adapters.enumerate.Enumerate (core.slice.iter.ChunksExact U8))
        pts
        (by rfl)
        (by grind)
        (by grind)
        (by
          simp only [show (0#usize : Usize).val = 0 from rfl, Nat.zero_add]
          grind))
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
        have := h_eq; simp at this; grind
      change pts1[j]!.value.val.length = _
      rw [h_val_eq, h_len_suf]
      split <;> grind
    · intro j hj k hk
      obtain ⟨suffix, h_eq, h_len_suf, h_content⟩ := h_suffix j hj
      have h_empty := h_pts_empty j hj
      have h_empty' : (pts[j]!).value.val = [] := by
        rw [Array.getElem!_Nat_eq]; exact h_empty
      have h_val_eq : pts1[j]!.value.val = suffix := by
        have := h_eq; simp  at this; grind
      have hk' : k < suffix.length := by
        have := congr_arg List.length h_val_eq
        simp_all
      obtain ⟨h_chunk_bound, h_enc⟩ := h_content k hk'
      have h_bound : 2 * (j + 16 * k) + 1 < msg.val.length := by
        have h_even' : msg.val.length % 2 = 0 := by
          have := h_even; simp only [Slice.length] at this; exact this
        grind
      refine ⟨h_bound, ?_⟩
      simp only [← List.getElem!_eq_getElem?_getD]
      simp only [Array.getElem!_Nat_eq] at h_val_eq
      simp only [h_val_eq, ← getElem!_toGF216_eq_coeff]
      rw [h_enc]
      have h_bytes := chunks_exact_content msg ce h_ce_content (j + 16 * k) h_chunk_bound
      simp only [Slice.getElem!_Nat_eq] at h_bytes ⊢
      rw [h_bytes.1, h_bytes.2]

end spqr.encoding.polynomial.PolyEncoder
