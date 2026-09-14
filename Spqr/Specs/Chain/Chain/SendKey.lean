/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Chain.Chain.EpochIdx
import Spqr.Specs.Chain.ChainEpochDirection.NextKey
import Spqr.Specs.Chain.EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH
import Spqr.Specs.Aeneas.RangeIteratorNext
import Spqr.Specs.Chain.ChainEpochDirection.ClearNext
import Spqr.Specs.Chain.Chain.Defs
/-! # Spec theorem for `spqr::chain::{spqr::chain::Chain}::send_key`: loop body 1

Body of the clearing loop `for i in 0..epoch_index { self.links[i].send.clear_next(); }`.
Each iteration either returns `done vd` (range exhausted) or clears `links[i].send.next`
via `index_mut` and `clear_next`, then continues with the advanced iterator and updated deque.

Preconditions: `iter.end ≤ vd.length` and `vd.head + vd.length ≤ vd.buf.length`.

**Source**: spqr/src/chain.rs-/

open Aeneas Aeneas.Std Result spqr crypto

namespace spqr.chain.Chain.send_key_loop1

/-- **Spec theorem for `spqr.chain.Chain.send_key_loop1.body`**:

One step of the clearing loop. **Done**: deque unchanged. **Cont**: clears `send.next` at
slot `vd.head + iter.start`, advances the iterator, preserves deque shape and loop invariant,
and the termination measure strictly decreases. -/
@[step]
theorem body_spec
    (iter : core.ops.range.Range Std.Usize)
    (vd : alloc.collections.vec_deque.VecDeque chain.ChainEpoch Global)
    (h_end_le : iter.end.val ≤ vd.length.val)
    (h_wf : vd.head.val + vd.length.val ≤ vd.buf.val.length) :
    body iter vd ⦃ cf =>
      match cf with
      | ControlFlow.done vd' =>
          vd' = vd ∧ ¬(iter.start.val < iter.end.val)
      | ControlFlow.cont (iter1, vd1) =>
          iter.start.val < iter.end.val ∧
          iter1.start.val = iter.start.val + 1 ∧
          iter1.end = iter.end ∧
          vd1.head = vd.head ∧
          vd1.length = vd.length ∧
          vd1.buf.val.length = vd.buf.val.length ∧
          (∃ ce : chain.ChainEpoch, ∃ ced : chain.ChainEpochDirection,
            vd.buf.val[vd.head.val + iter.start.val]? = some ce ∧
            vd1.buf.val = vd.buf.val.set (vd.head.val + iter.start.val) { ce with send := ced } ∧
            ced.next.length = 0 ∧
            ced.next.val = [] ∧
            ced.ctr = ce.send.ctr ∧
            ced.prev = ce.send.prev) ∧
          iter1.end.val ≤ vd1.length.val ∧
          vd1.head.val + vd1.length.val ≤ vd1.buf.val.length ∧
          iter1.end.val - iter1.start.val < iter.end.val - iter.start.val ⦄ := by
  unfold body
  obtain ⟨⟨opt, iter1⟩, hnext, h_none, h_some⟩ :=
    WP.spec_imp_exists (core.iter.range.IteratorRange.next_Usize_spec' iter)
  rw [hnext]; simp only [bind_tc_ok]
  by_cases h_lt : iter.start.val < iter.end.val
  · obtain ⟨h_opt, h_start1, h_end1⟩ := h_some h_lt
    subst h_opt
    have h_idx : iter.start.val < vd.length := by scalar_tac
    have h_phys : vd.head + iter.start < vd.buf.length := by
      simp only [alloc.vec.Vec.length]; scalar_tac
    step*
    have h_get : vd.buf.val[vd.head.val + iter.start.val]? =
        some (vd.buf.val[vd.head.val + iter.start.val]'h_phys) :=
      List.getElem?_eq_getElem h_phys
    rw [h_get] at ce_post
    obtain ⟨h_ce, h_back⟩ := ce_post
    obtain ⟨h_buf, h_head, h_len⟩ := h_back { ce with send := ced }
    refine ⟨h_lt, h_start1, h_end1, h_head, h_len, ?_, ⟨ce, ced, ?_, ?_, ced_post1, ced_post2,
      ced_post3, ced_post4⟩, ?_, ?_, ?_⟩
    · simp [h_buf]
    · simp [h_get, h_ce]
    · exact h_buf
    · simp only [h_len, h_end1]; exact h_end_le
    · simp only [h_head, h_len, h_buf, List.length_set]; exact h_wf
    · simp only [h_end1]; omega
  · obtain ⟨h_opt, h_iter⟩ := h_none h_lt
    subst h_opt
    simp [h_lt]

/-- **Spec theorem for `spqr.chain.Chain.send_key_loop1`**:

Full clearing loop. Preserves deque shape, clears visited window, leaves other slots untouched.

**Source**: spqr/src/chain.rs -/
@[step]
theorem send_key_loop1_spec
    (iter : core.ops.range.Range Std.Usize)
    (vd : alloc.collections.vec_deque.VecDeque chain.ChainEpoch Global)
    (h_end_le : iter.end.val ≤ vd.length.val)
    (h_wf : vd.head.val + vd.length.val ≤ vd.buf.val.length) :
    send_key_loop1 iter vd
      ⦃ (vd' : alloc.collections.vec_deque.VecDeque chain.ChainEpoch Global) =>
      vd'.head = vd.head ∧
      vd'.length = vd.length ∧
      vd'.buf.val.length = vd.buf.val.length ∧
      (∀ j, vd.head.val + iter.start.val ≤ j → j < vd.head.val + iter.end.val →
        clearedAt vd vd' j) ∧
      (∀ j, (j < vd.head.val + iter.start.val ∨ vd.head.val + iter.end.val ≤ j) →
        vd'.buf.val[j]? = vd.buf.val[j]?) ⦄ := by
  unfold send_key_loop1
  apply loop.spec_decr_nat
    (measure := fun (it, _) => it.end.val - it.start.val)
    (inv := fun (it, vd') =>
      it.end = iter.end ∧
      iter.start.val ≤ it.start.val ∧
      it.start.val ≤ max iter.start.val iter.end.val ∧
      vd'.head = vd.head ∧
      vd'.length = vd.length ∧
      vd'.buf.val.length = vd.buf.val.length ∧
      (∀ j, vd.head.val + iter.start.val ≤ j → j < vd.head.val + it.start.val →
        clearedAt vd vd' j) ∧
      (∀ j, (j < vd.head.val + iter.start.val ∨ vd.head.val + it.start.val ≤ j) →
        vd'.buf.val[j]? = vd.buf.val[j]?))
  · rintro ⟨it, vd'⟩ ⟨h_end, h_ge, h_le, h_hd, h_ln, h_bl, h_clr, h_same⟩
    have h_end_le' : it.end.val ≤ vd'.length.val := by rw [h_end, h_ln]; exact h_end_le
    have h_wf' : vd'.head.val + vd'.length.val ≤ vd'.buf.val.length := by
      rw [h_hd, h_ln, h_bl]; exact h_wf
    step*
    split
    · obtain ⟨h_vd, h_nlt⟩ := r_post
      subst h_vd
      have h_start : it.start.val = max iter.start.val iter.end.val := by
        rw [h_end] at h_nlt; omega
      refine ⟨h_hd, h_ln, h_bl, ?_, ?_⟩
      · intro j hj1 hj2
        exact h_clr j hj1 (by omega)
      · intro j hj
        exact h_same j (by omega)
    · rename_i x'
      obtain ⟨it1, vd1⟩ := x'
      obtain ⟨h_lt, h_start1, h_end1, h_hd1, h_ln1, h_bl1,
        ⟨ce, ced, h_ce, h_buf1, _, h_next, h_ctr, h_prev⟩, _, _, h_decr⟩ := r_post
      simp only at h_start1 h_end1 h_hd1 h_ln1 h_bl1 h_buf1 h_decr ⊢
      rw [h_hd] at h_ce h_buf1
      have h_lt' : it.start.val < iter.end.val := by rw [h_end] at h_lt; exact h_lt
      have h_phys_lt : vd.head.val + it.start.val < vd.buf.val.length := by omega
      have h_phys_lt' : vd.head.val + it.start.val < vd'.buf.val.length := by omega
      refine ⟨by rw [h_end1, h_end], by omega, by omega,
        by rw [h_hd1, h_hd], by rw [h_ln1, h_ln], by rw [h_buf1, List.length_set, h_bl],
        ?_, ?_, h_decr⟩
      · intro j hj1 hj2
        by_cases h_eq : j = vd.head.val + it.start.val
        · subst h_eq
          have h_orig := h_same _ (Or.inr le_rfl)
          rw [h_ce] at h_orig
          obtain ⟨ce0, h_ce0⟩ : ∃ ce0, vd.buf.val[vd.head.val + it.start.val]? = some ce0 :=
            ⟨_, List.getElem?_eq_getElem h_phys_lt⟩
          rw [h_ce0, Option.some.injEq] at h_orig
          refine ⟨ce0, { ce with send := ced }, h_ce0, ?_, ?_, h_next, ?_, ?_⟩
          · rw [h_buf1, List.getElem?_set_self h_phys_lt']
          · simp [h_orig]
          · simp [h_ctr, h_orig]
          · simp [h_prev, h_orig]
        · obtain ⟨ce0, ce0', h0, h0', hr, hn, hc, hp⟩ := h_clr j hj1 (by omega)
          refine ⟨ce0, ce0', h0, ?_, hr, hn, hc, hp⟩
          rw [h_buf1, List.getElem?_set_ne (Ne.symm h_eq)]
          exact h0'
      · intro j hj
        have h_ne : vd.head.val + it.start.val ≠ j := by omega
        rw [h_buf1, List.getElem?_set_ne h_ne]
        exact h_same j (by omega)
  · exact ⟨rfl, le_rfl, le_max_left _ _, rfl, rfl, rfl,
      fun j hj1 hj2 => absurd hj2 (by omega),
      fun j _ => rfl⟩

end spqr.chain.Chain.send_key_loop1

/-! # Spec theorem for `spqr::chain::{spqr::chain::Chain}::send_key`: loop body 0

Trimming loop body: pops front and decrements `epoch_index` while `epoch_index > 1`,
otherwise returns unchanged. Keeps at most `EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH` epochs
before the send epoch.

**Source**: spqr/src/chain.rs -/

namespace spqr.chain.Chain.send_key_loop0

/-- **Spec theorem for `spqr.chain.Chain.send_key_loop0.body`**:

One step of the trimming loop. **Done**: unchanged when `epoch_index ≤ 1`.
**Cont**: pops front, decrements index, preserves loop invariant, measure decreases. -/
@[step]
theorem body_spec
    (vd : alloc.collections.vec_deque.VecDeque chain.ChainEpoch Global)
    (epoch_index : Std.Usize)
    (h_head_room : vd.head.val + epoch_index.val < vd.buf.val.length)
    (h_len_ge : vd.length.val ≥ epoch_index.val + 1) :
    body vd epoch_index ⦃ cf =>
      match cf with
      | ControlFlow.done (vd', ei') =>
          vd' = vd ∧ ei' = epoch_index ∧ ¬(epoch_index > chain.EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH)
      | ControlFlow.cont (vd', ei') =>
          epoch_index > chain.EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH ∧
          vd'.head.val = vd.head + 1 ∧
          vd'.length.val = vd.length.val - 1 ∧
          vd'.buf = vd.buf ∧
          ei'.val = epoch_index.val - 1 ∧
          vd'.head.val + ei'.val < vd'.buf.val.length ∧
          vd'.length.val ≥ ei'.val + 1 ∧
          ei' > 0#usize ∧
          ei'.val < epoch_index.val ⦄ := by
  unfold body
  simp only [chain.EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH_spec]
  split
  · have h_head : vd.head < vd.buf.length := by
      simp only [alloc.vec.Vec.length]; scalar_tac
    have h_len : vd.length ≠ 0#usize := by scalar_tac
    step*
    grind
  · simp_all

/-- **Spec theorem for `spqr.chain.Chain.send_key_loop0`**:

Full trimming loop. Result: `ei' = min epoch_index EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH`,
head advances by `epoch_index - ei'`, buffer unchanged, deque stays well-formed. -/
@[step]
theorem send_key_loop0_spec
    (vd : alloc.collections.vec_deque.VecDeque chain.ChainEpoch Global)
    (epoch_index : Std.Usize)
    (h_head_room : vd.head.val + epoch_index.val < vd.buf.val.length)
    (h_len_ge : vd.length.val ≥ epoch_index.val + 1) :
    send_key_loop0 vd epoch_index ⦃ (result : _ × Std.Usize) =>
      let (vd', ei') := result
      ei'.val = min epoch_index.val chain.EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH.val ∧
      vd'.buf = vd.buf ∧
      vd'.head.val = vd.head.val + (epoch_index.val - ei'.val) ∧
      vd'.length.val = vd.length.val - (epoch_index.val - ei'.val) ∧
      vd'.length.val ≥ ei'.val + 1 ∧
      vd'.head.val + ei'.val < vd'.buf.val.length ⦄ := by
  unfold send_key_loop0
  simp only [chain.EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH_spec]
  apply loop.spec_decr_nat
    (measure := fun (_, ei) => ei.val)
    (inv := fun (vd', ei') =>
      vd'.buf = vd.buf ∧
      vd'.head.val = vd.head.val + (epoch_index.val - ei'.val) ∧
      vd'.length.val = vd.length.val - (epoch_index.val - ei'.val) ∧
      ei'.val ≤ epoch_index.val ∧
      (ei'.val = 0 → epoch_index.val = 0) ∧
      vd'.length.val ≥ ei'.val + 1 ∧
      vd'.head.val + ei'.val < vd'.buf.val.length)
  · rintro ⟨vd', ei'⟩ ⟨h_buf, h_hd, h_ln, h_le, h_zero, h_len_inv, h_head_inv⟩
    step*
    split
    · obtain ⟨h_vd, h_ei, h_le1⟩ := r_post
      simp only [chain.EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH_spec] at h_le1
      have h1 : ei'.val ≤ 1 := by scalar_tac
      simp only [h_vd, h_ei]
      refine ⟨?_, h_buf, h_hd, h_ln, h_len_inv, h_head_inv⟩
      simp only [Nat.min_def]
      split <;> scalar_tac
    · obtain ⟨h_gt, h_head_eq, h_len_eq, h_buf_eq, h_ei_eq, h_hd2, h_ln2, h_ei2, h_decr⟩ := r_post
      refine ⟨by simp_all, ?_, ?_, ?_, ?_, h_ln2, h_hd2, h_decr⟩ <;> scalar_tac
  · exact ⟨by simp, by scalar_tac, by scalar_tac, by scalar_tac, by scalar_tac,
      h_len_ge, h_head_room⟩

end spqr.chain.Chain.send_key_loop0

/-! # Spec theorem for `spqr::chain::{spqr::chain::Chain}::send_key`

Derives the next sending key for a given `Epoch`. Three outcomes:
1. `epoch < send_epoch` → `Err SendKeyEpochDecreased`, `self` unchanged.
2. `epoch_idx` fails → `Err EpochOutOfRange`, `self` unchanged.
3. Success: trims old epochs (loop0), clears send secrets (loop1), then calls `next_key`
   on the target slot `phys = head + idx`. The derived key depends only on the original
   element at `phys`: `i = ce.send.ctr + 1`, `key = (nextKeyHkdfOutput ce.send.next i).drop 32`.

Preconditions are guarded by the path on which they are consumed (error paths need nothing).

**Source**: spqr/src/chain.rs -/

namespace spqr.chain.Chain

/-- **Spec theorem for `spqr.chain.Chain.send_key`**:

• **`SendKeyEpochDecreased`** (`epoch < self.send_epoch`): returns
  `Err (Error.SendKeyEpochDecreased self.send_epoch epoch)` and `self` unchanged.
• **`EpochOutOfRange`** (`epoch > current_epoch` or `current_epoch - epoch ≥ links.len()`):
  returns `Err (Error.EpochOutOfRange epoch)` and `self` unchanged.
• **Success**: returns `Ok (i, key)` and an updated chain `self'`.  Writing
  `idx = sendKeyIdx self epoch`, `ei = sendKeyEi self epoch`, `phys = self.links.head + idx`
  and `ce = self.links.buf[phys]` (which exists):
    - `i = ce.send.ctr + 1`, `key.length = 32` and
      `key = (nextKeyHkdfOutput ce.send.next i).drop 32`.
    - `self'.send_epoch = epoch`; `dir`, `current_epoch`, `next_root`, `params` are unchanged.
    - Deque shape: `self'.links.head = head + (idx - ei)`,
      `self'.links.length = length - (idx - ei)`, `buf.length` unchanged, and the deque stays
      well-formed with `ei < self'.links.length`.
    - The advanced slot: `self'.links.buf[phys] = { ce with send := ced }` where
      `ced.ctr = i`, `ced.next = (nextKeyHkdfOutput ce.send.next i).take 32`,
      `ced.next.length = ce.send.next.length` and the key history `ced.prev = ce.send.prev`
      is untouched (`recv` is untouched as well, since only `send` is replaced).
    - If the send epoch moved, every slot in `[head + (idx - ei), phys)` is cleared
      (`send_key_loop1.clearedAt self.links self'.links j`).
    - Every slot outside `[head + (idx - ei), phys]` is untouched.

**Source**: spqr/src/chain.rs, lines 384:4-407:5
-/
@[step]
theorem send_key_spec (self : chain.Chain) (epoch : U64)
    (h_diff_fits : self.send_epoch ≤ epoch.val → epoch.val ≤ self.current_epoch →
      self.current_epoch - epoch ≤ Usize.max)
    (h_wf : self.links.head + self.links.length ≤ self.links.buf.val.length)
    (h_target : self.send_epoch ≤ epoch → epoch ≤ self.current_epoch →
      self.current_epoch - epoch < self.links.length.val →
      match self.links.buf.val[self.links.head + sendKeyIdx self epoch]? with
      | none => True
      | some ce => ce.send.next.length = 32 ∧ ce.send.ctr < U32.max) :
    send_key self epoch ⦃ (result : (core.result.Result (U32 × alloc.vec.Vec U8) Error) ×
        chain.Chain) =>
      match result.1 with
      | core.result.Result.Err e =>
          result.2 = self ∧
          ((e = Error.SendKeyEpochDecreased self.send_epoch epoch ∧
              epoch < self.send_epoch) ∨
           (e = Error.EpochOutOfRange epoch ∧ self.send_epoch.val ≤ epoch.val ∧
              (epoch > self.current_epoch ∨
               self.current_epoch - epoch ≥ self.links.length.val)))
      | core.result.Result.Ok (i, key) =>
          let idx := sendKeyIdx self epoch
          let ei := sendKeyEi self epoch
          let phys := self.links.head + idx
          self.send_epoch ≤ epoch ∧
          epoch ≤ self.current_epoch ∧
          self.current_epoch - epoch < self.links.length.val ∧
          match self.links.buf.val[phys]? with
          | none => False
          | some ce =>
            i.val = ce.send.ctr + 1 ∧
            key.length = 32 ∧
            key = (nextKeyHkdfOutput ce.send.next i).drop 32 ∧
            result.2.dir = self.dir ∧
            result.2.current_epoch = self.current_epoch ∧
            result.2.send_epoch = epoch ∧
            result.2.next_root = self.next_root ∧
            result.2.params = self.params ∧
            result.2.links.head = self.links.head + (idx - ei) ∧
            result.2.links.length = self.links.length - (idx - ei) ∧
            result.2.links.buf.val.length = self.links.buf.val.length ∧
            result.2.links.head + result.2.links.length ≤ result.2.links.buf.val.length ∧
            ei < result.2.links.length ∧
            (match result.2.links.buf.val[phys]? with
             | none => False
             | some ce' =>
                 ce'.recv = ce.recv ∧
                 ce'.send.ctr = i ∧
                 ce'.send.next.length = ce.send.next.length ∧
                 ce'.send.next = (nextKeyHkdfOutput ce.send.next i).take 32 ∧
                 ce'.send.prev = ce.send.prev) ∧
            (self.send_epoch ≠ epoch →
              ∀ j, self.links.head + (idx - ei) ≤ j → j < phys →
                clearedAt self.links result.2.links j) ∧
            (∀ j, (j < self.links.head.val + (idx - ei) ∨ phys < j) →
              result.2.links.buf.val[j]? = self.links.buf.val[j]?) ⦄ := by
  unfold send_key
  split
  · simp only [WP.spec_ok]
    exact ⟨trivial, Or.inl ⟨trivial, by scalar_tac⟩⟩
  · rename_i h_nlt
    have h_ge : self.send_epoch.val ≤ epoch.val := by scalar_tac
    step (h_diff_fits := h_diff_fits h_ge)
    simp only [r_post1]
    rcases r with idx | e
    · obtain ⟨h_le, h_back, h_idx⟩ := r_post2
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok, bne_iff_ne, ne_eq,
        ite_not]
      have h_idx_lt : idx.val < self.links.length.val := by omega
      have h_phys_lt : self.links.head.val + idx.val < self.links.buf.val.length := by omega
      obtain ⟨ce, h_ce⟩ : ∃ ce, self.links.buf.val[self.links.head.val + idx.val]? = some ce :=
        ⟨_, List.getElem?_eq_getElem h_phys_lt⟩
      have h_idx' : sendKeyIdx self epoch = idx.val := by simp only [sendKeyIdx, h_idx]
      have h_target' := h_target h_ge h_le h_back
      rw [h_idx', h_ce] at h_target'
      obtain ⟨h_next32, h_ctr⟩ := h_target'
      split
      · rename_i h_eq_ep
        have h_ei : sendKeyEi self epoch = idx.val := by
          simp only [sendKeyEi, if_pos h_eq_ep, h_idx']
        step*
        rw [h_ce] at ce_post
        obtain ⟨h_ce_eq, h_back_fn⟩ := ce_post
        subst h_ce_eq
        obtain ⟨h_buf2, h_hd2, h_ln2⟩ := h_back_fn { ce with send := ced }
        have h_p1 : p.1 = (⟨ce.send.ctr.val + 1, by scalar_tac⟩ : U32) :=
          UScalar.eq_of_val_eq p_post1
        have h64 : (nextKeyHkdfOutput ce.send.next p.1).length = 64 := by
          simp [nextKeyHkdfOutput, crypto.hkdf_length]
        simp only [h_idx', h_ei, Nat.sub_self, Nat.add_zero, Nat.sub_zero]
        simp only [h_ce]
        refine ⟨h_ge, h_le, h_back, p_post1, ?_, ?_, h_eq_ep, by rw [h_hd2],
          by rw [h_ln2], ?_, ?_, ?_, ?_, fun h => absurd h_eq_ep h, ?_⟩
        · simp only [alloc.vec.Vec.length, ← h_p1] at p_post6 ⊢
          rw [p_post6, List.length_drop, h64]
        · rw [p_post6, h_p1]
        · simp only [h_buf2, List.length_set]
        · simp only [h_buf2, List.length_set, h_hd2, h_ln2]; exact h_wf
        · rw [h_ln2]; exact h_idx_lt
        · simp only [h_buf2, List.getElem?_set_self h_phys_lt]
          exact ⟨trivial, UScalar.eq_of_val_eq (by rw [p_post2, p_post1]),
            p_post3, by rw [p_post4, h_p1], p_post5⟩
        · intro j hj
          rw [h_buf2, List.getElem?_set_ne (by omega)]
      · rename_i h_ne
        have h_ei : sendKeyEi self epoch = min idx.val 1 := by
          rw [sendKeyEi, if_neg h_ne, h_idx', chain.EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH_spec]
          rfl
        obtain ⟨⟨vd, ei⟩, h_l0, h_ei_val, h_buf0, h_hd0, h_ln0, h_len_ge0, h_room0⟩ :=
          WP.spec_imp_exists (send_key_loop0.send_key_loop0_spec self.links idx h_phys_lt
            (by omega))
        simp only [EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH_spec, UScalar.ofNatCore_val_eq] at h_ei_val
        simp only [h_l0, bind_tc_ok]
        have h_wf0 : vd.head.val + vd.length.val ≤ vd.buf.val.length := by
          rw [h_buf0]; omega
        obtain ⟨vd1, h_l1, h_hd1, h_ln1, h_bl1, h_clr1, h_same1⟩ :=
          WP.spec_imp_exists (send_key_loop1.send_key_loop1_spec ⟨0#usize, ei⟩ vd
            (by simp only; omega) h_wf0)
        simp only at h_hd1 h_ln1 h_bl1 h_clr1 h_same1
        have h_zero : (0#usize).val = 0 := rfl
        change (do
          let vd1 ← send_key_loop1 { start := 0#usize, «end» := ei } vd
          let (ce, index_mut_back) ←
            alloc.collections.vec_deque.VecDeque.Insts.CoreOpsIndexIndexMutUsizeT.index_mut vd1 ei
          let (p, ced) ← chain.ChainEpochDirection.next_key ce.send
          ok (core.result.Result.Ok p,
            { self with send_epoch := epoch, links := index_mut_back { ce with send := ced } }))
            ⦃ _ ⦄
        rw [h_l1]; simp only [bind_tc_ok]
        have h_phys_eq : vd1.head.val + ei.val = self.links.head.val + idx.val := by
          rw [h_hd1, h_hd0]; omega
        have h_ce1 : vd1.buf.val[vd1.head.val + ei.val]? = some ce := by
          rw [h_same1 _ (Or.inr (by omega)), h_buf0, h_phys_eq]; exact h_ce
        have h_ei_lt1 : ei.val < vd1.length.val := by rw [h_ln1]; omega
        have h_phys_lt1 : vd1.head + ei < vd1.buf.length := by
          simp only [alloc.vec.Vec.length]; rw [h_bl1, h_buf0, h_phys_eq]; exact h_phys_lt
        step*
        rw [h_ce1] at ce_post
        obtain ⟨h_ce_eq, h_back_fn⟩ := ce_post
        subst h_ce_eq
        obtain ⟨h_buf2, h_hd2, h_ln2⟩ := h_back_fn { ce with send := ced }
        have h_p1 : p.1 = (⟨ce.send.ctr.val + 1, by scalar_tac⟩ : U32) :=
          UScalar.eq_of_val_eq p_post1
        have h64 : (nextKeyHkdfOutput ce.send.next p.1).length = 64 := by
          simp [nextKeyHkdfOutput, crypto.hkdf_length]
        have h_phys_lt1' : vd1.head.val + ei.val < vd1.buf.val.length := by
          simpa [alloc.vec.Vec.length] using h_phys_lt1
        simp only [h_idx', h_ei, h_ce]
        refine ⟨h_ge, h_le, h_back, p_post1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_⟩
        · simp only [alloc.vec.Vec.length, ← h_p1] at p_post6 ⊢
          rw [p_post6, List.length_drop, h64]
        · rw [p_post6, h_p1]
        · simp only [h_hd2, h_hd1, h_hd0]; omega
        · simp only [h_ln2, h_ln1, h_ln0]; omega
        · simp only [h_buf2, List.length_set, h_bl1, h_buf0]
        · simp only [h_buf2, List.length_set, h_hd2, h_ln2, h_bl1, h_hd1, h_ln1]; exact h_wf0
        · simp only [h_ln2, h_ln1, h_ln0]; omega
        · simp only [h_buf2, ← h_phys_eq, List.getElem?_set_self h_phys_lt1']
          exact ⟨trivial, UScalar.eq_of_val_eq (by rw [p_post2, p_post1]),
            p_post3, by rw [p_post4, h_p1], p_post5⟩
        · intro _ j hj1 hj2
          have hj1' : vd.head.val + (0#usize).val ≤ j := by rw [h_hd0, h_zero]; omega
          have hj2' : j < vd.head.val + ei.val := by rw [h_hd0]; omega
          obtain ⟨ce0, ce0', h0, h0', hr, hn, hc, hp⟩ := h_clr1 j hj1' hj2'
          refine ⟨ce0, ce0', by rw [← h_buf0]; exact h0, ?_, hr, hn, hc, hp⟩
          rw [h_buf2, List.getElem?_set_ne (by omega)]; exact h0'
        · intro j hj
          rw [h_buf2, List.getElem?_set_ne (by omega), h_same1 j (by rw [h_hd0, h_zero]; omega),
            h_buf0]
    · obtain ⟨h_e, h_bad⟩ := r_post2
      simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
      exact ⟨trivial, Or.inr ⟨h_e, h_ge, h_bad⟩⟩

end spqr.chain.Chain
