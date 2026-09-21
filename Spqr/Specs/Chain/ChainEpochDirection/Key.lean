/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Chain.ChainEpochDirection.NextKey
import Spqr.Specs.Chain.KeyHistory.Get
import Spqr.Specs.Chain.KeyHistory.Clear
import Spqr.Specs.Chain.KeyHistory.Gc
import Spqr.Specs.Chain.ChainParams.MaxJumpOrDefault
import Spqr.Specs.Chain.Chain.Defs
import Spqr.Specs.Chain.KeyHistory.Add
/-!
# Spec theorem for `spqr::chain::{spqr::chain::ChainEpochDirection}::key`: loop body 0

The main advancing loop body of `ChainEpochDirection::key`.  At each iteration the loop
checks whether the requested counter `at1` is still more than one step ahead of the current
counter `i`:

  1. It computes `i1 = i + 1`.  If `at1 > i1` (i.e. `at1 > i + 1`) the current chain secret
     has not yet reached the target, so the body:
       a. Mutably borrows `v` (the chain secret vector) and calls `next_key_internal` to
          derive the next 64-byte HKDF output, splitting it into a new chain secret
          (first 32 bytes, written back into `v`) and a 32-byte derived key `k`.
       b. Checks whether `i2 + max_ooo_keys_or_default(params) >= at1`.  If so, the key `k`
          is added to the key history `kh` via `KeyHistory::add`; otherwise it is discarded
          (since the key would be immediately garbage-collected).
       c. Returns `cont (i2, v', kh')` to continue looping.
  2. If `at1 ≤ i + 1` the counter has caught up and the body returns `done (i, v, kh)`.

The preconditions require that the chain secret `v` has length 32 and the counter `i` is
below `U32.max` (so that incrementing it does not overflow).

**Source**: spqr/src/chain.rs -/

open Aeneas Aeneas.Std Result spqr crypto

namespace spqr.chain.ChainEpochDirection.key_loop

/-- **Spec theorem for `spqr.chain.ChainEpochDirection.key_loop.body`**:

One step of the chain-key advancement loop.

- **Done case** (`at1 ≤ i + 1`): the body returns `done (i, v, kh)` with the counter, chain
  secret, and key history all unchanged.
- **Cont case** (`at1 > i + 1`): `next_key_internal` is called, producing an incremented
  counter `i2 = i + 1` and a new HKDF output `okm = nextKeyHkdfOutput v.val (i+1)`.
  The new chain secret satisfies `v2.length = 32` and `v2.val = okm.take 32`.
  The derived key is `k.2.val = okm.drop 32`.
    • If `i2 + max_ooo_keys_or_default(params) ≥ at1`, the key `k` is added to the history:
      `kh2.data.length = kh.data.length + 36` and
      `kh2.data = kh.data ++ to_be_bytes(k.1) ++ k.2`.
    • Otherwise the history is unchanged: `kh2 = kh`.
  In both sub-cases the counter advances: `i2.val = i.val + 1`. -/
@[step]
theorem body_spec
    (at1 : U32) (params : proto.pq_ratchet.ChainParams)
    (i : U32) (v : alloc.vec.Vec U8) (kh : chain.KeyHistory)
    (h_v_len : v.length = 32)
    (h_i : i < U32.max)
    (h_kh_cap : kh.data.length + 36 ≤ Usize.max)
    (h_ctr_bound : i.val + 1 ≤ U32.max - 390451572)
    (h_maxooo_bound : (chain.maxOoo params).val < 390451572) :
    body at1 params i v kh ⦃ cf =>
      match cf with
      | ControlFlow.done (i', v', kh') =>
          i' = i ∧ v' = v ∧ kh' = kh ∧ ¬(at1.val > i.val + 1)
      | ControlFlow.cont (i2, v2, kh2) =>
          at1.val > i.val + 1 ∧
          i2.val = i.val + 1 ∧
          v2.length = 32 ∧
          (let okm := nextKeyHkdfOutput v.val (⟨i.val + 1, by scalar_tac⟩ : U32)
           v2.val = okm.take 32) ∧
          -- Key history: added when i2 + maxOoo(params) ≥ at1, discarded otherwise
          (let ctr1 : U32 := ⟨i.val + 1, by scalar_tac⟩
           let okm := nextKeyHkdfOutput v.val ctr1
           if (i.val + 1) + (chain.maxOoo params).val ≥ at1.val then
              kh2.data.length = kh.data.length + 36 ∧
              kh2.data = kh.data ++ (core.num.U32.to_be_bytes ctr1).val ++ okm.drop 32
           else
            kh2 = kh) ⦄ := by
  unfold body chain.ChainParams.max_ooo_keys_or_default
  simp only [alloc.vec.Vec.deref_mut, alloc.vec.Vec.length, lift, bind_tc_ok] at *
  step*
  split
  · step*
    · simp only [maxOoo] at h_maxooo_bound
      split_ifs at h_maxooo_bound
      · scalar_tac
      · have := DEFAULT_CHAIN_PARAMS_spec.2; scalar_tac
    · simp only [Slice.length] at *
      refine ⟨by scalar_tac, by scalar_tac, by scalar_tac, k_post5, ?_⟩
      simp only [maxOoo]
      split
      · split
        · constructor
          · simp_all [UScalar.eq_equiv]
          · have hi2 : i2 = (⟨i.val + 1, by scalar_tac⟩ : U32) :=
                UScalar.val_eq_imp _ _ k_post1
            simp_all [List.append_assoc]
        · simp_all [UScalar.eq_equiv]
      · split
        · constructor
          · simp_all [UScalar.eq_equiv]
          · have hi2 : i2 = (⟨i.val + 1, by scalar_tac⟩ : U32) :=
                UScalar.val_eq_imp _ _ k_post1
            simp_all [List.append_assoc]
        · simp_all [UScalar.eq_equiv]
    · simp only [Slice.length] at *
      refine ⟨by scalar_tac, by scalar_tac, by scalar_tac, k_post5, ?_⟩
      simp only [maxOoo]
      split
      · split
        · constructor
          · simp_all [UScalar.eq_equiv]
          · have hi2 : i2 = (⟨i.val + 1, by scalar_tac⟩ : U32) :=
                UScalar.val_eq_imp _ _ k_post1
            simp_all only [gt_iff_lt, UScalar.lt_equiv, UScalarTy.U32_numBits_eq, Nat.reducePow,
              List.length_take, inf_eq_left, UScalar.ofNatCore_val_eq, List.append_assoc,
              List.self_eq_append_right, List.append_eq_nil_iff, List.drop_eq_nil_iff]
            scalar_tac
        · simp_all [UScalar.eq_equiv]
      · split
        · constructor
          · simp_all [UScalar.eq_equiv]
          · have hi2 : i2 = (⟨i.val + 1, by scalar_tac⟩ : U32) :=
                UScalar.val_eq_imp _ _ k_post1
            simp_all
        · simp_all [UScalar.eq_equiv]
  · step*
    · have := DEFAULT_CHAIN_PARAMS_spec.2; scalar_tac
    · simp_all only [gt_iff_lt, UScalar.lt_equiv, Nat.add_left_cancel_iff, UScalar.eq_equiv,
      Slice.length, UScalarTy.U32_numBits_eq, Nat.reducePow, List.length_take, inf_eq_left,
      UScalar.ofNatCore_val_eq, not_lt, nonpos_iff_eq_zero, ge_iff_le, UScalar.le_equiv,
      alloc.vec.Vec.length, List.append_assoc, List.length_append, List.Vector.length_val,
      List.length_drop, alloc.vec.Vec.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, getElem!_pos,
      inf_of_le_left, List.append_cancel_left_eq, List.append_cancel_right_eq, true_and]
      split
      · simp_all only [maxOoo, gt_iff_lt, UScalar.lt_equiv, UScalar.ofNatCore_val_eq,
        lt_self_iff_false, ↓reduceIte, DEFAULT_CHAIN_PARAMS, Nat.reduceLT]
        have hk1 : k.1 = (⟨i.val + 1, by scalar_tac⟩ : U32) :=
          UScalar.eq_imp _ _ k_post3
        rw [hk1]
      · simp_all [chain.maxOoo,  chain.DEFAULT_CHAIN_PARAMS]
    · simp only [maxOoo]
      simp_all [UScalar.eq_equiv]

end spqr.chain.ChainEpochDirection.key_loop

/-! # Spec theorem for `spqr::chain::{spqr::chain::ChainEpochDirection}::key`: loop 0

The full loop spec for the chain-key advancement loop of `ChainEpochDirection::key`.  The loop
iterates from counter `i` up to `at - 1`, repeatedly calling `next_key_internal` to derive the
next chain secret and (conditionally) recording derived keys in the key history.

The loop uses the `loop` fixed-point combinator.  We prove the spec by applying
`loop.spec_decr_nat` with:

  - **Measure**: `at.val - i.val` (strictly decreasing at each iteration since the counter
    advances by 1).
  - **Invariant**: the chain-secret vector has length 32, the counter stays below `U32.max`,
    the key-history capacity bound is maintained, and the counter–maxOoo arithmetic stays
    in range.

On termination the loop returns `(i_final, v_final, kh_final)` where `i_final` is the last
counter value at which `at ≤ i_final + 1` (i.e. `i_final + 1 ≥ at`), `v_final` has length 32,
and `kh_final` is the accumulated key history.

## Properties

1. **Exact counter value**: the final counter satisfies `i_f.val + 1 = max at1.val (i.val + 1)`,
   i.e. `i_f = at1 - 1` when the loop executes and `i_f = i` when it does not.
2. **Chain secret length**: `v_f.length = 32`.
3. **Chain secret value**: the final chain secret equals `iterChainSecret v.val i.val steps`
   where `steps = at1.val - (i.val + 1)` (clamped to 0).  This captures the functional
   correctness of iterated HKDF derivation.
4. **Key history content**: the final key history equals
   `iterKeyHistory v.val i.val at1.val params kh steps`, i.e. exactly the keys that
   `next_key_internal` derived during the loop, selectively recorded based on the
   `maxOoo` proximity check.
5. **Key history bounds**: the key history can only grow, and grows by at most 36 bytes per
   iteration: `kh.data.length ≤ kh_f.data.length ≤ kh.data.length + 36 * (at1.val - i.val)`.
6. **Zero-iteration identity**: when `at1.val ≤ i.val + 1` the state is returned unchanged:
   `i_f = i ∧ v_f = v ∧ kh_f = kh`.

**Source**: spqr/src/chain.rs, lines 270:8-286:9 -/


namespace spqr.chain.ChainEpochDirection

@[step]
theorem key_loop_spec
    (at1 : U32) (params : proto.pq_ratchet.ChainParams)
    (i : U32) (v : alloc.vec.Vec U8) (kh : chain.KeyHistory)
    (h_v_len : v.length = 32)
    (h_at_bound : at1.val ≤ U32.max - 390451572)
    (h_maxooo_bound : (chain.maxOoo params).val < 390451572)
    (h_kh_cap : kh.data.length + 36 * (at1.val - i.val) ≤ Usize.max)
    (h_i_bound : i.val < U32.max) :
    key_loop i v kh at1 params ⦃ (result : U32 × (alloc.vec.Vec U8) × chain.KeyHistory) =>
      let steps := at1.val - (i.val + 1)
      result.1.val + 1 = Nat.max at1.val (i.val + 1) ∧
      result.2.1.length = 32 ∧
      result.2.1.val = iterChainSecret v.val i.val steps ∧
      result.2.2 = iterKeyHistory v.val i.val at1.val params kh steps ∧
      kh.data.length ≤ result.2.2.data.length ∧
      result.2.2.data.length ≤ kh.data.length + 36 * (at1.val - i.val) ∧
      (at1.val ≤ i.val + 1 → result.1 = i ∧ result.2.1 = v ∧ result.2.2 = kh) ⦄ := by
  unfold key_loop
  apply loop.spec_decr_nat
    (measure := fun (s : U32 × (alloc.vec.Vec U8) × chain.KeyHistory) => at1.val - s.1.val)
    (inv := fun (s : U32 × (alloc.vec.Vec U8) × chain.KeyHistory) =>
      let steps := s.1.val - i.val
      s.2.1.length = 32 ∧
      i.val ≤ s.1.val ∧
      s.1.val < U32.max ∧
      at1.val ≤ U32.max - 390451572 ∧
      (chain.maxOoo params).val < 390451572 ∧
      s.2.2.data.length + 36 * (at1.val - s.1.val) ≤ Usize.max ∧
      kh.data.length ≤ s.2.2.data.length ∧
      s.2.2.data.length ≤ kh.data.length + 36 * (s.1.val - i.val) ∧
      s.2.1.val = iterChainSecret v.val i.val steps ∧
      s.2.2 = iterKeyHistory v.val i.val at1.val params kh steps ∧
      (at1.val > i.val + 1 → s.1.val + 1 ≤ at1.val) ∧
      (at1.val ≤ i.val + 1 → s.1 = i ∧ s.2.1 = v ∧ s.2.2 = kh))
  · intro ⟨i', v', kh'⟩ hinv
    simp only  at hinv
    obtain ⟨h_inv_v, h_inv_i_le, h_inv_i_lt, h_inv_at, h_inv_maxooo,
      h_inv_kh_cap, h_inv_kh_lb, h_inv_kh_ub, h_inv_secret, h_inv_kh_content,
      h_inv_ctr, h_inv_zero⟩ := hinv
    by_cases h_continue : at1.val > i'.val + 1
    · have h_kh'_cap : kh'.data.length + 36 ≤ Usize.max := by
        have : 36 * 1 ≤ 36 * (at1.val - i'.val) := Nat.mul_le_mul_left 36 (by omega)
        omega
      have hspec := key_loop.body_spec at1 params i' v' kh' h_inv_v
          h_inv_i_lt h_kh'_cap (by omega) h_inv_maxooo
      apply WP.spec_mono hspec
      intro cf hcf
      rcases cf with ⟨i'', v'', kh''⟩ | ⟨i'', v'', kh''⟩
      · simp only at hcf ⊢
        obtain ⟨_, he, hvl, hvv, hks⟩ := hcf
        have hstep : i''.val - i.val = (i'.val - i.val) + 1 := by omega
        have h_cs : v''.val = iterChainSecret v.val i.val (i''.val - i.val) := by
          rw [hstep, iterChainSecret]
          simp only [show i.val + (i'.val - i.val) + 1 ≤ U32.max from by omega, ↓reduceDIte]
          convert hvv using 2; ext; simp_all
        have h_ctr_eq : (⟨i.val + (i'.val - i.val) + 1, by scalar_tac⟩ : U32) =
            (⟨i'.val + 1, by scalar_tac⟩ : U32) := by
              have : i.val + (i'.val - i.val) + 1 = i'.val + 1 := by omega
              congr 1; ext; simp_all
        split_ifs at hks with ha
        · obtain ⟨hl, hdata⟩ := hks
          have h_kh_s : kh'' = iterKeyHistory v.val i.val at1.val params kh (i''.val - i.val) := by
            rw [hstep, iterKeyHistory, iterKeyHistoryData]
            simp only [show i.val + (i'.val - i.val) + 1 ≤ U32.max from by omega, ↓reduceDIte]
            simp only [h_ctr_eq]
            rw [h_inv_kh_content] at hdata hl
            simp only [iterKeyHistory] at hdata hl
            split at hdata
            · simp only [] at hdata hl
              rw [← h_inv_secret]
              simp only [show i.val + (i'.val - i.val) + 1 = i'.val + 1 from by omega]
              simp only [ha, ↓reduceIte]
              split
              · rename_i h_len
                cases kh'' with | mk d' =>
                  simp only [chain.KeyHistory.mk.injEq]
                  exact Subtype.ext hdata
              · rename_i h_neg; exfalso; apply h_neg
                rename_i h_prev_len
                simp only [List.length_append] at h_neg ⊢
                have h_kh'_cap := h_inv_kh_cap
                rw [h_inv_kh_content] at h_kh'_cap
                simp only [iterKeyHistory, alloc.vec.Vec.length,
                  h_prev_len, ↓reduceDIte] at h_kh'_cap
                simp_all; omega
            · rename_i h_notfit
              exfalso
              apply h_notfit
              have hb := iterKeyHistoryData_length_le v.val i.val at1.val params
                kh.data.val (i'.val - i.val)
              have hle : 36 * (i'.val - i.val) ≤ 36 * (at1.val - i.val) :=
                Nat.mul_le_mul_left 36 (by omega)
              have hcap := h_kh_cap
              simp only [alloc.vec.Vec.length] at hcap
              omega
          exact ⟨⟨hvl, by omega, by omega, h_inv_at, h_inv_maxooo,
            by rw [hl]; omega, by omega, by rw [hl]; omega,
            h_cs, h_kh_s, fun _ => by omega, fun h => absurd h (by omega)⟩, by omega⟩
        · have h_kh_s : kh'' = iterKeyHistory v.val i.val at1.val params kh (i''.val - i.val) := by
            rw [hstep, iterKeyHistory, iterKeyHistoryData]
            simp only [show i.val + (i'.val - i.val) + 1 ≤ U32.max from by omega, ↓reduceDIte]
            simp only [h_ctr_eq]
            rw [← h_inv_secret]
            simp only [show i.val + (i'.val - i.val) + 1 = i'.val + 1 from by omega]
            simp only [ha, ↓reduceIte]
            rw [hks, h_inv_kh_content, iterKeyHistory]
          refine ⟨⟨hvl, by omega, by omega, h_inv_at, h_inv_maxooo, ?_, ?_, ?_,
            h_cs, h_kh_s, fun _ => by omega, fun h => absurd h (by omega)⟩, by omega⟩
          · rw [hks]
            have := Nat.mul_le_mul_left 36 (show at1.val - i''.val ≤ at1.val - i'.val from by omega)
            omega
          · rw [hks]; exact h_inv_kh_lb
          · rw [hks]; omega
      · simp only  at hcf
        exact absurd h_continue hcf.2.2.2
    · push Not at h_continue
      have h_i_le : i.val ≤ i'.val := h_inv_i_le
      have h_le : at1.val ≤ i'.val + 1 := h_continue
      have key1 : i'.val + 1 = Nat.max at1.val (i.val + 1) := by
        by_cases hc : at1.val ≤ i.val + 1
        · have hz := h_inv_zero hc
          have hi : i'.val = i.val := UScalar.val_eq_of_eq hz.1
          simp only [hi, Nat.max_eq_right (by omega : at1.val ≤ i.val + 1)]
        · have := h_inv_ctr (by omega)
          simp only [Nat.max_eq_left (by omega : i.val + 1 ≤ at1.val)]; omega
      have key2 : i'.val - i.val = at1.val - (i.val + 1) := by
        by_cases hc : at1.val ≤ i.val + 1
        · have hz := h_inv_zero hc
          have hi : i'.val = i.val := UScalar.val_eq_of_eq hz.1
          omega
        · have := h_inv_ctr (by omega)
          omega
      unfold key_loop.body chain.ChainParams.max_ooo_keys_or_default
      simp only [alloc.vec.Vec.deref_mut, alloc.vec.Vec.length, lift, bind_tc_ok] at *
      have h_i1_ok : i'.val + 1 ≤ U32.max := by omega
      simp only [gt_iff_lt, UScalar.lt_equiv]
      step*
  · exact ⟨h_v_len, Nat.le_refl _, h_i_bound, h_at_bound, h_maxooo_bound, h_kh_cap,
      Nat.le_refl _, by simp, by simp [iterChainSecret],
      by simp [iterKeyHistory, iterKeyHistoryData],
      fun h => by scalar_tac, fun _ => ⟨rfl, rfl, rfl⟩⟩

theorem maxOoo_if_eq (params : proto.pq_ratchet.ChainParams) :
    (if 0#u32 < params.max_ooo_keys then params.max_ooo_keys.val else 2000) =
    (chain.maxOoo params).val := by
  unfold chain.maxOoo; split <;> simp_all [DEFAULT_CHAIN_PARAMS_spec]

/-- GC precondition for the no-clear branch: `maxOoo ≤ i4` when the trim threshold is hit.

In the no-clear branch we have `ats ≤ self.ctr + maxOoo` (the OOO window still covers
`self.prev`).  Together with the key-history well-formedness invariant
`self.prev.data.length ≤ 36 * self.ctr.val` (a stored key exists only for a counter value that
has already been derived), this bounds the pre-GC history length by `36 * (ats - 1)`, which in
turn forces `maxOoo ≤ ats - 1 = i4` whenever the trim threshold is reached. -/
theorem key_gc_precond_no_clear
    (self : chain.ChainEpochDirection) (ats : U32)
    (params : proto.pq_ratchet.ChainParams)
    (i4 : U32) (kh1 : chain.KeyHistory)
    (h_gt : self.ctr.val < ats.val)
    (h_prev_ctr : self.prev.data.length ≤ 36 * self.ctr.val)
    (h_i4 : i4.val + 1 = Nat.max ats.val (self.ctr.val + 1))
    (h_ub : kh1.data.length ≤ self.prev.data.length + 36 * (ats.val - self.ctr.val)) :
    let m := if 0#u32 < params.max_ooo_keys then params.max_ooo_keys.val else 2000
    (m * 11 / 10 + 1) * 36 ≤ kh1.data.length → m ≤ i4.val := by
  intro m h_trim
  have hm : m = (chain.maxOoo params).val := maxOoo_if_eq params
  have hmax : Nat.max ats.val (self.ctr.val + 1) = ats.val := Nat.max_eq_left (by omega)
  rw [hmax] at h_i4
  have hg : m ≤ m * 11 / 10 := by omega
  omega

/-- Bridge lemma for `max_jump_or_default`: from the two biconditional postconditions produced by
`max_jump_or_default_spec` (a value `v` that equals `params.max_jump` iff the field is positive, and
equals the default iff the field is zero or already the default), conclude that `v` equals the pure
`chain.maxJump params`. -/
theorem maxJump_val_eq_of_posts
    (params : proto.pq_ratchet.ChainParams) (v : U32)
    (hpos : v = params.max_jump ↔ params.max_jump > 0#u32)
    (hdef : v = chain.DEFAULT_CHAIN_PARAMS.max_jump ↔
      params.max_jump = 0#u32 ∨ params.max_jump = chain.DEFAULT_CHAIN_PARAMS.max_jump) :
    v.val = (chain.maxJump params).val := by
  unfold chain.maxJump
  by_cases h : params.max_jump > 0#u32
  · have := hpos.mpr h; simp [h, this]
  · simp only [gt_iff_lt, not_lt] at h
    have hz : params.max_jump = 0#u32 := by scalar_tac
    have := hdef.mpr (Or.inl hz)
    simp [hz, this]

/-- Bridge lemma for `max_ooo_keys_or_default`: analogous to `maxJump_val_eq_of_posts`, converting
the two biconditional postconditions of `max_ooo_keys_or_default_spec` into the pure
`chain.maxOoo params`. -/
theorem maxOoo_val_eq_of_posts
    (params : proto.pq_ratchet.ChainParams) (v : U32)
    (hpos : v = params.max_ooo_keys ↔ params.max_ooo_keys > 0#u32)
    (hdef : v = chain.DEFAULT_CHAIN_PARAMS.max_ooo_keys ↔
      params.max_ooo_keys = 0#u32 ∨ params.max_ooo_keys = chain.DEFAULT_CHAIN_PARAMS.max_ooo_keys) :
    v.val = (chain.maxOoo params).val := by
  unfold chain.maxOoo
  by_cases h : params.max_ooo_keys > 0#u32
  · have := hpos.mpr h; simp [h, this]
  · simp only [gt_iff_lt, not_lt] at h
    have hz : params.max_ooo_keys = 0#u32 := by scalar_tac
    have := hdef.mpr (Or.inl hz)
    simp [hz, this]

/-- The loop upper counter `i4` (defined via `Nat.max ats (self.ctr + 1)`) is one below the target
`ats` whenever `self.ctr < ats`. This is the recurring `i4.val + 1 = ats.val` fact used to identify
`i4` with `ctr_new = ats - 1`. -/
theorem i4_succ_eq_ats
    (self : chain.ChainEpochDirection) (ats i4 : U32)
    (h_gt : self.ctr.val < ats.val)
    (h_i4 : i4.val + 1 = Nat.max ats.val (self.ctr.val + 1)) :
    i4.val + 1 = ats.val := by
  simp only [Nat.max_def] at h_i4
  split at h_i4 <;> omega


/-- **Spec theorem for `spqr.chain.ChainEpochDirection.key`**:

• Takes a `ChainEpochDirection` value `self`, a target counter `ats`, and chain parameters
  `params`.
• Branches on the comparison of `ats` with `self.ctr`:

  **Case `ats = self.ctr`** (Ordering::Equal):
    Returns `(Err (Error.KeyAlreadyRequested ats), self)` — the key has already been consumed.

  **Case `ats < self.ctr`** (Ordering::Less):
    Delegates to `KeyHistory.get` to retrieve a previously-stored key.
    In all sub-cases, `result.2.ctr = self.ctr` and `result.2.next = self.next` (only `prev`
    is modified). The domain-level result is one of:
    - `Err (Error.KeyTrimmed ats)` when `ats + maxOoo params < self.ctr`
    (key was garbage-collected), with `self.prev` unchanged.
    - `Err (Error.KeyAlreadyRequested ats)` when the key is within the OOO window but not found
      in history, with `self.prev` unchanged.
    - `Ok out` with `out.length = 32`, key found and removed from history
      (`result.2.prev.data.length = self.prev.data.length - 36`), and provenance:
      there exists a 36-aligned offset `off` in `self.prev.data` whose 4-byte tag matches `ats`
      and whose 32-byte payload equals `out`.

  **Case `ats > self.ctr`** (Ordering::Greater), jump too large:
    If `ats.val - self.ctr.val > max_jump_or_default params`, returns
    `(Err (Error.KeyJump self.ctr ats), self)` with `self` unchanged.

  **Case `ats > self.ctr`** (Ordering::Greater), within jump budget:
    Advances the chain from `self.ctr` to `ats`, garbage-collects stale keys, and derives
    the final key via `next_key_internal`. Let `loopSteps = ats - (self.ctr + 1)`,
    `loopSecret = iterChainSecret self.next.val self.ctr loopSteps`, and
    `finalOkm = nextKeyHkdfOutput loopSecret ats`. Postcondition:
    - The result is `Ok key` with `key.length = 32`.
    - `result.2.ctr = ats` (counter advanced to the requested position).
    - `result.2.next.length = 32` (chain secret updated).
    - Functional correctness of returned key: `key.val = finalOkm.drop 32`.
    - Functional correctness of chain secret: `result.2.next.val = finalOkm.take 32`.
    - `result.2.prev.data.length % 36 = 0` (key history alignment preserved post-GC).
    - Key history bounded by `kh0.data.length + 36 * (ats - self.ctr)` where `kh0` is
      `∅` if clear was applied, else `self.prev` (accounts for clear optimization).
    - Overall bound: `result.2.prev.data.length ≤ self.prev.data.length + 36 * (ats - self.ctr)`.
    - When all existing keys become obsolete (`ats > self.ctr + maxOoo params`),
      the history is bounded by `36 * (ats - self.ctr)` (clear was applied).
    - The pre-GC key history equals `iterKeyHistory self.next.val self.ctr ats params kh0
    loopSteps`,
      and GC only removes records from it (shrinkage), preserving alignment.
    - GC liveness: when the trim threshold is exceeded, every retained 36-byte record in
      `result.2.prev` is unexpired w.r.t. the horizon `ctr_new - maxOoo`.
    - GC completeness: every unexpired record from the pre-GC history appears in the
      post-GC result.
    - GC no-op below threshold: when the pre-GC history is smaller than
      `trim_threshold`, the post-GC history equals the pre-GC history.
    - GC injective forward provenance: every post-GC record originated from a distinct
      pre-GC record (no duplication).
    - GC injective reverse completeness: injective mapping from unexpired pre-GC records
      to post-GC records; together with the forward provenance, establishes a bijection
      between post-GC records and live pre-GC records.
    - Post-GC key history fits in memory: `result.2.prev.data.length ≤ Usize.max`.
    - Pre-GC history monotonic growth: `kh0.data.length ≤ khPreGc.data.length`.

  **Case `ats < self.ctr`** (Ok sub-case) additionally establishes:
    - First-match provenance: the returned key comes from the earliest 36-aligned record
      whose 4-byte tag matches `ats` (no earlier record has the same tag).
    - Structural removal: the post-state history is either a swap-remove (when the removed
      record is not the last) or a tail-truncation (when it is), with bytes before the
      removed offset preserved element-wise.

The function always succeeds (returns `ok`) at the Lean/Aeneas level; the inner
`core.result.Result` carries the domain-level success/error.

**Source**: spqr/src/chain.rs, lines 247:4-296:5
-/
@[step]
theorem key_spec_equal (self : chain.ChainEpochDirection) (ats : U32)
    (params : proto.pq_ratchet.ChainParams)
    (h_next_len : self.next.length = 32)
    (h_at_bound : ats.val ≤ U32.max - 390451572)
    (h_maxooo_bound : (chain.maxOoo params).val < 390451572)
    (h_kh_cap : self.prev.data.length + 36 * (ats.val - self.ctr.val) ≤ Usize.max)
    (h_ctr_lt : self.ctr < U32.max)
    (h_prev_aligned : self.prev.data.length % 36 = 0)
    (h_prev_bound : self.prev.data.length ≤ Usize.max)
    (h_prev_ctr : self.prev.data.length ≤ 36 * self.ctr.val)
    (h_ooo_no_overflow : ats + (chain.maxOoo params).val ≤ U32.max)
    (h_platform : System.Platform.numBits = 64) :
    key self ats params ⦃ (result : (core.result.Result (alloc.vec.Vec U8) Error) ×
        chain.ChainEpochDirection) =>
      (ats = self.ctr →
          result.1 = core.result.Result.Err (Error.KeyAlreadyRequested ats) ∧
          result.2 = self) ⦄ := by
  unfold key
  simp only [alloc.vec.Vec.deref_mut,  lift, bind_tc_ok]
  step*
  · simp only [core.cmp.impls.OrdU32.cmp, Nat.compare_eq_gt] at *; omega
  · have h_i2_eq : i2.val = (chain.maxOoo params).val :=
      maxOoo_val_eq_of_posts params i2 i2_post1 i2_post2
    omega
  · have h_i2_eq := maxOoo_val_eq_of_posts params i2 i2_post1 i2_post2
    split
    · step*
      · rw [i4_post4]
        exact iterKeyHistory_data_length_mod_36 _ _ _ _ _ _
          (by simp [alloc.vec.Vec.length, kh_post])
      · scalar_tac
      · scalar_tac
      · rename_i y _ _ _ _ _ _
        obtain ⟨idx, key_arr⟩ := y
        step*
    · step*
      · rw [i4_post4]
        exact iterKeyHistory_data_length_mod_36 _ _ _ _ _ _ h_prev_aligned
      · have h_ats_gt : self.ctr.val < ats.val := by
          simp only [core.cmp.impls.OrdU32.cmp, Nat.compare_eq_gt] at *; omega
        exact key_gc_precond_no_clear self ats params i4 kh1  h_ats_gt
          h_prev_ctr i4_post1  i4_post6
      · scalar_tac
      · rename_i y _ _ _ _ _ _
        obtain ⟨idx, key_arr⟩ := y
        step*

theorem less_branch_vacuous {P : Prop} {a b : Nat}
    (h_lt : a < b) (h_gt : b < a) : P := by omega

@[step]
theorem key_spec_greater (self : chain.ChainEpochDirection) (ats : U32)
    (params : proto.pq_ratchet.ChainParams)
    (h_next_len : self.next.length = 32)
    (h_at_bound : ats.val ≤ U32.max - 390451572)
    (h_maxooo_bound : (chain.maxOoo params).val < 390451572)
    (h_ctr_bound : self.ctr.val ≤ U32.max - 390451572)
    (h_kh_cap : self.prev.data.length + 36 * (ats.val - self.ctr.val) ≤ Usize.max)
    (h_ctr_lt : self.ctr < U32.max)
    (h_prev_aligned : self.prev.data.length % 36 = 0)
    (h_prev_bound : self.prev.data.length ≤ Usize.max)
    (h_prev_ctr : self.prev.data.length ≤ 36 * self.ctr.val)
    (h_ooo_no_overflow : ats + (chain.maxOoo params).val ≤ U32.max)
    (h_platform : System.Platform.numBits = 64) :
    key self ats params ⦃
      (result : (core.result.Result (alloc.vec.Vec U8) Error) ×
        chain.ChainEpochDirection) =>
      (ats > self.ctr →
          ats.val - self.ctr.val > (chain.maxJump params).val →
          result.1 = core.result.Result.Err (Error.KeyJump self.ctr ats) ∧
          result.2 = self) ⦄ := by
  unfold key
  simp only [alloc.vec.Vec.deref_mut,  lift, bind_tc_ok]
  split
  · step
    simp only [core.cmp.impls.OrdU32.cmp, Nat.compare_eq_lt] at *
    intro h_gt
    omega
  · intro h_gt
    simp only [core.cmp.impls.OrdU32.cmp, Nat.compare_eq_eq] at *
    omega
  · step
    · simp only [core.cmp.impls.OrdU32.cmp, Nat.compare_eq_gt] at *; omega
    · step
      split
      · intro h_gt h_jump_gt
        have h_i1_eq : i1.val = (chain.maxJump params).val :=
          maxJump_val_eq_of_posts params i1 i1_post1 i1_post2
        simp only [gt_iff_lt] at *
        constructor <;> scalar_tac
      · step
        step
        · have h_i2_eq : i2.val = (chain.maxOoo params).val :=
          maxOoo_val_eq_of_posts params i2 i2_post1 i2_post2
          omega
        · have h_i2_eq : i2.val = (chain.maxOoo params).val :=
            maxOoo_val_eq_of_posts params i2 i2_post1 i2_post2
          split
          · step
            step
            step
            · rw [i4_post4]
              exact iterKeyHistory_data_length_mod_36 _ _ _ _ _ _
               (by simp [alloc.vec.Vec.length, kh_post])
            · scalar_tac
            · step
              · scalar_tac
              · rename_i y
                obtain ⟨idx, key_arr⟩ := y
                step
                intros h_gt h_jump_gt
                have h_i1_eq : i1.val = (chain.maxJump params).val :=
                  maxJump_val_eq_of_posts params i1 i1_post1 i1_post2
                simp only [gt_iff_lt] at *
                constructor <;> scalar_tac
          · step
            step
            · rw [kh_post4]
              exact iterKeyHistory_data_length_mod_36 _ _ _ _ _ _ h_prev_aligned
            · have h_ats_gt : self.ctr.val < ats.val := by
                simp only [core.cmp.impls.OrdU32.cmp, Nat.compare_eq_gt] at *; omega
              exact key_gc_precond_no_clear self ats params kh _  h_ats_gt
                h_prev_ctr kh_post1  kh_post6
            step
            · simp only [Nat.max_def] at kh_post1; split at kh_post1 <;> omega
            · rename_i y
              obtain ⟨idx, key_arr⟩ := y
              step
              intros h_gt h_jump_gt
              have h_i1_eq : i1.val = (chain.maxJump params).val :=
                maxJump_val_eq_of_posts params i1 i1_post1 i1_post2
              simp only [gt_iff_lt] at *
              constructor <;> scalar_tac

@[step]
theorem key_spec_less (self : chain.ChainEpochDirection) (ats : U32)
    (params : proto.pq_ratchet.ChainParams)
    (h_next_len : self.next.length = 32)
    (h_at_bound : ats.val ≤ U32.max - 390451572)
    (h_maxooo_bound : (chain.maxOoo params).val < 390451572)
    (h_ctr_bound : self.ctr.val ≤ U32.max - 390451572)
    (h_kh_cap : self.prev.data.length + 36 * (ats.val - self.ctr.val) ≤ Usize.max)
    (h_ctr_lt : self.ctr < U32.max)
    (h_prev_aligned : self.prev.data.length % 36 = 0)
    (h_prev_bound : self.prev.data.length ≤ Usize.max)
    (h_prev_ctr : self.prev.data.length ≤ 36 * self.ctr.val)
    (h_ooo_no_overflow : ats + (chain.maxOoo params).val ≤ U32.max)
    (h_platform : System.Platform.numBits = 64) :
    key self ats params ⦃
      (result : (core.result.Result (alloc.vec.Vec U8) Error) ×
        chain.ChainEpochDirection) =>
      (ats < self.ctr →
          chain.cedKeyLessPost self ats params result.1 result.2) ⦄ := by
  unfold chain.cedKeyLessPost
  unfold key
  simp only [alloc.vec.Vec.deref_mut,  lift, bind_tc_ok]
  step*
  · simp only [core.cmp.impls.OrdU32.cmp] at *
    intro _
    match r, r_post with
    | .Err _, h => exact h
    | .Ok out, ⟨hle, off, hmod, hbound, hslice, hfirst, hlen, hout, hkhlen, _,
    hkhalign, hpres, hswap, htail⟩ =>
      exact ⟨hle, hlen, hkhlen, hkhalign, off, hmod, hbound, hslice, hfirst, hout,
      hpres, hswap, htail⟩
  · simp only [core.cmp.impls.OrdU32.cmp, Nat.compare_eq_gt] at *; omega
  · have h_i2_eq : i2.val = (chain.maxOoo params).val :=
      maxOoo_val_eq_of_posts params i2 i2_post1 i2_post2
    omega
  · have h_i2_eq : i2.val = (chain.maxOoo params).val :=
      maxOoo_val_eq_of_posts params i2 i2_post1 i2_post2
    split
    · step*
      · rw [i4_post4]
        exact iterKeyHistory_data_length_mod_36 _ _ _ _ _ _
          (by simp [alloc.vec.Vec.length, kh_post])
      · scalar_tac
      · scalar_tac
      · rename_i y _ _ _ _ _ _
        obtain ⟨idx, key_arr⟩ := y
        step*
    · step
      step
      · rw [kh_post4]
        exact iterKeyHistory_data_length_mod_36 _ _ _ _ _ _ h_prev_aligned
      · have h_ats_gt : self.ctr.val < ats.val := by
          simp only [core.cmp.impls.OrdU32.cmp, Nat.compare_eq_gt] at *; omega
        exact key_gc_precond_no_clear self ats params kh _  h_ats_gt
          h_prev_ctr kh_post1  kh_post6
      step
      · simp only [Nat.max_def] at kh_post1; split at kh_post1 <;> omega
      · rename_i y
        obtain ⟨idx, key_arr⟩ := y
        step*


/-- **Sub-lemma for the clear branch** of `key_spec_greater_jump`:
when `ats > self.ctr + maxOoo params`, the key history is cleared before advancing. -/
private theorem key_spec_greater_jump_clear (self : chain.ChainEpochDirection) (ats : U32)
    (params : proto.pq_ratchet.ChainParams)
    (h_next_len : self.next.length = 32)
    (h_at_bound : ats.val ≤ U32.max - 390451572)
    (h_maxooo_bound : (chain.maxOoo params).val < 390451572)
    (h_ctr_bound : self.ctr.val ≤ U32.max - 390451572)
    (h_kh_cap : self.prev.data.length + 36 * (ats.val - self.ctr.val) ≤ Usize.max)
    (h_ctr_lt : self.ctr < U32.max)
    (h_prev_aligned : self.prev.data.length % 36 = 0)
    (h_prev_bound : self.prev.data.length ≤ Usize.max)
    (h_prev_ctr : self.prev.data.length ≤ 36 * self.ctr.val)
    (h_ooo_no_overflow : ats + (chain.maxOoo params).val ≤ U32.max)
    (h_platform : System.Platform.numBits = 64) :
    key self ats params ⦃
      (result : (core.result.Result (alloc.vec.Vec U8) Error) ×
        chain.ChainEpochDirection) =>
        (∀ (h_gt : ats > self.ctr),
          ats.val - self.ctr.val ≤ (chain.maxJump params).val →
          self.ctr.val + (chain.maxOoo params).val < ats.val →
          chain.cedKeyAdvancePost self ats params result.1 result.2 h_gt) ⦄ := by
  unfold chain.cedKeyAdvancePost
  unfold key
  simp only [alloc.vec.Vec.deref_mut,  lift, bind_tc_ok]
  split
  · step
    rename_i h
    simp only [core.cmp.impls.OrdU32.cmp, Nat.compare_eq_lt] at h
    scalar_tac
  · simp only [gt_iff_lt, UScalar.lt_equiv, tsub_le_iff_right, alloc.vec.Vec.length,
    UScalarTy.U32_numBits_eq, Nat.reducePow, WP.spec_ok,
    reduceCtorEq, false_and, exists_const, le_add_iff_nonneg_right, zero_le, true_and, imp_false]
    rename_i h
    simp only [core.cmp.impls.OrdU32.cmp, Nat.compare_eq_eq] at h
    omega
  · step
    · rename_i h
      simp only [core.cmp.impls.OrdU32.cmp, Nat.compare_eq_gt] at h
      omega
    · step
      split
      · have := maxJump_val_eq_of_posts params i1 i1_post1 i1_post2
        intro h_gt h_jump_le
        simp only [gt_iff_lt] at h_gt
        scalar_tac
      · step
        step
        · have := maxOoo_val_eq_of_posts params i2 i2_post1 i2_post2
          omega
        · have h_i2_eq:= maxOoo_val_eq_of_posts params i2 i2_post1 i2_post2
          split
          · step
            step
            step
            · rw [i4_post4]
              exact iterKeyHistory_data_length_mod_36 _ _ _ _ _ _
               (by simp [alloc.vec.Vec.length, kh_post])
            · scalar_tac
            · step
              · scalar_tac
              · rename_i y
                obtain ⟨idx, key_arr⟩ := y
                step
                intros h_gt h_jump_gt h_ats_gt_ooo
                simp only [gt_iff_lt] at *
                have h_ats_gt : ats.val > self.ctr.val := by omega
                have h_i4_eq : i4.val + 1 = ats.val :=
                  i4_succ_eq_ats self ats i4 h_ats_gt i4_post1
                have h_i5_eq : i5.val = ats.val := by omega
                simp only [if_pos h_ats_gt_ooo]
                unfold chain.KeyHistory.GcPost at kh2_post
                obtain ⟨kh2_post1, kh2_post2, kh2_post3, kh2_post4⟩ := kh2_post
                rw [maxOoo_if_eq] at kh2_post3 kh2_post4
                have hkh_eq : kh = { data := ⟨[], by simp⟩ } := by
                  obtain ⟨⟨dl, dp⟩⟩ := kh
                  simp only [List.length_eq_zero_iff] at kh_post
                  subst kh_post
                  rfl
                have h_pregc_eq :
                    iterKeyHistory (↑self.next) (↑self.ctr) (↑ats) params
                      { data := ⟨[], by simp⟩ } (↑ats - (↑self.ctr + 1)) = kh1 := by
                  rw [← hkh_eq]
                  exact i4_post4.symm
                simp only [h_pregc_eq]
                have h_kh1_mod : kh1.data.length % 36 = 0 := by
                  rw [i4_post4]
                  apply iterKeyHistory_data_length_mod_36
                  simp [alloc.vec.Vec.length, kh_post]
                have h_i4_val : (↑i4 : Nat) = ↑ats - 1 := by omega
                have h_36bound : kh1.data.length ≤ 36 * (↑ats - ↑self.ctr) := by
                  have h := i4_post6
                  simp only [alloc.vec.Vec.length, kh_post] at h; omega
                have h_empty_len :
                    (({ data := ⟨[], by simp⟩ } : chain.KeyHistory).data).length = 0 := rfl
                refine ⟨⟨result, rfl, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                · rw [← result_post]; simp
                · rw [← result_post]
                  simp only [Array.val_to_slice, UScalarTy.U32_numBits_eq,
                    Nat.reducePow, s1_post6, i4_post3]
                  congr 2
                  apply UScalar.val_eq_imp
                  simp only [UScalar.val]
                  simp
                  omega
                · exact h_i5_eq
                · simp only [Slice.length] at s1_post4 ⊢
                  simp only [alloc.vec.Vec.length] at i4_post2
                  simp only [alloc.vec.Vec.length]
                  rw [s1_post4, i4_post2]
                · simp only [s1_post5, i4_post3, UScalarTy.U32_numBits_eq, Nat.reducePow]
                  congr 2
                  apply UScalar.val_eq_imp
                  simp only [UScalar.val]; simp; omega
                · exact kh2_post1
                · simp only [h_empty_len, Nat.zero_add]
                  exact le_trans kh2_post2 h_36bound
                · have h := le_trans kh2_post2 h_36bound
                  simp only [alloc.vec.Vec.length] at h ⊢; omega
                · intro _
                  exact le_trans kh2_post2 h_36bound
                · exact le_trans (le_trans kh2_post2 h_36bound) (by
                    simp only [alloc.vec.Vec.length] at h_kh_cap ⊢; omega)
                · exact kh2_post2
                · exact h_kh1_mod
                · simp only [h_empty_len]; exact Nat.zero_le _
                · exact chain.keyPostGc_of_GcPost _ _ _ _ _
                    h_i4_val kh2_post2 kh2_post3 kh2_post4
          · step
            step
            · rw [kh_post4]
              exact iterKeyHistory_data_length_mod_36 _ _ _ _ _ _ h_prev_aligned
            · have h_ats_gt : self.ctr.val < ats.val := by
                simp only [core.cmp.impls.OrdU32.cmp, Nat.compare_eq_gt] at *
                omega
              exact key_gc_precond_no_clear self ats params kh _  h_ats_gt
                h_prev_ctr kh_post1  kh_post6
            step
            · simp only [Nat.max_def] at kh_post1; split at kh_post1 <;> omega
            · rename_i y
              obtain ⟨idx, key_arr⟩ := y
              step
              intros h_gt h_jump_gt h_ats_gt_ooo
              have h_i1_eq : i1.val = (chain.maxJump params).val :=
                maxJump_val_eq_of_posts params i1 i1_post1 i1_post2
              simp only [gt_iff_lt] at *
              -- In the no-clear branch, ats ≤ self.ctr + maxOoo, contradiction
              exfalso
              have h_not_split : ¬(i3 < ats) := by assumption
              exact h_not_split ((UScalar.lt_equiv i3 ats).mpr (by scalar_tac))

/-- **Sub-lemma for the no-clear branch** of `key_spec_greater_jump`:
when `ats ≤ self.ctr + maxOoo params`, the existing key history is preserved. -/
private theorem key_spec_greater_jump_no_clear (self : chain.ChainEpochDirection) (ats : U32)
    (params : proto.pq_ratchet.ChainParams)
    (h_next_len : self.next.length = 32)
    (h_at_bound : ats.val ≤ U32.max - 390451572)
    (h_maxooo_bound : (chain.maxOoo params).val < 390451572)
    (h_ctr_bound : self.ctr.val ≤ U32.max - 390451572)
    (h_kh_cap : self.prev.data.length + 36 * (ats.val - self.ctr.val) ≤ Usize.max)
    (h_ctr_lt : self.ctr < U32.max)
    (h_prev_aligned : self.prev.data.length % 36 = 0)
    (h_prev_bound : self.prev.data.length ≤ Usize.max)
    (h_prev_ctr : self.prev.data.length ≤ 36 * self.ctr.val)
    (h_ooo_no_overflow : ats + (chain.maxOoo params).val ≤ U32.max)
    (h_platform : System.Platform.numBits = 64) :
    key self ats params ⦃
      (result : (core.result.Result (alloc.vec.Vec U8) Error) ×
        chain.ChainEpochDirection) =>
        (∀ (h_gt : ats > self.ctr),
          ats.val - self.ctr.val ≤ (chain.maxJump params).val →
          ¬(self.ctr.val + (chain.maxOoo params).val < ats.val) →
          chain.cedKeyAdvancePost self ats params result.1 result.2 h_gt) ⦄ := by
  unfold chain.cedKeyAdvancePost
  unfold key
  simp only [alloc.vec.Vec.deref_mut,  lift, bind_tc_ok]
  split
  · step
    rename_i h
    simp only [core.cmp.impls.OrdU32.cmp, Nat.compare_eq_lt] at h
    scalar_tac
  · simp only [gt_iff_lt, UScalar.lt_equiv, tsub_le_iff_right, alloc.vec.Vec.length,
    UScalarTy.U32_numBits_eq, Nat.reducePow, WP.spec_ok,
    reduceCtorEq, false_and, exists_const, le_add_iff_nonneg_right, zero_le, true_and, imp_false]
    rename_i h
    simp only [core.cmp.impls.OrdU32.cmp, Nat.compare_eq_eq] at h
    omega
  · step
    · simp only [core.cmp.impls.OrdU32.cmp, Nat.compare_eq_gt] at *; omega
    · step
      split
      · have h_i1_eq : i1.val = (chain.maxJump params).val :=
          maxJump_val_eq_of_posts params i1 i1_post1 i1_post2
        intro h_gt h_jump_le
        simp only [gt_iff_lt] at h_gt
        scalar_tac
      · step
        step
        · have h_i2_eq : i2.val = (chain.maxOoo params).val :=
          maxOoo_val_eq_of_posts params i2 i2_post1 i2_post2
          omega
        · have h_i2_eq : i2.val = (chain.maxOoo params).val :=
            maxOoo_val_eq_of_posts params i2 i2_post1 i2_post2
          split
          · step
            step
            step
            · rw [i4_post4]
              exact iterKeyHistory_data_length_mod_36 _ _ _ _ _ _
               (by simp [alloc.vec.Vec.length, kh_post])
            · scalar_tac
            · step
              · scalar_tac
              · rename_i y
                obtain ⟨idx, key_arr⟩ := y
                step
                intros h_gt h_jump_gt h_ats_le_ooo
                exfalso
                apply h_ats_le_ooo
                have h_split : i3 < ats := by assumption
                have h_split_val : i3.val < ats.val :=
                  (UScalar.lt_equiv i3 ats).mp h_split
                omega
          · step
            step
            · rw [kh_post4]
              exact iterKeyHistory_data_length_mod_36 _ _ _ _ _ _ h_prev_aligned
            · have h_ats_gt : self.ctr.val < ats.val := by
                simp only [core.cmp.impls.OrdU32.cmp, Nat.compare_eq_gt] at *
                omega
              exact key_gc_precond_no_clear self ats params kh _  h_ats_gt
                h_prev_ctr kh_post1  kh_post6
            step
            · simp only [Nat.max_def] at kh_post1; split at kh_post1 <;> omega
            · rename_i y
              obtain ⟨idx, key_arr⟩ := y
              step
              intros h_gt h_jump_gt h_ats_le_ooo
              have h_i1_eq : i1.val = (chain.maxJump params).val :=
                maxJump_val_eq_of_posts params i1 i1_post1 i1_post2
              simp only [gt_iff_lt] at *
              simp only [if_neg h_ats_le_ooo]
              unfold chain.KeyHistory.GcPost at kh2_post
              obtain ⟨kh2_post1, kh2_post2, kh2_post3, kh2_post4⟩ := kh2_post
              rw [maxOoo_if_eq] at kh2_post3 kh2_post4
              have hkv : kh.val + 1 = ats.val := by
                have h := kh_post1
                have hle : self.ctr.val + 1 ≤ ats.val := by scalar_tac
                simp only [Nat.max_eq_left hle] at h; exact h
              have hkv2 : kh.val = ats.val - 1 := by omega
              refine ⟨⟨result, rfl, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · rw [← result_post]; simp
              · rw [← result_post]
                simp only [Array.val_to_slice, UScalarTy.U32_numBits_eq,
                  Nat.reducePow, s1_post6]
                congr 2; apply UScalar.val_eq_imp
                simp only [UScalar.val]
                simp only [UScalarTy.U32_numBits_eq, Bvify.U32.UScalar_bv, UScalar.bv_toNat,
                  BitVec.toNat_ofFin]
                omega
              · omega
              · simp only [Slice.length, alloc.vec.Vec.length] at *; omega
              · simp only [s1_post5, UScalarTy.U32_numBits_eq, Nat.reducePow]
                congr 2; apply UScalar.val_eq_imp
                simp only [UScalar.val]; simp; omega
              · exact kh2_post1
              · exact le_trans kh2_post2 kh_post6
              · exact le_trans kh2_post2 kh_post6
              · intro h_ooo_gt; omega
              · exact le_trans (le_trans kh2_post2 kh_post6)
                  (by simp only [alloc.vec.Vec.length] at h_kh_cap ⊢; omega)
              · rw [kh_post4] at kh2_post2; exact kh2_post2
              · exact iterKeyHistory_data_length_mod_36 _ _ _ _ _ _ h_prev_aligned
              · rw [← kh_post4]; exact kh_post5
              · rw [kh_post4] at kh2_post2 kh2_post3 kh2_post4
                exact chain.keyPostGc_of_GcPost _ _ _ _ _
                  hkv2 kh2_post2 kh2_post3 kh2_post4

/-- **Spec theorem for `spqr.chain.ChainEpochDirection.key`** (greater-jump case):

Proves the **greater case with jump within budget** (`ats > self.ctr` and
`ats.val - self.ctr.val ≤ max_jump_or_default(params)`). Combines
`key_spec_greater_jump_clear` and `key_spec_greater_jump_no_clear`.

**Source**: spqr/src/chain.rs, lines 247:4-296:5
-/
@[step]
theorem key_spec_greater_jump (self : chain.ChainEpochDirection) (ats : U32)
    (params : proto.pq_ratchet.ChainParams)
    (h_next_len : self.next.length = 32)
    (h_at_bound : ats.val ≤ U32.max - 390451572)
    (h_maxooo_bound : (chain.maxOoo params).val < 390451572)
    (h_ctr_bound : self.ctr.val ≤ U32.max - 390451572)
    (h_kh_cap : self.prev.data.length + 36 * (ats.val - self.ctr.val) ≤ Usize.max)
    (h_ctr_lt : self.ctr < U32.max)
    (h_prev_aligned : self.prev.data.length % 36 = 0)
    (h_prev_bound : self.prev.data.length ≤ Usize.max)
    (h_prev_ctr : self.prev.data.length ≤ 36 * self.ctr.val)
    (h_ooo_no_overflow : ats + (chain.maxOoo params).val ≤ U32.max)
    (h_platform : System.Platform.numBits = 64) :
    key self ats params ⦃
      (result : (core.result.Result (alloc.vec.Vec U8) Error) ×
        chain.ChainEpochDirection) =>
      (∀ (h_gt : ats > self.ctr),
          ats.val - self.ctr.val ≤ (chain.maxJump params).val →
          chain.cedKeyAdvancePost self ats params result.1 result.2 h_gt) ⦄ := by
  have h_clear := key_spec_greater_jump_clear self ats params h_next_len h_at_bound
    h_maxooo_bound h_ctr_bound h_kh_cap h_ctr_lt h_prev_aligned h_prev_bound h_prev_ctr
    h_ooo_no_overflow h_platform
  have h_no_clear := key_spec_greater_jump_no_clear self ats params h_next_len h_at_bound
    h_maxooo_bound h_ctr_bound h_kh_cap h_ctr_lt h_prev_aligned h_prev_bound h_prev_ctr
    h_ooo_no_overflow h_platform
  have h_ok : ∃ v, key self ats params = ok v := by
    unfold WP.spec WP.theta WP.wp_return at h_clear
    match hk : key self ats params with
    | ok v => exact ⟨v, rfl⟩
    | fail _ => simp [hk] at h_clear
    | div => simp [hk] at h_clear
  obtain ⟨v, hv⟩ := h_ok
  simp only [WP.spec, WP.theta, WP.wp_return, hv] at h_clear h_no_clear ⊢
  intro h_gt h_jump_le
  by_cases h_ooo : self.ctr.val + (chain.maxOoo params).val < ats.val
  · exact h_clear h_gt h_jump_le h_ooo
  · exact h_no_clear h_gt h_jump_le h_ooo

@[step]
theorem key_spec (self : chain.ChainEpochDirection) (ats : U32)
    (params : proto.pq_ratchet.ChainParams)
    (h_next_len : self.next.length = 32)
    (h_at_bound : ats.val ≤ U32.max - 390451572)
    (h_maxooo_bound : (chain.maxOoo params).val < 390451572)
    (h_ctr_bound : self.ctr.val ≤ U32.max - 390451572)
    (h_kh_cap : self.prev.data.length + 36 * (ats.val - self.ctr.val) ≤ Usize.max)
    (h_ctr_lt : self.ctr < U32.max)
    (h_prev_aligned : self.prev.data.length % 36 = 0)
    (h_prev_bound : self.prev.data.length ≤ Usize.max)
    (h_prev_ctr : self.prev.data.length ≤ 36 * self.ctr.val)
    (h_ooo_no_overflow : ats + (chain.maxOoo params).val ≤ U32.max)
    (h_platform : System.Platform.numBits = 64) :
    key self ats params ⦃ (result : (core.result.Result (alloc.vec.Vec U8) Error) ×
        chain.ChainEpochDirection) =>
      chain.cedKeyPost self ats params result.1 result.2 ⦄ := by
  have h_eq := key_spec_equal self ats params h_next_len h_at_bound h_maxooo_bound
    h_kh_cap h_ctr_lt h_prev_aligned h_prev_bound h_prev_ctr h_ooo_no_overflow h_platform
  have h_lt := key_spec_less self ats params h_next_len h_at_bound h_maxooo_bound h_ctr_bound
    h_kh_cap h_ctr_lt h_prev_aligned h_prev_bound h_prev_ctr h_ooo_no_overflow h_platform
  have h_gt := key_spec_greater self ats params h_next_len h_at_bound h_maxooo_bound h_ctr_bound
    h_kh_cap h_ctr_lt h_prev_aligned h_prev_bound h_prev_ctr h_ooo_no_overflow h_platform
  have h_gj := key_spec_greater_jump self ats params h_next_len h_at_bound h_maxooo_bound
    h_ctr_bound h_kh_cap h_ctr_lt h_prev_aligned h_prev_bound h_prev_ctr h_ooo_no_overflow
    h_platform
  have h_ok : ∃ v, key self ats params = ok v := by
    unfold WP.spec WP.theta WP.wp_return at h_eq
    match hk : key self ats params with
    | ok v => exact ⟨v, rfl⟩
    | fail _ => simp [hk] at h_eq
    | div => simp [hk] at h_eq
  obtain ⟨v, hv⟩ := h_ok
  simp only [WP.spec, WP.theta, WP.wp_return, hv] at h_eq h_lt h_gt h_gj ⊢
  unfold chain.cedKeyPost
  exact ⟨h_eq, h_lt, h_gt, fun h1 h2 => h_gj h1 h2⟩

end spqr.chain.ChainEpochDirection
