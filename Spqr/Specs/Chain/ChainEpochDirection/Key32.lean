/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Chain.ChainEpochDirection.Key

/-! # 32-bit platform variants for `ChainEpochDirection::key`

This file provides 32-bit platform variants of the loop body spec, loop spec,
and the equal-case key spec.  The only differences from the 64-bit versions in
`Key.lean` are:

  - The maxOoo bound is tightened from `390451572` to `108458770`.
    On a 32-bit platform `Usize.max = 2³² − 1`, so the GC trim threshold
    `(maxOoo * 11/10 + 1) * 36` must fit in 32 bits, which requires
    `maxOoo < 108458770`.
  - The GC step uses `chain.KeyHistory.gc_spec` (platform-independent,
    `params.max_ooo_keys.val < 108458770`) instead of `gc_spec_64`.

All proofs mirror the 64-bit versions with the constant substitution.

**Source**: spqr/src/chain.rs -/

open Aeneas Aeneas.Std Result spqr crypto

namespace spqr.chain.ChainEpochDirection.key_loop

/-- **Spec theorem for `spqr.chain.ChainEpochDirection.key_loop.body`** (32-bit platform):

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
  In both sub-cases the counter advances: `i2.val = i.val + 1`.

Identical to `body_spec` but with the tighter maxOoo bound `108458770` for 32-bit platforms. -/
@[step]
theorem body_spec_32
    (at1 : U32) (params : proto.pq_ratchet.ChainParams)
    (i : U32) (v : alloc.vec.Vec U8) (kh : chain.KeyHistory)
    (h_v_len : v.length = 32)
    (h_i : i < U32.max)
    (h_kh_cap : kh.data.length + 36 ≤ Usize.max)
    (h_ctr_bound : i.val + 1 ≤ U32.max - 108458770)
    (h_maxooo_bound : (chain.maxOoo params).val < 108458770) :
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
          (let ctr1 : U32 := ⟨i.val + 1, by scalar_tac⟩
           let okm := nextKeyHkdfOutput v.val ctr1
           if (i.val + 1) + (chain.maxOoo params).val ≥ at1.val then
              kh2.data.length = kh.data.length + 36 ∧
              kh2.data = kh.data ++ (core.num.U32.to_be_bytes ctr1).val ++ okm.drop 32
           else
            kh2 = kh) ⦄ := by
  have hmo : chain.ChainParams.max_ooo_keys_or_default params = ok (chain.maxOoo params) := by
    unfold chain.ChainParams.max_ooo_keys_or_default chain.maxOoo; split <;> rfl
  have hvs : v.slice.length = 32 := by simpa [alloc.vec.Vec.val, Slice.length] using h_v_len
  have hb : i.val + 1 < 2 ^ UScalarTy.U32.numBits := by scalar_tac
  unfold body
  simp only [alloc.vec.Vec.deref_mut, lift, hmo, bind_ok]
  step*
  all_goals
    have hat : at1.val > i.val + 1 := by scalar_tac
    have hi2 : i2.val = i.val + 1 := by scalar_tac
    have hi4 : i4.val = i.val + 1 + (chain.maxOoo params).val := by scalar_tac
    have hs1v : s1.val = List.take 32 (nextKeyHkdfOutput v.val (⟨i.val + 1, hb⟩ : U32)) :=
      ‹s1.val = _›
    have hk2 : k.2.val = List.drop 32 (nextKeyHkdfOutput v.val (⟨i.val + 1, hb⟩ : U32)) :=
      ‹k.2.val = _›
    have hk1 : k.1 = (⟨i.val + 1, hb⟩ : U32) :=
      UScalar.val_eq_imp _ _ (by rw [‹k.1.val = i.val + 1›]; rfl)
    have hs1 : (({ slice := s1 } : alloc.vec.Vec U8)).length = 32 := by
      have : s1.length = 32 := by rw [‹s1.length = _›, hvs]
      exact this
    refine ⟨hat, hi2, hs1, hs1v, ?_⟩
    have hge : (i4 ≥ at1) ↔ (i.val + 1 + (chain.maxOoo params).val ≥ at1.val) := by
      rw [ge_iff_le, UScalar.le_equiv, hi4]
    split_ifs with hc <;> first
      | exact ⟨‹_›, by rw [‹kh1.data.val = _›, hk1, hk2]⟩
      | exact absurd (hge.mpr hc) ‹_›
      | exact absurd (hge.mp ‹_›) hc

end spqr.chain.ChainEpochDirection.key_loop


open Aeneas Aeneas.Std Result spqr crypto

/-! # Spec theorem for `spqr::chain::{spqr::chain::ChainEpochDirection}::key`: loop 0 (32-bit)

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

Identical to `key_loop_spec` but with the tighter maxOoo bound `108458770` for 32-bit platforms.

**Source**: spqr/src/chain.rs, lines 270:8-286:9 -/


namespace spqr.chain.ChainEpochDirection

@[step]
theorem key_loop_spec_32
    (at1 : U32) (params : proto.pq_ratchet.ChainParams)
    (i : U32) (v : alloc.vec.Vec U8) (kh : chain.KeyHistory)
    (h_v_len : v.length = 32)
    (h_at_bound : at1.val ≤ U32.max - 108458770)
    (h_maxooo_bound : (chain.maxOoo params).val < 108458770)
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
      at1.val ≤ U32.max - 108458770 ∧
      (chain.maxOoo params).val < 108458770 ∧
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
      have hspec := key_loop.body_spec_32 at1 params i' v' kh' h_inv_v
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
                  apply alloc.vec.Vec.ext; simpa using hdata
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
              vecOmega
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
      simp only [alloc.vec.Vec.deref_mut, alloc.vec.Vec.length, lift] at *
      have h_i1_ok : i'.val + 1 ≤ U32.max := by omega
      simp only [gt_iff_lt, UScalar.lt_equiv]
      step*
  · exact ⟨h_v_len, Nat.le_refl _, h_i_bound, h_at_bound, h_maxooo_bound, h_kh_cap,
      Nat.le_refl _, by simp, by simp [iterChainSecret],
      by simp [iterKeyHistory, iterKeyHistoryData],
      fun h => by scalar_tac, fun _ => ⟨rfl, rfl, rfl⟩⟩


/-- Helper: `(chain.maxOoo params).val < bound` implies `params.max_ooo_keys.val < bound`. -/
private theorem maxOoo_imp_raw_ooo (params : proto.pq_ratchet.ChainParams) (bound : Nat)
    (h : (chain.maxOoo params).val < bound) : params.max_ooo_keys.val < bound := by
  unfold chain.maxOoo at h
  by_cases hpos : params.max_ooo_keys > 0#u32
  · simp only [hpos, ↓reduceIte] at h; exact h
  · simp only [gt_iff_lt, UScalar.lt_equiv, UScalar.ofNatCore_val_eq, not_lt,
      Nat.le_zero] at hpos
    omega

/-- **Spec for `keyAdvanceTail`** (32-bit variant of `keyAdvanceTail_spec`): same
postcondition, with the tighter 32-bit bounds and `gc` discharged by `KeyHistory.gc_spec`. -/
private theorem keyAdvanceTail_spec_32 (self : chain.ChainEpochDirection) (ats : U32)
    (params : proto.pq_ratchet.ChainParams) (kh : chain.KeyHistory)
    (h_gt : ats > self.ctr)
    (h_next_len : self.next.length = 32)
    (h_at_bound : ats.val ≤ U32.max - 108458770)
    (h_maxooo_bound : (chain.maxOoo params).val < 108458770)
    (h_kh_cap : kh.data.length + 36 * (ats.val - self.ctr.val) ≤ Usize.max)
    (h_kh_aligned : kh.data.length % 36 = 0)
    (h_kh_ctr : kh.data.length ≤ 36 * self.ctr.val) :
    keyAdvanceTail self ats params kh ⦃ (r : chain.KeyHistory × U32 × alloc.vec.Vec U8 ×
        alloc.vec.Vec U8) =>
      keyAdvanceTailPost self ats params kh r.1 r.2.1 r.2.2.1 r.2.2.2 h_gt ⦄ := by
  unfold keyAdvanceTail
  simp only [alloc.vec.Vec.deref_mut, lift]
  step as ⟨i4, v, kh1⟩
  step with chain.KeyHistory.gc_spec
  · rw [‹kh1 = _›]
    exact iterKeyHistory_data_length_mod_36 _ _ _ _ _ _ h_kh_aligned
  · exact maxOoo_imp_raw_ooo params _ h_maxooo_bound
  · exact key_gc_precond_no_clear { self with prev := kh } ats params i4 kh1 h_gt h_kh_ctr ‹_› ‹_›
  step*
  · exact ‹v.length = 32›
  · scalar_tac
  · unfold keyAdvanceTailPost
    simp only
    have hb4 : i4.val + 1 < 2 ^ UScalarTy.U32.numBits := by scalar_tac
    have hba : ats.val < 2 ^ UScalarTy.U32.numBits := by scalar_tac
    have hle : self.ctr.val + 1 ≤ ats.val := by scalar_tac
    have hkv : i4.val + 1 = ats.val := by
      have h : i4.val + 1 = Nat.max ats.val (self.ctr.val + 1) := ‹_›
      simp only [Nat.max_eq_left hle] at h; exact h
    have h_i4_val : i4.val = ats.val - 1 := by omega
    have h_i5_eq : i5.val = ats.val := by
      have : i5.val = i4.val + 1 := ‹_›
      omega
    have hgc : kh1.GcPost i4 params kh2 := ‹_›
    unfold chain.KeyHistory.GcPost at hgc
    obtain ⟨g1, g2, g3, g4⟩ := hgc
    rw [maxOoo_if_eq] at g3 g4
    have hkh1 : kh1 = iterKeyHistory (↑self.next) (↑self.ctr) (↑ats) params kh
        (↑ats - (↑self.ctr + 1)) := ‹_›
    have hkh1_ub : kh1.data.length ≤ kh.data.length + 36 * (↑ats - ↑self.ctr) := ‹_›
    have hkh1_lb : kh.data.length ≤ kh1.data.length := ‹_›
    have hctr : ({ toFin := ⟨↑i4 + 1, hb4⟩ }#uscalar : U32) =
        ({ toFin := ⟨↑ats, hba⟩ }#uscalar : U32) := by
      apply UScalar.val_eq_imp; simp only [UScalar.val]; simp; omega
    have hka : a.val = List.drop 32 (nextKeyHkdfOutput (↑v.slice)
        ({ toFin := ⟨↑i4 + 1, hb4⟩ }#uscalar)) := ‹_›
    have hs1 : s1.val = List.take 32 (nextKeyHkdfOutput (↑v.slice)
        ({ toFin := ⟨↑i4 + 1, hb4⟩ }#uscalar)) := ‹_›
    have hv : v.slice.val = iterChainSecret (↑self.next) (↑self.ctr) (↑ats - (↑self.ctr + 1)) :=
      ‹v.val = _›
    have hv1 : v1.val = a.val := by
      have : a.to_slice = v1.slice := ‹_›
      simp [alloc.vec.Vec.val, ← this]
    rw [← hkh1]
    refine ⟨?_, ?_, h_i5_eq, ?_, ?_, g1, le_trans g2 hkh1_ub, ?_, g2, ?_, hkh1_lb, ?_⟩
    · simp [alloc.vec.Vec.length, hv1]
    · rw [hv1, hka, hv, hctr]
    · have : s1.length = v.slice.length := ‹_›
      have : v.length = 32 := ‹_›
      simp only [alloc.vec.Vec.length, alloc.vec.Vec.val, Slice.length] at *
      omega
    · change s1.val = _
      rw [hs1, hv, hctr]
    · exact le_trans (le_trans g2 hkh1_ub) (by vecOmega)
    · rw [hkh1]
      exact iterKeyHistory_data_length_mod_36 _ _ _ _ _ _ h_kh_aligned
    · exact chain.keyPostGc_of_GcPost _ _ _ _ _ h_i4_val g2 g3 g4


attribute [local step] keyAdvanceTail_spec_32

/-- **Combined spec for all branches of `key`** (32-bit platform): the full postcondition
`chain.cedKeyPost`, proved with a single symbolic execution of `key`.  The per-branch
theorems below are projections of this one.
Uses `gc_spec` (platform-independent) instead of `gc_spec_64`. -/
private theorem key_spec_all_32 (self : chain.ChainEpochDirection) (ats : U32)
    (params : proto.pq_ratchet.ChainParams)
    (h_next_len : self.next.length = 32)
    (h_at_bound : ats.val ≤ U32.max - 108458770)
    (h_maxooo_bound : (chain.maxOoo params).val < 108458770)
    (h_kh_cap : self.prev.data.length + 36 * (ats.val - self.ctr.val) ≤ Usize.max)
    (h_prev_aligned : self.prev.data.length % 36 = 0)
    (h_prev_bound : self.prev.data.length ≤ Usize.max)
    (h_prev_ctr : self.prev.data.length ≤ 36 * self.ctr.val)
    (h_ooo_no_overflow : ats + (chain.maxOoo params).val ≤ U32.max) :
    key self ats params ⦃ (result : (core.result.Result (alloc.vec.Vec U8) Error) ×
        chain.ChainEpochDirection) =>
      chain.cedKeyPost self ats params result.1 result.2 ⦄ := by
  rw [key_eq]
  simp only [lift]
  step*
  · -- Less: delegate to `KeyHistory.get`
    have hlt := ordU32_cmp_lt_val ‹_›
    refine ⟨fun h => ?_, fun _ => ⟨rfl, rfl, ?_⟩, fun h => ?_, fun h => ?_⟩
    · subst h; omega
    · cases r with
      | Err _ => exact ‹_›
      | Ok out =>
        obtain ⟨hle, off, hmod, hbound, hslice, hfirst, hlen, hout, hkhlen, _,
          hkhalign, hpres, hswap, htail⟩ := ‹_ ∧ ∃ off, _›
        exact ⟨hle, hlen, hkhlen, hkhalign, off, hmod, hbound, hslice, hfirst, hout,
          hpres, hswap, htail⟩
    · exfalso; scalar_tac
    · exfalso; scalar_tac
  · -- Equal
    have heq := ordU32_cmp_eq_val ‹_›
    refine ⟨fun _ => ⟨rfl, rfl⟩, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> exfalso <;> scalar_tac
  · have := ordU32_cmp_gt_val ‹_›
    omega
  · -- Greater, jump too large
    have hgt := ordU32_cmp_gt_val ‹_›
    have := maxJump_val_eq_of_posts params i1 ‹_› ‹_›
    refine ⟨fun h => ?_, fun h => ?_, fun _ _ => ⟨rfl, rfl⟩, fun _ h => ?_⟩
    · subst h; omega
    all_goals exfalso; scalar_tac
  · have h_i2_eq := maxOoo_val_eq_of_posts params i2 ‹_› ‹_›
    omega
  · -- Greater, within jump budget: pick the starting key history, then the shared tail
    have hgt := ordU32_cmp_gt_val ‹_›
    have h_i1_eq := maxJump_val_eq_of_posts params i1 ‹_› ‹_›
    have h_i2_eq := maxOoo_val_eq_of_posts params i2 ‹_› ‹_›
    have h_gt : ats > self.ctr := by scalar_tac
    split
    · step*
      refine ⟨fun h => ?_, fun h => ?_, fun _ h => ?_, fun h_gt' _ => ?_⟩
      · subst h; omega
      · exfalso; scalar_tac
      · exfalso; scalar_tac
      exact cedKeyAdvancePost_of_tail self ats params _ kh2 i5 v1 v2 h_gt' (fun _ => ‹_›)
        (fun h => absurd (by scalar_tac) h) ‹_›
    · step*
      refine ⟨fun h => ?_, fun h => ?_, fun _ h => ?_, fun h_gt' _ => ?_⟩
      · subst h; omega
      · exfalso; scalar_tac
      · exfalso; scalar_tac
      exact cedKeyAdvancePost_of_tail self ats params self.prev kh2 i5 v1 v2 h_gt'
        (fun h => absurd h (by scalar_tac)) (fun _ => rfl) ‹_›


/-- **Spec theorem for `spqr.chain.ChainEpochDirection.key`** (32-bit platform, equal case):

• Takes a `ChainEpochDirection` value `self`, a target counter `ats`, and chain parameters
  `params`.
• Proves the **equal case** (`ats = self.ctr`): the function returns
  `(Err (Error.KeyAlreadyRequested ats), self)` — the key has already been consumed.

Identical to `key_spec_equal` but with:
  - `h_at_bound : ats.val ≤ U32.max - 108458770` (tighter bound for 32-bit)
  - `h_maxooo_bound : (chain.maxOoo params).val < 108458770`
  - No `h_platform` hypothesis required.

Uses `gc_spec` (platform-independent) instead of `gc_spec_64`.

**Source**: spqr/src/chain.rs, lines 247:4-296:5
-/
@[step]
theorem key_spec_equal_32 (self : chain.ChainEpochDirection) (ats : U32)
    (params : proto.pq_ratchet.ChainParams)
    (h_next_len : self.next.length = 32)
    (h_at_bound : ats.val ≤ U32.max - 108458770)
    (h_maxooo_bound : (chain.maxOoo params).val < 108458770)
    (h_kh_cap : self.prev.data.length + 36 * (ats.val - self.ctr.val) ≤ Usize.max)
    (h_prev_aligned : self.prev.data.length % 36 = 0)
    (h_prev_bound : self.prev.data.length ≤ Usize.max)
    (h_prev_ctr : self.prev.data.length ≤ 36 * self.ctr.val)
    (h_ooo_no_overflow : ats + (chain.maxOoo params).val ≤ U32.max) :
    key self ats params ⦃ (result : (core.result.Result (alloc.vec.Vec U8) Error) ×
        chain.ChainEpochDirection) =>
        -- Equal case: key already requested
      (ats = self.ctr →
          result.1 = core.result.Result.Err (Error.KeyAlreadyRequested ats) ∧
          result.2 = self) ⦄ := by
  apply WP.spec_mono (key_spec_all_32 self ats params h_next_len h_at_bound h_maxooo_bound
    h_kh_cap h_prev_aligned h_prev_bound h_prev_ctr h_ooo_no_overflow)
  exact fun _ h => h.1

/-- **Spec theorem for `spqr.chain.ChainEpochDirection.key`** (32-bit platform, greater case):

Proves that when `ats > self.ctr` and the jump exceeds `max_jump_or_default(params)`, the function
returns `(Err (Error.KeyJump self.ctr ats), self)` with the state unchanged.

Identical to `key_spec_greater` but with the tighter maxOoo bound `108458770` and no `h_platform`
hypothesis. Uses `gc_spec` (platform-independent) instead of `gc_spec_64`.

**Source**: spqr/src/chain.rs, lines 247:4-296:5
-/
@[step]
theorem key_spec_greater_32 (self : chain.ChainEpochDirection) (ats : U32)
    (params : proto.pq_ratchet.ChainParams)
    (h_next_len : self.next.length = 32)
    (h_at_bound : ats.val ≤ U32.max - 108458770)
    (h_maxooo_bound : (chain.maxOoo params).val < 108458770)
    (h_kh_cap : self.prev.data.length + 36 * (ats.val - self.ctr.val) ≤ Usize.max)
    (h_prev_aligned : self.prev.data.length % 36 = 0)
    (h_prev_bound : self.prev.data.length ≤ Usize.max)
    (h_prev_ctr : self.prev.data.length ≤ 36 * self.ctr.val)
    (h_ooo_no_overflow : ats + (chain.maxOoo params).val ≤ U32.max) :
    key self ats params ⦃
      (result : (core.result.Result (alloc.vec.Vec U8) Error) ×
        chain.ChainEpochDirection) =>
      (ats > self.ctr →
          ats.val - self.ctr.val > (chain.maxJump params).val →
          result.1 = core.result.Result.Err (Error.KeyJump self.ctr ats) ∧
          result.2 = self) ⦄ := by
  apply WP.spec_mono (key_spec_all_32 self ats params h_next_len h_at_bound h_maxooo_bound
    h_kh_cap h_prev_aligned h_prev_bound h_prev_ctr h_ooo_no_overflow)
  exact fun _ h => h.2.2.1

/-- **Spec theorem for `spqr.chain.ChainEpochDirection.key`** (32-bit platform, less case):

Proves the **less case** (`ats < self.ctr`): delegates to `KeyHistory.get` to retrieve a
previously-stored key. In all sub-cases, `result.2.ctr = self.ctr` and
`result.2.next = self.next` (only `prev` is modified). The domain-level result is one of:
  - `Err (Error.KeyTrimmed ats)` when `ats + maxOoo params < self.ctr`
    (key was garbage-collected), with `self.prev` unchanged.
  - `Err (Error.KeyAlreadyRequested ats)` when the key is within the OOO window but not found
    in history, with `self.prev` unchanged.
  - `Ok out` with `out.length = 32`, key found and removed from history
    (`result.2.prev.data.length = self.prev.data.length - 36`), and provenance:
    there exists a 36-aligned offset `off` in `self.prev.data` whose 4-byte tag matches `ats`
    and whose 32-byte payload equals `out`.

Identical to `key_spec_less` but with the tighter maxOoo bound `108458770` and no `h_platform`
hypothesis. Uses `gc_spec` (platform-independent) instead of `gc_spec_64`.

**Source**: spqr/src/chain.rs, lines 247:4-296:5
-/
@[step]
theorem key_spec_less_32 (self : chain.ChainEpochDirection) (ats : U32)
    (params : proto.pq_ratchet.ChainParams)
    (h_next_len : self.next.length = 32)
    (h_at_bound : ats.val ≤ U32.max - 108458770)
    (h_maxooo_bound : (chain.maxOoo params).val < 108458770)
    (h_kh_cap : self.prev.data.length + 36 * (ats.val - self.ctr.val) ≤ Usize.max)
    (h_prev_aligned : self.prev.data.length % 36 = 0)
    (h_prev_bound : self.prev.data.length ≤ Usize.max)
    (h_prev_ctr : self.prev.data.length ≤ 36 * self.ctr.val)
    (h_ooo_no_overflow : ats + (chain.maxOoo params).val ≤ U32.max) :
    key self ats params ⦃
      (result : (core.result.Result (alloc.vec.Vec U8) Error) ×
        chain.ChainEpochDirection) =>
      (ats < self.ctr →
          chain.cedKeyLessPost self ats params result.1 result.2) ⦄ := by
  apply WP.spec_mono (key_spec_all_32 self ats params h_next_len h_at_bound h_maxooo_bound
    h_kh_cap h_prev_aligned h_prev_bound h_prev_ctr h_ooo_no_overflow)
  exact fun _ h => h.2.1

/-- **Spec theorem for `spqr.chain.ChainEpochDirection.key`** (32-bit platform, greater-jump case):

Proves the **greater case with jump within budget** (`ats > self.ctr` and
`ats.val - self.ctr.val ≤ max_jump_or_default(params)`). Projection of
`key_spec_all_32`.

Identical to `key_spec_greater_jump` but with the tighter maxOoo bound `108458770` and no
`h_platform` hypothesis. Uses `gc_spec` (platform-independent) instead of `gc_spec_64`.

**Source**: spqr/src/chain.rs, lines 247:4-296:5
-/
@[step]
theorem key_spec_greater_jump_32 (self : chain.ChainEpochDirection) (ats : U32)
    (params : proto.pq_ratchet.ChainParams)
    (h_next_len : self.next.length = 32)
    (h_at_bound : ats.val ≤ U32.max - 108458770)
    (h_maxooo_bound : (chain.maxOoo params).val < 108458770)
    (h_kh_cap : self.prev.data.length + 36 * (ats.val - self.ctr.val) ≤ Usize.max)
    (h_prev_aligned : self.prev.data.length % 36 = 0)
    (h_prev_bound : self.prev.data.length ≤ Usize.max)
    (h_prev_ctr : self.prev.data.length ≤ 36 * self.ctr.val)
    (h_ooo_no_overflow : ats + (chain.maxOoo params).val ≤ U32.max) :
    key self ats params ⦃
      (result : (core.result.Result (alloc.vec.Vec U8) Error) ×
        chain.ChainEpochDirection) =>
      (∀ (h_gt : ats > self.ctr),
          ats.val - self.ctr.val ≤ (chain.maxJump params).val →
          chain.cedKeyAdvancePost self ats params result.1 result.2 h_gt) ⦄ := by
  apply WP.spec_mono (key_spec_all_32 self ats params h_next_len h_at_bound h_maxooo_bound
    h_kh_cap h_prev_aligned h_prev_bound h_prev_ctr h_ooo_no_overflow)
  exact fun _ h => h.2.2.2

/-- **Combined spec theorem for `spqr.chain.ChainEpochDirection.key`** (32-bit platform):

Combines the equal, less, greater, and greater-jump cases into a single postcondition
`chain.cedKeyPost self ats params result.1 result.2`.

Identical to `key_spec` but with the tighter maxOoo bound `108458770` and no `h_platform`
hypothesis. Uses `gc_spec` (platform-independent) instead of `gc_spec_64`.

**Source**: spqr/src/chain.rs, lines 247:4-296:5
-/
@[step]
theorem key_spec_32 (self : chain.ChainEpochDirection) (ats : U32)
    (params : proto.pq_ratchet.ChainParams)
    (h_next_len : self.next.length = 32)
    (h_at_bound : ats.val ≤ U32.max - 108458770)
    (h_maxooo_bound : (chain.maxOoo params).val < 108458770)
    (h_kh_cap : self.prev.data.length + 36 * (ats.val - self.ctr.val) ≤ Usize.max)
    (h_prev_aligned : self.prev.data.length % 36 = 0)
    (h_prev_bound : self.prev.data.length ≤ Usize.max)
    (h_prev_ctr : self.prev.data.length ≤ 36 * self.ctr.val)
    (h_ooo_no_overflow : ats + (chain.maxOoo params).val ≤ U32.max) :
    key self ats params ⦃ (result : (core.result.Result (alloc.vec.Vec U8) Error) ×
        chain.ChainEpochDirection) =>
      chain.cedKeyPost self ats params result.1 result.2 ⦄ := by
  exact key_spec_all_32 self ats params h_next_len h_at_bound h_maxooo_bound
    h_kh_cap h_prev_aligned h_prev_bound h_prev_ctr h_ooo_no_overflow

end spqr.chain.ChainEpochDirection
