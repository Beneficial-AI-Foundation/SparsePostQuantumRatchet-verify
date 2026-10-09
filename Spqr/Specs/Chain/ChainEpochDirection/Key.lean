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



/-- Value-level reading of `OrdU32.cmp a b = .lt` (and `.eq`, `.gt` below). -/
theorem ordU32_cmp_lt_val {a b : U32} (h : core.cmp.impls.OrdU32.cmp a b = Ordering.lt) :
    a.val < b.val := by
  simp only [core.cmp.impls.OrdU32.cmp, Nat.compare_eq_lt] at h; scalar_tac

theorem ordU32_cmp_eq_val {a b : U32} (h : core.cmp.impls.OrdU32.cmp a b = Ordering.eq) :
    a.val = b.val := by
  simp only [core.cmp.impls.OrdU32.cmp, Nat.compare_eq_eq] at h; scalar_tac

theorem ordU32_cmp_gt_val {a b : U32} (h : core.cmp.impls.OrdU32.cmp a b = Ordering.gt) :
    b.val < a.val := by
  simp only [core.cmp.impls.OrdU32.cmp, Nat.compare_eq_gt] at h; scalar_tac

/-! ### Shared tail of the advancing branch

In the `ats > self.ctr` branch (within the jump budget), `key` first picks a starting key
history `kh` (cleared when `ats` is beyond the out-of-order window, `self.prev` otherwise) and
then runs the same tail on it: `key_loop`, `gc`, `next_key_internal`, and the final `to_vec`.
`#decompose` extracts that tail into `keyAdvanceTail`, so its spec is proved once for an
arbitrary starting `kh` rather than once per branch. -/
set_option linter.hashCommand false in
#decompose key key_eq
  letAt 1 (branch 2 (letAt 2 (branch 1 (letRange 3 7)))) => keyAdvanceTail

/-- The tail of `key`'s advancing branch. -/
add_decl_doc keyAdvanceTail

/-- Postcondition of `keyAdvanceTail self ats params kh`, returning `(kh2, i5, v1, v2)`:
`chain.cedKeyAdvancePost` with the starting key history `kh0` replaced by `kh`, and without the
conjuncts that relate `kh` to `self.prev`. -/
def keyAdvanceTailPost (self : chain.ChainEpochDirection) (ats : U32)
    (params : proto.pq_ratchet.ChainParams) (kh : chain.KeyHistory)
    (kh2 : chain.KeyHistory) (i5 : U32) (v1 v2 : alloc.vec.Vec U8)
    (h_gt : ats > self.ctr) : Prop :=
  let loopSteps := ats.val - (self.ctr.val + 1)
  let loopSecret := chain.ChainEpochDirection.iterChainSecret self.next.val self.ctr.val loopSteps
  let ctrAts : U32 := ⟨ats.val, by scalar_tac⟩
  let finalOkm := nextKeyHkdfOutput loopSecret ctrAts
  let khPreGc := chain.ChainEpochDirection.iterKeyHistory
    self.next.val self.ctr.val ats.val params kh loopSteps
  let max_ooo : Nat := (chain.maxOoo params).val
  let trim_threshold : Nat := (max_ooo * 11 / 10 + 1) * 36
  let ctr_new : U32 := ⟨ats.val - 1, by scalar_tac⟩
  v1.length = 32 ∧
  v1.val = finalOkm.drop 32 ∧
  i5.val = ats.val ∧
  v2.length = 32 ∧
  v2.val = finalOkm.take 32 ∧
  kh2.data.length % 36 = 0 ∧
  kh2.data.length ≤ kh.data.length + 36 * (ats.val - self.ctr.val) ∧
  kh2.data.length ≤ Usize.max ∧
  kh2.data.length ≤ khPreGc.data.length ∧
  khPreGc.data.length % 36 = 0 ∧
  kh.data.length ≤ khPreGc.data.length ∧
  chain.keyPostGc ⟨i5, v2, kh2⟩ khPreGc max_ooo trim_threshold ctr_new

/-- **Spec for `keyAdvanceTail`** (64-bit platform), for any starting key history `kh` that is
36-aligned, holds at most one record per counter value below `self.ctr`, and leaves room for
the `ats - self.ctr` records the loop may add. -/
private theorem keyAdvanceTail_spec (self : chain.ChainEpochDirection) (ats : U32)
    (params : proto.pq_ratchet.ChainParams) (kh : chain.KeyHistory)
    (h_gt : ats > self.ctr)
    (h_next_len : self.next.length = 32)
    (h_at_bound : ats.val ≤ U32.max - 390451572)
    (h_maxooo_bound : (chain.maxOoo params).val < 390451572)
    (h_kh_cap : kh.data.length + 36 * (ats.val - self.ctr.val) ≤ Usize.max)
    (h_kh_aligned : kh.data.length % 36 = 0)
    (h_kh_ctr : kh.data.length ≤ 36 * self.ctr.val)
    (h_platform : System.Platform.numBits = 64) :
    keyAdvanceTail self ats params kh ⦃ (r : chain.KeyHistory × U32 × alloc.vec.Vec U8 ×
        alloc.vec.Vec U8) =>
      keyAdvanceTailPost self ats params kh r.1 r.2.1 r.2.2.1 r.2.2.2 h_gt ⦄ := by
  unfold keyAdvanceTail
  simp only [alloc.vec.Vec.deref_mut, lift]
  step*
  · rw [‹kh1 = _›]
    exact iterKeyHistory_data_length_mod_36 _ _ _ _ _ _ h_kh_aligned
  · have := maxOoo_if_eq params
    split at this <;> scalar_tac
  · exact key_gc_precond_no_clear { self with prev := kh } ats params i4 kh1 h_gt h_kh_ctr ‹_› ‹_›
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

attribute [local step] keyAdvanceTail_spec

/-- From the tail postcondition to `chain.cedKeyAdvancePost`, given how `key` picks the starting
key history `kh`: empty when `ats` is beyond the out-of-order window, `self.prev` otherwise. -/
theorem cedKeyAdvancePost_of_tail (self : chain.ChainEpochDirection) (ats : U32)
    (params : proto.pq_ratchet.ChainParams) (kh kh2 : chain.KeyHistory) (i5 : U32)
    (v1 v2 : alloc.vec.Vec U8) (h_gt : ats > self.ctr)
    (h_clear : self.ctr.val + (chain.maxOoo params).val < ats.val → kh.data.length = 0)
    (h_keep : ¬ self.ctr.val + (chain.maxOoo params).val < ats.val → kh = self.prev)
    (h_post : keyAdvanceTailPost self ats params kh kh2 i5 v1 v2 h_gt) :
    chain.cedKeyAdvancePost self ats params (.Ok v1) ⟨i5, v2, kh2⟩ h_gt := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h_post
  unfold chain.cedKeyAdvancePost
  by_cases hc : self.ctr.val + (chain.maxOoo params).val < ats.val
  · have hkh : kh = { data := alloc.vec.Vec.from [] (by simp) } := by
      have hlen := h_clear hc
      obtain ⟨d⟩ := kh
      congr 1
      apply alloc.vec.Vec.ext
      simpa [alloc.vec.Vec.length] using hlen
    subst hkh
    simp only [gt_iff_lt, if_pos hc]
    refine ⟨⟨v1, rfl, h1, h2⟩, h3, h4, h5, h6, h7, ?_, fun _ => ?_, h8, h9, h10, h11, h12⟩
    · simp only [alloc.vec.Vec.length] at h7 ⊢; simp at h7; omega
    · simp only [alloc.vec.Vec.length] at h7 ⊢; simp at h7; omega
  · have hkh := h_keep hc
    subst hkh
    simp only [gt_iff_lt, if_neg hc]
    exact ⟨⟨v1, rfl, h1, h2⟩, h3, h4, h5, h6, h7, h7, fun h => absurd h hc, h8, h9, h10, h11, h12⟩

/-- **Combined spec for all branches of `key`**: the full postcondition `chain.cedKeyPost`,
proved with a single symbolic execution of `key`.  The per-branch theorems below
(`key_spec_equal`, `key_spec_greater`, `key_spec_less`, `key_spec_greater_jump`, `key_spec`)
are projections of this one. -/
private theorem key_spec_all (self : chain.ChainEpochDirection) (ats : U32)
    (params : proto.pq_ratchet.ChainParams)
    (h_next_len : self.next.length = 32)
    (h_at_bound : ats.val ≤ U32.max - 390451572)
    (h_maxooo_bound : (chain.maxOoo params).val < 390451572)
    (h_kh_cap : self.prev.data.length + 36 * (ats.val - self.ctr.val) ≤ Usize.max)
    (h_prev_aligned : self.prev.data.length % 36 = 0)
    (h_prev_bound : self.prev.data.length ≤ Usize.max)
    (h_prev_ctr : self.prev.data.length ≤ 36 * self.ctr.val)
    (h_ooo_no_overflow : ats + (chain.maxOoo params).val ≤ U32.max)
    (h_platform : System.Platform.numBits = 64) :
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
  apply WP.spec_mono (key_spec_all self ats params h_next_len h_at_bound h_maxooo_bound
    h_kh_cap h_prev_aligned h_prev_bound h_prev_ctr h_ooo_no_overflow h_platform)
  exact fun _ h => h.1

@[step]
theorem key_spec_greater (self : chain.ChainEpochDirection) (ats : U32)
    (params : proto.pq_ratchet.ChainParams)
    (h_next_len : self.next.length = 32)
    (h_at_bound : ats.val ≤ U32.max - 390451572)
    (h_maxooo_bound : (chain.maxOoo params).val < 390451572)
    (h_kh_cap : self.prev.data.length + 36 * (ats.val - self.ctr.val) ≤ Usize.max)
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
  apply WP.spec_mono (key_spec_all self ats params h_next_len h_at_bound h_maxooo_bound
    h_kh_cap h_prev_aligned h_prev_bound h_prev_ctr h_ooo_no_overflow h_platform)
  exact fun _ h => h.2.2.1

@[step]
theorem key_spec_less (self : chain.ChainEpochDirection) (ats : U32)
    (params : proto.pq_ratchet.ChainParams)
    (h_next_len : self.next.length = 32)
    (h_at_bound : ats.val ≤ U32.max - 390451572)
    (h_maxooo_bound : (chain.maxOoo params).val < 390451572)
    (h_kh_cap : self.prev.data.length + 36 * (ats.val - self.ctr.val) ≤ Usize.max)
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
  apply WP.spec_mono (key_spec_all self ats params h_next_len h_at_bound h_maxooo_bound
    h_kh_cap h_prev_aligned h_prev_bound h_prev_ctr h_ooo_no_overflow h_platform)
  exact fun _ h => h.2.1

/-- **Spec theorem for `spqr.chain.ChainEpochDirection.key`** (greater-jump case):

Proves the **greater case with jump within budget** (`ats > self.ctr` and
`ats.val - self.ctr.val ≤ max_jump_or_default(params)`). Projection of `key_spec_all`.

**Source**: spqr/src/chain.rs, lines 247:4-296:5
-/
@[step]
theorem key_spec_greater_jump (self : chain.ChainEpochDirection) (ats : U32)
    (params : proto.pq_ratchet.ChainParams)
    (h_next_len : self.next.length = 32)
    (h_at_bound : ats.val ≤ U32.max - 390451572)
    (h_maxooo_bound : (chain.maxOoo params).val < 390451572)
    (h_kh_cap : self.prev.data.length + 36 * (ats.val - self.ctr.val) ≤ Usize.max)
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
  apply WP.spec_mono (key_spec_all self ats params h_next_len h_at_bound h_maxooo_bound
    h_kh_cap h_prev_aligned h_prev_bound h_prev_ctr h_ooo_no_overflow h_platform)
  exact fun _ h => h.2.2.2

@[step]
theorem key_spec (self : chain.ChainEpochDirection) (ats : U32)
    (params : proto.pq_ratchet.ChainParams)
    (h_next_len : self.next.length = 32)
    (h_at_bound : ats.val ≤ U32.max - 390451572)
    (h_maxooo_bound : (chain.maxOoo params).val < 390451572)
    (h_kh_cap : self.prev.data.length + 36 * (ats.val - self.ctr.val) ≤ Usize.max)
    (h_prev_aligned : self.prev.data.length % 36 = 0)
    (h_prev_bound : self.prev.data.length ≤ Usize.max)
    (h_prev_ctr : self.prev.data.length ≤ 36 * self.ctr.val)
    (h_ooo_no_overflow : ats + (chain.maxOoo params).val ≤ U32.max)
    (h_platform : System.Platform.numBits = 64) :
    key self ats params ⦃ (result : (core.result.Result (alloc.vec.Vec U8) Error) ×
        chain.ChainEpochDirection) =>
      chain.cedKeyPost self ats params result.1 result.2 ⦄ := by
  exact key_spec_all self ats params h_next_len h_at_bound h_maxooo_bound
    h_kh_cap h_prev_aligned h_prev_bound h_prev_ctr h_ooo_no_overflow h_platform

end spqr.chain.ChainEpochDirection
