/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import Spqr.Specs.Chain.ChainEpochDirection.NextKey
import Spqr.Specs.Chain.KeyHistory.Get
import Spqr.Specs.Chain.KeyHistory.Clear
import Spqr.Specs.Chain.KeyHistory.Gc
import Spqr.Specs.Chain.ChainParams.MaxJumpOrDefault
public import Spqr.Specs.Chain.Chain.Defs
import Spqr.Specs.Chain.KeyHistory.Add
import Spqr.Specs.Chain.ChainParams.MaxOooKeysOrDefault
import Spqr.Specs.Chain.DEFAULT_CHAIN_PARAMS
import Spqr.Specs.Chain.ChainEpochDirection.NextKeyInternal
/-!
# Spec theorem for `spqr::chain::{spqr::chain::ChainEpochDirection}::key`

`ChainEpochDirection::key` compares the requested counter `ats` with the current counter
`self.ctr`:

  * `ats < self.ctr`: the key is looked up (and removed) in the key history (`KeyHistory::get`);
  * `ats = self.ctr`: the key has already been requested;
  * `ats > self.ctr` beyond the jump budget: error;
  * `ats > self.ctr` within the jump budget: the chain advances to `ats`.  `key` picks a
    starting key history (cleared when `ats` is beyond the out-of-order window, `self.prev`
    otherwise), runs the advancing loop `key_loop`, garbage-collects the history (`gc`) and
    derives the final key with `next_key_internal`.

The proof follows the same structure:

  1. `key_loop.body_spec` / `key_loop.body_done`: one iteration of the loop.
  2. `KeyLoopInv` and `key_loop_spec_core`: the loop, via `loop.spec_decr_nat`.
  3. `keyAdvanceTail_spec_core`: the shared tail of the advancing branch (extracted with
     `#decompose`).
  4. `key_spec_all_core`: `key` itself, one case per comparison outcome, each closed by an
     introduction lemma for `chain.cedKeyPost`.

All of these are platform-independent; `key_spec` (here) and `key_spec_32` (`Key32.lean`)
instantiate them.

**Source**: spqr/src/chain.rs, lines 248:4-297:5 -/

@[expose] public section

open Aeneas Aeneas.Std Result spqr crypto

namespace spqr.chain.ChainEpochDirection

/-! ## Value-level helpers -/

private theorem max_ooo_keys_or_default_eq (params : proto.pq_ratchet.ChainParams) :
    chain.ChainParams.max_ooo_keys_or_default params = ok (chain.maxOoo params) := by
  unfold chain.ChainParams.max_ooo_keys_or_default chain.maxOoo; split <;> rfl

private theorem max_jump_or_default_eq (params : proto.pq_ratchet.ChainParams) :
    chain.ChainParams.max_jump_or_default params = ok (chain.maxJump params) := by
  unfold chain.ChainParams.max_jump_or_default chain.maxJump; split <;> rfl

private theorem ordU32_cmp_eq (a b : U32) :
    core.cmp.impls.OrdU32.cmp a b = compare a.val b.val := by
  simp [core.cmp.impls.OrdU32.cmp]

/-- The `max_ooo` value computed by `gc` is `chain.maxOoo`. -/
private theorem maxOoo_if_eq (params : proto.pq_ratchet.ChainParams) :
    (if 0#u32 < params.max_ooo_keys then params.max_ooo_keys.val else 2000) =
    (chain.maxOoo params).val := by
  unfold chain.maxOoo; split <;> simp_all [DEFAULT_CHAIN_PARAMS_spec]

/-- `(chain.maxOoo params).val < bound` implies `params.max_ooo_keys.val < bound`. -/
private theorem maxOoo_imp_raw_ooo (params : proto.pq_ratchet.ChainParams) (bound : Nat)
    (h : (chain.maxOoo params).val < bound) : params.max_ooo_keys.val < bound := by
  unfold chain.maxOoo at h
  by_cases hpos : params.max_ooo_keys > 0#u32
  · simp only [hpos, ↓reduceIte] at h; exact h
  · simp only [gt_iff_lt, UScalar.lt_equiv, UScalar.ofNatCore_val_eq, not_lt,
      Nat.le_zero] at hpos
    omega

/-! ## Functional model: one step of `iterChainSecret` / `iterKeyHistoryData` -/

private theorem iterChainSecret_succ (secret : List U8) (base n : Nat)
    (hb : base + n + 1 ≤ U32.max) :
    iterChainSecret secret base (n + 1) =
      (nextKeyHkdfOutput (iterChainSecret secret base n)
        ⟨base + n + 1, by scalar_tac⟩).take 32 := by
  rw [iterChainSecret, dif_pos hb]

private theorem iterKeyHistoryData_succ (secret : List U8) (base target : Nat)
    (params : proto.pq_ratchet.ChainParams) (d : List U8) (n : Nat)
    (hb : base + n + 1 ≤ U32.max) :
    iterKeyHistoryData secret base target params d (n + 1) =
      let ctr : U32 := ⟨base + n + 1, by scalar_tac⟩
      let okm := nextKeyHkdfOutput (iterChainSecret secret base n) ctr
      if base + n + 1 + (chain.maxOoo params).val ≥ target then
        iterKeyHistoryData secret base target params d n ++
          (core.num.U32.to_be_bytes ctr).val ++ okm.drop 32
      else iterKeyHistoryData secret base target params d n := by
  rw [iterKeyHistoryData, dif_pos hb]

/-- A key history whose data is `iterKeyHistoryData … n` is `iterKeyHistory … n` (its data
fits in `usize`, so `iterKeyHistory` is not in its junk branch). -/
private theorem eq_iterKeyHistory_of_data {secret : List U8} {base target : Nat}
    {params : proto.pq_ratchet.ChainParams} {kh kh' : chain.KeyHistory} {n : Nat}
    (h : kh'.data.val = iterKeyHistoryData secret base target params kh.data.val n) :
    kh' = iterKeyHistory secret base target params kh n := by
  have hlen : (iterKeyHistoryData secret base target params kh.data.val n).length ≤
      Usize.max := h ▸ kh'.data.property
  obtain ⟨d⟩ := kh'
  simp only [iterKeyHistory, dif_pos hlen, chain.KeyHistory.mk.injEq]
  exact alloc.vec.Vec.ext _ _ (by simpa [alloc.vec.Vec.from_val] using h)

/-! ## The loop body -/

namespace key_loop

/-- **Spec for `key_loop.body`, continue case** (`at1 > i + 1`): `next_key_internal` derives
`okm = nextKeyHkdfOutput v.val (i + 1)`; the new chain secret is `okm.take 32`, and the derived
key `okm.drop 32` (tagged with the counter `i + 1`) is appended to the key history iff
`i + 1 + maxOoo ≥ at1`. -/
private theorem body_spec
    (at1 : U32) (params : proto.pq_ratchet.ChainParams)
    (i : U32) (v : alloc.vec.Vec U8) (kh : chain.KeyHistory)
    (h_v_len : v.length = 32)
    (h_kh_cap : kh.data.length + 36 ≤ Usize.max)
    (h_ooo : i.val + 1 + (chain.maxOoo params).val ≤ U32.max)
    (h_cont : at1.val > i.val + 1) :
    body at1 params i v kh ⦃ cf => ∃ i2 v2 kh2, cf = ControlFlow.cont (i2, v2, kh2) ∧
      i2.val = i.val + 1 ∧
      v2.length = 32 ∧
      (let ctr : U32 := ⟨i.val + 1, by scalar_tac⟩
       let okm := nextKeyHkdfOutput v.val ctr
       v2.val = okm.take 32 ∧
       if i.val + 1 + (chain.maxOoo params).val ≥ at1.val then
         kh2.data.length = kh.data.length + 36 ∧
         kh2.data.val = kh.data.val ++ (core.num.U32.to_be_bytes ctr).val ++ okm.drop 32
       else kh2 = kh) ⦄ := by
  unfold body
  simp only [alloc.vec.Vec.deref_mut, lift, max_ooo_keys_or_default_eq, bind_ok]
  step as ⟨i1, h_i1⟩
  rw [if_pos (show at1 > i1 from (by omega : i1.val < at1.val))]
  have hvs : v.slice.length = 32 := h_v_len
  step as ⟨k, s1, i2, h_i2, h_k1, _, h_s1_len, h_s1, h_k2⟩
  step as ⟨i4, h_i4⟩
  by_cases hc : i.val + 1 + (chain.maxOoo params).val ≥ at1.val
  · rw [if_pos (show i4 ≥ at1 from (by omega : at1.val ≤ i4.val))]
    step as ⟨kh1, h_kh1_len, h_kh1, _⟩
    have hk1 : k.1 = ⟨i.val + 1, by scalar_tac⟩ := UScalar.val_eq_imp _ _ (by rw [h_k1]; rfl)
    refine ⟨_, _, _, rfl, h_i2, h_s1_len.trans hvs, h_s1, ?_⟩
    rw [if_pos hc]
    exact ⟨h_kh1_len, by rw [h_kh1, hk1, h_k2]; rfl⟩
  · rw [if_neg (show ¬ i4 ≥ at1 from fun h => by have : at1.val ≤ i4.val := h; omega),
      WP.spec_ok]
    refine ⟨_, _, _, rfl, h_i2, h_s1_len.trans hvs, h_s1, ?_⟩
    rw [if_neg hc]

/-- **Spec for `key_loop.body`, done case** (`at1 ≤ i + 1`): the state is returned unchanged. -/
private theorem body_done
    (at1 : U32) (params : proto.pq_ratchet.ChainParams)
    (i : U32) (v : alloc.vec.Vec U8) (kh : chain.KeyHistory)
    (h_i : i.val < U32.max) (h_done : ¬(at1.val > i.val + 1)) :
    body at1 params i v kh ⦃ cf => cf = ControlFlow.done (i, v, kh) ⦄ := by
  unfold body
  step as ⟨i1, h_i1⟩
  rw [if_neg (show ¬ at1 > i1 from fun h => by have : i1.val < at1.val := h; omega)]
  simp

end key_loop

/-! ## The loop

`key_loop` advances the counter from `i` towards `at1 - 1`.  After `n` iterations the chain secret
is `iterChainSecret v i n` and the key-history data is `iterKeyHistoryData v i at1 params kh n`. -/

/-- Loop invariant of `key_loop`, for the state `(i', v', kh')` reached from `(i, v, kh)`. -/
private structure KeyLoopInv (at1 : U32) (params : proto.pq_ratchet.ChainParams)
    (i : U32) (v : alloc.vec.Vec U8) (kh : chain.KeyHistory)
    (i' : U32) (v' : alloc.vec.Vec U8) (kh' : chain.KeyHistory) : Prop where
  ctr_ge : i.val ≤ i'.val
  ctr_lt : i'.val < U32.max
  ctr_le : at1.val > i.val + 1 → i'.val + 1 ≤ at1.val
  zero : at1.val ≤ i.val + 1 → i' = i ∧ v' = v ∧ kh' = kh
  v_len : v'.length = 32
  v_val : v'.val = iterChainSecret v.val i.val (i'.val - i.val)
  kh_val : kh'.data.val = iterKeyHistoryData v.val i.val at1.val params kh.data.val (i'.val - i.val)
  kh_lb : kh.data.length ≤ kh'.data.length
  kh_ub : kh'.data.length ≤ kh.data.length + 36 * (i'.val - i.val)
  kh_cap : kh'.data.length + 36 * (at1.val - i'.val) ≤ Usize.max

private theorem KeyLoopInv.init (at1 : U32) (params : proto.pq_ratchet.ChainParams)
    (i : U32) (v : alloc.vec.Vec U8) (kh : chain.KeyHistory)
    (h_v_len : v.length = 32)
    (h_kh_cap : kh.data.length + 36 * (at1.val - i.val) ≤ Usize.max)
    (h_i : i.val < U32.max) :
    KeyLoopInv at1 params i v kh i v kh where
  ctr_ge := le_refl _
  ctr_lt := h_i
  ctr_le := fun _ => by omega
  zero := fun _ => ⟨rfl, rfl, rfl⟩
  v_len := h_v_len
  v_val := by simp [iterChainSecret]
  kh_val := by simp [iterKeyHistoryData]
  kh_lb := le_refl _
  kh_ub := by simp
  kh_cap := h_kh_cap

/-- One continue step of the loop preserves the invariant. -/
private theorem KeyLoopInv.step {at1 : U32} {params : proto.pq_ratchet.ChainParams}
    {i : U32} {v : alloc.vec.Vec U8} {kh : chain.KeyHistory}
    {i' i'' : U32} {v' v'' : alloc.vec.Vec U8} {kh' kh'' : chain.KeyHistory}
    (h_ooo : at1.val + (chain.maxOoo params).val ≤ U32.max)
    (hinv : KeyLoopInv at1 params i v kh i' v' kh')
    (h_cont : at1.val > i'.val + 1)
    (h_i'' : i''.val = i'.val + 1)
    (h_v_len : v''.length = 32)
    (h_post : let ctr : U32 := ⟨i'.val + 1, by scalar_tac⟩
      let okm := nextKeyHkdfOutput v'.val ctr
      v''.val = okm.take 32 ∧
      if i'.val + 1 + (chain.maxOoo params).val ≥ at1.val then
        kh''.data.length = kh'.data.length + 36 ∧
        kh''.data.val = kh'.data.val ++ (core.num.U32.to_be_bytes ctr).val ++ okm.drop 32
      else kh'' = kh') :
    KeyLoopInv at1 params i v kh i'' v'' kh'' := by
  dsimp only at h_post
  obtain ⟨h_v'', h_kh''⟩ := h_post
  have h_le := hinv.ctr_ge
  have hn : i''.val - i.val = (i'.val - i.val) + 1 := by omega
  have h_len : kh'.data.length ≤ kh''.data.length ∧ kh''.data.length ≤ kh'.data.length + 36 := by
    split_ifs at h_kh''
    · omega
    · subst h_kh''; omega
  have := hinv.ctr_lt; have := hinv.kh_lb; have := hinv.kh_ub; have := hinv.kh_cap
  exact {
    ctr_ge := by omega
    ctr_lt := by omega
    ctr_le := fun _ => by omega
    zero := fun h => absurd h (by omega)
    v_len := h_v_len
    v_val := by
      rw [hn, iterChainSecret_succ _ _ _ (by omega)]
      simp only [Nat.add_sub_cancel' h_le, ← hinv.v_val]
      exact h_v''
    kh_val := by
      rw [hn, iterKeyHistoryData_succ _ _ _ _ _ _ (by omega)]
      simp only [Nat.add_sub_cancel' h_le, ← hinv.v_val, ← hinv.kh_val]
      by_cases hc : i'.val + 1 + (chain.maxOoo params).val ≥ at1.val
      · rw [if_pos hc] at h_kh'' ⊢; exact h_kh''.2
      · rw [if_neg hc] at h_kh'' ⊢; rw [h_kh'']
    kh_lb := by omega
    kh_ub := by omega
    kh_cap := by omega }

/-- Platform-independent spec of `key_loop`: the only arithmetic fact needed is that
`at1 + maxOoo` fits in `u32`. -/
private theorem key_loop_spec_core
    (at1 : U32) (params : proto.pq_ratchet.ChainParams)
    (i : U32) (v : alloc.vec.Vec U8) (kh : chain.KeyHistory)
    (h_v_len : v.length = 32)
    (h_ooo : at1.val + (chain.maxOoo params).val ≤ U32.max)
    (h_kh_cap : kh.data.length + 36 * (at1.val - i.val) ≤ Usize.max)
    (h_i_bound : i.val < U32.max) :
    key_loop i v kh at1 params ⦃ (r : U32 × (alloc.vec.Vec U8) × chain.KeyHistory) =>
      let steps := at1.val - (i.val + 1)
      (i.val < at1.val → r.1.val + 1 = at1.val) ∧
      r.2.1.length = 32 ∧
      r.2.1.val = iterChainSecret v.val i.val steps ∧
      r.2.2.data.val = iterKeyHistoryData v.val i.val at1.val params kh.data.val steps ∧
      kh.data.length ≤ r.2.2.data.length ∧
      r.2.2.data.length ≤ kh.data.length + 36 * (at1.val - i.val) ⦄ := by
  unfold key_loop
  apply loop.spec_decr_nat
    (measure := fun (s : U32 × (alloc.vec.Vec U8) × chain.KeyHistory) => at1.val - s.1.val)
    (inv := fun s => KeyLoopInv at1 params i v kh s.1 s.2.1 s.2.2)
  · rintro ⟨i', v', kh'⟩ (hinv : KeyLoopInv at1 params i v kh i' v' kh')
    have := hinv.ctr_lt; have := hinv.kh_cap
    by_cases h_cont : at1.val > i'.val + 1
    · apply WP.spec_mono (key_loop.body_spec at1 params i' v' kh' hinv.v_len (by omega)
        (by omega) h_cont)
      rintro _ ⟨i'', v'', kh'', rfl, h_i'', h_v_len, h_post⟩
      dsimp only
      exact ⟨KeyLoopInv.step h_ooo hinv h_cont h_i'' h_v_len h_post, by omega⟩
    · apply WP.spec_mono (key_loop.body_done at1 params i' v' kh' hinv.ctr_lt h_cont)
      rintro _ rfl
      dsimp only
      -- the loop exits at `i' = at1 - 1`, or at once if `at1 ≤ i + 1`
      have h_exit : i'.val + 1 = at1.val ∨ (at1.val ≤ i.val + 1 ∧ i'.val = i.val) := by
        by_cases hz : at1.val ≤ i.val + 1
        · exact Or.inr ⟨hz, by rw [(hinv.zero hz).1]⟩
        · have := hinv.ctr_le (by omega); omega
      have h_steps : i'.val - i.val = at1.val - (i.val + 1) := by omega
      exact ⟨fun _ => by omega, hinv.v_len, h_steps ▸ hinv.v_val, h_steps ▸ hinv.kh_val,
        hinv.kh_lb, le_trans hinv.kh_ub (by omega)⟩
  · exact KeyLoopInv.init at1 params i v kh h_v_len h_kh_cap h_i_bound

/-! ## The shared tail of the advancing branch

In the `ats > self.ctr` branch (within the jump budget), `key` first picks a starting key
history `kh` and then runs the same tail on it: `key_loop`, `gc`, `next_key_internal`, and the
final `to_vec`.  `#decompose` extracts that tail into `keyAdvanceTail`, so its spec is proved
once for an arbitrary starting `kh` rather than once per branch. -/
set_option linter.hashCommand false in
#decompose key key_eq
  letAt 1 (branch 2 (letAt 2 (branch 1 (letRange 3 7)))) => keyAdvanceTail

/-- The tail of `key`'s advancing branch. -/
add_decl_doc keyAdvanceTail

/-- Postcondition of `keyAdvanceTail self ats params kh`, returning `(kh2, i5, v1, v2)`:
`chain.cedKeyAdvancePost` with the starting key history `kh0` replaced by `kh`, and without the
conjuncts that relate `kh` to `self.prev`. -/
private def keyAdvanceTailPost (self : chain.ChainEpochDirection) (ats : U32)
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

/-- The GC precondition of the tail: when the trim threshold is reached, `maxOoo ≤ ats - 1`.
The pre-GC history holds at most `36 * (ats - 1)` bytes: the starting history `kh` at most
`36 * ctr` (`h_kh_ctr`), and the loop adds at most 36 bytes per counter value in
`(ctr, ats)`. -/
private theorem gc_precond (ctr ats i4 : U32) (params : proto.pq_ratchet.ChainParams)
    (kh kh1 : chain.KeyHistory)
    (h_gt : ctr.val < ats.val)
    (h_kh_ctr : kh.data.length ≤ 36 * ctr.val)
    (h_i4 : i4.val + 1 = ats.val)
    (h_ub : kh1.data.length ≤ kh.data.length + 36 * (ats.val - ctr.val)) :
    let m := if 0#u32 < params.max_ooo_keys then params.max_ooo_keys.val else 2000
    (m * 11 / 10 + 1) * 36 ≤ kh1.data.length → m ≤ i4.val := by
  intro m h_trim
  have hg : m ≤ m * 11 / 10 := by omega
  omega

/-- Repackaging of the facts produced by symbolically executing `keyAdvanceTail` into
`keyAdvanceTailPost`. -/
private theorem keyAdvanceTailPost_of_parts (self : chain.ChainEpochDirection) (ats : U32)
    (params : proto.pq_ratchet.ChainParams) (kh : chain.KeyHistory) (h_gt : ats > self.ctr)
    (h_kh_aligned : kh.data.length % 36 = 0)
    (i4 i5 : U32) (v v1 : alloc.vec.Vec U8) (kh1 kh2 : chain.KeyHistory)
    (s1 : Slice U8) (a : Std.Array U8 32#usize)
    (h_i4 : i4.val + 1 = ats.val)
    (h_v : v.val = iterChainSecret self.next.val self.ctr.val (ats.val - (self.ctr.val + 1)))
    (h_kh1 : kh1.data.val = iterKeyHistoryData self.next.val self.ctr.val ats.val params
      kh.data.val (ats.val - (self.ctr.val + 1)))
    (h_kh1_lb : kh.data.length ≤ kh1.data.length)
    (h_kh1_ub : kh1.data.length ≤ kh.data.length + 36 * (ats.val - self.ctr.val))
    (h_gc : kh1.GcPost i4 params kh2)
    (h_i5 : i5.val = i4.val + 1)
    (h_s1_len : s1.length = v.slice.length)
    (h_s1 : s1.val = (nextKeyHkdfOutput v.slice.val ⟨i4.val + 1, by scalar_tac⟩).take 32)
    (h_a : a.val = (nextKeyHkdfOutput v.slice.val ⟨i4.val + 1, by scalar_tac⟩).drop 32)
    (h_v_len : v.length = 32)
    (h_v1 : a.to_slice = v1.slice) :
    keyAdvanceTailPost self ats params kh kh2 i5 v1 { slice := s1 } h_gt := by
  have h_kh1_eq := eq_iterKeyHistory_of_data h_kh1
  subst h_kh1_eq
  unfold chain.KeyHistory.GcPost at h_gc
  obtain ⟨g1, g2, g3, g4⟩ := h_gc
  rw [maxOoo_if_eq] at g3 g4
  have hv1 : v1.val = a.val := by simp [alloc.vec.Vec.val, ← h_v1]
  refine ⟨?_, ?_, by omega, h_s1_len.trans h_v_len, ?_, g1, le_trans g2 h_kh1_ub,
    kh2.data.property, g2, iterKeyHistory_data_length_mod_36 _ _ _ _ _ _ h_kh_aligned, h_kh1_lb,
    chain.keyPostGc_of_GcPost _ _ _ _ _ (show i4.val = ats.val - 1 by omega) g2 g3 g4⟩
  · simp [alloc.vec.Vec.length, hv1]
  · rw [hv1, h_a]; simp only [h_i4, ← h_v]; rfl
  · change s1.val = _
    rw [h_s1]; simp only [h_i4, ← h_v]; rfl

/-- **Spec for `keyAdvanceTail`**, for any starting key history `kh` that is 36-aligned, holds at
most `36 * self.ctr` bytes, and leaves room for the `ats - self.ctr` records the loop may add.
Platform-independent: the arithmetic facts needed are that `ats + maxOoo` fits in `u32`, and
the two bounds `gc` needs (`h_raw_ooo`: `max_ooo * 11` fits in `u32`; `h_fit`: the trim
threshold fits in `usize`). -/
private theorem keyAdvanceTail_spec_core (self : chain.ChainEpochDirection) (ats : U32)
    (params : proto.pq_ratchet.ChainParams) (kh : chain.KeyHistory)
    (h_gt : ats > self.ctr)
    (h_next_len : self.next.length = 32)
    (h_ooo : ats.val + (chain.maxOoo params).val ≤ U32.max)
    (h_raw_ooo : params.max_ooo_keys.val < 390451572)
    (h_fit : (params.max_ooo_keys.val * 11 / 10 + 1) * 36 ≤ Usize.max)
    (h_kh_cap : kh.data.length + 36 * (ats.val - self.ctr.val) ≤ Usize.max)
    (h_kh_aligned : kh.data.length % 36 = 0)
    (h_kh_ctr : kh.data.length ≤ 36 * self.ctr.val) :
    keyAdvanceTail self ats params kh ⦃ (r : chain.KeyHistory × U32 × alloc.vec.Vec U8 ×
        alloc.vec.Vec U8) =>
      keyAdvanceTailPost self ats params kh r.1 r.2.1 r.2.2.1 r.2.2.2 h_gt ⦄ := by
  unfold keyAdvanceTail
  simp only [alloc.vec.Vec.deref_mut, lift]
  have h_gt' : self.ctr.val < ats.val := h_gt
  step with key_loop_spec_core as ⟨i4, v, kh1, h_i4, h_v_len, h_v, h_kh1, h_kh1_lb, h_kh1_ub⟩
  have h_i4' : i4.val + 1 = ats.val := h_i4 h_gt'
  -- the preconditions of `gc` and `next_key_internal`, stated up front for `step`
  have : kh1.data.length % 36 = 0 := by
    have : kh.data.val.length % 36 = 0 := h_kh_aligned
    simpa [alloc.vec.Vec.length, h_kh1] using iterKeyHistoryData_length_mod_36 _ _ _ _ _ _ this
  have := gc_precond self.ctr ats i4 params kh kh1 h_gt' h_kh_ctr h_i4' h_kh1_ub
  have : v.slice.length = 32 := h_v_len
  have : i4 < U32.max := by omega
  step with chain.KeyHistory.gc_spec_core as ⟨kh2, h_gc⟩
  step as ⟨_, a, s1, i5, h_i5, _, _, h_s1_len, h_s1, h_a⟩
  step as ⟨v1, h_v1⟩
  exact keyAdvanceTailPost_of_parts self ats params kh h_gt h_kh_aligned i4 i5 v v1 kh1 kh2 s1 a
    h_i4' h_v h_kh1 h_kh1_lb h_kh1_ub h_gc h_i5 h_s1_len h_s1 h_a h_v_len h_v1

/-! ## `key` -/

/-- From the tail postcondition to `chain.cedKeyAdvancePost`, given how `key` picks the starting
key history `kh`: empty when `ats` is beyond the out-of-order window, `self.prev` otherwise. -/
private theorem cedKeyAdvancePost_of_tail (self : chain.ChainEpochDirection) (ats : U32)
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
    have h7' : kh2.data.length ≤ 36 * (ats.val - self.ctr.val) := by
      simp only [alloc.vec.Vec.length] at h7 ⊢; simp at h7; omega
    exact ⟨⟨v1, rfl, h1, h2⟩, h3, h4, h5, h6, h7, by omega, fun _ => h7', h8, h9, h10, h11, h12⟩
  · have hkh := h_keep hc
    subst hkh
    simp only [gt_iff_lt, if_neg hc]
    exact ⟨⟨v1, rfl, h1, h2⟩, h3, h4, h5, h6, h7, h7, fun h => absurd h hc, h8, h9, h10, h11, h12⟩

/-- `KeyHistory::get`'s postcondition, lifted to `chain.cedKeyLessPost`. -/
private theorem cedKeyLessPost_of_get (self : chain.ChainEpochDirection) (ats : U32)
    (params : proto.pq_ratchet.ChainParams)
    (r : core.result.Result (alloc.vec.Vec U8) Error) (kh : chain.KeyHistory)
    (h_get : match r with
      | core.result.Result.Err e =>
          (e = Error.KeyTrimmed ats ∧ ats + (chain.maxOoo params).val < self.ctr ∧
            kh = self.prev) ∨
          (e = Error.KeyAlreadyRequested ats ∧
           self.ctr ≤ ats + (chain.maxOoo params).val ∧
           kh = self.prev ∧
           (∀ k, k + 36 ≤ self.prev.data.length → k % 36 = 0 →
             self.prev.data.val.slice k (k + 4) ≠ core.num.U32.to_be_bytes ats))
      | core.result.Result.Ok out =>
          self.ctr ≤ ats + (chain.maxOoo params).val ∧
          ∃ off, off % 36 = 0 ∧
            off + 36 ≤ self.prev.data.length ∧
            self.prev.data.val.slice off (off + 4) = (core.num.U32.to_be_bytes ats).val ∧
            (∀ k, k < off → k % 36 = 0 →
              self.prev.data.val.slice k (k + 4) ≠ (core.num.U32.to_be_bytes ats).val) ∧
            out.length = 32 ∧
            out = self.prev.data.val.slice (off + 4) (off + 36) ∧
            kh.data.length = self.prev.data.length - 36 ∧
            kh.data.length ≤ Usize.max ∧
            kh.data.length % 36 = 0 ∧
            (∀ j, j < off → kh.data[j]! = self.prev.data[j]!) ∧
            (off + 36 < self.prev.data.length →
              kh.data = (self.prev.data.val.setSlice! off
                    (self.prev.data.val.drop (self.prev.data.length - 36))).take
                      (self.prev.data.length - 36)) ∧
            (off + 36 = self.prev.data.length →
              kh.data = self.prev.data.val.take off)) :
    chain.cedKeyLessPost self ats params r { self with prev := kh } := by
  refine ⟨rfl, rfl, ?_⟩
  cases r with
  | Err _ => exact h_get
  | Ok out =>
    obtain ⟨hle, off, hmod, hbound, hslice, hfirst, hlen, hout, hkhlen, _,
      hkhalign, hpres, hswap, htail⟩ := h_get
    exact ⟨hle, hlen, hkhlen, hkhalign, off, hmod, hbound, hslice, hfirst, hout,
      hpres, hswap, htail⟩

/-! ### Introduction lemmas for `chain.cedKeyPost`, one per case of `key` -/

private theorem cedKeyPost_of_lt {self self' : chain.ChainEpochDirection} {ats : U32}
    {params : proto.pq_ratchet.ChainParams} {r : core.result.Result (alloc.vec.Vec U8) Error}
    (h : ats.val < self.ctr.val) (hp : chain.cedKeyLessPost self ats params r self') :
    chain.cedKeyPost self ats params r self' := by
  refine ⟨fun he => ?_, fun _ => hp, fun hg => ?_, fun hg => ?_⟩
  · exact absurd (UScalar.val_eq_of_eq he) (by omega)
  all_goals have : self.ctr.val < ats.val := hg; omega

private theorem cedKeyPost_of_eq {self : chain.ChainEpochDirection} {ats : U32}
    {params : proto.pq_ratchet.ChainParams} (h : ats.val = self.ctr.val) :
    chain.cedKeyPost self ats params (.Err (Error.KeyAlreadyRequested ats)) self := by
  refine ⟨fun _ => ⟨rfl, rfl⟩, fun hl => ?_, fun hg => ?_, fun hg => ?_⟩
  · have : ats.val < self.ctr.val := hl; omega
  all_goals have : self.ctr.val < ats.val := hg; omega

private theorem cedKeyPost_of_jump {self : chain.ChainEpochDirection} {ats : U32}
    {params : proto.pq_ratchet.ChainParams} (hgt : self.ctr.val < ats.val)
    (hj : (chain.maxJump params).val < ats.val - self.ctr.val) :
    chain.cedKeyPost self ats params (.Err (Error.KeyJump self.ctr ats)) self := by
  refine ⟨fun he => ?_, fun hl => ?_, fun _ _ => ⟨rfl, rfl⟩, fun _ hj' => ?_⟩
  · exact absurd (UScalar.val_eq_of_eq he) (by omega)
  · have : ats.val < self.ctr.val := hl; omega
  · omega

private theorem cedKeyPost_of_advance {self self' : chain.ChainEpochDirection} {ats : U32}
    {params : proto.pq_ratchet.ChainParams} {r : core.result.Result (alloc.vec.Vec U8) Error}
    (hgt : self.ctr.val < ats.val) (hj : ats.val - self.ctr.val ≤ (chain.maxJump params).val)
    (hp : ∀ h_gt : ats > self.ctr, chain.cedKeyAdvancePost self ats params r self' h_gt) :
    chain.cedKeyPost self ats params r self' := by
  refine ⟨fun he => ?_, fun hl => ?_, fun _ hj' => ?_, fun h_gt _ => hp h_gt⟩
  · exact absurd (UScalar.val_eq_of_eq he) (by omega)
  · have : ats.val < self.ctr.val := hl; omega
  · omega

/-- **Combined spec for all branches of `key`**: the full postcondition `chain.cedKeyPost`.
Platform-independent: instantiated by `key_spec` (64-bit) and `key_spec_32` (32-bit). -/
private theorem key_spec_all_core (self : chain.ChainEpochDirection) (ats : U32)
    (params : proto.pq_ratchet.ChainParams)
    (h_next_len : self.next.length = 32)
    (h_raw_ooo : params.max_ooo_keys.val < 390451572)
    (h_fit : (params.max_ooo_keys.val * 11 / 10 + 1) * 36 ≤ Usize.max)
    (h_kh_cap : self.prev.data.length + 36 * (ats.val - self.ctr.val) ≤ Usize.max)
    (h_prev_aligned : self.prev.data.length % 36 = 0)
    (h_prev_ctr : self.prev.data.length ≤ 36 * self.ctr.val)
    (h_ooo_no_overflow : ats + (chain.maxOoo params).val ≤ U32.max) :
    key self ats params ⦃ (result : (core.result.Result (alloc.vec.Vec U8) Error) ×
        chain.ChainEpochDirection) =>
      chain.cedKeyPost self ats params result.1 result.2 ⦄ := by
  rw [key_eq]
  simp only [lift, ordU32_cmp_eq, max_jump_or_default_eq, max_ooo_keys_or_default_eq, bind_ok]
  rcases Nat.lt_trichotomy ats.val self.ctr.val with hlt | heq | hgt
  · -- `ats < self.ctr`: look the key up in the history
    simp only [Nat.compare_eq_lt.mpr hlt]
    have := self.prev.data.property
    step as ⟨r, kh, h_get⟩
    exact cedKeyPost_of_lt hlt (cedKeyLessPost_of_get self ats params r kh h_get)
  · -- `ats = self.ctr`: already requested
    simp only [Nat.compare_eq_eq.mpr heq, WP.spec_ok]
    exact cedKeyPost_of_eq heq
  · -- `ats > self.ctr`
    simp only [Nat.compare_eq_gt.mpr hgt]
    step as ⟨i, h_i, _⟩
    by_cases hj : (chain.maxJump params).val < ats.val - self.ctr.val
    · -- beyond the jump budget
      have : (chain.maxJump params).val < i.val := by omega
      rw [if_pos (show i > chain.maxJump params from this), WP.spec_ok]
      exact cedKeyPost_of_jump hgt hj
    -- within the jump budget: pick the starting key history, then run the shared tail
    rw [if_neg (show ¬ i > chain.maxJump params from
      fun h => by have : (chain.maxJump params).val < i.val := h; omega)]
    step as ⟨i3, h_i3⟩
    have h_gt : ats > self.ctr := hgt
    by_cases hc : self.ctr.val + (chain.maxOoo params).val < ats.val
    · rw [if_pos (show ats > i3 from (by omega : i3.val < ats.val))]
      step as ⟨kh, h_kh⟩
      have : kh.data.length + 36 * (ats.val - self.ctr.val) ≤ Usize.max := by omega
      have : kh.data.length % 36 = 0 := by omega
      have : kh.data.length ≤ 36 * self.ctr.val := by omega
      step with keyAdvanceTail_spec_core as ⟨kh2, i5, v1, v2, h_tail⟩
      exact cedKeyPost_of_advance hgt (by omega) fun h_gt' =>
        cedKeyAdvancePost_of_tail self ats params kh kh2 i5 v1 v2 h_gt' (fun _ => h_kh)
          (fun h => absurd hc h) h_tail
    · rw [if_neg (show ¬ ats > i3 from fun h => by have : i3.val < ats.val := h; omega), bind_ok]
      step with keyAdvanceTail_spec_core as ⟨kh2, i5, v1, v2, h_tail⟩
      exact cedKeyPost_of_advance hgt (by omega) fun h_gt' =>
        cedKeyAdvancePost_of_tail self ats params self.prev kh2 i5 v1 v2 h_gt'
          (fun h => absurd h hc) (fun _ => rfl) h_tail

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
    - The pre-GC key history equals
      `iterKeyHistory self.next.val self.ctr ats params kh0 loopSteps`,
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

**Source**: spqr/src/chain.rs, lines 248:4-297:5
-/
@[step]
theorem key_spec (self : chain.ChainEpochDirection) (ats : U32)
    (params : proto.pq_ratchet.ChainParams)
    (h_next_len : self.next.length = 32)
    (h_maxooo_bound : (chain.maxOoo params).val < 390451572)
    (h_kh_cap : self.prev.data.length + 36 * (ats.val - self.ctr.val) ≤ Usize.max)
    (h_prev_aligned : self.prev.data.length % 36 = 0)
    (h_prev_ctr : self.prev.data.length ≤ 36 * self.ctr.val)
    (h_ooo_no_overflow : ats + (chain.maxOoo params).val ≤ U32.max)
    (h_platform : System.Platform.numBits = 64) :
    key self ats params ⦃ (result : (core.result.Result (alloc.vec.Vec U8) Error) ×
        chain.ChainEpochDirection) =>
      chain.cedKeyPost self ats params result.1 result.2 ⦄ := by
  have h_raw := maxOoo_imp_raw_ooo params _ h_maxooo_bound
  have h_usize : Usize.max = 2 ^ 64 - 1 := by simp [Usize.max, Usize.numBits, h_platform]
  exact key_spec_all_core self ats params h_next_len h_raw (by omega) h_kh_cap h_prev_aligned
    h_prev_ctr h_ooo_no_overflow

end spqr.chain.ChainEpochDirection
