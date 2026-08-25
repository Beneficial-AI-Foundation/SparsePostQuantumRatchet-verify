/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Chain.KeyHistory.KEY_SIZE
import Spqr.Specs.Chain.ChainParams.TrimSize
import Spqr.Specs.Chain.ChainParams.MaxOooKeysOrDefault
import Spqr.Specs.Aeneas.IndexRangeFull
import Spqr.Specs.Chain.KeyHistory.Remove
/-! # Spec theorem for `spqr::chain::{spqr::chain::KeyHistory}::gc`: loop body 0

At each iteration, the loop examines the 4-byte big-endian counter at offset `i1` in `self.data`:

- If `i1 ≥ self.data.len()`, scan ends: returns `done self.data`.
- Else reads slice `self.data[i1 .. i1 + 4]` and compares `trim_horizon`:
  - If `trim_horizon > slice` (expired), calls `KeyHistory::remove` to swap-remove the 36-byte
  record at `i1`, returns `cont (self', i1)` (re-examine same index).
  - Else (live), advances by `KEY_SIZE = 36`, returns `cont (self, i1 + 36)`.
**Source**: spqr/src/chain.rs -/

open Aeneas Aeneas.Std Result spqr

namespace spqr.chain.KeyHistory.gc_loop

/-- `Slice.lexCmpAux` with `OrdU8` always succeeds, returning `ok` of some `Ordering`. -/
private theorem lexCmpAux_OrdU8_ok (xs ys : List U8) :
    ∃ o, Slice.lexCmpAux core.cmp.OrdU8 xs ys = ok o := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => exact ⟨.eq, by unfold Slice.lexCmpAux; rfl⟩
    | cons _ _ => exact ⟨.lt, by unfold Slice.lexCmpAux; rfl⟩
  | cons a xs ih =>
    cases ys with
    | nil => exact ⟨.gt, by unfold Slice.lexCmpAux; rfl⟩
    | cons b ys =>
      unfold Slice.lexCmpAux
      simp only [core.cmp.OrdU8, liftFun2, core.cmp.impls.OrdU8.cmp]
      cases h : compare a.val b.val
      · exact ⟨.lt, by simp ⟩
      · simp only [bind_tc_ok]
        exact ih ys
      · exact ⟨.gt, by simp⟩


/-- **Spec theorem for `spqr.chain.KeyHistory.gc_loop.body`**:

One step of the garbage-collection loop:

- **Done** (`i1 ≥ self.data.len()`): returns `done self.data` unchanged.
- **Remove** (`i1 < self.data.len()` and `trim_horizon > self.data[i1..i1+4]`): swap-removes
  the 36-byte record at `i1`, returns `cont (self', i1)` where:
  - `self'.data.len() = self.data.len() - 36`
  - `i1` remains 36-aligned and in bounds
  - `self'.data.len() ≤ usize::MAX`
  - bytes before `i1` preserved: `∀ j < i1, self'.data[j] = self.data[j]`
  - content defined by `remove_spec`
- **Advance** (`i1 < self.data.len()` and `trim_horizon ≤ self.data[i1..i1+4]`): returns
  `cont (self, i1 + 36)` with `self` unchanged, `i1 + 36` 36-aligned and `≤ self.data.len()`. -/
@[step]
theorem body_spec
    (i : Usize) (params : proto.pq_ratchet.ChainParams)
    (trim_horizon : Slice U8) (self : chain.KeyHistory) (i1 : Usize)
    (h_i : i = 36#usize)
    (h_bound : self.data.length ≤ Usize.max)
    (h_aligned : i1.val % 36 = 0)
    (h_data_aligned : self.data.length % 36 = 0)
    (h_i1_bound : i1.val ≤ self.data.length) :
    body i params trim_horizon self i1 ⦃ cf =>
      match cf with
      | ControlFlow.done out =>
          out = self.data ∧ ¬(i1.val < self.data.length)
      | ControlFlow.cont (self', i1') =>
          i1.val < self.data.length ∧
          -- remove case: `trim_horizon > counter`, i.e. the record at `i1` is expired
          (Slice.lexCmpAux core.cmp.OrdU8 trim_horizon.val
              (self.data.val.slice i1.val (i1.val + 4)) = ok .gt →
            self'.data.length = self.data.length - 36 ∧
            i1' = i1 ∧
            i1'.val % 36 = 0 ∧
            i1' ≤ self'.data.length ∧
            self'.data.length ≤ Usize.max ∧
            (∀ j, j < i1.val →
              self'.data[j]! = self.data[j]!) ∧
            (i1.val + 36 < self.data.length →
              self'.data =
                (self.data.val.setSlice! i1
                  (self.data.val.drop (self.data.length - 36))).take
                    (self.data.length - 36)) ∧
            (i1.val + 36 = self.data.length →
              self'.data = self.data.val.take i1)) ∧
          -- advance case: `trim_horizon ≤ counter`, i.e. the record at `i1` is still live
          (Slice.lexCmpAux core.cmp.OrdU8 trim_horizon.val
              (self.data.val.slice i1.val (i1.val + 4)) ≠ ok .gt →
            self' = self ∧
            i1'.val = i1.val + 36 ∧
            i1'.val % 36 = 0 ∧
            i1'.val ≤ self'.data.length ∧
            self'.data.length ≤ Usize.max ∧
            self'.data.length % 36 = 0) ⦄ := by
  unfold body
  simp only [alloc.vec.Vec.len]
  by_cases h_lt : i1.val < self.data.length
  · split
    · have h4 : i1.val + 4 ≤ self.data.length := by omega
      step*
      simp only [Slice.Insts.CoreCmpOrd.cmp_eq, alloc.vec.Vec.length, not_lt]
      rw [i3_post] at s_post1
      rw [s_post1]
      obtain ⟨o, ho⟩ :=
        lexCmpAux_OrdU8_ok trim_horizon.val (self.data.val.slice i1.val (i1.val + 4))
      rw [ho]
      cases o
      · simp only [bind_tc_ok, Bool.false_eq_true, if_false]
        rw [h_i]
        step*
        refine ⟨h_lt, fun h => absurd h (by simp), fun _ => ⟨i4_post, ?_, ?_⟩⟩
        · rw [i4_post]; omega
        · rw [i4_post]; grind
      · simp only [bind_tc_ok, Bool.false_eq_true, if_false]
        rw [h_i]
        step*
        refine ⟨h_lt, fun h => absurd h (by simp), fun _ => ⟨i4_post, ?_, ?_⟩⟩
        · rw [i4_post]; omega
        · rw [i4_post]; grind
      · simp only [bind_tc_ok, if_true]
        have h36 : i1 + 36#usize ≤ self.data.length := by scalar_tac
        have hspec := remove_spec self i1 params h36
        step*
        refine ⟨h_lt, self1_post1, h_aligned, by scalar_tac,
          by scalar_tac, ?_, self1_post3, self1_post4,
          fun h => absurd rfl h⟩
        intro j hj
        have := self1_post2 j hj
        grind
    · have h4 : i1.val + 4 ≤ self.data.length := by omega
      step*
  · step*


end spqr.chain.KeyHistory.gc_loop

/-!
**Spec theorem for `spqr::chain::{spqr::chain::KeyHistory}::gc`: loop 0**

The garbage-collection loop iterates via fixed-point combinator, threading `(self, i1)`
until `done`:

- **Cont**: continues with updated state—either removes an expired 36-byte record (shrinks by 36,
`i1` unchanged) or advances `i1` by 36 past a live record.
- **Done**: terminates, returning final vector `out`.

**Termination**: measure `self.data.len() - i1` strictly decreases by 36 each iteration
(remove: length ↓36; advance: `i1` ↑36).

**Invariant**: `i1` remains 36-aligned and in bounds; data length stays 36-aligned,
within `usize::MAX`, and never exceeds initial length (removals only).

**Preconditions**: length within `usize::MAX`, step = 36, `i1` and length are 36-aligned,
`i1 ≤ self.data.len()`.

**Source**: spqr/src/chain.rs -/

namespace spqr.chain.KeyHistory

/-- Build a slice equality from element-wise `getElem!` equalities. -/
private theorem slice_eq_of_getElem! (a b : List Std.U8) (m n len : Nat)
    (ha : m + len ≤ a.length) (hb : n + len ≤ b.length)
    (h : ∀ j, j < len → a[m + j]! = b[n + j]!) :
    a.slice m (m + len) = b.slice n (n + len) := by
  apply List.ext_getElem
  · simp [List.slice_length]; omega
  · intro j h1 h2
    simp only [List.slice_length] at h1
    have hj : j < len := by omega
    rw [List.getElem_slice _ _ _ _ ⟨by omega, by omega⟩,
        List.getElem_slice _ _ _ _ ⟨by omega, by omega⟩,
        List.Inhabited_getElem_eq_getElem! _ _ (by omega),
        List.Inhabited_getElem_eq_getElem! _ _ (by omega)]
    exact h j hj

/-- Extract element-wise equality from equal slices. -/
private theorem getElem!_of_slice_eq (a b : List Std.U8) (m n len : Nat)
    (h : a.slice m (m + len) = b.slice n (n + len))
    (ha : m + len ≤ a.length) (hb : n + len ≤ b.length)
    (j : Nat) (hj : j < len) :
    a[m + j]! = b[n + j]! := by
  have h1 : (a.slice m (m + len))[j]! = a[m + j]! := by
    rw [List.getElem!_slice _ _ _ _ ⟨by omega, by omega⟩]
  have h2 : (b.slice n (n + len))[j]! = b[n + j]! := by
    rw [List.getElem!_slice _ _ _ _ ⟨by omega, by omega⟩]
  rw [← h1, ← h2, h]

private theorem slice_eq_of_prefix (a b : List Std.U8) (m : Nat)
    (ha : m + 4 ≤ a.length) (hb : m + 4 ≤ b.length)
    (h : ∀ j, j < m + 4 → a[j]! = b[j]!) :
    a.slice m (m + 4) = b.slice m (m + 4) := by
  apply List.ext_getElem
  · simp only [List.slice_length]; omega
  · intro n h1 h2
    have hn : n < 4 := by simp only [List.slice_length] at h1; omega
    rw [List.getElem_slice m (m + 4) n a (by omega),
        List.getElem_slice m (m + 4) n b (by omega),
        List.Inhabited_getElem_eq_getElem! a (m + n) (by omega),
        List.Inhabited_getElem_eq_getElem! b (m + n) (by omega)]
    exact h (m + n) (by omega)

/-- **Spec theorem for `spqr.chain.KeyHistory.gc_loop`**:

Executes the garbage-collection loop from state `(self, i1)`. Under invariant—`i1` and
`self.data.len()` 36-aligned, `i1 ≤ self.data.len()`, length within `usize::MAX`—the loop
terminates, returning `result` satisfying:

- `result.len() % 36 = 0` (whole records)
- `result.len() ≤ usize::MAX`
- `result.len() ≤ self.data.len()` (removals only) -/
@[step]
theorem gc_loop_spec
    (i : Std.Usize) (self : chain.KeyHistory)
    (params : proto.pq_ratchet.ChainParams)
    (trim_horizon : Slice Std.U8) (i1 : Std.Usize)
    (h_i : i = 36#usize)
    (h_bound : self.data.length ≤ Std.Usize.max)
    (h_aligned : i1.val % 36 = 0)
    (h_data_aligned : self.data.length % 36 = 0)
    (h_i1_bound : i1.val ≤ self.data.length) :
    gc_loop i self params trim_horizon i1 ⦃ (result : alloc.vec.Vec Std.U8) =>
      result.length % 36 = 0 ∧
      result.length ≤ Std.Usize.max ∧
      result.length ≤ self.data.length ∧
      (∀ j, j < i1.val → result.val[j]! = self.data.val[j]!) ∧
      i1.val ≤ result.length ∧
      (∀ m, i1.val ≤ m ∧  m < result.length ∧  m % 36 = 0 →
        Slice.lexCmpAux core.cmp.OrdU8 trim_horizon.val
          (result.val.slice m (m + 4)) ≠ ok .gt) ∧
      (∀ m, m < result.length ∧ m % 36 = 0 →
        ∃ n, n < self.data.length ∧ n % 36 = 0 ∧
          result.val.slice m (m + 36) = self.data.val.slice n (n + 36))⦄ := by
  unfold gc_loop
  apply loop.spec_decr_nat
    (measure := fun (p : chain.KeyHistory × Std.Usize) => p.1.data.length - p.2.val)
    (inv := fun (p : chain.KeyHistory × Std.Usize) =>
      p.2.val % 36 = 0 ∧ p.1.data.length % 36 = 0 ∧
      p.1.data.length ≤ Std.Usize.max ∧ p.2.val ≤ p.1.data.length ∧
      p.1.data.length ≤ self.data.length ∧
      i1.val ≤ p.2.val ∧
      (∀ j, j < i1.val → p.1.data.val[j]! = self.data.val[j]!) ∧
      (∀ m, i1.val ≤ m ∧  m < p.2.val ∧  m % 36 = 0 →
        Slice.lexCmpAux core.cmp.OrdU8 trim_horizon.val
          (p.1.data.val.slice m (m + 4)) ≠ ok .gt) ∧
      (∀ m, m < p.1.data.length ∧ m % 36 = 0 →
        ∃ n, n < self.data.length ∧ n % 36 = 0 ∧
          p.1.data.val.slice m (m + 36) = self.data.val.slice n (n + 36)))
  · intro ⟨s, k⟩ ⟨hk_al, hs_al, hs_bnd, hkb, hs_le, hmono, hpres, hlive, hsubseq⟩
    have hspec := gc_loop.body_spec i params trim_horizon s k h_i hs_bnd hk_al hs_al hkb
    apply WP.spec_mono hspec
    intro cf hcf
    rcases cf with ⟨s', k'⟩ | out
    · obtain ⟨hlt, hrem, hadv⟩ := hcf
      by_cases hcmp : Slice.lexCmpAux core.cmp.OrdU8 trim_horizon.val
          (s.data.val.slice k.val (k.val + 4)) = ok .gt
      · obtain ⟨hlen, hkeq, hal, hib, hbnd', hpre, hsw, htr⟩ := hrem hcmp
        refine ⟨⟨hal, ?_, hbnd', hib, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
        · rw [hlen]; grind
        · rw [hlen]; grind
        · rw [hkeq]; exact hmono
        · intro j hj
          have hjk : j < k.val := lt_of_lt_of_le hj hmono
          grind
        · intro m hm1 hm2
          rw [hkeq] at hm2
          have hm4 : m + 4 ≤ k.val := by grind
          have hibk : k.val ≤ s'.data.length := by rw [hkeq] at hib; exact hib
          have hsl : s'.data.val.slice m (m + 4) = s.data.val.slice m (m + 4) := by
            apply slice_eq_of_prefix
            · exact le_trans hm4 hibk
            · exact le_trans hm4 hkb
            · intro j hj; exact hpre j (by omega)
          grind
        · intro m ⟨hml, hmal⟩
          have hml_s : m < s.data.length := by grind
          by_cases hmk : m + 36 ≤ k.val
          · obtain ⟨n, hn1, hn2, hn3⟩ := hsubseq m ⟨hml_s, hmal⟩
            have hml36 : m + 36 ≤ s'.data.length := by
              have : s'.data.length % 36 = 0 := by rw [hlen]; grind
              grind
            have hn36 : n + 36 ≤ self.data.length := by grind
            refine ⟨n, hn1, hn2,
              slice_eq_of_getElem! _ _ _ _ 36 hml36 hn36 fun j hj => ?_⟩
            change (s'.data)[m + j]! = (self.data)[n + j]!
            rw [hpre (m + j) (by omega)]
            exact getElem!_of_slice_eq _ _ _ _ 36 hn3 (by grind) hn36 j hj
          · by_cases hmk2 : k.val + 36 < s.data.length
            · have hsw' := hsw hmk2
              by_cases hmeq : m = k.val
              · subst hmeq
                have hlast_m : s.data.length - 36 < s.data.length := by omega
                have hlast_al : (s.data.length - 36) % 36 = 0 := by grind
                obtain ⟨n, hn1, hn2, hn3⟩ := hsubseq (s.data.length - 36) ⟨hlast_m, hlast_al⟩
                have hn36' : n + 36 ≤ self.data.length := by grind
                refine ⟨n, hn1, hn2,
                  slice_eq_of_getElem! _ _ _ _ 36 (by grind) hn36' fun j hj => ?_⟩
                rw [hsw', List.getElem!_take_of_lt _ _ _ (by omega),
                    List.getElem!_setSlice!_middle _ _ _ _
                      ⟨by omega, by simp [List.length_drop]; grind, by grind⟩,
                    List.getElem!_drop]
                have key := getElem!_of_slice_eq _ _ _ _ 36 hn3 (by grind) hn36' j hj
                have : s.data.val.length - 36 + j = s.data.val.length - 36 + (j + k.val - k.val) :=
                  by omega
                rw [this] at key
                grind
              · have hm_gt36 : k.val + 36 ≤ m := by grind
                obtain ⟨n, hn1, hn2, hn3⟩ := hsubseq m ⟨hml_s, hmal⟩
                have hn36' : n + 36 ≤ self.data.length := by grind
                refine ⟨n, hn1, hn2,
                  slice_eq_of_getElem! _ _ _ _ 36 (by grind) hn36' fun j hj => ?_⟩
                rw [hsw', List.getElem!_take_of_lt _ _ _ (by grind),
                    List.getElem!_setSlice!_suffix _ _ _ _ (by simp [List.length_drop]; omega)]
                exact getElem!_of_slice_eq _ _ _ _ 36 hn3 (by grind) hn36' j hj
            · have hk36 : k.val + 36 = s.data.length := by grind
              have htr' := htr hk36
              have hml' : m < k.val := by grind
              obtain ⟨n, hn1, hn2, hn3⟩ := hsubseq m ⟨hml_s, hmal⟩
              have hn36' : n + 36 ≤ self.data.length := by grind
              refine ⟨n, hn1, hn2,
                slice_eq_of_getElem! _ _ _ _ 36 (by grind) hn36' fun j hj => ?_⟩
              rw [htr', List.getElem!_take_of_lt _ _ _ (by grind)]
              exact getElem!_of_slice_eq _ _ _ _ 36 hn3 (by grind) hn36' j hj
        · simp only; rw [hlen] at hib ⊢; grind
      · obtain ⟨hself, hkeq, hal, hib, _hbnd, _hal2⟩ := hadv hcmp
        subst hself
        refine ⟨⟨hal, hs_al, hs_bnd, hib, hs_le, ?_, hpres, ?_, hsubseq⟩, ?_⟩
        · grind
        · intro m hm1 hm2
          by_cases hmk : m < k.val
          · grind
          · have hmeq : m = k.val := by grind
            grind
        · simp only; omega
    · obtain ⟨hout, _hnlt⟩ := hcf
      subst hout
      refine ⟨hs_al, hs_bnd, hs_le, hpres, le_trans hmono hkb, ?_, ?_⟩
      · intro m ⟨hm1, hm2, hm3⟩
        have : m < k.val := by omega
        exact hlive m ⟨hm1, this, hm3⟩
      · intro m hm; exact hsubseq m hm
  · exact ⟨h_aligned, h_data_aligned, h_bound, h_i1_bound, le_refl _, le_refl _,
      fun j _ => rfl, fun m h => by grind,
      fun m ⟨hml, hmal⟩ => ⟨m, hml, hmal, rfl⟩⟩



/-!**Spec theorem for `spqr::chain::{spqr::chain::KeyHistory}::gc` (32-bit platform)**

32-bit variant of `gc_spec` (proved in `Gc.lean`). Differences from 64-bit:
- `h_platform : System.Platform.numBits = 32`
- `h_ooo : params.max_ooo_keys.val < 108458770` (tighter bound ensuring `trim_size * KEY_SIZE`
fits in 32-bit `usize`)

**Rationale for tighter bound**:
- `max_ooo_keys < 108458770` → `trim_size * 36 ≤ 4294967295` (`U32.max`)
- 64-bit bound (`390451572`) would yield `trim_threshold ≈ 15.4B`, overflowing 32-bit `usize`

**Source**: spqr/src/chain.rs-/
@[step]
theorem gc_spec (self : chain.KeyHistory) (current_key : Std.U32)
    (params : proto.pq_ratchet.ChainParams)
    (h_bound : self.data.length ≤ Std.Usize.max)
    (h_data_aligned : self.data.length % 36 = 0)
    (h_ooo : params.max_ooo_keys.val < 108458770)
    (h_key_ooo : params.max_ooo_keys.val ≤ current_key.val)
    (h_key_def : 2000 ≤ current_key.val) :
    gc self current_key params ⦃ (result : chain.KeyHistory) =>
      let max_ooo : Nat :=
        if 0#u32 < params.max_ooo_keys then params.max_ooo_keys.val else 2000
      let trim_size : Nat := max_ooo * 11 / 10 + 1
      let trim_threshold : Nat := trim_size * 36
      result.data.length % 36 = 0 ∧
      result.data.length ≤ self.data.length ∧
      result.data.length ≤ Std.Usize.max ∧
      (self.data.length < trim_threshold → result = self) ∧
      (trim_threshold ≤ self.data.length →
        ∃ horizon : Std.U32,
         horizon.val = current_key.val - max_ooo ∧
          (∀ m, m < result.data.length ∧ m % 36 = 0 →
            Slice.lexCmpAux core.cmp.OrdU8
              (horizon.bv.toBEBytes.map (@Std.UScalar.mk Std.UScalarTy.U8))
              (result.data.val.slice m (m + 4)) ≠ ok .gt)) ∧
      (∀ m, m < result.data.length ∧ m % 36 = 0 →
        ∃ n, n < self.data.length ∧ n % 36 = 0 ∧
          result.data.val.slice m (m + 36) = self.data.val.slice n (n + 36)) ⦄ := by
  unfold gc
  simp only [alloc.vec.Vec.len]
  step*
  · rcases Classical.em (params.max_ooo_keys > 0#u32) with hpos | hnpos
    · have := i4_post1.2 hpos
      subst this
      simp only [ge_iff_le, UScalar.le_equiv]
      exact h_key_ooo
    · have hz : params.max_ooo_keys = 0#u32 := by
        simp only [gt_iff_lt, UScalar.lt_equiv, UScalar.ofNatCore_val_eq, not_lt,
          Nat.le_zero] at hnpos
        scalar_tac
      have := i4_post2.2 (Or.inl hz)
      subst this
      simp only [ge_iff_le, UScalar.le_equiv, DEFAULT_CHAIN_PARAMS_spec]
      exact h_key_def
  · refine ⟨v_post1, v_post3, v_post2, ?_, ?_, ?_⟩
    · intro hlt
      exact absurd hlt (by grind)
    · intro _
      refine ⟨i5, ?_, ?_⟩
      · rcases Classical.em (params.max_ooo_keys > 0#u32) with hpos | hnpos
        · have hi4 := i4_post1.2 hpos
          subst hi4
          simp only [hpos, ite_true]
          exact i5_post1
        · have hz : params.max_ooo_keys = 0#u32 := by
            simp only [gt_iff_lt, UScalar.lt_equiv, UScalar.ofNatCore_val_eq, not_lt,
              Nat.le_zero] at hnpos
            scalar_tac
          have hi4 := i4_post2.2 (Or.inl hz)
          subst hi4
          have hnotpos : ¬ (0#u32 < params.max_ooo_keys) := by
            rw [hz]
            simp only [lt_self_iff_false, not_false_eq_true]
          simp only [hnotpos, ite_false]
          have := DEFAULT_CHAIN_PARAMS_spec.2
          scalar_tac
      · intro m hm_lt hm_al
        have hslice : (↑a.to_slice : List Std.U8) =
            List.map (@Std.UScalar.mk Std.UScalarTy.U8) i5.bv.toBEBytes := by
          simp only [Aeneas.Std.Array.to_slice]
          exact a_post
        rw [← hslice]
        exact v_post6 m (by omega) hm_lt hm_al
    · intro m hm
      exact v_post7 m hm
  · refine ⟨h_data_aligned, le_refl _, h_bound, fun _ => trivial, fun h => absurd h (by grind), ?_⟩
    intro m hm hmal
    exact ⟨m, hm, hmal, rfl⟩

/-- **Spec theorem for `spqr.chain.KeyHistory.gc`**:

Executes one garbage-collection pass on `self`. Preconditions: data length 36-aligned and within
`usize::MAX`; `params.max_ooo_keys` below overflow bound `390451572`; `current_key` dominates both
OOO budget and default `2000`. Returns `KeyHistory` with `result.data` satisfying:

- `result.data.len() % 36 = 0` (whole records)
- `result.data.len() ≤ self.data.len()` (removals only)
- `result.data.len() ≤ usize::MAX` (bound preserved) -/
@[step]
theorem gc_spec_64 (self : chain.KeyHistory) (current_key : U32)
    (params : proto.pq_ratchet.ChainParams)
    (h_bound : self.data.length ≤ Usize.max)
    (h_data_aligned : self.data.length % 36 = 0)
    (h_ooo : params.max_ooo_keys.val < 390451572)
    (h_key_ooo : params.max_ooo_keys.val ≤ current_key.val)
    (h_key_def : 2000 ≤ current_key.val)
    (h_platform : System.Platform.numBits = 64) :
    gc self current_key params ⦃ (result : chain.KeyHistory) =>
      let max_ooo : Nat :=
        if 0#u32 < params.max_ooo_keys then params.max_ooo_keys.val else 2000
      let trim_size : Nat := max_ooo * 11 / 10 + 1
      let trim_threshold : Nat := trim_size * 36
      result.data.length % 36 = 0 ∧
      result.data.length ≤ self.data.length ∧
      result.data.length ≤ Usize.max ∧
      (self.data.length < trim_threshold → result = self) ∧
      (trim_threshold ≤ self.data.length →
        ∃ horizon : U32,
         horizon.val = current_key.val - max_ooo ∧
          (∀ m, m < result.data.length ∧ m % 36 = 0 →
            Slice.lexCmpAux core.cmp.OrdU8
              (horizon.bv.toBEBytes.map (@UScalar.mk UScalarTy.U8))
              (result.data.val.slice m (m + 4)) ≠ ok .gt)) ∧
      (∀ m, m < result.data.length ∧ m % 36 = 0 →
        ∃ n, n < self.data.length ∧ n % 36 = 0 ∧
          result.data.val.slice m (m + 36) = self.data.val.slice n (n + 36)) ⦄ := by
  unfold gc
  simp only [alloc.vec.Vec.len]
  step*
  · have hi1 : i1.val ≤ 429496729 := by
      rcases Classical.em (params.max_ooo_keys > 0#u32) with hpos | hnpos
      · rw [i1_post1.2 hpos]
        omega
      · have : i1.val = 2201 := by
          apply i1_post2.2
          simp only [gt_iff_lt, UScalar.lt_equiv, UScalar.ofNatCore_val_eq, not_lt,
            Nat.le_zero] at hnpos
          left
          scalar_tac
        omega
    subst i2_post
    have hmax : Usize.max = U64.max := by
      simp only [Usize.max, Usize.numBits, UScalarTy.Usize_numBits_eq, h_platform,
        U64.max, U64.numBits, UScalarTy.U64_numBits_eq]
    rw [hmax, U64.max_eq]
    simp only [UScalar.ofNatCore_val_eq]
    omega
  · rcases Classical.em (params.max_ooo_keys > 0#u32) with hpos | hnpos
    · have := i4_post1.2 hpos
      subst this
      simp only [ge_iff_le, UScalar.le_equiv]
      exact h_key_ooo
    · have hz : params.max_ooo_keys = 0#u32 := by
        simp only [gt_iff_lt, UScalar.lt_equiv, UScalar.ofNatCore_val_eq, not_lt,
          Nat.le_zero] at hnpos
        scalar_tac
      have := i4_post2.2 (Or.inl hz)
      subst this
      simp only [ge_iff_le, UScalar.le_equiv, DEFAULT_CHAIN_PARAMS_spec]
      exact h_key_def
  · refine ⟨v_post1, v_post3, v_post2, ?_, ?_, ?_⟩
    · intro hlt
      exact absurd hlt (by grind)
    · intro _
      refine ⟨i5, ?_, ?_⟩
      · rcases Classical.em (params.max_ooo_keys > 0#u32) with hpos | hnpos
        · have hi4 := i4_post1.2 hpos
          subst hi4
          simp only [hpos, ite_true]
          exact i5_post1
        · have hz : params.max_ooo_keys = 0#u32 := by
            simp only [gt_iff_lt, UScalar.lt_equiv, UScalar.ofNatCore_val_eq, not_lt,
              Nat.le_zero] at hnpos
            scalar_tac
          have hi4 := i4_post2.2 (Or.inl hz)
          subst hi4
          have hnotpos : ¬ (0#u32 < params.max_ooo_keys) := by
            rw [hz]
            simp only [lt_self_iff_false, not_false_eq_true]
          simp only [hnotpos, ite_false]
          have := DEFAULT_CHAIN_PARAMS_spec.2
          scalar_tac
      · intro m hm_lt hm_al
        have hslice : (↑a.to_slice : List U8) =
            List.map (@UScalar.mk UScalarTy.U8) i5.bv.toBEBytes := by
          grind
        rw [← hslice]
        exact v_post6 m (by omega) hm_lt hm_al
    · intro m hm
      exact v_post7 m hm
  · refine ⟨h_data_aligned, le_refl _, h_bound, fun _ => trivial, fun h => absurd h (by grind), ?_⟩
    intro m hm hmal
    exact ⟨m, hm, hmal, rfl⟩

end spqr.chain.KeyHistory
