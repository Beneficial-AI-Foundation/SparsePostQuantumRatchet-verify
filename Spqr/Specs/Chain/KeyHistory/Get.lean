/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Chain.KeyHistory.KEY_SIZE
import Spqr.Specs.Chain.ChainParams.MaxOooKeysOrDefault
import Spqr.Specs.Chain.Defs
import Spqr.Specs.Chain.KeyHistory.Remove
/-! # Spec theorem for `spqr::chain::{spqr::chain::KeyHistory}::get`: loop body 0

One iteration of the key-lookup loop in `KeyHistory::get`. Steps through `data` in 36-byte
(KEY_SIZE) records via a `StepBy` iterator, comparing each record's 4-byte counter against
`want`. Returns `done Err` if exhausted, `done Ok` with the 32-byte payload (after
swap-removing the record) on match, or `cont` to advance on mismatch.

**Source**: spqr/src/chain.rs -/

open Aeneas Aeneas.Std Result spqr

namespace spqr.chain.KeyHistory.get_loop

/-- **Spec theorem for `spqr.chain.KeyHistory.get_loop.body`**:

One step of the key-lookup loop. Three outcomes:
- **Not found**: iterator exhausted → `done (Err KeyAlreadyRequested, { data := v })`.
- **Found**: counter matches → extracts 32-byte payload, swap-removes the 36-byte record,
  returns `done (Ok out, self')` with length/alignment/prefix invariants preserved.
- **No match**: counter differs → `cont iter1` with iterator advanced (36-aligned).

**Source**: spqr/src/chain.rs -/
@[step]
theorem body_spec
    (i : Usize) (v : alloc.vec.Vec U8) (at1 : U32)
    (params : proto.pq_ratchet.ChainParams) (want : Array U8 4#usize)
    (iter : core.iter.adapters.step_by.StepBy (core.ops.range.Range Usize))
    (h_i : i = 36#usize)
    (h_bound : v.length ≤ Usize.max)
    (h_data_aligned : v.length % 36 = 0)
    (h_step : iter.step_by = i)
    (h_start_aligned : iter.iter.start.val % 36 = 0)
    (h_end_eq : iter.iter.end = v.length) :
    body i v at1 params want iter ⦃ cf =>
      match cf with
      | ControlFlow.done (result, self') =>
          match result with
          | core.result.Result.Err e =>
              e = Error.KeyAlreadyRequested at1 ∧
              self'.data = v ∧
              iter.iter.start ≥ iter.iter.end
          | core.result.Result.Ok out =>
              let i1 := iter.iter.start
              i1.val % 36 = 0 ∧
              i1 + 36 ≤ v.length ∧
              v.val.slice i1 (i1 + 4) = want ∧
              out.length = 32 ∧
              out = v.val.slice (i1 + 4) (i1 + 36) ∧
              self'.data.length = v.length - 36 ∧
              self'.data.length ≤ Usize.max ∧
              self'.data.length % 36 = 0 ∧
              (∀ j, j < i1.val → self'.data[j]! = v[j]!) ∧
              (i1 + 36 < v.length →
                self'.data =
                  (v.val.setSlice! i1 (v.val.drop (v.length - 36))).take (v.length - 36)) ∧
              (i1 + 36 = v.length →
                self'.data = v.val.take i1)
      | ControlFlow.cont iter1 =>
          iter.iter.start < iter.iter.end ∧
          iter1.iter.start = min (iter.iter.start.val + 36) iter.iter.end ∧
          iter1.iter.end = iter.iter.end ∧
          iter1.iter.end = v.length ∧
          iter1.step_by = iter.step_by ∧
          v.val.slice iter.iter.start (iter.iter.start + 4) ≠ want ∧
          iter1.iter.start.val % 36 = 0 ⦄ := by
  unfold body
  have h_step_val : iter.step_by.val = 36 := by
    have := congrArg UScalar.val h_step
    simp only [h_i, UScalar.ofNatCore_val_eq] at this
    exact this
  by_cases h_lt : iter.iter.start.val < iter.iter.end.val
  · have h_step_pos : iter.step_by.val > 0 := by omega
    obtain ⟨⟨opt, iter1⟩, h_eq, h_post⟩ :=
      WP.spec_imp_exists
        (core.iter.adapters.step_by.IteratorStepBy.next_Range_Usize_spec iter h_step_pos)
    simp only [WP.uncurry'_pair] at h_post
    simp only [h_lt, ↓reduceIte] at h_post
    obtain ⟨⟨h_opt, h_start1⟩, h_end1, h_sb1⟩ := h_post
    rw [h_eq]
    simp only [bind_tc_ok, h_opt]
    have h_i1_lt : iter.iter.start.val < v.length := by omega
    have h_36 : iter.iter.start.val + 36 ≤ v.length := by
      have ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero h_start_aligned
      have ⟨m, hm⟩ := Nat.dvd_of_mod_eq_zero h_data_aligned
      omega
    have h_4 : iter.iter.start.val + 4 ≤ v.length := by omega
    step as ⟨i2, h_i2⟩
    step as ⟨s, h_s_val, h_s_len⟩
    have heq_spec := Slice.Insts.CoreCmpPartialEqArray.eq_U8_spec s want
    obtain ⟨b, hb_eq, hb_iff⟩ := WP.spec_imp_exists heq_spec
    rw [hb_eq]
    simp only [bind_tc_ok]
    by_cases hb : b = true
    · simp only [hb, ↓reduceIte]
      have h_s_want : s.val = want.val := hb_iff.1 hb
      rw [h_i]
      step as ⟨i3, h_i3⟩
      step as ⟨s1, h_s1_val, h_s1_len⟩
      have h_clone : ∀ x ∈ s1.val, core.clone.CloneU8.clone x = ok x := by
        intro x _; simp
      step as ⟨out, h_out⟩
      have h_36' : iter.iter.start + 36#usize ≤ v.length := by scalar_tac
      have hspec := remove_spec { data := v } iter.iter.start params h_36'
      step as ⟨self1, h_self1_len, h_self1_pres, h_self1_swap, h_self1_trunc⟩
      simp only [alloc.vec.Vec.length] at *
      refine ⟨h_start_aligned, h_36, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [← h_s_want, h_s_val]; congr 1
        scalar_tac
      · rw [← h_out]; simp only [h_s1_len]; scalar_tac
      · rw [← h_out, h_s1_val]; congr 1
      · exact h_self1_len
      · omega
      · omega
      · intro j hj
        have := h_self1_pres j hj
        grind
      · exact h_self1_swap
      · exact h_self1_trunc
    · simp only [show b = false from by cases b <;> simp_all]
      have h_ne : v.val.slice iter.iter.start.val (iter.iter.start.val + 4) ≠ want.val := by
        intro heq
        have : s.val = want.val := by rw [h_s_val]; scalar_tac
        have : b = true := hb_iff.2 this
        cases b <;> simp_all
      have h_start1_val : iter1.iter.start.val =
        min (iter.iter.start.val + 36) iter.iter.end.val := by
        have := h_start1; simp only [h_step_val] at this; exact this
      refine ⟨h_lt, h_start1_val, h_end1, ?_, h_sb1, h_ne, ?_⟩
      · rw [h_end1]; exact h_end_eq
      · rw [h_start1_val]
        simp only [Nat.min_def]
        split
        · omega
        · rw [h_end_eq]; exact h_data_aligned
  · obtain ⟨⟨opt, iter1⟩, h_eq, h_post⟩ :=
      WP.spec_imp_exists
        (core.iter.adapters.step_by.IteratorStepBy.next_Range_Usize_none_spec iter
          (by omega))
    simp only [WP.uncurry'_pair] at h_post
    obtain ⟨h_opt, h_it⟩ := h_post
    rw [h_eq]
    simp only [bind_tc_ok, h_opt]
    exact ⟨rfl, rfl, by grind⟩

end spqr.chain.KeyHistory.get_loop

/-! # Spec theorem for `spqr::chain::{spqr::chain::KeyHistory}::get`: loop 0

The key-lookup loop of `KeyHistory::get`.  It repeatedly runs the loop body
(`get_loop.body`, specified in `GetLoopBody0.lean`) via the `loop` fixed-point combinator,
threading the `StepBy` iterator over byte offsets `0, 36, 72, …` until the body signals `done`:

  * On `cont iter1` the loop continues with the advanced iterator to examine the next 36-byte
    record.
  * On `done (Err (KeyAlreadyRequested at1), { data := v })` the iterator was exhausted without
    finding a matching counter — the key was not present.
  * On `done (Ok out, self')` the record whose first 4 bytes matched `want` was found: the
    32-byte payload is returned and the record is swap-removed from the backing vector.

**Termination.**  The quantity `iter.iter.end.val - iter.iter.start.val` strictly decreases on
every `cont` step because the iterator start advances by 36 while the end stays fixed.  This
gives the `Nat` termination measure `fun iter => iter.iter.end.val - iter.iter.start.val`.

**Invariant.**  Throughout the loop the iterator end stays equal to `v.length`, the step size
equals `i` (= 36), the iterator start remains 36-aligned with
`iter.iter.start.val ≤ v.length`, and every 36-aligned offset from the original
`iter.iter.start` up to (but not including) the current iterator start has been checked and
does **not** match `want`.

**Completeness.**  Compared to the previous version of this spec, two properties are added:

  1. **Not-found ⇒ exhaustive non-match**: in the error branch we now assert that *no*
     36-aligned record from `iter.iter.start` to the end of the data matches `want`.
  2. **Found ⇒ first match**: in the success branch we now assert that the returned `off`
     is the *first* 36-aligned offset (from `iter.iter.start` onwards) whose 4-byte tag
     equals `want`.

These two additions make the postcondition a *complete* functional specification of the
sequential scan performed by the Rust source.

**Source**: spqr/src/chain.rs -/

namespace spqr.chain.KeyHistory

/-- **Spec theorem for `spqr.chain.KeyHistory.get_loop`**:

Runs the key-lookup loop starting from the given `StepBy` iterator over the flat data vector `v`.
Under the loop invariant — the iterator start is 36-aligned, the iterator end equals `v.length`,
the step size equals `i`, and the data length is 36-aligned and within `Usize.max` — the loop
terminates and returns a pair `(result, self')` satisfying:

  • **Not-found case** (`result = Err (KeyAlreadyRequested at1)`):
      - the error is exactly `KeyAlreadyRequested at1`,
      - the data is unchanged (`self'.data = v.val`),
      - **exhaustive non-match**: no 36-aligned offset from `iter.iter.start` to `v.length`
        has its first 4 bytes equal to `want.val`.

  • **Found case** (`result = Ok out`): a record was found at some 36-aligned offset `off`
    whose first 4 bytes matched `want`, the 32-byte payload is extracted, the record is
    swap-removed, and:
      - `off % 36 = 0`, `iter.iter.start.val ≤ off`, `off + 36 ≤ v.length`
      - `v.val.slice off (off + 4) = want.val` (tag match)
      - **first match**: every 36-aligned offset from `iter.iter.start` up to (but not
        including) `off` does *not* match `want`
      - `out.length = 32`
      - `out = v.val.slice (off + 4) (off + 36)`
      - `self'.data.length = v.length - 36`
      - `self'.data.length ≤ Usize.max`
      - `self'.data.length % 36 = 0`
      - all bytes before `off` are preserved: `∀ j < off, self'.data[j]! = v[j]!`
      - structural swap-remove / truncation identity inherited from `remove_spec`

The proof applies `loop.spec_decr_nat` with the termination measure
`fun iter => iter.iter.end.val - iter.iter.start.val` and the invariant above, discharging
the body obligation with the already-registered `get_loop.body_spec` (via `WP.spec_mono`)
and a case analysis on the `done` / `cont` outcomes. -/
@[step]
theorem get_loop_spec
    (i : Usize) (v : alloc.vec.Vec U8) (at1 : U32)
    (params : proto.pq_ratchet.ChainParams) (want : Array U8 4#usize)
    (iter : core.iter.adapters.step_by.StepBy (core.ops.range.Range Usize))
    (h_i : i = 36#usize)
    (h_bound : v.length ≤ Usize.max)
    (h_data_aligned : v.length % 36 = 0)
    (h_step : iter.step_by = i)
    (h_start_aligned : iter.iter.start.val % 36 = 0)
    (h_end_eq : iter.iter.end = v.length) :
    get_loop i iter v at1 params want ⦃ (p : (core.result.Result (alloc.vec.Vec U8) Error) ×
      chain.KeyHistory) =>
      match p.1 with
      | core.result.Result.Err e =>
          e = Error.KeyAlreadyRequested at1 ∧
          p.2.data = v ∧
          (∀ k, iter.iter.start.val ≤ k → k + 36 ≤ v.length → k % 36 = 0 →
            v.val.slice k (k + 4) ≠ want)
      | core.result.Result.Ok out =>
          ∃ off, off % 36 = 0 ∧
            iter.iter.start.val ≤ off ∧
            off + 36 ≤ v.length ∧
            v.val.slice off (off + 4) = want.val ∧
            (∀ k, iter.iter.start.val ≤ k → k < off → k % 36 = 0 →
              v.val.slice k (k + 4) ≠ want.val) ∧
            out.length = 32 ∧
            out = v.val.slice (off + 4) (off + 36) ∧
            p.2.data.length = v.length - 36 ∧
            p.2.data.length ≤ Usize.max ∧
            p.2.data.length % 36 = 0 ∧
            (∀ j, j < off → p.2.data[j]! = v[j]!) ∧
            (off + 36 < v.length →
              p.2.data = (v.val.setSlice! off
                    (v.val.drop (v.length - 36))).take
                      (v.length - 36)) ∧
            (off + 36 = v.length →
              p.2.data = v.val.take off) ⦄ := by
  unfold get_loop
  apply loop.spec_decr_nat
    (measure := fun iter' => iter'.iter.end - iter'.iter.start)
    (inv := fun iter' =>
      iter'.step_by = i ∧
      iter'.iter.start.val % 36 = 0 ∧
      iter'.iter.end = v.length ∧
      iter.iter.start ≤ iter'.iter.start ∧
      (∀ k, iter.iter.start.val ≤ k → k < iter'.iter.start.val → k % 36 = 0 →
        v.val.slice k (k + 4) ≠ want.val))
  · intro iter' ⟨h_step', h_start_aligned', h_end_eq', h_start_le', h_no_match_before⟩
    have h_body := get_loop.body_spec i v at1 params want iter'
      h_i h_bound h_data_aligned h_step' h_start_aligned' h_end_eq'
    apply WP.spec_mono h_body
    intro cf h_cf
    match cf with
    | .done (result, self') =>
      match result with
      | .Err e =>
        obtain ⟨h_err, h_data, h_exhausted⟩ := h_cf
        refine ⟨h_err, h_data, ?_⟩
        intro k hk_lo hk_hi hk_aligned
        have : k < iter'.iter.start := by
          simp [h_end_eq'] at h_exhausted; grind
        exact h_no_match_before k hk_lo this hk_aligned
      | .Ok out =>
        obtain ⟨h_aligned, h_36, h_slice, h_out_len, h_out_val,
          h_self_len, h_self_bound, h_self_aligned, h_pres, h_swap, h_trunc⟩ := h_cf
        exact ⟨iter'.iter.start.val, h_aligned, h_start_le', h_36, h_slice,
          h_no_match_before,
          h_out_len, h_out_val,
          h_self_len, h_self_bound, h_self_aligned, h_pres, h_swap, h_trunc⟩
    | .cont iter1 =>
      obtain ⟨h_lt, h_start1, h_end1, h_end1_le, h_sb1, h_ne, h_aligned1⟩ := h_cf
      have h_i_val : i.val = 36 := by
        have := congrArg UScalar.val h_i
        simp only [UScalar.ofNatCore_val_eq] at this
        exact this
      have h_step_val : iter'.step_by.val = 36 := by
        have := congrArg UScalar.val h_step'
        rw [h_i_val] at this
        exact this
      have h_36_le : iter'.iter.start.val + 36 ≤ iter'.iter.end.val := by
        have ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero h_start_aligned'
        have ⟨m, hm⟩ := Nat.dvd_of_mod_eq_zero h_data_aligned
        rw [h_end_eq']; grind
      have h_start1_eq : iter1.iter.start.val = iter'.iter.start.val + 36 := by
        rw [h_start1]; exact Nat.min_eq_left (by omega)
      have h_end1_eq : iter1.iter.end.val = iter'.iter.end.val := by
        exact congrArg UScalar.val h_end1
      refine ⟨⟨h_sb1 ▸ h_step', ?_, ?_, ?_, ?_⟩, ?_⟩
      · rw [h_start1_eq]; omega
      · rw [h_end1_eq]; exact h_end_eq'
      · grind
      · intro k hk_lo hk_hi hk_aligned
        rw [h_start1_eq] at hk_hi
        by_cases hk_lt : k < iter'.iter.start.val
        · exact h_no_match_before k hk_lo hk_lt hk_aligned
        · have : k = iter'.iter.start.val := by
            have ⟨a, ha⟩ := Nat.dvd_of_mod_eq_zero hk_aligned
            have ⟨b, hb⟩ := Nat.dvd_of_mod_eq_zero h_start_aligned'
            omega
          rw [this]; exact h_ne
      · rw [h_start1_eq, h_end1_eq]; omega
  · exact ⟨h_step, h_start_aligned, h_end_eq, le_refl _,
      fun _ h1 h2 _ => absurd h2 (not_lt.mpr h1)⟩

/-! # Spec theorem for `spqr::chain::{spqr::chain::KeyHistory}::get`

Looks up a key by its counter tag `at1` in the flat 36-byte-record backing vector.
Asserts 36-alignment, checks the trimmed guard (`at1 + maxOoo < current_ctr`), then
scans records via `get_loop`. Three outcomes:

- **Trimmed**: key too old → `Err (KeyTrimmed at1)`, history unchanged.
- **Not found**: scan exhausted → `Err (KeyAlreadyRequested at1)`, history unchanged.
- **Found**: extracts 32-byte payload, swap-removes the record via `remove`, returns
  `Ok out` with structural invariants preserved.

Preconditions model the Rust `assert_eq!` panic (36-alignment) and the `u32` overflow
on `at1 + max_ooo` as partial-correctness requirements. The found-case inlines
`remove_spec`'s swap-remove semantics. `∃ off` (not `∃! off`) suffices because the
"first match" conjunct already pins uniqueness.

**Source**: spqr/src/chain.rs-/
@[step]
theorem get_spec (self : chain.KeyHistory) (at1 : U32)
    (current_ctr : U32) (params : proto.pq_ratchet.ChainParams)
    (h_data_aligned : self.data.length % 36 = 0)
    (h_bound : self.data.length ≤ Usize.max)
    (h_ooo_no_overflow : at1 + (chain.maxOoo params).val ≤ U32.max) :
    get self at1 current_ctr params ⦃ (p : (core.result.Result (alloc.vec.Vec U8) Error) ×
      chain.KeyHistory) =>
      let max_ooo : Nat := (chain.maxOoo params).val
      match p.1 with
      | core.result.Result.Err e =>
          (e = Error.KeyTrimmed at1 ∧ at1 + max_ooo < current_ctr ∧ p.2 = self) ∨
          (e = Error.KeyAlreadyRequested at1 ∧
           current_ctr ≤ at1 + max_ooo ∧
           p.2 = self ∧
           (∀ k, k + 36 ≤ self.data.length → k % 36 = 0 →
             self.data.val.slice k (k + 4) ≠ core.num.U32.to_be_bytes at1))
      | core.result.Result.Ok out =>
          current_ctr ≤ at1 + max_ooo ∧
          ∃ off, off % 36 = 0 ∧
            off + 36 ≤ self.data.length ∧
            self.data.val.slice off (off + 4) = (core.num.U32.to_be_bytes at1).val ∧
            (∀ k, k < off → k % 36 = 0 →
              self.data.val.slice k (k + 4) ≠ (core.num.U32.to_be_bytes at1).val) ∧
            out.length = 32 ∧
            out = self.data.val.slice (off + 4) (off + 36) ∧
            p.2.data.length = self.data.length - 36 ∧
            p.2.data.length ≤ Usize.max ∧
            p.2.data.length % 36 = 0 ∧
            (∀ j, j < off → p.2.data[j]! = self.data[j]!) ∧
            (off + 36 < self.data.length →
              p.2.data = (self.data.val.setSlice! off
                    (self.data.val.drop (self.data.length - 36))).take
                      (self.data.length - 36)) ∧
            (off + 36 = self.data.length →
              p.2.data = self.data.val.take off) ⦄ := by
  unfold get
  step*
  · unfold chain.maxOoo at h_ooo_no_overflow
    rcases Classical.em (params.max_ooo_keys > 0#u32) with hpos | hnpos
    · have := i2_post1.2 hpos; subst this
      simp only [hpos, ite_true] at h_ooo_no_overflow; omega
    · simp only [gt_iff_lt, not_lt] at hnpos
      have hz : params.max_ooo_keys = 0#u32 := by scalar_tac
      have := i2_post2.2 (Or.inl hz); subst this
      simp only [hz] at h_ooo_no_overflow
      have := DEFAULT_CHAIN_PARAMS_spec.2; grind
  · unfold chain.maxOoo
    split
    · rename_i h_trimmed
      simp only [UScalar.lt_equiv] at h_trimmed
      step*
    · rename_i h_not_trimmed
      simp only [UScalar.lt_equiv, not_lt] at h_not_trimmed
      have hz : params.max_ooo_keys.val ≤ 0 := h_not_trimmed
      have hpz : params.max_ooo_keys = 0#u32 := by scalar_tac
      have hi2_eq : i2 = chain.DEFAULT_CHAIN_PARAMS.max_ooo_keys := i2_post2.2 (Or.inl hpz)
      have hdef := DEFAULT_CHAIN_PARAMS_spec.2
      have hi2_val : i2.val = 2000 := by rw [hi2_eq]; simp
      unfold chain.maxOoo at h_ooo_no_overflow
      simp only [hpz, gt_iff_lt] at h_ooo_no_overflow
      rename_i h_trimmed2
      simp only [UScalar.lt_equiv] at h_trimmed2
      left; grind
  · -- non-trimmed branch: current_ctr ≤ at1 + maxOoo params
    have h_not_trimmed : current_ctr ≤ at1 + (chain.maxOoo params).val := by
      unfold chain.maxOoo
      rcases Classical.em (params.max_ooo_keys > 0#u32) with hpos | hnpos
      · have hi2_eq := i2_post1.2 hpos; subst hi2_eq
        simp only [hpos, ite_true]; scalar_tac
      · simp only [gt_iff_lt, not_lt] at hnpos
        have hpz : params.max_ooo_keys = 0#u32 := by scalar_tac
        have hi2_eq := i2_post2.2 (Or.inl hpz)
        have hdef := DEFAULT_CHAIN_PARAMS_spec.2
        simp only [hpz, gt_iff_lt]
        subst hi2_eq; scalar_tac
    have h_start_zero : iter.iter.start = 0#usize := by
      have := congrArg (·.start) iter_post1
      simp only at this
      exact this
    have h_start_val : iter.iter.start.val = 0 := by
      rw [h_start_zero]
      simp
    rw [want_post] at p_post
    revert p_post; cases p.1 with
    | Err e =>
      intro p_post
      obtain ⟨h_err, h_data, h_exhausted⟩ := p_post
      right; exact ⟨h_err, h_not_trimmed, by
        have : p.2.data = self.data := h_data
        cases hp : p.2; cases hs : self; simp only [chain.KeyHistory.mk.injEq]
        rw [hp, hs] at this; exact this, fun k hk hk_align =>
        h_exhausted k (by omega) hk hk_align⟩
    | Ok out =>
      intro p_post
      obtain ⟨off, h_aligned, h_start_le, h_36, h_slice, h_no_match, h_out_len, h_out_val,
        h_self_len, h_self_bound, h_self_aligned, h_pres, h_swap, h_trunc⟩ := p_post
      exact ⟨h_not_trimmed, off, h_aligned, h_36, h_slice,
        fun k hk hk_align => h_no_match k (by omega) hk hk_align,
        h_out_len, h_out_val,
        h_self_len, h_self_bound, h_self_aligned, h_pres, h_swap, h_trunc⟩

end spqr.chain.KeyHistory
