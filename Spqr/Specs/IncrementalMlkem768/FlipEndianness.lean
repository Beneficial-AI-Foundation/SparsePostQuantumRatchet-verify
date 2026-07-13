/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Zhang Liao
-/
import SrcTranslated.Funs
import SrcTranslated.FunsExternal
import Spqr.Specs.Aeneas.VecClone

/-! # Spec theorem for `spqr::incremental_mlkem768::flip_endianness_of_encapsulation_state`

`flip_endianness_of_encapsulation_state` repairs an encapsulation state whose 16-bit words
were persisted with the wrong endianness (libcrux issue #1275): it clones the input byte
vector and swaps every adjacent byte pair in the prefix `[0, len - 32)`, leaving the final
32 bytes (the `randomness` field of `EncapsState`) untouched.  The Rust loop is
`for i in (0..fixed_es.len() - 32).step_by(2) { swap(fixed_es[i], fixed_es[i+1]) }`.

The Rust contract (`hax_lib`) is:
  `requires es.len() % 2 == 0 && es.len() == 2080`
  `ensures  |result| result.len() == es.len()`

The specification proved here is *functional* and slightly more general than the Rust
contract: for any input with even length `> 32` (the two `assert!`s at the top of the Rust
body require exactly evenness and `len > 32`; evenness also makes `len - 32` even so the
stepped loop never straddles the boundary), the function succeeds and returns a vector of
the same length whose prefix `[0, len - 32)` is the input with each byte pair swapped
(`result[k] = es[k+1]` for even `k`, `result[k] = es[k-1]` for odd `k`) and whose suffix
`[len - 32, len)` equals the input.  The Rust `ensures` is the first conjunct.  The call
site (`potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275`) always passes a
2080-byte state, which satisfies the preconditions.

The loop iterates a `StepBy (Range Usize)` iterator with step 2; the proof uses the Aeneas
step specs `IteratorStepBy.next_range_Usize_step_spec` / `_none_step_spec` and lifts the
body spec through `loop.spec_decr_nat` with measure `end - start`.  The parity invariants
(`start` and `end` both even) guarantee `start + 2 ≤ end` whenever `start < end`, so the
strong (non-saturating) iterator spec applies.

**Source**: src/incremental_mlkem768.rs (lines 143:0-151:1)
-/

open Aeneas Aeneas.Std Result

namespace spqr.incremental_mlkem768.flip_endianness_of_encapsulation_state_loop

/-! # Spec theorem for `flip_endianness_of_encapsulation_state`: loop body

One iteration of the byte-swapping loop.  If the range is exhausted (`start ≥ end`) the body
returns `done` with the vector unchanged; otherwise it returns `cont`, the iterator advances
by 2, and the byte pair at `(start, start + 1)` is swapped, all other entries unchanged.  The
parity preconditions (`start` and `end` even) guarantee `start + 2 ≤ end` whenever
`start < end`, so the non-saturating `StepBy` iterator spec applies and both indexing
operations are in bounds.  The proof case-splits on `start < end` and uses the Aeneas step
specs `IteratorStepBy.next_range_Usize_step_spec` / `_none_step_spec`. -/

/-- **Spec theorem for `flip_endianness_of_encapsulation_state_loop.body`**:

One step of the byte-swapping loop.
- Preconditions: the iterator steps by 2, its `start` and `end` are even, and `end` does not exceed
  the vector length.
- In the **done** case the vector is unchanged and the range is exhausted.
- In the **cont** case the iterator advances by 2 and the byte pair at `(start, start + 1)` is
  swapped, all other entries unchanged. -/
@[step]
theorem body_spec
    (iter : core.iter.adapters.step_by.StepBy (core.ops.range.Range Usize))
    (fixed_es : alloc.vec.Vec U8)
    (h_step : iter.step_by.val = 2)
    (h_start_even : iter.iter.start.val % 2 = 0)
    (h_end_even : iter.iter.end.val % 2 = 0)
    (h_end_le : iter.iter.end.val ≤ fixed_es.length) :
    body iter fixed_es ⦃ cf =>
      match cf with
      | ControlFlow.done out =>
          out = fixed_es ∧ ¬(iter.iter.start.val < iter.iter.end.val)
      | ControlFlow.cont (iter1, out) =>
          iter.iter.start.val < iter.iter.end.val ∧
          iter1.iter.start.val = iter.iter.start.val + 2 ∧
          iter1.iter.end = iter.iter.end ∧
          iter1.step_by = iter.step_by ∧
          out.length = fixed_es.length ∧
          out[iter.iter.start.val]! = fixed_es[iter.iter.start.val + 1]! ∧
          out[iter.iter.start.val + 1]! = fixed_es[iter.iter.start.val]! ∧
          (∀ k < fixed_es.length, k ≠ iter.iter.start.val → k ≠ iter.iter.start.val + 1 →
            out[k]! = fixed_es[k]!) ⦄ := by
  unfold body
  by_cases h_lt : iter.iter.start.val < iter.iter.end.val
  · obtain ⟨⟨opt, iter1⟩, h_eq, h_post⟩ :=
      WP.spec_imp_exists
        (core.iter.adapters.step_by.IteratorStepBy.next_range_Usize_step_spec iter h_lt
          (by omega) (by omega))
    simp only [WP.uncurry'_pair] at h_post
    obtain ⟨h_opt, h_start1, h_end1, h_sb1⟩ := h_post
    rw [h_eq]
    simp only [bind_tc_ok, h_opt]
    have h_i_lt : iter.iter.start.val < fixed_es.length := by omega
    have h_i1_lt : iter.iter.start.val + 1 < fixed_es.length := by omega
    step as ⟨i1, h_i1⟩
    step as ⟨i2, h_i2⟩
    step as ⟨i3, h_i3⟩
    step as ⟨x0, index_mut_back, h_x0, h_back⟩
    simp only [h_back]
    step as ⟨x1, index_mut_back1, h_x1, h_back1⟩
    simp only [h_back1]
    grind
  · obtain ⟨⟨opt, iter1⟩, h_eq, h_post⟩ :=
      WP.spec_imp_exists
        (core.iter.adapters.step_by.IteratorStepBy.next_range_Usize_none_step_spec iter
          (by omega))
    simp only [WP.uncurry'_pair] at h_post
    obtain ⟨h_opt, h_it⟩ := h_post
    rw [h_eq]
    simp only [bind_tc_ok, h_opt]
    grind


/-! # Spec theorem for `flip_endianness_of_encapsulation_state`: loop

The full byte-swapping loop, driving the body to completion.  Loop invariant: `start` is even
and bounded by `end`, the vector keeps its length, the already-processed prefix `[0, start)`
holds the swapped bytes of the reference vector `es`, and the unprocessed suffix `[start, len)`
still equals `es`.  The proof lifts `body_spec` via `loop.spec_decr_nat` with measure
`end - start`. -/


/-- **Spec theorem for `flip_endianness_of_encapsulation_state_loop`**:

Given a step-2 iterator over `[start, end)` with `start`, `end` even, `end ≤ es.length`, and a
working vector `fixed_es` that agrees with the reference vector `es` on `[start, len)` and holds
swapped bytes on `[0, start)`, the loop succeeds and returns the full swap of `es` on `[0, end)`
with the suffix `[end, len)` unchanged. -/
@[step]
theorem loop_spec
    (es : alloc.vec.Vec U8)
    (iter : core.iter.adapters.step_by.StepBy (core.ops.range.Range Usize))
    (fixed_es : alloc.vec.Vec U8)
    (h_step : iter.step_by.val = 2)
    (h_start_even : iter.iter.start.val % 2 = 0)
    (h_end_even : iter.iter.end.val % 2 = 0)
    (h_start_le : iter.iter.start.val ≤ iter.iter.end.val)
    (h_end_le : iter.iter.end.val ≤ es.length)
    (h_len : fixed_es.length = es.length)
    (h_suffix : ∀ k, iter.iter.start.val ≤ k → k < es.length → fixed_es[k]! = es[k]!)
    (h_prefix : ∀ k < iter.iter.start.val,
      fixed_es[k]! = if k % 2 = 0 then es[k + 1]! else es[k - 1]!) :
    flip_endianness_of_encapsulation_state_loop iter fixed_es ⦃ (result : alloc.vec.Vec U8) =>
      result.length = es.length ∧
      (∀ k < iter.iter.end.val, result[k]! = if k % 2 = 0 then es[k + 1]! else es[k - 1]!) ∧
      (∀ k, iter.iter.end.val ≤ k → k < es.length → result[k]! = es[k]!) ⦄ := by
  unfold flip_endianness_of_encapsulation_state_loop
  apply loop.spec_decr_nat
    (measure := fun (p : core.iter.adapters.step_by.StepBy (core.ops.range.Range Usize) ×
      alloc.vec.Vec U8) => p.1.iter.end.val - p.1.iter.start.val)
    (inv := fun (p : core.iter.adapters.step_by.StepBy (core.ops.range.Range Usize) ×
      alloc.vec.Vec U8) =>
      let it' := p.1
      let v' := p.2
      it'.iter.end = iter.iter.end ∧
      it'.step_by = iter.step_by ∧
      it'.iter.start.val % 2 = 0 ∧
      it'.iter.start.val ≤ it'.iter.end.val ∧
      v'.length = es.length ∧
      (∀ k, it'.iter.start.val ≤ k → k < es.length → v'[k]! = es[k]!) ∧
      (∀ k < it'.iter.start.val, v'[k]! = if k % 2 = 0 then es[k + 1]! else es[k - 1]!))
  · rintro ⟨it', v'⟩ ⟨h_end', h_sb', h_even', h_le', h_len', h_suf', h_pre'⟩
    simp only [] at h_end' h_sb' h_even' h_le' h_len' h_suf' h_pre' ⊢
    have h_body := body_spec it' v' (by grind) (by grind) (by grind) (by grind)
    apply WP.spec_mono h_body
    rintro (⟨iter1, out⟩ | out)
    · rintro ⟨h_lt, h_start1, h_end1, h_sb1, h_out_len, h_swap0, h_swap1, h_frame⟩
      have h_end_val : it'.iter.end.val = iter.iter.end.val := by rw [h_end']
      have h_end1_val : iter1.iter.end.val = it'.iter.end.val := by rw [h_end1]
      have h_s2 : it'.iter.start.val + 2 ≤ it'.iter.end.val := by omega
      simp only []
      refine ⟨⟨by rw [h_end1, h_end'], by rw [h_sb1, h_sb'], by omega, by omega, by omega, ?_, ?_⟩,
        by omega⟩
      · intro k hk hk'
        rw [h_frame k (by omega) (by omega) (by omega), h_suf' k (by omega) hk']
      · intro k hk
        rw [h_start1] at hk
        by_cases hk0 : k = it'.iter.start.val
        · subst hk0
          rw [h_swap0, if_pos h_even', h_suf' _ (by omega) (by omega)]
        · by_cases hk1 : k = it'.iter.start.val + 1
          · subst hk1
            rw [h_swap1, if_neg (by omega), h_suf' _ (by omega) (by omega)]
            simp
          · rw [h_frame k (by omega) hk0 hk1, h_pre' k (by omega)]
    · rintro ⟨h_out, h_done⟩
      subst h_out
      have h_end_val : it'.iter.end.val = iter.iter.end.val := by rw [h_end']
      have h_stop : it'.iter.start.val = iter.iter.end.val := by omega
      exact ⟨h_len', fun k hk => h_pre' k (by omega), fun k hk hk' => h_suf' k (by omega) hk'⟩
  · exact ⟨rfl, rfl, h_start_even, h_start_le, h_len, h_suffix, h_prefix⟩

end spqr.incremental_mlkem768.flip_endianness_of_encapsulation_state_loop

/-! # Spec theorem for `spqr::incremental_mlkem768::flip_endianness_of_encapsulation_state` -/

namespace spqr.incremental_mlkem768

/-- **Spec theorem for `incremental_mlkem768.flip_endianness_of_encapsulation_state`**:

For an input vector of even length `> 32` (the two Rust `assert!`s), the function succeeds and
returns a vector of the same length whose prefix `[0, len - 32)` has every adjacent byte pair
swapped (`result[k] = es[k+1]` for even `k`, `result[k] = es[k-1]` for odd `k`) and whose last
32 bytes equal the input.  The Rust contract's `result.len() == es.len()` is the first
conjunct; the call site's `es.len() == 2080` implies both preconditions. -/
@[step]
theorem flip_endianness_of_encapsulation_state_spec
    (es : alloc.vec.Vec U8)
    (h_even : es.length % 2 = 0)
    (h_gt : 32 < es.length) :
    flip_endianness_of_encapsulation_state es ⦃ (result : alloc.vec.Vec U8) =>
      result.length = es.length ∧
      (∀ k < es.length - 32, result[k]! = if k % 2 = 0 then es[k + 1]! else es[k - 1]!) ∧
      (∀ k, es.length - 32 ≤ k → k < es.length → result[k]! = es[k]!) ⦄ := by
  unfold flip_endianness_of_encapsulation_state
  step*
  subst fixed_es
  apply WP.spec_mono
    (flip_endianness_of_encapsulation_state_loop.loop_spec es _ es (by grind)
      (by scalar_tac) (by scalar_tac) (by scalar_tac) (by scalar_tac) rfl
      (fun _ _ _ => rfl) (by scalar_tac))
  rintro result ⟨h_len, h_swap, h_tail⟩
  refine ⟨h_len, fun k hk => ?_, fun k hk hk' => h_tail k (by scalar_tac) hk'⟩
  exact h_swap k (by scalar_tac)

end spqr.incremental_mlkem768
