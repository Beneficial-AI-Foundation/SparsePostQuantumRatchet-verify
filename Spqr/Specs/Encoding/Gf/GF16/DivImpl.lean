/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Spqr.Specs.Encoding.Gf.GF16.Mul
import Spqr.Specs.Encoding.Gf.GF16.MulAssign

/-!
# Spec theorem for `spqr::encoding::gf::{impl ops::Div for GF16}::div_impl`

In GF(2¹⁶) — the Galois field with 65 536 elements — multiplication is polynomial multiplication
modulo the irreducible polynomial POLY = x¹⁶ + x¹² + x³ + x + 1 (0x1100b).  Each field element is
represented as a polynomial of degree < 16 with coefficients in GF(2), stored as a 16-bit unsigned
integer; the `GF16` Rust type is the `u16` wrapper providing the field operations.


The extracted Lean body advances the `1..16` iterator by one step and, depending on whether the
iterator is exhausted, either returns the accumulated `out` (loop exit) or computes the new
`(square', out')` state for the next iteration:
  1. `out1 ← MulAssignGF16.mul_assign out square` — in-place
     `out *= square` delegating to the by-reference `MulAssign`
     instance, which itself delegates to the software (unaccelerated)
     carry-less multiplication `encoding.gf.unaccelerated.mul`.
  2. `square1 ← MulGF16GF16.mul square square` — by-value
     `square = square * square` delegating to the same software
     multiplication kernel.

**Source**: spqr/src/encoding/gf.rs (lines 451:8-454:9)
-/

open Aeneas Aeneas.Std Result
open spqr.encoding.gf

namespace spqr.encoding.gf.GF16

/--
**Spec and proof concerning `core.iter.range.IteratorRange.next core.iter.range.StepUsize`**:

The `next` method of the `Iterator` instance for `Range<usize>`, specified at the WP / postcondition
level: on a `range : Range Usize`, `next` returns `(opt, range')` where:

* if `range.start.val ≥ range.end.val` (the range is exhausted), then `opt = none` and `range' =
  range` (the iterator is unchanged);
* if `range.start.val < range.end.val` (the range still has an element), then `opt = some
  range.start`, `range'.start.val = range.start.val + 1`, and `range'.end = range.end` (the upper
  bound is preserved).

Both branches are derived from the underlying definitions of `core.iter.range.IteratorRange.next`,
`core.iter.range.StepUsize.forward_checked`, `core.cmp.impls.PartialOrdUsize.lt`, and
`core.clone.impls.CloneUsize.clone`, which together implement `Range::next` for `usize` ranges in
Rust.
-/
@[step]
theorem next_spec (range : core.ops.range.Range Usize) :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize range
      ⦃ (opt, range') =>
        (¬ range.start.val < range.end.val →
            opt = none ∧ range' = range) ∧
        (range.start.val < range.end.val →
            opt = some range.start ∧
            range'.start.val = range.start.val + 1 ∧
            range'.end = range.end) ⦄ := by
  suffices h : ∃ opt range',
      core.iter.range.IteratorRange.next core.iter.range.StepUsize range
        = ok (opt, range') ∧
      (¬ range.start.val < range.end.val → opt = none ∧ range' = range) ∧
      (range.start.val < range.end.val →
          opt = some range.start ∧
          range'.start.val = range.start.val + 1 ∧
          range'.end = range.end) by
    obtain ⟨opt, range', heq, h1, h2⟩ := h
    rw [heq]; simp only [WP.spec_ok]
    exact ⟨h1, h2⟩
  simp only [core.iter.range.IteratorRange.next]
  simp only [liftFun2, liftFun1, core.clone.impls.CloneUsize.clone, bind_tc_ok, not_lt]
  have h_lt_iff :
      (core.cmp.impls.PartialOrdUsize.lt range.start range.end = true) =
      (range.start.val < range.end.val) := by
    simp [core.cmp.impls.PartialOrdUsize.lt]
  simp only [h_lt_iff]
  by_cases hlt : range.start.val < range.end.val
  · rw [if_pos hlt]
    have hbound : range.start.val + 1 ≤ Usize.max := by
      have := range.end.hBounds; scalar_tac
    refine ⟨some range.start,
            {range with start := ⟨range.start.val + 1, by scalar_tac⟩},
            ?_, ?_, ?_⟩
    · simp only [core.iter.range.StepUsize.forward_checked, bind_tc_ok]
      have hca := Usize.checked_add_bv_spec range.start 1#usize
      rcases heq : Usize.checked_add range.start 1#usize with _ | z
      · rw [heq] at hca; scalar_tac
      · simp only
        rw [heq] at hca
        obtain ⟨_, hval, _⟩ := hca
        have hzval : z.val = range.start.val + 1 := by scalar_tac
        congr 4
        exact UScalar.eq_of_val_eq hzval
    · intro h; omega
    · intro _; exact ⟨rfl, rfl, rfl⟩
  · rw [if_neg hlt]
    exact ⟨none, range, rfl, fun _ => ⟨rfl, rfl⟩, fun h => absurd h hlt⟩

/--
**Spec theorem for `Step<i32>::forward_checked` with step 1.**

`I32.Insts.CoreIterRangeStep.forward_checked` is now defined concretely (see
`Spqr/Code/FunsExternal.lean`) as
  `fun start n => ok (IScalar.tryMkOpt .I32 (start.val + ↑n.val))`.

This theorem specialises to `n = 1` and derives:
  * The outer `Result` is always `ok`.
  * When `start.val + 1 ≤ I32.max`, the result is `some z` with
    `z.val = start.val + 1`.
  * When `¬ start.val + 1 ≤ I32.max`, the result is `none`.

The proof unfolds the definition, applies `IScalar.tryMkOpt_eq` to characterise the returned
`Option`, and uses `scalar_tac` to discharge the I32 bounds arithmetic.
-/
private theorem I32_forward_checked_one
    (start : Std.I32) :
    ∃ opt,
      I32.Insts.CoreIterRangeStep.forward_checked start 1#usize = ok opt ∧
      (start.val + 1 ≤ I32.max →
          ∃ z, opt = some z ∧ z.val = start.val + 1) ∧
      (¬ start.val + 1 ≤ I32.max → opt = none) := by
  unfold I32.Insts.CoreIterRangeStep.forward_checked
  have htry := IScalar.tryMkOpt_eq .I32 (start.val + ↑(1#usize).val)
  generalize IScalar.tryMkOpt .I32 (start.val + ↑(1#usize).val) = opt at htry ⊢
  cases opt with
  | none =>
    refine ⟨none, rfl, ?_, fun _ => rfl⟩
    intro hle; exfalso; apply htry
    constructor <;> scalar_tac
  | some z =>
    refine ⟨some z, rfl, fun _ => ⟨z, rfl, ?_⟩, fun h => ?_⟩
    · have hv : (↑(1#usize).val : Int) = 1 := by scalar_tac
      rw [hv] at htry; exact htry.1
    · exfalso; apply h
      have hv : (↑(1#usize).val : Int) = 1 := by scalar_tac
      rw [hv] at htry
      have := htry.2; simp at this; scalar_tac

/--
**Spec theorem for `Range<i32>` iterator `next` (totality)**:

The `next` method of the `Iterator` instance for `Range<i32>` always succeeds (returns `ok`).  The
proof unfolds `core.iter.range.IteratorRange.next`, simplifies the transparent `CloneI32.clone` and
`PartialOrdI32.lt` dispatches, then case-splits on whether the range is exhausted.  In the positive
branch, the `forward_checked` call is discharged by the helper theorem `I32_forward_checked_one`; in
the negative branch, `next` returns `(none, iter)` directly.
-/
private theorem IteratorRange_next_I32_ok
    (iter : core.ops.range.Range Std.I32) :
    ∃ o iter1,
      core.iter.range.IteratorRange.next I32.Insts.CoreIterRangeStep iter
        = ok (o, iter1) := by
  simp only [core.iter.range.IteratorRange.next]
  simp only [liftFun2, liftFun1, core.clone.impls.CloneI32.clone, bind_tc_ok]
  have h_lt_iff :
      (core.cmp.impls.PartialOrdI32.lt iter.start iter.end = true) =
      (iter.start.val < iter.end.val) := by
    simp [core.cmp.impls.PartialOrdI32.lt]
  simp only [h_lt_iff]
  by_cases hlt : iter.start.val < iter.end.val
  · rw [if_pos hlt]
    obtain ⟨opt_fc, hfc, hsome, _⟩ := I32_forward_checked_one iter.start
    have hbound : iter.start.val + 1 ≤ I32.max := by
      have := iter.end.hBounds; scalar_tac
    obtain ⟨z, hz_opt, _⟩ := hsome hbound
    subst hz_opt
    rw [hfc]
    simp only [bind_tc_ok]
    exact ⟨some iter.start, { iter with start := z }, rfl⟩
  · rw [if_neg hlt]
    exact ⟨none, iter, rfl⟩

/--
**Spec theorem for `encoding.gf.GF16.div_impl_loop.body`**:

• The function always succeeds (no panic) for any `(iter, square, out)`, since the underlying
  iterator advance and `unaccelerated.mul` are total.
• On `done` the result accumulator coincides with the input `out`:
    `(result.value.val.toGF216 : GF216) = out.value.val.toGF216`.
• On `cont (_, square', out')` the new state satisfies the iterated-
  squaring recurrence
    `out'.toGF216 =
        out.toGF216 * square.toGF216`,
    `square'.toGF216 =
        square.toGF216 * square.toGF216`.

**Per-iteration postcondition for `encoding.gf.GF16.div_impl_loop.body`**:

One iteration of the iterated-squaring loop driving `GF16::div_impl`. Both branches are
characterised at the GF(2¹⁶) level via `Nat.toGF216 = BinaryPoly.toGF216 ∘ natToBinaryPoly`:

* **`done`** — the `1..16` iterator is exhausted; the returned
  accumulator is the unchanged `out`:
    `result.toGF216 = out.toGF216`.

* **`cont`** — the iterator yielded another index; the new state
  `(_, square', out')` satisfies the squaring recurrence (note that,
  unlike `const_div`, the `*=` precedes the squaring, so `out'`
  involves the *old* `square`):
    `out'.toGF216 =
        out.toGF216 * square.toGF216`,
    `square'.toGF216 =
        square.toGF216 * square.toGF216`.

**Source**: spqr/src/encoding/gf.rs (lines 451:8-454:9)
-/
@[step]
theorem div_impl_loop_body_spec
    (iter : core.ops.range.Range Std.I32)
    (square out : spqr.encoding.gf.GF16) :
    div_impl_loop.body iter square out ⦃ cf =>
      match cf with
      | ControlFlow.done result =>
          (result.toGF216 : GF216) = out.toGF216
      | ControlFlow.cont (_, square', out') =>
          (out'.toGF216 : GF216) =
            out.toGF216 * square.toGF216 ∧
          (square'.toGF216 : GF216) =
            square.toGF216 * square.toGF216 ⦄ := by
  unfold div_impl_loop.body
  obtain ⟨o, iter1, hnext⟩ := IteratorRange_next_I32_ok iter
  rw [hnext]
  simp only [bind_tc_ok]
  cases o with
  | none => simp [WP.spec_ok]
  | some _ => step*


/-!
# Spec theorem for `encoding.gf.GF16.div_impl_loop` (closed-form postcondition)

In GF(2¹⁶) — the Galois field with 65 536 elements — multiplication is polynomial multiplication
modulo the irreducible polynomial POLY = x¹⁶ + x¹² + x³ + x + 1 (0x1100b).  Each field element is
represented as a polynomial of degree < 16 with coefficients in GF(2), stored as a 16-bit unsigned
integer.

The loop performs the canonical iterated-squaring schedule: after `k` iterations starting from
`(square, out)`, the accumulators carry

  `square_k = square^(2^k)`,
  `out_k    = out · square^(2^k − 1)`,

so that the geometric series `1 + 2 + 4 + ⋯ + 2^(k−1) = 2^k − 1` fully appears in the exponent of
`out_k`.  For `n = end − start` iterations of an `n`-step iterator, the loop returns `out ·
square^(2^n − 1)`.

Specialised to the entry point `(iter = 1..16, square = other², out = self)`, the loop runs for `n =
15` iterations, giving

  `self · (other²)^(2¹⁵ − 1) = self · other^(2¹⁶ − 2)`,

the Fermat-style inverse `other⁻¹ = other^(2¹⁶ − 2)` multiplied by `self`, i.e. the GF(2¹⁶) quotient
`self / other`.

**Source**: spqr/src/encoding/gf.rs (lines 451:8-454:9)
-/


/--
**Spec theorem strengthening `IteratorRange_next_I32_ok`**:

The `next` method of the `Iterator` instance for `Range<i32>`, specified at the WP / postcondition
level: on a `range : Range I32`, `next` returns `(opt, range')` where:

* if `range.start.val ≥ range.end.val` (the range is exhausted), then `opt = none` and `range' =
  range` (the iterator is unchanged);
* if `range.start.val < range.end.val` (the range still has an element), then `opt = some
  range.start`, `range'.start.val = range.start.val + 1`, and `range'.end = range.end` (the upper
  bound is preserved).

The proof unfolds `core.iter.range.IteratorRange.next` and simplifies the transparent parts
(`CloneI32.clone` is the identity, `PartialOrdI32.lt` reduces to value comparison).  The opaque
`forward_checked` call is discharged by the helper theorem `I32_forward_checked_one`, which
specifies `forward_checked start 1#usize` at the value level.  Since `iter.start.val < iter.end.val`
implies `iter.start.val + 1 ≤ I32.max` (because `iter.end.val ≤ I32.max` from the `I32` bounds), the
theorem yields a `some z` with `z.val = iter.start.val + 1`, matching the expected iterator-advance
semantics.
-/
private theorem IteratorRange_next_I32_post
    (iter : core.ops.range.Range Std.I32) :
    ∃ opt iter1,
      core.iter.range.IteratorRange.next I32.Insts.CoreIterRangeStep iter
        = ok (opt, iter1) ∧
      (¬ iter.start.val < iter.end.val →
          opt = none ∧ iter1 = iter) ∧
      (iter.start.val < iter.end.val →
          opt = some iter.start ∧
          iter1.start.val = iter.start.val + 1 ∧
          iter1.end = iter.end) := by
  simp only [core.iter.range.IteratorRange.next]
  simp only [liftFun2, liftFun1, core.clone.impls.CloneI32.clone, bind_tc_ok]
  have h_lt_iff :
      (core.cmp.impls.PartialOrdI32.lt iter.start iter.end = true) =
      (iter.start.val < iter.end.val) := by
    simp [core.cmp.impls.PartialOrdI32.lt]
  simp only [h_lt_iff]
  by_cases hlt : iter.start.val < iter.end.val
  · rw [if_pos hlt]
    have hbound : iter.start.val + 1 ≤ I32.max := by
      have := iter.end.hBounds; scalar_tac
    obtain ⟨opt_fc, hfc, hsome, _⟩ := I32_forward_checked_one iter.start
    obtain ⟨z, hz_opt, hz_val⟩ := hsome hbound
    subst hz_opt
    rw [hfc]
    simp only [bind_tc_ok]
    exact ⟨some iter.start,
           { iter with start := z },
           rfl,
           fun h => absurd hlt h,
           fun _ => ⟨rfl, hz_val, rfl⟩⟩
  · rw [if_neg hlt]
    exact ⟨none, iter, rfl, fun _ => ⟨rfl, rfl⟩, fun h => absurd h hlt⟩

/--
**Closed-form postcondition for `encoding.gf.GF16.div_impl_loop`**:

The iterated-squaring loop driving `GF16::div_impl`, specified at the GF(2¹⁶) level by the
closed-form iterated-squaring identity:

  `result.toGF216 =
       out.toGF216 *
       square.toGF216 ^
            (2 ^ (iter.end.val - iter.start.val).toNat - 1)`.

Specialised to the entry point `(iter, square, out) = (1..16, other², self)` this collapses to `self
· (other²)^(2¹⁵ − 1) = self · other^(2¹⁶ − 2)`, i.e. division in GF(2¹⁶).

**Source**: spqr/src/encoding/gf.rs (lines 451:8-454:9)
-/
theorem div_impl_loop_spec
    (iter : core.ops.range.Range I32)
    (square out : GF16)
    (h_le : iter.start.val ≤ iter.end.val) :
    div_impl_loop iter square out ⦃ (result : GF16) =>
      result.toGF216 =
        out.toGF216 *
        square.toGF216 ^
            (2 ^ (iter.end.val - iter.start.val).toNat - 1) ⦄ := by
  unfold div_impl_loop
  apply loop.spec_decr_nat
    (measure := fun p : core.ops.range.Range I32 × GF16 × GF16 =>
                  (p.1.end.val - p.1.start.val).toNat)
    (inv := fun p : core.ops.range.Range I32 × GF16 × GF16 =>
        p.1.end = iter.end ∧
        iter.start.val ≤ p.1.start.val ∧
        p.1.start.val ≤ iter.end.val ∧
        (p.2.1.value.val.toGF216 : GF216) =
          square.value.val.toGF216 ^
            (2 ^ (p.1.start.val - iter.start.val).toNat) ∧
        (p.2.2.value.val.toGF216 : GF216) =
          out.value.val.toGF216 *
            square.value.val.toGF216 ^
              (2 ^ (p.1.start.val - iter.start.val).toNat - 1))
  · rintro ⟨iter', sq', out'⟩ ⟨h_end, h_ge, h_le', h_sq, h_out⟩
    simp only [] at h_end h_ge h_le' h_sq h_out
    simp only []
    unfold div_impl_loop.body
    obtain ⟨opt, iter1, hnext, h_done, h_cont⟩ :=
      IteratorRange_next_I32_post iter'
    rw [hnext]
    simp only [bind_tc_ok]
    by_cases h_lt : iter'.start.val < iter'.end.val
    · obtain ⟨h_opt, h_start1, h_end1⟩ := h_cont h_lt
      rw [h_opt]
      simp only [uncurry_apply_pair, Int.lt_toNat, Int.ofNat_toNat, sup_lt_iff, Int.sub_pos,
        and_assoc]
      step*
      have hk1 :
          (iter1.start.val - iter.start.val).toNat =
            (iter'.start.val - iter.start.val).toNat + 1 := by
        have h0 : 0 ≤ iter'.start.val - iter.start.val := by omega
        have h1 : iter1.start.val - iter.start.val =
                    (iter'.start.val - iter.start.val) + 1 := by
          rw [h_start1]; ring
        rw [h1]
        rw [Int.toNat_add (by omega) (by omega)]
        simp
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [h_end1]; exact h_end
      · rw [h_start1]; omega
      · have : iter'.end.val = iter.end.val := by rw [← h_end]
        rw [h_start1]; omega
      · simp only [GF16.toGF216]at square1_post
        rw [square1_post, h_sq, ← pow_add, hk1, pow_succ]
        ring_nf
      · simp only [GF16.toGF216] at out1_post
        rw [out1_post, h_sq, h_out, mul_assoc, ← pow_add]
        have h_2le :
            2 ≤ 2 ^ ((iter'.start.val - iter.start.val).toNat + 1) := by
          calc (2 : Nat) = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ ((iter'.start.val - iter.start.val).toNat + 1) :=
              Nat.pow_le_pow_right (by norm_num) (by omega)
        have h_eq :
            (2 ^ (iter'.start.val - iter.start.val).toNat - 1) +
              2 ^ (iter'.start.val - iter.start.val).toNat =
            2 ^ (iter1.start.val - iter.start.val).toNat - 1 := by
          rw [hk1, pow_succ]
          omega
        rw [h_eq]
      · rw [h_start1, h_end1]
        have h_pos : 0 < iter'.end.val - iter'.start.val := by omega
        have h_eq : iter'.end.val - (iter'.start.val + 1) =
                      (iter'.end.val - iter'.start.val) - 1 := by ring
        rw [h_eq]
        have h_toNat :
            ((iter'.end.val - iter'.start.val) - 1).toNat
              = (iter'.end.val - iter'.start.val).toNat - 1 := by
          have h0 : (0 : Int) ≤ iter'.end.val - iter'.start.val := by omega
          have h1 : (1 : Int) ≤ iter'.end.val - iter'.start.val := by omega
          omega
        simp
        have h0 : 0 < (iter'.end.val - iter'.start.val).toNat := by
          have : (1 : Int) ≤ iter'.end.val - iter'.start.val := by omega
          omega
        omega
    · obtain ⟨h_opt, _⟩ := h_done h_lt
      rw [h_opt]
      simp only [uncurry_apply_pair, Int.lt_toNat, Int.ofNat_toNat, sup_lt_iff, Int.sub_pos,
        and_assoc, WP.spec_ok]
      have h_end' : iter'.end.val = iter.end.val := by rw [← h_end]
      have h_start_eq : iter'.start.val = iter.end.val := by omega
      have h_k_eq :
          (iter'.start.val - iter.start.val).toNat =
            (iter.end.val - iter.start.val).toNat := by
        rw [h_start_eq]
      rw [← h_k_eq]
      exact h_out
  · refine ⟨rfl, le_refl _, h_le, ?_, ?_⟩
    · simp only [Int.sub_self, Int.toNat_zero, pow_zero, pow_one]
    · simp only [Int.sub_self, Int.toNat_zero, pow_zero,
        Nat.sub_self, mul_one]

/-!
# Spec theorem for `encoding.gf.GF16.div_impl` (Fermat-style division via iterated squaring)

In GF(2¹⁶) — the Galois field with 65536 elements — every non-zero element `b` satisfies `b^(2¹⁶ −
1) = 1`, so the multiplicative inverse is `b⁻¹ = b^(2¹⁶ − 2)` and `a / b = a · b^(2¹⁶ − 2)`.  The
exponent `2¹⁶ − 2 = 2 · (2¹⁵ − 1)` is computed by iterated squaring: starting from `square = b²` and
`out = a`, one repeats

  `out = out · square;  square = square²`

for the 15 indices `i = 1, …, 15`, after which

  `out = a · (b²)^(2¹⁵ − 1) = a · b^(2¹⁶ − 2) = a / b`.

The function proceeds in two stages:
  1. The initial squaring `square := other · other` via the
     `Mul<GF16> for GF16` instance, which delegates (through
     `MulAssign<&GF16> for GF16`) to the software (unaccelerated)
     carry-less multiplication `encoding.gf.unaccelerated.mul`.
  2. `div_impl_loop {start := 1, end := 16} square self` — the
     Aeneas-extracted `loop` fixed-point driving the iterated-
     squaring body for 15 rounds, returning the final accumulator
     `out = self · (other²)^(2¹⁵ − 1) = self · other^(2¹⁶ − 2)`.

**Source**: spqr/src/encoding/gf.rs (lines 446:4-456:5)
-/


/--
**Spec theorem for `encoding.gf.GF16.div_impl`**:

• The function always succeeds (no panic) for any pair of `GF16` inputs, since the underlying
  `unaccelerated.mul` and the loop driver are total on `GF16 × GF16`.
• Lifting `result.value.val` into `GF216` via the canonical map
  `Nat.toGF216 = BinaryPoly.toGF216 ∘ natToBinaryPoly` yields the GF(2¹⁶) Fermat-style
  quotient of the similarly-lifted inputs:
    `(result.toGF216 : GF216) =
        self.toGF216 *
        other.toGF216 ^ (2 ^ 16 − 2)`
  where the operations on the right-hand side are performed in
  `GF216 = GaloisField 2 16`.  When `other ≠ 0` Fermat's little
  theorem in GF(2¹⁶) gives `other^(2¹⁶ − 1) = 1`, so
  `other^(2¹⁶ − 2) = other⁻¹` and the right-hand side is genuinely
  the field quotient `self / other`.

**Source**: spqr/src/encoding/gf.rs (lines 446:4-456:5)
-/
@[step]
theorem div_impl_spec (self other : GF16) :
    div_impl self other ⦃ (result : GF16) =>
      result.toGF216 = self.toGF216 * other.toGF216 ^ (2 ^ 16 - 2) ⦄ := by
  unfold div_impl
  have h_loop := fun (square : spqr.encoding.gf.GF16) =>
    div_impl_loop_spec { start := 1#i32, «end» := 16#i32 } square self
      (by scalar_tac)
  step*

end spqr.encoding.gf.GF16
