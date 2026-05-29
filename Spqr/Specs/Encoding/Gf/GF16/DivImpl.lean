/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Spqr.Specs.Encoding.Gf.GF16.Mul

/-! # Spec theorem for `spqr::encoding::gf::{impl ops::Div for GF16}::div_impl`

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

open Aeneas Aeneas.Std Result core.ops.range I32.Insts.CoreIterRangeStep core.iter.range

namespace spqr.encoding.gf.GF16

/-- **Spec and proof concerning `core.iter.range.IteratorRange.next core.iter.range.StepUsize`**:

The `next` method of the `Iterator` instance for `Range<usize>`, specified at the WP / postcondition
level: on a `range : Range Usize`, `next` returns `(opt, range')` where:

* if `range.start.val ≥ range.end.val` (the range is exhausted), then `opt = none` and `range' =
  range` (the iterator is unchanged);
* if `range.start.val < range.end.val` (the range still has an element), then `opt = some
  range.start`, `range'.start.val = range.start.val + 1`, and `range'.end = range.end` (the upper
  bound is preserved). -/
@[step]
theorem next_spec (range : Range Usize) :
    IteratorRange.next StepUsize range ⦃ (opt, range') =>
      (¬ range.start.val < range.end.val → opt = none ∧ range' = range) ∧
      (range.start.val < range.end.val →
            opt = some range.start ∧
            range'.start.val = range.start.val + 1 ∧
            range'.end = range.end) ⦄ := by
  suffices h : ∃ opt range',
      IteratorRange.next StepUsize range
        = ok (opt, range') ∧
      (¬ range.start.val < range.end.val → opt = none ∧ range' = range) ∧
      (range.start.val < range.end.val →
          opt = some range.start ∧
          range'.start.val = range.start.val + 1 ∧
          range'.end = range.end) by grind
  simp only [IteratorRange.next]
  simp only [liftFun2, liftFun1, core.clone.impls.CloneUsize.clone, bind_tc_ok, not_lt]
  have h_lt_iff :
      (core.cmp.impls.PartialOrdUsize.lt range.start range.end = true) =
      (range.start.val < range.end.val) := by
    simp [core.cmp.impls.PartialOrdUsize.lt]
  simp only [h_lt_iff]
  by_cases hlt : range.start.val < range.end.val
  · rw [if_pos hlt]
    have hbound : range.start.val + 1 ≤ Usize.max := by scalar_tac
    refine ⟨some range.start,
            {range with start := ⟨range.start.val + 1, by scalar_tac⟩},
            ?_, ?_, ?_⟩
    · simp only [StepUsize.forward_checked, bind_tc_ok]
      have hca := Usize.checked_add_bv_spec range.start 1#usize
      rcases heq : Usize.checked_add range.start 1#usize with _ | z
      · scalar_tac
      · simp only
        have hzval : z.val = range.start.val + 1 := by scalar_tac
        congr 4
        exact UScalar.eq_of_val_eq hzval
    · grind
    · intro _
      exact ⟨rfl, rfl, rfl⟩
  · rw [if_neg hlt]
    exact ⟨none, range, rfl, fun _ => ⟨rfl, rfl⟩, fun h => absurd h hlt⟩

/-- **Spec theorem for `Step<i32>::forward_checked` with step 1**

* if `start.val + 1 ≤ I32.max` the returned option is `some z` with `z.val = start.val + 1`;
* otherwise the returned option is `none`. -/
@[step]
private theorem I32_forward_checked_one_spec
    (start : I32) :
    forward_checked start 1#usize ⦃ (opt : Option I32) =>
      (start.val + 1 ≤ I32.max → ∃ z, opt = some z ∧ z.val = start.val + 1) ∧
      (¬ start.val + 1 ≤ I32.max → opt = none) ⦄ := by
  suffices h : ∃ opt,
      forward_checked start 1#usize = ok opt ∧
      (start.val + 1 ≤ I32.max →
          ∃ z, opt = some z ∧ z.val = start.val + 1) ∧
      (¬ start.val + 1 ≤ I32.max → opt = none) by grind
  unfold forward_checked
  have htry := IScalar.tryMkOpt_eq .I32 (start.val + ↑(1#usize).val)
  generalize IScalar.tryMkOpt .I32 (start.val + ↑(1#usize).val) = opt at htry ⊢
  cases opt with
  | none => grind
  | some z =>
    refine ⟨some z, rfl, fun _ => ⟨z, rfl, ?_⟩, fun h => ?_⟩
    · grind
    · grind

/-- **Spec theorem for `Range<i32>` iterator `next`**:

The `next` method of the `Iterator` instance for `Range<i32>`, specified at the WP / postcondition
level: on an `iter : Range I32`, `next` returns `(opt, iter')` where:

* if `iter.start.val ≥ iter.end.val` (the range is exhausted), then `opt = none` and `iter' =
  iter` (the iterator is unchanged);
* if `iter.start.val < iter.end.val` (the range still has an element), then `opt = some
  iter.start`, `iter'.start.val = iter.start.val + 1`, and `iter'.end = iter.end` (the upper bound
  is preserved). -/
@[step]
private theorem IteratorRange_next_I32_spec
    (iter : Range I32) :
    IteratorRange.next I32.Insts.CoreIterRangeStep iter ⦃ (opt, iter1) =>
      (¬ iter.start.val < iter.end.val →
            opt = none ∧ iter1 = iter) ∧
      (iter.start.val < iter.end.val →
            opt = some iter.start ∧
            iter1.start.val = iter.start.val + 1 ∧
            iter1.end = iter.end) ⦄ := by
  simp only [IteratorRange.next]
  simp only [liftFun2, liftFun1, core.clone.impls.CloneI32.clone, bind_tc_ok]
  have h_lt_iff :
      (core.cmp.impls.PartialOrdI32.lt iter.start iter.end = true) =
      (iter.start.val < iter.end.val) := by
    simp [core.cmp.impls.PartialOrdI32.lt]
  simp only [h_lt_iff]
  by_cases hlt : iter.start.val < iter.end.val
  · rw [if_pos hlt]
    have hbound : iter.start.val + 1 ≤ I32.max := by scalar_tac
    step
    grind
  · rw [if_neg hlt]
    grind

/-- **Spec theorem for `encoding.gf.GF16.div_impl_loop.body`**:

• The function always succeeds (no panic) for any `(iter, square, out)`, since the underlying
  iterator advance and `unaccelerated.mul` are total.
• On `done` the result accumulator coincides with the input `out`:
    `(result.value.val.toGF216 : GF216) = out.value.val.toGF216`.
• On `cont (_, square', out')` the new state satisfies the iterated-
  squaring recurrence
    `out'.toGF216 = out.toGF216 * square.toGF216`,
    `square'.toGF216 = square.toGF216 * square.toGF216`.

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
    `out'.toGF216 = out.toGF216 * square.toGF216`,
    `square'.toGF216 = square.toGF216 * square.toGF216`.

**Source**: spqr/src/encoding/gf.rs (lines 451:8-454:9)
-/
@[step]
theorem div_impl_loop_body_spec
    (iter : Range I32)
    (square out : GF16) :
    div_impl_loop.body iter square out ⦃ (cf : ControlFlow (Range I32 × GF16 × GF16) GF16) =>
      match cf with
      | ControlFlow.done result => result.toGF216 = out.toGF216
      | ControlFlow.cont (_, square', out') =>
          out'.toGF216 = out.toGF216 * square.toGF216 ∧
          square'.toGF216 = square.toGF216 * square.toGF216 ⦄ := by
  unfold div_impl_loop.body
  step
  cases o with
  | none => grind
  | some _ => step*

/-- **spec theorem for `encoding.gf.GF16.div_impl_loop`**:

The iterated-squaring loop driving `GF16::div_impl`, specified at the GF(2¹⁶) level by the
closed-form iterated-squaring identity:

  `result.toGF216 = out.toGF216 * square.toGF216 ^ (2 ^ (iter.end.val - iter.start.val).toNat - 1)`.

Specialised to the entry point `(iter, square, out) = (1..16, other², self)` this collapses to `self
· (other²)^(2¹⁵ − 1) = self · other^(2¹⁶ − 2)`, i.e. division in GF(2¹⁶). -/
theorem div_impl_loop_spec
    (iter : Range I32)
    (square out : GF16)
    (h_le : iter.start.val ≤ iter.end.val) :
    div_impl_loop iter square out ⦃ (result : GF16) =>
      result.toGF216 = out.toGF216 *
        square.toGF216 ^
            (2 ^ (iter.end.val - iter.start.val).toNat - 1) ⦄ := by
  unfold div_impl_loop
  apply loop.spec_decr_nat
    (measure := fun p : Range I32 × GF16 × GF16 => (p.1.end.val - p.1.start.val).toNat)
    (inv := fun p : Range I32 × GF16 × GF16 =>
        p.1.end = iter.end ∧
        iter.start.val ≤ p.1.start.val ∧
        p.1.start.val ≤ iter.end.val ∧
        p.2.1.value.val.toGF216 =
          square.value.val.toGF216 ^ (2 ^ (p.1.start.val - iter.start.val).toNat) ∧
        p.2.2.value.val.toGF216 = out.value.val.toGF216 *
            square.value.val.toGF216 ^
              (2 ^ (p.1.start.val - iter.start.val).toNat - 1))
  · rintro ⟨iter', sq', out'⟩ ⟨h_end, h_ge, h_le', h_sq, h_out⟩
    simp only  at h_end h_ge h_le' h_sq h_out
    simp only
    unfold div_impl_loop.body
    step
    split
    · step*
      simp [GF16.toGF216]
      grind
    · step*
      have hk1 :
          (iter1.start.val - iter.start.val).toNat =
            (iter'.start.val - iter.start.val).toNat + 1 := by grind
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · grind
      · grind
      · grind
      · simp only [GF16.toGF216]at square1_post
        rw [square1_post, h_sq, ← pow_add, hk1, pow_succ]
        grind
      · simp only [GF16.toGF216] at out1_post
        rw [out1_post, h_sq, h_out, mul_assoc, ← pow_add]
        grind
      · grind
  · grind

/-! # Spec theorem for `encoding.gf.GF16.div_impl` (Fermat-style division via iterated squaring)

In GF(2¹⁶) — the Galois field with 65536 elements — every non-zero element `b` satisfies `b^(2¹⁶ −
1) = 1`, so the multiplicative inverse is `b⁻¹ = b^(2¹⁶ − 2)` and `a / b = a · b^(2¹⁶ − 2)`.  The
exponent `2¹⁶ − 2 = 2 · (2¹⁵ − 1)` is computed by iterated squaring: starting from `square = b²` and
`out = a`, one repeats
  `out = out · square;  square = square²`
for the 15 indices `i = 1, …, 15`, after which
  `out = a · (b²)^(2¹⁵ − 1) = a · b^(2¹⁶ − 2) = a / b`.

**Source**: spqr/src/encoding/gf.rs -/


/-- **Spec theorem for `encoding.gf.GF16.div_impl`**:

• The function always succeeds (no panic) for any pair of `GF16` inputs, since the underlying
  `unaccelerated.mul` and the loop driver are total on `GF16 × GF16`.
• Lifting `result.value.val` into `GF216` via the canonical map
  `Nat.toGF216 = BinaryPoly.toGF216 ∘ natToBinaryPoly` yields the GF(2¹⁶) Fermat-style
  quotient of the similarly-lifted inputs:
    `result.toGF216 = self.toGF216 * other.toGF216 ^ (2 ^ 16 − 2)`
  where the operations on the right-hand side are performed in
  `GF216 = GaloisField 2 16`.  When `other ≠ 0` Fermat's little
  theorem in GF(2¹⁶) gives `other^(2¹⁶ − 1) = 1`, so
  `other^(2¹⁶ − 2) = other⁻¹` and the right-hand side is genuinely
  the field quotient `self / other`. -/
@[step]
theorem div_impl_spec (self other : GF16) :
    div_impl self other ⦃ (result : GF16) =>
      result.toGF216 = self.toGF216 * other.toGF216 ^ (2 ^ 16 - 2) ⦄ := by
  unfold div_impl
  step*
  have h_loop :=  div_impl_loop_spec { start := 1#i32, «end» := 16#i32 } square self (by norm_num)
  simp [square_post, ← pow_two, ← pow_mul ] at h_loop
  simp [h_loop]

end spqr.encoding.gf.GF16
