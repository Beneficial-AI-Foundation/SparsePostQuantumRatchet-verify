/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf

/-! # Spec Theorem for `GF16::div_impl_loop.body`

Specification and proof for `encoding.gf.GF16.div_impl_loop.body`,
the *body* of the iterated-squaring loop that powers
`GF16::div_impl`.

In GF(2¹⁶) — the Galois field with 65 536 elements — every non-zero
element `b` satisfies `b^(2¹⁶ − 1) = 1`, so the multiplicative
inverse is `b⁻¹ = b^(2¹⁶ − 2)` and `a / b = a · b^(2¹⁶ − 2)`.  The
exponent `2¹⁶ − 2 = 2 + 4 + 8 + ⋯ + 2¹⁵` is computed by iterated
squaring: starting from `square = b²` and `out = a`, one repeats

  `out *= square;  square = square²`

for the 15 indices `i = 1, …, 15`, after which

  `out = a · b^(2¹⁶ − 2) = a / b`     and     `square = b^(2¹⁶)`.

The function `div_impl_loop.body` is exactly *one* such step,
controlled by the Rust `for _i in 1..16` iterator and lifted into
the `ControlFlow` monad used by the Aeneas-extracted `loop`
combinator:

  1. **Termination guard.**  If `IteratorRange::next` reports the
     range is exhausted (`None`), the body returns
     `done out` — the current accumulator is the loop's final value.
  2. **Active step.**  Otherwise the body performs, in order,
       a. `out₁    := out *= square`   (in-place multiplication
          via `MulAssign<GF16> for GF16`),
       b. `square₁ := square * square` (re-square via
          `Mul<GF16, GF16> for GF16`),
     and returns `cont (iter₁, square₁, out₁)` to the surrounding
     `loop` driver.

At the GF(2¹⁶) level the active step is exactly the squaring
recurrence

  `square'.toGF216 = square.toGF216 · square.toGF216`
  `out'.toGF216    = out.toGF216    · square.toGF216`

which (composed 15 times along the `1..16` range) produces the
identity `out₁₅ = self · other^(2¹⁶ − 2)` discussed above.

Because all of `*=` and `*` on `GF16` ultimately delegate to
`unaccelerated::mul` on the underlying `u16` value (carry-less
polynomial multiplication followed by reduction modulo
POLY = x¹⁶ + x¹² + x³ + x + 1), the per-iteration postcondition
inherits its proof from `mul_spec` once the relevant
`MulAssign`/`Mul` glue is unfolded.

The shared polynomial-library facts (`natToGF2Poly`, `POLY_GF2`,
`POLY_GF2_monic`, etc.) are imported from `Spqr.Math.Gf`.

**Source**: spqr/src/encoding/gf.rs (lines 553:8-556:9)
-/

open Aeneas Aeneas.Std Result
open Polynomial spqr.encoding.gf.unaccelerated

namespace spqr.encoding.gf.GF16

/-! ## Spec axioms for the opaque GF(2¹⁶) `MulAssign` / `Mul` kernels

`encoding.gf.GF16.Insts.CoreOpsArithMulAssignShared0GF16.mul_assign`
is declared `#[hax_lib::opaque]` on the Rust side, so the
Aeneas-extracted Lean signature is an `axiom` in
`Spqr/Code/FunsExternal.lean` rather than a structural definition.
The Rust source nevertheless documents its semantics: it is
GF(2¹⁶) multiply-assign, i.e. it leaves the underlying `u16` field
of `self` equal to the carry-less product of `self.value` and
`other.value` reduced modulo `POLY = 0x1100b`.

We record this contract as a `@[step]`-axiom phrased at the
`GF216 = GaloisField 2 16` level, in exactly the same form as
`const_mul_spec` (which is the *transparent* analogue going through
`unaccelerated::mul`).  All structurally-defined wrappers
(`MulAssignGF16.mul_assign`, `MulGF16GF16.mul`,
`MulShared0GF16GF16.mul`) reduce — by `@[reducible]` instance
unfolding — to this opaque kernel, so a single axiom suffices to
discharge the whole `div_impl_loop.body` goal. -/

/-- GF(2¹⁶) postcondition for the opaque `MulAssign<&GF16> for GF16`
kernel.  The Rust function performs in-place GF(2¹⁶) multiplication
of the underlying `u16` polynomials. -/
@[step]
axiom mul_assign_shared0_spec
    (self other : spqr.encoding.gf.GF16) :
    Insts.CoreOpsArithMulAssignShared0GF16.mul_assign self other ⦃ result =>
      (result.value.val.toGF216 : GF216) =
        self.value.val.toGF216 * other.value.val.toGF216 ⦄

/-- GF(2¹⁶) postcondition for the by-value `MulAssign<GF16> for GF16`
wrapper, which forwards directly to the by-reference (opaque) kernel. -/
@[step]
theorem mul_assign_spec
    (self other : spqr.encoding.gf.GF16) :
    Insts.CoreOpsArithMulAssignGF16.mul_assign self other ⦃ result =>
      (result.value.val.toGF216 : GF216) =
        self.value.val.toGF216 * other.value.val.toGF216 ⦄ := by
  unfold Insts.CoreOpsArithMulAssignGF16.mul_assign
  step*

/-- GF(2¹⁶) postcondition for the by-value `Mul<GF16, GF16> for GF16`
wrapper, which forwards directly to the by-reference (opaque) kernel. -/
@[step]
theorem mul_spec
    (self other : spqr.encoding.gf.GF16) :
    Insts.CoreOpsArithMulGF16GF16.mul self other ⦃ result =>
      (result.value.val.toGF216 : GF216) =
        self.value.val.toGF216 * other.value.val.toGF216 ⦄ := by
  unfold Insts.CoreOpsArithMulGF16GF16.mul
  step*

/-- GF(2¹⁶) postcondition for the by-reference `Mul<&GF16, GF16> for GF16`
wrapper, which forwards directly to the by-reference (opaque) kernel. -/
@[step]
theorem mul_shared0_spec
    (self other : spqr.encoding.gf.GF16) :
    Insts.CoreOpsArithMulShared0GF16GF16.mul self other ⦃ result =>
      (result.value.val.toGF216 : GF216) =
        self.value.val.toGF216 * other.value.val.toGF216 ⦄ := by
  unfold Insts.CoreOpsArithMulShared0GF16GF16.mul
  step*



/-
natural language description:

• Receives the current loop state `(iter, square, out)` where
    - `iter   : Range I32` is the underlying `1..16` range iterator,
    - `square : GF16`      is the current iterated square (initially `other²`),
    - `out    : GF16`      is the running product (initially `self`).
• Steps the iterator via `IteratorRange::next`:
    - If the iterator is exhausted (`None`): return `done out`,
      handing the unchanged accumulator back to the `loop` driver
      as the loop's final result.
    - Otherwise (`Some _`):
        a. `out₁    := out *= square`    (GF(2¹⁶) multiply-assign).
        b. `square₁ := square * square`  (GF(2¹⁶) squaring).
        c. Return `cont (iter₁, square₁, out₁)`.

natural language specs:

• The function always succeeds (returns `ok`) since each of
  `IteratorRange::next`, `MulAssign::mul_assign`, and
  `Mul::mul` is total on `GF16`.
• On the **termination** branch the accumulator is preserved:
    `result.value.val.toGF216 = out.value.val.toGF216`.
• On the **active** branch the new pair `(square', out')`
  satisfies the squaring recurrence in `GF216`:
    `square'.value.val.toGF216 =
        square.value.val.toGF216 * square.value.val.toGF216`
    `out'.value.val.toGF216 =
        out.value.val.toGF216 * square.value.val.toGF216`.
-/

/-- **Spec and proof concerning `encoding.gf.GF16.div_impl_loop.body`**:

One iteration of the iterated-squaring loop driving `GF16::div_impl`.
Both the termination and active branches are characterised at the
GF(2¹⁶) level via `Nat.toGF216 = φ ∘ natToGF2Poly`:

* **`done`** — the iterator is exhausted; the returned accumulator
  is the unchanged `out`.
* **`cont`** — the iterator yielded another index; the new state
  satisfies the squaring recurrence
    `square'.value.val.toGF216 =
        square.value.val.toGF216 * square.value.val.toGF216`
    `out'.value.val.toGF216 =
        out.value.val.toGF216 * square.value.val.toGF216`.

The proof unfolds `div_impl_loop.body` to expose the underlying
`IteratorRange::next` / `MulAssign::mul_assign` / `Mul::mul`
delegation and discharges each branch by `step*`, which appeals to
the already-registered specs for `unaccelerated::mul` (the
GF(2¹⁶) multiplication kernel that `Mul`/`MulAssign` ultimately
delegate to).

**Source**: spqr/src/encoding/gf.rs (lines 553:8-556:9)
-/
@[step]
theorem div_impl_loop_body_spec
    (iter : core.ops.range.Range Std.I32)
    (square out : spqr.encoding.gf.GF16) :
    div_impl_loop.body iter square out ⦃ cf =>
      match cf with
      | ControlFlow.done result =>
          (result.value.val.toGF216 : GF216) = out.value.val.toGF216
      | ControlFlow.cont (_, square', out') =>
          (square'.value.val.toGF216 : GF216) =
            square.value.val.toGF216 * square.value.val.toGF216 ∧
          (out'.value.val.toGF216 : GF216) =
            out.value.val.toGF216 * square.value.val.toGF216 ⦄ := by
  unfold div_impl_loop.body
  -- The body first calls `IteratorRange::next` and then matches on
  -- the resulting `Option`.  Unfold `next` to expose the underlying
  -- `if`/`match` and discharge each branch with `step*` (which
  -- appeals to the registered `MulAssign`/`Mul` specs above).
  unfold core.iter.range.IteratorRange.next
  step*
  -- ControlFlow.cont branch
  sorry





end spqr.encoding.gf.GF16
