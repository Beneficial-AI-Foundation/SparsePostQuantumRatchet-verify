/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Basic
import Mathlib.RingTheory.Polynomial.Basic

/-! # Spec Theorem for `reduce::reduce_from_byte` — loop body

Specification and proof for
`encoding.gf.reduce.reduce_from_byte_loop.body`, which executes
a single iteration of the `while i > 0 { … }` loop inside
`reduce_from_byte`.  The full loop is specified in
`ReduceFromByte.lean`; this file isolates the per-step behaviour
so that `reduce_from_byte_loop_spec` can appeal to a clean step
lemma via `loop.spec_decr_nat`.

One call to the body with state `(a, out, i)` (where `i.val ≤ 8`)
performs the following computation:

  1. **Termination guard** — if `i = 0`, the loop is exhausted:
       return `done out` (the accumulated 32-bit XOR mask).
  2. **Active step** — if `i > 0`, let `i' = i − 1` (the *next*
     bit position to process, zero-indexed):
       a. Compute the bit-test mask `(1 : u8) << i'` and AND it with
          `a`.  This tests whether bit `i'` of `a` is set.
       b. **Bit set** (`(1 << i') & a ≠ 0`):
            - `poly_shifted = POLY << i'`  (`POLY = 0x1100b`).
            - `out' = out ⊕ poly_shifted`  (accumulate reduction).
            - `carry = ((poly_shifted >> 16) as u8)` (8-bit carry).
            - `a'  = a ⊕ carry`             (feed carry back into `a`).
            - Return `cont (a', out', i')`.
       c. **Bit not set** (`(1 << i') & a = 0`):
            - Return `cont (a, out, i')` (state unchanged, counter decremented).

The central invariant maintained by every step:
```
  reduceFromByteLoopSpec a'.val out'.val i'.val
    = reduceFromByteLoopSpec a.val out.val i.val
```
This is the one-step unfolding of `reduceFromByteLoopSpec`
(defined in `ReduceFromByte.lean`), which mirrors the Rust loop
structure exactly.  In particular:

- **Bit set**: `reduceFromByteLoopSpec a out (n + 1)` unfolds to
  `reduceFromByteLoopSpec ((a ⊕ ((POLY << n) >> 16)) % 256)
                           (out ⊕ (POLY << n)) n`
  matching the updated `(a', out', i')` state above.
- **Bit not set**: `reduceFromByteLoopSpec a out (n + 1)` unfolds to
  `reduceFromByteLoopSpec a out n`, matching `(a, out, i')`.

**Source**: spqr/src/encoding/gf.rs (lines 505:8–513:9)
-/

open Aeneas Aeneas.Std Result
open Polynomial spqr.encoding.gf.unaccelerated

namespace spqr.encoding.gf.reduce


/-- Spec-level high-to-low loop for `reduce_from_byte`.

Starting from byte `a`, accumulator `out`, and decrement counter `i`,
processes bit positions `i-1, i-2, …, 0` in that order (high to low),
directly mirroring the Rust `while i > 0 { i -= 1; … }` structure.

For each bit position `n` (from `i-1` down to `0`):
  - If bit `n` of the current `a` is set:
      • XOR `POLY << n` (= `0x1100b <<< n`) into `out`.
      • XOR `((POLY << n) >> 16)` — truncated to 8 bits via `% 256`
        to match the `as u8` cast in Rust — back into `a`.
  - Otherwise: leave `(a, out)` unchanged and continue.

The return value is the final `out` accumulator after all `i` steps.

Starting with `(a₀, 0, 8)` gives the full 32-bit return value of
`reduce_from_byte(a₀)`:
  `reduce_from_byte_loop a₀ 0#u32 8#u32 = ok (reduceFromByteLoopSpec a₀.val 0 8)` -/
def reduceFromByteLoopSpec (a out : Nat) : (i : Nat) → Nat
  | 0     => out
  | i + 1 =>
    if a.testBit i then
      let poly_shifted := 0x1100b <<< i
      reduceFromByteLoopSpec ((a ^^^ (poly_shifted >>> 16)) % 256) (out ^^^ poly_shifted) i
    else
      reduceFromByteLoopSpec a out i


/-- One-step unfolding of `reduceFromByteLoopSpec` for the successor case.

`reduceFromByteLoopSpec a out (n + 1)` unfolds to a conditional on
`a.testBit n`, which is exactly the body computation:
  - **Bit set**: recurse with updated `a` and `out`.
  - **Bit not set**: recurse with unchanged `a` and `out`. -/
theorem reduce_from_byte_loop_body_spec1
    (a out n : Nat) :
    reduceFromByteLoopSpec a out (n + 1) =
    if a.testBit n then
      let poly_shifted := 0x1100b <<< n
      reduceFromByteLoopSpec ((a ^^^ (poly_shifted >>> 16)) % 256) (out ^^^ poly_shifted) n
    else
      reduceFromByteLoopSpec a out n := by
  rfl

/-- Variant of `reduce_from_byte_loop_body_spec1` lifted to `Std.U8`/`Std.U32`
    parameters, for use in the loop body spec. -/
theorem reduce_from_byte_loop_body_spec1'
    (a : Std.U8) (out : Std.U32) (i : Std.U32)
    (hi : i.val ≤ 8) (hi_lt : i.val > 0) :
    reduceFromByteLoopSpec a.val out.val i.val =
    (if a.val.testBit (i.val - 1) then
      let poly_shifted := 0x1100b <<< (i.val - 1)
      reduceFromByteLoopSpec ((a.val ^^^ (poly_shifted >>> 16)) % 256)
        (out.val ^^^ poly_shifted) (i.val - 1)
    else
      reduceFromByteLoopSpec a.val out.val (i.val - 1)) := by
  have h := reduce_from_byte_loop_body_spec1 a.val out.val (i.val - 1)
  rw [show (i.val - 1) + 1 = i.val from by omega] at h
  exact h

/-- Connection between the U8 shift-and-AND bit test and `Nat.testBit`:
    `(1 <<< n) % 256 &&& a = 0` iff bit `n` of `a` is not set.
    Uses `Nat.two_pow_and` from Mathlib. -/
private lemma and_shiftLeft_one_eq_zero_iff_testBit_false
    (a n : Nat) (hn : n ≤ 7) :
    (1 <<< n % 256 &&& a = 0) ↔ (a.testBit n = false) := by
  have hmod : 1 <<< n % 256 = 1 <<< n := by
    apply Nat.mod_eq_of_lt; interval_cases n <;> norm_num [Nat.one_shiftLeft]
  rw [hmod, Nat.one_shiftLeft, Nat.two_pow_and]
  simp only [mul_eq_zero]
  constructor
  · intro h
    rcases h with hp | ht
    · exact absurd hp (by positivity)
    · cases hb : a.testBit n <;> simp_all
  · intro h
    right
    simp [h]



/-- XOR of two numbers below `2^n` stays below `2^n`. -/
private lemma nat_xor_lt {a b n : Nat} (ha : a < 2 ^ n) (hb : b < 2 ^ n) :
    a ^^^ b < 2 ^ n := by
  apply Nat.lt_of_testBit n
  · simp [Nat.testBit_xor, Nat.testBit_eq_false_of_lt ha, Nat.testBit_eq_false_of_lt hb]
  · rw [← Nat.one_shiftLeft, Nat.testBit_shiftLeft]
    simp
  · intro j hj
    have haj := Nat.testBit_eq_false_of_lt (lt_trans ha (Nat.pow_lt_pow_right (by norm_num) hj))
    have hbj := Nat.testBit_eq_false_of_lt (lt_trans hb (Nat.pow_lt_pow_right (by norm_num) hj))
    have h1lt : 1 < 2 ^ (j - n) := Nat.one_lt_pow (by omega) (by norm_num)
    simp [Nat.testBit_xor, haj, hbj, ← Nat.one_shiftLeft, Nat.testBit_shiftLeft,
          Nat.testBit_eq_false_of_lt h1lt, show n ≤ j from by omega]

/-
natural language description:

• Receives the current loop state:
    - `a   : u8`  — the byte being reduced, with carry feedback.
    - `out : u32` — the 32-bit XOR accumulator for the result.
    - `i   : u32` — the decrement counter (starts at 8, counts down to 0).
• If `i = 0`: the loop is exhausted; return `done out`.
• If `i > 0`:
    - Decrement: `i1 = i − 1`.
    - Compute bitmask: `i2 = (1 : u8) << i1`.
    - Test bit: `i3 = i2 & a`.
    - If `i3 ≠ 0` (bit `i1` of `a` is set):
        • Shift the irreducible polynomial: `i4 = POLY << i1`.
        • Accumulate into output:  `out1 = out ^ i4`.
        • Extract carry (high bits): `i5 = i4 >> 16`.
        • Truncate carry to 8 bits: `i6 = (u8) i5`.
        • Feed carry back into `a`:  `a1 = a ^ i6`.
        • Return `cont (a1, out1, i1)`.
    - If `i3 = 0` (bit `i1` of `a` is not set):
        • Return `cont (a, out, i1)`.

natural language specs:

• The function always succeeds (returns `ok`) for all inputs with
  `i.val ≤ 8`, since:
    - `(1 : u8) <<< i1` is valid for `i1 ≤ 7` (left shift of a u8 by
      at most 7 bits never overflows).
    - `POLY <<< i1` for `i1 ≤ 7` is at most `0x880580 < 2^24 < 2^32`,
      so the u32 shift never overflows.
    - `(u8)(i4 >>> 16)` for `i4 ≤ 0x880580` has the value
      `(0x1100b <<< i1) >>> 16 ≤ 0x88 < 256`, so the `UScalar.cast .U8`
      always succeeds.
    - `a ^^^ i6` stays within u8 arithmetic.
• The step is terminating: when `i.val > 0`, the returned `i'.val`
  satisfies `i'.val = i.val - 1 < i.val`, strictly decreasing the
  measure.  When `i.val = 0`, the loop returns `done`, ending iteration.
• **Loop invariant** — for every call with `i.val ≤ 8`:
    `reduceFromByteLoopSpec (result_a).val (result_out).val (result_i).val
       = reduceFromByteLoopSpec a.val out.val i.val`
  where `(result_a, result_out, result_i)` is the `cont` payload (when
  the result is `cont`), and `result_out = out` (when the result is
  `done`).  In detail:
    - `done out`: `i.val = 0`, and by definition
      `reduceFromByteLoopSpec a.val out.val 0 = out.val`.
    - `cont` with bit set: the spec unfolds as
      `reduceFromByteLoopSpec a out (i1+1)
         = reduceFromByteLoopSpec (a ^^^ ((POLY<<i1)>>>16) % 256)
                                   (out ^^^ (POLY<<i1)) i1`,
      which matches `(a1.val, out1.val, i1.val)` precisely.
    - `cont` with bit not set: the spec unfolds as
      `reduceFromByteLoopSpec a out (i1+1) = reduceFromByteLoopSpec a out i1`,
      which matches `(a.val, out.val, i1.val)`.
-/

/- **Step lemma for `encoding.gf.reduce.reduce_from_byte_loop.body`**:

One iteration of the `reduce_from_byte` loop, processing bit position
`i − 1` of byte `a` and updating the XOR accumulator `out`.

Given state `(a, out, i)` with `i.val ≤ 8`, the body always succeeds
(`ok`) and either:

1. **Terminates** (`i.val = 0`): returns `done out`, with
     `out.val = reduceFromByteLoopSpec a.val out.val 0`.

2. **Continues** (`i.val > 0`): returns `cont (a', out', i')` with:
     - `i'.val = i.val - 1`  (strictly decreasing measure),
     - `i'.val ≤ 8`           (invariant bound preserved),
     - the loop invariant maintained:
         `reduceFromByteLoopSpec a'.val out'.val i'.val
            = reduceFromByteLoopSpec a.val out.val i.val`.

This step lemma is the core inductive step that `reduce_from_byte_loop_spec`
(in `ReduceFromByte.lean`) relies on via `loop.spec_decr_nat` to prove that
the full loop returns `reduceFromByteLoopSpec a.val out.val i.val`.

**Source**: spqr/src/encoding/gf.rs (lines 505:8–513:9)
-/

set_option maxHeartbeats 10000000 in

@[step]
theorem reduce_from_byte_loop_body_spec
    (a : Std.U8) (out : Std.U32) (i : Std.U32)
    (hi : i.val ≤ 8) :
    reduce_from_byte_loop.body a out i ⦃ cf =>
      match cf with
      | ControlFlow.done result =>
          i.val = 0 ∧ result.val = out.val
      | ControlFlow.cont (a', out', i') =>
          i.val > 0 ∧
          i'.val = i.val - 1 ∧
          reduceFromByteLoopSpec a'.val out'.val i'.val =
            reduceFromByteLoopSpec a.val out.val i.val ⦄ := by
  unfold reduce_from_byte_loop.body
  simp only [encoding.gf.POLY]
  by_cases hgt : i > 0#u32
  · simp only [hgt, ↓reduceIte]
    step*
    · -- Bit set branch
      constructor
      · scalar_tac
      · constructor
        · scalar_tac
        · simp_all
          have : (i.val - 1) + 1 = i.val := by omega
          conv_rhs =>
            rw [← this, reduce_from_byte_loop_body_spec1]
          -- The bit IS set: the context contains ¬(mask &&& a.val = 0)
          have h_bound : i.val - 1 ≤ 7 := by omega
          have h_tb : (a.val).testBit (i.val - 1) = true := by
            by_contra h_neg
            have hf : (a.val).testBit (i.val - 1) = false := by
              revert h_neg; cases (a.val).testBit (i.val - 1) <;> simp
            have := (and_shiftLeft_one_eq_zero_iff_testBit_false a.val (i.val - 1) h_bound).mpr hf
            simp[Nat.shiftLeft_eq] at this
            rw [← Nat.one_shiftLeft, show (256 : Nat) = U8.size from by simp [U8.size, U8.numBits]] at this
            exact absurd this ‹_›
          simp only [h_tb, ↓reduceIte]
          -- Simplify % U32.size (69643 <<< n < 2^32 for n ≤ 7)
          have h_poly_lt : 69643 <<< (i.val - 1) < U32.size := by
            interval_cases i.val <;> simp_all [U32.size, U32.numBits]
          have h_mod_u32 : 69643 <<< (i.val - 1) % U32.size = 69643 <<< (i.val - 1) :=
            Nat.mod_eq_of_lt h_poly_lt
          rw [h_mod_u32]
          -- Simplify UScalar.cast value
          have h_shr_lt : 69643 <<< (i.val - 1) >>> 16 < 256 := by
            interval_cases i.val <;> simp_all
          have h_cast : (UScalar.cast UScalarTy.U8 i5).val =
              69643 <<< (i.val - 1) >>> 16 := by
            rw [UScalar.cast_val_eq, i5_post1, h_mod_u32]
            exact Nat.mod_eq_of_lt (by simp [UScalarTy.numBits]; exact h_shr_lt)
          rw [h_cast]
          -- Show % 256 = identity (XOR of two values < 256 is < 256)
          congr 1
          symm
          apply Nat.mod_eq_of_lt
          rw [(by norm_num : 256 = 2 ^ 8)]
          apply nat_xor_lt
          · grind
          · grind
    · -- Bit not set branch
      constructor
      · scalar_tac
      · simp_all
        have : (i.val - 1) + 1 = i.val := by omega
        conv_rhs =>
            rw [← this, reduce_from_byte_loop_body_spec1]
        have h_bound : i.val - 1 ≤ 7 := by omega
        have h_mask_zero : 1 <<< (i.val - 1) % U8.size &&& a.val = 0 := by assumption
        have h_tb : (a.val).testBit (i.val - 1) = false := by
          rw [show (U8.size : Nat) = 256 from by simp [U8.size, U8.numBits]] at h_mask_zero
          exact (and_shiftLeft_one_eq_zero_iff_testBit_false a.val (i.val - 1) h_bound).mp h_mask_zero
        simp [h_tb, ↓reduceIte]

  · simp only [show ¬(i > 0#u32) from hgt, ↓reduceIte]
    constructor
    · scalar_tac
    · rfl

/-- Spec-level byte-wise reduction corresponding to `reduce_from_byte`.

Given a byte value `a` (0 ≤ a < 256), computes the 32-bit XOR mask
that results from reducing all set bits in `a` against POLY.  This
corresponds to reducing the polynomial `a · x¹⁶` modulo POLY:
for each set bit `i` in `a` (from bit 7 down to bit 0), XOR
`POLY <<< i` into the accumulator and update `a` by clearing the
contribution of the high bits.

This matches the Rust `reduce_from_byte` function. -/
def reduceFromByte (a : Nat) : (n : Nat) → Nat × Nat
  | 0     => (a, 0)
  | n + 1 =>
    let (a', out) := reduceFromByte a n
    if a'.testBit n then
      let poly_shifted := 0x1100b <<< n
      (a' ^^^ (poly_shifted >>> 16), out ^^^ poly_shifted)
    else (a', out)

end spqr.encoding.gf.reduce
