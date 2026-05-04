/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf
import Spqr.Specs.Encoding.Gf.Unaccelerated.PolyMul

/-! # Spec Theorem for `spqr::encoding::gf::reduce::reduce_from_byte` — loop body

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
This is the one-step unfolding of `reduceFromByteLoopSpec`,
which mirrors the Rust loop structure exactly.

The shared polynomial-library facts (`natToGF2Poly`, `POLY_GF2`,
`POLY_GF2_monic`, `natToGF2Poly_xor`, `natToGF2Poly_shiftLeft`,
`natToGF2Poly_POLY`, etc.) are imported from `Spqr.Math.Gf`.

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
-/

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
        · simp_all only [gt_iff_lt, UScalar.lt_equiv, UScalar.ofNatCore_val_eq,
          UScalarTy.U8_numBits_eq, Bvify.U8.UScalar_bv, U8.ofNat_bv, UScalar.val_and,
          bne_iff_ne, ne_eq, UScalar.neq_to_neq_val, UScalarTy.U32_numBits_eq,
          Bvify.U32.UScalar_bv, U32.ofNat_bv, UScalar.val_xor, UScalar.cast_bv_eq]
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
            simp only [Nat.shiftLeft_eq, one_mul] at this
            rw [← Nat.one_shiftLeft,
            show (256 : Nat) = U8.size from by simp [U8.size, U8.numBits]] at this
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
            exact Nat.mod_eq_of_lt (by
              simp only [UScalarTy.numBits, Nat.reducePow];
              exact h_shr_lt)
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
      · simp_all only [gt_iff_lt, UScalar.lt_equiv, UScalar.ofNatCore_val_eq,
        UScalarTy.U8_numBits_eq, Bvify.U8.UScalar_bv, U8.ofNat_bv, UScalar.val_and,
        bne_iff_ne, ne_eq, UScalar.neq_to_neq_val, Decidable.not_not, true_and]
        have : (i.val - 1) + 1 = i.val := by omega
        conv_rhs =>
            rw [← this, reduce_from_byte_loop_body_spec1]
        have h_bound : i.val - 1 ≤ 7 := by omega
        have h_mask_zero : 1 <<< (i.val - 1) % U8.size &&& a.val = 0 := by assumption
        have h_tb : (a.val).testBit (i.val - 1) = false := by
          rw [show (U8.size : Nat) = 256 from by simp [U8.size, U8.numBits]] at h_mask_zero
          exact (and_shiftLeft_one_eq_zero_iff_testBit_false a.val
          (i.val - 1) h_bound).mp h_mask_zero
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


/-! # Spec Theorem for `spqr::encoding::gf::reduce::reduce_from_byte`

Specification and proof for `encoding.gf.reduce.reduce_from_byte`,
which computes the 32-bit XOR mask associated with a byte value `a`
(interpreted as a degree-< 8 polynomial over GF(2)) against the
irreducible polynomial POLY = x¹⁶ + x¹² + x³ + x + 1 (0x1100b = 69643).

The function iterates over the 8 bits of `a` from bit 7 down to bit 0
(high to low).  For each set bit `i`, it:
  1. XORs `POLY << i` into the 32-bit output accumulator `out`.
  2. Updates `a` by XOR-ing `((POLY << i) >> 16) as u8` into it,
     feeding the high-bit carry back into the lower bits of `a`.

The low 16 bits of the returned `u32` represent the canonical GF(2¹⁶)
element obtained by reducing `a · x¹⁶` modulo POLY:

  `(reduce_from_byte(a) as u16)  =  (a · X¹⁶) mod POLY_GF2`

This value is subsequently stored as `REDUCE_BYTES[a]` in the
precomputed lookup table used by `poly_reduce`.

**Source**: spqr/src/encoding/gf.rs (lines 502:4-515:5)
-/



/-- Spec-level table entry: the 16-bit reduction mask for byte `k`.

Given a byte value `k` (0 ≤ k < 256), `reduceByteTable k` is the
16-bit XOR mask obtained by the high-to-low loop spec
`reduceFromByteLoopSpec` (which matches the Rust `while i > 0`
loop order) retaining the low 16 bits of the 32-bit accumulator.

  `reduceByteTable k = reduceFromByteLoopSpec k 0 8 % 2 ^ 16`
-/
def reduceByteTable (k : Nat) : Nat :=
  reduceFromByteLoopSpec k 0 8 % 2 ^ 16

/-!
## Algebraic (GF(2)[X]) formulation of the reduction table

The following definition expresses `reduceByteTable` in terms of the
polynomial ring GF(2)[X] = (ZMod 2)[X], making the algebraic structure
explicit:
- Each byte `k` represents a polynomial of degree < 8 in GF(2)[X].
- `REDUCE_BYTES[k]` represents the remainder of `k · X¹⁶` divided by
  POLY_GF2 = X¹⁶ + X¹² + X³ + X + 1.
- The table entry is the canonical 16-bit representative of this
  remainder, which has degree < 16 since POLY_GF2 is monic of degree 16.
-/


/-- Spec-level polynomial table entry in (ZMod 2)[X].

Given a polynomial `p ∈ GF(2)[X]` (representing a byte value of
degree < 8), `reduceByteTable_poly p` is the canonical remainder of
`p * X¹⁶` modulo POLY_GF2:

  `reduceByteTable_poly p = (p * X ^ 16) %ₘ POLY_GF2` -/
noncomputable def reduceByteTable_poly (p : (ZMod 2)[X]) : (ZMod 2)[X] :=
  (p * X ^ 16) %ₘ POLY_GF2

/-- The carry register vanishes after 8 reduction steps of `reduceFromByte`
for any `k < 16`. -/
lemma reduceFromByte_carry_eq_zero (k : Nat) (hk : k < 16) :
    (reduceFromByte k 8).1 = 0 := by
  interval_cases k <;> decide

/-- For k < 16, the high-to-low loop (`reduceFromByteLoopSpec`)
and the low-to-high spec (`reduceFromByte`) agree on the low
16 bits. -/
private lemma loopSpec_eq_reduceFromByte_small :
    ∀ k : Fin 16,
      reduceFromByteLoopSpec k.val 0 8 % 2 ^ 16 =
        (reduceFromByte k.val 8).2 % 2 ^ 16 := by
  decide

/-- **Correspondence between `reduceByteTable` on `Nat` and
`reduceByteTable_poly` on GF(2)[X]** (for byte values `< 16`). -/
theorem reduceByteTable_eq_reduceByteTable_poly (k : Nat) (hk : k < 16) :
    natToGF2Poly (reduceByteTable k) = reduceByteTable_poly (natToGF2Poly k) := by
  -- Re-use shared facts from `Spqr.Math.Gf` (POLY_GF2_monic, natToGF2Poly_*).
  have hmonic : POLY_GF2.Monic := POLY_GF2_monic
  -- Helper: for any n, natToGF2Poly (0x1100b <<< n) = POLY_GF2 * X^n
  have hpoly_shift : ∀ n : Nat,
      natToGF2Poly (0x1100b <<< n) = POLY_GF2 * X ^ n := by
    intro n; rw [natToGF2Poly_shiftLeft, natToGF2Poly_POLY]
  -- Helper: XOR distributes over mod 2^16
  have xor_mod : ∀ a b : Nat,
      (a ^^^ b) % 2 ^ 16 = a % 2 ^ 16 ^^^ b % 2 ^ 16 := by
    intro a b
    apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_xor, Nat.testBit_mod_two_pow]
    by_cases hi : i < 16 <;> simp [hi]
  -- Main inductive invariant on `reduceFromByte` (low-to-high spec):
  --   (low16(reduceFromByte k n).2 + carry(reduceFromByte k n) * X^16) %ₘ POLY_GF2
  --   = (k * X^16) %ₘ POLY_GF2
  have inv : ∀ (n : Nat),
      (natToGF2Poly ((reduceFromByte k n).2 % 2 ^ 16) +
       natToGF2Poly ((reduceFromByte k n).1) * X ^ 16) %ₘ POLY_GF2 =
      (natToGF2Poly k * X ^ 16) %ₘ POLY_GF2 := by
    intro n
    induction n with
    | zero => simp only [reduceFromByte, Nat.zero_mod, natToGF2Poly_zero, zero_add]
    | succ n ih =>
      simp only [reduceFromByte]
      by_cases htb : (reduceFromByte k n).1.testBit n
      · simp only [htb, ↓reduceIte]
        set a'  := (reduceFromByte k n).1
        set out := (reduceFromByte k n).2
        set ps  := 0x1100b <<< n
        have hrw : natToGF2Poly ((out ^^^ ps) % 2 ^ 16) +
            natToGF2Poly (a' ^^^ (ps >>> 16)) * X ^ 16 =
            (natToGF2Poly (out % 2 ^ 16) + natToGF2Poly a' * X ^ 16) +
            POLY_GF2 * X ^ n := by
          rw [xor_mod, natToGF2Poly_xor, natToGF2Poly_xor,
              ← hpoly_shift n, natToGF2Poly_split ps 16]
          ring
        rw [hrw]
        have hdvd : POLY_GF2 ∣ POLY_GF2 * X ^ n := dvd_mul_right POLY_GF2 _
        have hzero : (POLY_GF2 * X ^ n) %ₘ POLY_GF2 = 0 :=
          (Polynomial.modByMonic_eq_zero_iff_dvd hmonic).mpr hdvd
        have hstep : ((natToGF2Poly (out % 2 ^ 16) + natToGF2Poly a' * X ^ 16) +
            POLY_GF2 * X ^ n) %ₘ POLY_GF2 =
            (natToGF2Poly (out % 2 ^ 16) + natToGF2Poly a' * X ^ 16) %ₘ POLY_GF2 := by
          rw [Polynomial.add_modByMonic, hzero, add_zero]
        rw [hstep, ih]
      · simp only [htb, Bool.false_eq_true, ↓reduceIte]; exact ih
  -- Apply invariant at n = 8.
  have h8 := inv 8
  simp only [reduceByteTable, reduceByteTable_poly]
  rw [loopSpec_eq_reduceFromByte_small ⟨k, hk⟩]
  -- The low-16-bit polynomial has degree < 16, so it equals itself %ₘ POLY_GF2.
  have hdeg : (natToGF2Poly ((reduceFromByte k 8).2 % 2 ^ 16)).natDegree < 16 := by
    rcases eq_or_ne (natToGF2Poly ((reduceFromByte k 8).2 % 2 ^ 16)) 0 with heq | hne
    · simp at heq; norm_num
      simp [heq]
    · rw [Polynomial.natDegree_lt_iff_degree_lt hne, Polynomial.degree_lt_iff_coeff_zero]
      intro m hm
      rw [natToGF2Poly_coeff]
      simp [Nat.testBit_eq_false_of_lt (calc
        (reduceFromByte k 8).2 % 2 ^ 16 < 2 ^ 16 := Nat.mod_lt _ (by norm_num)
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm)]
  have hPOLYdeg : POLY_GF2.natDegree = 16 := POLY_GF2_natDegree
  have hne1 : POLY_GF2 ≠ 1 := by
    intro heq
    have : (POLY_GF2 : (ZMod 2)[X]).coeff 16 = (1 : (ZMod 2)[X]).coeff 16 := by rw [heq]
    simp [POLY_GF2, coeff_add, coeff_X_pow, coeff_X, coeff_one] at this
  have hself : natToGF2Poly ((reduceFromByte k 8).2 % 2 ^ 16) %ₘ POLY_GF2 =
               natToGF2Poly ((reduceFromByte k 8).2 % 2 ^ 16) := by
    set A := natToGF2Poly ((reduceFromByte k 8).2 % 2 ^ 16)
    have hA := Polynomial.modByMonic_add_div A hmonic
    suffices hdivz : A /ₘ POLY_GF2 = 0 by
      rw [hdivz, mul_zero, add_zero] at hA
      exact hA
    by_contra hne
    have hprod_deg : (A /ₘ POLY_GF2 * POLY_GF2).natDegree ≥ 16 := by
      have hmul := Polynomial.natDegree_mul hne hmonic.ne_zero
      rw [hPOLYdeg] at hmul
      linarith [Nat.zero_le (A /ₘ POLY_GF2).natDegree]
    have hmod_lt : (A %ₘ POLY_GF2).natDegree < 16 := by
      rw [← hPOLYdeg]; exact Polynomial.natDegree_modByMonic_lt A hmonic hne1
    have hrearr : A = A %ₘ POLY_GF2 + A /ₘ POLY_GF2 * POLY_GF2 := by grind
    have hge : A.natDegree ≥ 16 := by
      rw [hrearr]
      apply le_trans hprod_deg
      apply Polynomial.le_natDegree_of_ne_zero
      intro hzero
      have hlt_deg : (A %ₘ POLY_GF2).natDegree < (A /ₘ POLY_GF2 * POLY_GF2).natDegree :=
        by linarith
      rw [Polynomial.coeff_add,
          Polynomial.coeff_eq_zero_of_natDegree_lt hlt_deg,
          zero_add] at hzero
      have hprod_ne : A /ₘ POLY_GF2 * POLY_GF2 ≠ 0 := by
        intro h; simp [h] at hprod_deg
      exact absurd hzero (by
        have hlc := Polynomial.leadingCoeff_ne_zero.mpr hprod_ne
        simp only [Polynomial.leadingCoeff] at hlc
        exact hlc)
    linarith [hdeg, hge]
  have hcarry : (natToGF2Poly ((reduceFromByte k 8).1) * X ^ 16) %ₘ POLY_GF2 = 0 := by
    have hzero := reduceFromByte_carry_eq_zero k hk
    simp only [hzero, natToGF2Poly_zero, zero_mul, Polynomial.zero_modByMonic]
  have hfinal : natToGF2Poly ((reduceFromByte k 8).2 % 2 ^ 16) %ₘ POLY_GF2 =
                natToGF2Poly k * X ^ 16 %ₘ POLY_GF2 := by
    have hstep : (natToGF2Poly ((reduceFromByte k 8).2 % 2 ^ 16) +
        natToGF2Poly ((reduceFromByte k 8).1) * X ^ 16) %ₘ POLY_GF2 =
        natToGF2Poly ((reduceFromByte k 8).2 % 2 ^ 16) %ₘ POLY_GF2 := by
      rw [Polynomial.add_modByMonic, hcarry, add_zero]
    rw [← hstep]; exact h8
  rw [← hself]; exact hfinal


/-- **`reduceByteTable_poly` is the modular reduction of `p * X¹⁶`**:

For any polynomial `p ∈ GF(2)[X]` with `natDegree p < 8`,
`reduceByteTable_poly p` equals the remainder of `p * X¹⁶` modulo
POLY_GF2, and has degree strictly less than 16. -/
theorem reduceByteTable_poly_degree_lt (p : (ZMod 2)[X])
    (hirr : POLY_GF2.Monic) :
    (reduceByteTable_poly p).natDegree < POLY_GF2.natDegree := by
  unfold reduceByteTable_poly
  apply Polynomial.natDegree_modByMonic_lt _ hirr
  intro heq
  have hcoeff : POLY_GF2.coeff 16 = 1 := by
    simp only [POLY_GF2,
      Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X,
      Polynomial.coeff_one]
    norm_num
  rw [heq, Polynomial.coeff_one] at hcoeff
  norm_num at hcoeff

/-!
## Algebraic (GF(2)[X]) formulation of `reduce_from_byte`
-/

/-- Spec-level polynomial result of `reduce_from_byte a` in (ZMod 2)[X]. -/
noncomputable def reduceFromByteSpec_poly (p : (ZMod 2)[X]) : (ZMod 2)[X] :=
  (p * X ^ 16) %ₘ POLY_GF2

/-- **`reduceFromByteSpec_poly` equals `reduceByteTable_poly`**. -/
theorem reduceFromByteSpec_poly_eq_reduceByteTable_poly (p : (ZMod 2)[X]) :
    reduceFromByteSpec_poly p = reduceByteTable_poly p := by
  simp [reduceFromByteSpec_poly, reduceByteTable_poly]

/-- The degree of `reduceFromByteSpec_poly p` is strictly less than 16. -/
theorem reduceFromByteSpec_poly_degree_lt (p : (ZMod 2)[X])
    (hirr : POLY_GF2.Monic) :
    (reduceFromByteSpec_poly p).natDegree < POLY_GF2.natDegree := by
  rw [reduceFromByteSpec_poly_eq_reduceByteTable_poly]
  exact reduceByteTable_poly_degree_lt p hirr

/-- High-to-low loop agrees with `reduceByteTable` at the 16-bit level. -/
theorem reduceFromByteLoopSpec_eq_reduceByteTable
    (k : Nat) (_hk : k < 256) :
    reduceFromByteLoopSpec k 0 8 % 2 ^ 16 =
      reduceByteTable k := rfl


/-
natural language description:

• Takes a mutable `u8` value `a`, initialises `out : u32 = 0`, `i : u32 = 8`.
• Loops while `i > 0`:
    - Decrements `i` (so `i` takes values 7, 6, 5, 4, 3, 2, 1, 0 in that order).
    - Computes `(1_u8 << i) & a` to test bit `i` of `a`.
    - If the bit is set:
        • `out ^= POLY << i`              (accumulate reduction contribution).
        • `a   ^= ((POLY << i) >> 16) as u8` (8-bit carry feedback into `a`).
• Returns `out : u32`.
• The constant `REDUCE_BYTES[k]` is defined as `reduce_from_byte(k as u8) as u16`.

natural language specs:

• The function always succeeds (no panic) for any `u8` input.
• The full 32-bit result satisfies:
    `(reduce_from_byte a).val  =  reduceFromByteLoopSpec a.val 0 8`
• The low 16 bits equal the precomputed table entry:
    `(reduce_from_byte a).val % 2^16  =  reduceByteTable a.val`
-/

@[step]
theorem reduce_from_byte_loop_spec
    (a : Std.U8) (out : Std.U32) (i : Std.U32)
    (hi : i.val ≤ 8) :
    reduce_from_byte_loop a out i ⦃ result =>
      result.val = reduceFromByteLoopSpec a.val out.val i.val ⦄ := by
  unfold reduce_from_byte_loop
  apply loop.spec_decr_nat
    (measure := fun (p : Std.U8 × Std.U32 × Std.U32) => p.2.2.val)
    (inv := fun (p : Std.U8 × Std.U32 × Std.U32) =>
      p.2.2.val ≤ 8 ∧
      reduceFromByteLoopSpec p.1.val p.2.1.val p.2.2.val =
        reduceFromByteLoopSpec a.val out.val i.val)
  · intro ⟨a', out', i'⟩ ⟨hi'_bound, hi'_spec⟩
    simp only []
    step*
    split
    · simp_all [reduceFromByteLoopSpec]
    · obtain ⟨h_gt, h_eq, h_spec⟩ := r_post
      simp_all
      grind
  · exact ⟨hi, rfl⟩

@[step]
theorem reduce_from_byte_spec (a : Std.U8) :
    reduce_from_byte a ⦃ result =>
      result.val % 2 ^ 16 = reduceByteTable a.val ⦄ := by
  unfold reduce_from_byte
  apply WP.spec_mono (reduce_from_byte_loop_spec a 0#u32 8#u32 (by scalar_tac))
  intro result hres
  simp only [hres]
  have ha : a.val < 256 := by scalar_tac
  rw [← reduceFromByteLoopSpec_eq_reduceByteTable a.val ha]
  simp [reduceFromByteLoopSpec]

/-- **GF(2)[X] formulation of `reduce_from_byte`**:

For a byte `a` with `a.val < 16`, the low 16 bits of `reduce_from_byte a`,
interpreted as a GF(2) polynomial via `natToGF2Poly`, equal the remainder
of `natToGF2Poly a.val * X¹⁶` modulo POLY_GF2. -/
theorem reduce_from_byte_poly_spec (a : Std.U8) (ha : a.val < 16) :
    reduce_from_byte a ⦃ result =>
      natToGF2Poly (result.val % 2 ^ 16) =
        (natToGF2Poly a.val * X ^ 16) %ₘ POLY_GF2 ⦄ := by
  apply WP.spec_mono (reduce_from_byte_spec a)
  intro result hres
  rw [hres, reduceByteTable_eq_reduceByteTable_poly a.val ha]
  simp [reduceByteTable_poly]

end spqr.encoding.gf.reduce
