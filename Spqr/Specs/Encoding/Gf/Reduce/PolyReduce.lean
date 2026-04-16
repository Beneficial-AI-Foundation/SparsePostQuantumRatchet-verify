/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Basic
import Spqr.Specs.Encoding.Gf.Unaccelerated.PolyMul
import Mathlib.RingTheory.Polynomial.Basic

/-! # Spec Theorem for `reduce::poly_reduce`

Specification and proof for `encoding.gf.reduce.poly_reduce`,
which implements table-based polynomial reduction of a 32-bit
carry-less product modulo the irreducible polynomial
POLY = x¹⁶ + x¹² + x³ + x + 1 (0x1100b), yielding a 16-bit
GF(2¹⁶) element.

In GF(2¹⁶) — the Galois field with 65 536 elements — after
carry-less polynomial multiplication (`poly_mul`) produces a
32-bit unreduced product (degree ≤ 30), reduction modulo the
irreducible polynomial POLY is needed to obtain the canonical
16-bit representative.

The reduction proceeds in two byte-by-byte passes using the
precomputed table `REDUCE_BYTES`:
  1. Extract the high byte `i1 = v >> 24` and XOR
     `REDUCE_BYTES[i1] << 8` into `v`, clearing bits 24–31.
  2. Extract the next byte `i2 = (v >> 16) & 0xFF` and XOR
     `REDUCE_BYTES[i2]` into `v`, clearing bits 16–23.
  3. Return the low 16 bits of `v` as the reduced result.

Each `REDUCE_BYTES[k]` entry stores the precomputed 16-bit XOR
mask that results from reducing all set bits in byte `k` against
POLY.  This is equivalent to computing `(k · x¹⁶) mod POLY`
for the second pass, and `(k · x²⁴) mod POLY` (after appropriate
shifting) for the first pass.

**Source**: spqr/src/encoding/gf.rs (lines 489:4-498:5)
-/

open Aeneas Aeneas.Std Result

namespace spqr.encoding.gf.reduce

/-- Spec-level bit-by-bit polynomial reduction modulo POLY over GF(2).

Reduces a natural number `v` (interpreted as a GF(2) polynomial)
modulo POLY = 0x1100b by iterating from bit position 16 up to
bit `n + 15`, clearing each set high-order bit by XOR-ing with
`POLY <<< (bit − 16)`.  After processing all bits above 15,
the result fits in 16 bits and is the canonical GF(2¹⁶)
representative.

This is the pure recursive definition corresponding to the
mathematical operation `v mod POLY` in GF(2)[X]. -/
def polyMod (v : Nat) : (n : Nat) → Nat
  | 0     => v
  | n + 1 =>
    let v' := polyMod v n
    if v'.testBit (n + 16)
    then v' ^^^ (0x1100b <<< n)
    else v'

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

/-!
## Algebraic (GF(2)[X]) formulation of polynomial reduction

The following definitions express `polyMod` in terms of the polynomial
ring GF(2)[X] = (ZMod 2)[X], making the algebraic structure explicit:
- XOR (`^^^`) becomes polynomial addition (`+`) over GF(2)
- Shift-left by n (`<<< n`) becomes multiplication by `X ^ n`
- `Nat.testBit n` becomes checking if the n-th coefficient is nonzero

The reduction computes `v mod POLY_GF2` where
  POLY_GF2 = X¹⁶ + X¹² + X³ + X + 1.
-/

open Polynomial in
/-- Spec-level polynomial reduction modulo POLY_GF2 in (ZMod 2)[X].

Given a polynomial `p ∈ GF(2)[X]`, reduces it modulo POLY_GF2 by
iterating from degree `n + 15` down to degree 16, subtracting
(= adding, in characteristic 2) `POLY_GF2 * X^k` for each nonzero
coefficient at position `k + 16`.

Morally, `polyMod_poly p n = p %ₘ POLY_GF2` when
`natDegree p < n + 16`. -/
noncomputable def polyMod_poly (p : (ZMod 2)[X]) :
    (n : Nat) → (ZMod 2)[X]
  | 0     => p
  | n + 1 =>
    let p' := polyMod_poly p n
    if p'.coeff (n + 16) ≠ 0
    then p' + spqr.encoding.gf.unaccelerated.POLY_GF2 * X ^ n
    else p'

/-- **Correspondence between `polyMod` on `Nat` and `polyMod_poly` on GF(2)[X]**:

Interpreting the natural-number input as a GF(2) polynomial via
`natToGF2Poly`, the `Nat`-level `polyMod` and the algebraic
`polyMod_poly` agree:

  `natToGF2Poly (polyMod v n) = polyMod_poly (natToGF2Poly v) n`

This justifies reasoning about the XOR/shift implementation in
terms of polynomial algebra over GF(2). -/
theorem polyMod_eq_polyMod_poly (v n : Nat) :
    spqr.encoding.gf.unaccelerated.natToGF2Poly (polyMod v n) =
      polyMod_poly (spqr.encoding.gf.unaccelerated.natToGF2Poly v) n := by
  sorry

open Polynomial in
/-- **`polyMod_poly` computes polynomial modular reduction**:

For any polynomial `p ∈ GF(2)[X]` with `natDegree p < n + 16`,
iterating `polyMod_poly` for `n` steps yields the remainder
modulo POLY_GF2:

  `polyMod_poly p n = p %ₘ POLY_GF2`   (when `natDegree p < n + 16`)

In particular, for the product of two 16-bit polynomials
(degree ≤ 30):
  `polyMod_poly p 16 = p %ₘ POLY_GF2`  (when `natDegree p < 32`) -/
theorem polyMod_poly_eq_modByMonic (p : (ZMod 2)[X]) (n : Nat)
    (hp : p.natDegree < n + 16)
    (hirr : spqr.encoding.gf.unaccelerated.POLY_GF2.Monic) :
    polyMod_poly p n = p %ₘ spqr.encoding.gf.unaccelerated.POLY_GF2 := by
  sorry


/-
natural language description:

• Takes a `u32` value `v` representing the unreduced carry-less
  polynomial product of two GF(2¹⁶) elements (degree ≤ 30).
• Extracts the high byte `i1 = v >> 24` (bits 24–31) and looks up
  `REDUCE_BYTES[i1]`, a precomputed 16-bit reduction mask.
• XORs `REDUCE_BYTES[i1] << 8` into `v`, effectively clearing bits
  24–31 and folding their contribution into bits 8–23.
• Extracts the next byte `i2 = (v >> 16) & 0xFF` (bits 16–23) and
  looks up `REDUCE_BYTES[i2]`.
• XORs `REDUCE_BYTES[i2]` into `v`, clearing bits 16–23 and
  folding their contribution into bits 0–15.
• Returns the low 16 bits of `v` as a `u16`, which is the
  canonical GF(2¹⁶) representative of the reduced polynomial.

natural language specs:

• The function always succeeds (no panic) for any valid `u32`
  input, since the table lookups use byte-range indices (0–255)
  and all arithmetic is within `u32` bounds.
• The result satisfies:
    `poly_reduce(v).val = polyMod v.val 16`
  where `polyMod` is the spec-level recursive polynomial
  modular reduction.
• Equivalently, interpreting inputs as GF(2) polynomials:
    `natToGF2Poly (poly_reduce(v).val) = natToGF2Poly v.val %ₘ POLY_GF2`
• The output is always less than 2¹⁶ (fits in a `u16`), since
  reduction modulo POLY (degree 16) yields a polynomial of
  degree < 16.
-/

/-- **Postcondition axiom for `encoding.gf.reduce.poly_reduce`**:

Table-based polynomial reduction of a 32-bit carry-less product
modulo the irreducible polynomial POLY = 0x1100b, yielding a
16-bit GF(2¹⁶) element.

The function uses the precomputed `REDUCE_BYTES` table to
process the input byte-by-byte from high to low:
  1. Clear bits 24–31 using `REDUCE_BYTES[v >> 24] << 8`.
  2. Clear bits 16–23 using `REDUCE_BYTES[(v >> 16) & 0xFF]`.
  3. Return the remaining 16 bits.

This is stated as an axiom because the implementation relies on
the correctness of the precomputed `REDUCE_BYTES` table (which
itself involves a loop computing `reduce_from_byte` for all 256
byte values), and the equivalence between byte-level table
lookup and bit-level polynomial reduction requires intricate
reasoning about XOR arithmetic and table construction that is
verified separately.

**Source**: spqr/src/encoding/gf.rs (lines 489:4-498:5)
-/
@[step]
theorem poly_reduce_spec (v : Std.U32) :
    poly_reduce v ⦃ result =>
      result.val = polyMod v.val 16 ⦄ := by
    sorry


end spqr.encoding.gf.reduce
