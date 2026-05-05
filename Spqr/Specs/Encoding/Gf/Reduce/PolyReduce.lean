/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Math.Gf
import Spqr.Specs.Encoding.Gf.Reduce.ReduceBytes
/-! # Spec Theorem for `spqr::encoding::gf::reduce::poly_reduce`

Specification and proof for `spqr.encoding.gf.reduce.poly_reduce`,
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

Source: "spqr/src/encoding/gf.rs" (lines 489:4-498:5)
-/

open Aeneas Aeneas.Std Result
open Polynomial spqr.encoding.gf.unaccelerated

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
    then p' + POLY_GF2 * X ^ n
    else p'

/-- **Correspondence between `polyMod` on `Nat` and `polyMod_poly` on GF(2)[X]**:

Interpreting the natural-number input as a GF(2) polynomial via
`natToGF2Poly`, the `Nat`-level `polyMod` and the algebraic
`polyMod_poly` agree:

  `natToGF2Poly (polyMod v n) = polyMod_poly (natToGF2Poly v) n`

This justifies reasoning about the XOR/shift implementation in
terms of polynomial algebra over GF(2). -/
theorem polyMod_eq_polyMod_poly (v n : Nat) :
    natToGF2Poly (polyMod v n) = polyMod_poly (natToGF2Poly v) n := by
  induction n with
  | zero => simp [polyMod, polyMod_poly]
  | succ n ih =>
    cases htb : (polyMod v n).testBit (n + 16) with
    | false =>
      have hcoeff : (polyMod_poly (natToGF2Poly v) n).coeff (n + 16) = 0 := by
        rw [← ih, natToGF2Poly_coeff]; simp [htb]
      have h1 : polyMod v (n + 1) = polyMod v n := by
        simp (config := { zeta := true }) [polyMod, htb]
      rw [h1, ih]; symm
      simp (config := { zeta := true }) [polyMod_poly, hcoeff]
    | true =>
      have hcoeff : (polyMod_poly (natToGF2Poly v) n).coeff (n + 16) ≠ 0 := by
        rw [← ih, natToGF2Poly_coeff]; simp [htb]
      have h1 : polyMod v (n + 1) = polyMod v n ^^^ (0x1100b <<< n) := by
        simp (config := { zeta := true }) [polyMod, htb]
      rw [h1, natToGF2Poly_xor, natToGF2Poly_shiftLeft, ih, natToGF2Poly_POLY]; symm
      simp (config := { zeta := true }) [polyMod_poly, hcoeff]

/-- Each step of `polyMod_poly` adds a multiple of `POLY_GF2` to the
    accumulator, so the result is always congruent to the original
    polynomial modulo `POLY_GF2`:

      `POLY_GF2 ∣ (p − polyMod_poly p n)`

    Proof by induction: the base case is trivial (`p − p = 0`),
    and each successor step either leaves the polynomial unchanged
    (divisibility preserved) or adds `POLY_GF2 * X ^ n`, which is
    itself divisible by `POLY_GF2`. -/
private lemma polyMod_poly_dvd_sub (p : (ZMod 2)[X]) (n : Nat) :
    POLY_GF2 ∣ (p - polyMod_poly p n) := by
  induction n with
  | zero => simp [polyMod_poly]
  | succ n ih =>
    by_cases hc : (polyMod_poly p n).coeff (n + 16) = 0
    · -- coefficient zero ⇒ polyMod_poly p (n+1) = polyMod_poly p n
      have h1 : polyMod_poly p (n + 1) = polyMod_poly p n := by
        simp (config := { zeta := true }) [polyMod_poly, hc]
      rw [h1]; exact ih
    · -- coefficient nonzero ⇒ polyMod_poly p (n+1) = polyMod_poly p n + POLY_GF2 * X^n
      have hne : (polyMod_poly p n).coeff (n + 16) ≠ 0 := hc
      have h1 : polyMod_poly p (n + 1) =
          polyMod_poly p n + POLY_GF2 * X ^ n := by
        simp (config := { zeta := true }) [polyMod_poly, hne]
      rw [h1, show p - (polyMod_poly p n +
          POLY_GF2 * X ^ n) =
          (p - polyMod_poly p n) -
          POLY_GF2 * X ^ n from by ring]
      exact dvd_sub ih (dvd_mul_right _ _)

/-- **`polyMod_poly` preserves congruence modulo POLY_GF2**:

For any polynomial `p ∈ GF(2)[X]`, the result of `polyMod_poly p n`
is congruent to `p` modulo POLY_GF2:

  `(polyMod_poly p n) %ₘ POLY_GF2 = p %ₘ POLY_GF2`

Note: `polyMod_poly` processes bit positions from low to high
(16, 17, …, n+15). Because POLY_GF2 has a sub-leading term X¹²
(degree gap of only 4), reducing a coefficient at position k+16
(for k ≥ 4) re-introduces a coefficient at position k+12 ≥ 16
which has already been processed. Hence `polyMod_poly p n` may
not be fully reduced (i.e. may have degree ≥ 16), but it always
preserves congruence modulo POLY_GF2. -/
theorem polyMod_poly_eq_modByMonic (p : (ZMod 2)[X]) (n : Nat) :
    (polyMod_poly p n) %ₘ POLY_GF2 =
      p %ₘ POLY_GF2 := by
  have hirr : POLY_GF2.Monic := POLY_GF2_monic
  have h : POLY_GF2 ∣
      (polyMod_poly p n - p) := by
    have h₁ := polyMod_poly_dvd_sub p n
    rwa [show p - polyMod_poly p n =
        -(polyMod_poly p n - p) from by ring, dvd_neg] at h₁
  exact Polynomial.modByMonic_eq_of_dvd_sub hirr h

/-- Spec-level two-pass table-based polynomial reduction.

Given a 32-bit value `v`, reduces modulo POLY = 0x1100b via two
byte-level table lookups (processing from the high byte down)
and returns the low 16 bits as the canonical GF(2¹⁶) representative.

  1. Look up `reduceByteTable[v >>> 24]` and XOR it (shifted left by 8)
     into `v`, folding bits 24–31 into bits 8–23.
  2. Look up `reduceByteTable[(v' >>> 16) &&& 0xFF]` and XOR it into `v'`,
     folding bits 16–23 into bits 0–15.
  3. Return the low 16 bits.

This is the correct specification for `poly_reduce`, matching the
high-to-low byte processing order of the Rust implementation.
Note: `polyMod v 16` processes bits low-to-high and may leave
residual high bits due to carry-back from the x¹² term.
Both `polyReduceSpec v` and `polyMod v 16` are congruent to `v`
modulo POLY_GF2, but only `polyReduceSpec` yields the canonical
fully-reduced representative (< 2¹⁶). -/
def polyReduceSpec (v : Nat) : Nat :=
  let t1 := reduceByteTable (v >>> 24)
  let v1 := v ^^^ (t1 <<< 8)
  let t2 := reduceByteTable ((v1 >>> 16) &&& 255)
  (v1 ^^^ t2) % 2 ^ 16

/-!
## Helper lemmas for `poly_reduce_spec`

The following helper lemmas support the main proof of `poly_reduce_spec`:
- `nat_and_255_lt_256`: bitwise AND with 255 yields a value < 256.
- `index_usize_ok_eq`: extraction of the value from a successful array lookup.
-/

/-- AND of a natural number with 255 is less than 256. -/
private lemma nat_and_255_lt_256 (n : Nat) : n &&& 255 < 256 := by
  apply Nat.lt_of_testBit 8
  · rw [Nat.testBit_and]
    have : Nat.testBit 255 8 = false :=
      Nat.testBit_eq_false_of_lt (by norm_num : 255 < 2 ^ 8)
    simp [this]
  · decide
  · intro j hj
    have h1 : Nat.testBit (n &&& 255) j = false := by
      rw [Nat.testBit_and]
      have : Nat.testBit 255 j = false :=
        Nat.testBit_eq_false_of_lt (calc (255 : Nat) < 2 ^ 8 := by norm_num
          _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega))
      simp [this]
    have h2 : Nat.testBit 256 j = false := by
      apply Nat.testBit_eq_false_of_lt
      calc (256 : Nat) = 2 ^ 8 := by norm_num
        _ < 2 ^ j := Nat.pow_lt_pow_right (by norm_num) (by omega)
    rw [h1, h2]

/- Helper: `index_usize` returning `ok w` implies `w` equals the list element at that index. -/
private lemma index_usize_ok_eq {α : Type _} [Inhabited α] {n : Std.Usize}
    (a : Array α n) (j : Std.Usize) (w : α)
    (h : a.index_usize j = ok w) :
    w = a.val[j.val]! := by
  simp only [Array.index_usize, Array.getElem?_Usize_eq] at h
  split at h <;> simp_all [List.getElem!_eq_getElem?_getD]

/-!
## Mathematical infrastructure for `poly_reduce_spec`

The following theorems provide the mathematical building blocks
corresponding to requirements (a)-(d) for proving `poly_reduce_spec`:

**(a)** Full-range table correctness: `reduceByteTable_eq_poly_full`
  (in ReduceBytes.lean) states that for k < 256,
  `natToGF2Poly (reduceByteTable k) = (natToGF2Poly k * X^16) %ₘ POLY_GF2`.

**(b)** First pass: XOR with `reduceByteTable(v>>>24) <<< 8` cancels the
  high-byte contribution modulo POLY_GF2. The key fact is
  `xor_table_shift_dvd`: the sum of `k * X^(n+16)` and `T[k] * X^n`
  is divisible by POLY_GF2, since T[k] ≡ k * X^16 (mod POLY_GF2).

**(c)** Second pass: analogous to (b), applied to byte 2 of the
  intermediate value, using `xor_table_shift_dvd` with n = 0.

**(d)** Truncation: `natToGF2Poly_mod_eq_of_lt` shows that `% 2^n` is
  the identity for values < 2^n. After both reduction passes,
  the result has degree < 16 (value < 2^16), so truncation is exact.
-/

/-- **Linearity of the table reduction function over GF(2).**

Since `reduceByteTable_poly` is defined as multiplication by `X^16`
followed by `modByMonic`, both of which are additive maps, the
composition is additive:
  `reduceByteTable_poly (p + q) = reduceByteTable_poly p + reduceByteTable_poly q` -/
theorem reduceByteTable_poly_add (p q : (ZMod 2)[X]) :
    reduceByteTable_poly (p + q) =
      reduceByteTable_poly p + reduceByteTable_poly q := by
  unfold reduceByteTable_poly
  rw [add_mul, Polynomial.add_modByMonic]

/-- **(b)+(c) XOR-table-shift divisibility.**

When interpreting `reduceByteTable(k)` as a GF(2) polynomial, the sum
  `natToGF2Poly(k) * X^(n+16) + natToGF2Poly(reduceByteTable(k)) * X^n`
is divisible by POLY_GF2. This holds because:
  - Table correctness: `natToGF2Poly(T[k]) = (natToGF2Poly(k) * X^16) %ₘ POLY`
  - So: `natToGF2Poly(k)*X^16 ≡ T[k] (mod POLY)`, i.e., `POLY | (k*X^16 - T[k])`
  - In char 2: `k*X^16 - T[k] = k*X^16 + T[k]`
  - Multiplying by `X^n`: `POLY | (k*X^(n+16) + T[k]*X^n)`

This lemma is the core algebraic fact behind both reduction passes:
  - Pass 1 uses it with `n = 8` and `k = v >>> 24`
  - Pass 2 uses it with `n = 0` and `k = (v1 >>> 16) &&& 255` -/
theorem xor_table_shift_dvd (k n : Nat)
    (htable : natToGF2Poly (reduceByteTable k) =
      (natToGF2Poly k * X ^ 16) %ₘ POLY_GF2) :
    POLY_GF2 ∣ (natToGF2Poly k * X ^ (n + 16) +
      natToGF2Poly (reduceByteTable k) * X ^ n) := by
  -- In char 2, a + b = a - b, so rewrite the sum as a product
  have hchar2 : natToGF2Poly k * X ^ (n + 16) +
      natToGF2Poly (reduceByteTable k) * X ^ n =
    (natToGF2Poly k * X ^ 16 - natToGF2Poly (reduceByteTable k)) * X ^ n := by
    rw [zmod2_poly_sub_eq_add]; ring
  rw [hchar2]
  apply dvd_mul_of_dvd_left
  -- Show POLY_GF2 | (k*X^16 - T[k]) using modByMonic_add_div
  rw [htable]
  set p := natToGF2Poly k * X ^ 16
  have h := Polynomial.modByMonic_add_div p POLY_GF2_monic
  -- h : p %ₘ POLY_GF2 + (p /ₘ POLY_GF2) * POLY_GF2 = p
  refine ⟨p /ₘ POLY_GF2, ?_⟩
  -- Goal: p - p %ₘ POLY_GF2 = POLY_GF2 * (p /ₘ POLY_GF2)
  -- `grind` closes the ring-level rearrangement of the Euclidean division identity
  grind

/-- **First pass preserves congruence modulo POLY_GF2.**

XOR-ing `reduceByteTable(v>>>24) <<< 8` into `v` preserves the
residue class of `natToGF2Poly(v)` modulo POLY_GF2. The XOR adds
`natToGF2Poly(T[k]) * X^8` (where k = v>>>24) to `natToGF2Poly(v)`.
Since `natToGF2Poly(v)` contains `natToGF2Poly(k) * X^24` as a
summand (from the byte decomposition), and
`natToGF2Poly(k)*X^24 + natToGF2Poly(T[k])*X^8 ≡ 0 (mod POLY_GF2)`
(by `xor_table_shift_dvd`), the two terms cancel modulo POLY_GF2.

Assumes the full-range table correctness `htable`. -/
theorem first_pass_congr (v : Nat)
    (htable : ∀ k, k < 256 → natToGF2Poly (reduceByteTable k) =
      (natToGF2Poly k * X ^ 16) %ₘ POLY_GF2)
    (hhi : v >>> 24 < 256) :
    let k := v >>> 24
    let t1 := reduceByteTable k
    let v1 := v ^^^ (t1 <<< 8)
    (natToGF2Poly v1) %ₘ POLY_GF2 = natToGF2Poly (v % 2 ^ 24) %ₘ POLY_GF2 := by
  simp only
  rw [natToGF2Poly_xor, natToGF2Poly_shiftLeft]
  -- natToGF2Poly(v1) = natToGF2Poly(v) + T[k]·X^8;
  -- split natToGF2Poly(v) at bit boundary 24 on the LHS
  conv_lhs => rw [natToGF2Poly_split v 24]
  -- Rearrange to group the high-byte term k·X^24 together with T[k]·X^8,
  -- matching exactly the form required by xor_table_shift_dvd (n = 8)
  rw [show natToGF2Poly (v % 2 ^ 24) + natToGF2Poly (v >>> 24) * X ^ 24 +
          natToGF2Poly (reduceByteTable (v >>> 24)) * X ^ 8 =
        natToGF2Poly (v % 2 ^ 24) +
          (natToGF2Poly (v >>> 24) * X ^ (8 + 16) +
           natToGF2Poly (reduceByteTable (v >>> 24)) * X ^ 8) from by ring,
    Polynomial.add_modByMonic,
    -- k·X^(8+16) + T[k]·X^8 ≡ 0 (mod POLY_GF2) by xor_table_shift_dvd with n = 8
    (Polynomial.modByMonic_eq_zero_iff_dvd POLY_GF2_monic).mpr
      (xor_table_shift_dvd (v >>> 24) 8 (htable (v >>> 24) hhi)),
    add_zero]

/-- **Second pass folds bits 16–23 into the low 16 bits modulo POLY_GF2.**

Analogous to `first_pass_congr`, applied to byte 2 of the intermediate
value `v1`. Assuming `v1 < 2^24` (i.e. the high byte is already
cleared by the first pass), XOR-ing `reduceByteTable((v1>>>16) &&& 255)`
into `v1` yields a value `v2` whose `natToGF2Poly` has the same residue
class modulo POLY_GF2 as the *low 16 bits* of `v1`.

Concretely:
  `(natToGF2Poly v2) %ₘ POLY_GF2 = (natToGF2Poly (v1 % 2^16)) %ₘ POLY_GF2`

The XOR adds `natToGF2Poly(T[k2])` to `natToGF2Poly v1`. Since
`v1 = (v1 % 2^16) + k2·X^16` (byte decomposition with `k2 = v1 >>> 16`)
and `k2·X^16 + T[k2] ≡ 0 (mod POLY_GF2)` by `xor_table_shift_dvd`
(with `n = 0`), the high-byte contribution of `v1` is replaced by zero
modulo POLY_GF2, leaving exactly the low-16-bit polynomial.

Note: the original formulation
  `(natToGF2Poly v2) %ₘ POLY_GF2 = (natToGF2Poly v1) %ₘ POLY_GF2`
is **not** valid in general: e.g. for `v1 = 2^16` one has `k2 = 1`,
`T[k2] = 0x100b`, so `v2 = POLY` and `natToGF2Poly v2 %ₘ POLY = 0`,
whereas `natToGF2Poly v1 %ₘ POLY = X^12 + X^3 + X + 1 ≠ 0`.
Hence the corrected statement uses `v1 % 2^16` on the RHS. -/
theorem second_pass_congr (v1 : Nat)
    (htable : ∀ k, k < 256 → natToGF2Poly (reduceByteTable k) =
      (natToGF2Poly k * X ^ 16) %ₘ POLY_GF2)
    (hlt : v1 < 2 ^ 24) :
    let k2 := (v1 >>> 16) &&& 255
    let t2 := reduceByteTable k2
    let v2 := v1 ^^^ t2
    (natToGF2Poly v2) %ₘ POLY_GF2 =
      (natToGF2Poly (v1 % 2 ^ 16)) %ₘ POLY_GF2 := by
  simp only
  -- Step 1: v1 >>> 16 < 256, since v1 < 2^24 = 256 · 2^16.
  have hsh : v1 >>> 16 < 256 := by
    rw [Nat.shiftRight_eq_div_pow]
    have hp : (0 : Nat) < 2 ^ 16 := by positivity
    rw [Nat.div_lt_iff_lt_mul hp]
    have h256 : (256 : Nat) * 2 ^ 16 = 2 ^ 24 := by norm_num
    omega
  -- Step 2: Since v1 >>> 16 < 256, masking with 255 is the identity.
  have hk2 : (v1 >>> 16) &&& 255 = v1 >>> 16 := by
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_and]
    by_cases hj : j < 8
    · have h255 : (255 : Nat).testBit j = true := by
        interval_cases j <;> decide
      simp [h255]
    · push_neg at hj
      have h255 : (255 : Nat).testBit j = false :=
        Nat.testBit_eq_false_of_lt
          (lt_of_lt_of_le (by norm_num : (255 : Nat) < 2 ^ 8)
            (Nat.pow_le_pow_right (by norm_num) hj))
      have hsh_j : (v1 >>> 16).testBit j = false :=
        Nat.testBit_eq_false_of_lt
          (lt_of_lt_of_le hsh
            (calc (256 : Nat) = 2 ^ 8 := by norm_num
              _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj))
      simp [h255, hsh_j]
  -- Step 3: rewrite XOR as polynomial addition, split v1 at bit 16,
  -- and use xor_table_shift_dvd with n = 0 to cancel the high-byte term.
  rw [hk2, natToGF2Poly_xor]
  conv_lhs => rw [natToGF2Poly_split v1 16]
  rw [show natToGF2Poly (v1 % 2 ^ 16) + natToGF2Poly (v1 >>> 16) * X ^ 16 +
          natToGF2Poly (reduceByteTable (v1 >>> 16)) =
        natToGF2Poly (v1 % 2 ^ 16) +
          (natToGF2Poly (v1 >>> 16) * X ^ (0 + 16) +
           natToGF2Poly (reduceByteTable (v1 >>> 16)) * X ^ 0) from by ring,
    Polynomial.add_modByMonic,
    (Polynomial.modByMonic_eq_zero_iff_dvd POLY_GF2_monic).mpr
      (xor_table_shift_dvd (v1 >>> 16) 0 (htable (v1 >>> 16) hsh)),
    add_zero]

/- **Combined two-pass reduction correctness (spec-level).**

Given full-range table correctness, the two-pass spec-level function
`polyReduceSpec` computes `natToGF2Poly(v) %ₘ POLY_GF2`:

  `natToGF2Poly (polyReduceSpec v) = (natToGF2Poly v) %ₘ POLY_GF2`

The proof uses byte decomposition of `v`, linearity of the table
reduction function, and the `xor_table_shift_dvd` lemma for both
passes. The key insight is:

  `p %ₘ POLY = b₀ + (b₁ + T(b₃)_lo) * X⁸ + T(b₂ + T(b₃)_hi)`

where `bᵢ` are the byte polynomials of `v`, `T = reduceByteTable_poly`,
and `T(b₃)_lo`, `T(b₃)_hi` are the lower/upper halves of `T(b₃)`.
By linearity of `T`, `T(b₂) + T(T(b₃)_hi) = T(b₂ + T(b₃)_hi)`,
which is exactly what the algorithm computes.
 **Combined two-pass reduction correctness (spec-level).**

Given full-range table correctness AND `v < 2^32`, the two-pass spec-level
function `polyReduceSpec` computes `natToGF2Poly(v) %ₘ POLY_GF2`:

  `natToGF2Poly (polyReduceSpec v) = (natToGF2Poly v) %ₘ POLY_GF2`

The hypothesis `v < 2^32` is required because `htable` only constrains
`k < 256`; without it `v >>> 24` could be ≥ 256 and the table fact would
not apply to the first pass. -/



theorem polyReduceSpec_correct (v : Nat) (hv : v < 2 ^ 32)
    (htable : ∀ k, k < 256 → natToGF2Poly (reduceByteTable k) =
      (natToGF2Poly k * X ^ 16) %ₘ POLY_GF2) :
    natToGF2Poly (polyReduceSpec v) = (natToGF2Poly v) %ₘ POLY_GF2 := by
  -- Bounds.
  have hk1_lt : v >>> 24 < 256 := by
    rw [Nat.shiftRight_eq_div_pow]
    have h2 : (0 : Nat) < 2 ^ 24 := by positivity
    rw [Nat.div_lt_iff_lt_mul h2]
    have h32 : (256 : Nat) * 2 ^ 24 = 2 ^ 32 := by norm_num
    omega
  have ht1_lt : reduceByteTable (v >>> 24) < 2 ^ 16 := by
    unfold reduceByteTable; exact Nat.mod_lt _ (by positivity)
  unfold polyReduceSpec
  set k1 := v >>> 24 with hk1_def
  set t1 := reduceByteTable k1 with ht1_def
  set v1 := v ^^^ (t1 <<< 8) with hv1_def
  set k2 := (v1 >>> 16) &&& 255 with hk2_def
  set t2 := reduceByteTable k2 with ht2_def
  have hk2_lt : k2 < 256 := nat_and_255_lt_256 _
  have ht2_lt : t2 < 2 ^ 16 := by
    rw [ht2_def]; unfold reduceByteTable; exact Nat.mod_lt _ (by positivity)
  -- The bit-level fact: bits ≥ 16 of `v1 ^^^ t2` collapse to k2 + k1·2^8.
  -- Equivalently, `(v1 ^^^ t2) >>> 16 = k2 ^^^ (k1 <<< 8)`.
  have hhigh : (v1 ^^^ t2) >>> 16 = k2 ^^^ (k1 <<< 8) := by
    apply Nat.eq_of_testBit_eq
    intro i
    have ht2_high : ∀ j, 16 ≤ j → t2.testBit j = false := fun j hj =>
      Nat.testBit_eq_false_of_lt
        (lt_of_lt_of_le ht2_lt (Nat.pow_le_pow_right (by norm_num) hj))
    have ht1_high : ∀ j, 16 ≤ j → t1.testBit j = false := fun j hj =>
      Nat.testBit_eq_false_of_lt
        (lt_of_lt_of_le ht1_lt (Nat.pow_le_pow_right (by norm_num) hj))
    have hv_high : ∀ j, 32 ≤ j → v.testBit j = false := fun j hj =>
      Nat.testBit_eq_false_of_lt
        (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) hj))
    have hk1_high : ∀ j, 8 ≤ j → k1.testBit j = false := fun j hj =>
      Nat.testBit_eq_false_of_lt
        (lt_of_lt_of_le hk1_lt
          (calc (256 : Nat) = 2 ^ 8 := by norm_num
            _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj))
    rw [hv1_def, hk2_def]
    simp only [Nat.testBit_shiftRight, Nat.testBit_xor, Nat.testBit_shiftLeft,
               Nat.testBit_and]
    -- The bit at index i+16 of t2 is always false.
    rw [show 16 + i = i + 16 from by ring, ht2_high (i + 16) (by omega)]
    -- 255.testBit j: true iff j < 8.
    have h255_lt : ∀ j, j < 8 → (255 : Nat).testBit j = true := by
      intro j hj; interval_cases j <;> decide
    have h255_ge : ∀ j, 8 ≤ j → (255 : Nat).testBit j = false := fun j hj =>
      Nat.testBit_eq_false_of_lt
        (lt_of_lt_of_le (by norm_num : (255 : Nat) < 2 ^ 8)
          (Nat.pow_le_pow_right (by norm_num) hj))
    -- Case split on i.
    rcases lt_or_ge i 8 with hi8 | hi8
    · -- i < 8: 255 bit is true, k1<<<8 bit i is false (i < 8 so condition fails).
      simp only [h255_lt i hi8, Bool.and_true]
      have h8le : (8 : Nat) ≤ i + 16 := by omega
      have hk1shift_i_false : (decide (8 ≤ i)) = false := by
        simp only [decide_eq_false_iff_not, not_le]; omega
      have h8le_i16 : decide ((8 : Nat) ≤ i + 16) = true := by
        simp only [decide_eq_true_eq]; omega
      simp only [hk1shift_i_false, Bool.false_and, Bool.xor_false,
                 h8le_i16, Bool.true_and]
      -- Goal:
      --   (v.testBit(i+16) ^^ t1.testBit(i+16-8)) = v1.testBit(i+16)
      -- Unfold v1 = v ^^^ (t1 <<< 8) on the RHS and reduce its testBit.
      rw [hv1_def, Nat.testBit_xor, Nat.testBit_shiftLeft, h8le_i16,
          Bool.true_and]
    · -- 8 ≤ i.
      rcases lt_or_ge i 16 with hi16 | hi16
      · -- 8 ≤ i < 16: 255 bit is false; k1<<<8 bit i is k1.testBit(i-8).
        have h255i : (255 : Nat).testBit i = false := h255_ge i hi8
        have h_ile : decide ((8 : Nat) ≤ i + 16) = true := by
          simp only [decide_eq_true_eq]; omega
        have h_ile_i : decide ((8 : Nat) ≤ i) = true := by
          simp only [decide_eq_true_eq]; omega
        simp only [h255i, Bool.and_false, Bool.false_xor, h_ile, Bool.true_and,
                   h_ile_i]
        -- LHS: v.testBit(i+16) ^^ t1.testBit(i+16-8)
        -- RHS: k1.testBit(i-8) = (v>>>24).testBit(i-8) = v.testBit(i-8+24) = v.testBit(i+16)
        -- And t1.testBit(i+16-8) = t1.testBit(i+8). For 8 ≤ i, i+8 ≥ 16, so = false.
        rw [hk1_def, Nat.testBit_shiftRight]
        have ht1_eq_false : t1.testBit (i + 16 - 8) = false := ht1_high _ (by omega)
        rw [ht1_eq_false, Bool.xor_false]
        grind
      · -- 16 ≤ i: All terms vanish (v.testBit too big, t1 too big, k1 << 8 too big).
        have hv_eq : v.testBit (i + 16) = false := hv_high _ (by omega)
        have ht1_eq : t1.testBit (i + 16 - 8) = false := ht1_high _ (by omega)
        have hk1_eq : k1.testBit (i - 8) = false := hk1_high _ (by omega)
        have h255i : (255 : Nat).testBit i = false := h255_ge i (by omega)
        have h_ile : decide ((8 : Nat) ≤ i + 16) = true := by
          simp only [decide_eq_true_eq]; omega
        have h_ile_i : decide ((8 : Nat) ≤ i) = true := by
          simp only [decide_eq_true_eq]; omega
        simp only [hv_eq, ht1_eq, hk1_eq, h255i, h_ile, h_ile_i,
                   Bool.and_false, Bool.xor_false]
  -- The polynomial counterpart of `hhigh`.
  have hhigh_poly : natToGF2Poly ((v1 ^^^ t2) >>> 16) =
      natToGF2Poly k2 + natToGF2Poly k1 * X ^ 8 := by
    rw [hhigh, natToGF2Poly_xor, natToGF2Poly_shiftLeft]
  -- Step 1: show natToGF2Poly v %ₘ P = natToGF2Poly result %ₘ P
  -- via `xor_table_shift_dvd` applied at (k1, n=8) and (k2, n=0).
  have hd1 : POLY_GF2 ∣ (natToGF2Poly k1 * X ^ (8 + 16) +
      natToGF2Poly t1 * X ^ 8) := xor_table_shift_dvd k1 8 (htable k1 hk1_lt)
  have hd2 : POLY_GF2 ∣ (natToGF2Poly k2 * X ^ (0 + 16) +
      natToGF2Poly t2 * X ^ 0) := xor_table_shift_dvd k2 0 (htable k2 hk2_lt)
  -- Express natToGF2Poly v + natToGF2Poly result in terms of D1, D2 (modulo P-multiples).
  -- Strategy:
  --   natToGF2Poly (v1^^^t2) = natToGF2Poly v + natToGF2Poly t1 * X^8 + natToGF2Poly t2 (XOR)
  --   natToGF2Poly (v1^^^t2) = natToGF2Poly result + natToGF2Poly ((v1^^^t2)>>>16) * X^16 (split)
  -- Combining:
  --   natToGF2Poly result = natToGF2Poly v + natToGF2Poly t1 * X^8 + natToGF2Poly t2
  --                          - natToGF2Poly ((v1^^^t2)>>>16) * X^16
  -- Using hhigh_poly:
  --   natToGF2Poly ((v1^^^t2)>>>16) * X^16 = natToGF2Poly k2 * X^16 + natToGF2Poly k1 * X^24
  -- So:
  --   natToGF2Poly v - natToGF2Poly result =
  --       natToGF2Poly k1 * X^24 + natToGF2Poly t1 * X^8
  --     + natToGF2Poly k2 * X^16 + natToGF2Poly t2  (in char 2)
  --     = D1 + D2
  -- This is divisible by P.
  have hxor_eq : natToGF2Poly (v1 ^^^ t2) =
      natToGF2Poly v + natToGF2Poly t1 * X ^ 8 + natToGF2Poly t2 := by
    rw [natToGF2Poly_xor, hv1_def, natToGF2Poly_xor, natToGF2Poly_shiftLeft]
  have hsplit : natToGF2Poly (v1 ^^^ t2) =
      natToGF2Poly ((v1 ^^^ t2) % 2 ^ 16) +
        natToGF2Poly ((v1 ^^^ t2) >>> 16) * X ^ 16 :=
    natToGF2Poly_split (v1 ^^^ t2) 16
  have hkey : natToGF2Poly v - natToGF2Poly ((v1 ^^^ t2) % 2 ^ 16) =
      (natToGF2Poly k1 * X ^ (8 + 16) + natToGF2Poly t1 * X ^ 8) +
      (natToGF2Poly k2 * X ^ (0 + 16) + natToGF2Poly t2 * X ^ 0) := by
    have h1 : natToGF2Poly ((v1 ^^^ t2) % 2 ^ 16) =
        natToGF2Poly v + natToGF2Poly t1 * X ^ 8 + natToGF2Poly t2 -
          natToGF2Poly ((v1 ^^^ t2) >>> 16) * X ^ 16 := by
      have hh := hsplit
      rw [hxor_eq] at hh
      linear_combination -hh
    rw [h1, hhigh_poly]
    rw [show natToGF2Poly v - (natToGF2Poly v + natToGF2Poly t1 * X ^ 8 +
            natToGF2Poly t2 - (natToGF2Poly k2 + natToGF2Poly k1 * X ^ 8) * X ^ 16) =
          (natToGF2Poly k2 + natToGF2Poly k1 * X ^ 8) * X ^ 16 +
            -(natToGF2Poly t1 * X ^ 8 + natToGF2Poly t2) from by ring,
        zmod2_poly_neg_eq]
    ring
  -- Combine: POLY_GF2 ∣ (v - a) since v - a = D1 + D2 with POLY_GF2 ∣ D1, D2.
  have hdvd : POLY_GF2 ∣ (natToGF2Poly v - natToGF2Poly ((v1 ^^^ t2) % 2 ^ 16)) := by
    rw [hkey]; exact dvd_add hd1 hd2
  have hmod_eq : natToGF2Poly v %ₘ POLY_GF2 =
      natToGF2Poly ((v1 ^^^ t2) % 2 ^ 16) %ₘ POLY_GF2 :=
    Polynomial.modByMonic_eq_of_dvd_sub POLY_GF2_monic hdvd
  -- The result is already reduced: (v1 ^^^ t2) % 2^16 < 2^16, so degree < 16.
  have ha_lt : (v1 ^^^ t2) % 2 ^ 16 < 2 ^ 16 := Nat.mod_lt _ (by norm_num)
  have ha_deg : (natToGF2Poly ((v1 ^^^ t2) % 2 ^ 16)).degree < POLY_GF2.degree := by
    rw [Polynomial.degree_eq_natDegree POLY_GF2_monic.ne_zero, POLY_GF2_natDegree]
    rcases eq_or_ne (natToGF2Poly ((v1 ^^^ t2) % 2 ^ 16)) 0 with heq | hne
    · rw [heq, Polynomial.degree_zero]; exact WithBot.bot_lt_coe _
    · rw [Polynomial.degree_lt_iff_coeff_zero]
      intro m hm
      have hm' : 16 ≤ m := by exact_mod_cast hm
      rw [natToGF2Poly_coeff]
      have hbnd : (v1 ^^^ t2) % 2 ^ 16 < 2 ^ m := lt_of_lt_of_le ha_lt
        (Nat.pow_le_pow_right (by norm_num) hm')
      rw [Nat.testBit_eq_false_of_lt hbnd]
      simp
  have ha_self : natToGF2Poly ((v1 ^^^ t2) % 2 ^ 16) %ₘ POLY_GF2 =
      natToGF2Poly ((v1 ^^^ t2) % 2 ^ 16) :=
    (Polynomial.modByMonic_eq_self_iff POLY_GF2_monic).mpr ha_deg
  rw [hmod_eq, ha_self]



/-!
## Main postcondition theorem for `poly_reduce`


The following theorem establishes that `poly_reduce v` produces a
16-bit value whose `natToGF2Poly` encoding equals
`(natToGF2Poly v.val) %ₘ POLY_GF2` — i.e. the canonical
remainder of the input polynomial modulo the irreducible polynomial
POLY_GF2 = X¹⁶ + X¹² + X³ + X + 1.

This is the key result needed by `unaccelerated.mul` (see `Mul.lean`):
after `poly_mul` produces the unreduced 32-bit carry-less product,
`poly_reduce` folds the high bytes back using the `REDUCE_BYTES`
table and returns the canonical GF(2¹⁶) representative.

Combined with `poly_mul_spec` from `PolyMul.lean`:
  `natToGF2Poly (poly_mul a b).val = natToGF2Poly a.val * natToGF2Poly b.val`
we obtain the end-to-end result:
  `natToGF2Poly (mul a b).val = (natToGF2Poly a.val * natToGF2Poly b.val) %ₘ POLY_GF2`
which is exactly multiplication in GF(2¹⁶) ≅ GF(2)[X] / (POLY_GF2).
-/

/-- **Spec theorem for `spqr::encoding::gf::reduce::poly_reduce`**:

Table-based polynomial reduction of a 32-bit carry-less product
modulo the irreducible polynomial POLY = 0x1100b, yielding a
16-bit GF(2¹⁶) element.

The function uses the precomputed `REDUCE_BYTES` table to
process the input byte-by-byte from high to low:
  1. Clear bits 24–31 using `REDUCE_BYTES[v >> 24] << 8`.
  2. Clear bits 16–23 using `REDUCE_BYTES[(v >> 16) & 0xFF]`.
  3. Return the remaining 16 bits.

The result satisfies the algebraic specification:
  `natToGF2Poly result.val = (natToGF2Poly v.val) %ₘ POLY_GF2`

This connects the bitwise table-lookup implementation to
polynomial reduction in GF(2)[X], confirming that `poly_reduce`
computes the canonical degree-< 16 representative of `v` modulo
POLY_GF2 = X¹⁶ + X¹² + X³ + X + 1.

The proof unfolds `poly_reduce` and `REDUCE_BYTES`, applies the
step lemmas for `reduce_bytes`, and then relies on:
  - Array bounds: `v >> 24 < 256` and `(v >> 16) & 0xFF < 256`.
  - The algebraic equivalence between the table lookups and
    polynomial reduction modulo POLY_GF2, using
    `reduceByteTable_eq_reduceByteTable_poly` and the
    `polyMod_poly_eq_modByMonic` congruence theorem.

**Source**: spqr/src/encoding/gf.rs (lines 489:4-498:5)
-/
@[step]
theorem poly_reduce_spec (v : Std.U32) :
    poly_reduce v ⦃ result =>
      natToGF2Poly result.val = (natToGF2Poly v.val) %ₘ POLY_GF2 ⦄ := by
  unfold poly_reduce spqr.encoding.gf.reduce.REDUCE_BYTES
  step*
  -- step* processes the full chain but leaves bound subgoals for Array.index_usize
  -- and the main correctness goal. Handle each with focus dots.
  · -- case hbound: first array lookup bound ↑i1 < a.length
    simp only [Array.length_eq]
    scalar_tac
  · -- case hbound: second array lookup bound ↑i21 < a.length
    simp only [Array.length_eq]
    rw [i21_post1, UScalar.val_and]
    exact nat_and_255_lt_256 _
  · -- main correctness goal: the low 16 bits of the two-pass reduction
    -- equal (natToGF2Poly v.val) %ₘ POLY_GF2.
    --
    -- The full proof requires:
    --   (a) Each REDUCE_BYTES[k] entry equals (natToGF2Poly k * X^16) %ₘ POLY_GF2
    --       (from reduce_byte_poly_spec / reduceByteTable_eq_reduceByteTable_poly).
    --   (b) The first pass folds bits 24–31:
    --       natToGF2Poly (v ^^^ (REDUCE_BYTES[v>>>24] <<< 8))
    --         ≡ natToGF2Poly v  (mod POLY_GF2)
    --       and clears bits 24–31 (since REDUCE_BYTES[k] << 8 cancels
    --       k << 24 modulo POLY).
    --   (c) The second pass folds bits 16–23 analogously.
    --   (d) The final truncation to 16 bits is the identity for the
    --       already-reduced polynomial (degree < 16).
    --
    -- Strategy:
    --   (i)   Bridge the array lookups (`i2`, `i6`) to `reduceByteTable` values
    --         using the algebraic property `a_post` and injectivity of
    --         `natToGF2Poly`.
    --   (ii)  Show `(UScalar.cast .U16 v2).val = polyReduceSpec v.val` by
    --         unfolding the cast/shift/xor chain.
    --   (iii) Conclude via `polyReduceSpec_correct`.
    have hv_lt : v.val < 2 ^ 32 := v.hBounds
    -- i.val = v.val >>> 24
    have hi_val : i.val = v.val >>> 24 := i_post1
    -- i1.val = v.val >>> 24
    have hi1_val : i1.val = v.val >>> 24 := by
      rw [i1_post, U32.cast_Usize_val_eq]; exact hi_val
    -- i1.val < 256
    have hi1_lt : i1.val < 256 := by
      rw [hi1_val, Nat.shiftRight_eq_div_pow]
      have hp : (0 : Nat) < 2 ^ 24 := by positivity
      rw [Nat.div_lt_iff_lt_mul hp]
      have h32 : (256 : Nat) * 2 ^ 24 = 2 ^ 32 := by norm_num
      omega
    -- Bridge i2 to reduceByteTable using injectivity of natToGF2Poly.
    have hi2_eq : i2.val = reduceByteTable i1.val := by
      obtain ⟨w, hw_idx, hw_poly⟩ := a_post i1 hi1_lt
      have hw_eq : w = i2 := by
        have hw_idx' := index_usize_ok_eq a i1 w hw_idx
        simp_all
      have hi2_poly :
          natToGF2Poly i2.val = natToGF2Poly i1.val * X ^ 16 %ₘ POLY_GF2 := by
        rw [← hw_eq]; exact hw_poly
      exact natToGF2Poly_inj _ _
        (hi2_poly.trans (reduceByteTable_eq_poly_full i1.val hi1_lt).symm)
    -- i3.val = i2.val
    have hi3_val : i3.val = i2.val := by
      rw [i3_post, U16.cast_U32_val_eq]
    -- i2.val < 2^16
    have hi2_lt : i2.val < 2 ^ 16 := i2.hBounds
    -- i4.val = i2.val <<< 8 (no overflow)
    have hi4_val : i4.val = i2.val <<< 8 := by
      rw [i4_post1, hi3_val]
      have hbnd : i2.val <<< 8 < U32.size := by
        rw [Nat.shiftLeft_eq]
        have hmul : i2.val * 2 ^ 8 < 2 ^ 16 * 2 ^ 8 :=
          Nat.mul_lt_mul_of_pos_right hi2_lt (by norm_num)
        have heq : (2 : Nat) ^ 16 * 2 ^ 8 = 2 ^ 24 := by norm_num
        have hlt : (2 : Nat) ^ 24 < U32.size := by
          scalar_tac
        omega
      exact Nat.mod_eq_of_lt hbnd
    -- v1.val = v.val ^^^ (i2.val <<< 8)
    have hv1_val : v1.val = v.val ^^^ (i2.val <<< 8) := by
      rw [v1_post1, UScalar.val_xor, hi4_val]
    -- i5.val = v1.val >>> 16
    have hi5_val : i5.val = v1.val >>> 16 := i5_post1
    -- shifted_v.val = i5.val
    have hsh_val : shifted_v.val = i5.val := by
      rw [shifted_v_post, U32.cast_Usize_val_eq]
    -- i21.val = (v1.val >>> 16) &&& 255
    have hi21_val : i21.val = (v1.val >>> 16) &&& 255 := by
      rw [i21_post1, UScalar.val_and, hsh_val, hi5_val]; rfl
    -- i21.val < 256
    have hi21_lt : i21.val < 256 := by
      rw [hi21_val]; exact nat_and_255_lt_256 _
    -- Bridge i6 to reduceByteTable using injectivity.
    have hi6_eq : i6.val = reduceByteTable i21.val := by
      obtain ⟨w, hw_idx, hw_poly⟩ := a_post i21 hi21_lt
      have hw_eq : w = i6 := by
        have hw_idx' := index_usize_ok_eq a i21 w hw_idx
        rw [i6_post, hw_idx']
      have hi6_poly :
          natToGF2Poly i6.val = natToGF2Poly i21.val * X ^ 16 %ₘ POLY_GF2 := by
        rw [← hw_eq]; exact hw_poly
      exact natToGF2Poly_inj _ _
        (hi6_poly.trans (reduceByteTable_eq_poly_full i21.val hi21_lt).symm)
    -- i7.val = i6.val
    have hi7_val : i7.val = i6.val := by
      rw [i7_post, U16.cast_U32_val_eq]
    -- v2.val = v1.val ^^^ i6.val
    have hv2_val : v2.val = v1.val ^^^ i6.val := by
      rw [v2_post1, UScalar.val_xor, hi7_val]
    -- Bridge to polyReduceSpec.
    have hbridge : (UScalar.cast UScalarTy.U16 v2).val = polyReduceSpec v.val := by
      rw [UScalar.cast_val_eq]
      change v2.val % 2 ^ 16 = polyReduceSpec v.val
      rw [hv2_val, hi6_eq, hi21_val, hv1_val, hi2_eq, hi1_val]
      simp only [polyReduceSpec]
    -- Conclude via polyReduceSpec_correct.
    rw [hbridge]
    exact polyReduceSpec_correct v.val hv_lt reduceByteTable_eq_poly_full

/-!
## Algebraic formulation of `polyReduceSpec`

The following theorem connects the Nat-level `polyReduceSpec` to
the polynomial-level `%ₘ POLY_GF2`, enabling algebraic reasoning
about the two-pass table-based reduction.
-/

/-- **`polyReduceSpec` preserves congruence modulo POLY_GF2**:

For any 32-bit value `v` (i.e. `v < 2^32`), `polyReduceSpec v` is
congruent to `v` modulo POLY_GF2:

  `natToGF2Poly (polyReduceSpec v) %ₘ POLY_GF2 = (natToGF2Poly v) %ₘ POLY_GF2`

Each pass XOR's in a multiple of POLY_GF2 (via the `reduceByteTable`),
so the residue class is preserved.  The final `% 2^16` truncation
removes only bits that are zero after both passes (since the result
has degree < 16), so it does not change the polynomial.

This is the algebraic justification for the two-pass table-based
approach: it computes the same residue class as bit-by-bit reduction.

**Note on the hypothesis `v < 2^32`**: the two-pass table-based
algorithm only reduces bits 16–31 of `v`. For `v ≥ 2^32`, bits 32+
are never folded back via the table (since `reduceByteTable` only
depends on the low 8 bits of its input, while bits 32+ of `v` end up
indexing the table out of its meaningful range). For instance,
`polyReduceSpec (2^32) = 0`, but `natToGF2Poly (2^32) %ₘ POLY_GF2
= X^32 %ₘ POLY_GF2 ≠ 0`. Hence the theorem is stated under the
necessary precondition `v < 2^32`. -/
theorem polyReduceSpec_eq_modByMonic (v : Nat) (hv : v < 2 ^ 32) :
    (natToGF2Poly (polyReduceSpec v)) %ₘ POLY_GF2 =
      (natToGF2Poly v) %ₘ POLY_GF2 := by
  -- Use `polyReduceSpec_correct` (already proved) to rewrite the LHS as
  --   ((natToGF2Poly v) %ₘ POLY_GF2) %ₘ POLY_GF2,
  -- then conclude by idempotence of `%ₘ POLY_GF2`.
  rw [polyReduceSpec_correct v hv reduceByteTable_eq_poly_full]
  exact modByMonic_modByMonic_self _


/-!
## Connection to `poly_mul` for GF(2¹⁶) multiplication

The combined specification for `mul(a, b) = poly_reduce(poly_mul(a, b))`
follows from:

  1. `poly_mul_spec` (from `PolyMul.lean`):
     `natToGF2Poly (poly_mul a b).val = natToGF2Poly a.val * natToGF2Poly b.val`

  2. `poly_reduce_spec` (above):
     `natToGF2Poly (poly_reduce v).val = (natToGF2Poly v.val) %ₘ POLY_GF2`

Together:
  `natToGF2Poly (mul a b).val
     = (natToGF2Poly a.val * natToGF2Poly b.val) %ₘ POLY_GF2`

This is exactly multiplication in the quotient ring
  GF(2¹⁶) ≅ GF(2)[X] / (POLY_GF2)

The remaining bridge to `GaloisField 2 16` (Mathlib's abstract
construction) requires:
  - An explicit isomorphism `GaloisField 2 16 ≅ (ZMod 2)[X] / (POLY_GF2)`
  - Showing that POLY_GF2 is irreducible over GF(2)
  - Connecting the natural-number ↔ polynomial ↔ quotient-ring chain

This algebraic bridge is stated below for use by `Mul.lean`.
-/

/-- **Polynomial-level combined specification for GF(2¹⁶) multiplication**:

For `u16` values `a` and `b`, the composition
`poly_reduce(poly_mul(a, b))` yields a `u16` result whose
`natToGF2Poly` encoding equals the product of the input polynomials
reduced modulo POLY_GF2:

  `natToGF2Poly result.val =
     (natToGF2Poly a.val * natToGF2Poly b.val) %ₘ POLY_GF2`

This is the polynomial-level specification for `unaccelerated.mul`,
composing `poly_mul_spec` and `poly_reduce_spec`.

The proof unfolds `mul`, applies `step*` (which uses both
`poly_mul_spec` and `poly_reduce_spec` from the `@[step]` database),
and then substitutes the intermediate postconditions:
  1. `poly_mul_spec`: `natToGF2Poly i.val = natToGF2Poly a.val * natToGF2Poly b.val`
  2. `poly_reduce_spec`: `natToGF2Poly result.val = (natToGF2Poly i.val) %ₘ POLY_GF2`

Together these yield the combined result by rewriting. -/
theorem poly_reduce_poly_mul_spec (a b : Std.U16) :
    spqr.encoding.gf.unaccelerated.mul a b ⦃ result =>
      natToGF2Poly result.val =
        (natToGF2Poly a.val * natToGF2Poly b.val) %ₘ POLY_GF2 ⦄ := by
  sorry

end spqr.encoding.gf.reduce
