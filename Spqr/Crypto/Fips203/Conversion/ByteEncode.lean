/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module
public import Spqr.Crypto.Fips203.Params
public import Spqr.Crypto.Fips203.Ring
public import Spqr.Crypto.Fips203.Conversion.BitsToBytes
public import Mathlib.Tactic.Ring
/-!
# FIPS 203 Algorithm 3: `ByteEncode_d`

NIST FIPS 203 (ML-KEM, August 2024), § 4.2.1, defines `ByteEncode_d` as the conversion from
an integer array `F` of length `n = 256` into a byte array of length `32·d`.  Each integer
`F[i]` is decomposed into `d` bits in little-endian order; the resulting `256·d` bits are then
packed into bytes via `BitsToBytes` (Algorithm 1).

For `d < 12`, each `F[i]` is an element of `ℤ_q` (i.e. in `{0, …, q−1}`).
For `d = 12`, each `F[i]` is a general element of `ℤ_q` and the encoding is injective.

The algorithm:

```
ByteEncode_d(F):
  b ← ()                           ▷ empty bit string
  for (i ← 0; i < 256; i++)
    a ← F[i]
    for (j ← 0; j < d; j++)
      b[i·d + j] ← a mod 2
      a ← ⌊a / 2⌋
  B ← BitsToBytes(b)
  return B
```

The output byte array `B` has length `32·d` (since `256·d` bits = `32·d` bytes).

Its inverse is `ByteDecode_d` (Algorithm 4).

**Source**: NIST FIPS 203, § 4.2.1, Algorithm 3
-/

@[expose] public section

namespace Fips203

/-! ## Integer-to-bit decomposition -/

/-- Extract the `j`-th bit (little-endian) of a natural number as a `Fin 2`.

`intBit a j = ⌊a / 2^j⌋ mod 2`, which is bit `j` of `a`. -/
def intBit (a : ℕ) (j : ℕ) : Fin 2 :=
  ⟨(a / 2 ^ j) % 2, Nat.mod_lt _ (by omega)⟩

/-- `intBit 0 j = 0` for all `j`. -/
theorem intBit_zero (j : ℕ) : intBit 0 j = 0 := by
  simp [intBit]

/-- `intBit a 0 = a % 2`. -/
theorem intBit_zero_eq_mod2 (a : ℕ) : (intBit a 0).val = a % 2 := by
  simp [intBit]

/-! ## Bit decomposition of a coefficient array -/

/-- The number of bits in the encoding: `n · d = 8 · (32 · d)`. -/
private theorem n_mul_d_eq (d : ℕ) : n * d = 8 * (32 * d) := by unfold n; ring

/-- Decompose an integer array `F` of length `n = 256` into a bit array of length `8 · (32·d)`.

Each integer `F[i]` contributes `d` consecutive bits in little-endian order:

  `b[i·d + j] = ⌊F[i] / 2^j⌋ mod 2`     for `0 ≤ i < 256`, `0 ≤ j < d`

This corresponds to the inner double loop of `ByteEncode_d`.  The index domain is stated as
`Fin (8 * (32 * d))` (rather than `Fin (n * d)`) so that the result can be passed directly
to `bitsToBytes` without a cast. -/
def coeffsToBits (d : ℕ) (F : Fin n → ℕ) : Fin (8 * (32 * d)) → Fin 2 :=
  fun idx =>
    let idx' : ℕ := (idx : ℕ)
    let i : Fin n := ⟨idx' / d, by
      have h1 : idx' < 8 * (32 * d) := idx.isLt
      have h2 : 8 * (32 * d) = n * d := by unfold n; ring
      rw [h2] at h1
      exact Nat.div_lt_of_lt_mul (by linarith)⟩
    let j : ℕ := idx' % d
    intBit (F i) j

/-! ## `ByteEncode_d` -/

/-- **Algorithm 3 — `ByteEncode_d`** (FIPS 203, § 4.2.1).

Encodes an integer array `F` of length `n = 256` into a byte array of length `32 · d`.

Each coefficient `F[i]` is decomposed into `d` little-endian bits; the resulting
`256 · d = 8 · (32 · d)` bits are packed into bytes via `BitsToBytes`:

  `ByteEncode_d(F) = BitsToBytes(b)`

where `b[i·d + j] = ⌊F[i] / 2^j⌋ mod 2`.

The definition mirrors the FIPS 203 pseudocode:

```
ByteEncode_d(F):
  for (i ← 0; i < 256; i++)
    a ← F[i]
    for (j ← 0; j < d; j++)
      b[i·d + j] ← a mod 2
      a ← ⌊a / 2⌋
  B ← BitsToBytes(b)
  return B
```
-/
def byteEncode (d : ℕ) (F : Fin n → ℕ) : Fin (32 * d) → UInt8 :=
  bitsToBytes (coeffsToBits d F)

/-! ## `ZMod`-based interface -/

/-- `ByteEncode_d` specialised to `ℤ_q`-valued coefficient arrays.

When encoding elements of `ℤ_q`, we use the canonical representative `ZMod.val`
(which lies in `{0, …, q−1}`) as the integer to be bit-decomposed. -/
def byteEncodeZq (d : ℕ) (F : Fin n → Zq) : Fin (32 * d) → UInt8 :=
  byteEncode d (fun i => (F i).val)

/-! ## Elementary properties -/

/-- `intBit` is bounded: the extracted bit is always in `{0, 1}`. -/
theorem intBit_val_lt (a : ℕ) (j : ℕ) : (intBit a j).val < 2 :=
  (intBit a j).isLt

/-- `coeffsToBits` applied to the all-zero integer array yields the all-zero bit string. -/
theorem coeffsToBits_zero (d : ℕ) :
    coeffsToBits d (fun (_ : Fin n) => 0) = fun _ => (0 : Fin 2) := by
  funext idx
  simp only [coeffsToBits, intBit_zero]

/-- `byteEncode` applied to the all-zero integer array yields the all-zero byte string. -/
theorem byteEncode_zero (d : ℕ) :
    byteEncode d (fun (_ : Fin n) => 0) = fun _ => (0 : UInt8) := by
  simp only [byteEncode, coeffsToBits_zero d]
  exact bitsToBytes_zero (32 * d)

/-- For `a < 2^d`, the bit decomposition of `a` into `d` bits is faithful:

  `a = ∑_{j=0}^{d-1} (intBit a j) · 2^j`

This ensures that `ByteEncode_d` is injective on elements of `ℤ_q` when `d = 12`
(since `q = 3329 < 2^12 = 4096`). -/
theorem intBit_sum_eq (a : ℕ) (d : ℕ) (ha : a < 2 ^ d) :
    a = Finset.univ.sum (fun (j : Fin d) => (intBit a j).val * 2 ^ (j : ℕ)) := by
  induction d generalizing a with
  | zero =>
    have : a = 0 := by omega
    subst this; simp [intBit_zero]
  | succ d ih =>
    rw [Fin.sum_univ_succ]
    have ha' : a / 2 < 2 ^ d := Nat.div_lt_of_lt_mul (by
      rw [Nat.pow_succ] at ha; linarith)
    have hrec := ih (a / 2) ha'
    simp only [Fin.val_zero, intBit_zero_eq_mod2, pow_zero, mul_one]
    have hshift : ∀ j : Fin d, (intBit a (↑(Fin.succ j))).val = (intBit (a / 2) j).val := by
      intro j
      simp [intBit, Fin.val_succ, Nat.pow_succ, Nat.mul_comm 2, Nat.div_div_eq_div_mul]
    simp_rw [hshift]
    have hpow : ∀ j : Fin d, (intBit (a / 2) j).val * 2 ^ (↑(Fin.succ j) : ℕ) =
        2 * ((intBit (a / 2) j).val * 2 ^ (j : ℕ)) := by
      intro j; rw [Fin.val_succ]; ring
    simp_rw [hpow]
    rw [← Finset.mul_sum, ← hrec]
    omega

/-- Encoding is injective when `d = 12`: since `q = 3329 < 4096 = 2^12`, every element of
`ℤ_q` has a unique 12-bit representation, so `ByteEncode_12` is injective. -/
theorem q_lt_two_pow_12 : q < 2 ^ 12 := by norm_num [q]

end Fips203
