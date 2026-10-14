/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module
public import Spqr.Crypto.Fips203.Params
public import Mathlib.Tactic.Ring
/-!
# FIPS 203 Algorithm 1: `BitsToBytes`

NIST FIPS 203 (ML-KEM, August 2024), § 4.2.1, defines `BitsToBytes` as the conversion from a
bit array of length `8·ℓ` to a byte array of length `ℓ`.  Each group of eight consecutive bits
is packed into a single byte in little-endian order:

  `B[i] = ∑_{j=0}^{7} b[8·i + j] · 2^j`     for `0 ≤ i < ℓ`

This is the fundamental serialisation primitive upon which `ByteEncode_d` (Algorithm 3) is
built.  Its inverse is `BytesToBits` (Algorithm 2).

**Source**: NIST FIPS 203, § 4.2.1, Algorithm 1
-/

@[expose] public section

namespace Fips203

/-! ## Bit-to-byte packing -/

/-- Helper: Horner-style fold that accumulates `n` bits (little-endian) into a natural number.

`packBitsAux bits n` uses Horner's method, processing bits from the most-significant
(bit 7) down to the least-significant (bit 0):

  `packBitsAux bits 0       = 0`
  `packBitsAux bits (n + 1) = 2 * packBitsAux bits n + bits(8 - (n+1))`

After 8 steps this yields `∑_{j=0}^{7} bits(j) · 2^j`.  The recursive structure makes
inductive proofs straightforward. -/
def packBitsAux (bits : Fin 8 → Fin 2) : (n : ℕ) → (h : n ≤ 8) → ℕ
  | 0,     _ => 0
  | n + 1, h => 2 * packBitsAux bits n (by omega) + (bits ⟨8 - (n + 1), by omega⟩).val

/-- Pack a single group of 8 bits (little-endian) into one byte.

Given a function `bits : Fin 8 → Fin 2`, returns

  `∑_{j=0}^{7} bits(j) · 2^j`

as a `UInt8`.

The implementation uses a recursive Horner-style accumulation (`packBitsAux`) that is
straightforward to reason about by induction, unlike a `Finset.sum`-based definition. -/
def packByte (bits : Fin 8 → Fin 2) : UInt8 :=
  (packBitsAux bits 8 (le_refl 8)).toUInt8

/-! ### `packBitsAux` lemmas -/

/-- `packBitsAux` is bounded by `2^n`. -/
theorem packBitsAux_lt (bits : Fin 8 → Fin 2) (n : ℕ) (h : n ≤ 8) :
    packBitsAux bits n h < 2 ^ n := by
  induction n with
  | zero => simp [packBitsAux]
  | succ n ih =>
    simp only [packBitsAux, Nat.pow_succ]
    have hbit : (bits ⟨n, by omega⟩).val < 2 := (bits ⟨n, by omega⟩).isLt
    have hprev := ih (by omega)
    omega

/-- Bridge: the recursive `packByte` agrees with the `Finset.univ.sum` specification. -/
theorem packByte_eq_sum (bits : Fin 8 → Fin 2) :
    packByte bits =
      (Finset.univ.sum fun (j : Fin 8) => (bits j).val * 2 ^ (j : ℕ)).toUInt8 := by
  unfold packByte
  congr 1
  simp only [packBitsAux, Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, Finset.sum_range_zero]
  simp (config := { decide := true })
  ring

/-- **Algorithm 1 — `BitsToBytes`** (FIPS 203, § 4.2.1).

Converts a bit array `b` of length `8 * l` into a byte array of length `l`.

Each output byte `B[i]` is the little-endian packing of the eight bits
`b[8·i], b[8·i+1], …, b[8·i+7]`:

  `B[i] = ∑_{j=0}^{7} b[8·i + j] · 2^j`

The definition mirrors the FIPS 203 pseudocode:

```
BitsToBytes(b):
  for (i ← 0; i < len(b)/8; i++)
    B[i] ← ∑_{j=0}^{7} b[8i + j] · 2^j
  return B
```
-/
def bitsToBytes {l : ℕ} (b : Fin (8 * l) → Fin 2) : Fin l → UInt8 :=
  fun i => packByte (fun j =>
    b ⟨8 * (i : ℕ) + (j : ℕ), by omega⟩)

/-! ## Elementary properties -/

/-- Each output byte is bounded by `2^8 - 1 = 255` (trivially true for `UInt8`, but useful
as a sanity-check lemma and for bridging to `Aeneas.Std.U8`). -/
theorem bitsToBytes_val_lt {l : ℕ} (b : Fin (8 * l) → Fin 2) (i : Fin l) :
    (bitsToBytes b i).toNat < 256 :=
  UInt8.toNat_lt (bitsToBytes b i)

/-- `bitsToBytes` applied to the all-zero bit string yields the all-zero byte string. -/
theorem bitsToBytes_zero (l : ℕ) :
    bitsToBytes (fun (_ : Fin (8 * l)) => (0 : Fin 2)) = fun _ => (0 : UInt8) := by
  funext i
  simp only [bitsToBytes, packByte, packBitsAux]
  rfl

/-- `bitsToBytes` applied to the all-one bit string yields the byte `0xFF` everywhere. -/
theorem bitsToBytes_ones (l : ℕ) :
    bitsToBytes (fun (_ : Fin (8 * l)) => (1 : Fin 2)) = fun _ => (255 : UInt8) := by
  funext i
  simp only [bitsToBytes, packByte, packBitsAux, Fin.val_one]
  rfl

end Fips203
