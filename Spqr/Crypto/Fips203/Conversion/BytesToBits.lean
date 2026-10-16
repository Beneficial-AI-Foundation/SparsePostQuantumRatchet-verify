/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module
public import Spqr.Crypto.Fips203.Params
public import Spqr.Crypto.Fips203.Conversion.BitsToBytes
public import Mathlib.Tactic.Ring
/-!
# FIPS 203 Algorithm 2: `BytesToBits`

NIST FIPS 203 (ML-KEM, August 2024), § 4.2.1, defines `BytesToBits` as the conversion from a
byte array of length `ℓ` to a bit array of length `8·ℓ`.  Each byte is unpacked into eight
consecutive bits in little-endian order:

  `b[8·i + j] = ⌊B[i] / 2^j⌋ mod 2`     for `0 ≤ i < ℓ`, `0 ≤ j < 8`

This is the fundamental deserialisation primitive upon which `ByteDecode_d` (Algorithm 4) is
built.  It is the inverse of `BitsToBytes` (Algorithm 1).

**Source**: NIST FIPS 203, § 4.2.1, Algorithm 2
-/

@[expose] public section

namespace Fips203

/-! ## Byte-to-bit unpacking -/

/-- Helper: extract the `j`-th bit (little-endian) of a `UInt8` as a `Fin 2`.

`extractBit B j = ⌊B / 2^j⌋ mod 2`, which is bit `j` of the byte `B`. -/
def extractBit (B : UInt8) (j : Fin 8) : Fin 2 :=
  ⟨(B.toNat / 2 ^ (j : ℕ)) % 2, Nat.mod_lt _ (by omega)⟩

/-- **Algorithm 2 — `BytesToBits`** (FIPS 203, § 4.2.1).

Converts a byte array `B` of length `l` into a bit array of length `8 * l`.

Each output bit `b[8·i + j]` is the `j`-th bit (little-endian) of byte `B[i]`:

  `b[8·i + j] = ⌊B[i] / 2^j⌋ mod 2`

The definition mirrors the FIPS 203 pseudocode:

```
BytesToBits(B):
  for (i ← 0; i < len(B); i++)
    for (j ← 0; j < 8; j++)
      b[8i + j] ← B[i] mod 2
      B[i] ← ⌊B[i] / 2⌋
  return b
```
-/
def bytesToBits {l : ℕ} (B : Fin l → UInt8) : Fin (8 * l) → Fin 2 :=
  fun idx =>
    let i : Fin l := ⟨(idx : ℕ) / 8, by omega⟩
    let j : Fin 8 := ⟨(idx : ℕ) % 8, Nat.mod_lt _ (by omega)⟩
    extractBit (B i) j

/-! ## Elementary properties -/

/-- `extractBit` always returns a value in `{0, 1}`. -/
theorem extractBit_val_lt (B : UInt8) (j : Fin 8) :
    (extractBit B j).val < 2 :=
  (extractBit B j).isLt

/-- Extracting bit `j` from byte `0` yields `0`. -/
theorem extractBit_zero (j : Fin 8) : extractBit 0 j = 0 := by
  simp [extractBit]

/-- Extracting bit `j` from byte `255` yields `1`. -/
theorem extractBit_ff (j : Fin 8) : extractBit 255 j = 1 := by
  simp only [extractBit, UInt8.toNat_ofNat]
  fin_cases j <;> simp (config := { decide := true })

/-- `bytesToBits` applied to the all-zero byte string yields the all-zero bit string. -/
theorem bytesToBits_zero (l : ℕ) :
    bytesToBits (fun (_ : Fin l) => (0 : UInt8)) = fun _ => (0 : Fin 2) := by
  funext idx
  simp only [bytesToBits, extractBit]
  simp

/-- `bytesToBits` applied to the all-`0xFF` byte string yields the all-one bit string. -/
theorem bytesToBits_ones (l : ℕ) :
    bytesToBits (fun (_ : Fin l) => (255 : UInt8)) = fun _ => (1 : Fin 2) := by
  funext idx
  simp only [bytesToBits]
  exact extractBit_ff _

/-! ## Correspondence with `Finset.sum` -/

/-- `extractBit` agrees with the `Finset.sum` characterisation of bit decomposition:

  `B.toNat = ∑_{j=0}^{7} (extractBit B j).val * 2^j`

for any `B : UInt8`.  This witnesses that `extractBit` faithfully decomposes a byte into
its binary digits. -/
theorem extractBit_sum (B : UInt8) :
    B.toNat = Finset.univ.sum (fun (j : Fin 8) => (extractBit B j).val * 2 ^ (j : ℕ)) := by
  simp only [extractBit, Finset.sum_fin_eq_sum_range, Finset.sum_range_succ,
    Finset.sum_range_zero]
  simp (config := { decide := true })
  have hB := UInt8.toNat_lt B
  omega

end Fips203
