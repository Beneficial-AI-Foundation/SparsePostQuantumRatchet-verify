/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module
public import Spqr.Crypto.Fips203.Conversion.BitsToBytes
public import Spqr.Crypto.Fips203.Conversion.BytesToBits
public import Mathlib.Tactic.Ring
import all Batteries.Data.UInt
/-!
# Round-trip lemmas for `BitsToBytes` / `BytesToBits`

NIST FIPS 203 (ML-KEM, August 2024), § 4.2.1, defines `BitsToBytes` (Algorithm 1) and
`BytesToBits` (Algorithm 2) as mutual inverses.  This file formally verifies both round-trip
identities:

  1. `bytesToBits ∘ bitsToBytes = id`  — encode then decode bits
  2. `bitsToBytes ∘ bytesToBits = id`  — decode then encode bytes

The core technical lemma is `extractBit_packByte`: extracting the `j`-th bit from the
byte produced by `packByte bits` recovers `bits j`.  Both round-trip theorems follow
from this by extensionality.

**Source**: NIST FIPS 203, § 4.2.1, Algorithms 1 & 2
-/

@[expose] public section

namespace Fips203

/-! ## Core inversion lemma -/


/-- **Core inversion lemma**: extracting bit `j` from `packByte bits` recovers `bits j`.

  `extractBit (packByte bits) j = bits j`

**Source**: NIST FIPS 203, § 4.2.1 -/
private theorem extractBit_packByte_aux (bits : Fin 8 → Fin 2) (j : Fin 8) :
    (extractBit (packByte bits) j).val = (bits j).val := by
  unfold extractBit packByte
  have h0 := (bits ⟨0, by omega⟩).isLt
  have h1 := (bits ⟨1, by omega⟩).isLt
  have h2 := (bits ⟨2, by omega⟩).isLt
  have h3 := (bits ⟨3, by omega⟩).isLt
  have h4 := (bits ⟨4, by omega⟩).isLt
  have h5 := (bits ⟨5, by omega⟩).isLt
  have h6 := (bits ⟨6, by omega⟩).isLt
  have h7 := (bits ⟨7, by omega⟩).isLt
  simp only [packBitsAux]
  fin_cases j <;> simp <;> omega

/-- **Core inversion lemma**: extracting bit `j` from `packByte bits` recovers `bits j`.

  `extractBit (packByte bits) j = bits j`

**Source**: NIST FIPS 203, § 4.2.1 -/
theorem extractBit_packByte (bits : Fin 8 → Fin 2) (j : Fin 8) :
    extractBit (packByte bits) j = bits j :=
  Fin.ext (extractBit_packByte_aux bits j)

/-- Packing the bits extracted from a byte recovers the original byte.

  `packByte (extractBit B) = B` -/
private theorem packByte_extractBit_aux (B : UInt8) :
    (packByte (extractBit B)).toNat = B.toNat := by
  rw [packByte_eq_sum, ← extractBit_sum B]
  simp

/-- Packing the bits extracted from a byte recovers the original byte.

  `packByte (extractBit B) = B` -/
theorem packByte_extractBit (B : UInt8) :
    packByte (extractBit B) = B := by
  have h := packByte_extractBit_aux B
  ext; exact h

/-! ## Round-trip theorems -/

/-- **Round-trip 1** — `bytesToBits ∘ bitsToBytes = id`:

Encoding a bit array into bytes and decoding back recovers the original bit array.

  `∀ b : Fin (8 * l) → Fin 2, bytesToBits (bitsToBytes b) = b`

**Source**: NIST FIPS 203, § 4.2.1 -/
theorem bytesToBits_bitsToBytes {l : ℕ} (b : Fin (8 * l) → Fin 2) :
    bytesToBits (bitsToBytes b) = b := by
  funext idx
  simp only [bytesToBits, bitsToBytes]
  rw [extractBit_packByte]
  congr 1; ext; simp; omega

/-- **Round-trip 2** — `bitsToBytes ∘ bytesToBits = id`:

Decoding a byte array into bits and encoding back recovers the original byte array.

  `∀ B : Fin l → UInt8, bitsToBytes (bytesToBits B) = B`

**Source**: NIST FIPS 203, § 4.2.1 -/
theorem bitsToBytes_bytesToBits {l : ℕ} (B : Fin l → UInt8) :
    bitsToBytes (bytesToBits B) = B := by
  funext i
  simp only [bitsToBytes, bytesToBits]
  have : (fun (j : Fin 8) => extractBit (B ⟨(8 * ↑i + ↑j) / 8, by omega⟩)
    ⟨(8 * ↑i + ↑j) % 8, Nat.mod_lt _ (by omega)⟩) = (fun (j : Fin 8) => extractBit (B i) j) := by
    funext j
    have hj := j.isLt
    have h_div : (8 * i.val + j.val) / 8 = i.val := by omega
    have h_mod : (8 * i.val + j.val) % 8 = j.val := by omega
    simp only [h_div, h_mod]
  rw [this]
  exact packByte_extractBit (B i)

/-- `BitsToBytes` and `BytesToBits` form an equivalence between bit arrays of length
`8 * l` and byte arrays of length `l`. -/
def bitsBytesEquiv (l : ℕ) : (Fin (8 * l) → Fin 2) ≃ (Fin l → UInt8) where
  toFun := bitsToBytes
  invFun := bytesToBits
  left_inv := bytesToBits_bitsToBytes
  right_inv := bitsToBytes_bytesToBits

end Fips203
