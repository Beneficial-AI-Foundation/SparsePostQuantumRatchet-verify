/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Crypto.Fips203.PKE.KeyGen
/-!
# FIPS 203 Algorithm 16: `ML-KEM.KeyGen_internal(d, z)`

NIST FIPS 203 (ML-KEM, August 2024), § 6.1, defines the internal KEM key generation
algorithm.  Given two 32-byte seeds `d` (for `K-PKE.KeyGen`) and `z` (for implicit
rejection), it produces an encapsulation key `ek` and a decapsulation key `dk`.

The algorithm:

1. `(ekPKE, dkPKE) ← K-PKE.KeyGen(d)`.
2. `ek ← ekPKE`.
3. `dk ← dkPKE ‖ ek ‖ H(ek) ‖ z`.

The decapsulation key therefore has `384·k + (384·k + 32) + 32 + 32 = 768·k + 96` bytes,
which is `ParamSet.dkSize`.  This file also provides the four field projections of `dk`
(`decodeDkPke`, `decodeDkEk`, `decodeDkH`, `decodeDkZ`) used by `ML-KEM.Decaps`, and proves
that they invert the concatenation.

`ML-KEM.KeyGen` (Algorithm 19) is `KeyGen_internal` applied to fresh random `d, z`; since
randomness is a parameter in this development, Algorithm 16 is the top-level definition.

**Source**: NIST FIPS 203, § 6.1 (Algorithm 16)
-/

noncomputable section

namespace Fips203

/-! ## Hash function `H` (axiomatised)

`H` is SHA3-256 producing 32 bytes.  Axiomatised as an opaque oracle like `hashG`. -/

/-- `H(input)` — SHA3-256 hash producing 32 bytes. -/
opaque hashH (input : List UInt8) : Fin 32 → UInt8

/-- `H(ek)`: hash of the encapsulation key, stored in `dk` and re-used by `Encaps`. -/
def hashEk {N : ℕ} (ek : Fin N → UInt8) : Fin 32 → UInt8 :=
  hashH (List.ofFn ek)

/-! ## Decapsulation-key layout

`dk = dkPKE ‖ ek ‖ H(ek) ‖ z`, with byte offsets

| field   | offset        | length        |
|---------|---------------|---------------|
| `dkPKE` | `0`           | `384·k`       |
| `ek`    | `384·k`       | `384·k + 32`  |
| `H(ek)` | `768·k + 32`  | `32`          |
| `z`     | `768·k + 64`  | `32`          | -/

/-- Concatenate the four fields of the decapsulation key. -/
def encodeMlkemDk {p : ParamSet} (dkPke : Fin (384 * p.k) → UInt8)
    (ek : Fin (384 * p.k + 32) → UInt8) (h z : Fin 32 → UInt8) :
    Fin p.dkSize → UInt8 :=
  fun idx =>
    if h1 : idx.val < 384 * p.k then dkPke ⟨idx.val, h1⟩
    else if h2 : idx.val < 768 * p.k + 32 then ek ⟨idx.val - 384 * p.k, by omega⟩
    else if h3 : idx.val < 768 * p.k + 64 then h ⟨idx.val - (768 * p.k + 32), by omega⟩
    else z ⟨idx.val - (768 * p.k + 64), by
      have := idx.isLt; unfold ParamSet.dkSize at this; omega⟩

/-- Field `dkPKE = dk[0 : 384·k]`. -/
def decodeDkPke {p : ParamSet} (dk : Fin p.dkSize → UInt8) : Fin (384 * p.k) → UInt8 :=
  fun i => dk ⟨i.val, by have := i.isLt; unfold ParamSet.dkSize; omega⟩

/-- Field `ekPKE = dk[384·k : 768·k + 32]`. -/
def decodeDkEk {p : ParamSet} (dk : Fin p.dkSize → UInt8) : Fin (384 * p.k + 32) → UInt8 :=
  fun i => dk ⟨384 * p.k + i.val, by have := i.isLt; unfold ParamSet.dkSize; omega⟩

/-- Field `h = H(ek) = dk[768·k + 32 : 768·k + 64]`. -/
def decodeDkH {p : ParamSet} (dk : Fin p.dkSize → UInt8) : Fin 32 → UInt8 :=
  fun i => dk ⟨768 * p.k + 32 + i.val, by have := i.isLt; unfold ParamSet.dkSize; omega⟩

/-- Field `z = dk[768·k + 64 : 768·k + 96]`. -/
def decodeDkZ {p : ParamSet} (dk : Fin p.dkSize → UInt8) : Fin 32 → UInt8 :=
  fun i => dk ⟨768 * p.k + 64 + i.val, by have := i.isLt; unfold ParamSet.dkSize; omega⟩

/-! ## Layout round-trips -/

/-- `decodeDkPke` inverts `encodeMlkemDk`. -/
theorem decodeDkPke_encodeMlkemDk {p : ParamSet} (dkPke : Fin (384 * p.k) → UInt8)
    (ek : Fin (384 * p.k + 32) → UInt8) (h z : Fin 32 → UInt8) :
    decodeDkPke (encodeMlkemDk dkPke ek h z) = dkPke := by
  funext i
  unfold decodeDkPke encodeMlkemDk
  rw [dif_pos i.isLt]

/-- `decodeDkEk` inverts `encodeMlkemDk`. -/
theorem decodeDkEk_encodeMlkemDk {p : ParamSet} (dkPke : Fin (384 * p.k) → UInt8)
    (ek : Fin (384 * p.k + 32) → UInt8) (h z : Fin 32 → UInt8) :
    decodeDkEk (encodeMlkemDk dkPke ek h z) = ek := by
  funext i
  have hi := i.isLt
  unfold decodeDkEk encodeMlkemDk
  rw [dif_neg (by change ¬ (384 * p.k + i.val < 384 * p.k); omega),
    dif_pos (by change 384 * p.k + i.val < 768 * p.k + 32; omega)]
  congr 1
  exact Fin.ext (by change 384 * p.k + i.val - 384 * p.k = i.val; omega)

/-- `decodeDkH` inverts `encodeMlkemDk`. -/
theorem decodeDkH_encodeMlkemDk {p : ParamSet} (dkPke : Fin (384 * p.k) → UInt8)
    (ek : Fin (384 * p.k + 32) → UInt8) (h z : Fin 32 → UInt8) :
    decodeDkH (encodeMlkemDk dkPke ek h z) = h := by
  funext i
  have hi := i.isLt
  unfold decodeDkH encodeMlkemDk
  rw [dif_neg (by change ¬ (768 * p.k + 32 + i.val < 384 * p.k); omega),
    dif_neg (by change ¬ (768 * p.k + 32 + i.val < 768 * p.k + 32); omega),
    dif_pos (by change 768 * p.k + 32 + i.val < 768 * p.k + 64; omega)]
  congr 1
  exact Fin.ext (by change 768 * p.k + 32 + i.val - (768 * p.k + 32) = i.val; omega)

/-- `decodeDkZ` inverts `encodeMlkemDk`. -/
theorem decodeDkZ_encodeMlkemDk {p : ParamSet} (dkPke : Fin (384 * p.k) → UInt8)
    (ek : Fin (384 * p.k + 32) → UInt8) (h z : Fin 32 → UInt8) :
    decodeDkZ (encodeMlkemDk dkPke ek h z) = z := by
  funext i
  have hi := i.isLt
  unfold decodeDkZ encodeMlkemDk
  rw [dif_neg (by change ¬ (768 * p.k + 64 + i.val < 384 * p.k); omega),
    dif_neg (by change ¬ (768 * p.k + 64 + i.val < 768 * p.k + 32); omega),
    dif_neg (by change ¬ (768 * p.k + 64 + i.val < 768 * p.k + 64); omega)]
  congr 1
  exact Fin.ext (by change 768 * p.k + 64 + i.val - (768 * p.k + 64) = i.val; omega)

/-! ## ML-KEM.KeyGen_internal — top-level definition -/

/-- The output of `ML-KEM.KeyGen_internal`: an encapsulation key and a decapsulation key. -/
structure MlkemKeyPair (p : ParamSet) where
  /-- Encapsulation key `ek = ekPKE` of size `384 · k + 32` bytes. -/
  ek : Fin (384 * p.k + 32) → UInt8
  /-- Decapsulation key `dk = dkPKE ‖ ek ‖ H(ek) ‖ z` of size `768 · k + 96` bytes. -/
  dk : Fin p.dkSize → UInt8

/-- **Algorithm 16 — `ML-KEM.KeyGen_internal(d, z)`** (FIPS 203, § 6.1).

Given the 32-byte seed `d` for `K-PKE.KeyGen` and the 32-byte implicit-rejection seed `z`,
produces the encapsulation key `ek` and the decapsulation key `dk`. -/
def mlkemKeyGen (d z : Fin 32 → UInt8) (p : ParamSet) : MlkemKeyPair p :=
  let kp := kpkeKeyGen d p
  { ek := kp.ek
    dk := encodeMlkemDk kp.dk kp.ek (hashEk kp.ek) z }

/-! ## Elementary properties -/

/-- The encapsulation key is exactly `ekPKE`. -/
theorem mlkemKeyGen_ek (d z : Fin 32 → UInt8) (p : ParamSet) :
    (mlkemKeyGen d z p).ek = (kpkeKeyGen d p).ek := rfl

/-- The decapsulation key is `dkPKE ‖ ekPKE ‖ H(ekPKE) ‖ z`. -/
theorem mlkemKeyGen_dk (d z : Fin 32 → UInt8) (p : ParamSet) :
    (mlkemKeyGen d z p).dk =
      encodeMlkemDk (kpkeKeyGen d p).dk (kpkeKeyGen d p).ek
        (hashEk (kpkeKeyGen d p).ek) z := rfl

/-- `dk[0 : 384·k]` of a generated key is `dkPKE`. -/
theorem decodeDkPke_mlkemKeyGen (d z : Fin 32 → UInt8) (p : ParamSet) :
    decodeDkPke (mlkemKeyGen d z p).dk = (kpkeKeyGen d p).dk := by
  rw [mlkemKeyGen_dk, decodeDkPke_encodeMlkemDk]

/-- `dk[384·k : 768·k + 32]` of a generated key is `ek`. -/
theorem decodeDkEk_mlkemKeyGen (d z : Fin 32 → UInt8) (p : ParamSet) :
    decodeDkEk (mlkemKeyGen d z p).dk = (mlkemKeyGen d z p).ek := by
  rw [mlkemKeyGen_dk, decodeDkEk_encodeMlkemDk, mlkemKeyGen_ek]

/-- `dk[768·k + 32 : 768·k + 64]` of a generated key is `H(ek)`. -/
theorem decodeDkH_mlkemKeyGen (d z : Fin 32 → UInt8) (p : ParamSet) :
    decodeDkH (mlkemKeyGen d z p).dk = hashEk (mlkemKeyGen d z p).ek := by
  rw [mlkemKeyGen_dk, decodeDkH_encodeMlkemDk, mlkemKeyGen_ek]

/-- `dk[768·k + 64 : 768·k + 96]` of a generated key is `z`. -/
theorem decodeDkZ_mlkemKeyGen (d z : Fin 32 → UInt8) (p : ParamSet) :
    decodeDkZ (mlkemKeyGen d z p).dk = z := by
  rw [mlkemKeyGen_dk, decodeDkZ_encodeMlkemDk]

/-- For ML-KEM-768, `ek` has `1184` bytes and `dk` has `2400` bytes. -/
theorem mlkemKeyGen_sizes_768 :
    384 * mlkem768.k + 32 = 1184 ∧ mlkem768.dkSize = 2400 := by
  simp only [mlkem768_k, mlkem768_dkSize, and_self]

end Fips203
