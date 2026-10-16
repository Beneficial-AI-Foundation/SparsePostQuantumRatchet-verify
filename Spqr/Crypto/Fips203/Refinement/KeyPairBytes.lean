/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module
public import Aeneas
public import Spqr.Auxiliary.Aeneas.Scalar
public import Spqr.Crypto.Fips203.KEM.KeyGen
/-!
# FIPS 203 model of libcrux's `KeyPairCompressedBytes::from_seed`

libcrux-ml-kem 0.0.7 (`src/mlkem.rs`, `KeyPairCompressedBytes::from_seed`) runs ML-KEM-768 key
generation on a 64-byte seed and serialises the whole key pair into one 2400-byte buffer with
(`src/ind_cca/incremental/types.rs`, `KeyPair::to_bytes_compressed`):

```
value = ByteEncode₁₂(ŝ) ‖ ByteEncode₁₂(t̂) ‖ ρ ‖ H(ek) ‖ z
        [0 : 1152]       [1152 : 2304]     [2304 : 2336] [2336 : 2368] [2368 : 2400]
```

where (`src/ind_cca.rs`, `generate_keypair`) the seed is split as `d = seed[0 : 32]` and
`z = seed[32 : 64]`.  Since `ek = ByteEncode₁₂(t̂) ‖ ρ`, this buffer is byte-for-byte the FIPS 203
decapsulation key `dk = dkPKE ‖ ek ‖ H(ek) ‖ z` of `ML-KEM.KeyGen_internal(d, z)` (Algorithm 16,
`Fips203.mlkemKeyGen`).  The accessors `pk2 = value[1152 : 2304]` (the serialised `t̂`) and
`pk1 = value[2304 : 2368]` (`ρ ‖ H(ek)`) are sub-ranges of that buffer.

This file states that model over Aeneas byte lists, so that `SrcTranslated/FunsExternal.lean` can
use it as the definition of the external `from_seed`, and proves the layout facts about it.  It
deliberately does **not** import `SrcTranslated` (it is imported *by* it).

**Sources**: NIST FIPS 203, § 6.1 (Algorithm 16); libcrux-ml-kem 0.0.7, `src/mlkem.rs`
lines 240–246 and `src/ind_cca/incremental/types.rs` lines 415–433.
-/

@[expose] public section

noncomputable section

open Aeneas Aeneas.Std

namespace Fips203.Refinement

/-! ## Seed split

libcrux's `KEY_GENERATION_SEED_SIZE = 64`; the first half is the K-PKE seed `d`, the second the
implicit-rejection value `z`. -/

/-- `d = seed[0 : 32]`. -/
def seedD (seed : Fin 64 → UInt8) : Fin 32 → UInt8 :=
  fun i => seed ⟨i.val, by omega⟩

/-- `z = seed[32 : 64]`. -/
def seedZ (seed : Fin 64 → UInt8) : Fin 32 → UInt8 :=
  fun i => seed ⟨32 + i.val, by omega⟩

/-- Read a 64-byte Aeneas array as a `Fin 64 → UInt8` seed. -/
def seedOfArray (seed : Array U8 64#usize) : Fin 64 → UInt8 :=
  fun i => (seed.val[i.val]'(by rw [Aeneas.Std.Array.length_eq]; exact i.isLt)).toUInt8

/-! ## Byte-vector ↔ Aeneas list -/

/-- A `Fin N → UInt8` byte vector as a list of Aeneas bytes. -/
def toU8List {N : ℕ} (b : Fin N → UInt8) : List U8 :=
  List.ofFn (fun i => U8.ofUInt8 (b i))

@[simp]
theorem toU8List_length {N : ℕ} (b : Fin N → UInt8) : (toU8List b).length = N := by
  simp only [toU8List, List.length_ofFn]

theorem toU8List_getElem {N : ℕ} (b : Fin N → UInt8) (i : ℕ) (h : i < (toU8List b).length) :
    (toU8List b)[i] = U8.ofUInt8 (b ⟨i, by simpa using h⟩) := by
  simp only [toU8List, List.getElem_ofFn]

/-! ## The FIPS 203 model of `from_seed` -/

/-- The 2400-byte `KeyPairCompressedBytes::value` produced by `from_seed(seed)`, as the
FIPS 203 decapsulation key `dk = dkPKE ‖ ek ‖ H(ek) ‖ z` of `ML-KEM.KeyGen_internal(d, z)` for
`d = seed[0 : 32]`, `z = seed[32 : 64]`. -/
def keyPairBytes (seed : Fin 64 → UInt8) : Fin mlkem768.dkSize → UInt8 :=
  (mlkemKeyGen (seedD seed) (seedZ seed) mlkem768).dk

/-- `keyPairBytes` as an Aeneas list. -/
def keyPairList (seed : Fin 64 → UInt8) : List U8 :=
  toU8List (keyPairBytes seed)

theorem keyPairList_length (seed : Fin 64 → UInt8) : (keyPairList seed).length = 2400 := by
  simp only [keyPairList, toU8List_length, mlkem768_dkSize]

/-- The buffer as an Aeneas `Array U8 2400`. -/
def keyPairArray (seed : Fin 64 → UInt8) : Array U8 2400#usize :=
  Aeneas.Std.Array.make 2400#usize (keyPairList seed) (keyPairList_length seed)

/-- The underlying list of `keyPairArray` is `keyPairList`. -/
@[simp] theorem keyPairArray_val (seed : Fin 64 → UInt8) :
    (keyPairArray seed).val = keyPairList seed :=
  Aeneas.Std.Array.make_val _ _ _

/-! ## The public projections

libcrux `pk2 = value[1152 : 2304]` is `ByteEncode₁₂(t̂)`, the encapsulation key without `ρ`;
`pk1 = value[2304 : 2368]` is `ρ ‖ H(ek)`. -/

/-- The 1184-byte FIPS 203 encapsulation key `ek = ByteEncode₁₂(t̂) ‖ ρ`. -/
def ekBytes (seed : Fin 64 → UInt8) : Fin (384 * mlkem768.k + 32) → UInt8 :=
  (mlkemKeyGen (seedD seed) (seedZ seed) mlkem768).ek

/-- libcrux `pk2`: the first `1152` bytes of `ek`, i.e. the serialised `t̂`. -/
def pk2Bytes (seed : Fin 64 → UInt8) : Fin 1152 → UInt8 :=
  fun i => ekBytes seed ⟨i.val, by have := i.isLt; simp only [mlkem768_k]; omega⟩

/-- libcrux `pk1 = ρ ‖ H(ek)`: the last `32` bytes of `ek` followed by `H(ek)`. -/
def pk1Bytes (seed : Fin 64 → UInt8) : Fin 64 → UInt8 :=
  fun i =>
    if h : i.val < 32 then ekBytes seed ⟨1152 + i.val, by simp only [mlkem768_k]; omega⟩
    else hashEk (ekBytes seed) ⟨i.val - 32, by omega⟩

/-! ## Layout lemmas

Each byte of `keyPairBytes` is one of the four fields, by `encodeMlkemDk`. -/

/-- `value[i] = dkPKE[i]` for `i < 1152`. -/
theorem keyPairBytes_dkPke (seed : Fin 64 → UInt8) (i : ℕ) (hi : i < 1152)
    (h : i < mlkem768.dkSize) :
    keyPairBytes seed ⟨i, h⟩ =
      (kpkeKeyGen (seedD seed) mlkem768).dk ⟨i, by simp only [mlkem768_k]; omega⟩ := by
  simp only [keyPairBytes, mlkemKeyGen_dk, encodeMlkemDk, mlkem768_k]
  rw [dif_pos (by omega)]

/-- `value[1152 + i] = ek[i]` for `i < 1184`. -/
theorem keyPairBytes_ek (seed : Fin 64 → UInt8) (i : ℕ) (hi : i < 1184)
    (h : 1152 + i < mlkem768.dkSize) :
    keyPairBytes seed ⟨1152 + i, h⟩ =
      ekBytes seed ⟨i, by simp only [mlkem768_k]; omega⟩ := by
  simp only [keyPairBytes, ekBytes, mlkemKeyGen_dk, mlkemKeyGen_ek, encodeMlkemDk, mlkem768_k]
  rw [dif_neg (by omega), dif_pos (by omega)]
  exact congrArg _ (Fin.ext (by simp only; omega))

/-- `value[2336 + i] = H(ek)[i]` for `i < 32`. -/
theorem keyPairBytes_hash (seed : Fin 64 → UInt8) (i : ℕ) (hi : i < 32)
    (h : 2336 + i < mlkem768.dkSize) :
    keyPairBytes seed ⟨2336 + i, h⟩ = hashEk (ekBytes seed) ⟨i, hi⟩ := by
  simp only [keyPairBytes, ekBytes, mlkemKeyGen_dk, mlkemKeyGen_ek, encodeMlkemDk, mlkem768_k]
  rw [dif_neg (by omega), dif_neg (by omega), dif_pos (by omega)]
  exact congrArg _ (Fin.ext (by simp only; omega))

/-- `value[2368 + i] = z[i]` for `i < 32`. -/
theorem keyPairBytes_z (seed : Fin 64 → UInt8) (i : ℕ) (hi : i < 32)
    (h : 2368 + i < mlkem768.dkSize) :
    keyPairBytes seed ⟨2368 + i, h⟩ = seedZ seed ⟨i, hi⟩ := by
  simp only [keyPairBytes, mlkemKeyGen_dk, encodeMlkemDk, mlkem768_k]
  rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega)]
  exact congrArg _ (Fin.ext (by simp only; omega))

/-! ## Slice facts used by the external `pk1`/`pk2`/`sk` specs -/

/-- `value[1152 : 2304]` is libcrux `pk2`, the serialised `t̂`. -/
theorem keyPairList_slice_pk2 (seed : Fin 64 → UInt8) :
    (keyPairList seed).slice 1152 2304 = toU8List (pk2Bytes seed) := by
  have hlen := keyPairList_length seed
  apply List.ext_getElem
  · simp only [List.slice_length, hlen, toU8List_length]; omega
  intro i h₁ h₂
  simp only [List.slice_length, hlen] at h₁
  rw [List.getElem_slice _ _ _ _ ⟨by omega, by omega⟩]
  simp only [keyPairList, toU8List_getElem, pk2Bytes]
  exact congrArg U8.ofUInt8 (keyPairBytes_ek seed i (by omega) _)

/-- `value[2304 : 2368]` is libcrux `pk1 = ρ ‖ H(ek)`. -/
theorem keyPairList_slice_pk1 (seed : Fin 64 → UInt8) :
    (keyPairList seed).slice 2304 2368 = toU8List (pk1Bytes seed) := by
  have hlen := keyPairList_length seed
  apply List.ext_getElem
  · simp only [List.slice_length, hlen, toU8List_length]; omega
  intro i h₁ h₂
  simp only [List.slice_length, hlen] at h₁
  rw [List.getElem_slice _ _ _ _ ⟨by omega, by omega⟩]
  simp only [keyPairList, toU8List_getElem, pk1Bytes]
  apply congrArg U8.ofUInt8
  by_cases hi : i < 32
  · rw [dif_pos hi]
    have : 2304 + i = 1152 + (1152 + i) := by omega
    simp only [this]
    exact keyPairBytes_ek seed (1152 + i) (by omega) _
  · rw [dif_neg hi]
    have : 2304 + i = 2336 + (i - 32) := by omega
    simp only [this]
    exact keyPairBytes_hash seed (i - 32) (by omega) _

end Fips203.Refinement
