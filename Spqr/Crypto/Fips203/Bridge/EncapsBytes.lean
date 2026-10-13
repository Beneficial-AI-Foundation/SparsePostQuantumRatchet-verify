/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Aeneas
import Spqr.Auxiliary.Aeneas.Array
import Spqr.Auxiliary.Aeneas.Scalar
import Spqr.Crypto.Fips203.KEM.EncapsIncremental
import Spqr.Crypto.Fips203.Bridge.KeyPairBytes
/-!
# FIPS 203 model of libcrux's incremental `encapsulate1`

libcrux-ml-kem 0.0.7 (`src/mlkem.rs`, `mlkem768::incremental::encapsulate1`) is
`encapsulate1(pk1, randomness, state, shared_secret)`:

1. `PublicKey1::try_from(pk1)`: fails with `InvalidInputLength` if `pk1.len() < 64`; otherwise
   `ρ = pk1[0 : 32]`, `h = pk1[32 : 64]` (`src/ind_cca/incremental/types.rs`).
2. `encapsulate1_serialized`: fails with `InvalidOutputLength` if `shared_secret.len() < 32`;
   runs round 1 of `ML-KEM.Encaps_internal` (`Fips203.mlkemEncapsPhase1`), then
   `EncapsState::to_bytes` fails with `InvalidOutputLength` if `state.len() < 2080`.
3. On success, `state[0 : 2080] := ŷ ‖ e₂ ‖ m` and `shared_secret[0 : 32] := K`; the rest of both
   buffers is untouched, and `Ok(Ciphertext1 { value := c₁ })` is returned.

The state layout (`EncapsState::to_bytes`, `src/ind_cca/incremental/types.rs`, and
`PolynomialRingElement::to_bytes`, `src/polynomial.rs`): each of the `3 + 1` polynomials is
`256` coefficients × `2` bytes, each coefficient stored as a little-endian `i16`; then the 32 raw
message bytes:

```
state = ŷ[0] ‖ ŷ[1] ‖ ŷ[2] ‖ e₂ ‖ m
        [0:512] [512:1024] [1024:1536] [1536:2048] [2048:2080]
```

**Modelling note (coefficient representatives).**  libcrux stores *a* signed 16-bit
representative of each coefficient (the portable backend keeps values in `[0, q)` after the NTT;
the AVX2 backend may additionally byte-swap, see libcrux issue 1275 and SPQR's
`potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275`).  The model stores the
canonical representative in `[0, q)`.  Every consumer of the state (`encapsulate2`,
`EncapsState::try_from_bytes`) reads coefficients modulo `q`, so the model and libcrux agree on
everything that is observable downstream; this is made precise by `decodeEncapsState_stateBytes`.

This file deliberately does **not** import `SrcTranslated` (it is imported *by* it).

**Sources**: NIST FIPS 203, § 6.2 (Algorithm 17); libcrux-ml-kem 0.0.7, `src/mlkem.rs` lines
344–367, `src/ind_cca/incremental.rs` lines 181–276, `src/ind_cca/incremental/types.rs` lines
76–90 and 186–244, `src/polynomial.rs` lines 100–135.
-/

noncomputable section

open Aeneas Aeneas.Std

namespace Fips203.Bridge

/-! ## Sizes -/

/-- libcrux `encaps_state_len()` for ML-KEM-768: `(3 + 1) · 512 + 32`. -/
def encapsStateSize : ℕ := 2080

/-- libcrux `Ciphertext1::len()` for ML-KEM-768: `32 · d_u · k`. -/
def ct1Size : ℕ := 960

/-- libcrux `SHARED_SECRET_SIZE`. -/
def sharedSecretSize : ℕ := 32

theorem ct1Size_eq : 32 * mlkem768.d_u * mlkem768.k = ct1Size := by
  simp only [mlkem768_d_u, mlkem768_k, ct1Size]

/-! ## Header parsing `pk1 = ρ ‖ H(ek)` -/

/-- `PublicKey1::try_from`: read `ρ = pk1[0 : 32]`, `h = pk1[32 : 64]` from a byte list of length
`≥ 64`. -/
def headerOfList (pk1 : List U8) (h : 64 ≤ pk1.length) : EncapsHeader :=
  { ρ := fun i => (pk1[i.val]'(by have := i.isLt; omega)).toUInt8
    h := fun i => (pk1[32 + i.val]'(by have := i.isLt; omega)).toUInt8 }

/-- The header read from the libcrux `pk1` buffer of a generated key pair is the FIPS 203
header `(ρ, H(ek))` of that key's `ek`. -/
theorem headerOfList_pk1Bytes (seed : Fin 64 → UInt8) (h : 64 ≤ (toU8List (pk1Bytes seed)).length) :
    headerOfList (toU8List (pk1Bytes seed)) h = headerOfEk (ekBytes seed) := by
  simp only [headerOfList, headerOfEk, toU8List_getElem, U8.toUInt8_ofUInt8, pk1Bytes]
  congr 1
  · funext i
    rw [dif_pos i.isLt]
    simp only [decodeEkRho, mlkem768_k]
  · funext i
    rw [dif_neg (by omega)]
    exact congrArg _ (Fin.ext (by simp only; omega))

/-! ## Coefficient serialisation: little-endian `i16` -/

/-- The low byte of the canonical representative of a coefficient. -/
def coeffLo (c : Zq) : UInt8 := UInt8.ofNat (c.val % 256)

/-- The high byte of the canonical representative of a coefficient. -/
def coeffHi (c : Zq) : UInt8 := UInt8.ofNat (c.val / 256)

/-- `PolynomialRingElement::to_bytes`: `512` bytes, coefficient `i` at `[2i, 2i + 1]`, little
endian. -/
def polyBytes (f : Fin n → Zq) : Fin 512 → UInt8 :=
  fun b =>
    let c := f ⟨b.val / 2, by have := b.isLt; change b.val / 2 < 256; omega⟩
    if b.val % 2 = 0 then coeffLo c else coeffHi c

/-- `PolynomialRingElement::from_bytes` on the model encoding: recover the coefficient. -/
def polyOfBytes (B : Fin 512 → UInt8) : Fin n → Zq :=
  fun i =>
    have hi : i.val < 256 := i.isLt
    Zq.ofNat ((B ⟨2 * i.val, by omega⟩).toNat + 256 * (B ⟨2 * i.val + 1, by omega⟩).toNat)

theorem coeffLo_toNat (c : Zq) : (coeffLo c).toNat = c.val % 256 := by
  simp only [coeffLo, UInt8.toNat_ofNat', Nat.reducePow, dvd_refl, Nat.mod_mod_of_dvd]

theorem coeffHi_toNat (c : Zq) : (coeffHi c).toNat = c.val / 256 := by
  have hc : c.val < 3329 := ZMod.val_lt c
  have : c.val / 256 < 256 := by omega
  simp only [coeffHi, UInt8.toNat_ofNat', Nat.reducePow]
  exact Nat.mod_eq_of_lt this

/-- Decoding inverts encoding on polynomials. -/
theorem polyOfBytes_polyBytes (f : Fin n → Zq) : polyOfBytes (polyBytes f) = f := by
  funext i
  have hi : i.val < 256 := i.isLt
  simp only [polyOfBytes, polyBytes]
  rw [if_pos (by omega), if_neg (by omega)]
  have h1 : (⟨2 * i.val / 2, by omega⟩ : Fin n) = i := Fin.ext (by simp only; omega)
  have h2 : (⟨(2 * i.val + 1) / 2, by omega⟩ : Fin n) = i := Fin.ext (by simp only; omega)
  rw [h1, h2, coeffLo_toNat, coeffHi_toNat, Nat.mod_add_div (f i).val]
  exact ZMod.natCast_zmod_val (f i)

/-! ## The 2080-byte state `ŷ[0] ‖ ŷ[1] ‖ ŷ[2] ‖ e₂ ‖ m` -/

/-- `EncapsState::to_bytes` for ML-KEM-768. -/
def stateBytes (st : EncapsState mlkem768) : Fin encapsStateSize → UInt8 :=
  fun idx =>
    if h1 : idx.val < 1536 then
      polyBytes (st.yHat ⟨idx.val / 512, by
        change idx.val / 512 < 3; omega⟩) ⟨idx.val % 512, Nat.mod_lt _ (by omega)⟩
    else if h2 : idx.val < 2048 then polyBytes st.e2 ⟨idx.val - 1536, by omega⟩
    else st.m ⟨idx.val - 2048, by have := idx.isLt; simp only [encapsStateSize] at this; omega⟩

/-- `EncapsState::try_from_bytes` for ML-KEM-768 (the model decoder). -/
def decodeEncapsState (B : Fin encapsStateSize → UInt8) : EncapsState mlkem768 :=
  { yHat := fun i => polyOfBytes (fun b => B ⟨512 * i.val + b.val, by
      have hi : i.val < 3 := i.isLt; have := b.isLt; simp only [encapsStateSize]; omega⟩)
    e2 := polyOfBytes (fun b => B ⟨1536 + b.val, by
      have := b.isLt; simp only [encapsStateSize]; omega⟩)
    m := fun i => B ⟨2048 + i.val, by have := i.isLt; simp only [encapsStateSize]; omega⟩ }

/-- `stateBytes` at `512·i + b` for `i < 3` reads `ŷ[i]`. -/
theorem stateBytes_yHat (st : EncapsState mlkem768) (i : Fin 3) (b : Fin 512)
    (h : 512 * i.val + b.val < encapsStateSize) :
    stateBytes st ⟨512 * i.val + b.val, h⟩ = polyBytes (st.yHat i) b := by
  have hi : i.val < 3 := i.isLt
  have hb := b.isLt
  simp only [stateBytes]
  rw [dif_pos (by omega)]
  have e1 : (⟨(512 * i.val + b.val) / 512, by change (512 * i.val + b.val) / 512 < 3; omega⟩ :
      Fin mlkem768.k) = i := Fin.ext (by simp only; omega)
  have e2 : (⟨(512 * i.val + b.val) % 512, Nat.mod_lt _ (by omega)⟩ : Fin 512) = b :=
    Fin.ext (by simp only; omega)
  rw [e1, e2]

/-- `stateBytes` at `1536 + b` reads `e₂`. -/
theorem stateBytes_e2 (st : EncapsState mlkem768) (b : Fin 512)
    (h : 1536 + b.val < encapsStateSize) :
    stateBytes st ⟨1536 + b.val, h⟩ = polyBytes st.e2 b := by
  have hb := b.isLt
  simp only [stateBytes]
  rw [dif_neg (by omega), dif_pos (by omega)]
  exact congrArg _ (Fin.ext (by simp only; omega))

/-- `stateBytes` at `2048 + i` reads `m`. -/
theorem stateBytes_m (st : EncapsState mlkem768) (i : Fin 32)
    (h : 2048 + i.val < encapsStateSize) :
    stateBytes st ⟨2048 + i.val, h⟩ = st.m i := by
  have hi := i.isLt
  simp only [stateBytes]
  rw [dif_neg (by omega), dif_neg (by omega)]
  exact congrArg _ (Fin.ext (by simp only; omega))

/-- **State round-trip.**  Decoding the serialised state recovers `(ŷ, e₂, m)`. -/
theorem decodeEncapsState_stateBytes (st : EncapsState mlkem768) :
    decodeEncapsState (stateBytes st) = st := by
  rcases st with ⟨yHat, e2, m⟩
  simp only [decodeEncapsState, EncapsState.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · funext i
    exact (congrArg polyOfBytes (funext fun b => stateBytes_yHat ⟨yHat, e2, m⟩ i b _)).trans
      (polyOfBytes_polyBytes (yHat i))
  · exact (congrArg polyOfBytes (funext fun b => stateBytes_e2 ⟨yHat, e2, m⟩ b _)).trans
      (polyOfBytes_polyBytes e2)
  · funext i
    exact stateBytes_m ⟨yHat, e2, m⟩ i _

/-! ## Writing into the `&mut [u8]` output buffers

`encapsulate1` writes `state[0 : 2080]` and `shared_secret[0 : 32]` and leaves the remaining
bytes of each slice unchanged (libcrux only requires `len ≥` the written size). -/

/-- Overwrite the first `N` bytes of `l` (of length `≥ N`) with `b`. -/
def overwritePrefix {N : ℕ} (l : List U8) (b : Fin N → UInt8) : List U8 :=
  toU8List b ++ l.drop N

theorem overwritePrefix_length {N : ℕ} (l : List U8) (b : Fin N → UInt8) (h : N ≤ l.length) :
    (overwritePrefix l b).length = l.length := by
  simp only [overwritePrefix, List.length_append, toU8List_length, List.length_drop]; omega

theorem overwritePrefix_getElem_lt {N : ℕ} (l : List U8) (b : Fin N → UInt8) (i : ℕ)
    (hi : i < N) (h : i < (overwritePrefix l b).length) :
    (overwritePrefix l b)[i] = U8.ofUInt8 (b ⟨i, hi⟩) := by
  simp only [overwritePrefix]
  rw [List.getElem_append_left (by simp only [toU8List_length]; exact hi)]
  exact toU8List_getElem b i _

theorem overwritePrefix_getElem_ge {N : ℕ} (l : List U8) (b : Fin N → UInt8) (i : ℕ)
    (hi : N ≤ i) (h : i < (overwritePrefix l b).length) (h' : i < l.length) :
    (overwritePrefix l b)[i] = l[i] := by
  simp only [overwritePrefix]
  rw [List.getElem_append_right (by simp only [toU8List_length]; exact hi)]
  simp only [toU8List_length, List.getElem_drop]
  congr 1
  omega

/-- The written prefix, as a list. -/
theorem overwritePrefix_take {N : ℕ} (l : List U8) (b : Fin N → UInt8) :
    (overwritePrefix l b).take N = toU8List b := by
  simp only [overwritePrefix]
  rw [List.take_append_of_le_length (by simp only [toU8List_length]; exact le_refl _)]
  exact List.take_of_length_le (by simp only [toU8List_length]; exact le_refl _)

/-! ## The FIPS 203 model of `encapsulate1` (ML-KEM-768) -/

/-- Round 1 of Algorithm 17 on the parsed header and the 32-byte message. -/
def encaps1Output (pk1 : List U8) (h : 64 ≤ pk1.length) (m : Fin 32 → UInt8) :
    EncapsPhase1Output mlkem768 :=
  mlkemEncapsPhase1 mlkem768 (headerOfList pk1 h) m

/-- The 960-byte first ciphertext half as a `Fin 960 → UInt8`. -/
def ct1Bytes (pk1 : List U8) (h : 64 ≤ pk1.length) (m : Fin 32 → UInt8) : Fin ct1Size → UInt8 :=
  fun i => (encaps1Output pk1 h m).ct1 ⟨i.val, by have := i.isLt; rw [ct1Size_eq]; exact this⟩

/-- The 960-byte first ciphertext half as an Aeneas list. -/
def ct1List (pk1 : List U8) (h : 64 ≤ pk1.length) (m : Fin 32 → UInt8) : List U8 :=
  toU8List (ct1Bytes pk1 h m)

theorem ct1List_length (pk1 : List U8) (h : 64 ≤ pk1.length) (m : Fin 32 → UInt8) :
    (ct1List pk1 h m).length = 960 := by
  simp only [ct1List, toU8List_length, ct1Size]

/-- The first ciphertext half as an Aeneas `Array U8 960`. -/
def ct1Array (pk1 : List U8) (h : 64 ≤ pk1.length) (m : Fin 32 → UInt8) : Array U8 960#usize :=
  Array.make 960#usize (ct1List pk1 h m) (ct1List_length pk1 h m)

/-- The serialised state `stateBytes (ŷ, e₂, m)` written by round 1. -/
def stateOut (pk1 : List U8) (h : 64 ≤ pk1.length) (m : Fin 32 → UInt8) :
    Fin encapsStateSize → UInt8 :=
  stateBytes (encaps1Output pk1 h m).state

/-- The shared secret written by round 1. -/
def ssOut (pk1 : List U8) (h : 64 ≤ pk1.length) (m : Fin 32 → UInt8) : Fin 32 → UInt8 :=
  (encaps1Output pk1 h m).ss

/-- Read a 32-byte Aeneas array as a `Fin 32 → UInt8` message. -/
def msgOfArray (r : Array U8 32#usize) : Fin 32 → UInt8 :=
  fun i => (r.val[i.val]'(by rw [Array.length_eq]; exact i.isLt)).toUInt8

/-! ## The FIPS 203 model of `encapsulate2` (ML-KEM-768)

libcrux `encapsulate2(state, pk2)` (`src/mlkem.rs`, `mlkem768::incremental::encapsulate2`) takes
the 2080-byte serialised round-1 state and the 1152-byte `pk2 = ByteEncode₁₂(t̂)` — both as
fixed-size arrays, so there are no error cases — decodes them and runs round 2 of Algorithm 17
(`Fips203.mlkemEncapsPhase2`): `c₂ = ByteEncode_{d_v}(Compress_{d_v}(NTT⁻¹(t̂ᵀ∘ŷ) + e₂ +
Decompress₁(m)))`. -/

/-- libcrux `Ciphertext2::len()` for ML-KEM-768: `32 · d_v`. -/
def ct2Size : ℕ := 128

theorem ct2Size_eq : 32 * mlkem768.d_v = ct2Size := by
  simp only [mlkem768_d_v, ct2Size]

/-- Read the 2080-byte Aeneas state array as a `Fin 2080 → UInt8` byte vector. -/
def stateOfArray (st : Array U8 2080#usize) : Fin encapsStateSize → UInt8 :=
  fun i => (st.val[i.val]'(by rw [Array.length_eq]; exact i.isLt)).toUInt8

/-- Read the 1152-byte Aeneas `pk2` array as a `Fin 1152 → UInt8` byte vector. -/
def pk2OfArray (pk2 : Array U8 1152#usize) : Fin 1152 → UInt8 :=
  fun i => (pk2.val[i.val]'(by rw [Array.length_eq]; exact i.isLt)).toUInt8

/-- Recover `t̂` from the serialised `pk2 = ByteEncode₁₂(t̂)` via `ByteDecode₁₂` (the first
`1152` bytes of `ek`, cf. `decodeEkTHat`). -/
def decodePk2THat (pk2 : Fin 1152 → UInt8) : Fin mlkem768.k → (Fin n → Zq) :=
  fun i => byteDecodeZq 12 (fun idx =>
    pk2 ⟨384 * i.val + idx.val, by
      have hi : i.val < 3 := i.isLt
      have hidx := idx.isLt
      have : 32 * 12 = 384 := by norm_num
      omega⟩)

/-- On a generated key, decoding `pk2` gives the same `t̂` as decoding the full `ek`. -/
theorem decodePk2THat_pk2Bytes (seed : Fin 64 → UInt8) :
    decodePk2THat (pk2Bytes seed) = decodeEkTHat (ekBytes seed) := by
  funext i
  simp only [decodePk2THat, decodeEkTHat, decodeEkPoly, pk2Bytes]

/-- The 128-byte second ciphertext half: round 2 of Algorithm 17 on the decoded state and `t̂`. -/
def ct2Bytes (st : Array U8 2080#usize) (pk2 : Array U8 1152#usize) : Fin ct2Size → UInt8 :=
  fun i =>
    mlkemEncapsPhase2 mlkem768 (decodeEncapsState (stateOfArray st))
      (decodePk2THat (pk2OfArray pk2)) ⟨i.val, by have := i.isLt; rw [ct2Size_eq]; exact this⟩

/-- The second ciphertext half as an Aeneas list. -/
def ct2List (st : Array U8 2080#usize) (pk2 : Array U8 1152#usize) : List U8 :=
  toU8List (ct2Bytes st pk2)

theorem ct2List_length (st : Array U8 2080#usize) (pk2 : Array U8 1152#usize) :
    (ct2List st pk2).length = 128 := by
  simp only [ct2List, toU8List_length, ct2Size]

/-- The second ciphertext half as an Aeneas `Array U8 128`. -/
def ct2Array (st : Array U8 2080#usize) (pk2 : Array U8 1152#usize) : Array U8 128#usize :=
  Array.make 128#usize (ct2List st pk2) (ct2List_length st pk2)

end Fips203.Bridge
