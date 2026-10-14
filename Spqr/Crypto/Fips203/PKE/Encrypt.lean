/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module
public import Spqr.Crypto.Fips203.PKE.KeyGen
public import Spqr.Crypto.Fips203.NTT.InvNTT
public import Spqr.Crypto.Fips203.Conversion.ByteDecode
public import Spqr.Crypto.Fips203.Conversion.Compress
public import Spqr.Crypto.Fips203.Conversion.Decompress
/-!
# FIPS 203 Algorithm 14: `K-PKE.Encrypt(ekPKE, m, r)`

NIST FIPS 203 (ML-KEM, August 2024), § 5.2, defines the internal PKE encryption
algorithm `K-PKE.Encrypt`.  Given an encryption key `ekPKE`, a 32-byte message `m`,
and 32 bytes of randomness `r`, it produces a ciphertext `c`.

The algorithm:

1. Parse `ekPKE` to recover `t̂` (via `ByteDecode₁₂`) and the public seed `ρ`.
2. Re-derive the `k × k` NTT-domain matrix `Â` from `ρ` via `SampleNTT(ρ ‖ i ‖ j)`.
3. Sample secret vector `y`, error vector `e₁` from `CBD_η₁`, and error polynomial
   `e₂` from `CBD_η₂`, using `PRF(r, N)` with a running counter `N`.
4. Compute `ŷ = NTT(y)`.
5. Compute `u = NTT⁻¹(Âᵀ ◦ ŷ) + e₁`.
6. Compute `v = NTT⁻¹(t̂ᵀ · ŷ) + e₂ + Decompress₁(m)`.
7. Compress and encode:
     `c₁ = ByteEncode_{d_u}(Compress_{d_u}(u))`
     `c₂ = ByteEncode_{d_v}(Compress_{d_v}(v))`
8. Return `c = c₁ ‖ c₂`.

**Source**: NIST FIPS 203, § 5.2 (Algorithm 14)
-/

@[expose] public section

noncomputable section

namespace Fips203

/-! ## Encryption key parsing -/

/-- Decode the `i`-th polynomial `t̂[i]` from `ekPKE` via `ByteDecode₁₂`. -/
def decodeEkPoly {p : ParamSet} (ek : Fin (384 * p.k + 32) → UInt8)
    (i : Fin p.k) : Fin n → Zq :=
  byteDecodeZq 12 (fun idx =>
    ek ⟨384 * i.val + idx.val, by
      have hi := i.isLt; have hidx := idx.isLt
      have : 32 * 12 = 384 := by norm_num
      omega⟩)

/-- Recover the full NTT-domain vector `t̂` from `ekPKE`. -/
def decodeEkTHat {p : ParamSet}
    (ek : Fin (384 * p.k + 32) → UInt8) : Fin p.k → (Fin n → Zq) :=
  fun i => decodeEkPoly ek i

/-- Recover the public seed `ρ` from the last 32 bytes of `ekPKE`. -/
def decodeEkRho {p : ParamSet} (ek : Fin (384 * p.k + 32) → UInt8) :
    Fin 32 → UInt8 :=
  fun i => ek ⟨384 * p.k + i.val, by omega⟩

/-! ## Encryption randomness sampling -/

/-- Sample encryption secret vector `y[i] = SamplePolyCBD_η₁(PRF(r, i))`. -/
def genEncSecret (r : Fin 32 → UInt8) (p : ParamSet) :
    Fin p.k → (Fin n → Zq) :=
  fun i => samplePolyCBD (prf r (UInt8.ofNat i.val) p.η₁) p.η₁

/-- Sample encryption error vector `e₁[i] = SamplePolyCBD_η₂(PRF(r, k+i))`. -/
def genEncError1 (r : Fin 32 → UInt8) (p : ParamSet) :
    Fin p.k → (Fin n → Zq) :=
  fun i => samplePolyCBD (prf r (UInt8.ofNat (p.k + i.val)) p.η₂) p.η₂

/-- Sample encryption error polynomial `e₂ = SamplePolyCBD_η₂(PRF(r, 2k))`. -/
def genEncError2 (r : Fin 32 → UInt8) (p : ParamSet) : Fin n → Zq :=
  samplePolyCBD (prf r (UInt8.ofNat (2 * p.k)) p.η₂) p.η₂

/-! ## Message encoding -/

/-- Extract bit `i` from the 32-byte message `m` (little-endian within each byte). -/
def msgBit (m : Fin 32 → UInt8) (i : Fin n) : ℕ :=
  ((m ⟨i.val / 8, by have := i.isLt; unfold n at *; omega⟩).toNat
    >>> (i.val % 8)) &&& 1

/-- `Decompress₁(m)`: map each message bit to `ℤ_q` via `Decompress₁`. -/
def decompressMsg (m : Fin 32 → UInt8) : Fin n → Zq :=
  fun i => decompress 1 (msgBit m i)

/-! ## Matrix transpose and vector operations -/

/-- Transpose the `k × k` NTT-domain matrix `Â`. -/
def genMatrixAT (ρ : Fin 32 → UInt8) (p : ParamSet) :
    Fin p.k → Fin p.k → (Fin n → Zq) :=
  fun i j => genMatrixA ρ p j i

/-- `NTT⁻¹` applied componentwise to a vector of NTT-domain polynomials. -/
def invNttVec {p : ParamSet} (v : Fin p.k → (Fin n → Zq)) :
    Fin p.k → (Fin n → Zq) :=
  fun i => invNtt (v i)

/-- Pointwise addition of two polynomials (coefficient representation). -/
def polyAdd (f g : Fin n → Zq) : Fin n → Zq :=
  fun i => f i + g i

/-- NTT-domain inner product `t̂ᵀ · ŷ = ∑ⱼ MultiplyNTTs(t̂[j], ŷ[j])`. -/
def nttInnerProd {p : ParamSet}
    (t_hat y_hat : Fin p.k → (Fin n → Zq)) : Fin n → Zq :=
  fun idx => ∑ j : Fin p.k, multiplyNTTs (t_hat j) (y_hat j) idx

/-! ## Ciphertext computation -/

/-- Compute ciphertext vector `u = NTT⁻¹(Âᵀ ◦ ŷ) + e₁`. -/
def computeU {p : ParamSet} (AT : Fin p.k → Fin p.k → (Fin n → Zq))
    (y_hat : Fin p.k → (Fin n → Zq))
    (e1 : Fin p.k → (Fin n → Zq)) : Fin p.k → (Fin n → Zq) :=
  fun i => polyAdd (invNtt (fun idx => ∑ j : Fin p.k,
    multiplyNTTs (AT i j) (y_hat j) idx)) (e1 i)

/-- Compute ciphertext polynomial
`v = NTT⁻¹(t̂ᵀ · ŷ) + e₂ + Decompress₁(m)`. -/
def computeV {p : ParamSet} (t_hat y_hat : Fin p.k → (Fin n → Zq))
    (e2 : Fin n → Zq) (mu : Fin n → Zq) : Fin n → Zq :=
  polyAdd (polyAdd (invNtt (nttInnerProd t_hat y_hat)) e2) mu

/-! ## Ciphertext encoding -/

/-- Encode a single compressed polynomial via `ByteEncode_d`. -/
def encodeCompressPoly (d : ℕ) (f : Fin n → Zq) :
    Fin (32 * d) → UInt8 :=
  byteEncode d (compressPoly d f)

/-- Ciphertext component `c₁`: compress each `u[i]` with depth `d_u`
and concatenate. -/
def encodeC1 {p : ParamSet}
    (u : Fin p.k → (Fin n → Zq)) :
    Fin (32 * p.compressionU * p.k) → UInt8 :=
  fun idx =>
    let polyIdx : Fin p.k := ⟨idx.val / (32 * p.compressionU), by
      have := idx.isLt; have := p.hCompressionU.1
      exact Nat.div_lt_of_lt_mul (by omega)⟩
    let byteIdx : Fin (32 * p.compressionU) := ⟨idx.val % (32 * p.compressionU), by
      have := p.hCompressionU.1; exact Nat.mod_lt _ (by omega)⟩
    encodeCompressPoly p.compressionU (u polyIdx) byteIdx

/-- Ciphertext component `c₂`: compress `v` with depth `d_v`. -/
def encodeC2 {p : ParamSet} (v : Fin n → Zq) :
    Fin (32 * p.compressionV) → UInt8 :=
  encodeCompressPoly p.compressionV v

/-! ## Ciphertext size -/

/-- Ciphertext size: `32 · d_u · k + 32 · d_v` bytes. -/
def ParamSet.ctSizeEnc (p : ParamSet) : ℕ :=
  32 * p.compressionU * p.k + 32 * p.compressionV

/-- The ciphertext size matches `32 · (d_u · k + d_v)`. -/
theorem ctSizeEnc_eq_ctSize (p : ParamSet) :
    p.ctSizeEnc = p.ctSize := by
  simp only [ParamSet.ctSizeEnc, ParamSet.ctSize]; ring

/-! ## Full ciphertext assembly -/

/-- The ciphertext `c = c₁ ‖ c₂`. -/
def encodeCiphertext {p : ParamSet}
    (u : Fin p.k → (Fin n → Zq)) (v : Fin n → Zq) :
    Fin p.ctSizeEnc → UInt8 :=
  fun idx =>
    if h : idx.val < 32 * p.compressionU * p.k then
      encodeC1 u ⟨idx.val, h⟩
    else
      have h_bound : idx.val - 32 * p.compressionU * p.k < 32 * p.compressionV := by
        have := idx.isLt; unfold ParamSet.ctSizeEnc at *; omega
      encodeC2 v ⟨idx.val - 32 * p.compressionU * p.k, h_bound⟩

/-! ## K-PKE.Encrypt — top-level definition -/

/-- The output of `K-PKE.Encrypt`: a ciphertext. -/
structure KpkeCiphertext (p : ParamSet) where
  /-- Ciphertext `c` of size `32 · (d_u · k + d_v)` bytes. -/
  ct : Fin p.ctSizeEnc → UInt8

/-- **Algorithm 14 — `K-PKE.Encrypt(ekPKE, m, r)`** (FIPS 203, § 5.2).

Given an encryption key `ekPKE` (of size `384 · k + 32` bytes), a
32-byte message `m`, and 32 bytes of randomness `r`, produces a
ciphertext `c` for the internal lattice-based PKE scheme. -/
def kpkeEncrypt (p : ParamSet) (ek : Fin (384 * p.k + 32) → UInt8)
    (m : Fin 32 → UInt8) (r : Fin 32 → UInt8) :
    KpkeCiphertext p :=
  let t_hat := decodeEkTHat ek
  let ρ     := decodeEkRho ek
  let aHatT := genMatrixAT ρ p
  let y     := genEncSecret r p
  let e1    := genEncError1 r p
  let e2    := genEncError2 r p
  let y_hat := nttVec y
  let u     := computeU aHatT y_hat e1
  let mu    := decompressMsg m
  let v     := computeV t_hat y_hat e2 mu
  { ct := encodeCiphertext u v }

/-! ## Elementary properties -/

/-- For ML-KEM-768, the ciphertext has `32·(10·3+4) = 1088` bytes. -/
theorem kpkeEncrypt_ct_size_768 :
    mlkem768.ctSizeEnc = 1088 := by
  simp only [ParamSet.ctSizeEnc, mlkem768]

/-- `computeU` unfolds to `NTT⁻¹(Âᵀ ◦ ŷ) + e₁` pointwise. -/
theorem computeU_eq {p : ParamSet}
    (AT : Fin p.k → Fin p.k → (Fin n → Zq))
    (y_hat : Fin p.k → (Fin n → Zq))
    (e1 : Fin p.k → (Fin n → Zq))
    (i : Fin p.k) (idx : Fin n) :
    computeU AT y_hat e1 i idx =
      invNtt (fun j => ∑ l : Fin p.k,
        multiplyNTTs (AT i l) (y_hat l) j) idx +
      e1 i idx := by
  simp [computeU, polyAdd]

/-- `computeV` unfolds to `NTT⁻¹(t̂ᵀ · ŷ) + e₂ + μ` pointwise. -/
theorem computeV_eq {p : ParamSet}
    (t_hat y_hat : Fin p.k → (Fin n → Zq))
    (e2 mu : Fin n → Zq) (idx : Fin n) :
    computeV t_hat y_hat e2 mu idx =
      invNtt (nttInnerProd t_hat y_hat) idx +
      e2 idx + mu idx := by
  simp [computeV, polyAdd, add_assoc]

/-- The transpose of `genMatrixA` equals `genMatrixAT`. -/
theorem genMatrixAT_eq_transpose (ρ : Fin 32 → UInt8)
    (p : ParamSet) (i j : Fin p.k) :
    genMatrixAT ρ p i j = genMatrixA ρ p j i := by
  simp [genMatrixAT]

end Fips203
