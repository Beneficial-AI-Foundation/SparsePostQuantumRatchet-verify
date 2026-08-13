/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module
public import Spqr.Crypto.Fips203.PKE.Encrypt
public import Spqr.Crypto.Fips203.NTT.InvNTT
public import Spqr.Crypto.Fips203.Conversion.ByteDecode
public import Spqr.Crypto.Fips203.Conversion.Decompress
public import Spqr.Crypto.Fips203.Conversion.ByteEncode
public import Spqr.Crypto.Fips203.Conversion.Compress
/-!
# FIPS 203 Algorithm 15: `K-PKE.Decrypt(dkPKE, c)`

NIST FIPS 203 (ML-KEM, August 2024), § 5.3, defines the internal PKE decryption
algorithm `K-PKE.Decrypt`.  Given a decryption key `dkPKE` and a ciphertext `c`,
it recovers the 32-byte plaintext message `m`.

The algorithm:

1. Parse ciphertext `c = c₁ ‖ c₂` where `c₁` has `32 · d_u · k` bytes and
   `c₂` has `32 · d_v` bytes.
2. Decode and decompress `u'` from `c₁` via `Decompress_{d_u}(ByteDecode_{d_u}(…))`.
3. Decode and decompress `v'` from `c₂` via `Decompress_{d_v}(ByteDecode_{d_v}(…))`.
4. Decode the secret vector `ŝ` from `dkPKE` via `ByteDecode₁₂`.
5. Compute `w = v' − NTT⁻¹(ŝᵀ ◦ NTT(u'))`.
6. Return `m = ByteEncode₁(Compress₁(w))`.

**Source**: NIST FIPS 203, § 5.3 (Algorithm 15)
-/

@[expose] public section

noncomputable section

namespace Fips203

/-! ## Ciphertext parsing -/

/-- Extract the `i`-th decompressed polynomial `u'[i]` from the first part `c₁`
of the ciphertext, via `Decompress_{d_u}(ByteDecode_{d_u}(…))`. -/
def decodeCiphertextU {p : ParamSet}
    (c : Fin p.ctSizeEnc → UInt8) (i : Fin p.k) : Fin n → Zq :=
  decompressPoly p.compressionU (byteDecode p.compressionU (fun j =>
    c ⟨32 * p.compressionU * i.val + j.val, by
      have hi := i.isLt; have hj := j.isLt
      have hd := p.hCompressionU.1
      have key : 32 * p.compressionU * i.val + j.val < 32 * p.compressionU * p.k := by
        calc 32 * p.compressionU * i.val + j.val
            < 32 * p.compressionU * i.val + 32 * p.compressionU := by omega
          _ = 32 * p.compressionU * (i.val + 1) := by ring
          _ ≤ 32 * p.compressionU * p.k := Nat.mul_le_mul_left _ (by omega)
      unfold ParamSet.ctSizeEnc; omega⟩))

/-- Extract the decompressed polynomial `v'` from the second part `c₂`
of the ciphertext, via `Decompress_{d_v}(ByteDecode_{d_v}(…))`. -/
def decodeCiphertextV {p : ParamSet}
    (c : Fin p.ctSizeEnc → UInt8) : Fin n → Zq :=
  decompressPoly p.compressionV (byteDecode p.compressionV (fun j =>
    c ⟨32 * p.compressionU * p.k + j.val, by
      have hj := j.isLt
      unfold ParamSet.ctSizeEnc; omega⟩))

/-! ## Decryption key parsing -/

/-- Decode the `i`-th NTT-domain polynomial `ŝ[i]` from `dkPKE` via `ByteDecode₁₂`. -/
def decodeDkPoly {p : ParamSet} (dk : Fin (384 * p.k) → UInt8)
    (i : Fin p.k) : Fin n → Zq :=
  byteDecodeZq 12 (fun idx =>
    dk ⟨384 * i.val + idx.val, by
      have hi := i.isLt; have hidx := idx.isLt
      have : 32 * 12 = 384 := by norm_num
      omega⟩)

/-- Recover the full NTT-domain secret vector `ŝ` from `dkPKE`. -/
def decodeDkSHat {p : ParamSet}
    (dk : Fin (384 * p.k) → UInt8) : Fin p.k → (Fin n → Zq) :=
  fun i => decodeDkPoly dk i

/-! ## Inner product in NTT domain -/

/-- NTT inner product `ŝᵀ ◦ NTT(u')`: `∑ᵢ MultiplyNTTs(ŝ[i], NTT(u'[i]))`. -/
def nttInnerProdDecrypt {p : ParamSet}
    (s_hat : Fin p.k → (Fin n → Zq))
    (u : Fin p.k → (Fin n → Zq)) : Fin n → Zq :=
  fun idx => ∑ i : Fin p.k, multiplyNTTs (s_hat i) (ntt (u i)) idx

/-! ## Decryption core: `w = v' − NTT⁻¹(ŝᵀ ◦ NTT(u'))` -/

/-- Compute `w = v' − NTT⁻¹(ŝᵀ ◦ NTT(u'))`.

This is the noise-removed approximation of the original message polynomial.
Compressing `w` via `Compress₁` recovers each message bit. -/
def computeW {p : ParamSet}
    (v : Fin n → Zq) (s_hat : Fin p.k → (Fin n → Zq))
    (u : Fin p.k → (Fin n → Zq)) : Fin n → Zq :=
  fun idx => v idx - invNtt (nttInnerProdDecrypt s_hat u) idx

/-! ## Message recovery: `m = ByteEncode₁(Compress₁(w))` -/

/-- Compress and encode `w` to recover the 32-byte message `m`.

Each coefficient `w[i]` is compressed to a single bit via `Compress₁`, then the
256 bits are packed into 32 bytes via `ByteEncode₁`. -/
def recoverMsg (w : Fin n → Zq) : Fin 32 → UInt8 :=
  byteEncode 1 (compressPoly 1 w)

/-! ## K-PKE.Decrypt — top-level definition -/

/-- **Algorithm 15 — `K-PKE.Decrypt(dkPKE, c)`** (FIPS 203, § 5.3).

Given a decryption key `dkPKE` (of size `384 · k` bytes) and a ciphertext `c`
(of size `32 · (d_u · k + d_v)` bytes), recovers the 32-byte plaintext
message `m` for the internal lattice-based PKE scheme. -/
def kpkeDecrypt (p : ParamSet) (dk : Fin (384 * p.k) → UInt8)
    (c : Fin p.ctSizeEnc → UInt8) : Fin 32 → UInt8 :=
  let u     := fun i => decodeCiphertextU c i
  let v     := decodeCiphertextV c
  let s_hat := decodeDkSHat dk
  let w     := computeW v s_hat u
  recoverMsg w

/-! ## Elementary properties -/

/-- For ML-KEM-768, the decryption key has `384 · 3 = 1152` bytes. -/
theorem kpkeDecrypt_dk_size_768 :
    384 * mlkem768.k = 1152 := by norm_num [mlkem768]

/-- For ML-KEM-768, the ciphertext has `32 · (10 · 3 + 4) = 1088` bytes. -/
theorem kpkeDecrypt_ct_size_768 :
    mlkem768.ctSizeEnc = 1088 := by
  simp only [ParamSet.ctSizeEnc, mlkem768]

/-- `computeW` unfolds to `v' − NTT⁻¹(ŝᵀ ◦ NTT(u'))` pointwise. -/
theorem computeW_eq {p : ParamSet}
    (v : Fin n → Zq) (s_hat : Fin p.k → (Fin n → Zq))
    (u : Fin p.k → (Fin n → Zq)) (idx : Fin n) :
    computeW v s_hat u idx =
      v idx - invNtt (fun j => ∑ i : Fin p.k,
        multiplyNTTs (s_hat i) (ntt (u i)) j) idx := by
  unfold computeW nttInnerProdDecrypt; rfl

/-- The recovered message is 32 bytes (by type).  This theorem witnesses
that the output type of `kpkeDecrypt` is `Fin 32 → UInt8`. -/
theorem kpkeDecrypt_msg_size (p : ParamSet) (dk : Fin (384 * p.k) → UInt8)
    (c : Fin p.ctSizeEnc → UInt8) :
    ∀ (i : Fin 32), ∃ (b : UInt8), kpkeDecrypt p dk c i = b :=
  fun i => ⟨kpkeDecrypt p dk c i, rfl⟩

/-- `recoverMsg` is equivalent to `encodeCompressPoly 1` applied to `w`. -/
theorem recoverMsg_eq_encodeCompressPoly (w : Fin n → Zq) :
    recoverMsg w = encodeCompressPoly 1 w := by
  simp [recoverMsg, encodeCompressPoly]

end Fips203
