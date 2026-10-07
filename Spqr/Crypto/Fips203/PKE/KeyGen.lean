/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Crypto.Fips203.Params
import Spqr.Crypto.Fips203.Ring
import Spqr.Crypto.Fips203.Sampling.SampleNTT
import Spqr.Crypto.Fips203.Sampling.SamplePolyCBD
import Spqr.Crypto.Fips203.NTT.NTT
import Spqr.Crypto.Fips203.NTT.MultiplyNTTs
import Spqr.Crypto.Fips203.Conversion.ByteEncode
/-!
# FIPS 203 Algorithm 13: `K-PKE.KeyGen(d)`

NIST FIPS 203 (ML-KEM, August 2024), § 5.1, defines the internal PKE key generation
algorithm `K-PKE.KeyGen`.  Given a 32-byte seed `d`, it produces an encryption key `ekPKE`
and a decryption key `dkPKE`.

The algorithm:

1. Expand the seed `d` via `G` (SHA3-512) to obtain `(ρ, σ) = G(d ‖ k)`.
2. Generate the `k × k` matrix `Â` in NTT domain via `SampleNTT(ρ ‖ i ‖ j)`.
3. Sample secret vector `s` and error vector `e` from `CBD_η₁` via `PRF_η₁(σ, N)`.
4. Compute `ŝ = NTT(s)`, `ê = NTT(e)`.
5. Compute `t̂ = Â ◦ ŝ + ê`.
6. Encode `ekPKE = ByteEncode₁₂(t̂) ‖ ρ` and `dkPKE = ByteEncode₁₂(ŝ)`.

**Source**: NIST FIPS 203, § 5.1 (Algorithm 13)
-/

noncomputable section

namespace Fips203

/-! ## Hash functions (axiomatised)

`G` is SHA3-512 producing 64 bytes.  `PRF_η` is SHAKE-256 producing `64·η` bytes
from a 33-byte input `(σ ‖ N)`.  Both are axiomatised as opaque oracles. -/

/-- `G(input)` — SHA3-512 hash producing 64 bytes. -/
opaque hashG (input : List UInt8) : Fin 64 → UInt8

/-- `PRF_η(σ, N)` — SHAKE-256 producing `64 · η` bytes from `σ ‖ N`. -/
opaque prf (σ : Fin 32 → UInt8) (N : UInt8) (η : ℕ) : ℕ → UInt8

/-! ## Seed expansion -/

/-- Concatenate the 32-byte seed `d` with the single-byte module rank `k`. -/
def seedInput (d : Fin 32 → UInt8) (p : ParamSet) : List UInt8 :=
  (List.ofFn d) ++ [UInt8.ofNat p.k]

/-- Extract the public seed `ρ` (first 32 bytes of `G(d ‖ k)`). -/
def rho (d : Fin 32 → UInt8) (p : ParamSet) : Fin 32 → UInt8 :=
  fun i => hashG (seedInput d p) ⟨i.val, by omega⟩

/-- Extract the private seed `σ` (last 32 bytes of `G(d ‖ k)`). -/
def sigma (d : Fin 32 → UInt8) (p : ParamSet) : Fin 32 → UInt8 :=
  fun i => hashG (seedInput d p) ⟨32 + i.val, by omega⟩

/-! ## XOF seed construction -/

/-- Build the 34-byte XOF seed `ρ ‖ i ‖ j` for matrix entry `Â[i,j]`. -/
def xofSeed (ρ : Fin 32 → UInt8) (i j : UInt8) : Fin 34 → UInt8 :=
  fun idx =>
    if h : idx.val < 32 then ρ ⟨idx.val, h⟩
    else if idx.val = 32 then i
    else j

/-! ## Matrix generation -/

/-- Generate the `k × k` NTT-domain matrix `Â` from the public seed `ρ`. -/
def genMatrixA (ρ : Fin 32 → UInt8) (p : ParamSet) :
    Fin p.k → Fin p.k → (Fin n → Zq) :=
  fun i j => sampleNTT (xofSeed ρ (UInt8.ofNat i.val) (UInt8.ofNat j.val))

/-! ## Secret and error vector sampling -/

/-- Sample secret vector `s[i] = SamplePolyCBD_η₁(PRF(σ, i))` for `i ∈ {0,…,k−1}`. -/
def genSecret (σ : Fin 32 → UInt8) (p : ParamSet) : Fin p.k → (Fin n → Zq) :=
  fun i => samplePolyCBD (prf σ (UInt8.ofNat i.val) p.η₁) p.η₁

/-- Sample error vector `e[i] = SamplePolyCBD_η₁(PRF(σ, k+i))` for `i ∈ {0,…,k−1}`. -/
def genError (σ : Fin 32 → UInt8) (p : ParamSet) : Fin p.k → (Fin n → Zq) :=
  fun i => samplePolyCBD (prf σ (UInt8.ofNat (p.k + i.val)) p.η₁) p.η₁

/-! ## NTT of vectors -/

/-- `NTT` applied componentwise to a vector of polynomials. -/
def nttVec {p : ParamSet} (v : Fin p.k → (Fin n → Zq)) : Fin p.k → (Fin n → Zq) :=
  fun i => ntt (v i)

/-! ## NTT-domain matrix-vector product -/

/-- `(A ◦ v)[i] = ∑ⱼ MultiplyNTTs(A[i,j], v[j])`. -/
def nttMatVecMul {p : ParamSet}
    (A : Fin p.k → Fin p.k → (Fin n → Zq))
    (v : Fin p.k → (Fin n → Zq)) : Fin p.k → (Fin n → Zq) :=
  fun i idx => ∑ j : Fin p.k, multiplyNTTs (A i j) (v j) idx

/-! ## Vector addition -/

/-- Pointwise addition of two NTT-domain vectors. -/
def nttVecAdd {p : ParamSet}
    (u v : Fin p.k → (Fin n → Zq)) : Fin p.k → (Fin n → Zq) :=
  fun i idx => u i idx + v i idx

/-! ## Public key computation -/

/-- `t̂ = Â ◦ ŝ + ê`. -/
def computeTHat {p : ParamSet} (A : Fin p.k → Fin p.k → (Fin n → Zq))
    (s_hat e_hat : Fin p.k → (Fin n → Zq)) : Fin p.k → (Fin n → Zq) :=
  nttVecAdd (nttMatVecMul A s_hat) e_hat

/-! ## Key encoding -/

/-- Encode a single NTT-domain polynomial via `ByteEncode₁₂`. -/
def encodePoly12 (f : Fin n → Zq) : Fin (32 * 12) → UInt8 :=
  byteEncodeZq 12 f

/-- `32 * 12 = 384`. -/
theorem encode12_size : 32 * 12 = 384 := by norm_num

/-- Encryption key: `ekPKE = ByteEncode₁₂(t̂₀) ‖ … ‖ ByteEncode₁₂(t̂_{k-1}) ‖ ρ`. -/
def encodeEk {p : ParamSet} (t_hat : Fin p.k → (Fin n → Zq)) (ρ : Fin 32 → UInt8) :
    Fin (384 * p.k + 32) → UInt8 :=
  fun idx =>
    if h : idx.val < 384 * p.k then
      let polyIdx : Fin p.k := ⟨idx.val / 384, by omega⟩
      let byteIdx : Fin 384 := ⟨idx.val % 384, by omega⟩
      encodePoly12 (t_hat polyIdx) (byteIdx.cast encode12_size.symm)
    else
      ρ ⟨idx.val - 384 * p.k, by omega⟩

/-- Decryption key: `dkPKE = ByteEncode₁₂(ŝ₀) ‖ … ‖ ByteEncode₁₂(ŝ_{k-1})`. -/
def encodeDk {p : ParamSet} (s_hat : Fin p.k → (Fin n → Zq)) :
    Fin (384 * p.k) → UInt8 :=
  fun idx =>
    let polyIdx : Fin p.k := ⟨idx.val / 384, by omega⟩
    let byteIdx : Fin 384 := ⟨idx.val % 384, by omega⟩
    encodePoly12 (s_hat polyIdx) (byteIdx.cast encode12_size.symm)

/-! ## K-PKE.KeyGen — top-level definition -/

/-- The output of `K-PKE.KeyGen`: an encryption key and a decryption key. -/
structure KpkeKeyPair (p : ParamSet) where
  /-- Encryption key `ekPKE` of size `384 · k + 32` bytes. -/
  ek : Fin (384 * p.k + 32) → UInt8
  /-- Decryption key `dkPKE` of size `384 · k` bytes. -/
  dk : Fin (384 * p.k) → UInt8

/-- **Algorithm 13 — `K-PKE.KeyGen(d)`** (FIPS 203, § 5.1).

Given a 32-byte seed `d`, produces an encryption key `ekPKE` and a decryption key
`dkPKE` for the internal lattice-based public-key encryption scheme. -/
def kpkeKeyGen (d : Fin 32 → UInt8) (p : ParamSet) : KpkeKeyPair p :=
  let ρ     := rho d p
  let σ     := sigma d p
  let aHat  := genMatrixA ρ p
  let s     := genSecret σ p
  let e     := genError σ p
  let s_hat := nttVec s
  let e_hat := nttVec e
  let t_hat := computeTHat aHat s_hat e_hat
  { ek := encodeEk t_hat ρ
    dk := encodeDk s_hat }

/-! ## Elementary properties -/

/-- For ML-KEM-768, `ekPKE` has `384 · 3 + 32 = 1184` bytes. -/
theorem kpkeKeyGen_ek_size_768 :
    384 * mlkem768.k + 32 = 1184 := by norm_num [mlkem768]

/-- For ML-KEM-768, `dkPKE` has `384 · 3 = 1152` bytes. -/
theorem kpkeKeyGen_dk_size_768 :
    384 * mlkem768.k = 1152 := by norm_num [mlkem768]

/-- `t̂` is determined by `Â`, `ŝ`, and `ê`:
`computeTHat A s_hat e_hat i idx = (∑ⱼ MultiplyNTTs(A[i,j], ŝ[j]))[idx] + ê[i][idx]`. -/
theorem computeTHat_eq {p : ParamSet} (A : Fin p.k → Fin p.k → (Fin n → Zq))
    (s_hat e_hat : Fin p.k → (Fin n → Zq)) (i : Fin p.k) (idx : Fin n) :
    computeTHat A s_hat e_hat i idx =
      (∑ j : Fin p.k, multiplyNTTs (A i j) (s_hat j) idx) + e_hat i idx := by
  simp [computeTHat, nttVecAdd, nttMatVecMul]

end Fips203
