/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Crypto.Fips203.PKE.Encrypt
import Spqr.Crypto.Fips203.PKE.Decrypt
import Spqr.Crypto.Fips203.NTT.RoundTrip
import Spqr.Crypto.Fips203.Conversion.Compress
import Spqr.Crypto.Fips203.Conversion.Decompress
/-!
# FIPS 203 K-PKE Round-Trip Correctness: `decrypt(dk, encrypt(ek, m, r)) = m`

NIST FIPS 203 (ML-KEM, August 2024), §§ 5.1–5.3, defines the internal PKE scheme
`K-PKE` consisting of `KeyGen` (Algorithm 13), `Encrypt` (Algorithm 14), and
`Decrypt` (Algorithm 15).  The fundamental correctness property is:

  **`kpkeDecrypt(dk, kpkeEncrypt(ek, m, r).ct) = m`**

provided that the combined noise introduced by the CBD samples and
compress/decompress rounding remains below the decryption threshold.

## Mathematical summary

Given a key pair `(ek, dk) ← kpkeKeyGen(d)` and a message `m` encrypted under
randomness `r`, the ciphertext carries:

  `u  = NTT⁻¹(Âᵀ ◦ ŷ) + e₁`
  `v  = NTT⁻¹(t̂ᵀ · ŷ) + e₂ + Decompress₁(m)`

Decryption computes `w = v' − NTT⁻¹(ŝᵀ ◦ NTT(u'))` which simplifies to
`Decompress₁(m) + noise`.  The message is recovered by `Compress₁(w)`, which
succeeds when the total noise is small relative to `⌊q/2⌋ = 1664`.

**Source**: NIST FIPS 203, §§ 5.1–5.3 (Algorithms 13–15)
-/
noncomputable section

namespace Fips203

/-! ## Centred representative and absolute value in `ℤ_q` -/

/-- The **centred representative** of `x ∈ ℤ_q`: maps `{0,…,q−1}` to
`{−⌊q/2⌋, …, ⌊q/2⌋}`. -/
def centredRep (x : Zq) : ℤ :=
  if x.val ≤ q / 2 then (x.val : ℤ) else (x.val : ℤ) - (q : ℤ)

/-- The **absolute value** of `x ∈ ℤ_q` in the centred representation. -/
def absZq (x : Zq) : ℕ := (centredRep x).natAbs

/-- The coefficient-wise **infinity norm** of a polynomial `f ∈ R_q`. -/
def polyInfNorm (f : Fin n → Zq) : ℕ :=
  Finset.sup Finset.univ (fun i => absZq (f i))

/-! ## Compression noise -/

/-- The **compression noise** at coefficient `idx`: the rounding error from
compress/decompress of `u` (depth `d_u`) and `v` (depth `d_v`). -/
def compressionNoisePoly
    (f : Fin n → Zq) (d : ℕ) (idx : Fin n) : Zq :=
  decompressPoly d (compressPoly d f) idx - f idx

/-! ## Noise-bounded correctness hypothesis -/

/-- The noise bound predicate: every coefficient of the total noise polynomial
has centred absolute value strictly less than `⌊q/4⌋ = 832`.  This is the
sufficient condition for `Compress₁` to recover each message bit correctly. -/
def noiseBoundedAt (noise : Fin n → Zq) : Prop :=
  ∀ idx : Fin n, absZq (noise idx) < q / 4

/-! ## Key-pair consistency -/

/-- A key pair `(ek, dk)` is **consistent** when it equals `kpkeKeyGen d p`. -/
structure ConsistentKeyPair (p : ParamSet) where
  /-- The 32-byte seed used for key generation. -/
  d : Fin 32 → UInt8
  /-- The key pair generated from `d`. -/
  kp : KpkeKeyPair p
  /-- The key pair equals the output of `kpkeKeyGen d p`. -/
  hkp : kp = kpkeKeyGen d p

/-! ## Round-trip correctness: `Compress₁` recovers the message bit -/

/-- **Message-bit recovery**: if `|noise| < ⌊q/4⌋` then
`compress 1 (decompress 1 b + noise) = b` for `b ∈ {0, 1}`.

This is the pointwise condition ensuring that each bit of the message survives
the noise introduced during encryption and compression. -/
axiom compress1_decompress1_stable (b : ℕ) (noise : Zq)
    (hb : b < 2) (hnoise : absZq noise < q / 4) :
    compress 1 (decompress 1 b + noise) = b

/-! ## Core algebraic identity -/

/-- **Core algebraic identity**: In the absence of compression noise,
`w = v − NTT⁻¹(ŝᵀ ◦ NTT(u))` simplifies to `Decompress₁(m) + noise`.

Expanding the definitions of `u` and `v` from `K-PKE.Encrypt` and using
`t̂ = Â ◦ ŝ + ê`, the `NTT⁻¹(Âᵀ ◦ ŷ)` terms cancel, leaving only the
cross-noise `e₂ + ⟨s, e₁⟩ − ⟨e, y⟩` plus the message. -/
theorem decrypt_encrypt_noise_identity {p : ParamSet}
    (aHat : Fin p.k → Fin p.k → (Fin n → Zq))
    (s_hat e_hat y_hat : Fin p.k → (Fin n → Zq))
    (t_hat : Fin p.k → (Fin n → Zq))
    (e1 : Fin p.k → (Fin n → Zq))
    (e2 mu : Fin n → Zq)
    (h_that : ∀ i idx,
      t_hat i idx = (∑ j : Fin p.k,
        multiplyNTTs (aHat i j) (s_hat j) idx) + e_hat i idx)
    (u : Fin p.k → (Fin n → Zq))
    (h_u : ∀ i idx,
      u i idx = invNtt (fun j => ∑ l : Fin p.k,
        multiplyNTTs (aHat l i) (y_hat l) j) idx + e1 i idx)
    (v : Fin n → Zq)
    (h_v : ∀ idx,
      v idx = invNtt (nttInnerProd t_hat y_hat) idx +
        e2 idx + mu idx) :
    ∀ idx : Fin n,
      computeW v s_hat (fun i => u i) idx =
        mu idx +
        (e2 idx +
         (∑ i : Fin p.k, invNtt (fun j =>
           multiplyNTTs (ntt (s_hat i)) (ntt (e1 i)) j) idx) -
         (∑ i : Fin p.k, invNtt (fun j =>
           multiplyNTTs (ntt (e_hat i)) (ntt (y_hat i)) j) idx)) := by
  sorry


/-! ## Main round-trip theorem -/

/-- **K-PKE round-trip correctness** (FIPS 203, §§ 5.1–5.3):

  `kpkeDecrypt(dk, kpkeEncrypt(ek, m, r).ct) = m`

under the hypothesis that the total noise (algebraic + compression) is bounded
at every coefficient.

The proof proceeds by:
1. Unfolding `kpkeDecrypt` and `kpkeEncrypt` to expose `computeW`.
2. Applying `decrypt_encrypt_noise_identity` to rewrite `w` as
   `Decompress₁(m) + noise`.
3. Showing that `recoverMsg w = m` by applying `compress1_decompress1_stable`
   at each coefficient.

**Source**: NIST FIPS 203, §§ 5.1–5.3 -/
theorem kpke_roundTrip (p : ParamSet)
    (d : Fin 32 → UInt8) (m r : Fin 32 → UInt8)
    (kp : KpkeKeyPair p)
    (h_kp : kp = kpkeKeyGen d p)
    -- Encoding round-trip hypotheses
    (h_dk_rt : ∀ i idx,
      decodeDkSHat kp.dk i idx =
        nttVec (genSecret (sigma d p) p) i idx)
    (h_ek_rt : ∀ i idx,
      decodeEkTHat kp.ek i idx =
        computeTHat (genMatrixA (rho d p) p)
          (nttVec (genSecret (sigma d p) p))
          (nttVec (genError (sigma d p) p)) i idx)
    -- Message bit bound
    (h_msg : ∀ i : Fin n, msgBit m i < 2)
    -- Noise bound
    (h_noise : ∀ idx : Fin n,
      absZq (
        let s_hat := nttVec (genSecret (sigma d p) p)
        let e_hat := nttVec (genError (sigma d p) p)
        let y     := genEncSecret r p
        let e1    := genEncError1 r p
        let e2    := genEncError2 r p
        let y_hat := nttVec y
        let aHat  := genMatrixA (rho d p) p
        let t_hat := computeTHat aHat s_hat e_hat
        let u     := computeU (genMatrixAT (rho d p) p) y_hat e1
        let v     := computeV t_hat y_hat e2 (decompressMsg m)
        -- algebraic noise + compression noise
        (computeW
          (decompressPoly p.d_v (compressPoly p.d_v v))
          s_hat
          (fun i => decompressPoly p.d_u (compressPoly p.d_u (u i)))
          idx -
         decompressMsg m idx)) < q / 4) :
    kpkeDecrypt p kp.dk (kpkeEncrypt p kp.ek m r).ct = m := by
  sorry

/-! ## Corollary: ML-KEM-768 instantiation -/

/-- **ML-KEM-768 round-trip correctness**: specialisation of `kpke_roundTrip`
to the ML-KEM-768 parameter set used by SPQR. -/
theorem kpke_roundTrip_768
    (d : Fin 32 → UInt8) (m r : Fin 32 → UInt8)
    (kp : KpkeKeyPair mlkem768)
    (h_kp : kp = kpkeKeyGen d mlkem768)
    (h_dk_rt : ∀ i idx,
      decodeDkSHat kp.dk i idx =
        nttVec (genSecret (sigma d mlkem768) mlkem768) i idx)
    (h_ek_rt : ∀ i idx,
      decodeEkTHat kp.ek i idx =
        computeTHat (genMatrixA (rho d mlkem768) mlkem768)
          (nttVec (genSecret (sigma d mlkem768) mlkem768))
          (nttVec (genError (sigma d mlkem768) mlkem768)) i idx)
    (h_msg : ∀ i : Fin n, msgBit m i < 2)
    (h_noise : ∀ idx : Fin n,
      absZq (
        let s_hat := nttVec (genSecret (sigma d mlkem768) mlkem768)
        let e_hat := nttVec (genError (sigma d mlkem768) mlkem768)
        let y     := genEncSecret r mlkem768
        let e1    := genEncError1 r mlkem768
        let e2    := genEncError2 r mlkem768
        let y_hat := nttVec y
        let aHat  := genMatrixA (rho d mlkem768) mlkem768
        let t_hat := computeTHat aHat s_hat e_hat
        let u     := computeU (genMatrixAT (rho d mlkem768) mlkem768) y_hat e1
        let v     := computeV t_hat y_hat e2 (decompressMsg m)
        (computeW
          (decompressPoly mlkem768.d_v (compressPoly mlkem768.d_v v))
          s_hat
          (fun i => decompressPoly mlkem768.d_u
            (compressPoly mlkem768.d_u (u i)))
          idx -
         decompressMsg m idx)) < q / 4) :
    kpkeDecrypt mlkem768 kp.dk
      (kpkeEncrypt mlkem768 kp.ek m r).ct = m :=
  kpke_roundTrip mlkem768 d m r kp h_kp h_dk_rt h_ek_rt h_msg h_noise

/-! ## Noise bound constants for ML-KEM-768 -/

/-- The decryption threshold for `Compress₁`: `⌊q/4⌋ = 832`. -/
theorem q_div_4_eq : q / 4 = 832 := by norm_num [q]

/-- For ML-KEM-768, `η₁ = η₂ = 2`. -/
theorem mlkem768_eta_bound : mlkem768.η₁ = 2 ∧ mlkem768.η₂ = 2 := by
  simp [mlkem768]

end Fips203
