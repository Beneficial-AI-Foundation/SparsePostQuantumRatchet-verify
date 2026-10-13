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
succeeds when every coefficient of the noise has centred absolute value
`< ⌊q/4⌋ = 832`.

The main theorem `kpke_roundTrip` is proved **without axioms or `sorry`** for
every parameter set: the key and ciphertext encode/decode round-trips are
theorems (`decode*_encode*`), the honest ciphertext and decryption polynomial
are named (`honestU`, `honestV`, `honestW`), and the only hypothesis is the
noise bound `noiseBoundedAt (honestW − Decompress₁ m)`.

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
lemma compress1_decompress1_stable (b : ℕ) (noise : Zq)
    (hb : b < 2) (hnoise : absZq noise < q / 4) :
    compress 1 (decompress 1 b + noise) = b := by
  have hval : noise.val < q := ZMod.val_lt noise
  -- Extract noise range from absZq hypothesis
  have hnoise_range : noise.val ≤ 831 ∨ (noise.val ≥ 2498 ∧ noise.val ≤ 3328) := by
    unfold absZq centredRep at hnoise
    simp only [q] at hnoise
    by_cases h : noise.val ≤ 3329 / 2
    · -- noise.val ≤ 1664: centred rep = noise.val ≥ 0
      simp only [h, ite_true] at hnoise
      have := Int.natAbs_of_nonneg (show (0 : ℤ) ≤ ↑noise.val by omega)
      left; omega
    · -- noise.val > 1664: centred rep = noise.val - 3329 < 0
      simp only [show ¬(noise.val ≤ 3329 / 2) from by omega, ite_false] at hnoise
      have hval2 : noise.val < 3329 := by unfold q at hval; exact hval
      have h1 : (↑(noise.val) - ↑(3329 : ℕ) : ℤ).natAbs = 3329 - noise.val := by
        have : (↑noise.val : ℤ) ≤ ↑(3329 : ℕ) := by omega
        omega
      rw [h1] at hnoise
      right; constructor <;> omega
  -- Now prove the main goal
  interval_cases b
  · -- b = 0
    simp only [decompress, compress, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, q]
    norm_num
    rcases hnoise_range with h | ⟨h1, h2⟩ <;> omega
  · -- b = 1
    simp only [decompress, compress, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, q]
    norm_num
    -- Goal: (2 * ZMod.val (1665 + noise) + 1664) / 3329 % 2 = 1
    -- Need to rewrite ZMod.val (1665 + noise)
    have hval1665 : (1665 : ZMod 3329).val = 1665 := by
      change (ZMod.val ((1665 : ℕ) : ZMod 3329)) = 1665
      rw [ZMod.val_natCast_of_lt (by norm_num : (1665 : ℕ) < 3329)]
    rw [show (1665 : Zq) = (1665 : ZMod 3329) from rfl]
    rw [ZMod.val_add, hval1665]
    have hval2 : noise.val < 3329 := by unfold q at hval; exact hval
    rcases hnoise_range with h | ⟨h1, h2⟩ <;> omega

/-! ## Linearity helpers -/

/-- `invNtt` distributes over subtraction. -/
private lemma invNtt_sub (f g : Fin n → Zq) :
    invNtt (fun i => f i - g i) =
      fun i => invNtt f i - invNtt g i := by
  have hsub : (fun i => f i - g i) = fun i => f i + ((-1) * g i) := by
    funext i; ring
  rw [hsub, invNtt_add]
  have := invNtt_smul (-1) g
  funext i; rw [congrFun this i]; ring

/-! ## polyMulCoeffs associativity -/

/-- `polyMulCoeffs` is associative (inherited from `Rq` ring multiplication). -/
private lemma polyMulCoeffs_assoc (f g h : Fin n → Zq) :
    polyMulCoeffs (polyMulCoeffs f g) h =
      polyMulCoeffs f (polyMulCoeffs g h) := by
  simp only [polyMulCoeffs, ofCoeffs_toCoeffs, mul_assoc]

/-! ## multiplyNTTs associativity -/

/-- `multiplyNTTs` is associative. -/
private lemma multiplyNTTs_assoc (a b c : Fin n → Zq) :
    multiplyNTTs (multiplyNTTs a b) c =
      multiplyNTTs a (multiplyNTTs b c) := by
  obtain ⟨a', rfl⟩ := ntt_surjective a
  obtain ⟨b', rfl⟩ := ntt_surjective b
  obtain ⟨c', rfl⟩ := ntt_surjective c
  have hab : multiplyNTTs (ntt a') (ntt b') = ntt (polyMulCoeffs a' b') :=
    (ntt_polyMul a' b').symm
  have hbc : multiplyNTTs (ntt b') (ntt c') = ntt (polyMulCoeffs b' c') :=
    (ntt_polyMul b' c').symm
  have lhs : multiplyNTTs (multiplyNTTs (ntt a') (ntt b')) (ntt c') =
      ntt (polyMulCoeffs (polyMulCoeffs a' b') c') := by
    rw [hab]; exact (ntt_polyMul (polyMulCoeffs a' b') c').symm
  have rhs : multiplyNTTs (ntt a') (multiplyNTTs (ntt b') (ntt c')) =
      ntt (polyMulCoeffs a' (polyMulCoeffs b' c')) := by
    rw [hbc]; exact (ntt_polyMul a' (polyMulCoeffs b' c')).symm
  rw [lhs, rhs, polyMulCoeffs_assoc]

/-! ## Signal cancellation helper -/

/-- `multiplyNTTs(multiplyNTTs a b) c = multiplyNTTs b (multiplyNTTs a c)` -/
private lemma multiplyNTTs_comm_assoc (a b c : Fin n → Zq) :
    multiplyNTTs (multiplyNTTs a b) c =
      multiplyNTTs b (multiplyNTTs a c) := by
  rw [multiplyNTTs_comm a b, multiplyNTTs_assoc]

/-! ## Generalized sum lemmas -/

/-- `invNtt` commutes with finite sums over any index type. -/
private lemma invNtt_finset_sum {ι : Type*} (s : Finset ι)
    (g : ι → Fin n → Zq) :
    invNtt (fun i => ∑ j ∈ s, g j i) =
      fun i => ∑ j ∈ s, invNtt (g j) i := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using invNtt_zero
  | insert a s ha ih =>
    have h1 : (fun i => ∑ j ∈ insert a s, g j i)
        = fun i => g a i + ∑ j ∈ s, g j i := by
      funext i; rw [Finset.sum_insert ha]
    rw [h1, invNtt_add, ih]
    funext i; simp [Finset.sum_insert ha]

/-! ## Generalized multiplyNTTs sum lemmas -/

/-- `multiplyNTTs` commutes with finite sums (right argument), over any index type. -/
private lemma multiplyNTTs_finset_sum_right {ι : Type*} (s : Finset ι)
    (fh : Fin n → Zq) (G : ι → Fin n → Zq) :
    multiplyNTTs fh (fun i => ∑ k ∈ s, G k i) =
      fun i => ∑ k ∈ s, multiplyNTTs fh (G k) i := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using multiplyNTTs_zero_right fh
  | insert a s ha ih =>
    have h1 : (fun i => ∑ k ∈ insert a s, G k i)
        = fun i => G a i + ∑ k ∈ s, G k i := by
      funext i; rw [Finset.sum_insert ha]
    rw [h1, multiplyNTTs_add_right, ih]
    funext i; simp [Finset.sum_insert ha]

/-- `multiplyNTTs` commutes with finite sums (left argument), over any index type. -/
private lemma multiplyNTTs_finset_sum_left {ι : Type*} (s : Finset ι)
    (F : ι → Fin n → Zq) (gh : Fin n → Zq) :
    multiplyNTTs (fun i => ∑ j ∈ s, F j i) gh =
      fun i => ∑ j ∈ s, multiplyNTTs (F j) gh i := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using multiplyNTTs_zero_left gh
  | insert a s ha ih =>
    have h1 : (fun i => ∑ j ∈ insert a s, F j i)
        = fun i => F a i + ∑ j ∈ s, F j i := by
      funext i; rw [Finset.sum_insert ha]
    rw [h1, multiplyNTTs_add_left, ih]
    funext i; simp [Finset.sum_insert ha]

/-! ## Signal term equality -/

/-- The signal terms from encryption and decryption are equal:
`∑ᵢ ∑ⱼ multiplyNTTs(multiplyNTTs(Â_ij)(ŝ_j))(ŷ_i)
= ∑ᵢ ∑ₗ multiplyNTTs(ŝ_i)(multiplyNTTs(Â_li)(ŷ_l))`. -/
private lemma signal_terms_eq {p : ParamSet}
    (aHat : Fin p.k → Fin p.k → (Fin n → Zq))
    (s_hat y_hat : Fin p.k → (Fin n → Zq)) :
    (fun j => ∑ i : Fin p.k, (∑ l : Fin p.k,
        multiplyNTTs (multiplyNTTs (aHat i l) (s_hat l)) (y_hat i) j)) =
    (fun j => ∑ i : Fin p.k, (∑ l : Fin p.k,
        multiplyNTTs (s_hat i) (multiplyNTTs (aHat l i) (y_hat l)) j)) := by
  funext j
  rw [Finset.sum_comm]
  congr 1; ext i
  congr 1; ext l
  exact congrFun (multiplyNTTs_comm_assoc (aHat l i) (s_hat i) (y_hat l)) j

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
           multiplyNTTs (e_hat i) (y_hat i) j) idx) -
         (∑ i : Fin p.k, invNtt (fun j =>
           multiplyNTTs (s_hat i) (ntt (e1 i)) j) idx)) := by
  intro idx
  -- Step 1: Unfold computeW and substitute v
  rw [computeW_eq, h_v idx]
  -- Step 2: Expand ntt(u i) using h_u
  have h_ntt_u : ∀ i : Fin p.k, ntt (u i) = fun j =>
      (∑ l : Fin p.k, multiplyNTTs (aHat l i) (y_hat l) j) +
        ntt (e1 i) j := by
    intro i
    have : u i = fun idx => invNtt (fun j => ∑ l : Fin p.k,
        multiplyNTTs (aHat l i) (y_hat l) j) idx + e1 i idx := by
      funext idx; exact h_u i idx
    rw [this, ntt_add, ntt_invNtt]
  -- Step 3: Expand nttInnerProdDecrypt
  have h_decrypt : (fun j => ∑ i : Fin p.k,
      multiplyNTTs (s_hat i) (ntt (u i)) j) =
    fun j => (∑ i : Fin p.k, ∑ l : Fin p.k,
        multiplyNTTs (s_hat i)
          (multiplyNTTs (aHat l i) (y_hat l)) j) +
      (∑ i : Fin p.k,
        multiplyNTTs (s_hat i) (ntt (e1 i)) j) := by
    funext j
    rw [← Finset.sum_add_distrib]
    congr 1; ext i; rw [h_ntt_u i]
    rw [congrFun (multiplyNTTs_add_right (s_hat i)
      (fun j => ∑ l, multiplyNTTs (aHat l i) (y_hat l) j)
      (ntt (e1 i))) j]
    congr 1
    exact congrFun (multiplyNTTs_finset_sum_right Finset.univ
      (s_hat i) (fun l j => multiplyNTTs (aHat l i) (y_hat l) j)) j
  -- Step 4: Expand nttInnerProd t_hat y_hat
  have h_encrypt : nttInnerProd t_hat y_hat =
    fun j => (∑ i : Fin p.k, ∑ l : Fin p.k,
        multiplyNTTs (multiplyNTTs (aHat i l) (s_hat l))
          (y_hat i) j) +
      (∑ i : Fin p.k,
        multiplyNTTs (e_hat i) (y_hat i) j) := by
    funext j; simp only [nttInnerProd]
    rw [← Finset.sum_add_distrib]
    congr 1; ext i
    have : t_hat i = fun idx =>
        (∑ j : Fin p.k, multiplyNTTs (aHat i j) (s_hat j) idx) +
          e_hat i idx := by funext idx; exact h_that i idx
    rw [this]
    rw [congrFun (multiplyNTTs_add_left
      (fun idx => ∑ l, multiplyNTTs (aHat i l) (s_hat l) idx)
      (e_hat i) (y_hat i)) j]
    congr 1
    exact congrFun (multiplyNTTs_finset_sum_left Finset.univ
      (fun l idx => multiplyNTTs (aHat i l) (s_hat l) idx)
      (y_hat i)) j
  -- Step 5: Rewrite inner products and apply invNtt linearity
  rw [h_encrypt, h_decrypt]
  rw [congrFun (invNtt_add _ _) idx, congrFun (invNtt_add _ _) idx]
  -- Signal cancellation
  have h_signal := signal_terms_eq aHat s_hat y_hat
  rw [h_signal]
  -- Distribute invNtt over sums
  have h_inv_ey : invNtt (fun j => ∑ i : Fin p.k,
      multiplyNTTs (e_hat i) (y_hat i) j) idx =
    ∑ i : Fin p.k, invNtt (fun j => multiplyNTTs (e_hat i) (y_hat i) j) idx := by
    exact congrFun (invNtt_finset_sum Finset.univ
      (fun i j => multiplyNTTs (e_hat i) (y_hat i) j)) idx
  have h_inv_se : invNtt (fun j => ∑ i : Fin p.k,
      multiplyNTTs (s_hat i) (ntt (e1 i)) j) idx =
    ∑ i : Fin p.k, invNtt (fun j => multiplyNTTs (s_hat i) (ntt (e1 i)) j) idx :=
    congrFun (invNtt_finset_sum Finset.univ
      (fun i j => multiplyNTTs (s_hat i) (ntt (e1 i)) j)) idx
  rw [h_inv_ey, h_inv_se]
  ring


/-! ## Ciphertext encoding round-trip lemmas -/

/-- **Ciphertext U decode–encode round-trip**: decoding `u` from an encoded
ciphertext recovers `Decompress_{d_u}(Compress_{d_u}(u_i))`.

This follows from `byteDecode ∘ byteEncode = id` on values bounded by `2^{d_u}`,
composed with the index arithmetic of `encodeCiphertext` / `decodeCiphertextU`. -/
lemma decodeCiphertextU_encodeCiphertext {p : ParamSet}
    (u : Fin p.k → (Fin n → Zq)) (v : Fin n → Zq)
    (i : Fin p.k) (idx : Fin n) :
    decodeCiphertextU (encodeCiphertext u v) i idx =
      decompressPoly p.d_u (compressPoly p.d_u (u i)) idx := by
  simp only [decodeCiphertextU, decompressPoly]
  congr 1
  have hd_u := p.hd_u.1
  have hi := i.isLt
  -- The byte array extracted from the ciphertext for polynomial i
  -- equals byteEncode d_u (compressPoly d_u (u i))
  have h_eq_bytes : ∀ (j : Fin (32 * p.d_u)),
      encodeCiphertext u v ⟨32 * p.d_u * i.val + j.val, by
        have hj := j.isLt; simp only [ParamSet.ctSizeEnc]; nlinarith⟩ =
      encodeCompressPoly p.d_u (u i) j := by
    intro j; have hj := j.isLt
    simp only [encodeCiphertext]
    have h_lt : 32 * p.d_u * i.val + j.val < 32 * p.d_u * p.k := by nlinarith
    simp only [h_lt, dite_true, encodeC1, encodeCompressPoly]
    -- Goal: byteEncode p.d_u (compressPoly p.d_u (u ⟨div, _⟩)) ⟨mod, _⟩ =
    --       byteEncode p.d_u (compressPoly p.d_u (u i)) j
    have h0 : 0 < 32 * p.d_u := by omega
    have h_div : (32 * p.d_u * i.val + j.val) / (32 * p.d_u) = i.val := by
      rw [show 32 * p.d_u * i.val = (32 * p.d_u) * i.val from by ring]
      rw [Nat.mul_add_div h0]
      have : j.val / (32 * p.d_u) = 0 := Nat.div_eq_of_lt hj
      omega
    have h_mod : (32 * p.d_u * i.val + j.val) % (32 * p.d_u) = j.val := by
      rw [show 32 * p.d_u * i.val = (32 * p.d_u) * i.val from by ring]
      rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hj
    -- Use Fin.val equality to substitute
    have h1 : (⟨(32 * p.d_u * i.val + j.val) / (32 * p.d_u),
      Nat.div_lt_of_lt_mul (by omega)⟩ : Fin p.k) = i := Fin.ext h_div
    have h2 : (⟨(32 * p.d_u * i.val + j.val) % (32 * p.d_u),
      Nat.mod_lt _ h0⟩ : Fin (32 * p.d_u)) = j := Fin.ext h_mod
    rw [h1, h2]
  conv_lhs => rw [show (fun j => encodeCiphertext u v ⟨32 * p.d_u * i.val + j.val, _⟩) =
    encodeCompressPoly p.d_u (u i) from funext h_eq_bytes]
  simp only [encodeCompressPoly]
  exact byteDecode_byteEncode p.d_u hd_u _
    (fun idx => compress_lt_two_pow p.d_u (u i idx)) idx

/-- **Ciphertext V decode–encode round-trip**: decoding `v` from an encoded
ciphertext recovers `Decompress_{d_v}(Compress_{d_v}(v))`. -/
lemma decodeCiphertextV_encodeCiphertext {p : ParamSet}
    (u : Fin p.k → (Fin n → Zq)) (v : Fin n → Zq)
    (idx : Fin n) :
    decodeCiphertextV (encodeCiphertext u v) idx =
      decompressPoly p.d_v (compressPoly p.d_v v) idx := by
  simp only [decodeCiphertextV, decompressPoly]
  congr 1
  have hd_v := p.hd_v.1
  have h_eq_bytes : ∀ (j : Fin (32 * p.d_v)),
      encodeCiphertext u v ⟨32 * p.d_u * p.k + j.val, by
        have hj := j.isLt; simp only [ParamSet.ctSizeEnc]; omega⟩ =
      encodeCompressPoly p.d_v v j := by
    intro j
    simp only [encodeCiphertext]
    have h_not_lt : ¬ ((32 * p.d_u * p.k + j.val) < 32 * p.d_u * p.k) := by omega
    simp only [h_not_lt, dite_false, encodeC2, encodeCompressPoly]
    congr 1; exact Fin.ext (by grind)
  conv_lhs => rw [show (fun j => encodeCiphertext u v ⟨32 * p.d_u * p.k + j.val, _⟩) =
    encodeCompressPoly p.d_v v from funext h_eq_bytes]
  simp only [encodeCompressPoly]
  exact byteDecode_byteEncode p.d_v hd_v _
    (fun idx => compress_lt_two_pow p.d_v (v idx)) idx

/-! ## Message byte-encoding round-trip -/

/-- **Message encoding round-trip**: `byteEncode 1 (msgBit m) = m`. -/
lemma byteEncode1_msgBit (m : Fin 32 → UInt8) :
    byteEncode 1 (msgBit m) = m := by
  -- Show coeffsToBits 1 (msgBit m) = bytesToBits m
  suffices h_bits : coeffsToBits 1 (msgBit m) = bytesToBits m by
    simp only [byteEncode]; rw [h_bits, bitsToBytes_bytesToBits]
  funext idx
  simp only [coeffsToBits, bytesToBits, msgBit, intBit, extractBit,
    Nat.div_one, Nat.mod_one, pow_zero, Nat.shiftRight_eq_div_pow]
  ext
  -- Goal: ⟨((m[idx/8].toNat / 2^(idx%8)) &&& 1) % 2, _⟩ =
  --       ⟨(m[idx/8].toNat / 2^(idx%8)) % 2, _⟩
  simp only [Nat.and_one_is_mod]; omega

/-- **Message recovery**: if `compress 1 (w idx) = msgBit m idx` for every
coefficient, then `recoverMsg w = m`. -/
lemma recoverMsg_of_compress_eq (w : Fin n → Zq) (m : Fin 32 → UInt8)
    (h : ∀ idx : Fin n, compress 1 (w idx) = msgBit m idx) :
    recoverMsg w = m := by
  simp only [recoverMsg]
  have h_eq : compressPoly 1 w = msgBit m := funext h
  rw [h_eq]; exact byteEncode1_msgBit m

/-! ## Key encoding round-trips

The `ByteEncode₁₂ / ByteDecode₁₂` pair is the identity on `ℤ_q` (since
`q < 2¹²`), so every component of a generated key pair is recoverable. -/

/-- Byte `384·i + j` of `encodeDk s_hat` is byte `j` of `encodePoly12 (s_hat i)`. -/
private lemma encodeDk_byte {p : ParamSet} (s_hat : Fin p.k → (Fin n → Zq))
    (i : Fin p.k) (j : Fin (32 * 12)) :
    encodeDk s_hat ⟨384 * i.val + j.val, by
      have hi := i.isLt; have hj := j.isLt; omega⟩ = encodePoly12 (s_hat i) j := by
  have hj := j.isLt
  simp only [encodeDk]
  have h_div : (384 * i.val + j.val) / 384 = i.val := by omega
  have h_mod : (384 * i.val + j.val) % 384 = j.val := by omega
  have h1 : (⟨(384 * i.val + j.val) / 384, by omega⟩ : Fin p.k) = i := Fin.ext h_div
  have h2 : (⟨(384 * i.val + j.val) % 384, by omega⟩ : Fin 384).cast encode12_size.symm
      = j := Fin.ext h_mod
  rw [h1, h2]

/-- Byte `384·i + j` of `encodeEk t_hat ρ` is byte `j` of `encodePoly12 (t_hat i)`. -/
private lemma encodeEk_byte {p : ParamSet} (t_hat : Fin p.k → (Fin n → Zq))
    (ρ : Fin 32 → UInt8) (i : Fin p.k) (j : Fin (32 * 12)) :
    encodeEk t_hat ρ ⟨384 * i.val + j.val, by
      have hi := i.isLt; have hj := j.isLt; omega⟩ = encodePoly12 (t_hat i) j := by
  have hj := j.isLt
  have hi := i.isLt
  have h_lt : 384 * i.val + j.val < 384 * p.k := by
    calc 384 * i.val + j.val < 384 * i.val + 384 := by omega
      _ = 384 * (i.val + 1) := by ring
      _ ≤ 384 * p.k := Nat.mul_le_mul_left _ (by omega)
  simp only [encodeEk, h_lt, dite_true]
  have h_div : (384 * i.val + j.val) / 384 = i.val := by omega
  have h_mod : (384 * i.val + j.val) % 384 = j.val := by omega
  have h1 : (⟨(384 * i.val + j.val) / 384, by omega⟩ : Fin p.k) = i := Fin.ext h_div
  have h2 : (⟨(384 * i.val + j.val) % 384, by omega⟩ : Fin 384).cast encode12_size.symm
      = j := Fin.ext h_mod
  rw [h1, h2]

/-- **Decryption key round-trip**: `decodeDkSHat (encodeDk ŝ) = ŝ`. -/
lemma decodeDkSHat_encodeDk {p : ParamSet} (s_hat : Fin p.k → (Fin n → Zq)) :
    decodeDkSHat (encodeDk s_hat) = s_hat := by
  funext i idx
  simp only [decodeDkSHat, decodeDkPoly]
  have h_bytes : (fun j : Fin (32 * 12) => encodeDk s_hat ⟨384 * i.val + j.val, by
      have hi := i.isLt; have hj := j.isLt; omega⟩) = byteEncodeZq 12 (s_hat i) :=
    funext fun j => encodeDk_byte s_hat i j
  rw [h_bytes]
  exact byteDecodeZq_byteEncodeZq_12 (s_hat i) idx

/-- **Encryption key round-trip (t̂ part)**: `decodeEkTHat (encodeEk t̂ ρ) = t̂`. -/
lemma decodeEkTHat_encodeEk {p : ParamSet} (t_hat : Fin p.k → (Fin n → Zq))
    (ρ : Fin 32 → UInt8) :
    decodeEkTHat (encodeEk t_hat ρ) = t_hat := by
  funext i idx
  simp only [decodeEkTHat, decodeEkPoly]
  have h_bytes : (fun j : Fin (32 * 12) => encodeEk t_hat ρ ⟨384 * i.val + j.val, by
      have hi := i.isLt; have hj := j.isLt; omega⟩) = byteEncodeZq 12 (t_hat i) :=
    funext fun j => encodeEk_byte t_hat ρ i j
  rw [h_bytes]
  exact byteDecodeZq_byteEncodeZq_12 (t_hat i) idx

/-- **Encryption key round-trip (ρ part)**: `decodeEkRho (encodeEk t̂ ρ) = ρ`. -/
lemma decodeEkRho_encodeEk {p : ParamSet} (t_hat : Fin p.k → (Fin n → Zq))
    (ρ : Fin 32 → UInt8) :
    decodeEkRho (encodeEk t_hat ρ) = ρ := by
  funext i
  have hi := i.isLt
  have h_not : ¬ (384 * p.k + i.val < 384 * p.k) := by omega
  simp only [decodeEkRho, encodeEk, h_not, dite_false]
  congr 1
  exact Fin.ext (by simp)

/-- The NTT-domain secret `ŝ` is recoverable from the generated decryption key. -/
lemma decodeDkSHat_kpkeKeyGen (d : Fin 32 → UInt8) (p : ParamSet) :
    decodeDkSHat (kpkeKeyGen d p).dk = nttVec (genSecret (sigma d p) p) :=
  decodeDkSHat_encodeDk _

/-- The NTT-domain public value `t̂ = Â∘ŝ + ê` is recoverable from the
generated encryption key. -/
lemma decodeEkTHat_kpkeKeyGen (d : Fin 32 → UInt8) (p : ParamSet) :
    decodeEkTHat (kpkeKeyGen d p).ek =
      computeTHat (genMatrixA (rho d p) p)
        (nttVec (genSecret (sigma d p) p)) (nttVec (genError (sigma d p) p)) :=
  decodeEkTHat_encodeEk _ _

/-- The public seed `ρ` is recoverable from the generated encryption key. -/
lemma decodeEkRho_kpkeKeyGen (d : Fin 32 → UInt8) (p : ParamSet) :
    decodeEkRho (kpkeKeyGen d p).ek = rho d p :=
  decodeEkRho_encodeEk _ _

/-! ## The decryption polynomial `w` as an explicit function of the seeds

To keep elaboration cheap, the honest ciphertext and the polynomial `w`
recovered by `kpkeDecrypt` are named once, and every unfolding step is a
separate rewriting lemma. -/

/-- The ciphertext polynomial `u` (before compression) for seeds `(d, r)`. -/
def honestU (d r : Fin 32 → UInt8) (p : ParamSet) : Fin p.k → (Fin n → Zq) :=
  computeU (genMatrixAT (rho d p) p) (nttVec (genEncSecret r p)) (genEncError1 r p)

/-- The ciphertext polynomial `v` (before compression) for seeds `(d, m, r)`. -/
def honestV (d m r : Fin 32 → UInt8) (p : ParamSet) : Fin n → Zq :=
  computeV
    (computeTHat (genMatrixA (rho d p) p)
      (nttVec (genSecret (sigma d p) p)) (nttVec (genError (sigma d p) p)))
    (nttVec (genEncSecret r p)) (genEncError2 r p) (decompressMsg m)

/-- The polynomial `w = v' − NTT⁻¹(ŝᵀ ∘ NTT(u'))` computed by `kpkeDecrypt` on an
honestly generated ciphertext, with `u', v'` the compress/decompress images. -/
def honestW (d m r : Fin 32 → UInt8) (p : ParamSet) : Fin n → Zq :=
  computeW
    (decompressPoly p.d_v (compressPoly p.d_v (honestV d m r p)))
    (nttVec (genSecret (sigma d p) p))
    (fun i => decompressPoly p.d_u (compressPoly p.d_u (honestU d r p i)))

/-- `kpkeEncrypt` on a generated key produces `encodeCiphertext honestU honestV`. -/
lemma kpkeEncrypt_kpkeKeyGen_ct (d m r : Fin 32 → UInt8) (p : ParamSet) :
    (kpkeEncrypt p (kpkeKeyGen d p).ek m r).ct =
      encodeCiphertext (honestU d r p) (honestV d m r p) := by
  simp only [kpkeEncrypt, honestU, honestV]
  rw [decodeEkTHat_kpkeKeyGen, decodeEkRho_kpkeKeyGen]

/-- `kpkeDecrypt` on a generated key and an honest ciphertext is
`recoverMsg honestW`. -/
lemma kpkeDecrypt_kpkeKeyGen (d m r : Fin 32 → UInt8) (p : ParamSet) :
    kpkeDecrypt p (kpkeKeyGen d p).dk (kpkeEncrypt p (kpkeKeyGen d p).ek m r).ct =
      recoverMsg (honestW d m r p) := by
  rw [kpkeEncrypt_kpkeKeyGen_ct]
  have hv : decodeCiphertextV (encodeCiphertext (honestU d r p) (honestV d m r p)) =
      decompressPoly p.d_v (compressPoly p.d_v (honestV d m r p)) :=
    funext (decodeCiphertextV_encodeCiphertext _ _)
  have hu : (fun i => decodeCiphertextU
      (encodeCiphertext (honestU d r p) (honestV d m r p)) i) =
      fun i => decompressPoly p.d_u (compressPoly p.d_u (honestU d r p i)) :=
    funext fun i => funext (decodeCiphertextU_encodeCiphertext _ _ i)
  change recoverMsg (computeW
      (decodeCiphertextV (encodeCiphertext (honestU d r p) (honestV d m r p)))
      (decodeDkSHat (kpkeKeyGen d p).dk)
      (fun i => decodeCiphertextU
        (encodeCiphertext (honestU d r p) (honestV d m r p)) i)) = _
  rw [hv, hu, decodeDkSHat_kpkeKeyGen]
  rfl

/-- Each message bit is `0` or `1`. -/
lemma msgBit_lt_two (m : Fin 32 → UInt8) (i : Fin n) : msgBit m i < 2 := by
  unfold msgBit
  have := Nat.and_le_right (n := (m ⟨i.val / 8, by
    have := i.isLt; unfold n at *; omega⟩).toNat >>> (i.val % 8)) (m := 1)
  omega

/-! ## Main round-trip theorem -/

/-- **K-PKE round-trip correctness** (FIPS 203, §§ 5.1–5.3):

  `kpkeDecrypt(dk, kpkeEncrypt(ek, m, r).ct) = m`   for `(ek, dk) = kpkeKeyGen d`

under the single hypothesis that the total noise (algebraic + compression) is
bounded by `⌊q/4⌋` at every coefficient, i.e. `|honestW − Decompress₁(m)| < 832`.

The key round-trips (`decodeDkSHat_kpkeKeyGen`, `decodeEkTHat_kpkeKeyGen`,
`decodeEkRho_kpkeKeyGen`) and the ciphertext round-trips are theorems, not
hypotheses.  The proof:
1. `kpkeDecrypt_kpkeKeyGen` rewrites the left-hand side to `recoverMsg honestW`;
2. `recoverMsg_of_compress_eq` reduces to `compress 1 (w idx) = msgBit m idx`;
3. writing `w idx = decompress 1 (msgBit m idx) + noise`,
   `compress1_decompress1_stable` closes the goal.

**Source**: NIST FIPS 203, §§ 5.1–5.3 -/
theorem kpke_roundTrip (p : ParamSet) (d m r : Fin 32 → UInt8)
    (h_noise : ∀ idx : Fin n,
      absZq (honestW d m r p idx - decompressMsg m idx) < q / 4) :
    kpkeDecrypt p (kpkeKeyGen d p).dk (kpkeEncrypt p (kpkeKeyGen d p).ek m r).ct = m := by
  rw [kpkeDecrypt_kpkeKeyGen]
  apply recoverMsg_of_compress_eq
  intro idx
  have hw : honestW d m r p idx =
      decompress 1 (msgBit m idx) + (honestW d m r p idx - decompressMsg m idx) := by
    simp [decompressMsg]
  rw [hw]
  exact compress1_decompress1_stable (msgBit m idx) _ (msgBit_lt_two m idx) (h_noise idx)

/-- **K-PKE round-trip for an arbitrary consistent key pair**: the same
statement for any `kp` with `kp = kpkeKeyGen d p`. -/
theorem kpke_roundTrip_of_consistent (p : ParamSet) (d m r : Fin 32 → UInt8)
    (kp : KpkeKeyPair p) (h_kp : kp = kpkeKeyGen d p)
    (h_noise : ∀ idx : Fin n,
      absZq (honestW d m r p idx - decompressMsg m idx) < q / 4) :
    kpkeDecrypt p kp.dk (kpkeEncrypt p kp.ek m r).ct = m := by
  subst h_kp; exact kpke_roundTrip p d m r h_noise

/-- **K-PKE round-trip, `ConsistentKeyPair` / `noiseBoundedAt` form.** -/
theorem kpke_roundTrip' {p : ParamSet} (ckp : ConsistentKeyPair p)
    (m r : Fin 32 → UInt8)
    (h_noise : noiseBoundedAt
      (fun idx => honestW ckp.d m r p idx - decompressMsg m idx)) :
    kpkeDecrypt p ckp.kp.dk (kpkeEncrypt p ckp.kp.ek m r).ct = m :=
  kpke_roundTrip_of_consistent p ckp.d m r ckp.kp ckp.hkp h_noise

/-! ## Corollary: ML-KEM-768 instantiation -/

/-- **ML-KEM-768 round-trip correctness**: specialisation of `kpke_roundTrip`
to the ML-KEM-768 parameter set used by SPQR. -/
theorem kpke_roundTrip_768 (d m r : Fin 32 → UInt8)
    (h_noise : ∀ idx : Fin n,
      absZq (honestW d m r mlkem768 idx - decompressMsg m idx) < q / 4) :
    kpkeDecrypt mlkem768 (kpkeKeyGen d mlkem768).dk
      (kpkeEncrypt mlkem768 (kpkeKeyGen d mlkem768).ek m r).ct = m :=
  kpke_roundTrip mlkem768 d m r h_noise

/-! ## Noise bound constants for ML-KEM-768 -/

/-- The decryption threshold for `Compress₁`: `⌊q/4⌋ = 832`. -/
theorem q_div_4_eq : q / 4 = 832 := by norm_num [q]

/-- For ML-KEM-768, `η₁ = η₂ = 2`. -/
theorem mlkem768_eta_bound : mlkem768.η₁ = 2 ∧ mlkem768.η₂ = 2 := by
  simp [mlkem768]

end Fips203
