/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module
public import Spqr.Crypto.Fips203.KEM.Encaps
/-!
# FIPS 203 Algorithm 17, split into libcrux's two incremental rounds

libcrux-ml-kem's incremental API (`src/ind_cca/incremental.rs`) computes `ML-KEM.Encaps_internal`
in two rounds, so that the ciphertext can be started knowing only the *header*
`pk1 = ρ ‖ H(ek)` and finished later once the serialised `t̂` (`pk2`) arrives:

* **Round 1** (`encapsulate1(pk1, m)`): `(K, r) ← G(m ‖ H(ek))`, re-derive `Â` from `ρ`, sample
  `y, e₁, e₂` from `r`, and output the shared secret `K`, the first ciphertext half
  `c₁ = ByteEncode_{d_u}(Compress_{d_u}(NTT⁻¹(Âᵀ ∘ ŷ) + e₁))`, and a *state*
  `(ŷ, e₂, m)` to be consumed by round 2.
* **Round 2** (`encapsulate2(state, pk2)`): decode `t̂` from `pk2` and output
  `c₂ = ByteEncode_{d_v}(Compress_{d_v}(NTT⁻¹(t̂ᵀ ∘ ŷ) + e₂ + Decompress₁(m)))`.

This file defines both rounds as pure functions of the FIPS 203 ingredients and proves that they
compose to Algorithm 17 (`mlkemEncaps`): the shared secret of round 1 is `(mlkemEncaps ek m).ss`
and `c₁ ‖ c₂` is `(mlkemEncaps ek m).ct`.  The byte-level serialisation of the state and the
refinement to the Aeneas externals live in `Spqr/Crypto/Fips203/Refinement/`.

**Sources**: NIST FIPS 203, § 5.2 (Algorithm 14) and § 6.2 (Algorithm 17);
libcrux-ml-kem 0.0.7, `src/ind_cca/incremental.rs` (`encapsulate1`, `encapsulate2`) and
`src/ind_cpa.rs` (`encrypt_c1`, `encrypt_c2`).
-/

@[expose] public section

noncomputable section

namespace Fips203

variable (prims : Primitives)

/-! ## The header `pk1 = ρ ‖ H(ek)` -/

/-- The 64-byte libcrux header: the matrix seed `ρ` followed by `H(ek)`. -/
structure EncapsHeader where
  /-- Matrix seed `ρ = ek[384·k : 384·k + 32]`. -/
  ρ : Fin 32 → UInt8
  /-- Hash of the encapsulation key `H(ek)`. -/
  h : Fin 32 → UInt8

/-- The header of a FIPS 203 encapsulation key. -/
def headerOfEk {p : ParamSet} (ek : Fin (384 * p.k + 32) → UInt8) : EncapsHeader :=
  { ρ := decodeEkRho ek, h := hashEk prims ek }

/-! ## The round-1 state `(ŷ, e₂, m)` -/

/-- The data round 1 hands to round 2 (libcrux `EncapsState { r_as_ntt, error2, randomness }`). -/
structure EncapsState (p : ParamSet) where
  /-- `ŷ = NTT(y)`, the NTT-domain encryption secret. -/
  yHat : Fin p.k → (Fin n → Zq)
  /-- The error polynomial `e₂`. -/
  e2 : Fin n → Zq
  /-- The 32-byte message `m` (libcrux: `randomness`). -/
  m : Fin 32 → UInt8

/-! ## Round 1 -/

/-- The output of round 1: the shared secret, the first ciphertext half and the state. -/
structure EncapsPhase1Output (p : ParamSet) where
  /-- Shared secret `K`. -/
  ss : Fin 32 → UInt8
  /-- First ciphertext half `c₁` of `32 · d_u · k` bytes. -/
  ct1 : Fin (32 * p.compressionU * p.k) → UInt8
  /-- The state `(ŷ, e₂, m)` for round 2. -/
  state : EncapsState p

/-- The vector `u = NTT⁻¹(Âᵀ ∘ ŷ) + e₁` computed from the header and the encryption
randomness `r`. -/
def encapsU (p : ParamSet) (ρ : Fin 32 → UInt8) (r : Fin 32 → UInt8) :
    Fin p.k → (Fin n → Zq) :=
  computeU (genMatrixAT prims ρ p) (nttVec (genEncSecret prims r p)) (genEncError1 prims r p)

/-- **Round 1 of incremental encapsulation** (libcrux `encapsulate1`).

From the header `ρ ‖ h` and the message `m`: derive `(K, r) = G(m ‖ h)`, compute `c₁` from `ρ`
and `r`, and keep `(ŷ, e₂, m)` for round 2. -/
def mlkemEncapsPhase1 (p : ParamSet) (hdr : EncapsHeader) (m : Fin 32 → UInt8) :
    EncapsPhase1Output p :=
  let K := sharedKey prims m hdr.h
  let r := encRandomness prims m hdr.h
  { ss := K
    ct1 := encodeC1 (encapsU prims p hdr.ρ r)
    state := { yHat := nttVec (genEncSecret prims r p), e2 := genEncError2 prims r p, m := m } }

/-! ## Round 2 -/

/-- **Round 2 of incremental encapsulation** (libcrux `encapsulate2`).

From the state `(ŷ, e₂, m)` and the NTT-domain public vector `t̂`, output
`c₂ = ByteEncode_{d_v}(Compress_{d_v}(NTT⁻¹(t̂ᵀ ∘ ŷ) + e₂ + Decompress₁(m)))`. -/
def mlkemEncapsPhase2 (p : ParamSet) (st : EncapsState p) (tHat : Fin p.k → (Fin n → Zq)) :
    Fin (32 * p.compressionV) → UInt8 :=
  encodeC2 (computeV tHat st.yHat st.e2 (decompressMsg st.m))

/-! ## Composition: the two rounds compute Algorithm 17 -/

/-- Round 1 on the header of `ek` returns the shared secret of `ML-KEM.Encaps_internal(ek, m)`. -/
theorem mlkemEncapsPhase1_ss (p : ParamSet) (ek : Fin (384 * p.k + 32) → UInt8)
    (m : Fin 32 → UInt8) :
    (mlkemEncapsPhase1 prims p (headerOfEk prims ek) m).ss = (mlkemEncaps prims p ek m).ss :=
  rfl

/-- The state of round 1 records the message. -/
theorem mlkemEncapsPhase1_state_m (p : ParamSet) (hdr : EncapsHeader) (m : Fin 32 → UInt8) :
    (mlkemEncapsPhase1 prims p hdr m).state.m = m := rfl

/-- The first ciphertext half of round 1 on the header of `ek` is the `c₁` part of the
ciphertext of `ML-KEM.Encaps_internal(ek, m)`. -/
theorem mlkemEncapsPhase1_ct1 (p : ParamSet) (ek : Fin (384 * p.k + 32) → UInt8)
    (m : Fin 32 → UInt8) (i : Fin (32 * p.compressionU * p.k)) :
    (mlkemEncapsPhase1 prims p (headerOfEk prims ek) m).ct1 i =
      (mlkemEncaps prims p ek m).ct ⟨i.val, by
        have := i.isLt; unfold ParamSet.ctSizeEnc; omega⟩ := by
  simp only [mlkemEncapsPhase1, headerOfEk, mlkemEncaps, kpkeEncrypt, encodeCiphertext,
    encapsU]
  rw [dite_eq_left i.isLt]

/-- Round 2 on the state of round 1 is the `c₂` part of the ciphertext of
`ML-KEM.Encaps_internal(ek, m)`. -/
theorem mlkemEncapsPhase2_ct2 (p : ParamSet) (ek : Fin (384 * p.k + 32) → UInt8)
    (m : Fin 32 → UInt8) (i : Fin (32 * p.compressionV)) :
    mlkemEncapsPhase2 p (mlkemEncapsPhase1 prims p (headerOfEk prims ek) m).state
        (decodeEkTHat ek) i =
      (mlkemEncaps prims p ek m).ct ⟨32 * p.compressionU * p.k + i.val, by
        have := i.isLt; unfold ParamSet.ctSizeEnc; omega⟩ := by
  simp only [mlkemEncapsPhase2, mlkemEncapsPhase1, headerOfEk, mlkemEncaps, kpkeEncrypt,
    encodeCiphertext]
  rw [dite_eq_right (by omega)]
  exact congrArg _ (Fin.ext (by simp only; omega))

/-- **Composition.**  `c₁ ‖ c₂` of the two rounds is exactly the ciphertext of Algorithm 17. -/
theorem mlkemEncaps_ct_eq_phases (p : ParamSet) (ek : Fin (384 * p.k + 32) → UInt8)
    (m : Fin 32 → UInt8) (idx : Fin p.ctSizeEnc) :
    (mlkemEncaps prims p ek m).ct idx =
      if h : idx.val < 32 * p.compressionU * p.k then
        (mlkemEncapsPhase1 prims p (headerOfEk prims ek) m).ct1 ⟨idx.val, h⟩
      else
        mlkemEncapsPhase2 p (mlkemEncapsPhase1 prims p (headerOfEk prims ek) m).state
          (decodeEkTHat ek)
          ⟨idx.val - 32 * p.compressionU * p.k, by
            have := idx.isLt; unfold ParamSet.ctSizeEnc at this; omega⟩ := by
  by_cases h : idx.val < 32 * p.compressionU * p.k
  · rw [dite_eq_left h, mlkemEncapsPhase1_ct1]
  · rw [dite_eq_right h, mlkemEncapsPhase2_ct2]
    exact congrArg _ (Fin.ext (by simp only; omega))

/-- For ML-KEM-768, `c₁` has `960` bytes and `c₂` has `128` bytes. -/
theorem encapsPhase_sizes_768 :
    32 * mlkem768.compressionU * mlkem768.k = 960 ∧ 32 * mlkem768.compressionV = 128 := by
  simp only [mlkem768CompressionU, mlkem768_k, mlkem768CompressionV, and_self]

end Fips203
