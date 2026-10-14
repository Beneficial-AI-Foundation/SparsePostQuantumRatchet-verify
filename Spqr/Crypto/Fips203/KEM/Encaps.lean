/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module
public import Spqr.Crypto.Fips203.KEM.KeyGen
public import Spqr.Crypto.Fips203.PKE.Encrypt
/-!
# FIPS 203 Algorithm 17: `ML-KEM.Encaps_internal(ek, m)`

NIST FIPS 203 (ML-KEM, August 2024), § 6.2, defines the internal KEM encapsulation
algorithm.  Given an encapsulation key `ek` and a 32-byte random message `m`, it produces
a 32-byte shared secret `K` and a ciphertext `c`.

The algorithm:

1. `(K, r) ← G(m ‖ H(ek))` — 64 bytes split into the shared secret and the encryption
   randomness.
2. `c ← K-PKE.Encrypt(ek, m, r)`.
3. Return `(K, c)`.

`ML-KEM.Encaps` (Algorithm 20) is `Encaps_internal` applied to fresh random `m`; since
randomness is a parameter in this development, Algorithm 17 is the top-level definition.

**Source**: NIST FIPS 203, § 6.2 (Algorithm 17)
-/

@[expose] public section

noncomputable section

namespace Fips203

/-! ## Key derivation `(K, r) = G(m ‖ h)` -/

/-- The 64-byte input `m ‖ h` to `G`. -/
def gInput (m h : Fin 32 → UInt8) : List UInt8 :=
  List.ofFn m ++ List.ofFn h

/-- Shared secret `K`: the first 32 bytes of `G(m ‖ h)`. -/
def sharedKey (m h : Fin 32 → UInt8) : Fin 32 → UInt8 :=
  fun i => hashG (gInput m h) ⟨i.val, by omega⟩

/-- Encryption randomness `r`: the last 32 bytes of `G(m ‖ h)`. -/
def encRandomness (m h : Fin 32 → UInt8) : Fin 32 → UInt8 :=
  fun i => hashG (gInput m h) ⟨32 + i.val, by omega⟩

/-! ## ML-KEM.Encaps_internal — top-level definition -/

/-- The output of `ML-KEM.Encaps_internal`: a shared secret and a ciphertext. -/
structure MlkemEncapsOutput (p : ParamSet) where
  /-- Shared secret `K` of 32 bytes. -/
  ss : Fin 32 → UInt8
  /-- Ciphertext `c` of size `32 · (d_u · k + d_v)` bytes. -/
  ct : Fin p.ctSizeEnc → UInt8

/-- **Algorithm 17 — `ML-KEM.Encaps_internal(ek, m)`** (FIPS 203, § 6.2).

Given an encapsulation key `ek` (of size `384 · k + 32` bytes) and a 32-byte message `m`,
produces the shared secret `K` and the ciphertext `c`. -/
def mlkemEncaps (p : ParamSet) (ek : Fin (384 * p.k + 32) → UInt8)
    (m : Fin 32 → UInt8) : MlkemEncapsOutput p :=
  let h := hashEk ek
  let K := sharedKey m h
  let r := encRandomness m h
  { ss := K
    ct := (kpkeEncrypt p ek m r).ct }

/-! ## Elementary properties -/

/-- The shared secret is the first half of `G(m ‖ H(ek))`. -/
theorem mlkemEncaps_ss (p : ParamSet) (ek : Fin (384 * p.k + 32) → UInt8)
    (m : Fin 32 → UInt8) :
    (mlkemEncaps p ek m).ss = sharedKey m (hashEk ek) := rfl

/-- The ciphertext is `K-PKE.Encrypt(ek, m, r)` with `r` the second half of `G(m ‖ H(ek))`. -/
theorem mlkemEncaps_ct (p : ParamSet) (ek : Fin (384 * p.k + 32) → UInt8)
    (m : Fin 32 → UInt8) :
    (mlkemEncaps p ek m).ct = (kpkeEncrypt p ek m (encRandomness m (hashEk ek))).ct := rfl

/-- For ML-KEM-768, the ciphertext has `1088` bytes and the shared secret `32` bytes. -/
theorem mlkemEncaps_sizes_768 :
    mlkem768.ctSizeEnc = 1088 ∧ mlkem768.ssSize = 32 :=
  ⟨kpkeEncrypt_ct_size_768, mlkem768_ssSize⟩

end Fips203
