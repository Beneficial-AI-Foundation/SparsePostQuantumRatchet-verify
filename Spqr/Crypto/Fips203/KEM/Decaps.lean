/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Crypto.Fips203.KEM.Encaps
import Spqr.Crypto.Fips203.PKE.Decrypt
/-!
# FIPS 203 Algorithm 18: `ML-KEM.Decaps_internal(dk, c)`

NIST FIPS 203 (ML-KEM, August 2024), § 6.3, defines the internal KEM decapsulation
algorithm.  Given a decapsulation key `dk` and a ciphertext `c`, it produces a 32-byte
shared secret `K'`, using the Fujisaki–Okamoto transform with **implicit rejection**.

The algorithm:

1. Parse `dk = dkPKE ‖ ekPKE ‖ h ‖ z`.
2. `m' ← K-PKE.Decrypt(dkPKE, c)`.
3. `(K', r') ← G(m' ‖ h)`.
4. `K̄ ← J(z ‖ c)` — the implicit-rejection key.
5. `c' ← K-PKE.Encrypt(ekPKE, m', r')`.
6. If `c ≠ c'` then `K' ← K̄`.
7. Return `K'`.

`ML-KEM.Decaps` (Algorithm 21) is `Decaps_internal` after input validation; the validation
concerns only byte lengths, which are enforced here by the dependent types.

**Source**: NIST FIPS 203, § 6.3 (Algorithm 18)
-/

noncomputable section

namespace Fips203

/-! ## Hash function `J` (axiomatised)

`J` is SHAKE-256 producing 32 bytes.  Axiomatised as an opaque oracle like `hashG`. -/

/-- `J(input)` — SHAKE-256 producing 32 bytes. -/
opaque hashJ (input : List UInt8) : Fin 32 → UInt8

/-- Implicit-rejection key `K̄ = J(z ‖ c)`. -/
def rejectionKey {p : ParamSet} (z : Fin 32 → UInt8) (c : Fin p.ctSizeEnc → UInt8) :
    Fin 32 → UInt8 :=
  hashJ (List.ofFn z ++ List.ofFn c)

/-! ## ML-KEM.Decaps_internal — top-level definition -/

/-- **Algorithm 18 — `ML-KEM.Decaps_internal(dk, c)`** (FIPS 203, § 6.3).

Given a decapsulation key `dk` (of size `768 · k + 96` bytes) and a ciphertext `c`
(of size `32 · (d_u · k + d_v)` bytes), produces the 32-byte shared secret.  If the
re-encryption check fails, the implicit-rejection key `J(z ‖ c)` is returned instead. -/
def mlkemDecaps (p : ParamSet) (dk : Fin p.dkSize → UInt8)
    (c : Fin p.ctSizeEnc → UInt8) : Fin 32 → UInt8 :=
  let dkPke := decodeDkPke dk
  let ekPke := decodeDkEk dk
  let h     := decodeDkH dk
  let z     := decodeDkZ dk
  let m'    := kpkeDecrypt p dkPke c
  let K'    := sharedKey m' h
  let r'    := encRandomness m' h
  let Kbar  := rejectionKey z c
  let c'    := (kpkeEncrypt p ekPke m' r').ct
  if c = c' then K' else Kbar

/-! ## Elementary properties -/

/-- When the re-encryption check succeeds, `Decaps` returns `G(m' ‖ h)`'s first half. -/
theorem mlkemDecaps_of_reencrypt_eq (p : ParamSet) (dk : Fin p.dkSize → UInt8)
    (c : Fin p.ctSizeEnc → UInt8)
    (h_eq : c = (kpkeEncrypt p (decodeDkEk dk) (kpkeDecrypt p (decodeDkPke dk) c)
      (encRandomness (kpkeDecrypt p (decodeDkPke dk) c) (decodeDkH dk))).ct) :
    mlkemDecaps p dk c = sharedKey (kpkeDecrypt p (decodeDkPke dk) c) (decodeDkH dk) := by
  unfold mlkemDecaps
  rw [if_pos h_eq]

/-- When the re-encryption check fails, `Decaps` returns the implicit-rejection key. -/
theorem mlkemDecaps_of_reencrypt_ne (p : ParamSet) (dk : Fin p.dkSize → UInt8)
    (c : Fin p.ctSizeEnc → UInt8)
    (h_ne : c ≠ (kpkeEncrypt p (decodeDkEk dk) (kpkeDecrypt p (decodeDkPke dk) c)
      (encRandomness (kpkeDecrypt p (decodeDkPke dk) c) (decodeDkH dk))).ct) :
    mlkemDecaps p dk c = rejectionKey (decodeDkZ dk) c := by
  unfold mlkemDecaps
  rw [if_neg h_ne]

end Fips203
