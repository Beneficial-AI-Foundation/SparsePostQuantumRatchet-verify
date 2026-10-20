/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module
public import Spqr.Crypto.Fips203.KEM.Encaps
public import Spqr.Crypto.Fips203.PKE.Decrypt
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

`ML-KEM.Decaps` (Algorithm 21) is `Decaps_internal` after the input validation of § 7.3,
which consists of two checks:

* **Length checks** — `dk` has `768·k + 96` bytes and `c` has `32·(d_u·k + d_v)` bytes.
  These are enforced here by the dependent types `Fin p.dkSize → UInt8` and
  `Fin p.ctSizeEnc → UInt8`.
* **Hash check** — `H(dk[384k : 768k+32]) = dk[768k+32 : 768k+64]`, i.e. the `h` segment
  stored in `dk` must be the hash of the embedded `ekPKE`.  This check is **not** modelled:
  this file defines only `Decaps_internal`, and the libcrux function it is used to specify
  (`incremental::decapsulate_compressed_key`) does not perform the hash check either, so
  `mlkemDecaps` is applied to every well-sized `dk`.  Modelling the check would make the
  specification stricter than the code it describes.

**Source**: NIST FIPS 203, § 6.3 (Algorithm 18)
-/

@[expose] public section

noncomputable section

namespace Fips203

/-! ## Hash function `J`

`J` (SHAKE-256, 32 bytes) is the field `J` of a `Primitives` record (`Primitives.lean`), taken
as the explicit argument `prims` by every definition below that depends on it. -/

variable (prims : Primitives)

/-- Implicit-rejection key `K̄ = J(z ‖ c)`. -/
def rejectionKey {p : ParamSet} (z : Fin 32 → UInt8) (c : Fin p.ctSizeEnc → UInt8) :
    Fin 32 → UInt8 :=
  prims.J (List.ofFn z ++ List.ofFn c)

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
  let K'    := sharedKey prims m' h
  let r'    := encRandomness prims m' h
  let Kbar  := rejectionKey prims z c
  let c'    := (kpkeEncrypt prims p ekPke m' r').ct
  if c = c' then K' else Kbar

/-! ## Elementary properties -/

/-- When the re-encryption check succeeds, `Decaps` returns `G(m' ‖ h)`'s first half. -/
theorem mlkemDecaps_of_reencrypt_eq (p : ParamSet) (dk : Fin p.dkSize → UInt8)
    (c : Fin p.ctSizeEnc → UInt8)
    (h_eq : c = (kpkeEncrypt prims p (decodeDkEk dk) (kpkeDecrypt p (decodeDkPke dk) c)
      (encRandomness prims (kpkeDecrypt p (decodeDkPke dk) c) (decodeDkH dk))).ct) :
    mlkemDecaps prims p dk c =
      sharedKey prims (kpkeDecrypt p (decodeDkPke dk) c) (decodeDkH dk) := by
  unfold mlkemDecaps
  rw [ite_eq_left h_eq]

/-- When the re-encryption check fails, `Decaps` returns the implicit-rejection key. -/
theorem mlkemDecaps_of_reencrypt_ne (p : ParamSet) (dk : Fin p.dkSize → UInt8)
    (c : Fin p.ctSizeEnc → UInt8)
    (h_ne : c ≠ (kpkeEncrypt prims p (decodeDkEk dk) (kpkeDecrypt p (decodeDkPke dk) c)
      (encRandomness prims (kpkeDecrypt p (decodeDkPke dk) c) (decodeDkH dk))).ct) :
    mlkemDecaps prims p dk c = rejectionKey prims (decodeDkZ dk) c := by
  unfold mlkemDecaps
  rw [ite_eq_right h_ne]

end Fips203
