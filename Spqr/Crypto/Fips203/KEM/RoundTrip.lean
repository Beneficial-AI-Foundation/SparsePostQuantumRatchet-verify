/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Crypto.Fips203.KEM.Decaps
import Spqr.Crypto.Fips203.PKE.RoundTrip
/-!
# FIPS 203 ML-KEM Round-Trip Correctness: `Decaps(dk, Encaps(ek, m).c) = Encaps(ek, m).K`

NIST FIPS 203 (ML-KEM, August 2024), § 6, defines the KEM from `K-PKE` via the
Fujisaki–Okamoto transform.  Its correctness property is:

  **`mlkemDecaps dk (mlkemEncaps ek m).ct = (mlkemEncaps ek m).ss`**

for `(ek, dk) = mlkemKeyGen d z`, whenever the underlying `K-PKE` round trip succeeds
on `m` with the derived randomness `r = G(m ‖ H(ek))[32:64]`.

## Proof structure

1. The `dk` field projections of a generated key are theorems
   (`decodeDkPke_mlkemKeyGen`, `decodeDkEk_mlkemKeyGen`, `decodeDkH_mlkemKeyGen`).
2. `kpke_roundTrip` gives `m' = m` under the noise bound.
3. Hence `(K', r') = G(m ‖ H(ek)) = (K, r)`, the re-encryption `c'` is literally `c`,
   and the implicit-rejection branch is not taken.

The only hypothesis is the `K-PKE` noise bound at the derived randomness; the theorem
holds for every parameter set and every instantiation of the oracles `G`, `H`, `J`.

**Source**: NIST FIPS 203, § 6 (Algorithms 16–18)
-/

noncomputable section

namespace Fips203

/-- The encryption randomness used by `Encaps` on a key generated from seed `d`. -/
def honestR (d m : Fin 32 → UInt8) (p : ParamSet) : Fin 32 → UInt8 :=
  encRandomness m (hashEk (kpkeKeyGen d p).ek)

/-- `mlkemEncaps` on a generated key produces the `K-PKE` ciphertext at `honestR`. -/
lemma mlkemEncaps_mlkemKeyGen_ct (d z m : Fin 32 → UInt8) (p : ParamSet) :
    (mlkemEncaps p (mlkemKeyGen d z p).ek m).ct =
      (kpkeEncrypt p (kpkeKeyGen d p).ek m (honestR d m p)).ct := rfl

/-- `mlkemEncaps` on a generated key produces the shared secret `G(m ‖ H(ek))[0:32]`. -/
lemma mlkemEncaps_mlkemKeyGen_ss (d z m : Fin 32 → UInt8) (p : ParamSet) :
    (mlkemEncaps p (mlkemKeyGen d z p).ek m).ss =
      sharedKey m (hashEk (kpkeKeyGen d p).ek) := rfl

/-- **ML-KEM round-trip correctness** (FIPS 203, § 6):

  `mlkemDecaps(dk, mlkemEncaps(ek, m).ct) = mlkemEncaps(ek, m).ss`
  for `(ek, dk) = mlkemKeyGen d z`

under the single hypothesis that the `K-PKE` noise at the derived randomness
`honestR d m p` is bounded by `⌊q/4⌋` at every coefficient. -/
theorem mlkem_roundTrip (p : ParamSet) (d z m : Fin 32 → UInt8)
    (h_noise : ∀ idx : Fin n,
      absZq (honestW d m (honestR d m p) p idx - decompressMsg m idx) < q / 4) :
    mlkemDecaps p (mlkemKeyGen d z p).dk (mlkemEncaps p (mlkemKeyGen d z p).ek m).ct =
      (mlkemEncaps p (mlkemKeyGen d z p).ek m).ss := by
  have h_m : kpkeDecrypt p (decodeDkPke (mlkemKeyGen d z p).dk)
      (mlkemEncaps p (mlkemKeyGen d z p).ek m).ct = m := by
    rw [decodeDkPke_mlkemKeyGen, mlkemEncaps_mlkemKeyGen_ct]
    exact kpke_roundTrip p d m (honestR d m p) h_noise
  rw [mlkemEncaps_mlkemKeyGen_ss, mlkemDecaps_of_reencrypt_eq, h_m, decodeDkH_mlkemKeyGen,
    mlkemKeyGen_ek]
  rw [h_m, decodeDkEk_mlkemKeyGen, decodeDkH_mlkemKeyGen, mlkemKeyGen_ek]
  exact mlkemEncaps_ct p (kpkeKeyGen d p).ek m

/-- **ML-KEM-768 round-trip correctness**: specialisation of `mlkem_roundTrip` to the
parameter set used by SPQR. -/
theorem mlkem_roundTrip_768 (d z m : Fin 32 → UInt8)
    (h_noise : ∀ idx : Fin n,
      absZq (honestW d m (honestR d m mlkem768) mlkem768 idx - decompressMsg m idx) < q / 4) :
    mlkemDecaps mlkem768 (mlkemKeyGen d z mlkem768).dk
        (mlkemEncaps mlkem768 (mlkemKeyGen d z mlkem768).ek m).ct =
      (mlkemEncaps mlkem768 (mlkemKeyGen d z mlkem768).ek m).ss :=
  mlkem_roundTrip mlkem768 d z m h_noise

end Fips203
