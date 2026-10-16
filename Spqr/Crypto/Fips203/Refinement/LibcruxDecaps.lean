/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module
public import SrcTranslated.FunsExternal
public import Spqr.Crypto.Fips203.Refinement.DecapsBytes
public import Spqr.Crypto.Fips203.Refinement.LibcruxEncaps2
public import Spqr.Crypto.Fips203.KEM.RoundTrip
/-!
# Refinement: FIPS 203 Algorithm 18 ↔ libcrux `incremental::decapsulate_compressed_key`

The Aeneas external
`libcrux_ml_kem.mlkem768.incremental.decapsulate_compressed_key` is modelled in
`SrcTranslated/FunsExternal.lean` by `ML-KEM.Decaps_internal` (`Fips203.mlkemDecaps`,
Algorithm 18) on the decapsulation key read from the 2400-byte compressed key-pair buffer
(Refinement 6.1) and the reassembled ciphertext `c = c₁ ‖ c₂`.

This file states the refinement as equations between the Aeneas side and the FIPS 203 definitions:

| libcrux output | FIPS 203 value                                      |
|----------------|------------------------------------------------------|
| `ss`           | `mlkemDecaps dk (c₁ ‖ c₂)` (`Fips203.Refinement.ssBytes`) |

and, when the inputs come from the other three refinement lemmas — `dk` from
`from_seed` (6.1), `c₁` from
`encapsulate1` (6.2), `c₂` from `encapsulate2` (6.3) — composes them into the end-to-end KEM
round trip: under the K-PKE noise bound, the decapsulated secret equals the shared secret of the
monolithic Algorithm 17 on that key's `ek`.

**Sources**: NIST FIPS 203, § 6.3 (Algorithm 18); libcrux-ml-kem 0.0.7, `src/mlkem.rs` lines
439–443 and `src/ind_cca/incremental.rs` (`decapsulate_compressed_key`).
-/

@[expose] public section

noncomputable section

open Aeneas Aeneas.Std Result

namespace Fips203.Refinement

open libcrux_ml_kem.mlkem768.incremental

/-! ## `decapsulate_compressed_key` ↔ Algorithm 18 -/

/-- **Refinement 6.4.**  `decapsulate_compressed_key` returns, without failure, the 32-byte shared
secret of Algorithm 18 on the decoded decapsulation key and the ciphertext `c₁ ‖ c₂`. -/
theorem decapsulate_eq_mlkemDecaps (dk : Array U8 2400#usize)
    (ct1 : spqr.libcrux_ml_kem.ind_cca.incremental.types.Ciphertext1 960#usize)
    (ct2 : spqr.libcrux_ml_kem.ind_cca.incremental.types.Ciphertext2 128#usize) :
    decapsulate_compressed_key dk ct1 ct2 = ok (ssArray dk ct1.value ct2.value) := rfl

/-- The returned secret, as a byte list, is `mlkemDecaps dk (c₁ ‖ c₂)`. -/
theorem decapsulate_ss (dk : Array U8 2400#usize)
    (ct1 : spqr.libcrux_ml_kem.ind_cca.incremental.types.Ciphertext1 960#usize)
    (ct2 : spqr.libcrux_ml_kem.ind_cca.incremental.types.Ciphertext2 128#usize)
    (ss : Array U8 32#usize) (h : decapsulate_compressed_key dk ct1 ct2 = ok ss) :
    ss.val = toU8List
      (mlkemDecaps stdPrimitives mlkem768 (dkOfArray dk) (ctOfParts ct1.value ct2.value)) := by
  rw [decapsulate_eq_mlkemDecaps, ok.injEq] at h
  rw [← h]
  rfl

/-! ## Composition with Refinements 6.1–6.3

When `dk` is the buffer of `from_seed seed`, `c₁` the output of `encapsulate1` on that key's
header and `c₂` the output of `encapsulate2` on the serialised round-1 state and `pk2`, the
reassembled ciphertext is byte-for-byte the ciphertext of the monolithic Algorithm 17 on the
key's `ek`, and — under the K-PKE noise bound — decapsulation recovers the encapsulated
secret. -/

/-- The reassembled ciphertext of the three refinement lemmas is
 the ciphertext of Algorithm 17 on the generated key's `ek`. -/
theorem ctOfParts_ct1Array_ct2Array (seed : Fin 64 → UInt8)
    (h : 64 ≤ (toU8List (pk1Bytes seed)).length) (m : Fin 32 → UInt8) :
    ctOfParts (ct1Array (toU8List (pk1Bytes seed)) h m)
        (ct2Array (stateArray (stateOut (toU8List (pk1Bytes seed)) h m))
          (pk2Array (pk2Bytes seed))) =
      (mlkemEncaps stdPrimitives mlkem768 (ekBytes seed) m).ct := by
  funext idx
  rw [ct_eq_ct1Bytes_append_ct2Bytes seed h m idx]
  unfold ctOfParts
  by_cases hlt : idx.val < ct1Size
  · rw [dif_pos hlt, dif_pos hlt]
    simp only [ct1Array, Aeneas.Std.Array.make_val, ct1List]
    rw [toU8List_getElem, U8.toUInt8_ofUInt8]
  · rw [dif_neg hlt, dif_neg hlt]
    simp only [ct2Array, Aeneas.Std.Array.make_val, ct2List]
    rw [toU8List_getElem, U8.toUInt8_ofUInt8]

/-- **End-to-end KEM round trip across the four refinement lemmas.**  Decapsulating the ciphertext
assembled by `encapsulate1`/`encapsulate2` with the key pair of `from_seed` recovers the shared
secret of Algorithm 17 on the key's `ek`, under the K-PKE noise bound at the derived
randomness. -/
theorem ssBytes_roundTrip (seed : Fin 64 → UInt8)
    (h : 64 ≤ (toU8List (pk1Bytes seed)).length) (m : Fin 32 → UInt8)
    (h_noise : ∀ idx : Fin n,
      absZq (honestW stdPrimitives (seedD seed) m
        (honestR stdPrimitives (seedD seed) m mlkem768) mlkem768 idx - decompressMsg m idx)
        < q / 4) :
    ssBytes (keyPairArray seed) (ct1Array (toU8List (pk1Bytes seed)) h m)
        (ct2Array (stateArray (stateOut (toU8List (pk1Bytes seed)) h m))
          (pk2Array (pk2Bytes seed))) =
      (mlkemEncaps stdPrimitives mlkem768 (ekBytes seed) m).ss := by
  rw [ssBytes, dkOfArray_keyPairArray, ctOfParts_ct1Array_ct2Array seed h m]
  exact mlkem_roundTrip_768 stdPrimitives (seedD seed) (seedZ seed) m h_noise

end Fips203.Refinement
