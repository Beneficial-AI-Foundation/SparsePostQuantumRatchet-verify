/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module
public import SrcTranslated.FunsExternal
public import Spqr.Crypto.Fips203.Bridge.KeyPairBytes
import all Aeneas.Std.Array.Array
/-!
# Bridge: FIPS 203 Algorithm 16 ↔ libcrux `KeyPairCompressedBytes::from_seed`

Phase 6.1 of `doc/plan.md`.  The Aeneas external
`libcrux_ml_kem.mlkem768.incremental.KeyPairCompressedBytes.from_seed` is modelled in
`SrcTranslated/FunsExternal.lean` by the FIPS 203 definition `Fips203.Bridge.keyPairArray`,
i.e. `ML-KEM.KeyGen_internal(seed[0:32], seed[32:64])` serialised as `dk ‖ ek ‖ H(ek) ‖ z`.
This file states the bridge as equations between the Aeneas side and the FIPS 203 definitions
(`Fips203.mlkemKeyGen`, Algorithm 16) and derives the value-level description of the three
accessors `sk`, `pk2`, `pk1` that `spqr::incremental_mlkem768::generate` reads:

| libcrux accessor | bytes                 | FIPS 203 value                          |
|------------------|-----------------------|-----------------------------------------|
| `sk`             | `value[0 : 2400]`     | `(mlkemKeyGen d z mlkem768).dk`         |
| `pk2`            | `value[1152 : 2304]`  | `ek[0 : 1152] = ByteEncode₁₂(t̂)`        |
| `pk1`            | `value[2304 : 2368]`  | `ek[1152 : 1184] ‖ H(ek) = ρ ‖ H(ek)`   |

with `d = seed[0 : 32]`, `z = seed[32 : 64]`, `ek = (mlkemKeyGen d z mlkem768).ek`.

**Sources**: NIST FIPS 203, § 6.1 (Algorithm 16); libcrux-ml-kem 0.0.7, `src/mlkem.rs`
lines 240–285.
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace Fips203.Bridge

open libcrux_ml_kem.mlkem768.incremental

/-! ## `from_seed` ↔ Algorithm 16 -/

/-- **Bridge 6.1.** `from_seed seed` returns, without failure, the `KeyPairCompressedBytes` whose
buffer is the FIPS 203 decapsulation key of `ML-KEM.KeyGen_internal(seed[0:32], seed[32:64])`. -/
theorem from_seed_eq_mlkemKeyGen (seed : Array U8 64#usize) :
    KeyPairCompressedBytes.from_seed seed =
      ok { value := keyPairArray (seedOfArray seed) } := rfl

/-- The buffer, as a byte list, is `toU8List (mlkemKeyGen d z mlkem768).dk`. -/
theorem from_seed_value (seed : Array U8 64#usize) (kp : KeyPairCompressedBytes)
    (h : KeyPairCompressedBytes.from_seed seed = ok kp) :
    kp.value.val =
      toU8List (mlkemKeyGen (seedD (seedOfArray seed)) (seedZ (seedOfArray seed)) mlkem768).dk := by
  rw [from_seed_eq_mlkemKeyGen, ok.injEq] at h
  subst h; rfl

/-! ## The accessors in FIPS 203 terms

These are the value-level facts that `spqr.incremental_mlkem768.generate` exposes through
`Keys { hdr := pk1, ek := pk2, dk := sk }`. -/

/-- `sk (from_seed seed)` is the FIPS 203 decapsulation key. -/
theorem sk_from_seed (seed : Array U8 64#usize) :
    (KeyPairCompressedBytes.from_seed seed >>= KeyPairCompressedBytes.sk) =
      ok (keyPairArray (seedOfArray seed)) := by
  rw [from_seed_eq_mlkemKeyGen, bind_tc_ok]
  rfl

/-- `pk2` of the generated key pair is `ek[0 : 1152]`, the serialised `t̂` of the FIPS 203 key. -/
theorem pk2_from_seed (seed : Array U8 64#usize) (r : Array U8 1152#usize)
    (h : KeyPairCompressedBytes.pk2 { value := keyPairArray (seedOfArray seed) } = ok r) :
    r.val = toU8List (pk2Bytes (seedOfArray seed)) := by
  rw [KeyPairCompressedBytes.pk2, ok.injEq] at h
  rw [← h, Aeneas.Std.Array.make_val]
  have henc : Spqr.Mlkem.mlkem768Params.encapsulationKeyBytes = 1152 := by decide
  rw [henc]
  change (keyPairArray (seedOfArray seed)).val.slice 1152 (2 * 1152) = _
  rw [keyPairArray_val]
  exact keyPairList_slice_pk2 _

/-- `pk1` of the generated key pair is `ρ ‖ H(ek)` of the FIPS 203 key. -/
theorem pk1_from_seed (seed : Array U8 64#usize) (r : Array U8 64#usize)
    (h : KeyPairCompressedBytes.pk1 { value := keyPairArray (seedOfArray seed) } = ok r) :
    r.val = toU8List (pk1Bytes (seedOfArray seed)) := by
  rw [KeyPairCompressedBytes.pk1, ok.injEq] at h
  rw [← h, Aeneas.Std.Array.make_val]
  have henc : Spqr.Mlkem.mlkem768Params.encapsulationKeyBytes = 1152 := by decide
  have hhdr : Spqr.Mlkem.headerBytes = 64 := by decide
  rw [henc, hhdr]
  change (keyPairArray (seedOfArray seed)).val.slice (2 * 1152) (2 * 1152 + 64) = _
  rw [keyPairArray_val]
  exact keyPairList_slice_pk1 _

/-- Composite: `from_seed` then `pk2`, as a single `Result` computation. -/
theorem bind_from_seed_pk2 (seed : Array U8 64#usize) :
    (KeyPairCompressedBytes.from_seed seed >>= KeyPairCompressedBytes.pk2) =
      KeyPairCompressedBytes.pk2 { value := keyPairArray (seedOfArray seed) } := by
  rw [from_seed_eq_mlkemKeyGen]
  exact bind_tc_ok _ _

/-- Composite: `from_seed` then `pk1`, as a single `Result` computation. -/
theorem bind_from_seed_pk1 (seed : Array U8 64#usize) :
    (KeyPairCompressedBytes.from_seed seed >>= KeyPairCompressedBytes.pk1) =
      KeyPairCompressedBytes.pk1 { value := keyPairArray (seedOfArray seed) } := by
  rw [from_seed_eq_mlkemKeyGen]
  exact bind_tc_ok _ _

/-! ## Consequences from the FIPS 203 side

Because the buffer *is* `mlkemKeyGen … .dk`, the layout projections of `KEM/KeyGen.lean` apply
directly: e.g. the last 32 bytes are the implicit-rejection value `z = seed[32 : 64]`. -/

/-- The implicit-rejection value stored in the buffer is `seed[32 : 64]`. -/
theorem from_seed_decodeDkZ (seed : Array U8 64#usize) :
    decodeDkZ (keyPairBytes (seedOfArray seed)) = seedZ (seedOfArray seed) :=
  decodeDkZ_mlkemKeyGen _ _ _

/-- The hash stored in the buffer is `H(ek)` of the FIPS 203 encapsulation key. -/
theorem from_seed_decodeDkH (seed : Array U8 64#usize) :
    decodeDkH (keyPairBytes (seedOfArray seed)) = hashEk (ekBytes (seedOfArray seed)) :=
  decodeDkH_mlkemKeyGen _ _ _

/-- The encapsulation key embedded in the buffer is the FIPS 203 `ek`. -/
theorem from_seed_decodeDkEk (seed : Array U8 64#usize) :
    decodeDkEk (keyPairBytes (seedOfArray seed)) = ekBytes (seedOfArray seed) :=
  decodeDkEk_mlkemKeyGen _ _ _

/-- The PKE decryption key embedded in the buffer is the K-PKE `dkPKE`. -/
theorem from_seed_decodeDkPke (seed : Array U8 64#usize) :
    decodeDkPke (keyPairBytes (seedOfArray seed)) =
      (kpkeKeyGen (seedD (seedOfArray seed)) mlkem768).dk :=
  decodeDkPke_mlkemKeyGen _ _ _

end Fips203.Bridge
