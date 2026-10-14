/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module
public import SrcTranslated.FunsExternal
public import Spqr.Crypto.Fips203.Bridge.EncapsBytes
public import Spqr.Crypto.Fips203.Bridge.LibcruxKeygen
/-!
# Bridge: FIPS 203 Algorithm 17 (round 1) ↔ libcrux `incremental::encapsulate1`

The Aeneas external
`libcrux_ml_kem.mlkem768.incremental.encapsulate1` is modelled in `SrcTranslated/FunsExternal.lean`
by round 1 of `ML-KEM.Encaps_internal` (`Fips203.mlkemEncapsPhase1`, see
`Spqr/Crypto/Fips203/KEM/EncapsIncremental.lean`) on the header `pk1 = ρ ‖ H(ek)` and the message
`randomness`, serialised as in `Spqr/Crypto/Fips203/Bridge/EncapsBytes.lean`.

This file states the bridge as equations between the Aeneas side and the FIPS 203 definitions:

| libcrux output                   | FIPS 203 value                                              |
|----------------------------------|-------------------------------------------------------------|
| `Ok(ct1).value`                  | `c₁ = (mlkemEncapsPhase1 (ρ, h) m).ct1`                     |
| `state[0 : 2080]`                | `stateBytes (ŷ, e₂, m)`; decodes back to the state          |
| `shared_secret[0 : 32]`          | `K = (mlkemEncapsPhase1 (ρ, h) m).ss`                       |

and, when the header is the `pk1` of a key pair produced by `from_seed` (Bridge 6.1), connects the
outputs to the *monolithic* Algorithm 17 on that key's `ek`: `K = (mlkemEncaps ek m).ss` and
`c₁ = (mlkemEncaps ek m).ct[0 : 960]`.

**Sources**: NIST FIPS 203, § 6.2 (Algorithm 17); libcrux-ml-kem 0.0.7, `src/mlkem.rs` lines
344–367 and `src/ind_cca/incremental.rs` lines 181–276.
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace Fips203.Bridge

open libcrux_ml_kem.mlkem768.incremental

/-! ## `encapsulate1` ↔ round 1 of Algorithm 17 -/

/-- **Bridge 6.2.**  Under the size preconditions, `encapsulate1` returns, without failure,
`Ok(c₁)` together with the two overwritten output buffers, all given by round 1 of
Algorithm 17 on `(pk1[0:32], pk1[32:64])` and `randomness`. -/
theorem encapsulate1_eq_mlkemEncapsPhase1 (pk1 : Slice U8) (randomness : Array U8 32#usize)
    (state shared_secret : Slice U8) (h_pk1 : 64 ≤ pk1.length) (h_ss : 32 ≤ shared_secret.length)
    (h_state : encapsStateSize ≤ state.length) :
    encapsulate1 pk1 randomness state shared_secret =
      ok (.Ok { value := ct1Array pk1.val h_pk1 (msgOfArray randomness) },
        Slice.from (overwritePrefix state.val (stateOut pk1.val h_pk1 (msgOfArray randomness))) (by
          rw [overwritePrefix_length _ _ h_state]; exact state.length_ineq),
        Slice.from
          (overwritePrefix shared_secret.val (ssOut pk1.val h_pk1 (msgOfArray randomness))) (by
          rw [overwritePrefix_length _ _ h_ss]; exact shared_secret.length_ineq)) := by
  simp only [encapsulate1, dif_pos h_pk1, dif_neg (Nat.not_lt.mpr h_ss),
    dif_neg (Nat.not_lt.mpr h_state)]

/-- The ciphertext half, as a byte list, is `c₁` of round 1. -/
theorem encapsulate1_ct1 (pk1 : Slice U8) (randomness : Array U8 32#usize)
    (state shared_secret : Slice U8) (h_pk1 : 64 ≤ pk1.length) (h_ss : 32 ≤ shared_secret.length)
    (h_state : encapsStateSize ≤ state.length)
    (c : spqr.libcrux_ml_kem.ind_cca.incremental.types.Ciphertext1 960#usize)
    (st ss : Slice U8)
    (h : encapsulate1 pk1 randomness state shared_secret = ok (.Ok c, st, ss)) :
    c.value.val = ct1List pk1.val h_pk1 (msgOfArray randomness) := by
  rw [encapsulate1_eq_mlkemEncapsPhase1 pk1 randomness state shared_secret h_pk1 h_ss h_state,
    ok.injEq, Prod.mk.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at h
  rw [← h.1]; simp only [ct1Array, Aeneas.Std.Array.make_val]

/-- The first `2080` bytes of the output `state` are the serialised `(ŷ, e₂, m)`. -/
theorem encapsulate1_state_take (pk1 : Slice U8) (randomness : Array U8 32#usize)
    (state shared_secret : Slice U8) (h_pk1 : 64 ≤ pk1.length) (h_ss : 32 ≤ shared_secret.length)
    (h_state : encapsStateSize ≤ state.length)
    (c : spqr.libcrux_ml_kem.ind_cca.incremental.types.Ciphertext1 960#usize)
    (st ss : Slice U8)
    (h : encapsulate1 pk1 randomness state shared_secret = ok (.Ok c, st, ss)) :
    st.val.take encapsStateSize =
      toU8List (stateBytes (encaps1Output pk1.val h_pk1 (msgOfArray randomness)).state) := by
  rw [encapsulate1_eq_mlkemEncapsPhase1 pk1 randomness state shared_secret h_pk1 h_ss h_state,
    ok.injEq, Prod.mk.injEq, Prod.mk.injEq] at h
  rw [← h.2.1]; simp only [Slice.from_val]
  exact overwritePrefix_take _ _

/-- The first `32` bytes of the output `shared_secret` are `K` of round 1. -/
theorem encapsulate1_ss_take (pk1 : Slice U8) (randomness : Array U8 32#usize)
    (state shared_secret : Slice U8) (h_pk1 : 64 ≤ pk1.length) (h_ss : 32 ≤ shared_secret.length)
    (h_state : encapsStateSize ≤ state.length)
    (c : spqr.libcrux_ml_kem.ind_cca.incremental.types.Ciphertext1 960#usize) (st ss : Slice U8)
    (h : encapsulate1 pk1 randomness state shared_secret = ok (.Ok c, st, ss)) :
    ss.val.take 32 = toU8List (encaps1Output pk1.val h_pk1 (msgOfArray randomness)).ss := by
  rw [encapsulate1_eq_mlkemEncapsPhase1 pk1 randomness state shared_secret h_pk1 h_ss h_state,
    ok.injEq, Prod.mk.injEq, Prod.mk.injEq] at h
  rw [← h.2.2]; simp only [Slice.from_val]
  exact overwritePrefix_take _ _

/-- The written state decodes back to the FIPS 203 state `(ŷ, e₂, m)` of round 1: this is the
value `encapsulate2` will read (Bridge 6.3). -/
theorem decodeEncapsState_stateOut (pk1 : List U8) (h : 64 ≤ pk1.length) (m : Fin 32 → UInt8) :
    decodeEncapsState (stateOut pk1 h m) = (encaps1Output pk1 h m).state :=
  decodeEncapsState_stateBytes _

/-- Error case: a header shorter than `64` bytes is rejected with `InvalidInputLength` and the
output buffers are untouched. -/
theorem encapsulate1_short_header (pk1 : Slice U8) (randomness : Array U8 32#usize)
    (state shared_secret : Slice U8) (h_pk1 : pk1.length < 64) :
    encapsulate1 pk1 randomness state shared_secret =
      ok (.Err .InvalidInputLength, state, shared_secret) := by
  simp only [encapsulate1, dif_neg (Nat.not_le.mpr h_pk1)]

/-! ## Composition with Bridge 6.1: the header of a generated key pair

When `pk1` is the header `ρ ‖ H(ek)` of `from_seed seed` (`pk1Bytes`, Bridge 6.1), round 1 is
round 1 of Algorithm 17 on that key's `ek`, so the outputs are those of the *monolithic*
`ML-KEM.Encaps_internal(ek, m)`. -/

/-- On the header of a generated key, the parsed header is `headerOfEk ek`. -/
theorem encaps1Output_pk1Bytes (seed : Fin 64 → UInt8) (h : 64 ≤ (toU8List (pk1Bytes seed)).length)
    (m : Fin 32 → UInt8) :
    encaps1Output (toU8List (pk1Bytes seed)) h m =
      mlkemEncapsPhase1 mlkem768 (headerOfEk (ekBytes seed)) m := by
  rw [encaps1Output, headerOfList_pk1Bytes]

/-- The shared secret of round 1 on a generated key's header is the shared secret of
Algorithm 17 on its `ek`. -/
theorem ssOut_pk1Bytes (seed : Fin 64 → UInt8) (h : 64 ≤ (toU8List (pk1Bytes seed)).length)
    (m : Fin 32 → UInt8) :
    ssOut (toU8List (pk1Bytes seed)) h m = (mlkemEncaps mlkem768 (ekBytes seed) m).ss := by
  rw [ssOut, encaps1Output_pk1Bytes, mlkemEncapsPhase1_ss]

/-- `c₁` of round 1 on a generated key's header is `ct[0 : 960]` of Algorithm 17 on its `ek`. -/
theorem ct1Bytes_pk1Bytes (seed : Fin 64 → UInt8) (h : 64 ≤ (toU8List (pk1Bytes seed)).length)
    (m : Fin 32 → UInt8) (i : Fin ct1Size) :
    ct1Bytes (toU8List (pk1Bytes seed)) h m i =
      (mlkemEncaps mlkem768 (ekBytes seed) m).ct ⟨i.val, by
        have := i.isLt; simp only [ct1Size] at this
        rw [ctSizeEnc_eq_ctSize, mlkem768_ctSize]; omega⟩ := by
  rw [ct1Bytes, encaps1Output_pk1Bytes, mlkemEncapsPhase1_ct1]

/-- The message stored in the state is `randomness`. -/
theorem stateOut_m (pk1 : List U8) (h : 64 ≤ pk1.length) (m : Fin 32 → UInt8) :
    (decodeEncapsState (stateOut pk1 h m)).m = m := by
  rw [decodeEncapsState_stateOut]
  rfl

end Fips203.Bridge
