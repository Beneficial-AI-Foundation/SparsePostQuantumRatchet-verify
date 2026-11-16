/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module
public import SrcTranslated.Funs
public import SrcTranslated.FunsExternal
public import Spqr.Crypto.Fips203.Refinement.LibcruxEncaps2
public import Spqr.Specs.Aeneas.ResultExpect
public import Spqr.Specs.IncrementalMlkem768.PotentiallyFixState
/-! # Spec theorem for `incremental_mlkem768::encaps2`

`encaps2` is round 2 of ML-KEM-768 encapsulation packaged for the SPQR ratchet: given the
1152-byte encapsulation key `ek = ByteEncode₁₂(t̂)` of a peer's key pair and the 2080-byte
serialized encapsulation state `es = ŷ ‖ e₂ ‖ m` produced by `encaps1`, it returns the 128-byte
second ciphertext half `c₂`.

The extracted body in `SrcTranslated/Funs.lean` proceeds in three steps:
* call `potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275 es` and fall back to
  `es` when it returns `None` — the endianness workaround for libcrux issue #1275;
* `try_into` the (possibly fixed) state and `ek` into fixed-size arrays of 2080 and 1152 bytes
  and unwrap both `Result`s (`expect`) — with the length preconditions these cannot fail;
* call libcrux's incremental `encapsulate2` and copy the ciphertext into an owned `Vec`.

By `Spqr/Crypto/Fips203/Refinement/LibcruxEncaps2.lean`, the output is
`Fips203.Refinement.ct2List st pk` — round 2 of FIPS 203 Algorithm 17
(`Fips203.mlkemEncapsPhase2`) on the state `(ŷ, e₂, m)` decoded from `st` and the NTT-domain
vector `t̂` decoded from `pk = ByteEncode₁₂(t̂)` — where `pk` holds the bytes of `ek` and `st`
holds the bytes of the state actually consumed: the fixed state when the endianness workaround
returned `Some`, and `es` itself otherwise. `encaps2_spec` uses only the contract theorem
`potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275_spec` (success, any `Some` has
2080 bytes), so it holds for every 2080-byte state, including the byte-swapped ones the Rust
repairs.

When the `e₂` words of `es` are signed 16-bit little-endian values in `-2 … 2`, as libcrux-ml-kem
0.0.10 writes them, `encaps2EffectiveState_signedE2` shows that the effective state is `es` itself.
`encaps2EffectiveState_stateOut` shows the same for a state that the FIPS 203 model of
`encapsulate1` writes. The model stores `e₂` in `[0, q)`, so the bytes that libcrux writes do not
satisfy its premise (issue #800). If in addition the
header is `pk1Bytes seed` and `ek` is `pk2Bytes seed` of one generated key,
`ct2Bytes_stateOut_pk2Bytes` and `ct_eq_ct1Bytes_append_ct2Bytes` identify the output with
`ct[960 : 1088]` of the monolithic `ML-KEM.Encaps_internal(ek, m)`.

Source: `src/incremental_mlkem768.rs`, lines 71:0-79:1. -/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace Fips203.Refinement

/-- `try_from` on a slice of exactly `N` elements succeeds with `Ok` of an array holding the
slice's elements. -/
@[step]
theorem tryFromSharedArraySlice_ok_spec {T : Type} (N : Usize) (s : Slice T)
    (h : s.length = N.val) :
    core.array.TryFromSharedArraySlice.try_from N s
      ⦃ (r : core.result.Result (Array T N) core.array.TryFromSliceError) =>
      ∃ a : Array T N, r = core.result.Result.Ok a ∧ a.val = s.val ⦄ := by
  simp only [core.array.TryFromSharedArraySlice.try_from]
  rw [dite_eq_left (by scalar_tac)]
  simp only [WP.spec_ok]
  exact ⟨_, rfl, Array.from_val _ _⟩

end Fips203.Refinement

namespace Spqr.IncrementalMlkem768

open libcrux_ml_kem.mlkem768.incremental

/-- The effective state bytes consumed by `encaps2`: if the endianness workaround
(`potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275`) returns `Some fixed`,
use `fixed`; otherwise fall back to the original state `es`.

`Result` is the Aeneas ITree monad and cannot be pattern-matched directly, so the selection
is expressed monadically with `Option.elim`. -/
noncomputable def encaps2EffectiveState
    (es : alloc.vec.Vec Std.U8) : Result (List Std.U8) := do
  let mf ←
    spqr.incremental_mlkem768.potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275
      es
  ok (mf.elim es.val (fun fixed => fixed.val))

open spqr.incremental_mlkem768 in
/-- On a 2080-byte state whose `e₂` words are signed 16-bit little-endian values in `-2 … 2`, the
effective state of `encaps2` is `es` itself. -/
theorem encaps2EffectiveState_signedE2 (es : alloc.vec.Vec U8) (h_len : es.val.length = 2080)
    (h_e2 : ∀ k < 256,
      (es.val[1536 + 2 * k]!, es.val[1536 + 2 * k + 1]!) ∈ Fips203.Refinement.signedE2Pairs) :
    encaps2EffectiveState es = ok es.val := by
  simp only [encaps2EffectiveState,
    potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275_signedE2 es h_len h_e2,
    bind_ok, Option.elim]

open spqr.incremental_mlkem768 in
/-- On every state that the FIPS 203 model of `encapsulate1` writes, the effective state of
`encaps2` is `es` itself. The model stores `e₂` in `[0, q)`, so the bytes that libcrux-ml-kem
0.0.10 writes do not satisfy `h_es` (issue #800). -/
theorem encaps2EffectiveState_stateOut (hdr : List U8) (h_hdr : 64 ≤ hdr.length)
    (m : Fin 32 → UInt8) (es : alloc.vec.Vec U8)
    (h_es : es.val = Fips203.Refinement.toU8List (Fips203.Refinement.stateOut hdr h_hdr m)) :
    encaps2EffectiveState es = ok es.val := by
  simp only [encaps2EffectiveState,
    potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275_stateOut hdr h_hdr m es h_es,
    bind_ok, Option.elim]

/-- Postcondition predicate for `encaps2`: the result is the 128-byte
second ciphertext half `c₂` computed from the effective state and the
encapsulation key, via FIPS 203 round 2. -/
def Encaps2Post
    (ek es : alloc.vec.Vec Std.U8)
    (result : alloc.vec.Vec Std.U8) : Prop :=
  ∃ stBytes : List Std.U8,
    encaps2EffectiveState es = ok stBytes ∧
    ∃ (st : Array Std.U8 2080#usize)
      (pk : Array Std.U8 1152#usize),
      st.val = stBytes ∧
      pk.val = ek.val ∧
      result.val = Fips203.Refinement.ct2List st pk

end Spqr.IncrementalMlkem768

namespace spqr.incremental_mlkem768

open Spqr.IncrementalMlkem768

/-- Assume the Rust `requires` (`es.len() = 2080`, `ek.len() = 1152`). Then `encaps2` succeeds
and returns the 128-byte second ciphertext half `c₂` of round 2 of FIPS 203 Algorithm 17: there
are fixed-size arrays `st` (the possibly fixed state the workaround selected) and `pk` (the bytes
of `ek`) with `result = Fips203.Refinement.ct2List st pk`, i.e.
`c₂ = ByteEncode_{d_v}(Compress_{d_v}(NTT⁻¹(t̂ᵀ∘ŷ) + e₂ + Decompress₁(m)))` on the decoded
state `(ŷ, e₂, m)` and `t̂`.

The proof uses only the contract theorem
`potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275_spec` (success, and any `Some`
has 2080 bytes), so it holds for every 2080-byte state. It makes no assumption on whether the
workaround returns `None` or `Some`; `Encaps2Post` records the state actually consumed through
`encaps2EffectiveState`. -/
theorem encaps2_spec (ek es : alloc.vec.Vec Std.U8)
    (h_ek : ek.length = 1152) (h_es : es.length = 2080) :
    encaps2 ek es ⦃ (result : alloc.vec.Vec Std.U8) =>
      Encaps2Post ek es result ∧
      result.length = 128 ⦄ := by
  -- Suffices to show the expanded form of `Encaps2Post`.
  suffices h : encaps2 ek es ⦃ (result : alloc.vec.Vec Std.U8) =>
      (∃ stBytes : List Std.U8,
        encaps2EffectiveState es = ok stBytes ∧
        ∃ (st : Array Std.U8 2080#usize)
          (pk : Array Std.U8 1152#usize),
          st.val = stBytes ∧
          pk.val = ek.val ∧
          result.val = Fips203.Refinement.ct2List st pk) ∧
      result.length = 128 ⦄ from h
  obtain ⟨mf, h_eq, h_len⟩ :=
    WP.spec_imp_exists
      (potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275_spec es h_es)
  -- The effective state has 2080 bytes in both branches (`Some` by `h_len`, `None` by `h_es`).
  have h_eff_len : (mf.elim es.val (fun fixed => fixed.val)).length = 2080 := by
    cases mf with
    | none => simpa [alloc.vec.Vec.length] using h_es
    | some v => simpa [alloc.vec.Vec.length] using h_len v (by simp)
  unfold encaps2
  rw [h_eq]
  step*
  case h =>
    simp only [Slice.length, s_post, es1_post, o_post]
    cases mf with
    | none =>
      simp only [core.option.Option.unwrap_or_none, Option.elim] at h_eff_len ⊢
      exact h_eff_len
    | some v =>
      simp only [core.option.Option.unwrap_or_some, Option.elim] at h_eff_len ⊢
      exact h_eff_len
  obtain ⟨a0, r_post, r_post1⟩ :
      ∃ a0 : Array Std.U8 2080#usize,
        r = core.result.Result.Ok a0 ∧ a0.val = s.val :=
    ⟨_, r_post, r_post1⟩
  rw [r_post]
  step*
  rw [r1_post]
  step*
  rw [a_post, a1_post] at ct2_post1
  have h_s2 : result.slice = ct2.value.to_slice := by
    rwa [← s2_post]
  have h_result : result.val = Fips203.Refinement.ct2List a0 a := by
    rw [alloc.vec.Vec.val, h_s2, Array.val_to_slice, ct2_post1]
  refine ⟨⟨mf.elim es.val (fun fixed => fixed.val), ?_, a0, a, ?_, ?_, h_result⟩, ?_⟩
  · simp [encaps2EffectiveState, h_eq]
  · rw [r_post1, s_post, es1_post]
    cases mf <;> simp only [o_post, core.option.Option.unwrap_or_none,
      core.option.Option.unwrap_or_some, Option.elim]
  · rw [r1_post1, s1_post]
  · simp only [alloc.vec.Vec.length, h_result, Fips203.Refinement.ct2List_length]

end spqr.incremental_mlkem768
