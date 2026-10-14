/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import SrcTranslated.FunsExternal
import Spqr.Crypto.Fips203.Bridge.LibcruxEncaps2
import Spqr.Specs.Aeneas.ResultExpect

/-! # Spec theorem for `incremental_mlkem768::encaps2`

`encaps2` is round 2 of ML-KEM-768 encapsulation packaged for the SPQR ratchet: given the
1152-byte encapsulation key `ek = ByteEncode₁₂(t̂)` of a peer's key pair and the 2080-byte
serialized encapsulation state `es = ŷ ‖ e₂ ‖ m` produced by `encaps1`, it returns the 128-byte
second ciphertext half `c₂`.

The extracted body in `SrcTranslated/Funs.lean` proceeds in three steps:
* call the opaque `potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275 es` and fall
  back to `es` when it returns `None` — the endianness workaround for libcrux issue #1275;
* `try_into` the (possibly fixed) state and `ek` into fixed-size arrays of 2080 and 1152 bytes
  and unwrap both `Result`s (`expect`) — with the length preconditions these cannot fail;
* call libcrux's incremental `encapsulate2` and copy the ciphertext into an owned `Vec`.

**FIPS 203 value semantics** (Phase 7.3 of `doc/plan.md`, via Bridge 6.3
`Spqr/Crypto/Fips203/Bridge/LibcruxEncaps2.lean`): the output is
`Fips203.Bridge.ct2List st pk` — round 2 of FIPS 203 Algorithm 17
(`Fips203.mlkemEncapsPhase2`) on the state `(ŷ, e₂, m)` decoded from `st` and the NTT-domain
vector `t̂` decoded from `pk = ByteEncode₁₂(t̂)` — where `pk` holds the bytes of `ek` and `st`
holds the bytes of the state actually consumed: the fixed state when the opaque endianness
workaround returned `Some`, and `es` itself otherwise.  The correctness of the workaround is
outside FIPS 203 scope (`doc/plan.md`, § 10.3); its hax contract (success, 2080-byte output) is
taken as the hypothesis `h_fix`.

When `es` is the serialised round-1 state of `encaps1` on a generated key and the workaround is
the identity (`None`), `ct2Bytes_stateOut_pk2Bytes` and `ct_eq_ct1Bytes_append_ct2Bytes` of
Bridge 6.3 identify the output with `ct[960 : 1088]` of the monolithic
`ML-KEM.Encaps_internal(ek, m)`.

**Source**: `src/incremental_mlkem768.rs`, lines 71:0-79:1 -/

open Aeneas Aeneas.Std Result

namespace Fips203.Bridge

/-- `try_from` on a slice of exactly `N` elements succeeds with `Ok` of an array holding the
slice's elements. -/
@[step]
theorem tryFromSharedArraySlice_ok_spec {T : Type} (N : Usize) (s : Slice T)
    (h : s.length = N.val) :
    core.array.TryFromSharedArraySlice.try_from N s
      ⦃ (r : core.result.Result (Array T N) core.array.TryFromSliceError) =>
      ∃ a : Array T N, r = core.result.Result.Ok a ∧ a.val = s.val ⦄ := by
  simp only [core.array.TryFromSharedArraySlice.try_from]
  rw [dif_pos (by scalar_tac)]
  simp only [WP.spec_ok]
  exact ⟨_, rfl, rfl⟩

end Fips203.Bridge

namespace spqr.incremental_mlkem768

open libcrux_ml_kem.mlkem768.incremental

/-- The effective state bytes consumed by `encaps2`: if the endianness workaround
(`potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275`) returns `Some fixed`,
use `fixed`; otherwise fall back to the original state `es`. -/
def encaps2EffectiveState
    (es : alloc.vec.Vec Std.U8) : Result (List Std.U8) :=
  open _root_.incremental_mlkem768 in
  match potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275
    es with
  | ok (some fixed) => ok fixed.val
  | ok none         => ok es.val
  | fail e          => fail e
  | div             => div

/-- Postcondition predicate for `encaps2`: the result is the 128-byte
second ciphertext half `c₂` computed from the effective state and the
encapsulation key, via FIPS 203 round 2 (Bridge 6.3). -/
def Encaps2Post
    (ek es : alloc.vec.Vec Std.U8)
    (result : alloc.vec.Vec Std.U8) : Prop :=
  ∃ stBytes : List Std.U8,
    encaps2EffectiveState es = ok stBytes ∧
    ∃ (st : Array Std.U8 2080#usize)
      (pk : Array Std.U8 1152#usize),
      st.val = stBytes ∧
      pk.val = ek.val ∧
      result.val = Fips203.Bridge.ct2List st pk

/-- **Spec theorem for `incremental_mlkem768.encaps2`**:

Assuming the Rust `requires` (`es.len() = 2080`, `ek.len() = 1152`), `encaps2` succeeds and
returns the 128-byte second ciphertext half `c₂` of round 2 of FIPS 203 Algorithm 17
(Bridge 6.3): there are fixed-size arrays `st` (the possibly fixed state the workaround
selected) and `pk` (the bytes of `ek`) with `result = Fips203.Bridge.ct2List st pk`, i.e.
`c₂ = ByteEncode_{d_v}(Compress_{d_v}(NTT⁻¹(t̂ᵀ∘ŷ) + e₂ + Decompress₁(m)))` on the decoded
state `(ŷ, e₂, m)` and `t̂`.

The hax contract of the opaque endianness workaround (it succeeds, and when it returns `Some`
the fixed state has 2080 bytes) is derived from the concrete definition and spec theorem
`potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275_spec` rather than taken as
an external hypothesis. -/
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
          result.val = Fips203.Bridge.ct2List st pk) ∧
      result.length = 128 ⦄ from h
  -- Resolve the endianness workaround to `none`.
  open _root_.incremental_mlkem768 in
  have h_fix_spec :=
    potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275_spec
      es h_es
  open _root_.incremental_mlkem768 in
  have h_eq :
    potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275
      es = ok none := by
    simp [
      potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275]
  set mf : Option (alloc.vec.Vec Std.U8) := none
  have h_len : ∀ v ∈ mf, v.length = 2080 := by
    simp [mf]
  unfold encaps2
  rw [h_eq]
  step*
  case h =>
    simp only [Slice.length, s_post, es1_post, o_post, mf]
    simp only [core.option.Option.unwrap_or_none]
    scalar_tac
  simp only [r_post1]
  step*
  simp only [r1_post1]
  step*
  refine ⟨⟨es.val, ?_, r, r1, ?_, ?_, ?_⟩, ?_⟩
  · simp [encaps2EffectiveState, h_eq, mf]
  · rw [r_post2, s_post, es1_post]
    simp only [o_post, mf, core.option.Option.unwrap_or_none]
  · rw [r1_post2, s1_post]
  · simp only [← result_post, s2_post,
      Array.val_to_slice, ct2_post2, a_post, a1_post]
  · simp only [alloc.vec.Vec.length, ← result_post,
      s2_post, Array.val_to_slice, ct2_post2,
      Fips203.Bridge.ct2List_length]

end spqr.incremental_mlkem768
