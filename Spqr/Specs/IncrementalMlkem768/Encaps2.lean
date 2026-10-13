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

/-- **Spec theorem for `incremental_mlkem768.encaps2`**:

Assuming the Rust `requires` (`es.len() = 2080`, `ek.len() = 1152`) and the hax contract of the
opaque endianness workaround (`h_fix`: it succeeds, and when it returns `Some` the fixed state
has 2080 bytes), `encaps2` succeeds and returns the 128-byte second ciphertext half `c₂` of
round 2 of FIPS 203 Algorithm 17 (Bridge 6.3): there are fixed-size arrays `st` (the possibly
fixed state the workaround selected) and `pk` (the bytes of `ek`) with
`result = Fips203.Bridge.ct2List st pk`, i.e.
`c₂ = ByteEncode_{d_v}(Compress_{d_v}(NTT⁻¹(t̂ᵀ∘ŷ) + e₂ + Decompress₁(m)))` on the decoded
state `(ŷ, e₂, m)` and `t̂`. -/
theorem encaps2_spec (ek es : alloc.vec.Vec Std.U8)
    (h_ek : ek.length = 1152) (h_es : es.length = 2080)
    (h_fix : ∃ mf : Option (alloc.vec.Vec Std.U8),
      _root_.incremental_mlkem768.potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275
        es = ok mf ∧ ∀ v ∈ mf, v.length = 2080) :
    encaps2 ek es ⦃ (result : alloc.vec.Vec Std.U8) =>
      (∃ (mf : Option (alloc.vec.Vec Std.U8)) (st : Array Std.U8 2080#usize)
          (pk : Array Std.U8 1152#usize),
        _root_.incremental_mlkem768.potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275
          es = ok mf ∧
        st.val = (core.option.Option.unwrap_or mf es).val ∧
        pk.val = ek.val ∧
        result.val = Fips203.Bridge.ct2List st pk) ∧
      result.length = 128 ⦄ := by
  obtain ⟨mf, h_eq, h_len⟩ := h_fix
  unfold encaps2
  rw [h_eq]
  step*
  -- The (possibly fixed) state has 2080 bytes: by `h_fix` when the workaround returned `Some`,
  -- and by `h_es` when it fell back to `es`.
  case h =>
    simp only [Slice.length, s_post, es1_post, o_post]
    cases mf with
    | none => simp only [core.option.Option.unwrap_or_none]; scalar_tac
    | some v =>
      have := h_len v rfl
      simp only [core.option.Option.unwrap_or_some]; scalar_tac
  -- Unwrap the first `expect` on the `Ok` state array and continue to the second `try_from`.
  simp only [r_post1]
  step*
  -- Unwrap the second `expect` on the `Ok` `ek` array, run `encapsulate2` (Bridge 6.3) and copy
  -- the ciphertext bytes into an owned `Vec`.
  simp only [r1_post1]
  step*
  refine ⟨⟨mf, r, r1, rfl, ?_, ?_, ?_⟩, ?_⟩
  · rw [r_post2, s_post, es1_post, o_post]
  · rw [r1_post2, s1_post]
  · simp only [← result_post, s2_post, Array.val_to_slice, ct2_post2, a_post, a1_post]
  · simp only [alloc.vec.Vec.length, ← result_post, s2_post, Array.val_to_slice, ct2_post2,
      Fips203.Bridge.ct2List_length]

end spqr.incremental_mlkem768
