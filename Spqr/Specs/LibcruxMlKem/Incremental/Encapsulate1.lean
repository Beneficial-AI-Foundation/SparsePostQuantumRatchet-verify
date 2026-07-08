/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Zhang Liao
-/
import SrcTranslated.FunsExternal

/-! # Specification axioms for `libcrux_ml_kem::mlkem768::incremental::encapsulate1`

`encapsulate1` is an opaque external function (declared as a bare axiom in
`SrcTranslated/FunsExternal.lean`), so its behaviour cannot be proved and is
instead assumed here as specification axioms, stating the conditions needed by
the round-trip spec (`Spqr/Specs/IncrementalMlkem768/Roundtrip.lean`).

The specification is functional, in the style of
`KeyPairCompressedBytes.pk1!` (`SrcTranslated/FunsExternal.lean`): the three
outputs get pure companions (`encapsulate1_ct1!`, `encapsulate1_st!`,
`encapsulate1_ss!`) and the bridging axiom `encapsulate1_eq` states that the
call succeeds and returns exactly the companions' values.  Unlike key
generation, `encapsulate1` takes plain slices and genuinely fails on mis-sized
inputs, so the bridging axiom is conditional on the length preconditions
(64-byte header, 2080-byte state buffer, 32-byte shared-secret buffer); the
companions are unspecified outside of them.  The buffer-length postconditions
are the axioms `encapsulate1_st_length` / `encapsulate1_ss_length`, and the
Hoare-style `encapsulate1_ok` is a derived theorem.
-/

open Aeneas Aeneas.Std Result

open spqr.libcrux_ml_kem.ind_cca.incremental.types (Ciphertext1)

namespace libcrux_ml_kem.mlkem768.incremental

/-- Pure companion of `encapsulate1` (first output): the first ciphertext
produced on header `hdr`, randomness `rand`, and buffers `st`, `ss`.
Meaningful only under the length preconditions of `encapsulate1_eq`. -/
axiom encapsulate1_ct1!
    (hdr : Slice Std.U8) (rand : Array Std.U8 32#usize) (st ss : Slice Std.U8) :
    Ciphertext1 960#usize

/-- Pure companion of `encapsulate1` (second output): the encapsulation state
written back into the state buffer.  Meaningful only under the length
preconditions of `encapsulate1_eq`. -/
axiom encapsulate1_st!
    (hdr : Slice Std.U8) (rand : Array Std.U8 32#usize) (st ss : Slice Std.U8) :
    Slice Std.U8

/-- Pure companion of `encapsulate1` (third output): the shared secret written
back into the shared-secret buffer.  Meaningful only under the length
preconditions of `encapsulate1_eq`. -/
axiom encapsulate1_ss!
    (hdr : Slice Std.U8) (rand : Array Std.U8 32#usize) (st ss : Slice Std.U8) :
    Slice Std.U8

/-- On well-sized inputs (64-byte header, 2080-byte state buffer, 32-byte
shared-secret buffer), `encapsulate1` succeeds and returns exactly its pure
companions' values. -/
axiom encapsulate1_eq
    (hdr : Slice Std.U8) (rand : Array Std.U8 32#usize) (st ss : Slice Std.U8)
    (h_hdr : hdr.length = 64) (h_st : st.length = 2080) (h_ss : ss.length = 32) :
    encapsulate1 hdr rand st ss =
      ok (core.result.Result.Ok (encapsulate1_ct1! hdr rand st ss),
        encapsulate1_st! hdr rand st ss, encapsulate1_ss! hdr rand st ss)

/-- On well-sized inputs, `encapsulate1` preserves the state-buffer length. -/
axiom encapsulate1_st_length
    (hdr : Slice Std.U8) (rand : Array Std.U8 32#usize) (st ss : Slice Std.U8)
    (h_hdr : hdr.length = 64) (h_st : st.length = 2080) (h_ss : ss.length = 32) :
    (encapsulate1_st! hdr rand st ss).length = 2080

/-- On well-sized inputs, `encapsulate1` preserves the shared-secret-buffer
length. -/
axiom encapsulate1_ss_length
    (hdr : Slice Std.U8) (rand : Array Std.U8 32#usize) (st ss : Slice Std.U8)
    (h_hdr : hdr.length = 64) (h_st : st.length = 2080) (h_ss : ss.length = 32) :
    (encapsulate1_ss! hdr rand st ss).length = 32

/-- `encapsulate1` succeeds on well-sized inputs (64-byte header, 2080-byte
state buffer, 32-byte shared-secret buffer) and preserves the buffer lengths
(consequence of `encapsulate1_eq` and the length axioms). -/
theorem encapsulate1_ok
    (hdr : Slice Std.U8) (rand : Array Std.U8 32#usize) (st ss : Slice Std.U8)
    (h_hdr : hdr.length = 64) (h_st : st.length = 2080) (h_ss : ss.length = 32) :
    encapsulate1 hdr rand st ss
      ⦃ r st' ss' => (∃ ct1, r = core.result.Result.Ok ct1) ∧
        st'.length = 2080 ∧ ss'.length = 32 ⦄ := by
  rw [encapsulate1_eq hdr rand st ss h_hdr h_st h_ss]
  simp only [WP.spec_ok, WP.uncurry'_pair]
  exact ⟨⟨_, rfl⟩, encapsulate1_st_length hdr rand st ss h_hdr h_st h_ss,
    encapsulate1_ss_length hdr rand st ss h_hdr h_st h_ss⟩

end libcrux_ml_kem.mlkem768.incremental
