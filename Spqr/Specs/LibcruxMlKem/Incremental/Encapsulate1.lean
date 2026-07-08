/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Zhang Liao
-/
import SrcTranslated.FunsExternal

/-! # Specification axiom for `libcrux_ml_kem::mlkem768::incremental::encapsulate1`

`encapsulate1` is an opaque external function (declared as a bare axiom in
`SrcTranslated/FunsExternal.lean`), so its behaviour cannot be proved and is
instead assumed here as a specification axiom, stating the conditions needed by
the round-trip spec (`Spqr/Specs/IncrementalMlkem768/Roundtrip.lean`).
-/

open Aeneas Aeneas.Std Result

namespace libcrux_ml_kem.mlkem768.incremental

/-- `encapsulate1` succeeds on well-sized inputs (64-byte header, 2080-byte
state buffer, 32-byte shared-secret buffer) and preserves the buffer lengths. -/
axiom encapsulate1_ok
    (hdr : Slice Std.U8) (rand : Array Std.U8 32#usize) (st ss : Slice Std.U8)
    (h_hdr : hdr.length = 64) (h_st : st.length = 2080) (h_ss : ss.length = 32) :
    ∃ ct1 st' ss',
      encapsulate1 hdr rand st ss =
        ok (core.result.Result.Ok ct1, st', ss') ∧
      st'.length = 2080 ∧ ss'.length = 32

end libcrux_ml_kem.mlkem768.incremental
