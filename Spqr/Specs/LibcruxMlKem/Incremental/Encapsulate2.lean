/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Zhang Liao
-/
import SrcTranslated.FunsExternal

/-! # Specification axiom for `libcrux_ml_kem::mlkem768::incremental::encapsulate2`

`encapsulate2` is an opaque external function (declared as a bare axiom in
`SrcTranslated/FunsExternal.lean`), so its behaviour cannot be proved and is
instead assumed here as a specification axiom, stating the conditions needed by
the round-trip spec (`Spqr/Specs/IncrementalMlkem768/Roundtrip.lean`).
-/

open Aeneas Aeneas.Std Result

namespace libcrux_ml_kem.mlkem768.incremental

/-- `encapsulate2` is panic-free: on fixed-size inputs it always returns a
ciphertext. -/
axiom encapsulate2_ok
    (st : Array Std.U8 2080#usize) (ek : Array Std.U8 1152#usize) :
    encapsulate2 st ek ⦃ _ => True ⦄

end libcrux_ml_kem.mlkem768.incremental
