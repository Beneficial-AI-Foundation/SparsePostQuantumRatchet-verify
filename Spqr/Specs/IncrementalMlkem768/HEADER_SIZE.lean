/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import SrcTranslated.Funs
public import SrcTranslated.FunsExternal
/-! # Spec theorem for `spqr::incremental_mlkem768::HEADER_SIZE`

`HEADER_SIZE` is the number of bytes of the ML-KEM-768 incremental "header" `ρ ‖ H(ek)` — the
first public-key half sent from A to B — and is defined in the Rust source as
`libcrux_ml_kem::mlkem768::incremental::pk1_len()`.  Its value is `32 + 32 = 64`, matching the
model constant `Spqr.Mlkem.headerBytes`.

**Source**: spqr/src/incremental_mlkem768.rs (line 13) -/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace spqr.incremental_mlkem768

/-- **Spec theorem for `spqr.incremental_mlkem768.HEADER_SIZE`**:

Concretely: the constant always succeeds and `r.val = Spqr.Mlkem.headerBytes` (`= 64`). -/
@[step]
theorem HEADER_SIZE_spec :
    HEADER_SIZE ⦃ (r : Usize) => r.val = Spqr.Mlkem.headerBytes ⦄ := by
  unfold HEADER_SIZE
  step*

/-- **Spec theorem for `spqr.incremental_mlkem768.HEADER_SIZE`** (numeric form):
`HEADER_SIZE = ok 64#usize`. -/
theorem HEADER_SIZE_eq : HEADER_SIZE = ok 64#usize := by
  unfold HEADER_SIZE
  rfl

end spqr.incremental_mlkem768
