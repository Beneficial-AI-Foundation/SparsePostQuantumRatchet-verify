/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Lacramioara Astefanoaei
-/
module

public import SrcTranslated.Funs
public import SrcTranslated.FunsExternal
/-! # Spec theorem for `spqr::incremental_mlkem768::CIPHERTEXT1_SIZE`

`CIPHERTEXT1_SIZE` is `Ciphertext1::<960>::len()`, the size in bytes of the first
ML-KEM-768 ciphertext part.

**Source**: spqr/src/incremental_mlkem768.rs:8 -/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace spqr.incremental_mlkem768

/-- `CIPHERTEXT1_SIZE` returns 960. -/
@[step]
theorem CIPHERTEXT1_SIZE_spec : CIPHERTEXT1_SIZE ⦃ (r : Usize) => r.val = 960 ⦄ := by
  unfold CIPHERTEXT1_SIZE
  step*

/-- `CIPHERTEXT1_SIZE = ok 960#usize`. -/
theorem CIPHERTEXT1_SIZE_eq : CIPHERTEXT1_SIZE = ok 960#usize := by
  unfold CIPHERTEXT1_SIZE
  rfl

end spqr.incremental_mlkem768
