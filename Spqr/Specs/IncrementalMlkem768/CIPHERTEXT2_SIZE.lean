/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Lacramioara Astefanoaei
-/
module

public import SrcTranslated.Funs
public import SrcTranslated.FunsExternal
/-! # Spec theorem for `spqr::incremental_mlkem768::CIPHERTEXT2_SIZE`

`CIPHERTEXT2_SIZE` is `Ciphertext2::<128>::len()`, the size in bytes of the second
ML-KEM-768 ciphertext part.

**Source**: spqr/src/incremental_mlkem768.rs:11 -/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace spqr.incremental_mlkem768

/-- `CIPHERTEXT2_SIZE` returns 128. -/
@[step]
theorem CIPHERTEXT2_SIZE_spec : CIPHERTEXT2_SIZE ⦃ (r : Usize) => r.val = 128 ⦄ := by
  unfold CIPHERTEXT2_SIZE
  step*

/-- `CIPHERTEXT2_SIZE = ok 128#usize`. -/
theorem CIPHERTEXT2_SIZE_eq : CIPHERTEXT2_SIZE = ok 128#usize := by
  unfold CIPHERTEXT2_SIZE
  rfl

end spqr.incremental_mlkem768
