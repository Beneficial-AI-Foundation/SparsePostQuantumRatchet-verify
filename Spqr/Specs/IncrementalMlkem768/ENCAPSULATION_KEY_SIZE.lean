/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Lacramioara Astefanoaei
-/
module

public import SrcTranslated.Funs
public import SrcTranslated.FunsExternal
/-! # Spec theorem for `spqr::incremental_mlkem768::ENCAPSULATION_KEY_SIZE`

`ENCAPSULATION_KEY_SIZE` is libcrux's `pk2_len()`, the size in bytes of the encoding
`ByteEncode₁₂(t̂)`. The FIPS 203 encapsulation key is this encoding followed by the 32-byte seed
`ρ`, 1184 bytes in all. libcrux sends `ρ` in `pk1`, so SPQR's "encapsulation key" is 1152 bytes.

**Source**: spqr/src/incremental_mlkem768.rs:15 -/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace spqr.incremental_mlkem768

/-- `ENCAPSULATION_KEY_SIZE` returns 1152. -/
@[step]
theorem ENCAPSULATION_KEY_SIZE_spec : ENCAPSULATION_KEY_SIZE ⦃ (r : Usize) => r.val = 1152 ⦄ := by
  unfold ENCAPSULATION_KEY_SIZE libcrux_ml_kem.mlkem768.incremental.pk2_len
  simp only [WP.spec_ok]
  rfl

/-- `ENCAPSULATION_KEY_SIZE = ok 1152#usize`. -/
theorem ENCAPSULATION_KEY_SIZE_eq : ENCAPSULATION_KEY_SIZE = ok 1152#usize := by
  unfold ENCAPSULATION_KEY_SIZE
  rfl

end spqr.incremental_mlkem768
