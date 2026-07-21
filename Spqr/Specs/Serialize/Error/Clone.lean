/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Liao Zhang
-/
import SrcTranslated.Funs

/-! # Spec theorem for
`spqr::serialize::{impl core::clone::Clone for spqr::serialize::Error}::clone`

The derived `Clone` for the fieldless enum `serialize::Error` returns a copy of the input
value. Since the enum carries no data, the clone is exactly the input.

**Source**: src/serialize.rs (line 6, `#[derive(..., Clone)]`)
-/

open Aeneas Aeneas.Std Result

namespace spqr.serialize.Error.Insts.CoreCloneClone

/-- **Spec theorem for `serialize.Error.Insts.CoreCloneClone.clone`**:

The derived `Clone for Error` always succeeds (no panic) and returns a value equal to its
input: `clone self = ok self`. -/
@[step]
theorem clone_spec (self : serialize.Error) :
    clone self ⦃ (result : serialize.Error) =>
      result = self ⦄ := by
  simp only [clone, WP.spec_ok]

end spqr.serialize.Error.Insts.CoreCloneClone
