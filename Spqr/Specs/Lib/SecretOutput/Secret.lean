/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
/-! # Spec theorem for `spqr::SecretOutput::secret`

Returns `some secret` for both `Send` and `Recv` variants, `none` for `None`.

**Source**: spqr/src/lib.rs -/

open Aeneas Aeneas.Std Result

namespace spqr

/-- **Spec theorem for `spqr.SecretOutput.secret`**:

Maps `Send s | Recv s` to `some s` and `None` to `none`. Always succeeds. -/
@[step]
theorem SecretOutput.secret_spec (self : SecretOutput) :
    SecretOutput.secret self ⦃ (result : Option (alloc.vec.Vec U8)) =>
      result = match self with
      | .Send s => some s
      | .Recv s => some s
      | .None => none ⦄ := by
  unfold SecretOutput.secret
  match self with
  | .None => simp
  | .Send s => simp
  | .Recv s => simp

end spqr
