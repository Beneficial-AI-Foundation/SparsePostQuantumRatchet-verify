/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
/-!
# Spec theorem for `spqr::SecretOutput::has_secret`

Returns `true` for `Send(_)` or `Recv(_)`, `false` for `None`.

**Source**: spqr/src/lib.rs (lines 173:4-175:5)
-/

open Aeneas Aeneas.Std Result

namespace spqr

/--
**Spec theorem for `spqr.SecretOutput.has_secret`**:

`true` iff `self` is `Send(_)` or `Recv(_)`; `false` for `None`. Always succeeds. -/
@[step]
theorem SecretOutput.has_secret_spec (self : SecretOutput) :
    SecretOutput.has_secret self ⦃ (result : Bool) =>
      result = true ↔ self ≠ .None ⦄ := by
  unfold SecretOutput.has_secret
  match self with
  | .None => simp
  | .Send s => simp
  | .Recv s => simp

end spqr
