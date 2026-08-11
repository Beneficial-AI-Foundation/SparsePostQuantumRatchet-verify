/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
/-! # Spec theorem for `spqr::SecretOutput::send_secret`

Returns `Some(secret)` for `Send(secret)`, `None` otherwise. Pure pattern match, never fails.

**Source**: spqr/src/lib.rs -/

open Aeneas Aeneas.Std Result

namespace spqr

/-- **Spec theorem for `spqr.SecretOutput.send_secret`**:

Returns `some s` for `Send s`, `none` otherwise. Always succeeds. -/
@[step]
theorem SecretOutput.send_secret_spec (self : SecretOutput) :
    SecretOutput.send_secret self ⦃ (result : Option (alloc.vec.Vec U8)) =>
      result = match self with
      | .Send s => some s
      | _ => none ⦄ := by
  unfold SecretOutput.send_secret
  match self with
  | .None => simp
  | .Send s => simp
  | .Recv s => simp

end spqr
