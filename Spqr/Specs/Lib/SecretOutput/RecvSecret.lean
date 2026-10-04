/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
/-!
# Spec theorem for `spqr::SecretOutput::recv_secret`

Returns `some secret` for `Recv(secret)`, `none` otherwise. Pure pattern match, always succeeds.

**Source**: spqr/src/lib.rs (lines 159:4-165:5)
-/

open Aeneas Aeneas.Std Result

namespace spqr

/--
**Spec theorem for `spqr.SecretOutput.recv_secret`**:

Maps `Recv s` to `some s`, all other variants to `none`. Total and infallible. -/
@[step]
theorem SecretOutput.recv_secret_spec (self : SecretOutput) :
    SecretOutput.recv_secret self ⦃ (result : Option (alloc.vec.Vec U8)) =>
      result = match self with
        | .Recv s => some s
        | _ => none ⦄ := by
  unfold SecretOutput.recv_secret
  match self with
  | .None => simp
  | .Send s => simp
  | .Recv s => simp

end spqr
