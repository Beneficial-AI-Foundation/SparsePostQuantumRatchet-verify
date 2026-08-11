/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
/-!
# Spec theorem for `spqr::SecretOutput::send_secret`

`SecretOutput::send_secret` is a projection accessor on the `SecretOutput` enum.  It returns
`Some(&secret)` when the output is `Send(secret)`, indicating that a shared secret was derived
that should be mixed into the sending chain before encrypting the next message.  For `Recv(_)`
and `None` variants, it returns `None`.

The function is a pure pattern match with no error paths — it always succeeds for any valid
`SecretOutput` value.

**Source**: spqr/src/lib.rs (lines 152:4-158:5)
-/

open Aeneas Aeneas.Std Result

namespace spqr

/--
**Spec theorem for `spqr.SecretOutput.send_secret`**:

• Takes a `SecretOutput` value `self`.
• Pattern-matches on `self`:
  - `Send(s)` → returns `some s`
  - `Recv(_)` → returns `none`
  - `None`    → returns `none`
• The function always succeeds (no panic) for any `SecretOutput` input.

The result satisfies the projection postcondition:

  `(self = .Send s → result = some s) ∧`
  `(self = .Recv _ ∨ self = .None → result = none)`

**Source**: spqr/src/lib.rs (lines 152:4-158:5)
-/
@[step]
theorem SecretOutput.send_secret_spec (self : SecretOutput) :
    SecretOutput.send_secret self ⦃ (result : Option (alloc.vec.Vec U8)) =>
      (∀ s, self = .Send s → result = some s) ∧
      (self = .None → result = none) ∧
      (∀ s, self = .Recv s → result = none) ⦄ := by
  unfold SecretOutput.send_secret
  sorry

end spqr
