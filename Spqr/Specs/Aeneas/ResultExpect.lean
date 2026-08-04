/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs

/-!
# Spec theorem for `core.result.Result.expect`

`Result::expect` unwraps `Ok(v)` to `v` or panics on `Err`.
Aeneas models this as `.ok v` or `.fail .panic`.
-/

open Aeneas Aeneas.Std Result

/-- **Spec theorem for `core.result.Result.expect` on `Ok` values**: `expect` on `.Ok v` succeeds with `v`. -/
@[step]
theorem core.result.Result.expect_ok_spec {T E : Type}
    (inst : core.fmt.Debug E)
    (v : T) (msg : Str) :
    core.result.Result.expect inst (core.result.Result.Ok v : core.result.Result T E) msg
    ⦃ result => result = v ⦄ := by
  simp [core.result.Result.expect, WP.spec_ok]
