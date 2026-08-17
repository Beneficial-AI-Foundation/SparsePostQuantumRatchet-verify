/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
/-! # Spec theorem for `spqr::chain::{impl core::clone::Clone for spqr::chain::ChainParams}::clone`

`ChainParams` is a `Copy` type with two `u32` fields, so its derived `clone` is the identity.
After Aeneas extraction this reduces to `clone self = ok self`. The function never fails.

**Source**: spqr/src/chain.rs (lines 16:9-16:14)
-/

open Aeneas Aeneas.Std Result spqr

namespace spqr.chain.ChainParams.Insts.CoreCloneClone

/-- **Spec theorem for `spqr.chain.ChainParams.Insts.CoreCloneClone.clone`**:

`clone self` returns `ok self` (identity clone). Always succeeds; both fields are preserved. -/
@[step]
theorem clone_spec (self : chain.ChainParams) :
    clone self ⦃ (result : chain.ChainParams) =>
      result = self ⦄ := by
  unfold clone
  simp

end spqr.chain.ChainParams.Insts.CoreCloneClone
