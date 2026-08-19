/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Chain.DEFAULT_CHAIN_PARAMS
/-! # Spec theorem for
`spqr::chain::{impl core::default::Default for spqr::chain::ChainParams}::default`

`Default` for `ChainParams` returns the compile-time constant `DEFAULT_CHAIN_PARAMS`
(`max_jump = 25000`, `max_ooo_keys = 2000`). Never fails.

**Source**: spqr/src/chain.rs -/

open Aeneas Aeneas.Std Result spqr

namespace spqr.chain.ChainParams.Insts.CoreDefaultDefault

/-- **Spec theorem for `spqr.chain.ChainParams.Insts.CoreDefaultDefault.default`**:

Returns `DEFAULT_CHAIN_PARAMS` (i.e. `max_jump = 25000`, `max_ooo_keys = 2000`).
Always succeeds. Proof: unfold + `simp` with `DEFAULT_CHAIN_PARAMS_spec`. -/
@[step]
theorem default_spec :
    default ⦃ (result : chain.ChainParams) =>
      result = chain.DEFAULT_CHAIN_PARAMS ∧
      result.max_jump = 25000#u32 ∧
      result.max_ooo_keys = 2000#u32 ⦄ := by
  unfold default
  simp [chain.DEFAULT_CHAIN_PARAMS_spec]

end spqr.chain.ChainParams.Insts.CoreDefaultDefault
