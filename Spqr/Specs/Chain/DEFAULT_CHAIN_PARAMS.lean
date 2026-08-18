/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
/-!
# Spec theorem for `spqr::chain::DEFAULT_CHAIN_PARAMS`

Default `ChainParams` constant: `max_jump = 25 000` (max tolerated epoch jump)
and `max_ooo_keys = 2 000` (max retained out-of-order message keys).

**Source**: spqr/src/chain.rs -/

open Aeneas Aeneas.Std Result spqr

namespace spqr.chain

/--
**Spec theorem for `spqr.chain.DEFAULT_CHAIN_PARAMS`**:

`DEFAULT_CHAIN_PARAMS.max_jump = 25000#u32` and
`DEFAULT_CHAIN_PARAMS.max_ooo_keys = 2000#u32`, matching the Rust source. -/
@[simp]
theorem DEFAULT_CHAIN_PARAMS_spec :
    chain.DEFAULT_CHAIN_PARAMS.max_jump = 25000#u32 ∧
    chain.DEFAULT_CHAIN_PARAMS.max_ooo_keys = 2000#u32  := by
  unfold chain.DEFAULT_CHAIN_PARAMS
  grind

end spqr.chain
