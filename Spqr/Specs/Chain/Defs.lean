/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
/-!
# Definitions for `ChainEpochDirection` key-loop helpers

Reusable pure definitions used by the chain-key advancement loop and related specs.
-/

open Aeneas Aeneas.Std Result spqr

namespace spqr.chain

/-- Pure version of `max_ooo_keys_or_default`: returns `params.max_ooo_keys` if positive,
    otherwise the default (2000). -/
noncomputable def maxOoo (params : proto.pq_ratchet.ChainParams) : U32 :=
  if params.max_ooo_keys > 0#u32 then params.max_ooo_keys
  else chain.DEFAULT_CHAIN_PARAMS.max_ooo_keys

end spqr.chain
