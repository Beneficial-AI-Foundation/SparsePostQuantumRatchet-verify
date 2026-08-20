/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Chain.DEFAULT_CHAIN_PARAMS
/-! # Spec theorem for `spqr::chain::{spqr::chain::ChainParams}::into_pb`

Converts `ChainParams` to its protobuf form `ChainParamsPB`, replacing each field with `0` when
it equals the library default (zero-as-default convention) and copying it verbatim otherwise.
The conversion is total — no arithmetic, only two equality checks and a struct literal.

**Source**: spqr/src/chain.rs -/

open Aeneas Aeneas.Std Result spqr

namespace spqr.chain.ChainParams

/-- **Spec theorem for `spqr.chain.ChainParams.into_pb`**:

Converts `ChainParams` to protobuf form, zeroing each field that equals the default and copying
it verbatim otherwise. Each field is characterized by two biconditionals: `result.f = 0` iff the
source equals the default or is already zero; `result.f = self.f` iff the source differs from the
default. The function is total (no panics). Proved by unfolding and `split <;> split <;> simp_all`.
-/
@[step]
theorem into_pb_spec (self : chain.ChainParams) :
    into_pb self ⦃ (result : proto.pq_ratchet.ChainParams) =>
      (result.max_jump = 0#u32 ↔ self.max_jump = chain.DEFAULT_CHAIN_PARAMS.max_jump ∨
        self.max_jump = 0#u32) ∧
      (result.max_jump = self.max_jump ↔ self.max_jump ≠ chain.DEFAULT_CHAIN_PARAMS.max_jump) ∧
      (result.max_ooo_keys = 0#u32 ↔ self.max_ooo_keys = chain.DEFAULT_CHAIN_PARAMS.max_ooo_keys ∨
          self.max_ooo_keys = 0#u32) ∧
      (result.max_ooo_keys = self.max_ooo_keys ↔
        self.max_ooo_keys ≠ chain.DEFAULT_CHAIN_PARAMS.max_ooo_keys) ⦄ := by
  unfold into_pb
  split <;> split <;> simp_all

end spqr.chain.ChainParams
