/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Chain.DEFAULT_CHAIN_PARAMS
/-!
# Spec theorem for `spqr::chain::{spqr::proto::pq_ratchet::ChainParams}::max_ooo_keys_or_default`

Returns `max_ooo_keys` when positive, otherwise falls back to `DEFAULT_CHAIN_PARAMS.max_ooo_keys`
(= 2 000). This resolves the protobuf zero-means-unset ambiguity. Total and allocation-free.

**Source**: spqr/src/chain.rs -/

open Aeneas Aeneas.Std Result spqr

namespace spqr.chain.ChainParams

/-- **Spec theorem for `spqr.chain.ChainParams.max_ooo_keys_or_default`**:

Result equals `self.max_ooo_keys` iff it is positive; equals the default iff the field is zero or
already matches the default. Always succeeds (no panic, no overflow). -/
@[step]
theorem max_ooo_keys_or_default_spec (self : proto.pq_ratchet.ChainParams) :
    max_ooo_keys_or_default self ⦃ (result : Std.U32) =>
      (result = self.max_ooo_keys ↔ self.max_ooo_keys > 0#u32) ∧
      (result = chain.DEFAULT_CHAIN_PARAMS.max_ooo_keys ↔
        self.max_ooo_keys = 0#u32
        ∨ self.max_ooo_keys = chain.DEFAULT_CHAIN_PARAMS.max_ooo_keys) ⦄ := by
  unfold max_ooo_keys_or_default
  split
  · simp_all
  · simp_all only [gt_iff_lt, UScalar.lt_equiv, UScalar.ofNatCore_val_eq, not_lt,
    nonpos_iff_eq_zero, DEFAULT_CHAIN_PARAMS_spec, ne_eq, UScalar.neq_to_neq_val,
    iff_false, Nat.not_eq, OfNat.zero_ne_ofNat, not_false_eq_true, OfNat.ofNat_ne_zero,
    Nat.ofNat_pos, not_lt_zero, or_false, or_self, UScalar.val_not_eq_imp_not_eq, WP.spec_ok,
    true_iff, true_and]
    scalar_tac

end spqr.chain.ChainParams
