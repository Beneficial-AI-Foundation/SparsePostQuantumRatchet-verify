/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Chain.ChainParams.MaxOooKeysOrDefault
/-! # Spec theorem for `spqr::chain::{spqr::proto::pq_ratchet::ChainParams}::trim_size`

Computes the GC threshold as `max_ooo * 11 / 10 + 1`, where `max_ooo` comes from
`max_ooo_keys_or_default` (default 2000). The bound `max_ooo < 390451572` ensures no overflow
even on 32-bit targets. Reintroduced here as `h_ooo` since Aeneas erases `hax_lib::assume!`.

**Source**: spqr/src/chain.rs -/

open Aeneas Aeneas.Std Result spqr

namespace spqr.chain.ChainParams

/-- **Spec theorem for `spqr.chain.ChainParams.trim_size`**:

Shows `result.val = max_ooo * 11 / 10 + 1` where `max_ooo` is the defaulted OOO budget.
Two biconditionals capture the verbatim vs default branches:
  • `result.val = self.max_ooo_keys.val * 11 / 10 + 1 ↔ self.max_ooo_keys > 0#u32`
  • `result.val = 2201 ↔ self.max_ooo_keys = 0#u32 ∨ self.max_ooo_keys = 2000#u32`

The `∨ 2000` disjunct covers the case where the caller supplied exactly the default.
No overflow: `h_ooo` bounds `max_ooo` so `max_ooo * 11` fits in 32 bits. -/
@[step]
theorem trim_size_spec (self : proto.pq_ratchet.ChainParams)
    (h_ooo : self.max_ooo_keys.val < 390451572) :
    trim_size self ⦃ (result : Std.Usize) =>
      (result.val = self.max_ooo_keys.val * 11 / 10 + 1 ↔ self.max_ooo_keys > 0#u32) ∧
      (result.val = 2201 ↔
        self.max_ooo_keys = 0#u32 ∨ self.max_ooo_keys = 2000#u32) ⦄ := by
  unfold trim_size max_ooo_keys_or_default
  split <;>
    (step* <;>
      simp_all only [gt_iff_lt, UScalar.lt_equiv, UScalar.ofNatCore_val_eq,
        DEFAULT_CHAIN_PARAMS_spec] <;>
      scalar_tac)

end spqr.chain.ChainParams
