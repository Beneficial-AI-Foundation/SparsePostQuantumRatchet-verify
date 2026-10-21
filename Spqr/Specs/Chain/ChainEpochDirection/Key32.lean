/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import Spqr.Specs.Chain.ChainEpochDirection.Key
-- For the private platform-independent core `key_spec_all_core` and `maxOoo_imp_raw_ooo`.
import all Spqr.Specs.Chain.ChainEpochDirection.Key

/-! # 32-bit platform variant of the spec for `ChainEpochDirection::key`

The only differences from `key_spec` in `Key.lean` are:

  - The maxOoo bound is tightened from `390451572` to `108458770`.  On a 32-bit platform
    `Usize.max = 2³² − 1`, so the GC trim threshold `(maxOoo * 11/10 + 1) * 36` must fit in
    32 bits, which requires `maxOoo < 108458770`.
  - No `h_platform` hypothesis is needed.

The proof is an instance of the platform-independent core `key_spec_all_core` in `Key.lean`.

**Source**: spqr/src/chain.rs -/

@[expose] public section

open Aeneas Aeneas.Std Result spqr crypto

namespace spqr.chain.ChainEpochDirection

/-- **Spec theorem for `spqr.chain.ChainEpochDirection.key`** (32-bit platform):

The full postcondition `chain.cedKeyPost self ats params result.1 result.2`, covering the
equal, less, greater and greater-jump cases.

Identical to `key_spec` but with the tighter maxOoo bound `108458770` and no `h_platform`
hypothesis.

**Source**: spqr/src/chain.rs, lines 248:4-297:5
-/
@[step]
theorem key_spec_32 (self : chain.ChainEpochDirection) (ats : U32)
    (params : proto.pq_ratchet.ChainParams)
    (h_next_len : self.next.length = 32)
    (h_maxooo_bound : (chain.maxOoo params).val < 108458770)
    (h_kh_cap : self.prev.data.length + 36 * (ats.val - self.ctr.val) ≤ Usize.max)
    (h_prev_aligned : self.prev.data.length % 36 = 0)
    (h_prev_ctr : self.prev.data.length ≤ 36 * self.ctr.val)
    (h_ooo_no_overflow : ats + (chain.maxOoo params).val ≤ U32.max) :
    key self ats params ⦃ (result : (core.result.Result (alloc.vec.Vec U8) Error) ×
        chain.ChainEpochDirection) =>
      chain.cedKeyPost self ats params result.1 result.2 ⦄ := by
  have h_raw := maxOoo_imp_raw_ooo params _ h_maxooo_bound
  exact key_spec_all_core self ats params h_next_len (by omega) (by scalar_tac) h_kh_cap
    h_prev_aligned h_prev_ctr h_ooo_no_overflow

end spqr.chain.ChainEpochDirection
