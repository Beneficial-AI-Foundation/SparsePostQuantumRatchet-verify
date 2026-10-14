/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module
public import Spqr.Crypto.Fips203.NTT.Packed
/-!
# FIPS 203 NTT — kernel verification shard 1 (basis vectors 64–127)

One quarter of the kernel check that the packed clone of Algorithm 7 maps each
packed basis vector `δⱼ` to the packed closed form of `nttSpec δⱼ`.  Split into
four files so each compiles in well under 30 s and `lake` can run them in
parallel.
-/

@[expose] public section

namespace Fips203

set_option maxHeartbeats 400000 in
-- `decide +kernel` evaluates the 7-layer butterfly network on 64 packed basis
-- vectors inside the kernel; this exceeds the default budget.
/-- Kernel verification for basis vectors `64 ≤ j < 128`. -/
lemma nttP_deltaP_eq_formulaP_1 :
    ∀ j ∈ List.range 64, nttP (deltaP (j + 64)) = formulaP (j + 64) := by
  decide +kernel

end Fips203
