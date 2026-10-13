/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Crypto.Fips203.NTT.Packed
/-!
# FIPS 203 NTT⁻¹ — kernel verification shard 2 (basis vectors 128–191)

One quarter of the kernel check that the packed clone of the Algorithm 8
butterfly layers sends the packed closed form of `NTT δⱼ` back to `128 · δⱼ`.
Split into four files so each compiles in well under 30 s and `lake` can run
them in parallel.
-/

namespace Fips203

set_option maxHeartbeats 400000 in
-- `decide +kernel` evaluates the 7-layer inverse butterfly network on 64
-- packed basis vectors inside the kernel; this exceeds the default budget.
/-- Inverse kernel verification for basis vectors `128 ≤ j < 192`. -/
lemma invNttP_formulaP_eq_2 :
    ∀ j ∈ List.range 64, invNttP (formulaP (j + 128)) = 128 * deltaP (j + 128) := by
  decide +kernel

end Fips203
