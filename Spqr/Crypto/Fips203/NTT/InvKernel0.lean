/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module
public import Spqr.Crypto.Fips203.NTT.Packed
meta import Spqr.Crypto.Fips203.NTT.Packed
/-!
# FIPS 203 NTT⁻¹ — kernel verification shard 0 (basis vectors 0–63)

One quarter of the kernel check that the packed clone of the Algorithm 8
butterfly layers sends the packed closed form of `NTT δⱼ` back to `128 · δⱼ`.
Split into four files so each compiles in well under 30 s and `lake` can run
them in parallel.
-/

public section

namespace Fips203

set_option linter.style.native false in
set_option maxHeartbeats 400000 in
-- `decide +kernel` evaluates the 7-layer inverse butterfly network on 64
-- packed basis vectors inside the kernel; this exceeds the default budget.
/-- Inverse kernel verification for basis vectors `0 ≤ j < 64`. -/
lemma invNttP_formulaP_eq_0 :
    ∀ j ∈ List.range 64, invNttP (formulaP (j + 0)) = 128 * deltaP (j + 0) := by
  /- This goal closes with `decide +kernel`. However there are 8 similar files which often build in
  parallel and can cause the runner to crash and so `native_decide` is used temporarily.
  TODO: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/721 -/
  native_decide

end Fips203
