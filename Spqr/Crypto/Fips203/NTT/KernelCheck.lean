/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Crypto.Fips203.NTT.Kernel0
import Spqr.Crypto.Fips203.NTT.Kernel1
import Spqr.Crypto.Fips203.NTT.Kernel2
import Spqr.Crypto.Fips203.NTT.Kernel3
import Spqr.Crypto.Fips203.NTT.InvKernel0
import Spqr.Crypto.Fips203.NTT.InvKernel1
import Spqr.Crypto.Fips203.NTT.InvKernel2
import Spqr.Crypto.Fips203.NTT.InvKernel3
/-!
# FIPS 203 NTT — combined kernel verification

Glues the shards `Kernel0`–`Kernel3` and `InvKernel0`–`InvKernel3` into the
two statements used by `RoundTrip.lean`: for every `j < 256`,

* the packed clone of Algorithm 7 sends `δⱼ` to the packed closed form of
  `nttSpec δⱼ`  (`nttP_deltaP_eq_formulaP`);
* the packed clone of the Algorithm 8 butterfly layers sends that closed form
  back to `128 · δⱼ`  (`invNttP_formulaP_eq`).
-/

namespace Fips203

/-- **Kernel verification**: the packed-natural clone of Algorithm 7 maps each
packed basis vector to the packed closed form — 256 concrete GMP computations
checked by the Lean kernel (`decide +kernel`), in four shards of 64. -/
lemma nttP_deltaP_eq_formulaP (j : ℕ) (hj : j < 256) :
    nttP (deltaP j) = formulaP j := by
  rcases Nat.lt_or_ge j 64 with h | h
  · exact nttP_deltaP_eq_formulaP_0 j (List.mem_range.mpr h)
  rcases Nat.lt_or_ge j 128 with h2 | h2
  · have := nttP_deltaP_eq_formulaP_1 (j - 64) (List.mem_range.mpr (by omega))
    rwa [Nat.sub_add_cancel h] at this
  rcases Nat.lt_or_ge j 192 with h3 | h3
  · have := nttP_deltaP_eq_formulaP_2 (j - 128) (List.mem_range.mpr (by omega))
    rwa [Nat.sub_add_cancel h2] at this
  · have := nttP_deltaP_eq_formulaP_3 (j - 192) (List.mem_range.mpr (by omega))
    rwa [Nat.sub_add_cancel h3] at this

/-- **Inverse kernel verification**: the packed clone of the Algorithm 8
butterfly layers maps the packed closed form of `NTT δⱼ` to `128 · δⱼ` — 256
concrete GMP computations checked by the Lean kernel, in four shards of 64. -/
lemma invNttP_formulaP_eq (j : ℕ) (hj : j < 256) :
    invNttP (formulaP j) = 128 * deltaP j := by
  rcases Nat.lt_or_ge j 64 with h | h
  · exact invNttP_formulaP_eq_0 j (List.mem_range.mpr h)
  rcases Nat.lt_or_ge j 128 with h2 | h2
  · have := invNttP_formulaP_eq_1 (j - 64) (List.mem_range.mpr (by omega))
    rwa [Nat.sub_add_cancel h] at this
  rcases Nat.lt_or_ge j 192 with h3 | h3
  · have := invNttP_formulaP_eq_2 (j - 128) (List.mem_range.mpr (by omega))
    rwa [Nat.sub_add_cancel h2] at this
  · have := invNttP_formulaP_eq_3 (j - 192) (List.mem_range.mpr (by omega))
    rwa [Nat.sub_add_cancel h3] at this

end Fips203
