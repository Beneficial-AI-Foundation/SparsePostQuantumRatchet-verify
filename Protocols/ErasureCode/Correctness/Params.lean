/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Alessandro D'Angelo
-/
import Protocols.ErasureCode.Contract

/-! # Concrete Reed–Solomon parameters for SPQR -/

open ErasureCode.SPQRReedSolomon

namespace Protocols.ErasureCode

noncomputable def concreteParams (k : ℕ) (hk : k ≤ 2 ^ 16) (hk_pos : 0 < k) :
    ErasureCode.ReedSolomon.Parameters GF16 where
  N := 2 ^ 16
  N_pos := by norm_num
  k := k
  k_pos := hk_pos
  k_le_N := hk
  point := fun i => Nat.toGF216 i.val
  point_injective := by
    intro a b hab
    exact Fin.ext (Nat.toGF216_injOn a.isLt b.isLt hab)

noncomputable def modelEC (k : ℕ) (hk : k ≤ 2 ^ 16) (hk_pos : 0 < k) :
    ErasureCode (Chunk GF16) :=
  ErasureCode.SPQRReedSolomon.parallelErasureCode (concreteParams k hk hk_pos)

theorem modelEC_correct (k : ℕ) (hk : k ≤ 2 ^ 16) (hk_pos : 0 < k) :
    (modelEC k hk hk_pos).Correct :=
  ErasureCode.SPQRReedSolomon.parallelErasureCode_correct _

end Protocols.ErasureCode
