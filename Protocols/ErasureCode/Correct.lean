/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Alessandro D'Angelo
-/
import Protocols.ErasureCode.Correctness.Decode

/-! # Correctness of the concrete SPQR erasure code -/

open ErasureCode.SPQRReedSolomon

namespace Protocols.ErasureCode

noncomputable def concreteSpqrErasureCode
    (k : ℕ) (hk : k ≤ 2 ^ 16) (hk_pos : 0 < k) :
    ErasureCode (Chunk GF16) where
  N := 2 ^ 16
  N_pos := by norm_num
  nchunk := k
  nchunk_pos := hk_pos
  nchunk_le_N := hk
  encode := encodeConcrete k hk
  decode := decodeConcrete k hk

theorem encodeChunks_toModel
    (k : ℕ) (hk : k ≤ 2 ^ 16) (hk_pos : 0 < k)
    (hk_tab : k ∈ ({1, 3, 5, 30, 34, 36} : Finset ℕ))
    (M : Fin k → Chunk GF16) (I : Finset (Fin (2 ^ 16))) :
    (concreteSpqrErasureCode k hk hk_pos).encodeChunks M I =
      (modelEC k hk hk_pos).encodeChunks M I := by
  classical
  unfold ErasureCode.encodeChunks
  congr 1
  apply Function.Embedding.ext
  intro i
  change (i, encodeConcrete k hk M i) =
    (i, (modelEC k hk hk_pos).encode M i)
  exact Prod.ext rfl (encode_toModel k hk hk_pos hk_tab M i)

theorem concreteSpqrErasureCode_correct
    (k : ℕ) (hk : k ≤ 2 ^ 16) (hk_pos : 0 < k)
    (hk_tab : k ∈ ({1, 3, 5, 30, 34, 36} : Finset ℕ)) :
    (concreteSpqrErasureCode k hk hk_pos).Correct := by
  intro M I
  change
    (k ≤ I.card →
        decodeConcrete k hk
            ((concreteSpqrErasureCode k hk hk_pos).encodeChunks M I) = some M) ∧
      (I.card < k →
        decodeConcrete k hk
            ((concreteSpqrErasureCode k hk hk_pos).encodeChunks M I) = none)
  rw [encodeChunks_toModel k hk hk_pos hk_tab M I]
  rw [decode_toModel k hk hk_pos M I]
  exact (modelEC_correct k hk hk_pos) M I

end Protocols.ErasureCode
