/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Alessandro D'Angelo
-/
import Protocols.ErasureCode.Correctness.Decode

/-!
# Correctness of the concrete SPQR erasure code

`ErasureCode` packages deterministic encode and decode functions. Its `Correct` predicate is a
separate property. The result below proves the deterministic extensional fragment of Definition
A.6 and strengthens the paper's exactly-`k` clause to recovery from at least `k` honest chunks. It
establishes no computability, polynomial-time or PPT, asymptotic-cost, or protocol-security
theorem.

The decoder correspondence covers honest chunks at distinct indices and starts from a fresh
decoder. Its fold invariant proves that equation without identifying persistent states produced
by different input orders. It makes no claim about arbitrary input sets or streaming states.
-/

open ErasureCode.SPQRReedSolomon

namespace Protocols.ErasureCode

/-- Package the concrete encoder and decoder for the structural bound `k ≤ 2^16`. This constructor
supplies `ErasureCode` operations. Correctness is the separate theorem below, and extracted
encoder failures have already been mapped to `default`. -/
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

/-- Correctness for the six supported table sizes. Honest chunks at distinct indices recover the
message when at least `k` are present and decode to `none` when fewer are present. -/
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
