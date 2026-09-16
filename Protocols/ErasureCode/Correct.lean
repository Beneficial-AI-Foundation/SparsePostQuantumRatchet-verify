/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Alessandro D'Angelo
-/
import Protocols.ErasureCode.Correctness.Decode
import Protocols.ErasureCode.Model.Specs

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

## VerifiedErasureCode approach

`VerifiedErasureCode model ec` (in `Model/Specs.lean`) says that `ec` agrees with the reference
`model`, which is itself correct; `VerifiedErasureCode.correct` then gives `ec.Correct`. So the
work below is to build one instance; correctness follows with no further argument.

Here `model` is `modelErasureCode k hk hk_pos` and `ec` is `concreteErasureCode k hk hk_pos`.
Both have type `ErasureCode (Chunk GF16) (2 ^ 16) k`, so they share `N` and `nchunk` by
construction: no parameter equalities and no casts arise, and the two correspondence fields are
discharged by `encode_toModel` and `decode_toModel` directly.
-/

open ErasureCode.SPQRReedSolomon

namespace Protocols.ErasureCode

/-- Package the concrete encoder and decoder for the structural bound `k ≤ 2^16`. This constructor
supplies `ErasureCode` operations at block length `2 ^ 16` and threshold `k`. Correctness is the
separate theorem below, and extracted encoder failures have already been mapped to `default`. -/
noncomputable def concreteErasureCode
    (k : ℕ) (hk : k ≤ 2 ^ 16) (hk_pos : 0 < k) :
    ErasureCode (Chunk GF16) (2 ^ 16) k where
  N_pos := by norm_num
  nchunk_pos := hk_pos
  nchunk_le_N := hk
  encode := encodeConcrete k hk
  decode := decodeConcrete k hk

/-- The concrete SPQR erasure code verified against the reference model
`modelErasureCode k hk hk_pos`, for the six supported table sizes.

Both codes have type `ErasureCode (Chunk GF16) (2 ^ 16) k`, so the class carries only the two
correspondence proofs and the model’s correctness, and those are exactly the statements
`encode_toModel` and `decode_toModel` already prove.

The two code parameters pin down `k`, `hk` and `hk_pos`, and `hk_tab` is carried as a `Fact` so
that it too can be synthesized. That makes this a genuine `instance`: callers name the two codes
and typeclass resolution supplies the rest. -/
noncomputable instance verifiedConcreteErasureCode
    (k : ℕ) (hk : k ≤ 2 ^ 16) (hk_pos : 0 < k)
    [hk_tab : Fact (k ∈ ({1, 3, 5, 30, 34, 36} : Finset ℕ))] :
    VerifiedErasureCode (modelErasureCode k hk hk_pos) (concreteErasureCode k hk hk_pos) where
  encode_eq_model := encode_toModel k hk hk_pos hk_tab.out
  decode_eq_model := decode_toModel k hk hk_pos
  model_correct := modelErasureCode_correct k hk hk_pos

/-- Correctness for the six supported table sizes, read off from `verifiedConcreteErasureCode`.
Honest chunks at distinct indices recover the message when at least `k` are present and decode
to `none` when fewer are present. -/
theorem concreteErasureCode_correct
    (k : ℕ) (hk : k ≤ 2 ^ 16) (hk_pos : 0 < k)
    (hk_tab : k ∈ ({1, 3, 5, 30, 34, 36} : Finset ℕ)) :
    (concreteErasureCode k hk hk_pos).Correct :=
  haveI : Fact (k ∈ ({1, 3, 5, 30, 34, 36} : Finset ℕ)) := ⟨hk_tab⟩
  VerifiedErasureCode.correct (modelErasureCode k hk hk_pos) (concreteErasureCode k hk hk_pos)

end Protocols.ErasureCode
