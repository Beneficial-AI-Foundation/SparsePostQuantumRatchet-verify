/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Beneficial AI Foundation
-/
import Protocols.ErasureCode.Model.Defs

/-!
# Erasure codes verified against a reference model

`ErasureCode.Correct` is a property each code has to establish on its own. `ErasureCode_correct`
packages the usual way of establishing it.
Then, a `low`/`concrete` erasure code implements / refiens a `high`/`abstract` one if its
`encode` and `decode` functions agree with the epinomous functions of the latter.

## Design

`ErasureCode_implem` relates two erasure codes. Both are parameters, so each application
of the class fixes the `high` code that `low` is judged against,
and the class's own fields are
only the correspondence proofs.

Since `ErasureCode` is parametrized over `N` and `nchunk`, the two codes sharing a type *is* the
statement that they share those parameters. Writing `ErasureCode_implem high low` requires
`high low : ErasureCode Sym N nchunk` for one and the same `N` and `nchunk`, so a mismatched pair
is rejected when the type is elaborated rather than generating an equality to discharge. Hence no
`N_eq`/`nchunk_eq` fields, and no `Fin.cast` anywhere in the correspondence statements: they are
plain equations between the two encoders and the two decoders.

`ErasureCode_implem.correct` construct the instance asserting correctness of `low` if it
implements a `high` instance of `ErasureCode_correct`.
-/

variable {Sym : Type} {N nchunk : ℕ}

/-- An erasure code carrying a proof of its correctness. -/
-- ANCHOR: ErasureCode_correct
class ErasureCode_correct (ec : ErasureCode Sym N nchunk) where
  /-- ec satisfies the erasure code correctness property. -/
  ec_correct : ec.Correct
-- ANCHOR_END: ErasureCode_correct

/-- An erasure code `low` implements an erasure code `high` if its encoder and decoder functions
agree with those of `high`.

The two codes share the parameters `N` and `nchunk` by having the same type, so the correspondence
fields below need no casts. -/
-- ANCHOR: ErasureCode_implem
class ErasureCode_implem (high low : ErasureCode Sym N nchunk) where
  /-- The encoder agrees with the model at every position. -/
  ec_implem_encode : ∀ (M : Fin nchunk → Sym) (i : Fin N), low.encode M i = high.encode M i

  /-- The decoder agrees with the model on honestly encoded chunk sets. This is exactly what
  `Correct` quantifies over, so a bridge proof never has to describe the decoder on arbitrary
  input. -/
  ec_implem_decode : ∀ (M : Fin nchunk → Sym) (I : Finset (Fin N)),
    low.decode (high.encodeChunks M I) = high.decode (high.encodeChunks M I)
-- ANCHOR_END: ErasureCode_implem

namespace ErasureCode_implem

/-- The honest chunk sets of the implementation and of the model coincide, since their encoders
agree at every position. -/
theorem encodeChunks_eq_model (high low : ErasureCode Sym N nchunk)
    [c : ErasureCode_implem high low] (M : Fin nchunk → Sym) (I : Finset (Fin N)) :
    low.encodeChunks M I = high.encodeChunks M I := by
  unfold ErasureCode.encodeChunks
  congr 1
  apply Function.Embedding.ext
  intro i
  exact Prod.ext rfl (c.ec_implem_encode M i)

/-- A `low` erasureCode that implements a CORRECT `high` erasureCode is itself correct -/
theorem correct (high low : ErasureCode Sym N nchunk) [c : ErasureCode_correct high]
    [i : ErasureCode_implem high low] : ErasureCode_correct low where
  ec_correct := by
    intro M I
    have hdec : low.decode (low.encodeChunks M I) = high.decode (high.encodeChunks M I) := by
      rw [encodeChunks_eq_model high low M I]
      exact i.ec_implem_decode M I
    rw [hdec]
    exact (c.ec_correct M I)

-- ANCHOR: ErasureCode_refines_some_correct
class ErasureCode_refines_some_correct (low : ErasureCode Sym N nchunk) where
  /-- assert existence of SOME high ec with same parameters -/
  ec_ref_high : ErasureCode Sym N nchunk

  /-- assert correctness of the high ec -/
  ec_ref_correct : ErasureCode_correct ec_ref_high

  /-- assert refinement property -/
  ec_ref_implem : ErasureCode_implem ec_ref_high low

-- ANCHOR_END: ErasureCode_refines_some_correct

namespace ErasureCode_refines_some_correct

/-- An instance of `ErasureCode_refines_some_correct low` is a witness of `low`'s correctness -/
theorem refines_correct (low : ErasureCode Sym N nchunk)
    [r : ErasureCode_refines_some_correct low] : ErasureCode_correct low := by
  letI : ErasureCode_correct r.ec_ref_high := r.ec_ref_correct
  letI : ErasureCode_implem r.ec_ref_high low := r.ec_ref_implem
  exact ErasureCode_implem.correct r.ec_ref_high low

end ErasureCode_refines_some_correct
end ErasureCode_implem
