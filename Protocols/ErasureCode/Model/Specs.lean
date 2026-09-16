/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Beneficial AI Foundation
-/
import Protocols.ErasureCode.Model.Defs

/-!
# Erasure codes verified against a reference model

`ErasureCode.Correct` is a property each code has to establish on its own. `VerifiedErasureCode`
packages the usual way of establishing it: the implementation's `encode` and `decode` agree with
a reference model already known to be correct.

## Design

`VerifiedErasureCode model ec` relates two erasure codes. Both are parameters, so each application
of the class fixes the model the implementation is judged against, and the class's own fields are
only the correspondence proofs and the model's correctness.

Since `ErasureCode` is parametrized over `N` and `nchunk`, the two codes sharing a type *is* the
statement that they share those parameters. Writing `VerifiedErasureCode model ec` requires
`model ec : ErasureCode Sym N nchunk` for one and the same `N` and `nchunk`, so a mismatched pair
is rejected when the type is elaborated rather than generating an equality to discharge. Hence no
`N_eq`/`nchunk_eq` fields, and no `Fin.cast` anywhere in the correspondence statements: they are
plain equations between the two encoders and the two decoders.

`VerifiedErasureCode.correct` turns those into `ec.Correct`, so an instance needs no separate
correctness argument.
-/

variable {Sym : Type} {N nchunk : ℕ}

/-- An erasure code `ec` carrying a proof of its own correctness: its encoder and decoder agree
with the reference `model`, which is itself correct.

The two codes share the parameters `N` and `nchunk` by having the same type, so the correspondence
fields below need no casts. -/
-- ANCHOR: VerifiedErasureCode
class VerifiedErasureCode (model ec : ErasureCode Sym N nchunk) where
  /-- The encoder agrees with the model at every position. -/
  encode_eq_model : ∀ (M : Fin nchunk → Sym) (i : Fin N), ec.encode M i = model.encode M i
  /-- The decoder agrees with the model on honestly encoded chunk sets. This is exactly what
  `Correct` quantifies over, so a bridge proof never has to describe the decoder on arbitrary
  input. -/
  decode_eq_model : ∀ (M : Fin nchunk → Sym) (I : Finset (Fin N)),
    ec.decode (model.encodeChunks M I) = model.decode (model.encodeChunks M I)
  /-- The reference model satisfies the erasure code correctness property. -/
  model_correct : model.Correct
-- ANCHOR_END: VerifiedErasureCode

namespace VerifiedErasureCode

/-- The honest chunk sets of the implementation and of the model coincide, since their encoders
agree at every position. -/
theorem encodeChunks_eq_model (model ec : ErasureCode Sym N nchunk)
    [c : VerifiedErasureCode model ec] (M : Fin nchunk → Sym) (I : Finset (Fin N)) :
    ec.encodeChunks M I = model.encodeChunks M I := by
  unfold ErasureCode.encodeChunks
  congr 1
  apply Function.Embedding.ext
  intro i
  exact Prod.ext rfl (c.encode_eq_model M i)

/-- Every `VerifiedErasureCode` instance makes its code correct: the class's fields already imply
`Correct`. -/
theorem correct (model ec : ErasureCode Sym N nchunk) [c : VerifiedErasureCode model ec] :
    ec.Correct := by
  intro M I
  have hdec : ec.decode (ec.encodeChunks M I) = model.decode (model.encodeChunks M I) := by
    rw [encodeChunks_eq_model model ec M I]
    exact c.decode_eq_model M I
  rw [hdec]
  exact c.model_correct M I

end VerifiedErasureCode
