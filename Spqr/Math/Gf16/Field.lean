/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Math.Gf16.Irreducible
import Spqr.Code.Types
import Mathlib.FieldTheory.Finite.GaloisField

/-! # The construction of GF(2¹⁶)

`GF216 = GaloisField 2 16` as a quotient of `(ZMod 2)[X]` by
`POLY_GF2`, together with the canonical ring homomorphism `φ` and the
interpretation function `Nat.toGF216`.
-/

open Polynomial

abbrev GF216 := GaloisField 2 16

namespace spqr.math.gf

lemma exists_ringHom_modByMonic :
    ∃ φ : GF2Poly →+* GF216,
      φ POLY_GF2 = 0 := by
  classical
  have hmonic : POLY_GF2.Monic := POLY_GF2_monic
  have hne : POLY_GF2 ≠ 0 := hmonic.ne_zero
  have hirr : Irreducible POLY_GF2 := POLY_GF2_irreducible
  haveI : Fact (Irreducible POLY_GF2) := ⟨hirr⟩
  let pb := AdjoinRoot.powerBasis hne
  haveI : Module.Finite (ZMod 2) (AdjoinRoot POLY_GF2) := pb.finite
  haveI : Fintype (AdjoinRoot POLY_GF2) := Module.fintypeOfFintype pb.basis
  have hdim : Module.finrank (ZMod 2) (AdjoinRoot POLY_GF2) = 16 := by
    rw [pb.finrank, AdjoinRoot.powerBasis_dim, POLY_GF2_natDegree]
  have hcard : Fintype.card (AdjoinRoot POLY_GF2) = 2 ^ 16 := by
    rw [Module.card_fintype pb.basis, ZMod.card, Fintype.card_fin,
        AdjoinRoot.powerBasis_dim, POLY_GF2_natDegree]
  let e : AdjoinRoot POLY_GF2 ≃ₐ[ZMod 2] GF216 :=
    GaloisField.algEquivGaloisFieldOfFintype 2 16 hcard
  have hmk : (AdjoinRoot.mk POLY_GF2) POLY_GF2 = 0 := AdjoinRoot.mk_self
  refine ⟨(e : AdjoinRoot POLY_GF2 →+* GF216).comp (AdjoinRoot.mk POLY_GF2), ?_⟩
  rw [RingHom.comp_apply, hmk, map_zero]

/-- A chosen ring homomorphism `GF2Poly →+* GF216` that vanishes on
`POLY_GF2`.  We pick one provided by `exists_ringHom_modByMonic`. -/
noncomputable def φ : GF2Poly →+* GF216 :=
  Classical.choose exists_ringHom_modByMonic

/-- The chosen ring homomorphism `φ` sends `POLY_GF2` to `0`. -/
lemma hφ : φ POLY_GF2 = 0 :=
  Classical.choose_spec exists_ringHom_modByMonic

/-- Interpret a natural number as an element of `GF216 = GF(2¹⁶)`,
using the canonical chain
`Nat → GF2Poly → GF216`
where the first arrow is `natToGF2Poly` (binary expansion as a
GF(2)-polynomial) and the second arrow is the chosen ring homomorphism
`φ` (which factors through `GF2Poly / (POLY_GF2)`). -/
noncomputable def _root_.Nat.toGF216 (n : Nat) : GF216 :=
  φ (natToGF2Poly n)

end spqr.math.gf

open spqr.encoding.gf in
/-- Interpret a `GF16` field element as an element of `GF216 = GF(2¹⁶)`,
using the canonical chain `GF16.value.val → GF2Poly → GF216`. -/
noncomputable def GF16toGF216 (g : GF16) : GF216 := g.value.val.toGF216
