/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Liao Zhang
-/
import Lean.Meta.Tactic.Simp

/-!
# Simp attributes for the SPQR mathematical bridge

This file declares the named simp sets used across `Spqr.Math` and `Spqr.Specs`. It has to be
a separate file because in Lean 4 an attribute cannot be used in the file where it is declared
(see `Mathlib.Tactic.Attr.Register` for the same pattern).
-/

/-- Simp set for the machine-to-mathlib bridge: rewrites machine-level representations
(`GF16` values, `Poly` coefficient vectors, `Nat` bit operations) into their mathematical
counterparts (`GF216 = GaloisField 2 16`, `GF216[X]`, `(ZMod 2)[X]`).

Lemmas tagged with this attribute should rewrite *towards* the mathlib normal form, e.g.
`natToBinaryPoly (a ^^^ b) = natToBinaryPoly a + natToBinaryPoly b` or
`(listToGF216Poly cs).coeff m = ...`, so that after `simp only [gf216_simp]` a goal speaks the
language of mathlib polynomials. -/
register_simp_attr gf216_simp
