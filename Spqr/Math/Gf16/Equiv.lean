/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Alessandro D'Angelo
-/
module

public import Spqr.Math.Gf16.Field
import Spqr.Math.Gf2Poly.Basic
import Spqr.Math.Poly.CharTwo.ToGF216
import Mathlib.Data.Fintype.EquivFin
import Batteries.Data.Nat.Bitwise.Lemmas

/-!
# Natural-number representatives of `GF216`

`Nat.toGF216` is injective below `2 ^ 16`, and `GF216` has `2 ^ 16` elements.
-/

@[expose] public section

open spqr.encoding.polynomial spqr.math.gf

/-- Naturals below `2 ^ 16` have distinct images in `GF216`. -/
theorem Nat.toGF216_injOn : Set.InjOn Nat.toGF216 (Set.Iio (2 ^ 16)) := by
  intro a ha b hb hab
  apply Nat.eq_of_xor_eq_zero
  apply Nat_toGF216_eq_zero (Nat.xor_lt_two_pow ha hb)
  calc
    Nat.toGF216 (a ^^^ b) = Nat.toGF216 a + Nat.toGF216 b := by
      simp only [Nat.toGF216, natToBinaryPoly_xor, map_add]
    _ = Nat.toGF216 b + Nat.toGF216 b := by rw [hab]
    _ = 0 := CharTwo.add_self_eq_zero (Nat.toGF216 b)

/-- The finite type structure on `GF216`. -/
noncomputable instance GF216.instFintype : Fintype GF216 := Fintype.ofFinite GF216

/-- `GF216` has `2 ^ 16` elements. -/
theorem GF216.card_eq : Fintype.card GF216 = 2 ^ 16 := by
  rw [Fintype.card_eq_nat_card]
  exact GaloisField.card 2 16 (by norm_num)
