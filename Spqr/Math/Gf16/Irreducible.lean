/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Math.Gf16.Basic
import Spqr.Math.Gf2Poly.NatRep

/-! # Irreducibility of POLY_GF2

Proof that `POLY_GF2 = X¹⁶ + X¹² + X³ + X + 1` is irreducible over
`GF(2) = ZMod 2`, using the computable Nat-level representation and
bridge lemmas from `Spqr.Math.Gf2Poly.NatRep`.
-/

open Polynomial

namespace spqr.math.gf

/-- **`POLY_GF2 = X¹⁶ + X¹² + X³ + X + 1` is irreducible over `GF(2) = ZMod 2`.**

The proof proceeds by computational verification: we implement a GF(2)
polynomial remainder function via XOR bit-manipulation on natural numbers,
check that no monic polynomial of degree 1 through 8 divides `0x1100b`
(the bit-encoding of `POLY_GF2`), and link this computation back to the
algebraic statement using `natToGF2Poly` and
`Monic.irreducible_iff_lt_natDegree_lt`. -/
theorem POLY_GF2_irreducible : Irreducible POLY_GF2 := by
  have hmonic := POLY_GF2_monic
  rw [hmonic.irreducible_iff_lt_natDegree_lt POLY_GF2_ne_one, POLY_GF2_natDegree]
  intro q hq_monic hq_deg hq_dvd
  simp only [Nat.reduceDiv, Finset.mem_Ioc] at hq_deg
  obtain ⟨b, hb_ge, hb_eq⟩ := monic_eq_natToGF2Poly q (by omega)
  rw [← hb_eq, ← natToGF2Poly_POLY] at hq_dvd
  have hlog_eq : b.log2 = q.natDegree := by
    rw [← natToGF2Poly_natDegree_eq_log2 b hb_ge, hb_eq]
  have hlog_pos : 1 ≤ b.log2 := by omega
  have hlog_le : b.log2 ≤ 8 := by omega
  set d := b.log2
  set lower := b - 2 ^ d
  have h2d_le_b : 2 ^ d ≤ b := Nat.log2_self_le (show b ≠ 0 by omega)
  have hb_decomp : b = 2 ^ d + lower := by omega
  have hb_lt_2d1 : b < 2 ^ (d + 1) :=
    (Nat.log2_lt (show b ≠ 0 by omega)).mp (by omega : b.log2 < b.log2 + 1)
  have h2d1_eq : 2 ^ (d + 1) = 2 * 2 ^ d := by ring
  have hlower_lt : lower < 2 ^ d := by omega
  have hmod_ne : gf2Mod 0x1100b b ≠ 0 := by
    rw [hb_decomp]
    exact gf2_no_divisor_all d hlog_pos hlog_le lower hlower_lt
  exact gf2Mod_ne_zero_of_not_dvd 0x1100b b hb_ge hmod_ne hq_dvd

end spqr.math.gf
