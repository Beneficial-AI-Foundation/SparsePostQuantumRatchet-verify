/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
/-! # Spec theorem for
  `spqr::encoding::polynomial::{impl core::cmp::PartialOrd<Pt> for Pt}::partial_cmp`

The `PartialOrd` implementation for `Pt` — a Cartesian point `(x, y)` in GF(2¹⁶) × GF(2¹⁶) —
defines ordering solely by comparing the underlying `u16` values of the x-coordinates.  The
y-coordinate is entirely ignored for ordering purposes.

The function delegates to `core.cmp.impls.OrdU16.cmp`, which computes the standard natural-number
comparison of the `u16` bit representations, and wraps the result in `some` to produce
`Option Ordering`.

Because x-coordinate comparison is always defined (total), `partial_cmp` always returns `some _`,
never `none`.

**Source**: spqr/src/encoding/polynomial.rs (lines 55:4-57:5)
-/

open Aeneas Aeneas.Std Result

namespace spqr.encoding.polynomial.Pt.Insts.CoreCmpPartialOrdPt

/--
**Spec theorem for `spqr.encoding.polynomial.Pt.Insts.CoreCmpPartialOrdPt.partial_cmp`**:

• Takes two `Pt` values `self` and `other`, each containing an x-coordinate and y-coordinate
  as `GF16` field elements wrapping `u16` values.
• Delegates to `core.cmp.impls.OrdU16.cmp` to compare the underlying `u16` values of the
  x-coordinates:
    `core.cmp.impls.OrdU16.cmp self.x.value other.x.value`
  which computes `compare self.x.value.val other.x.value.val`.
• Returns the result wrapped in `some`, yielding an `Option Ordering`.

• The function always succeeds (no panic) for any pair of `Pt` inputs, since integer comparison
  is a total operation.
• The y-coordinate is not considered in the ordering.
• The result is always `some _`, never `none`.

The result satisfies the postcondition:

  `result = some (compare self.x.value.val other.x.value.val)`

where `compare` is the standard natural-number three-way comparison returning
`Ordering.lt`, `Ordering.eq`, or `Ordering.gt`.

The proof unfolds `partial_cmp`, simplifies the `lift` wrapping the pure `OrdU16.cmp` call, and
discharges the resulting goal with `simp`.

**Source**: spqr/src/encoding/polynomial.rs (lines 55:4-57:5)
-/
@[step]
theorem partial_cmp_spec (self other : Pt) :
    partial_cmp self other ⦃ (result : Option Ordering) =>
      result = some (compare self.x.value.val other.x.value.val) ⦄ := by
  unfold partial_cmp
  simp only [lift]
  step*

end spqr.encoding.polynomial.Pt.Insts.CoreCmpPartialOrdPt
