/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
/-! # Spec theorem for
  `spqr::encoding::polynomial::{impl core::cmp::PartialOrd<Pt> for Pt}::partial_cmp`

Orders `Pt` values by comparing x-coordinate `u16` values via `OrdU16.cmp`; y-coordinate is
ignored. Always returns `some _`.

**Source**: spqr/src/encoding/polynomial.rs -/

open Aeneas Aeneas.Std Result

namespace spqr.encoding.polynomial.Pt.Insts.CoreCmpPartialOrdPt

/--
**Spec theorem for `spqr.encoding.polynomial.Pt.Insts.CoreCmpPartialOrdPt.partial_cmp`**:

Compares two `Pt` values by their x-coordinate `u16` values, returning
`some (compare self.x.value.val other.x.value.val)`. Always succeeds; y-coordinate is ignored. -/
@[step]
theorem partial_cmp_spec (self other : Pt) :
    partial_cmp self other ⦃ (result : Option Ordering) =>
      result = some (compare self.x.value.val other.x.value.val) ⦄ := by
  unfold partial_cmp
  simp only [lift]
  step*

end spqr.encoding.polynomial.Pt.Insts.CoreCmpPartialOrdPt
