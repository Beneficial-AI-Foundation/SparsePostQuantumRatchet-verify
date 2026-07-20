/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Encoding.Polynomial.Pt.PartialCmp
/-!
# Spec theorem for `spqr::encoding::polynomial::{impl core::cmp::Ord for Pt}::cmp`

Total ordering on `Pt` by comparing x-coordinates' underlying `u16` values.
Delegates to `partial_cmp` (always `some _`) and unwraps. Points with the same
x but different y compare as equal.

**Source**: spqr/src/encoding/polynomial.rs (lines 47:4-49:5)
-/

open Aeneas Aeneas.Std Result

namespace spqr.encoding.polynomial.Pt.Insts.CoreCmpOrd

/--
**Spec theorem for `spqr.encoding.polynomial.Pt.Insts.CoreCmpOrd.cmp`**:

Delegates to `partial_cmp` and unwraps the result. Always succeeds since
`partial_cmp` is total. Only the x-coordinate participates in comparison.

Postcondition: `result = compare self.x.value.val other.x.value.val`.

**Source**: spqr/src/encoding/polynomial.rs (lines 47:4-49:5)
-/
@[step]
theorem cmp_spec (self other : Pt) :
    cmp self other ⦃ (result : Ordering) =>
      result = compare self.x.value.val other.x.value.val ⦄ := by
  unfold cmp
  step*

end spqr.encoding.polynomial.Pt.Insts.CoreCmpOrd
