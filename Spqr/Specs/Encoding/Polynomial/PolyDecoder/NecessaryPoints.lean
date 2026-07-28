/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs

/-! # Spec theorem for `spqr::encoding::polynomial::{PolyDecoder}::necessary_points`

Distributes `pts_needed` across 16 polynomials via Euclidean division: each gets
`pts_needed / 16`, and the first `pts_needed % 16` get one extra. Always succeeds
(division by 16 is infallible; the `+1` cannot overflow `usize`).

**Source**: spqr/src/encoding/polynomial.rs -/

open Aeneas Aeneas.Std Result

namespace spqr.encoding.polynomial.PolyDecoder

/-- **Spec theorem for `encoding.polynomial.PolyDecoder.necessary_points`**:

Returns `pts_needed / 16 + (if poly < pts_needed % 16 then 1 else 0)`.
Always succeeds — division/modulo by 16 are infallible and `+1` cannot overflow. -/
@[step]
theorem necessary_points_spec (self : PolyDecoder) (poly : Usize) :
    necessary_points self poly ⦃ (result : Usize) =>
      result = self.pts_needed.val / 16 + if poly < self.pts_needed.val % 16 then 1 else 0 ⦄ := by
  unfold necessary_points
  step*
  grind

end spqr.encoding.polynomial.PolyDecoder
