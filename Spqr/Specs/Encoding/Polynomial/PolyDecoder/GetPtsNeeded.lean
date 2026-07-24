/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs

/-!
# Spec theorem for `spqr::encoding::polynomial::{PolyDecoder}::get_pts_needed`

Pure field accessor returning `self.pts_needed`. Always succeeds.

**Source**: spqr/src/encoding/polynomial.rs -/

open Aeneas Aeneas.Std

namespace spqr.encoding.polynomial.PolyDecoder

/-- **Spec theorem for `encoding.polynomial.PolyDecoder.get_pts_needed`**:

Always succeeds, returning `self.pts_needed` unchanged. -/
@[step]
theorem get_pts_needed_spec (self : encoding.polynomial.PolyDecoder) :
    get_pts_needed self ⦃ (result : Std.Usize) =>
      result = self.pts_needed ⦄ := by
  unfold get_pts_needed
  simp [WP.spec_ok]

end spqr.encoding.polynomial.PolyDecoder
