/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Encoding.Polynomial.PolyEncoder.PointAt.CallMut

/-! # Spec theorem for `PolyEncoder::point_at` closure#1 `call_once`

`FnOnce` variant of the `.map(|(x, y)| Pt { x: GF16::new(x as u16), y: *y })`
closure in `point_at` (lines 641–644). Delegates to `call_mut`, discarding the
returned closure state and keeping only the `Pt`. Postcondition inherited from
`call_mut_spec`:

  - `result.x.toGF216 = p.1.val.toGF216`
  - `result.y = p.2`

**Source**: spqr/src/encoding/polynomial.rs -/

open Aeneas Aeneas.Std Result spqr.encoding.gf

namespace spqr.encoding.polynomial.PolyEncoder.point_at.closure_1
namespace Insts.CoreOpsFunctionFnOnceTuplePairUsizeSharedGF16Pt
/-- **Spec theorem for `PolyEncoder.point_at.closure_1.call_once`**:

Succeeds when `p.1.val < 2 ^ 16`. Returns a `Pt` with:
• `result.x.toGF216 = p.1.val.toGF216`
• `result.y = p.2` -/
@[step]
theorem call_once_spec
    (c : PolyEncoder.point_at.closure_1)
    (p : Usize × GF16)
    (h : p.1.val < 2 ^ 16) :
    call_once c p ⦃ (result : Pt) =>
      result.x.toGF216 = p.1.val.toGF216 ∧
      result.y = p.2 ⦄ := by
  unfold call_once
  step*

end Insts.CoreOpsFunctionFnOnceTuplePairUsizeSharedGF16Pt
end spqr.encoding.polynomial.PolyEncoder.point_at.closure_1
