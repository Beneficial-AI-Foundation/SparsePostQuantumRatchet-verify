/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Encoding.Gf.GF16.New

/-! # Spec theorem for `PolyEncoder::point_at` closure#1 `call_mut`

The closure `|(x, y)| Pt { x: GF16::new(x as u16), y: *y }` inside
`PolyEncoder::point_at` maps an enumerated `(usize, &GF16)` pair to a point
`Pt { x, y }`: `x` is the index cast to `u16` and wrapped via `GF16::new`,
and `y` is the referenced value unchanged.  Aeneas extracts it as `call_mut`,
taking a `Unit` closure state and a `(Usize × GF16)` argument, returning the
built `Pt` paired with the unchanged state.

**Source**: spqr/src/encoding/polynomial.rs -/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf

namespace spqr.encoding.polynomial.PolyEncoder.point_at
namespace closure_1.Insts.CoreOpsFunctionFnMutTuplePairUsizeSharedGF16Pt

/-- **Spec theorem for `PolyEncoder.point_at.closure_1.call_mut`**:

Given a `Unit` closure state `c` and a `(Usize × GF16)` argument whose index
fits in a `u16` (`tupled_args.1.val < 2 ^ 16`), `call_mut` succeeds and yields
`(result, c)` where:

• `result.1.x.toGF216 = tupled_args.1.val.toGF216` — the x-coordinate lifts to
  the same GF(2¹⁶) element as the index;
• `result.1.y = tupled_args.2` — the y-coordinate is unchanged;
• `result.2 = c` — the closure state is unchanged. -/
@[step]
theorem call_mut_spec
    (c : PolyEncoder.point_at.closure_1)
    (tupled_args : Usize × GF16)
    (h : tupled_args.1.val < 2 ^ 16) :
    call_mut c tupled_args ⦃ (result : Pt × PolyEncoder.point_at.closure_1) =>
      result.1.x.toGF216 = tupled_args.1.val.toGF216 ∧
      result.1.y = tupled_args.2 ∧
      result.2 = c ⦄ := by
  unfold call_mut
  obtain ⟨x, y⟩ := tupled_args
  simp only [] at h ⊢
  step*

end closure_1.Insts.CoreOpsFunctionFnMutTuplePairUsizeSharedGF16Pt
end spqr.encoding.polynomial.PolyEncoder.point_at
