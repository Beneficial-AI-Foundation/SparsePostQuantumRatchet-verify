/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Encoding.Polynomial.ConstPolysToPolys.CallMut

/-! # Spec theorem for `spqr::encoding::polynomial::const_polys_to_polys::{FnOnce}::call_once`

The `FnOnce` variant of the closure `|x| x.to_poly()` inside `const_polys_to_polys`.
Delegates to `call_mut`, discarding the returned closure state.

Postcondition (inherited from `call_mut_spec`):
  - `result.coefficients.val = pc.coefficients.val`
  - `result.toGF216Poly = listToGF216Poly pc.coefficients.val`

**Source**: spqr/src/encoding/polynomial.rs -/

open Aeneas Aeneas.Std Result

namespace spqr.encoding.polynomial.const_polys_to_polys.closure.Insts
namespace CoreOpsFunctionFnOnceTupleSharedPolyConstPoly

/--
**Spec theorem for `encoding.polynomial.const_polys_to_polys.closure.Insts.
CoreOpsFunctionFnOnceTupleSharedPolyConstPoly.call_once`**:

`call_once c pc` delegates to `call_mut` and drops the closure state. Always succeeds since
`PolyConst.to_poly` is total. Guarantees:
  - `result.coefficients.val = pc.coefficients.val`
  - `result.toGF216Poly = listToGF216Poly pc.coefficients.val` -/
@[step]
theorem call_once_spec
    {N : Usize}
    (c : const_polys_to_polys.closure N)
    (pc : PolyConst N) :
    call_once c pc ⦃ (result : Poly) =>
      result.coefficients.val = pc.coefficients.val ∧
      result.toGF216Poly = listToGF216Poly pc.coefficients.val ⦄ := by
  unfold call_once
  step*

end CoreOpsFunctionFnOnceTupleSharedPolyConstPoly
end spqr.encoding.polynomial.const_polys_to_polys.closure.Insts
