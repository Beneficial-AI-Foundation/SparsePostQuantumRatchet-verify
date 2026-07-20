/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Encoding.Polynomial.PolyConst.ToPoly

/-!
# Spec theorem for `spqr::encoding::polynomial::const_polys_to_polys::{FnMut}::call_mut`

Aeneas extraction of the closure `|x| x.to_poly()` inside `const_polys_to_polys`
(src/encoding/polynomial.rs, line 466). The `call_mut` method takes a unit closure state `c`
and a `PolyConst N`, delegates to `PolyConst.to_poly`, and returns the resulting `Poly` paired
with the unchanged state. Postconditions (coefficient preservation, polynomial identity in
`GF216[X]`, closure unchanged) are inherited directly from `to_poly_spec`.
-/

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf Polynomial

namespace spqr.encoding.polynomial.const_polys_to_polys.closure.Insts.CoreOpsFunctionFnMutTupleSharedPolyConstPoly

/--
**Spec theorem for `encoding.polynomial.const_polys_to_polys.closure.Insts.CoreOpsFunctionFnMutTupleSharedPolyConstPoly.call_mut`**:

Always succeeds. Delegates to `PolyConst.to_poly` and returns the result with the closure
state unchanged. Guarantees:
• `result.coefficients.val = tupled_args.coefficients.val`
• `result.toGF216Poly = listToGF216Poly tupled_args.coefficients.val`
• `c' = c`
-/
@[step]
theorem call_mut_spec
    {N : Usize}
    (c : const_polys_to_polys.closure N)
    (tupled_args : PolyConst N) :
    call_mut c tupled_args ⦃ (result : Poly × const_polys_to_polys.closure N) =>
      result.1.coefficients.val = tupled_args.coefficients.val ∧
      result.1.toGF216Poly = listToGF216Poly tupled_args.coefficients.val ∧
      result.2 = c ⦄ := by
  unfold call_mut
  step*

end spqr.encoding.polynomial.const_polys_to_polys.closure.Insts.CoreOpsFunctionFnMutTupleSharedPolyConstPoly
