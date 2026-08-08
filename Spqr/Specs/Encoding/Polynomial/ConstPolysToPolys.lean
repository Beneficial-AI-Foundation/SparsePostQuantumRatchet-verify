/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong, Lacramioara Astefanoaei
-/
import Spqr.Specs.Aeneas.SliceIter
import Spqr.Specs.Aeneas.MapCollectBridge
import Spqr.Specs.Encoding.Polynomial.ConstPolysToPolys.SliceIterMapCollect

/-!
# Spec theorem for `spqr::encoding::polynomial::const_polys_to_polys`

`const_polys_to_polys` maps a fixed-size array `[PolyConst<N>; N]` into a
`Vec<Poly>` via `cps.iter().map(|x| x.to_poly()).collect()`. This is a pure
element-wise map: each output element is `PolyConst.to_poly` of the input, a
verbatim coefficient copy that preserves the `GF216[X]` interpretation. It is
used in `from_complete_points` to convert the `COMPLETE_POINTS_POLYS_N` arrays
into the `Vec<Poly>` expected by `Poly.lagrange_sum`.

**Source**: spqr/src/encoding/polynomial.rs -/

open Aeneas Aeneas.Std Result

namespace spqr.encoding.polynomial

/--
**Spec theorem for `encoding.polynomial.const_polys_to_polys`**:

The function always succeeds and, for each index `j < N`:
  - **Length**: `result.val.length = N.val`.
  - **Coefficients**: `result[j].coefficients.val = cps[j].coefficients.val`.
  - **Polynomial identity in `GF216[X]`**:
      `result[j].toGF216Poly = listToGF216Poly cps[j].coefficients.val`. -/
@[step]
theorem const_polys_to_polys_spec {N : Usize} (cps : Array (PolyConst N) N) :
    const_polys_to_polys cps ⦃ (result : alloc.vec.Vec Poly) =>
      result.length = N.val ∧
      (∀ j < N.val,
        ∀ (hj : j < result.length) (hjc : j < cps.length),
          result[j].coefficients.val = cps[j].coefficients ∧
          result[j].toGF216Poly = listToGF216Poly cps[j].coefficients) ⦄ := by
  unfold const_polys_to_polys
  step*
  -- Cross from the generated instance (whose `next` is `sorry`, aeneas#1043) to the
  -- hand-written `mapIteratorTransformer` semantics, then fold back up into `collect`.
  rw [Spqr.Aeneas.collect_default_bridge (inferInstanceAs (Subsingleton Unit)) _ _ _ m,
    ← core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.collect_spec]
  apply WP.spec_mono
    (core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.collect_const_polys_spec m)
  intro result ⟨h_len, h_elts⟩
  simp_all

end spqr.encoding.polynomial
