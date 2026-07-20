/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import Spqr.Specs.Encoding.Polynomial.ConstPolysToPolys.CallOne
import Spqr.Specs.Aeneas.SliceIter
import Spqr.Specs.Encoding.Polynomial.ConstPolysToPolys.SliceIterMapCollect

/-!
# Spec theorem for `spqr::encoding::polynomial::const_polys_to_polys`

`const_polys_to_polys` maps a fixed-size array `[PolyConst<N>; N]` into a
`Vec<Poly>` via `cps.iter().map(|x| x.to_poly()).collect()`. This is a pure
element-wise map: each output element is `PolyConst.to_poly` of the input, a
verbatim coefficient copy that preserves the `GF216[X]` interpretation. It is
used in `from_complete_points` to convert the `COMPLETE_POINTS_POLYS_N` arrays
into the `Vec<Poly>` expected by `Poly.lagrange_sum`.

**Source**: spqr/src/encoding/polynomial.rs (lines 465:0-467:1)
-/


open Aeneas Aeneas.Std Result
open spqr.encoding.polynomial spqr.encoding.gf Polynomial

namespace spqr.encoding.polynomial

/-- Axiom: the `Iterator.map.default` + `Iterator.collect.default` pipeline is equivalent to
    the specialized `Map.Insts.CoreIterTraitsIteratorIterator.collect` applied to `⟨iter, f⟩`.

    This bridges the generated Aeneas code (which uses the generic trait-default
    `Iterator.map.default` axiom followed by `Iterator.collect.default` with the
    sorry-based `Map` iterator instance) with the hand-verified specialized collect
    implementation `Map.Insts.CoreIterTraitsIteratorIterator.collect` that uses
    `mapIteratorTransformer` (whose `next` is concretely defined).

    The axiom is sound because `Iterator.map.default` in Rust simply constructs
    `Map { iter, f }`, and collecting via the `Map` iterator instance is
    equivalent to the specialized collect. -/
private axiom map_collect_eq
    {N : Usize}
    (iter : core.slice.iter.Iter (PolyConst N))
    (f : const_polys_to_polys.closure N) :
    (do
      let m ← core.iter.traits.iterator.Iterator.map.default
        (core.iter.traits.iterator.IteratorSliceIter (PolyConst N))
        (const_polys_to_polys.closure.Insts.CoreOpsFunctionFnMutTupleSharedPolyConstPoly N)
        iter f
      core.iter.traits.iterator.Iterator.collect.default
        (core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator
          (core.iter.traits.iterator.IteratorSliceIter (PolyConst N))
          (const_polys_to_polys.closure.Insts.CoreOpsFunctionFnMutTupleSharedPolyConstPoly N))
        (core.iter.traits.collect.FromIteratorVec Poly) m)
    = core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.collect
        (core.iter.traits.iterator.IteratorSliceIter (PolyConst N))
        (const_polys_to_polys.closure.Insts.CoreOpsFunctionFnMutTupleSharedPolyConstPoly N)
        (core.iter.traits.collect.FromIteratorVec Poly)
        ⟨iter, f⟩

/--
**Spec theorem for `encoding.polynomial.const_polys_to_polys`**:

The function always succeeds and, for each index `j < N`:
  - **Length**: `result.val.length = N.val`.
  - **Coefficients**: `result[j].coefficients.val = cps[j].coefficients.val`.
  - **Polynomial identity in `GF216[X]`**:
      `result[j].toGF216Poly = listToGF216Poly cps[j].coefficients.val`.

**Source**: spqr/src/encoding/polynomial.rs (lines 465:0-467:1)
-/

@[step]
theorem const_polys_to_polys_spec {N : Usize} (cps : Array (PolyConst N) N) :
    const_polys_to_polys cps ⦃ result =>
      result.length = N.val ∧
      (∀ j < N.val,
        ∀ (hj : j < result.length) (hjc : j < cps.length),
          result[j].coefficients.val = cps[j].coefficients ∧
          result[j].toGF216Poly = listToGF216Poly cps[j].coefficients) ⦄ := by
  unfold const_polys_to_polys
  step*
  rw [map_collect_eq]
  have h := core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.collect_spec
    (⟨i, ()⟩ : core.iter.adapters.map.Map (core.slice.iter.Iter (PolyConst N))
      (const_polys_to_polys.closure N))
  simp only [core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.collect_eq] at h
  apply WP.spec_mono h
  intro result ⟨h_len, h_elts⟩
  simp_all

end spqr.encoding.polynomial
