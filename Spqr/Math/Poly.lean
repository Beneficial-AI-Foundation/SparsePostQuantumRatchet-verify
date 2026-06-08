/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Mathlib.RingTheory.Polynomial.Basic

/-!
# GF(2¹⁶)[X] Polynomial Library

Consolidated definitions, lemmas, and theorems about polynomials over
`GF(2¹⁶) = GaloisField 2 16`, connecting the implementation type `spqr.encoding.polynomial.Poly`
(which stores coefficients as a vector of `GF16` elements in ascending degree order) to the Mathlib
polynomial ring `GF216[X]`.

A `Poly` represents a polynomial over GF(2¹⁶) via its coefficient list:
  `coefficients = [a₀, a₁, …, aₙ]`
represents the polynomial `a₀ + a₁·X + … + aₙ·Xⁿ`.  The zero polynomial is the unique
polynomial with no terms (empty coefficient list), and it evaluates to `0 : GF(2¹⁶)` at every point.

The identifier names follow Mathlib's conventions for similar objects:

* `GF216Poly` for the type abbreviation `GF216[X]`, matching the pattern used by `BinaryPoly` in
  `Spqr.Math.Gf2Poly.Basic`.
* `listToGF216Poly` for the canonical map from `List GF16` to `GF216Poly`, matching the pattern of
  `natToBinaryPoly`.
* `Poly.toGF216Poly` for the canonical bridge from the Aeneas-extracted `Poly` to `GF216Poly`,
  matching the pattern of `Nat.toGF216`.
* `GF216Poly.neg_eq` and `GF216Poly.sub_eq_add` for the basic algebraic facts in characteristic 2,
  matching `BinaryPoly.neg_eq` and `BinaryPoly.sub_eq_add`.
* `GF216.two_eq_zero` for the characteristic-2 fact in `GF216`.

Note: this development is intended to be upstream-friendly so that it can be reused by other
projects working with the same Galois field.

The bridge from the implementation to the mathematics is:

```
  Implementation Layer          Mathematical Layer
  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  GF16 (value : U16)    ──────► GF216 = GF(2¹⁶)
          │    GF16.toGF216         │
          │                        │
  Vec<GF16>             ──────► GF216[X]
          │    listToGF216Poly     │
          │                        │
  Poly                  ──────► GF216[X]
               Poly.toGF216Poly
```

## Main definitions

### Core polynomial bridge
* `listToGF216Poly` — interprets a `List GF16` as a polynomial in `GF216[X]`.
* `Poly.toGF216Poly` — bridge from the Aeneas-extracted `Poly` to `GF216[X]`.
* `Poly.evalAt` — evaluation of the mathematical polynomial at a `GF16` point.

### Lagrange interpolation support
* `prodLinearFactors` — product `∏_{j=start}^{stop−1} (X − C(pts[j].x.toGF216))`.
* `lagrangeDenomProd` — denominator product `∏_{j, pts[j].x ≠ pi.x} (pi.x − pts[j].x)`.
* `lagrangeScaleGF216` — Lagrange scaling factor `pi.y * denomProd^(2^16−2)`.
* `lagrangeBasisPoly` — Lagrange basis polynomial `∏_{j≠i} (X − pts[j].x)`.
* `lagrangeInterpolantSum` — partial Lagrange interpolant sum.

### Horner scheme
* `hornerAccum` — Horner-scheme accumulator for polynomial evaluation.

### Trailing polynomial (for `lagrange_interpolate_prepare`)
* `expectedTrailingPoly` — expected trailing sub-polynomial after k iterations.

## Conventions

- `GF216`  = `GaloisField 2 16` (the finite field, from `Spqr.Math.Gf`).
- `GF216Poly` = `GF216[X]` (the univariate polynomial ring over GF(2¹⁶)).
- `GF16.toGF216` maps a `spqr.encoding.gf.GF16` element (U16 value) to `GF216` via the `Nat.toGF216`
  bridge from `Spqr.Math.Gf`.
- `listToGF216Poly` interprets a `List GF16` as a polynomial in `GF216[X]`.
- `Poly.toGF216Poly` is the canonical bridge from the Aeneas-extracted
  `spqr.encoding.polynomial.Poly` to the mathematical `GF216Poly`.
-/

open Aeneas Aeneas.Std Result
open Polynomial
open spqr.encoding.gf spqr.math.gf

abbrev GF216Poly := GF216[X]


namespace spqr.encoding.polynomial

/-! ## Inhabited instances -/

deriving instance Inhabited for spqr.encoding.gf.GF16

instance : Inhabited spqr.encoding.polynomial.Pt where
  default := ⟨⟨0#u16⟩, ⟨0#u16⟩⟩

/-! ## Core definitions -/

/--
Interpret a list of `GF16` coefficients (in ascending degree order) as a polynomial in
`GF(2¹⁶)[X]`.

Given `cs = [a₀, a₁, …, aₙ]`, this produces:

  `C(a₀.toGF216) + C(a₁.toGF216)·X + … + C(aₙ.toGF216)·Xⁿ`

where `C : GF216 →+* GF216[X]` is the constant-polynomial embedding. The sum is indexed by `Fin
cs.length`, ensuring well-typed access to each coefficient.
-/
noncomputable def listToGF216Poly (cs : List spqr.encoding.gf.GF16) : GF216Poly :=
  ∑ i : Fin cs.length, C ((cs.get i).toGF216) * X ^ i.val

/--
Interpret a `Poly` as a mathematical polynomial in `GF(2¹⁶)[X]`.

This is the canonical bridge between the Aeneas-extracted implementation type
`spqr.encoding.polynomial.Poly` and the Mathlib polynomial ring `GF216[X]`.  It reads the
coefficient vector from the `Poly` and maps each `GF16` coefficient through `GF16.toGF216`.
-/
noncomputable def Poly.toGF216Poly (p : Poly) : GF216Poly :=
  listToGF216Poly p.coefficients.val

/-! ## Zero polynomial characterization -/

/--
**The empty coefficient list produces the zero polynomial.**

`listToGF216Poly [] = 0` because `Fin 0` is empty, so the sum over `Fin [].length` yields the
additive identity.
-/
lemma listToGF216Poly_nil :
    listToGF216Poly [] = 0 := by
  simp [listToGF216Poly]

/--
**A `Poly` with an empty coefficient vector represents the zero polynomial in `GF(2¹⁶)[X]`.**
-/
theorem Poly.toGF216Poly_eq_zero (p : Poly)
    (h : p.coefficients.length = 0) :
    p.toGF216Poly = 0 := by
  unfold Poly.toGF216Poly
  have hnil : p.coefficients.val = [] :=
    List.eq_nil_of_length_eq_zero h
  rw [hnil]
  exact listToGF216Poly_nil

/-- **`listToGF216Poly [] = 0`** (simp-normal form). -/
@[simp]
lemma listToGF216Poly_empty :
    listToGF216Poly ([] : List spqr.encoding.gf.GF16) = 0 :=
  listToGF216Poly_nil

/-! ## Coefficient characterization and basic lemmas of `listToGF216Poly` -/

/--
The coefficient of `listToGF216Poly cs` at position `m` is `cs[m].toGF216` when `m < cs.length`, and
`0` otherwise.
-/
lemma listToGF216Poly_coeff (cs : List spqr.encoding.gf.GF16) (m : Nat) :
    (listToGF216Poly cs).coeff m =
      if hm : m < cs.length
      then (cs.get ⟨m, hm⟩).toGF216
      else 0 := by
  unfold listToGF216Poly
  simp only [finset_sum_coeff, coeff_C_mul, coeff_X_pow]
  split
  · rename_i hm
    rw [Finset.sum_eq_single_of_mem ⟨m, hm⟩ (Finset.mem_univ _)
        (fun ⟨j, hj⟩ _ hjm => by simp [show m ≠ j from fun h => hjm (Fin.ext h.symm)])]
    simp
  · rename_i hm
    push Not at hm
    exact Finset.sum_eq_zero fun ⟨i, hi⟩ _ => by
      simp [show m ≠ i from by omega]

/--
Coefficients at positions `≥ cs.length` are zero.
-/
lemma listToGF216Poly_coeff_eq_zero (cs : List spqr.encoding.gf.GF16)
    (m : Nat) (hm : cs.length ≤ m) :
    (listToGF216Poly cs).coeff m = 0 := by
  rw [listToGF216Poly_coeff]
  simp [show ¬(m < cs.length) from by omega]

/-! ## Singleton and cons decomposition -/

/--
A single-coefficient list `[a]` produces the constant polynomial `C (a.toGF216)` in `GF(2¹⁶)[X]`.
-/
lemma listToGF216Poly_singleton (a : spqr.encoding.gf.GF16) :
    listToGF216Poly [a] = C (a.toGF216) := by
  simp [listToGF216Poly, Finset.univ_unique]

/--
**Decomposition: `listToGF216Poly (c :: cs) = C(c.toGF216) + X · listToGF216Poly cs`.**

This is the cons-cell decomposition that mirrors the Horner-scheme evaluation pattern.
-/
lemma listToGF216Poly_cons
    (c : spqr.encoding.gf.GF16)
    (cs : List spqr.encoding.gf.GF16) :
    listToGF216Poly (c :: cs) =
      C (c.toGF216) + X * listToGF216Poly cs := by
  ext m
  cases m with
  | zero =>
    simp only [coeff_add, listToGF216Poly_coeff,
               dif_pos (show 0 < (c :: cs).length from by simp)]
    simp only [List.get_eq_getElem, List.getElem_cons_zero,
               coeff_C_zero, coeff_X_mul_zero, add_zero]
  | succ n =>
    simp only [coeff_add, coeff_C_succ, zero_add, coeff_X_mul,
               listToGF216Poly_coeff]
    by_cases hlt : n + 1 < (c :: cs).length
    · rw [dif_pos hlt, dif_pos (show n < cs.length from by simp at hlt; omega)]
      congr 1
    · rw [dif_neg hlt, dif_neg (show ¬(n < cs.length) from by simp at hlt ⊢; omega)]

/-! ## Properties of `GF16.toGF216` -/

/--
**`GF16.toGF216` maps the zero GF16 element to `0 : GF216`.**
-/
lemma GF16.toGF216_zero_val (g : spqr.encoding.gf.GF16) (h : g.value.val = 0) :
    g.toGF216 = 0 := by
  unfold GF16.toGF216 Nat.toGF216
  rw [h]
  simp [natToBinaryPoly_zero, map_zero]

/--
**`GF16.toGF216` preserves the one element.**
-/
lemma GF16.toGF216_one_val (g : spqr.encoding.gf.GF16) (h : g.value.val = 1) :
    g.toGF216 = 1 := by
  unfold GF16.toGF216 Nat.toGF216
  rw [h]
  simp [natToBinaryPoly_one, map_one]

/--
**Bridge: `getElem!` with `toGF216` equals `listToGF216Poly` coefficient.**

Connects the Lean list indexing `cs[j]!.toGF216` to the mathematical coefficient
`(listToGF216Poly cs).coeff j`, handling the out-of-bounds case.
-/
lemma getElem_bang_toGF216_eq_coeff
    (cs : List GF16) (j : Nat) :
    (cs[j]!).toGF216 = (listToGF216Poly cs).coeff j := by
  rw [listToGF216Poly_coeff]
  by_cases hj : j < cs.length
  · rw [dif_pos hj, List.get_eq_getElem]
    grind
  · rw [dif_neg hj]
    have : (cs[j]! : spqr.encoding.gf.GF16) = default := by
      grind
    rw [this]; exact GF16.toGF216_zero_val _ (by rfl)

/-! ## Characteristic-2 facts in `GF216` and `GF216Poly` -/

/--
**GF(2¹⁶) has characteristic 2**: `(2 : GF216) = 0`.
-/
lemma GF216.two_eq_zero : (2 : GF216) = 0 :=
  CharP.cast_eq_zero GF216 2

/--
**In `GF216`, every element added to itself gives zero.**

This is the fundamental `x + x = 0` identity in characteristic 2.
-/
lemma GF216.add_self_eq_zero (x : GF216) : x + x = 0 := by
  have h2 : (2 : GF216) = 0 := GF216.two_eq_zero
  have : x + x = 2 * x := by ring
  rw [this, h2, zero_mul]

/--
**In `GF216Poly`, every element is its own negation.**

This is a consequence of characteristic 2: `a + a = 0` implies `-a = a`.  This parallels
`BinaryPoly.neg_eq` from `Spqr.Math.Gf`, now lifted from `BinaryPoly` to `GF216Poly`.
-/
lemma GF216Poly.neg_eq (a : GF216Poly) : -a = a := by
  have h : a + a = 0 := by
    ext n; simp only [coeff_add, coeff_zero]
    calc (a.coeff n) + (a.coeff n) = 2 * (a.coeff n) := by ring
      _ = 0 * (a.coeff n) := by rw [GF216.two_eq_zero]
      _ = 0 := by ring
  exact neg_eq_of_add_eq_zero_left h

/--
**In `GF216Poly`, subtraction equals addition.**

Direct consequence of `GF216Poly.neg_eq`: `a - b = a + (-b) = a + b`. This mirrors
`BinaryPoly.sub_eq_add` from `Spqr.Math.Gf`, and is the algebraic reason that `GF16::sub` in the
Rust implementation is identical to `GF16::add` (both are XOR).
-/
lemma GF216Poly.sub_eq_add (a b : GF216Poly) : a - b = a + b := by
  rw [sub_eq_add_neg, GF216Poly.neg_eq]

/-! ## Polynomial evaluation bridge -/

/--
Evaluate the mathematical interpretation of a `Poly` at a `GF16` point.
-/
noncomputable def Poly.evalAt (p : Poly) (x : GF16) : GF216 :=
  (p.toGF216Poly).eval (x.toGF216)

/--
**Evaluating the zero polynomial at any point gives `0 : GF216`.**
-/
lemma Poly.evalAt_zero_poly (p : Poly) (x : GF16)
    (h : p.coefficients.length = 0) :
    p.evalAt x = 0 := by
  unfold Poly.evalAt
  rw [Poly.toGF216Poly_eq_zero p h]
  simp

/--
**Evaluation of `listToGF216Poly` equals the coefficient sum.**

This is the key linking lemma for verifying `Poly.compute_at`.
-/
lemma listToGF216Poly_eval (cs : List spqr.encoding.gf.GF16) (a : GF216) :
    (listToGF216Poly cs).eval a =
      ∑ i : Fin cs.length,
        (cs.get i).toGF216 * a ^ i.val := by
  unfold listToGF216Poly
  simp [eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X]

/-! ## Linking lemmas: `listToGF216Poly` and list operations -/

/--
**Extending the coefficient list by one element corresponds to adding a new highest-degree term.**
-/
lemma listToGF216Poly_append_singleton
    (cs : List spqr.encoding.gf.GF16) (a : spqr.encoding.gf.GF16) :
    listToGF216Poly (cs ++ [a]) =
      listToGF216Poly cs + C (a.toGF216) * X ^ cs.length := by
  ext m
  simp only [listToGF216Poly_coeff, coeff_add, coeff_C_mul, coeff_X_pow]
  by_cases hm1 : m < cs.length
  · -- m < cs.length < cs.length + 1: LHS = cs[m], RHS = cs[m] + 0
    have hm2 : m < (cs ++ [a]).length := by simp; omega
    have hm3 : m ≠ cs.length := by omega
    rw [dif_pos hm2, dif_pos hm1]
    simp only [hm3, if_false, mul_zero, add_zero]
    congr 1
    simp [List.get_eq_getElem, List.getElem_append_left hm1]
  · push Not at hm1
    by_cases hm2 : m = cs.length
    · -- m = cs.length: LHS = a, RHS = 0 + a
      subst hm2
      have hlt : cs.length < (cs ++ [a]).length := by simp
      have hnotlt : ¬(cs.length < cs.length) := by omega
      rw [dif_pos hlt, dif_neg hnotlt]
      simp only [ite_true, mul_one, zero_add]
      congr 1
      simp [List.get_eq_getElem, List.getElem_append_right (Nat.le_refl cs.length)]
    · -- m > cs.length: LHS = 0, RHS = 0 + 0
      have hm3 : ¬(m < cs.length) := by omega
      have hm4 : ¬(m < (cs ++ [a]).length) := by simp; omega
      rw [dif_neg hm4, dif_neg hm3]
      simp [hm2]

/--
**Pointwise addition of equal-length coefficient lists corresponds to polynomial addition in
`GF216[X]`.**
-/
lemma listToGF216Poly_add (cs ds : List spqr.encoding.gf.GF16)
    (hlen : cs.length = ds.length)
    (rs : List spqr.encoding.gf.GF16)
    (hrs : rs.length = cs.length)
    (hcoeff : ∀ i (hi : i < cs.length),
      (rs.get ⟨i, by omega⟩).toGF216 =
        (cs.get ⟨i, hi⟩).toGF216 +
        (ds.get ⟨i, by omega⟩).toGF216) :
    listToGF216Poly rs =
      listToGF216Poly cs + listToGF216Poly ds := by
  ext m
  simp only [listToGF216Poly_coeff, coeff_add]
  by_cases hm : m < cs.length
  · simp only [hm, show m < ds.length from by omega, show m < rs.length from by omega, dif_pos]
    exact hcoeff m hm
  · push Not at hm
    simp [show ¬(m < cs.length) from by omega,
          show ¬(m < ds.length) from by omega,
          show ¬(m < rs.length) from by omega]

/--
**`listToGF216Poly` of `drop 1` relates to the original polynomial by division by `X`.**

If the constant-term coefficient of a `GF16` list has `toGF216 = 0`, then
`listToGF216Poly cs = X · listToGF216Poly (cs.drop 1)`.
-/
lemma listToGF216Poly_eq_X_mul_drop_one
    (cs : List spqr.encoding.gf.GF16)
    (h0 : (listToGF216Poly cs).coeff 0 = 0) :
    listToGF216Poly cs = X * listToGF216Poly (cs.drop 1) := by
  ext m
  cases m with
  | zero =>
    simp only [coeff_X_mul_zero, h0]
  | succ n =>
    rw [coeff_X_mul, listToGF216Poly_coeff, listToGF216Poly_coeff]
    by_cases hn : n + 1 < cs.length
    · have hdn : n < (cs.drop 1).length := by rw [List.length_drop]; omega
      rw [dif_pos hn, dif_pos hdn]
      congr 1
      simp only [List.get_eq_getElem]
      simp only [List.getElem_drop]
      grind
    · have hdn : ¬(n < (cs.drop 1).length) := by rw [List.length_drop]; omega
      rw [dif_neg hn, dif_neg hdn]

/--
If all coefficients of a list, interpreted via `GF16.toGF216`, match those of a polynomial `q` at
in-range positions, and `q` has zero coefficients beyond the list length, then `listToGF216Poly cs =
q`.
-/
lemma listToGF216Poly_eq_of_coeffs
    (cs : List GF16) (q : GF216Poly)
    (h_in : ∀ (m : Nat) (hm : m < cs.length),
      (cs.get ⟨m, hm⟩).toGF216 = q.coeff m)
    (h_out : ∀ m, cs.length ≤ m → q.coeff m = 0) :
    listToGF216Poly cs = q := by
  ext m
  rw [listToGF216Poly_coeff]
  split
  · rename_i hm; exact h_in m hm
  · rename_i hm; push Not at hm; exact (h_out m hm).symm

/-! ## Product of linear factors -/

/--
**Product of linear factors** `∏_{j=start}^{stop−1} (X − C(pts[j].x.toGF216))`.

This is the target polynomial that `lagrange_interpolate_prepare` constructs.  It returns `1` when
`start ≥ stop` or `start ≥ pts.length` (empty product).
-/
noncomputable def prodLinearFactors
    (pts : List Pt) (start stop : Nat) : GF216Poly :=
  if h : start < stop ∧ start < pts.length then
    (X - C ((pts.get ⟨start, h.2⟩).x.toGF216)) *
      prodLinearFactors pts (start + 1) stop
  else 1
termination_by stop - start

/-- When `start ≥ stop` or `start ≥ pts.length`, the product is `1` (empty product). -/
@[simp]
lemma prodLinearFactors_base (pts : List Pt) (start stop : Nat)
    (h : ¬(start < stop ∧ start < pts.length)) :
    prodLinearFactors pts start stop = 1 := by
  unfold prodLinearFactors; rw [dif_neg h]

/-- One-step unfolding of `prodLinearFactors` from the left. -/
lemma prodLinearFactors_step (pts : List Pt) (start stop : Nat)
    (h1 : start < stop) (h2 : start < pts.length) :
    prodLinearFactors pts start stop =
      (X - C ((pts.get ⟨start, h2⟩).x.toGF216)) *
        prodLinearFactors pts (start + 1) stop := by
  conv_lhs => unfold prodLinearFactors
  rw [dif_pos ⟨h1, h2⟩]

/--
One-step unfolding of `prodLinearFactors` from the right (snoc form).
-/
private lemma prodLinearFactors_snoc_aux (pts : List Pt) (stop : Nat)
    (h2 : stop < pts.length) :
    ∀ d s, s + d = stop → s ≤ stop →
      prodLinearFactors pts s (stop + 1) =
        prodLinearFactors pts s stop *
          (X - C ((pts.get ⟨stop, h2⟩).x.toGF216)) := by
  intro d
  induction d with
  | zero =>
    intro s hs hle
    have hseq : stop = s := by omega
    subst hseq
    rw [prodLinearFactors_step pts stop (stop + 1) (by omega) h2,
        prodLinearFactors_base pts (stop + 1) (stop + 1) (by omega),
        prodLinearFactors_base pts stop stop (by omega)]
    ring
  | succ n ih =>
    intro s hs hle
    rw [prodLinearFactors_step pts s (stop + 1) (by omega) (by omega),
        prodLinearFactors_step pts s stop (by omega) (by omega)]
    rw [ih (s + 1) (by omega) (by omega)]
    ring

lemma prodLinearFactors_snoc (pts : List Pt) (start stop : Nat)
    (h1 : start ≤ stop) (h2 : stop < pts.length) :
    prodLinearFactors pts start (stop + 1) =
      prodLinearFactors pts start stop *
        (X - C ((pts.get ⟨stop, h2⟩).x.toGF216)) :=
  prodLinearFactors_snoc_aux pts stop h2 (stop - start) start (by omega) h1

/-- Evaluation of `prodLinearFactors` at a root is zero. -/
lemma prodLinearFactors_eval_root (pts : List Pt) (start stop : Nat)
    (j : Nat) (hj1 : start ≤ j) (hj2 : j < stop) (hj3 : j < pts.length) :
    (prodLinearFactors pts start stop).eval
      ((pts.get ⟨j, hj3⟩).x.toGF216) = 0 := by
  suffices h : ∀ (d : Nat) (start : Nat), stop - start = d → start ≤ j →
      (prodLinearFactors pts start stop).eval
        ((pts.get ⟨j, hj3⟩).x.toGF216) = 0 from
    h (stop - start) start rfl hj1
  intro d
  induction d with
  | zero => intro start hd; omega
  | succ n ih =>
    intro start hd hj1'
    rw [prodLinearFactors_step pts start stop (by omega) (by omega)]
    simp only [eval_mul]
    by_cases hjs : j = start
    · subst hjs; simp [eval_sub, eval_X, eval_C]
    · have := ih (start + 1) (by omega) (by omega)
      rw [this]; ring

/-- Splitting `prodLinearFactors` at a midpoint. -/
lemma prodLinearFactors_split_at
    (pts : List Pt) (mid n : Nat)
    (hmid : mid ≤ n) (hn : n ≤ pts.length) :
    prodLinearFactors pts 0 n =
      prodLinearFactors pts 0 mid * prodLinearFactors pts mid n := by
  induction n with
  | zero =>
    have : mid = 0 := by omega
    subst this; simp
  | succ k ih =>
    by_cases hmk : mid = k + 1
    · subst hmk; simp
    · rw [prodLinearFactors_snoc pts 0 k (by omega) (by omega : k < pts.length),
          ih (by omega) (by omega),
          prodLinearFactors_snoc pts mid k (by omega) (by omega : k < pts.length)]
      ring

/-- The full product factors as `(X − pts[i].x) · lagrangeBasisPoly pts i`. -/
lemma prodLinearFactors_eq_factor_mul_basis
    (pts : List Pt) (i : Nat)
    (hi : i < pts.length) :
    prodLinearFactors pts 0 pts.length =
      (X - C ((pts.get ⟨i, hi⟩).x.toGF216)) *
        (prodLinearFactors pts 0 i *
          prodLinearFactors pts (i + 1) pts.length) := by
  rw [prodLinearFactors_split_at pts (i + 1) pts.length (by omega) (le_refl _),
      prodLinearFactors_snoc pts 0 i (by omega) hi]
  ring

/-- Degree bound for `prodLinearFactors`. -/
lemma natDegree_prodLinearFactors_le
    (pts : List Pt) (s t : Nat) (hs : s ≤ t) (ht : t ≤ pts.length) :
    (prodLinearFactors pts s t).natDegree ≤ t - s := by
  induction t with
  | zero => simp [show s = 0 from by omega]
  | succ k ih =>
    by_cases hsk : s = k + 1
    · subst hsk; simp
    · rw [prodLinearFactors_snoc pts s k (by omega) (by omega : k < pts.length)]
      calc (prodLinearFactors pts s k * (X - C _)).natDegree
          ≤ (prodLinearFactors pts s k).natDegree +
              (X - C ((pts.get ⟨k, by omega⟩).x.toGF216)).natDegree :=
            Polynomial.natDegree_mul_le
        _ ≤ (k - s) + 1 := by
            have h1 := ih (by omega) (by omega)
            have h2 : (X - C ((pts.get ⟨k, by omega⟩).x.toGF216) : GF216Poly).natDegree = 1 :=
              Polynomial.natDegree_X_sub_C _
            omega
        _ = k + 1 - s := by omega

/-- Coefficients of `prodLinearFactors` beyond degree `stop − start` are zero. -/
lemma prodLinearFactors_coeff_eq_zero_high
    (pts : List Pt) (start stop m : Nat) (hm : stop - start < m) :
    (prodLinearFactors pts start stop).coeff m = 0 := by
  suffices h : ∀ d start stop m, stop - start = d → d < m →
      (prodLinearFactors pts start stop).coeff m = 0 from
    h (stop - start) start stop m rfl hm
  intro d
  induction d with
  | zero =>
    intro start stop m hd hm'
    have : ¬(start < stop ∧ start < pts.length) := by omega
    rw [prodLinearFactors_base _ _ _ this, coeff_one]
    exact if_neg (by omega)
  | succ n ih =>
    intro start stop m hd hm'
    by_cases h : start < stop ∧ start < pts.length
    · rw [prodLinearFactors_step _ _ _ h.1 h.2]
      cases m with
      | zero => omega
      | succ m' =>
        rw [sub_mul, coeff_sub, coeff_X_mul, coeff_C_mul,
            ih (start + 1) stop (m' + 1) (by omega) (by omega),
            ih (start + 1) stop m' (by omega) (by omega)]
        ring
    · rw [prodLinearFactors_base _ _ _ h, coeff_one]
      exact if_neg (by omega)

/-! ## Lagrange interpolation definitions -/

/--
**Lagrange denominator product over a suffix of the point list.**

Given a distinguished x-coordinate `pi_x : GF16`, a list of points `pts`, and a starting index
`start`, compute the product
  `∏_{j = start}^{pts.length - 1}
      (if pi_x.value = pts[j].x.value then 1
       else pi_x.toGF216 - pts[j].x.toGF216)`
over the remaining points in the list.
-/
noncomputable def lagrangeDenomProd (pi_x : spqr.encoding.gf.GF16)
    (pts : List spqr.encoding.polynomial.Pt) (start : Nat) : GF216 :=
  if h : start < pts.length then
    if pi_x.value = (pts.get ⟨start, h⟩).x.value
    then lagrangeDenomProd pi_x pts (start + 1)
    else (pi_x.toGF216 - (pts.get ⟨start, h⟩).x.toGF216) *
         lagrangeDenomProd pi_x pts (start + 1)
  else 1
termination_by pts.length - start

/-- When `start ≥ pts.length`, the product is `1` (empty product). -/
@[simp]
lemma lagrangeDenomProd_ge (pi_x : spqr.encoding.gf.GF16)
    (pts : List spqr.encoding.polynomial.Pt) (start : Nat)
    (h : pts.length ≤ start) :
    lagrangeDenomProd pi_x pts start = 1 := by
  unfold lagrangeDenomProd
  simp [show ¬(start < pts.length) from by omega]

/-- One-step unfolding when the current point matches `pi_x`. -/
lemma lagrangeDenomProd_skip (pi_x : spqr.encoding.gf.GF16)
    (pts : List spqr.encoding.polynomial.Pt) (start : Nat)
    (h : start < pts.length)
    (heq : pi_x.value = (pts.get ⟨start, h⟩).x.value) :
    lagrangeDenomProd pi_x pts start =
      lagrangeDenomProd pi_x pts (start + 1) := by
  conv_lhs => unfold lagrangeDenomProd
  rw [dif_pos h, if_pos heq]

/-- One-step unfolding when the current point differs from `pi_x`. -/
lemma lagrangeDenomProd_accum (pi_x : spqr.encoding.gf.GF16)
    (pts : List spqr.encoding.polynomial.Pt) (start : Nat)
    (h : start < pts.length)
    (hne : pi_x.value ≠ (pts.get ⟨start, h⟩).x.value) :
    lagrangeDenomProd pi_x pts start =
      (pi_x.toGF216 - (pts.get ⟨start, h⟩).x.toGF216) *
        lagrangeDenomProd pi_x pts (start + 1) := by
  conv_lhs => unfold lagrangeDenomProd
  rw [dif_pos h, if_neg hne]

/--
**Lagrange scaling factor** in `GF216`.

Given a distinguished point `pi` and the full point list `pts`,
`lagrangeScaleGF216 pi pts = pi.y.toGF216 * (lagrangeDenomProd pi.x pts 0) ^ (2^16 − 2)`.

In a field of order `q`, `x^(q−2)` is the multiplicative inverse of `x` (for `x ≠ 0`) by Fermat's
little theorem, so this equals `pi.y / ∏_{j, pts[j].x ≠ pi.x} (pi.x − pts[j].x)`.
-/
noncomputable def lagrangeScaleGF216
    (pi : spqr.encoding.polynomial.Pt)
    (pts : List spqr.encoding.polynomial.Pt) : GF216 :=
  pi.y.toGF216 *
    (lagrangeDenomProd pi.x pts 0) ^ (2 ^ 16 - 2)

/--
**Lagrange basis polynomial**: the product `∏_{j ≠ i} (X − pts[j].x)`
of linear factors over all points except the `i`-th.
-/
noncomputable def lagrangeBasisPoly
    (pts : List spqr.encoding.polynomial.Pt) (i : Nat) :
    Polynomial GF216 :=
  if i < pts.length then
    prodLinearFactors pts 0 i *
      prodLinearFactors pts (i + 1) pts.length
  else 1

/-- Degree bound for `lagrangeBasisPoly`. -/
lemma natDegree_lagrangeBasisPoly_le
    (pts : List Pt) (i : Nat) (hi : i < pts.length) (hn : 0 < pts.length) :
    (lagrangeBasisPoly pts i).natDegree ≤ pts.length - 1 := by
  simp only [lagrangeBasisPoly, if_pos hi]
  calc (prodLinearFactors pts 0 i * prodLinearFactors pts (i + 1) pts.length).natDegree
      ≤ (prodLinearFactors pts 0 i).natDegree +
          (prodLinearFactors pts (i + 1) pts.length).natDegree :=
        Polynomial.natDegree_mul_le
    _ ≤ (i - 0) + (pts.length - (i + 1)) := by
        have h1 := natDegree_prodLinearFactors_le pts 0 i (by omega) (by omega)
        have h2 := natDegree_prodLinearFactors_le pts (i + 1) pts.length (by omega) (by omega)
        omega
    _ = pts.length - 1 := by omega

/--
**Sum of `lagrangeScale · lagrangeBasis` over a prefix `[0, n)` of the point list `pts`.**

This is the partial Lagrange interpolant.
-/
noncomputable def lagrangeInterpolantSum
    (pts : List spqr.encoding.polynomial.Pt) : Nat → Polynomial GF216
  | 0     => 0
  | n + 1 =>
      lagrangeInterpolantSum pts n +
        (if h : n < pts.length then
          C (lagrangeScaleGF216 (pts.get ⟨n, h⟩) pts) *
            lagrangeBasisPoly pts n
        else 0)

/-- `lagrangeInterpolantSum` equals a `Finset.sum`. -/
lemma lagrangeInterpolantSum_eq_finset_sum
    (pts : List Pt) (n : Nat) (hn : n ≤ pts.length) :
    lagrangeInterpolantSum pts n =
      Finset.sum (Finset.range n) (fun i =>
        if h : i < pts.length then
          C (lagrangeScaleGF216 (pts.get ⟨i, h⟩) pts) *
            lagrangeBasisPoly pts i
        else 0) := by
  induction n with
  | zero => simp [lagrangeInterpolantSum]
  | succ k ih =>
    rw [lagrangeInterpolantSum, ih (by omega), Finset.sum_range_succ]

/-- Coefficient of `lagrangeInterpolantSum` beyond degree is zero. -/
lemma lagrangeInterpolantSum_coeff_high
    (pts : List Pt) (n j : Nat) (hn : n ≤ pts.length)
    (hj : pts.length ≤ j) :
    (lagrangeInterpolantSum pts n).coeff j = 0 := by
  rw [lagrangeInterpolantSum_eq_finset_sum pts n hn]
  simp only [Polynomial.finset_sum_coeff]
  apply Finset.sum_eq_zero
  intro i hi
  rw [Finset.mem_range] at hi
  have hi' : i < pts.length := by omega
  rw [dif_pos hi']
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (by
    calc (C _ * lagrangeBasisPoly pts i).natDegree
        ≤ (lagrangeBasisPoly pts i).natDegree := Polynomial.natDegree_C_mul_le _ _
      _ ≤ pts.length - 1 := natDegree_lagrangeBasisPoly_le pts i hi' (by omega)
      _ < j := by omega)

/-! ## Horner scheme evaluation -/

/--
**Horner-scheme accumulator** for polynomial evaluation.

`hornerAccum g_x coeffs pos` computes the Horner evaluation of the polynomial with
coefficients `coeffs[pos], coeffs[pos+1], …` at the point `g_x.toGF216`.
-/
noncomputable def hornerAccum (g_x : spqr.encoding.gf.GF16)
    (coeffs : List spqr.encoding.gf.GF16) (pos : Nat) : GF216 :=
  if h : pos < coeffs.length then
    (coeffs.get ⟨pos, h⟩).toGF216 +
      g_x.toGF216 * hornerAccum g_x coeffs (pos + 1)
  else 0
termination_by coeffs.length - pos

@[simp]
lemma hornerAccum_ge (g_x : spqr.encoding.gf.GF16)
    (coeffs : List spqr.encoding.gf.GF16) (pos : Nat)
    (h : coeffs.length ≤ pos) :
    hornerAccum g_x coeffs pos = 0 := by
  unfold hornerAccum
  simp [show ¬(pos < coeffs.length) from by omega]

lemma hornerAccum_unfold (g_x : spqr.encoding.gf.GF16)
    (coeffs : List spqr.encoding.gf.GF16) (pos : Nat)
    (h : pos < coeffs.length) :
    hornerAccum g_x coeffs pos =
      (coeffs.get ⟨pos, h⟩).toGF216 +
        g_x.toGF216 * hornerAccum g_x coeffs (pos + 1) := by
  conv_lhs => unfold hornerAccum
  rw [dif_pos h]

/--
Shifting lemma: evaluating `hornerAccum` on `c :: cs` at position `pos + 1` is the same as
evaluating on `cs` at position `pos`.
-/
lemma hornerAccum_cons
    (g c : GF16)
    (cs : List GF16)
    (pos : Nat) :
    hornerAccum g (c :: cs) (pos + 1) =
      hornerAccum g cs pos := by
  by_cases hlt : pos < cs.length
  · rw [hornerAccum_unfold g (c :: cs) (pos + 1) (by simp; omega),
        hornerAccum_unfold g cs pos hlt]
    have hget : (c :: cs).get ⟨pos + 1, by simp; omega⟩ = cs.get ⟨pos, hlt⟩ := by
      simp [List.get_eq_getElem]
    rw [hget]; congr 1; congr 1
    exact hornerAccum_cons g c cs (pos + 1)
  · rw [hornerAccum_ge g (c :: cs) (pos + 1) (by simp; omega),
        hornerAccum_ge g cs pos (by omega)]
termination_by cs.length - pos
decreasing_by omega

/--
Horner cancellation: `hornerAccum g coeffs k + g.toGF216 * hornerAccum g coeffs (k + 1) =
coeffs[k].toGF216`.

In characteristic 2, the intermediate terms cancel out.
-/
lemma hornerAccum_cancel (g : spqr.encoding.gf.GF16)
    (coeffs : List spqr.encoding.gf.GF16) (k : Nat)
    (hk : k < coeffs.length) :
    hornerAccum g coeffs k +
      g.toGF216 * hornerAccum g coeffs (k + 1) =
      (coeffs.get ⟨k, hk⟩).toGF216 := by
  conv_lhs => rw [hornerAccum_unfold g coeffs k hk]
  set c := (coeffs.get ⟨k, hk⟩).toGF216
  set t := g.toGF216 * hornerAccum g coeffs (k + 1)
  rw [show (c + t) + t = c + (t + t) from by ring]
  rw [GF216.add_self_eq_zero t, add_zero]

/--
**`hornerAccum` at position 0 equals polynomial evaluation.**

This connects the Horner-scheme computation `hornerAccum g coeffs 0`
to the Mathlib `Polynomial.eval` of `listToGF216Poly coeffs`.
-/
lemma hornerAccum_zero_eq_eval
    (g : GF16) (coeffs : List GF16) :
    hornerAccum g coeffs 0 =
      (listToGF216Poly coeffs).eval (g.toGF216) := by
  induction coeffs with
  | nil =>
    rw [hornerAccum_ge g [] 0 (by simp)]
    simp
  | cons c cs ih =>
    rw [hornerAccum_unfold g (c :: cs) 0 (by simp)]
    simp only [List.get_eq_getElem, List.getElem_cons_zero]
    rw [hornerAccum_cons g c cs 0, ih, listToGF216Poly_cons]
    simp [eval_add, eval_mul, eval_C, eval_X]

/-! ## Expected trailing polynomial -/

/--
**Expected trailing sub-polynomial** after `k` iterations.

Defined by the recurrence:
  `S₀ = C(p_coeffs[offset]!.toGF216)`
  `S_{k+1} = C(p_coeffs[offset − (k + 1)]!.toGF216) +
             (X − C(pts[iter_start + k]!.x.toGF216)) · Sₖ`

This tracks the compound effect of `k` calls to `mult_xdiff_assign_trailing` on the trailing
sub-polynomial rooted at position `offset`.
-/
noncomputable def expectedTrailingPoly
    (p_coeffs : List GF16) (pts : List Pt)
    (offset iter_start : Nat) : Nat → GF216Poly
  | 0 => C (p_coeffs[offset]!.toGF216)
  | k + 1 =>
    C (p_coeffs[offset - (k + 1)]!.toGF216) +
    (X - C (pts[iter_start + k]!.x.toGF216)) *
      expectedTrailingPoly p_coeffs pts offset iter_start k

/-- Base case: the expected trailing polynomial after 0 iterations. -/
@[simp]
lemma expectedTrailingPoly_zero (p_coeffs : List GF16) (pts : List Pt)
    (offset iter_start : Nat) :
    expectedTrailingPoly p_coeffs pts offset iter_start 0 =
      C (p_coeffs[offset]!.toGF216) := rfl

/-- Step case: one-step unfolding of `expectedTrailingPoly`. -/
lemma expectedTrailingPoly_succ (p_coeffs : List GF16) (pts : List Pt)
    (offset iter_start k : Nat) :
    expectedTrailingPoly p_coeffs pts offset iter_start (k + 1) =
      C (p_coeffs[offset - (k + 1)]!.toGF216) +
      (X - C (pts[iter_start + k]!.x.toGF216)) *
        expectedTrailingPoly p_coeffs pts offset iter_start k := rfl

/-- Coefficients of `expectedTrailingPoly` beyond degree `k` are zero. -/
lemma expectedTrailingPoly_coeff_eq_zero
    (p_coeffs : List GF16) (pts : List Pt)
    (offset iter_start k n : Nat) (hn : k < n) :
    (expectedTrailingPoly p_coeffs pts offset iter_start k).coeff n = 0 := by
  induction k generalizing n with
  | zero =>
    simp only [expectedTrailingPoly_zero, coeff_C]
    exact if_neg (by omega)
  | succ k ih =>
    cases n with
    | zero => omega
    | succ n' =>
      rw [expectedTrailingPoly_succ]
      -- Coefficient n'+1 of C a + (X - C b) * P
      rw [sub_mul, coeff_add, coeff_sub, coeff_X_mul, coeff_C_mul]
      have h1 := ih n' (by omega)
      have h2 := ih (n' + 1) (by omega)
      have : (C (p_coeffs[offset - (k + 1)]!.toGF216) : GF216Poly).coeff (n' + 1) = 0 := by
        rw [coeff_C]; exact if_neg (by omega)
      rw [h1, h2, this]; ring

/--
**Bridge lemma**: When the initial polynomial has `p[offset] = ONE` and `p[j] = ZERO` for `j <
offset`, the expected trailing polynomial collapses to `prodLinearFactors`.
-/
lemma expectedTrailingPoly_eq_prodLinearFactors
    (p_coeffs : List GF16) (pts : List Pt) (offset : Nat)
    (h_leading : p_coeffs[offset]!.toGF216 = 1)
    (h_zeros : ∀ j, j < offset → p_coeffs[j]!.toGF216 = 0)
    (h_pts : offset ≤ pts.length) :
    ∀ k, k ≤ offset →
      expectedTrailingPoly p_coeffs pts offset 0 k =
        prodLinearFactors pts 0 k := by
  intro k hk
  induction k with
  | zero =>
    rw [expectedTrailingPoly_zero, prodLinearFactors_base pts 0 0 (by omega),
        h_leading, map_one]
  | succ n ih =>
    rw [expectedTrailingPoly_succ]
    have hn_le : n ≤ offset := by omega
    rw [ih hn_le]
    have h_zero : p_coeffs[offset - (n + 1)]!.toGF216 = 0 := by
      apply h_zeros; omega
    rw [h_zero, map_zero, zero_add]
    have h_n_lt : n < pts.length := by omega
    rw [prodLinearFactors_snoc pts 0 n (by omega) h_n_lt]
    conv_lhs =>
      rw [show pts[0 + n]!.x.toGF216 = (pts.get ⟨n, h_n_lt⟩).x.toGF216 from by
        congr 1; congr 1; rw [Nat.zero_add]; exact getElem!_pos pts n h_n_lt]
    ring

/-! ## Advanced polynomial identity helpers -/

/--
**The constant term of a polynomial satisfying a factored identity with an X factor is zero.**

From the polynomial identity
  `p · (X − C(a)) = X · C(s) · P`
the RHS has a factor of `X` and hence zero constant term.

• When `a ≠ 0`: since `GF216` is an integral domain, `p.coeff(0) = 0`.
• When `a = 0`: `(X − C(0)) = X`, and the root hypothesis `P.eval(a) = 0` gives `X ∣ P`,
  from which `p.coeff(0) = 0` follows.
-/
lemma coeff_zero_of_X_mul_identity
    (p : GF216Poly) (a s : GF216) (P : GF216Poly)
    (h_id : p * (X - C a) = X * C s * P)
    (h_root : P.eval a = 0) :
    p.coeff 0 = 0 := by
  by_cases ha : a = 0
  · subst ha
    simp only [map_zero, sub_zero] at h_id
    have h_X_dvd_P : (X : GF216Poly) ∣ P := by
      have h_div : (X - C (0 : GF216)) ∣ P := dvd_iff_isRoot.mpr h_root
      rwa [map_zero, sub_zero] at h_div
    obtain ⟨Q, hQ⟩ := h_X_dvd_P
    have hX_ne : (X : GF216Poly) ≠ 0 := X_ne_zero
    have hp_eq : p = C s * P := by
      have h1 : p * X = (C s * P) * X := by
        ring_nf; ring_nf at h_id; exact h_id
      exact mul_right_cancel₀ hX_ne h1
    rw [hp_eq, hQ]
    simp only [Polynomial.mul_coeff_zero, coeff_C_zero, coeff_X_zero,
               zero_mul, mul_zero]
  · have h0 := congr_arg (fun q => q.coeff 0) h_id
    simp only [Polynomial.mul_coeff_zero, coeff_sub, coeff_X_zero, coeff_C_zero,
               zero_sub, zero_mul] at h0
    rw [CharTwo.neg_eq] at h0
    exact (mul_eq_zero.mp h0).elim id (absurd · ha)

/-- Converting `List.map/sum` to `Finset.sum` indexed by `Fin`. -/
lemma list_map_sum_eq_finset_sum
    {α β : Type} [AddCommMonoid β]
    (l : List α) (f : α → β) :
    (l.map f).sum = Finset.sum Finset.univ (fun i : Fin l.length => f (l.get i)) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, List.get_eq_getElem]
    rw [ih, Fin.sum_univ_succ]
    simp [Fin.val_succ, List.get_eq_getElem]


instance : Inhabited spqr.encoding.polynomial.Pt :=
  ⟨{ x := default, y := default }⟩

instance : Inhabited spqr.encoding.polynomial.Poly :=
  ⟨{ coefficients := alloc.vec.Vec.new _ }⟩



end spqr.encoding.polynomial
