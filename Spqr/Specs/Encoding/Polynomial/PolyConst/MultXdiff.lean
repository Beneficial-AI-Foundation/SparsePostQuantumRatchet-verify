/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import Spqr.Specs.Encoding.Gf.GF16.ZERO
public import Spqr.Math.List
import Spqr.Math.Poly.Identities.MultXdiff
import Spqr.Specs.Encoding.Gf.GF16.ConstSub
import Spqr.Specs.Encoding.Gf.GF16.ConstMul
public import Spqr.Math.Poly.Basic.Defs
public import SrcTranslated.Funs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Tactic.ComputeDegree
import Spqr.Math.Gf16.Irreducible
import Spqr.Math.Poly.Basic.Zero
import Spqr.Math.Poly.LinearFactors.Degree
import Spqr.Specs.Encoding.Gf.Unaccelerated.Mul

/-! # Spec theorem for `PolyConst::mult_xdiff`: loop body 0

One step of the first loop in `mult_xdiff` (lines 430–440), which builds the `xp` (shifted)
and `dp` (scaled) arrays for computing `(x − difference) · self` in GF(2¹⁶)[X].

- **Done** (`i1 ≥ N`): returns `(xp, dp)` unchanged.
- **Continue** (`i1 < N`): sets `xp[i1+1] := a[i1]` (if `i1 < N−1`),
  `dp[i1] := a[i1] · difference`, and advances `i1`.

**Source**: spqr/src/encoding/polynomial.rs -/

@[expose] public section

open Aeneas Aeneas.Std Result spqr.encoding.polynomial spqr.encoding.gf Polynomial

namespace spqr.encoding.polynomial.PolyConst.mult_xdiff_loop0

/-- Reading back the slot just written by `Array.set`. -/
private lemma array_set_get_self {N : Usize} (arr : Array GF16 N) (k : Usize) (x : GF16)
    (h : k.val < (arr.set k x).length) : (arr.set k x).val.get ⟨k.val, h⟩ = x := by
  simp only [List.get_eq_getElem, Array.set_val_eq, List.getElem_set_self]

/-- `Array.set` leaves all other slots unchanged. -/
private lemma array_set_getElem?_ne {N : Usize} (arr : Array GF16 N) (k : Usize) (x : GF16)
    (j : Nat) (hj : j ≠ k.val) : (arr.set k x).val[j]? = arr.val[j]? := by
  rw [Array.set_val_eq, List.getElem?_set_ne (Ne.symm hj)]

/-- **Spec theorem for `encoding.polynomial.PolyConst.mult_xdiff_loop0.body`**:

Processes one index `i1` of the first loop, building `xp` and `dp`. Succeeds when `i.val < N.val`.

• **Done** (`i1 ≥ N`): `xp' = xp ∧ dp' = dp`.
• **Cont** (`i1 < N`): advances counter (`i2 = i1 + 1`), sets
  `dp1[i1].toGF216 = a[i1].toGF216 * difference.toGF216` (other `dp` positions unchanged),
  and if `i1 < i` sets `xp1[i1+1] = a[i1]` (other `xp` positions unchanged),
  otherwise `xp1 = xp`. -/
@[step]
theorem body_spec
    {N : Usize} (i i1 : Usize) (a xp dp : Array GF16 N) (difference : GF16)
    (h_i_lt_N : i < N) :
    body i a difference xp dp i1 ⦃ cf =>
      match cf with
      | ControlFlow.done (xp', dp') => xp' = xp ∧ dp' = dp ∧ ¬ (i1 < N)
      | ControlFlow.cont (xp1, dp1, i2) =>
          i1 < N ∧
          i2 = i1.val + 1 ∧
          (∀ (h_idx : i1 < dp1.length),
            (dp1.val.get ⟨i1.val, h_idx⟩).toGF216 = (a.val[i1.val]!).toGF216 * difference.toGF216) ∧
          (∀ (j : Nat), j ≠ i1 → dp1.val[j]? = dp.val[j]?) ∧
          (i1 < i → (∀ (h_idx : i1 + 1 < xp1.length),
            xp1.val.get ⟨i1 + 1, h_idx⟩ = a.val[i1.val]!) ∧
            ∀ (j : Nat), j ≠ i1 + 1 → xp1.val[j]? = xp.val[j]?) ∧
          (¬ i1 < i → xp1 = xp) ⦄ := by
  unfold body
  by_cases h_lt : i1.val < N.val
  · rw [if_pos (show i1 < N from h_lt)]
    have h_alen : a.val.length = N.val := a.property
    by_cases h_lt_i : i1.val < i.val
    · rw [if_pos (show i1 < i from h_lt_i)]
      step as ⟨g, h_g⟩
      step as ⟨i2, h_i2⟩
      step as ⟨xp1, h_xp1⟩
      step as ⟨g', h_g'⟩
      step as ⟨g1, h_g1⟩
      step as ⟨a1, h_a1⟩
      step as ⟨i3, h_i3⟩
      have h_ag : a.val[i1.val]! = g' := by rw [h_g', getElem!_pos a.val _ (by omega)]
      subst h_xp1 h_a1
      refine ⟨h_lt, h_i3, fun h_idx => ?_, fun j hj => array_set_getElem?_ne _ _ _ j hj,
        fun _ => ⟨fun h_idx => ?_, fun j hj => ?_⟩, fun h => absurd h_lt_i h⟩
      · rw [array_set_get_self, h_g1, h_ag]
      · simp only [← h_i2]
        rw [array_set_get_self, h_g, getElem!_pos a.val _ (by omega)]
      · exact array_set_getElem?_ne _ _ _ j (by omega)
    · rw [if_neg (show ¬i1 < i from h_lt_i)]
      simp only [bind_ok]
      step as ⟨g', h_g'⟩
      step as ⟨g1, h_g1⟩
      step as ⟨a1, h_a1⟩
      step as ⟨i3, h_i3⟩
      have h_ag : a.val[i1.val]! = g' := by rw [h_g', getElem!_pos a.val _ (by omega)]
      subst h_a1
      refine ⟨h_lt, h_i3, fun h_idx => ?_, fun j hj => array_set_getElem?_ne _ _ _ j hj,
        fun h => absurd h h_lt_i, fun _ => trivial⟩
      rw [array_set_get_self, h_g1, h_ag]
  · rw [if_neg (show ¬i1 < N from h_lt)]
    exact (WP.spec_ok _).mpr ⟨rfl, rfl, h_lt⟩

/-! # Spec theorem for `PolyConst::mult_xdiff`: loop 0

Full first loop wrapper around `body_spec`, iterating `i1 = 0, …, N−1` to build `xp` and `dp`.

**Postcondition**:
- `dp[j].toGF216 = a[j].toGF216 * difference.toGF216` for all `j < N`.
- `xp[j+1] = a[j]` for `j < N−1`; position 0 and out-of-range positions unchanged.

**Source**: spqr/src/encoding/polynomial.rs -/
@[step]
theorem loop_spec
    {N : Usize} (i i1 : Usize) (a xp dp : Array GF16 N) (difference : GF16)
    (h_i_lt_N : i < N)
    (h_i1_le_N : i1 ≤ N)
    (h_dp_inv : ∀ (j : Nat), j < i1 →
        ∀ (hj : j < dp.length),
          (dp.val.get ⟨j, hj⟩).toGF216 =
            (a.val[j]!).toGF216 * difference.toGF216)
    (h_xp_inv : ∀ (j : Nat), j < i1 → j < i →
        ∀ (h_idx : j + 1 < xp.length),
          xp.val.get ⟨j + 1, h_idx⟩ = a.val[j]!) :
    mult_xdiff_loop0 i a difference xp dp i1 ⦃ result =>
      let (xpR, dpR) := result
      (∀ (j : Nat), j < N →
          ∀ (hj : j < dpR.length),
            (dpR.val.get ⟨j, hj⟩).toGF216 = (a.val[j]!).toGF216 * difference.toGF216) ∧
      (∀ (j : Nat), j < i →
          ∀ (h_idx : j + 1 < xpR.length), xpR.val.get ⟨j + 1, h_idx⟩ = a.val[j]!) ∧
      (∀ (j : Nat), ¬(0 < j ∧ j ≤ i) → xpR.val[j]? = xp.val[j]?) ⦄ := by
  unfold mult_xdiff_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : (Array GF16 N) × (Array GF16 N) × Usize) => N - p.2.2)
    (inv := fun (p : (Array GF16 N) × (Array GF16 N) × Usize) =>
        p.2.2 ≤ N ∧
        (∀ (j : Nat), j < p.2.2 →
          ∀ (hj : j < p.2.1.length),
            (p.2.1.val.get ⟨j, hj⟩).toGF216 = (a.val[j]!).toGF216 * difference.toGF216) ∧
        (∀ (j : Nat), p.2.2 ≤ j → p.2.1.val[j]? = dp.val[j]?) ∧
        (∀ (j : Nat), j < p.2.2 → j < i →
          ∀ (h_idx : j + 1 < p.1.length),
            p.1.val.get ⟨j + 1, h_idx⟩ = a.val[j]!) ∧
        (∀ (j : Nat), ¬(0 < j ∧ j ≤ p.2.2 ∧ j ≤ i) →
          p.1.val[j]? = xp.val[j]?))
  · rintro ⟨xp', dp', i1'⟩ hinv
    dsimp only at hinv
    obtain ⟨h_i1_le, h_dp_proc, h_dp_rest, h_xp_shift, h_xp_rest⟩ := hinv
    have h_i1_le' : i1'.val ≤ N.val := h_i1_le
    have h_iN : i.val < N.val := h_i_lt_N
    have h_xlen : xp'.val.length = N.val := xp'.property
    have h_dlen : dp'.val.length = N.val := dp'.property
    apply WP.spec_mono (body_spec i i1' a xp' dp' difference h_i_lt_N)
    rintro (⟨xp1, dp1, i2⟩ | ⟨xp_r, dp_r⟩) h_cf
    · obtain ⟨hlt, hi2, hdp, hdprest, hxpif, hxpelse⟩ := h_cf
      have hlt' : i1'.val < N.val := hlt
      have h_xlen1 : xp1.val.length = N.val := xp1.property
      have h_dlen1 : dp1.val.length = N.val := dp1.property
      dsimp only
      refine ⟨⟨show i2.val ≤ N.val by omega, fun j hj hj_len => ?_, fun j hj => ?_,
        fun j hj hji h_idx => ?_, fun j hj => ?_⟩, show N.val - i2.val < N.val - i1'.val by omega⟩
      · rcases Nat.lt_or_ge j i1'.val with h | h
        · rw [list_get_of_getElem?_eq (hdprest j (by omega)) hj_len (by omega)]
          exact h_dp_proc j h _
        · obtain rfl : j = i1'.val := by omega
          exact hdp hj_len
      · rw [hdprest j (by omega)]
        exact h_dp_rest j (by omega)
      · by_cases hii : i1'.val < i.val
        · rcases Nat.lt_or_ge j i1'.val with h | h
          · rw [list_get_of_getElem?_eq ((hxpif hii).2 (j + 1) (by omega)) h_idx (by omega)]
            exact h_xp_shift j h hji _
          · obtain rfl : j = i1'.val := by omega
            exact (hxpif hii).1 h_idx
        · obtain rfl := hxpelse hii
          exact h_xp_shift j (by omega) hji h_idx
      · by_cases hii : i1'.val < i.val
        · rw [(hxpif hii).2 j (by omega)]
          exact h_xp_rest j (by omega)
        · obtain rfl := hxpelse hii
          exact h_xp_rest j (by omega)
    · obtain ⟨rfl, rfl, hnlt⟩ := h_cf
      have h_eq : i1'.val = N.val := by have : ¬i1'.val < N.val := hnlt; omega
      exact ⟨fun j hj hjl => h_dp_proc j (by omega) hjl,
        fun j hj h_idx => h_xp_shift j (by omega) hj h_idx,
        fun j hj => h_xp_rest j (by omega)⟩
  · exact ⟨h_i1_le_N, h_dp_inv, fun j _ => rfl, h_xp_inv, fun j _ => rfl⟩

end spqr.encoding.polynomial.PolyConst.mult_xdiff_loop0

/-! # Spec theorem for `PolyConst::mult_xdiff`: loop body 1

One step of the second loop (lines 446–451), computing `xp[i] := xp[i] − dp[i]` in GF(2¹⁶).

- **Done** (`i ≥ N`): returns `xp` unchanged.
- **Continue** (`i < N`): sets `xp[i] := xp[i] − dp[i]` and advances `i`.

**Source**: spqr/src/encoding/polynomial.rs -/

namespace spqr.encoding.polynomial.PolyConst.mult_xdiff_loop1

/-- **Spec theorem for `encoding.polynomial.PolyConst.mult_xdiff_loop1.body`**:

Processes one index `i` of the second loop, computing `xp[i] := xp[i] − dp[i]`.

• **Done** (`i ≥ N`): `xp' = xp`.
• **Cont** (`i < N`): advances counter (`i1 = i + 1`), sets
  `xp'[i].toGF216 = xp[i].toGF216 - dp[i].toGF216` (other positions unchanged). -/
@[step]
theorem body_spec
    {N : Usize} (dp xp : Array GF16 N) (i : Usize) :
    body dp xp i ⦃ cf =>
      match cf with
      | ControlFlow.done xp' =>
          xp' = xp ∧ ¬ (i < N)
      | ControlFlow.cont (xp', i1) =>
          i < N ∧
          i1 = i.val + 1 ∧
          (∀ (h_idx : i < xp'.length),
            (xp'.val.get ⟨i.val, h_idx⟩).toGF216 =
              (xp.val[i.val]!).toGF216 - (dp.val[i.val]!).toGF216) ∧
          (∀ (j : Nat), j ≠ i → xp'.val[j]? = xp.val[j]?) ⦄ := by
  unfold body
  by_cases h_lt : i.val < N.val
  · rw [if_pos (show i < N from h_lt)]
    have h_xlen : xp.val.length = N.val := xp.property
    have h_dlen : dp.val.length = N.val := dp.property
    step as ⟨g, h_g⟩
    step as ⟨g1, h_g1⟩
    step as ⟨g2, h_g2⟩
    step as ⟨a, h_a⟩
    step as ⟨i1, h_i1⟩
    subst h_a
    refine ⟨h_lt, h_i1, fun h_idx => ?_,
      fun j hj => mult_xdiff_loop0.array_set_getElem?_ne _ _ _ j hj⟩
    rw [mult_xdiff_loop0.array_set_get_self, h_g2, h_g, h_g1, getElem!_pos xp.val _ (by omega),
      getElem!_pos dp.val _ (by omega)]
  · rw [if_neg (show ¬i < N from h_lt)]
    exact (WP.spec_ok _).mpr ⟨rfl, h_lt⟩

/-! # Spec theorem for `PolyConst::mult_xdiff`: loop 1

Full second loop wrapper around `body_spec`, iterating `i = 0, …, N−1` to compute
element-wise `xp[i] := xp[i] − dp[i]` in GF(2¹⁶).

**Postcondition**:
- `xpR[j].toGF216 = xp[j].toGF216 − dp[j].toGF216` for `i ≤ j < N`.
- `xpR[j]? = xp[j]?` for `j < i`.

**Source**: spqr/src/encoding/polynomial.rs -/
@[step]
theorem loop_spec
    {N : Usize} (xp dp : Array GF16 N) (i : Usize)
    (h_i_le_N : i ≤ N) :
    mult_xdiff_loop1 xp dp i ⦃ xpR =>
      (∀ (j : Nat), i ≤ j ∧  j < N →
          ∀ (hj : j < xpR.val.length),
            (xpR.val.get ⟨j, hj⟩).toGF216 = (xp.val[j]!).toGF216 - (dp.val[j]!).toGF216) ∧
      (∀ (j : Nat), j < i → xpR[j]? = xp.val[j]?) ⦄ := by
  unfold mult_xdiff_loop1
  apply loop.spec_decr_nat
    (measure := fun (p : (Array GF16 N) × Usize) => N - p.2)
    (inv := fun (p : (Array GF16 N) × Usize) =>
        i ≤ p.2 ∧
        p.2 ≤ N ∧
        (∀ (j : Nat), i ≤ j → j < p.2 →
          ∀ (hj : j < p.1.length),
            (p.1.val.get ⟨j, hj⟩).toGF216 = (xp.val[j]!).toGF216 - (dp.val[j]!).toGF216) ∧
        (∀ (j : Nat), ¬(i ≤ j ∧ j < p.2) → p.1.val[j]? = xp.val[j]?))
  · rintro ⟨xp', i'⟩ hinv
    dsimp only at hinv
    obtain ⟨h_i_le_i', h_i'_le_N, h_xp_proc, h_xp_rest⟩ := hinv
    have h_i_le_i'' : i.val ≤ i'.val := h_i_le_i'
    have h_i'_le_N' : i'.val ≤ N.val := h_i'_le_N
    have h_xlen : xp'.val.length = N.val := xp'.property
    have h_xlen0 : xp.val.length = N.val := xp.property
    apply WP.spec_mono (body_spec dp xp' i')
    rintro (⟨xp1, i1⟩ | xp_r) h_cf
    · obtain ⟨hlt, hi1, hupd, hrest⟩ := h_cf
      have hlt' : i'.val < N.val := hlt
      have h_xlen1 : xp1.val.length = N.val := xp1.property
      dsimp only
      refine ⟨⟨show i.val ≤ i1.val by omega, show i1.val ≤ N.val by omega,
        fun j hj1 hj2 hj => ?_, fun j hj => ?_⟩, show N.val - i1.val < N.val - i'.val by omega⟩
      · rcases Nat.lt_or_ge j i'.val with h | h
        · rw [list_get_of_getElem?_eq (hrest j (by omega)) hj (by omega)]
          exact h_xp_proc j hj1 h _
        · obtain rfl : j = i'.val := by omega
          rw [hupd hj]
          have h_eq := h_xp_rest i'.val (by omega)
          rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at h_eq
          rw [getElem!_pos xp'.val _ (by omega), getElem!_pos xp.val _ (by omega),
            Option.some.inj h_eq]
      · rw [hrest j (by omega)]
        exact h_xp_rest j (by omega)
    · obtain ⟨rfl, hnlt⟩ := h_cf
      have h_eq : i'.val = N.val := by have : ¬i'.val < N.val := hnlt; omega
      exact ⟨fun j hj hjl => h_xp_proc j hj.1 (by omega) hjl,
        fun j hj => h_xp_rest j (by omega)⟩
  · exact ⟨le_refl _, h_i_le_N, fun j hj1 hj2 => absurd hj2 (by dsimp only; omega),
      fun j _ => rfl⟩

end spqr.encoding.polynomial.PolyConst.mult_xdiff_loop1

/-! # Spec theorem for
`spqr::encoding::polynomial::{spqr::encoding::polynomial::PolyConst<N>}::mult_xdiff`

Computes `(x − diff) · self` in GF(2¹⁶)[X] by composing loop 0 (build `xp`, `dp`)
and loop 1 (element-wise `xp − dp`). Requires the polynomial degree to be strictly less
than `N − 1` (equivalently, `degree + 1 < N`), so that multiplying by a linear factor
keeps the result within the `N`-coefficient representation.

The postcondition is the polynomial identity:
  `listToGF216Poly result.coefficients.val =
     (X − C (diff.toGF216)) * listToGF216Poly self.coefficients.val`

**Source**: spqr/src/encoding/polynomial.rs -/

namespace spqr.encoding.polynomial.PolyConst

/-- **Spec theorem for `encoding.polynomial.PolyConst.mult_xdiff`**:

Succeeds when `0 < N` and the polynomial degree of `self` satisfies `self.degree + 1 < N`
(i.e., the polynomial fits in `N − 1` coefficients, leaving room for the degree-raising
multiplication by `(X − diff)`).

• **Postcondition**:
  `listToGF216Poly result.coefficients =
     (X − C (diff.toGF216)) * listToGF216Poly self.coefficients` -/
@[step]
theorem mult_xdiff_spec
    {N : Usize} (self : PolyConst N) (diff : GF16)
    (h_N_pos : 0 < N.val)
    (h_deg : self.degree + 1 < N) :
    mult_xdiff self diff ⦃ (result : PolyConst N) =>
      listToGF216Poly result.coefficients =
        (X - C (diff.toGF216)) * listToGF216Poly self.coefficients ⦄ := by
  have h_leading_zero  := getElem!_value_val_eq_zero_of_natDegree_lt self.coefficients.val N
    h_N_pos h_deg
  unfold mult_xdiff
  step as ⟨i, h_i, _⟩
  step as ⟨g, h_g⟩
  have h_clen : self.coefficients.val.length = N.val := self.coefficients.property
  have h_g0 : g.value.val = 0 := by
    rw [h_g, ← getElem!_pos self.coefficients.val i.val (by omega), h_i]
    exact h_leading_zero
  have h_assert : ¬(g.value != 0#u16) = true := by
    simp only [bne_iff_ne, ne_eq, not_not]
    exact UScalar.eq_of_val_eq h_g0
  step
  have h_iN : i < N := by change i.val < N.val; omega
  step with mult_xdiff_loop0.loop_spec i 0#usize self.coefficients _ _ diff h_iN
    (by change 0 ≤ N.val; omega) (fun j hj => absurd hj (Nat.not_lt_zero _))
    (fun j hj => absurd hj (Nat.not_lt_zero _)) as ⟨xp1, dp1, h_loop0⟩
  obtain ⟨h_dp, h_xp_shift, h_xp_unch⟩ := h_loop0
  step with mult_xdiff_loop1.loop_spec xp1 dp1 0#usize (by change 0 ≤ N.val; omega) as
    ⟨xp2, h_sub, _⟩
  refine mult_xdiff_result_eq self.coefficients diff i xp1 dp1 xp2 h_N_pos h_i h_deg
    (fun j hj hjl => ?_) (fun j hj h_idx => ?_) h_xp_unch (fun j hj => h_sub j hj.1 hj.2)
  · rw [Array.getElem!_Nat_eq, getElem!_pos dp1.val j hjl, Array.getElem!_Nat_eq]
    exact h_dp j hj hjl
  · rw [Array.getElem!_Nat_eq, getElem!_pos xp1.val _ h_idx]
    exact h_xp_shift j hj h_idx

end spqr.encoding.polynomial.PolyConst
