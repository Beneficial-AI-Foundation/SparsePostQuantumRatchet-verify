/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module
public import Spqr.Crypto.Fips203.NTT.MultiplyNTTs
/-!
# FIPS 203 NTT Specification via the CRT Decomposition

NIST FIPS 203 (ML-KEM, August 2024), § 4.3, describes the NTT domain of a
polynomial `f ∈ R_q = ℤ_q[X]/(X²⁵⁶ + 1)` as its image under the Chinese
Remainder Theorem isomorphism

  `R_q ≅ ∏ᵢ₌₀¹²⁷ ℤ_q[X] / (X² − γᵢ)`,   `γᵢ = ζ^{2·BitRev₇(i)+1}`.

This file constructs that decomposition *algebraically* (no butterflies):

1. **`gammaPoly i`** — the quadratic `X² − γᵢ` and its quotient ring
   **`QuadRq i`**.
2. **`crtHom i`** — the ring homomorphism `R_q →+* QuadRq i`, well defined
   because `γᵢ¹²⁸ = −1` makes the root of `X² − γᵢ` a root of `X²⁵⁶ + 1`.
3. **`quadCoeff0` / `quadCoeff1`** — the two coordinates of an element of
   `QuadRq i` in the basis `{1, X}`, with the multiplication law matching
   `BaseCaseMultiply` (Algorithm 10).
4. **`nttSpec`** — the specification NTT: coefficient pair `(2i, 2i+1)` of
   `nttSpec f` is the image of `f` under `crtHom i`.
5. **`nttSpec_toCoeffs_mul`** — the multiplicative homomorphism
   `nttSpec(f·g) = MultiplyNTTs(nttSpec f, nttSpec g)`, proved from the ring
   homomorphism property of `crtHom` alone.
6. **`toCoeffs_ofCoeffs` / `ofCoeffs_toCoeffs`** — the coefficient round trip
   on `R_q`.

The remaining connection to the imperative Algorithm 7 — `ntt = nttSpec` —
is the butterfly-correctness obligation isolated in `RoundTrip.lean`.

**Source**: NIST FIPS 203, § 4.3 (Algorithms 7, 9, 10)
-/

@[expose] public section

open Polynomial

noncomputable section

namespace Fips203

/-! ## Coefficient round trip on `R_q` -/

/-- The `IsAdjoinRootMonic` structure underlying `Rq.toCoeffs`. -/
private def HRq : IsAdjoinRootMonic Rq cycloPoly :=
  AdjoinRoot.isAdjoinRootMonic cycloPoly cycloPoly_monic

private lemma HRq_map (p : Polynomial Zq) :
    HRq.map p = AdjoinRoot.mk cycloPoly p := rfl

private lemma HRq_coeff_lt (x : Rq) (j : ℕ) (hj : j < cycloPoly.natDegree) :
    HRq.coeff x j = (HRq.modByMonicHom x).coeff j := by
  rw [HRq.coeff_apply_lt x j hj, HRq.basis_repr]

/-- The canonical degree-`< 256` representative has degree below `cycloPoly`. -/
private lemma ofCoeffs_degree_lt (f : Fin n → Zq) :
    (∑ i : Fin n, C (f i) * X ^ (i : ℕ)).degree < cycloPoly.degree := by
  have hdeg : cycloPoly.degree = (n : ℕ) := by
    rw [degree_eq_natDegree cycloPoly_ne_zero, cycloPoly_natDegree]
  rw [hdeg]
  refine lt_of_le_of_lt (degree_sum_le _ _) ?_
  rw [Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe (n : ℕ))]
  intro i _
  refine lt_of_le_of_lt (degree_C_mul_X_pow_le _ _) ?_
  exact_mod_cast i.isLt

/-- **Round trip 1**: `toCoeffs (ofCoeffs f) = f`. -/
theorem toCoeffs_ofCoeffs (f : Fin n → Zq) :
    Rq.toCoeffs (Rq.ofCoeffs f) = f := by
  funext j
  change HRq.coeff (AdjoinRoot.mk cycloPoly (∑ i : Fin n, C (f i) * X ^ (i : ℕ))) (j : ℕ) = f j
  rw [← HRq_map, HRq_coeff_lt _ _ (by rw [cycloPoly_natDegree]; exact j.isLt),
    HRq.modByMonicHom_map,
    (modByMonic_eq_self_iff cycloPoly_monic).mpr (ofCoeffs_degree_lt f),
    finsetSum_coeff]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    rw [coeff_C_mul, coeff_X_pow, if_neg (by simpa [Fin.ext_iff, eq_comm] using hij), mul_zero]
  · simp

/-- **Round trip 2**: `ofCoeffs (toCoeffs r) = r`. -/
theorem ofCoeffs_toCoeffs (r : Rq) : Rq.ofCoeffs (Rq.toCoeffs r) = r := by
  apply HRq.ext_elem
  intro j hj
  rw [cycloPoly_natDegree] at hj
  exact congrFun (toCoeffs_ofCoeffs (Rq.toCoeffs r)) ⟨j, hj⟩

/-! ## The quadratic quotient rings `ℤ_q[X]/(X² − γᵢ)` -/

/-- The quadratic modulus `X² − γᵢ` of the `i`-th CRT component. -/
def gammaPoly (i : Fin 128) : Polynomial Zq := X ^ 2 - C (gammaForPair i)

/-- `gammaPoly` is monic. -/
theorem gammaPoly_monic (i : Fin 128) : (gammaPoly i).Monic :=
  monic_X_pow_sub_C _ (by norm_num)

/-- `gammaPoly` has degree 2. -/
theorem gammaPoly_natDegree (i : Fin 128) : (gammaPoly i).natDegree = 2 :=
  natDegree_X_pow_sub_C

/-- The `i`-th CRT component ring `ℤ_q[X]/(X² − γᵢ)`. -/
abbrev QuadRq (i : Fin 128) : Type := AdjoinRoot (gammaPoly i)

/-- The `IsAdjoinRootMonic` structure on the `i`-th CRT component. -/
def HQuad (i : Fin 128) : IsAdjoinRootMonic (QuadRq i) (gammaPoly i) :=
  AdjoinRoot.isAdjoinRootMonic _ (gammaPoly_monic i)

/-- In `QuadRq i`, the root squares to `γᵢ`. -/
theorem quadRoot_sq (i : Fin 128) :
    (AdjoinRoot.root (gammaPoly i)) ^ 2 =
      AdjoinRoot.of (gammaPoly i) (gammaForPair i) := by
  have h : AdjoinRoot.mk (gammaPoly i) (X ^ 2 - C (gammaForPair i)) = 0 :=
    AdjoinRoot.mk_self
  rw [map_sub, map_pow, AdjoinRoot.mk_X, sub_eq_zero] at h
  rw [h]; rfl

/-- `γᵢ¹²⁸ = −1`: the root of `X² − γᵢ` is a primitive 512th root of unity,
hence a root of `X²⁵⁶ + 1`. -/
theorem gammaForPair_pow_128 (i : Fin 128) : gammaForPair i ^ 128 = -1 := by
  unfold gammaForPair
  rw [← pow_mul,
    show (2 * (bitRev7Table i).val + 1) * 128 = 256 * (bitRev7Table i).val + 128 by ring,
    pow_add, pow_mul, ζ_pow_256, one_pow, one_mul, ζ_pow_128]

/-- The quadratic root is a root of `X²⁵⁶ + 1`: its 256th power is `−1`. -/
theorem quadRoot_pow_256 (i : Fin 128) :
    (AdjoinRoot.root (gammaPoly i)) ^ 256 = -1 := by
  rw [show (256 : ℕ) = 2 * 128 by norm_num, pow_mul, quadRoot_sq, ← map_pow,
    gammaForPair_pow_128, map_neg, map_one]

set_option maxRecDepth 1000000 in
/-- `cycloPoly` vanishes at the quadratic root. -/
theorem cycloPoly_eval₂_quadRoot (i : Fin 128) :
    eval₂ (AdjoinRoot.of (gammaPoly i)) (AdjoinRoot.root (gammaPoly i))
      cycloPoly = 0 := by
  have h256 := quadRoot_pow_256 i
  have hc : cycloPoly = X ^ n + 1 := rfl
  rw [hc, eval₂_add, eval₂_X_pow, eval₂_one,
    show (n : ℕ) = 256 from rfl, h256, neg_add_cancel]

/-- **The `i`-th CRT projection** `R_q →+* ℤ_q[X]/(X² − γᵢ)`, sending the
class of `X` in `R_q` to the class of `X` in the quadratic quotient.  Well
defined because `X²⁵⁶ + 1` vanishes at the quadratic root (as `γᵢ¹²⁸ = −1`). -/
def crtHom (i : Fin 128) : Rq →+* QuadRq i :=
  AdjoinRoot.lift (AdjoinRoot.of (gammaPoly i)) (AdjoinRoot.root (gammaPoly i))
    (cycloPoly_eval₂_quadRoot i)

/-! ## Coordinates in `QuadRq i` and `BaseCaseMultiply` -/

/-- Constant coefficient of an element of `QuadRq i` in the basis `{1, X}`. -/
def quadCoeff0 (i : Fin 128) (x : QuadRq i) : Zq := (HQuad i).coeff x 0

/-- Linear coefficient of an element of `QuadRq i` in the basis `{1, X}`. -/
def quadCoeff1 (i : Fin 128) (x : QuadRq i) : Zq := (HQuad i).coeff x 1

private lemma HQuad_root (i : Fin 128) :
    (HQuad i).root = AdjoinRoot.root (gammaPoly i) := rfl

private lemma of_eq_smul_one (i : Fin 128) (a : Zq) :
    AdjoinRoot.of (gammaPoly i) a = a • (1 : QuadRq i) := by
  rw [← AdjoinRoot.algebraMap_eq, Algebra.algebraMap_eq_smul_one]

private lemma of_mul_root_eq_smul (i : Fin 128) (b : Zq) :
    AdjoinRoot.of (gammaPoly i) b * AdjoinRoot.root (gammaPoly i) =
      b • AdjoinRoot.root (gammaPoly i) := by
  rw [← AdjoinRoot.algebraMap_eq, ← Algebra.smul_def]

/-- `quadCoeff0` reads off the constant coordinate of `a + b·X`. -/
theorem quadCoeff0_repr (i : Fin 128) (a b : Zq) :
    quadCoeff0 i
      (AdjoinRoot.of (gammaPoly i) a +
        AdjoinRoot.of (gammaPoly i) b * AdjoinRoot.root (gammaPoly i)) = a := by
  unfold quadCoeff0
  rw [of_eq_smul_one, of_mul_root_eq_smul, map_add, map_smul, map_smul,
    show (1 : QuadRq i) = (HQuad i).root ^ 0 by rw [pow_zero],
    show AdjoinRoot.root (gammaPoly i) = (HQuad i).root ^ 1 by rw [pow_one, HQuad_root],
    (HQuad i).coeff_root_pow (by rw [gammaPoly_natDegree]; omega),
    (HQuad i).coeff_root_pow (by rw [gammaPoly_natDegree]; omega)]
  simp

/-- `quadCoeff1` reads off the linear coordinate of `a + b·X`. -/
theorem quadCoeff1_repr (i : Fin 128) (a b : Zq) :
    quadCoeff1 i
      (AdjoinRoot.of (gammaPoly i) a +
        AdjoinRoot.of (gammaPoly i) b * AdjoinRoot.root (gammaPoly i)) = b := by
  unfold quadCoeff1
  rw [of_eq_smul_one, of_mul_root_eq_smul, map_add, map_smul, map_smul,
    show (1 : QuadRq i) = (HQuad i).root ^ 0 by rw [pow_zero],
    show AdjoinRoot.root (gammaPoly i) = (HQuad i).root ^ 1 by rw [pow_one, HQuad_root],
    (HQuad i).coeff_root_pow (by rw [gammaPoly_natDegree]; omega),
    (HQuad i).coeff_root_pow (by rw [gammaPoly_natDegree]; omega)]
  simp

/-- Every element of `QuadRq i` is `c₀ + c₁·X` for its two coordinates. -/
theorem quad_repr (i : Fin 128) (x : QuadRq i) :
    x = AdjoinRoot.of (gammaPoly i) (quadCoeff0 i x) +
      AdjoinRoot.of (gammaPoly i) (quadCoeff1 i x) * AdjoinRoot.root (gammaPoly i) := by
  apply (HQuad i).ext_elem
  intro j hj
  rw [gammaPoly_natDegree] at hj
  interval_cases j
  · exact (quadCoeff0_repr i _ _).symm
  · exact (quadCoeff1_repr i _ _).symm

/-- Expansion of a product in `QuadRq i` in the basis `{1, X}` — this is
exactly the `BaseCaseMultiply` formula (FIPS 203, Algorithm 10). -/
theorem quad_mul_expand (i : Fin 128) (a₀ a₁ b₀ b₁ : Zq) :
    (AdjoinRoot.of (gammaPoly i) a₀ +
        AdjoinRoot.of (gammaPoly i) a₁ * AdjoinRoot.root (gammaPoly i)) *
      (AdjoinRoot.of (gammaPoly i) b₀ +
        AdjoinRoot.of (gammaPoly i) b₁ * AdjoinRoot.root (gammaPoly i)) =
    AdjoinRoot.of (gammaPoly i) (a₀ * b₀ + a₁ * b₁ * gammaForPair i) +
      AdjoinRoot.of (gammaPoly i) (a₀ * b₁ + a₁ * b₀) *
        AdjoinRoot.root (gammaPoly i) := by
  have hsq := quadRoot_sq i
  simp only [map_add, map_mul]
  rw [← hsq]
  ring

/-- Constant coordinate of a product: the first `BaseCaseMultiply` output. -/
theorem quadCoeff0_mul (i : Fin 128) (x y : QuadRq i) :
    quadCoeff0 i (x * y) =
      quadCoeff0 i x * quadCoeff0 i y +
        quadCoeff1 i x * quadCoeff1 i y * gammaForPair i := by
  conv_lhs => rw [quad_repr i x, quad_repr i y, quad_mul_expand, quadCoeff0_repr]

/-- Linear coordinate of a product: the second `BaseCaseMultiply` output. -/
theorem quadCoeff1_mul (i : Fin 128) (x y : QuadRq i) :
    quadCoeff1 i (x * y) =
      quadCoeff0 i x * quadCoeff1 i y + quadCoeff1 i x * quadCoeff0 i y := by
  conv_lhs => rw [quad_repr i x, quad_repr i y, quad_mul_expand, quadCoeff1_repr]

/-! ## The specification NTT -/

/-- **Specification NTT**: coefficient `2i` (resp. `2i+1`) of `nttSpec f` is
the constant (resp. linear) coordinate of the image of `f` in the `i`-th CRT
component `ℤ_q[X]/(X² − γᵢ)`.  This is the mathematical content of the NTT
domain in FIPS 203 § 4.3; Algorithm 7 (`ntt`) is an efficient butterfly
implementation of this map. -/
def nttSpec (f : Fin n → Zq) : Fin n → Zq := fun idx =>
  have hlt : idx.val < 256 := idx.isLt
  if idx.val % 2 = 0 then
    quadCoeff0 ⟨idx.val / 2, by omega⟩
      (crtHom ⟨idx.val / 2, by omega⟩ (Rq.ofCoeffs f))
  else
    quadCoeff1 ⟨idx.val / 2, by omega⟩
      (crtHom ⟨idx.val / 2, by omega⟩ (Rq.ofCoeffs f))

/-- `nttSpec` at an even index reads `quadCoeff0` of the CRT image. -/
theorem nttSpec_even (f : Fin n → Zq) (i : Fin 128)
    (h : 2 * i.val < 256 := by have := i.isLt; omega) :
    nttSpec f ⟨2 * i.val, h⟩ = quadCoeff0 i (crtHom i (Rq.ofCoeffs f)) := by
  have hfin : (⟨2 * i.val / 2, by omega⟩ : Fin 128) = i :=
    Fin.ext (show 2 * i.val / 2 = i.val by omega)
  simp only [nttSpec, Nat.mul_mod_right, reduceIte]
  rw [hfin]

/-- `nttSpec` at an odd index reads `quadCoeff1` of the CRT image. -/
theorem nttSpec_odd (f : Fin n → Zq) (i : Fin 128)
    (h : 2 * i.val + 1 < 256 := by have := i.isLt; omega) :
    nttSpec f ⟨2 * i.val + 1, h⟩ = quadCoeff1 i (crtHom i (Rq.ofCoeffs f)) := by
  have hmod : (2 * i.val + 1) % 2 = 1 := by omega
  have hfin : (⟨(2 * i.val + 1) / 2, by omega⟩ : Fin 128) = i :=
    Fin.ext (show (2 * i.val + 1) / 2 = i.val by omega)
  simp only [nttSpec, hmod]
  rw [if_neg (by omega : ¬(1 = 0)), hfin]

/-! ## The multiplicative homomorphism for `nttSpec` -/

/-- **CRT multiplicativity of the specification NTT**:
`nttSpec(toCoeffs(r·s)) = MultiplyNTTs(nttSpec(toCoeffs r), nttSpec(toCoeffs s))`.
This is a pure consequence of `crtHom` being a ring homomorphism together
with the `BaseCaseMultiply` expansion of products in `ℤ_q[X]/(X² − γᵢ)`. -/
theorem nttSpec_toCoeffs_mul (r s : Rq) :
    nttSpec (Rq.toCoeffs (r * s)) =
      multiplyNTTs (nttSpec (Rq.toCoeffs r)) (nttSpec (Rq.toCoeffs s)) := by
  funext idx
  have hn : n = 256 := rfl
  have hlt : idx.val < 256 := hn ▸ idx.isLt
  have h2 : idx.val / 2 < 128 := by omega
  have hdiv : 2 * (idx.val / 2) ≤ idx.val := Nat.mul_div_le idx.val 2
  set i : Fin 128 := ⟨idx.val / 2, h2⟩ with hi
  have hrs : crtHom i (Rq.ofCoeffs (Rq.toCoeffs (r * s))) =
      crtHom i (Rq.ofCoeffs (Rq.toCoeffs r)) *
        crtHom i (Rq.ofCoeffs (Rq.toCoeffs s)) := by
    rw [ofCoeffs_toCoeffs, ofCoeffs_toCoeffs, ofCoeffs_toCoeffs, map_mul]
  have hibound : i.val < 128 := i.isLt
  by_cases hpar : idx.val % 2 = 0
  · have hidx : idx = ⟨2 * i.val, by omega⟩ :=
      Fin.ext (by simp only [hi, Fin.val_mk]; omega)
    rw [hidx, multiplyNTTs_even _ _ i]
    simp only [baseCaseMultiply]
    rw [nttSpec_even _ i, nttSpec_even _ i, nttSpec_odd _ i, nttSpec_odd _ i,
      nttSpec_even _ i, hrs, quadCoeff0_mul]
  · have hidx : idx = ⟨2 * i.val + 1, by omega⟩ :=
      Fin.ext (by simp only [hi, Fin.val_mk]; omega)
    rw [hidx, multiplyNTTs_odd _ _ i]
    simp only [baseCaseMultiply]
    rw [nttSpec_even _ i, nttSpec_even _ i, nttSpec_odd _ i, nttSpec_odd _ i,
      nttSpec_odd _ i, hrs, quadCoeff1_mul]

end Fips203
