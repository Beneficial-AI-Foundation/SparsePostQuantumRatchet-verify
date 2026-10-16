/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module
public import Spqr.Crypto.Fips203.NTT.MultiplyNTTs
public import Spqr.Crypto.Fips203.NTT.InvNTT
public import Spqr.Crypto.Fips203.NTT.Spec
public import Spqr.Crypto.Fips203.NTT.KernelCheck
/-!
# FIPS 203 NTT Round-Trip and Multiplicative Homomorphism

NIST FIPS 203 (ML-KEM, August 2024), § 4.3, specifies the forward NTT (Algorithm 7)
and inverse NTT (Algorithm 8) as mutually inverse maps on `ℤ_q^{256}`.  Together with
`MultiplyNTTs` (Algorithm 9), they satisfy two fundamental identities:

1. **Round-trip**: `NTT⁻¹ ∘ NTT = id` and `NTT ∘ NTT⁻¹ = id`.
2. **Multiplicative homomorphism**: For polynomials `f, g ∈ R_q`,
   `NTT(f · g) = MultiplyNTTs(NTT(f), NTT(g))`.

Both identities are proved **without axioms or `sorry`**.  They are reduced to
the 256 standard basis vectors `δⱼ` by linearity of the transforms, and the
basis cases are settled by *verified computation*: packed-natural clones of the
Algorithm 7/8 butterfly loops (`Packed.lean`) are evaluated by the Lean kernel
(`Kernel*.lean`, `InvKernel*.lean`, glued in `KernelCheck.lean`) and the results
are transported back to `ntt`/`invNtt` through the simulation relation `simR`
proved in this file.  The multiplicative homomorphism then encapsulates the CRT
isomorphism `R_q ≅ ∏ᵢ ℤ_q[X]/(X² − γᵢ)` of `Spec.lean`.

**Source**: NIST FIPS 203, § 4.3 (Algorithms 7–10)
-/

@[expose] public section

noncomputable section

namespace Fips203

/-! ## Standard basis vectors -/

/-- The `j`-th standard basis vector `δⱼ` of `ℤ_q^{256}`. -/
def delta (j : Fin n) : Fin n → Zq := fun i => if i = j then 1 else 0

/-- Every coefficient vector is the linear combination `∑ⱼ f(j) · δⱼ`. -/
lemma eq_sum_delta (f : Fin n → Zq) :
    f = fun i => ∑ j : Fin n, f j * delta j i := by
  funext i
  simp [delta]

/-! ## Finite-sum linearity of the transforms -/

/-- `ntt` commutes with finite sums (from `ntt_zero` and `ntt_add`). -/
lemma ntt_sum (s : Finset (Fin n)) (g : Fin n → Fin n → Zq) :
    ntt (fun i => ∑ j ∈ s, g j i) = fun i => ∑ j ∈ s, ntt (g j) i := by
  induction s using Finset.induction_on with
  | empty => simpa using ntt_zero
  | insert a s ha ih =>
    have h1 : (fun i => ∑ j ∈ insert a s, g j i)
        = fun i => g a i + ∑ j ∈ s, g j i := by
      funext i; rw [Finset.sum_insert ha]
    rw [h1, ntt_add, ih]
    funext i
    simp [Finset.sum_insert ha]

/-- `invNtt` commutes with finite sums (from `invNtt_zero` and `invNtt_add`). -/
lemma invNtt_sum (s : Finset (Fin n)) (g : Fin n → Fin n → Zq) :
    invNtt (fun i => ∑ j ∈ s, g j i) = fun i => ∑ j ∈ s, invNtt (g j) i := by
  induction s using Finset.induction_on with
  | empty => simpa using invNtt_zero
  | insert a s ha ih =>
    have h1 : (fun i => ∑ j ∈ insert a s, g j i)
        = fun i => g a i + ∑ j ∈ s, g j i := by
      funext i; rw [Finset.sum_insert ha]
    rw [h1, invNtt_add, ih]
    funext i
    simp [Finset.sum_insert ha]

/-! ## Multiplicative homomorphism -/

/-- Polynomial multiplication in `R_q` at the coefficient-vector level. -/
def polyMulCoeffs (f g : Fin n → Zq) : Fin n → Zq :=
  Rq.toCoeffs (Rq.ofCoeffs f * Rq.ofCoeffs g)

/-! ### Linearity of `Rq.ofCoeffs` and `Rq.toCoeffs` -/

/-- `Rq.ofCoeffs` of the zero vector is `0`. -/
lemma ofCoeffs_zero : Rq.ofCoeffs (fun _ => (0 : Zq)) = 0 := by
  simp [Rq.ofCoeffs]

/-- `Rq.ofCoeffs` is additive. -/
lemma ofCoeffs_add (f g : Fin n → Zq) :
    Rq.ofCoeffs (fun i => f i + g i) = Rq.ofCoeffs f + Rq.ofCoeffs g := by
  unfold Rq.ofCoeffs
  rw [← map_add, ← Finset.sum_add_distrib]
  exact congrArg (AdjoinRoot.mk cycloPoly)
    (Finset.sum_congr rfl fun i _ => by rw [map_add]; ring)

/-- `Rq.ofCoeffs` turns coefficientwise scaling into multiplication by the
constant polynomial `C c`. -/
lemma ofCoeffs_smul (c : Zq) (f : Fin n → Zq) :
    Rq.ofCoeffs (fun i => c * f i)
      = AdjoinRoot.mk cycloPoly (Polynomial.C c) * Rq.ofCoeffs f := by
  unfold Rq.ofCoeffs
  rw [← map_mul, Finset.mul_sum]
  exact congrArg (AdjoinRoot.mk cycloPoly)
    (Finset.sum_congr rfl fun i _ => by rw [map_mul]; ring)

/-- `Rq.toCoeffs 0 = 0`. -/
lemma toCoeffs_zero : Rq.toCoeffs 0 = fun _ => (0 : Zq) := by
  funext i
  simp [Rq.toCoeffs]

/-- `Rq.toCoeffs` is additive. -/
lemma toCoeffs_add (r s : Rq) :
    Rq.toCoeffs (r + s) = fun i => Rq.toCoeffs r i + Rq.toCoeffs s i := by
  funext i
  simp [Rq.toCoeffs, map_add]

/-- `Rq.toCoeffs` commutes with scaling by a constant polynomial. -/
lemma toCoeffs_smul (c : Zq) (r : Rq) :
    Rq.toCoeffs (AdjoinRoot.mk cycloPoly (Polynomial.C c) * r)
      = fun i => c * Rq.toCoeffs r i := by
  funext i
  have h : AdjoinRoot.mk cycloPoly (Polynomial.C c) * r = c • r := by
    rw [Algebra.smul_def, AdjoinRoot.algebraMap_eq]; rfl
  rw [h]
  simp [Rq.toCoeffs, map_smul]

/-! ### Bilinearity of `polyMulCoeffs` -/

/-- Commutativity of `polyMulCoeffs`. -/
lemma polyMulCoeffs_comm (f g : Fin n → Zq) :
    polyMulCoeffs f g = polyMulCoeffs g f := by
  unfold polyMulCoeffs; rw [mul_comm]

/-- Left annihilation for `polyMulCoeffs`. -/
lemma polyMulCoeffs_zero_left (g : Fin n → Zq) :
    polyMulCoeffs (fun _ => 0) g = fun _ => 0 := by
  unfold polyMulCoeffs
  rw [ofCoeffs_zero, zero_mul, toCoeffs_zero]

/-- Right annihilation for `polyMulCoeffs`. -/
lemma polyMulCoeffs_zero_right (f : Fin n → Zq) :
    polyMulCoeffs f (fun _ => 0) = fun _ => 0 := by
  rw [polyMulCoeffs_comm]; exact polyMulCoeffs_zero_left f

/-- Left additivity of `polyMulCoeffs`. -/
lemma polyMulCoeffs_add_left (f f' g : Fin n → Zq) :
    polyMulCoeffs (fun i => f i + f' i) g =
      fun i => polyMulCoeffs f g i + polyMulCoeffs f' g i := by
  unfold polyMulCoeffs
  rw [ofCoeffs_add, add_mul, toCoeffs_add]

/-- Right additivity of `polyMulCoeffs`. -/
lemma polyMulCoeffs_add_right (f g g' : Fin n → Zq) :
    polyMulCoeffs f (fun i => g i + g' i) =
      fun i => polyMulCoeffs f g i + polyMulCoeffs f g' i := by
  rw [polyMulCoeffs_comm, polyMulCoeffs_add_left,
    polyMulCoeffs_comm g f, polyMulCoeffs_comm g' f]

/-- Left scaling of `polyMulCoeffs`. -/
lemma polyMulCoeffs_smul_left (c : Zq) (f g : Fin n → Zq) :
    polyMulCoeffs (fun i => c * f i) g = fun i => c * polyMulCoeffs f g i := by
  unfold polyMulCoeffs
  rw [ofCoeffs_smul, mul_assoc, toCoeffs_smul]

/-- Right scaling of `polyMulCoeffs`. -/
lemma polyMulCoeffs_smul_right (c : Zq) (f g : Fin n → Zq) :
    polyMulCoeffs f (fun i => c * g i) = fun i => c * polyMulCoeffs f g i := by
  rw [polyMulCoeffs_comm, polyMulCoeffs_smul_left, polyMulCoeffs_comm g f]

/-- `polyMulCoeffs` commutes with finite sums in the left argument. -/
lemma polyMulCoeffs_sum_left (s : Finset (Fin n)) (F : Fin n → Fin n → Zq)
    (g : Fin n → Zq) :
    polyMulCoeffs (fun i => ∑ j ∈ s, F j i) g =
      fun i => ∑ j ∈ s, polyMulCoeffs (F j) g i := by
  induction s using Finset.induction_on with
  | empty => simpa using polyMulCoeffs_zero_left g
  | insert a s ha ih =>
    have h1 : (fun i => ∑ j ∈ insert a s, F j i)
        = fun i => F a i + ∑ j ∈ s, F j i := by
      funext i; rw [Finset.sum_insert ha]
    rw [h1, polyMulCoeffs_add_left, ih]
    funext i
    simp [Finset.sum_insert ha]

/-- `polyMulCoeffs` commutes with finite sums in the right argument. -/
lemma polyMulCoeffs_sum_right (s : Finset (Fin n)) (f : Fin n → Zq)
    (G : Fin n → Fin n → Zq) :
    polyMulCoeffs f (fun i => ∑ k ∈ s, G k i) =
      fun i => ∑ k ∈ s, polyMulCoeffs f (G k) i := by
  rw [polyMulCoeffs_comm, polyMulCoeffs_sum_left]
  funext i
  exact Finset.sum_congr rfl fun k _ => congrFun (polyMulCoeffs_comm (G k) f) i

/-! ### Finite-sum linearity of `multiplyNTTs` -/

/-- `multiplyNTTs` commutes with finite sums in the left argument. -/
lemma multiplyNTTs_sum_left (s : Finset (Fin n)) (F : Fin n → Fin n → Zq)
    (gh : Fin n → Zq) :
    multiplyNTTs (fun i => ∑ j ∈ s, F j i) gh =
      fun i => ∑ j ∈ s, multiplyNTTs (F j) gh i := by
  induction s using Finset.induction_on with
  | empty => simpa using multiplyNTTs_zero_left gh
  | insert a s ha ih =>
    have h1 : (fun i => ∑ j ∈ insert a s, F j i)
        = fun i => F a i + ∑ j ∈ s, F j i := by
      funext i; rw [Finset.sum_insert ha]
    rw [h1, multiplyNTTs_add_left, ih]
    funext i
    simp [Finset.sum_insert ha]

/-- `multiplyNTTs` commutes with finite sums in the right argument. -/
lemma multiplyNTTs_sum_right (s : Finset (Fin n)) (fh : Fin n → Zq)
    (G : Fin n → Fin n → Zq) :
    multiplyNTTs fh (fun i => ∑ k ∈ s, G k i) =
      fun i => ∑ k ∈ s, multiplyNTTs fh (G k) i := by
  induction s using Finset.induction_on with
  | empty => simpa using multiplyNTTs_zero_right fh
  | insert a s ha ih =>
    have h1 : (fun i => ∑ k ∈ insert a s, G k i)
        = fun i => G a i + ∑ k ∈ s, G k i := by
      funext i; rw [Finset.sum_insert ha]
    rw [h1, multiplyNTTs_add_right, ih]
    funext i
    simp [Finset.sum_insert ha]

/-! ### Linearity of `nttSpec` -/

/-- `crtHom` sends the constant `c` of `R_q` to the constant `c` of the
quadratic quotient. -/
lemma crtHom_of (i : Fin 128) (c : Zq) :
    crtHom i (AdjoinRoot.of cycloPoly c) = AdjoinRoot.of (gammaPoly i) c := by
  unfold crtHom
  exact AdjoinRoot.lift_of _

/-- `crtHom` is `ℤ_q`-linear (it is a ring homomorphism commuting with the
structure maps). -/
lemma crtHom_smul (i : Fin 128) (c : Zq) (r : Rq) :
    crtHom i (c • r) = c • crtHom i r := by
  rw [Algebra.smul_def, AdjoinRoot.algebraMap_eq, map_mul, crtHom_of,
    ← AdjoinRoot.algebraMap_eq, ← Algebra.smul_def]

/-- `quadCoeff0` is additive. -/
lemma quadCoeff0_add (i : Fin 128) (x y : QuadRq i) :
    quadCoeff0 i (x + y) = quadCoeff0 i x + quadCoeff0 i y := by
  simp [quadCoeff0, map_add]

/-- `quadCoeff1` is additive. -/
lemma quadCoeff1_add (i : Fin 128) (x y : QuadRq i) :
    quadCoeff1 i (x + y) = quadCoeff1 i x + quadCoeff1 i y := by
  simp [quadCoeff1, map_add]

/-- `quadCoeff0` commutes with scaling. -/
lemma quadCoeff0_smul (i : Fin 128) (c : Zq) (x : QuadRq i) :
    quadCoeff0 i (c • x) = c * quadCoeff0 i x := by
  simp [quadCoeff0, map_smul]

/-- `quadCoeff1` commutes with scaling. -/
lemma quadCoeff1_smul (i : Fin 128) (c : Zq) (x : QuadRq i) :
    quadCoeff1 i (c • x) = c * quadCoeff1 i x := by
  simp [quadCoeff1, map_smul]

/-- `nttSpec` is additive. -/
lemma nttSpec_add (f g : Fin n → Zq) :
    nttSpec (fun i => f i + g i) = fun i => nttSpec f i + nttSpec g i := by
  funext idx
  simp only [nttSpec, ofCoeffs_add, map_add]
  split
  · exact quadCoeff0_add _ _ _
  · exact quadCoeff1_add _ _ _

/-- `nttSpec` of the zero vector is zero. -/
lemma nttSpec_zero : nttSpec (fun _ => (0 : Zq)) = fun _ => (0 : Zq) := by
  funext idx
  simp only [nttSpec, ofCoeffs_zero, map_zero]
  split
  · simp [quadCoeff0]
  · simp [quadCoeff1]

/-- `nttSpec` commutes with scaling. -/
lemma nttSpec_smul (c : Zq) (f : Fin n → Zq) :
    nttSpec (fun i => c * f i) = fun i => c * nttSpec f i := by
  have hof : Rq.ofCoeffs (fun i => c * f i) = c • Rq.ofCoeffs f := by
    rw [ofCoeffs_smul, Algebra.smul_def, AdjoinRoot.algebraMap_eq]
    rfl
  funext idx
  simp only [nttSpec, hof, crtHom_smul]
  split
  · exact quadCoeff0_smul _ _ _
  · exact quadCoeff1_smul _ _ _

/-- `nttSpec` commutes with finite sums. -/
lemma nttSpec_sum (s : Finset (Fin n)) (g : Fin n → Fin n → Zq) :
    nttSpec (fun i => ∑ j ∈ s, g j i) = fun i => ∑ j ∈ s, nttSpec (g j) i := by
  induction s using Finset.induction_on with
  | empty => simpa using nttSpec_zero
  | insert a s ha ih =>
    have h1 : (fun i => ∑ j ∈ insert a s, g j i)
        = fun i => g a i + ∑ j ∈ s, g j i := by
      funext i; rw [Finset.sum_insert ha]
    rw [h1, nttSpec_add, ih]
    funext i
    simp [Finset.sum_insert ha]

/-! ### Closed form of `nttSpec` on basis vectors -/

set_option maxRecDepth 4000 in
/-- `Rq.ofCoeffs δⱼ` is the monomial `Xʲ`. -/
lemma ofCoeffs_delta (j : Fin n) :
    Rq.ofCoeffs (delta j) = AdjoinRoot.mk cycloPoly (Polynomial.X ^ (j : ℕ)) := by
  unfold Rq.ofCoeffs delta
  congr 1
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [hij]
  · simp

/-- `crtHom` sends the class of `Xᵉ` to the `e`-th power of the quadratic root. -/
lemma crtHom_mk_X_pow (i : Fin 128) (e : ℕ) :
    crtHom i (AdjoinRoot.mk cycloPoly (Polynomial.X ^ e)) =
      AdjoinRoot.root (gammaPoly i) ^ e := by
  rw [map_pow, AdjoinRoot.mk_X, map_pow]
  unfold crtHom
  rw [AdjoinRoot.lift_root]

/-- Powers of the quadratic root reduce via `root² = γᵢ`. -/
lemma quadRoot_pow (i : Fin 128) (e : ℕ) :
    AdjoinRoot.root (gammaPoly i) ^ e =
      AdjoinRoot.of (gammaPoly i) (gammaForPair i ^ (e / 2)) *
        AdjoinRoot.root (gammaPoly i) ^ (e % 2) := by
  conv_lhs => rw [show e = 2 * (e / 2) + e % 2 by omega]
  rw [pow_add, pow_mul, quadRoot_sq, ← map_pow]

/-- **Closed form of `nttSpec` on basis vectors**: at index `idx`, the value is
`γ_{idx/2}^{j/2}` when `idx` and `j` have the same parity and `0` otherwise. -/
lemma nttSpec_delta (j idx : Fin n) :
    nttSpec (delta j) idx =
      if idx.val % 2 = j.val % 2 then
        gammaForPair ⟨idx.val / 2, by have h : idx.val < 256 := idx.isLt; omega⟩ ^ (j.val / 2)
      else 0 := by
  have hlt : idx.val < 256 := idx.isLt
  set i : Fin 128 := ⟨idx.val / 2, by omega⟩ with hi
  have himg : crtHom i (Rq.ofCoeffs (delta j)) =
      AdjoinRoot.of (gammaPoly i) (gammaForPair i ^ (j.val / 2)) *
        AdjoinRoot.root (gammaPoly i) ^ (j.val % 2) := by
    rw [ofCoeffs_delta, crtHom_mk_X_pow, quadRoot_pow]
  have h0 : AdjoinRoot.of (gammaPoly i) (0 : Zq) = 0 := map_zero _
  by_cases hj : j.val % 2 = 0
  · -- `j` even: the image is `γ^{j/2} + 0·X`.
    have himg' : crtHom i (Rq.ofCoeffs (delta j)) =
        AdjoinRoot.of (gammaPoly i) (gammaForPair i ^ (j.val / 2)) +
          AdjoinRoot.of (gammaPoly i) (0 : Zq) * AdjoinRoot.root (gammaPoly i) := by
      rw [himg, hj, pow_zero, mul_one, h0, zero_mul, add_zero]
    by_cases hidx : idx.val % 2 = 0
    · rw [if_pos (by omega)]
      simp only [nttSpec, hidx, reduceIte]
      rw [← hi, himg', quadCoeff0_repr]
    · rw [if_neg (by omega)]
      simp only [nttSpec]
      rw [if_neg hidx, ← hi, himg', quadCoeff1_repr]
  · -- `j` odd: the image is `0 + γ^{j/2}·X`.
    have himg' : crtHom i (Rq.ofCoeffs (delta j)) =
        AdjoinRoot.of (gammaPoly i) (0 : Zq) +
          AdjoinRoot.of (gammaPoly i) (gammaForPair i ^ (j.val / 2)) *
            AdjoinRoot.root (gammaPoly i) := by
      rw [himg, show j.val % 2 = 1 by omega, pow_one, h0, zero_add]
    by_cases hidx : idx.val % 2 = 0
    · rw [if_neg (by omega)]
      simp only [nttSpec, hidx, reduceIte]
      rw [← hi, himg', quadCoeff0_repr]
    · rw [if_pos (by omega)]
      simp only [nttSpec]
      rw [if_neg hidx, ← hi, himg', quadCoeff1_repr]

/-! ### Simulation relation between packed naturals and coefficient vectors -/

/-- `l` simulates `f` when each base-4096 digit of `l` is a canonical
(`< 3329`) representative of the corresponding coefficient of `f`. -/
def simR (l : ℕ) (f : Fin n → Zq) : Prop :=
  ∀ i : Fin n, getP l i.val < 3329 ∧ ((getP l i.val : ℕ) : Zq) = f i

lemma cast_3329_eq_zero : ((3329 : ℕ) : Zq) = 0 := by
  exact_mod_cast ZMod.natCast_self q

lemma cast_mod_3329 (x : ℕ) : ((x % 3329 : ℕ) : Zq) = (x : Zq) := by
  exact_mod_cast ZMod.natCast_mod x q

/-- Single butterfly simulation. -/
lemma simR_bfP {l : ℕ} {f : Fin n → Zq} (hs : simR l f)
    (z : ℕ) {start len : ℕ} (hlen : 0 < len)
    (h1 : start < n) (h2 : start + len < n) :
    simR (bfP z l start len)
      (nttButterfly f (z : Zq) ⟨start, h1⟩ ⟨start + len, h2⟩) := by
  intro i
  obtain ⟨hbj, hcj⟩ := hs ⟨start, h1⟩
  obtain ⟨hbl, hcl⟩ := hs ⟨start + len, h2⟩
  set a := getP l start with ha
  set b := getP l (start + len) with hb
  set t := z * b % 3329 with htdef
  have ht : t < 3329 := Nat.mod_lt _ (by norm_num)
  have hv1 : (a + t) % 3329 < 3329 := Nat.mod_lt _ (by norm_num)
  have hv2 : (a + 3329 - t) % 3329 < 3329 := Nat.mod_lt _ (by norm_num)
  have hne : start ≠ start + len := by omega
  have hcast1 : (((a + t) % 3329 : ℕ) : Zq)
      = f ⟨start, h1⟩ + (z : Zq) * f ⟨start + len, h2⟩ := by
    rw [cast_mod_3329]
    push_cast
    rw [hcj, htdef, cast_mod_3329]
    push_cast
    rw [hcl]
  have hcast2 : (((a + 3329 - t) % 3329 : ℕ) : Zq) =
      f ⟨start, h1⟩ - (z : Zq) * f ⟨start + len, h2⟩ := by
    rw [cast_mod_3329, Nat.cast_sub (by omega), Nat.cast_add,
      cast_3329_eq_zero, add_zero, hcj, htdef, cast_mod_3329]
    push_cast
    rw [hcl]
  simp only [bfP, nttButterfly]
  by_cases hij : i.val = start
  · have hieq : i = ⟨start, h1⟩ := Fin.ext hij
    rw [hij, getP_setP_self _ _ _ (by omega), hieq, Function.update_self]
    exact ⟨hv1, hcast1⟩
  · have hine : i ≠ (⟨start, h1⟩ : Fin n) := fun hc => hij (by rw [hc])
    rw [getP_setP_ne _ _ _ _ (by omega) hij, Function.update_of_ne hine]
    by_cases hil : i.val = start + len
    · have hieq : i = ⟨start + len, h2⟩ := Fin.ext hil
      rw [hil, getP_setP_self _ _ _ (by omega), hieq, Function.update_self]
      exact ⟨hv2, hcast2⟩
    · have hine' : i ≠ (⟨start + len, h2⟩ : Fin n) := fun hc => hil (by rw [hc])
      rw [getP_setP_ne _ _ _ _ (by omega) hil, Function.update_of_ne hine']
      exact hs i

/-- Inner-loop simulation. -/
lemma simR_innerP (z : ℕ) :
    ∀ (count l : ℕ) (f : Fin n → Zq) (start len : ℕ) (_hlen : 0 < len)
      (h1 : ∀ r, r < count → start + r < n)
      (h2 : ∀ r, r < count → start + r + len < n),
      simR l f →
      simR (innerP z l start len count)
        (nttInnerLoop f (z : Zq) start len count h1 h2)
  | 0, _, _, _, _, _, _, _, hs => hs
  | c + 1, l, f, start, len, hlen, h1, h2, hs => by
    simp only [innerP, nttInnerLoop]
    exact simR_innerP z c _ _ (start + 1) len hlen _ _
      (simR_bfP hs z hlen (h1 0 (by omega))
        (by have := h2 0 (by omega); omega))

/-- Zeta-index bookkeeping of the packed middle loop. -/
lemma middleP_snd : ∀ (nb l len startOff k : ℕ),
    (middleP l len startOff k nb).2 = k + nb
  | 0, _, _, _, _ => rfl
  | nb + 1, l, len, startOff, k => by
    simp only [middleP]
    rw [middleP_snd nb]
    omega

/-- The packed twiddle factor is the imperative `zetaTable` entry. -/
lemma cast_zeta (k : ℕ) (hk : k < 128) :
    ((17 ^ brN k % 3329 : ℕ) : Zq) = zetaTable ⟨k, hk⟩ := by
  rw [cast_mod_3329]
  push_cast
  rw [zetaTable, ← brN_eq_bitRev7 ⟨k, hk⟩]
  rfl

/-- Middle-loop simulation. -/
lemma simR_middleP :
    ∀ (nb l : ℕ) (f : Fin n → Zq) (len startOff k : ℕ)
      (h_pos : 0 < len)
      (h_fit : ∀ b, b < nb → startOff + b * (2 * len) + 2 * len ≤ n)
      (h_k : ∀ b, b < nb → k + b < 128),
      simR l f →
      simR (middleP l len startOff k nb).1
        (nttMiddleLoop f len startOff k nb h_pos h_fit h_k).1
  | 0, _, _, _, _, _, _, _, _, hs => hs
  | nb + 1, l, f, len, startOff, k, h_pos, h_fit, h_k, hs => by
    simp only [middleP, nttMiddleLoop]
    have hk0 : k < 128 := by have := h_k 0 (by omega); omega
    have hz : zetaTable ⟨k, by omega⟩ = ((17 ^ brN k % 3329 : ℕ) : Zq) :=
      (cast_zeta k hk0).symm
    rw [hz]
    exact simR_middleP nb _ _ len (startOff + 2 * len) (k + 1) h_pos _ _
      (simR_innerP _ len _ _ startOff len h_pos _ _ hs)

/-- Outer-loop simulation. -/
lemma simR_outerP :
    ∀ (layers : List ℕ) (l : ℕ) (f : Fin n → Zq) (k : ℕ)
      (h_layers : ∀ x ∈ layers, 0 < x ∧ 2 * x ∣ n)
      (h_k : k + (layers.map (fun x => n / (2 * x))).sum ≤ 128),
      simR l f →
      simR (outerP l k layers).1
        (nttOuterLoop f k layers h_layers h_k).1
  | [], _, _, _, _, _, hs => hs
  | len :: rest, l, f, k, h_layers, h_k, hs => by
    simp only [outerP, nttOuterLoop]
    simp only [nttMiddleLoop_snd, middleP_snd]
    exact simR_outerP rest _ _ _ _ _
      (simR_middleP _ _ _ _ _ _ _ _ _ hs)

/-! ### Endpoint simulations -/

/-- The packed basis vector simulates `delta j`. -/
lemma simR_deltaP (j : Fin n) : simR (deltaP j.val) (delta j) := by
  intro i
  unfold deltaP delta getP
  rcases lt_trichotomy i.val j.val with h | h | h
  · rw [if_neg (Fin.val_ne_iff.mp (by omega))]
    have hdvd : (4096 : ℕ) ^ j.val / 4096 ^ i.val = 4096 ^ (j.val - i.val) :=
      Nat.pow_div (by omega) (by norm_num)
    rw [hdvd]
    have h1 : j.val - i.val = (j.val - i.val - 1) + 1 := by omega
    rw [h1, pow_succ, Nat.mul_mod_left]
    exact ⟨by norm_num, by simp⟩
  · have hij : i = j := Fin.ext h
    have hdiv : (4096 : ℕ) ^ j.val / 4096 ^ i.val = 1 := by
      rw [h, Nat.div_self (Nat.pow_pos (show 0 < 4096 by norm_num))]
    rw [if_pos hij, hdiv]
    exact ⟨by norm_num, by norm_num⟩
  · rw [if_neg (Fin.val_ne_iff.mp (by omega))]
    have hlt : (4096 : ℕ) ^ j.val < 4096 ^ i.val :=
      Nat.pow_lt_pow_right (by norm_num) h
    rw [Nat.div_eq_of_lt hlt]
    exact ⟨by norm_num, by simp⟩

/-- The packed formula simulates the closed form of `nttSpec (delta j)`. -/
lemma simR_formulaP (j : Fin n) : simR (formulaP j.val) (nttSpec (delta j)) := by
  intro i
  have hcell : ∀ idx, formulaCell j.val idx < 3329 := by
    intro idx
    unfold formulaCell
    split
    · exact Nat.mod_lt _ (by norm_num)
    · norm_num
  have hget : getP (formulaP j.val) i.val = formulaCell j.val i.val := by
    unfold formulaP
    rw [getP_packList _ ?_ _ (by simp), getD_map_range _ _ _ (by simp)]
    intro x hx
    obtain ⟨idx, _, rfl⟩ := List.mem_map.mp hx
    have := hcell idx
    omega
  rw [hget]
  refine ⟨hcell i.val, ?_⟩
  rw [nttSpec_delta]
  unfold formulaCell
  by_cases hpar : i.val % 2 = j.val % 2
  · rw [if_pos hpar, if_pos hpar, cast_mod_3329]
    have hbr : brN (i.val / 2)
        = (bitRev7Table ⟨i.val / 2, by have h : i.val < 256 := i.isLt; omega⟩).val :=
      brN_eq_bitRev7 ⟨i.val / 2, by have h : i.val < 256 := i.isLt; omega⟩
    rw [hbr]
    unfold gammaForPair
    rw [← pow_mul]
    push_cast
    rfl
  · rw [if_neg hpar, if_neg hpar]
    simp

/-! ### The kernel verification and the basis-vector correspondence -/

/-- **Butterfly correctness on basis vectors**.  For each of the 256 standard
basis vectors `δⱼ`, the imperative Cooley–Tukey butterfly network of
Algorithm 7 (`ntt`) agrees with the algebraically defined CRT projection
`nttSpec` of `Spec.lean`.  Proved (no axioms, no `sorry`) by transporting the
kernel verification `nttP_deltaP_eq_formulaP` across the simulation
`simR_outerP` and matching the result with the closed form `nttSpec_delta`. -/
lemma ntt_delta_eq_nttSpec_delta (j : Fin n) : ntt (delta j) = nttSpec (delta j) := by
  have hsim : simR (nttP (deltaP j.val)) (ntt (delta j)) := by
    unfold nttP ntt
    exact simR_outerP nttLens _ _ 1 _ _ (simR_deltaP j)
  have hkey : nttP (deltaP j.val) = formulaP j.val :=
    nttP_deltaP_eq_formulaP j.val (by have h : j.val < 256 := j.isLt; omega)
  have hsim' : simR (formulaP j.val) (ntt (delta j)) := hkey ▸ hsim
  funext i
  obtain ⟨_, h1⟩ := hsim' i
  obtain ⟨_, h2⟩ := simR_formulaP j i
  rw [← h1, h2]

/-! ### Simulation of the inverse butterfly layers (Algorithm 8) -/

/-- Single inverse butterfly simulation. -/
lemma simR_ibfP {l : ℕ} {f : Fin n → Zq} (hs : simR l f)
    (z : ℕ) {start len : ℕ} (hlen : 0 < len)
    (h1 : start < n) (h2 : start + len < n) :
    simR (ibfP z l start len)
      (invNttButterfly f (z : Zq) ⟨start, h1⟩ ⟨start + len, h2⟩) := by
  intro i
  obtain ⟨hbj, hcj⟩ := hs ⟨start, h1⟩
  obtain ⟨hbl, hcl⟩ := hs ⟨start + len, h2⟩
  set a := getP l start with ha
  set b := getP l (start + len) with hb
  have hv1 : (a + b) % 3329 < 3329 := Nat.mod_lt _ (by norm_num)
  have hv2 : z * ((b + 3329 - a) % 3329) % 3329 < 3329 := Nat.mod_lt _ (by norm_num)
  have hcast1 : (((a + b) % 3329 : ℕ) : Zq) = f ⟨start, h1⟩ + f ⟨start + len, h2⟩ := by
    rw [cast_mod_3329]; push_cast; rw [hcj, hcl]
  have hcast2 : ((z * ((b + 3329 - a) % 3329) % 3329 : ℕ) : Zq) =
      (z : Zq) * (f ⟨start + len, h2⟩ - f ⟨start, h1⟩) := by
    rw [cast_mod_3329, Nat.cast_mul, cast_mod_3329, Nat.cast_sub (by omega), Nat.cast_add,
      cast_3329_eq_zero, add_zero, hcj, hcl]
  simp only [ibfP, invNttButterfly]
  by_cases hil : i.val = start + len
  · have hieq : i = ⟨start + len, h2⟩ := Fin.ext hil
    rw [hil, getP_setP_ne _ _ _ _ (by omega) (by omega), getP_setP_self _ _ _ (by omega),
      hieq, Function.update_self]
    exact ⟨hv2, hcast2⟩
  · have hine : i ≠ (⟨start + len, h2⟩ : Fin n) := fun hc => hil (by rw [hc])
    rw [Function.update_of_ne hine]
    by_cases hij : i.val = start
    · have hieq : i = ⟨start, h1⟩ := Fin.ext hij
      rw [hij, getP_setP_self _ _ _ (by omega), hieq, Function.update_self]
      exact ⟨hv1, hcast1⟩
    · have hine' : i ≠ (⟨start, h1⟩ : Fin n) := fun hc => hij (by rw [hc])
      rw [getP_setP_ne _ _ _ _ (by omega) hij, getP_setP_ne _ _ _ _ (by omega) hil,
        Function.update_of_ne hine']
      exact hs i

/-- Inverse inner-loop simulation. -/
lemma simR_iinnerP (z : ℕ) :
    ∀ (count l : ℕ) (f : Fin n → Zq) (start len : ℕ) (_hlen : 0 < len)
      (h1 : ∀ r, r < count → start + r < n)
      (h2 : ∀ r, r < count → start + r + len < n),
      simR l f →
      simR (iinnerP z l start len count)
        (invNttInnerLoop f (z : Zq) start len count h1 h2)
  | 0, _, _, _, _, _, _, _, hs => hs
  | c + 1, l, f, start, len, hlen, h1, h2, hs => by
    simp only [iinnerP, invNttInnerLoop]
    exact simR_iinnerP z c _ _ (start + 1) len hlen _ _
      (simR_ibfP hs z hlen (h1 0 (by omega))
        (by have := h2 0 (by omega); omega))

/-- Zeta-index bookkeeping of the packed inverse middle loop. -/
lemma imiddleP_snd : ∀ (nb l len startOff k : ℕ),
    (imiddleP l len startOff k nb).2 = k - nb
  | 0, _, _, _, _ => rfl
  | nb + 1, l, len, startOff, k => by
    simp only [imiddleP]
    rw [imiddleP_snd nb]
    omega

/-- Inverse middle-loop simulation. -/
lemma simR_imiddleP :
    ∀ (nb l : ℕ) (f : Fin n → Zq) (len startOff k : ℕ)
      (h_pos : 0 < len)
      (h_fit : ∀ b, b < nb → startOff + b * (2 * len) + 2 * len ≤ n)
      (h_k : ∀ b, b < nb → k - b < 128)
      (h_nb : nb ≤ k + 1),
      simR l f →
      simR (imiddleP l len startOff k nb).1
        (invNttMiddleLoop f len startOff k nb h_pos h_fit h_k h_nb).1
  | 0, _, _, _, _, _, _, _, _, _, hs => hs
  | nb + 1, l, f, len, startOff, k, h_pos, h_fit, h_k, h_nb, hs => by
    simp only [imiddleP, invNttMiddleLoop]
    have hk0 : k < 128 := by have := h_k 0 (by omega); omega
    have hz : zetaTable ⟨k, by omega⟩ = ((17 ^ brN k % 3329 : ℕ) : Zq) :=
      (cast_zeta k hk0).symm
    rw [hz]
    exact simR_imiddleP nb _ _ len (startOff + 2 * len) (k - 1) h_pos _ _ _
      (simR_iinnerP _ len _ _ startOff len h_pos _ _ hs)

/-- Inverse outer-loop simulation. -/
lemma simR_iouterP :
    ∀ (layers : List ℕ) (l : ℕ) (f : Fin n → Zq) (k : ℕ)
      (h_layers : ∀ x ∈ layers, 0 < x ∧ 2 * x ∣ n)
      (h_k : k + 1 ≥ (layers.map (fun x => n / (2 * x))).sum)
      (h_k128 : k < 128),
      simR l f →
      simR (iouterP l k layers).1
        (invNttOuterLoop f k layers h_layers h_k h_k128).1
  | [], _, _, _, _, _, _, hs => hs
  | len :: rest, l, f, k, h_layers, h_k, h_k128, hs => by
    simp only [iouterP, invNttOuterLoop]
    simp only [invNttMiddleLoop_snd, imiddleP_snd]
    exact simR_iouterP rest _ _ _ _ _ _
      (simR_imiddleP _ _ _ _ _ _ _ _ _ _ hs)

/-- `128 · deltaP j` simulates `128 · δⱼ` (digit `j` is `128`, others `0`). -/
lemma simR_128_deltaP (j : Fin n) :
    simR (128 * deltaP j.val) (fun i => (128 : Zq) * delta j i) := by
  intro i
  change getP (128 * deltaP j.val) i.val < 3329 ∧
    ((getP (128 * deltaP j.val) i.val : ℕ) : Zq) = 128 * (if i = j then 1 else 0)
  unfold deltaP getP
  rcases lt_trichotomy i.val j.val with h | h | h
  · rw [if_neg (Fin.val_ne_iff.mp (by omega))]
    set d := j.val - i.val - 1 with hd
    have h1 : j.val = d + 1 + i.val := by omega
    have hdvd : 128 * (4096 : ℕ) ^ j.val / 4096 ^ i.val = 128 * 4096 ^ d * 4096 := by
      rw [h1, pow_add, pow_succ, ← mul_assoc, ← mul_assoc]
      exact Nat.mul_div_cancel _ (Nat.pow_pos (by norm_num))
    rw [hdvd, Nat.mul_mod_left]
    exact ⟨by norm_num, by simp⟩
  · have hij : i = j := Fin.ext h
    have hdiv : 128 * (4096 : ℕ) ^ j.val / 4096 ^ i.val = 128 := by
      rw [h]; exact Nat.mul_div_cancel _ (Nat.pow_pos (by norm_num))
    rw [if_pos hij, hdiv]
    exact ⟨by norm_num, by norm_num⟩
  · rw [if_neg (Fin.val_ne_iff.mp (by omega))]
    have hlt : 128 * (4096 : ℕ) ^ j.val < 4096 ^ i.val := by
      calc 128 * (4096 : ℕ) ^ j.val < 4096 * 4096 ^ j.val :=
            Nat.mul_lt_mul_of_pos_right (by norm_num) (Nat.pow_pos (by norm_num))
        _ = 4096 ^ (j.val + 1) := by rw [pow_succ, mul_comm]
        _ ≤ 4096 ^ i.val := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.div_eq_of_lt hlt]
    exact ⟨by norm_num, by simp⟩

/-- **Round trip on basis vectors**.  For each of the 256 standard basis
vectors `δⱼ`, Algorithm 8 applied after Algorithm 7 returns `δⱼ`.  Proved (no
axioms, no `sorry`): the forward direction is `ntt_delta_eq_nttSpec_delta`
together with `simR_formulaP`; the inverse butterfly layers are transported
from the kernel verification `invNttP_formulaP_eq` across `simR_iouterP`, and
the final scaling `3303 · 128 = 1` is `nInv_mul_n`. -/
lemma invNtt_ntt_delta (j : Fin n) : invNtt (ntt (delta j)) = delta j := by
  have hfwd : ntt (delta j) = nttSpec (delta j) := ntt_delta_eq_nttSpec_delta j
  have hsim : simR (invNttP (formulaP j.val))
      (invNttOuterLoop (nttSpec (delta j)) 127 invNttLens
        (by simp [invNttLens, n]) (by simp [invNttLens, n]) (by omega)).1 := by
    unfold invNttP
    exact simR_iouterP invNttLens _ _ 127 _ _ _ (simR_formulaP j)
  have hkey : invNttP (formulaP j.val) = 128 * deltaP j.val :=
    invNttP_formulaP_eq j.val (by have h : j.val < 256 := j.isLt; omega)
  rw [hkey] at hsim
  funext i
  obtain ⟨_, h1⟩ := hsim i
  obtain ⟨_, h2⟩ := simR_128_deltaP j i
  have hmul : nInv * (128 : Zq) = 1 := nInv_mul_n
  simp only [invNtt, invNttScale, hfwd]
  rw [← h1, h2, ← mul_assoc, hmul, one_mul]

/-! ## Round-trip lemmas -/

/-- **`NTT⁻¹(NTT(f)) = f`** — Algorithm 8 undoes Algorithm 7.  Proved by
decomposing `f = ∑ⱼ f(j) · δⱼ` and using linearity of both transforms
together with the basis-vector round trip `invNtt_ntt_delta`. -/
lemma invNtt_ntt (f : Fin n → Zq) : invNtt (ntt f) = f := by
  have h1 : ntt f = fun i => ∑ j : Fin n, f j * ntt (delta j) i := by
    conv_lhs => rw [eq_sum_delta f]
    rw [ntt_sum]
    funext i
    exact Finset.sum_congr rfl fun j _ =>
      congrFun (ntt_smul (f j) (delta j)) i
  have h2 : invNtt (ntt f) = fun i => ∑ j : Fin n, f j * invNtt (ntt (delta j)) i := by
    rw [h1, invNtt_sum]
    funext i
    exact Finset.sum_congr rfl fun j _ =>
      congrFun (invNtt_smul (f j) (ntt (delta j))) i
  rw [h2]
  simp only [invNtt_ntt_delta]
  exact (eq_sum_delta f).symm

/-- **`NTT(NTT⁻¹(f̂)) = f̂`** — Algorithm 7 undoes Algorithm 8.  Derived from
`invNtt_ntt`: a left-inverse on a finite type is a two-sided inverse. -/
lemma ntt_invNtt (f : Fin n → Zq) : ntt (invNtt f) = f := by
  have hinj : Function.Injective (ntt : (Fin n → Zq) → Fin n → Zq) := by
    intro a b hab
    have h := congrArg invNtt hab
    rwa [invNtt_ntt, invNtt_ntt] at h
  obtain ⟨g, hg⟩ := Finite.surjective_of_injective hinj f
  rw [← hg, invNtt_ntt]

/-- **Butterfly correctness**.  The imperative Cooley–Tukey
butterfly network of Algorithm 7 (`ntt`) computes the algebraically defined
CRT projection `nttSpec` of `Spec.lean` — i.e. coefficient pair `(2i, 2i+1)`
of the output is the image of the input polynomial in `ℤ_q[X]/(X² − γᵢ)`.

This is the single remaining link between the FIPS 203 § 4.3 pseudocode and
its mathematical specification.  Removing it requires a layer-by-layer loop
invariant for `nttInnerLoop`/`nttMiddleLoop`/`nttOuterLoop` of the form
"after processing block length `len`, each contiguous block of size `2·len`
holds the coefficients of `f mod (X^{2·len} − ζ^{bitRev-indexed power})`",
together with the `bitRev7Table` index bookkeeping — a substantial but
self-contained formalization roadmap:

1. closed-form lemma for `nttInnerLoop` as a parallel butterfly on a block;
2. invariant: one `nttMiddleLoop` layer splits each residue
   `f mod (X^{2len} − γ²)` into `f mod (X^{len} ± γ)`;
3. induction over `nttLens = [128, 64, 32, 16, 8, 4, 2]` connecting the
   threaded zeta index `k` with `bitRev7Table`;
4. base case: blocks of size 2 are exactly the `crtHom i` coordinates.

Here it is proved from the basis-vector correspondence `ntt_delta_eq_nttSpec_delta`
by decomposing `f = ∑ⱼ f(j)·δⱼ` and using linearity of both `ntt`
(`ntt_sum`, `ntt_smul`) and `nttSpec` (`nttSpec_sum`, `nttSpec_smul`). -/
lemma ntt_eq_nttSpec : (ntt : (Fin n → Zq) → Fin n → Zq) = nttSpec := by
  funext f
  have hL : ntt f = fun i => ∑ j : Fin n, f j * ntt (delta j) i := by
    conv_lhs => rw [eq_sum_delta f]
    rw [ntt_sum]
    funext i
    exact Finset.sum_congr rfl fun j _ =>
      congrFun (ntt_smul (f j) (delta j)) i
  have hR : nttSpec f = fun i => ∑ j : Fin n, f j * nttSpec (delta j) i := by
    conv_lhs => rw [eq_sum_delta f]
    rw [nttSpec_sum]
    funext i
    exact Finset.sum_congr rfl fun j _ =>
      congrFun (nttSpec_smul (f j) (delta j)) i
  rw [hL, hR]
  funext i
  exact Finset.sum_congr rfl fun j _ => by
    rw [ntt_delta_eq_nttSpec_delta]

/-- **CRT isomorphism on basis vectors**.  For each pair of
standard basis vectors `δⱼ, δₖ`, the NTT of their product in `R_q` equals the
componentwise `MultiplyNTTs` product of their NTTs.  Proved from the
butterfly-correctness lemma `ntt_eq_nttSpec` together with the fully proven
CRT multiplicativity `nttSpec_toCoeffs_mul` and the coefficient round trip
`toCoeffs_ofCoeffs` of `Spec.lean`:  the NTT realises the CRT isomorphism
`R_q ≅ ∏ᵢ ℤ_q[X]/(X² − γᵢ)` under which ring multiplication corresponds to
`BaseCaseMultiply` on each component. -/
lemma ntt_polyMul_delta (j k : Fin n) :
    ntt (polyMulCoeffs (delta j) (delta k)) =
      multiplyNTTs (ntt (delta j)) (ntt (delta k)) := by
  rw [ntt_eq_nttSpec]
  unfold polyMulCoeffs
  rw [nttSpec_toCoeffs_mul, toCoeffs_ofCoeffs, toCoeffs_ofCoeffs]

/-- **`NTT(f · g) = MultiplyNTTs(NTT(f), NTT(g))`** — the CRT isomorphism.
Proved by decomposing `f = ∑ⱼ f(j)·δⱼ` and `g = ∑ₖ g(k)·δₖ` and expanding both
sides into the double sum `∑ⱼ ∑ₖ f(j)·g(k)·(…)` using bilinearity of
`polyMulCoeffs` and `multiplyNTTs` together with linearity of `ntt`; the
summands then agree by the basis-vector identity `ntt_polyMul_delta`. -/
lemma ntt_polyMul (f g : Fin n → Zq) :
    ntt (polyMulCoeffs f g) = multiplyNTTs (ntt f) (ntt g) := by
  have hdg : ∀ j : Fin n, polyMulCoeffs (delta j) g
      = fun i => ∑ k : Fin n, g k * polyMulCoeffs (delta j) (delta k) i := by
    intro j
    conv_lhs => rw [eq_sum_delta g]
    rw [polyMulCoeffs_sum_right]
    funext i
    exact Finset.sum_congr rfl fun k _ =>
      congrFun (polyMulCoeffs_smul_right (g k) (delta j) (delta k)) i
  have hfg : polyMulCoeffs f g
      = fun i => ∑ j : Fin n, f j * polyMulCoeffs (delta j) g i := by
    conv_lhs => rw [eq_sum_delta f]
    rw [polyMulCoeffs_sum_left]
    funext i
    exact Finset.sum_congr rfl fun j _ =>
      congrFun (polyMulCoeffs_smul_left (f j) (delta j) g) i
  have hL : ntt (polyMulCoeffs f g)
      = fun i => ∑ j : Fin n, ∑ k : Fin n,
          f j * (g k * ntt (polyMulCoeffs (delta j) (delta k)) i) := by
    rw [hfg, ntt_sum]
    funext i
    refine Finset.sum_congr rfl fun j _ => ?_
    calc ntt (fun i => f j * polyMulCoeffs (delta j) g i) i
        = f j * ntt (polyMulCoeffs (delta j) g) i :=
          congrFun (ntt_smul (f j) (polyMulCoeffs (delta j) g)) i
      _ = f j * ntt (fun i => ∑ k : Fin n,
            g k * polyMulCoeffs (delta j) (delta k) i) i := by rw [hdg j]
      _ = f j * ∑ k : Fin n,
            ntt (fun i => g k * polyMulCoeffs (delta j) (delta k) i) i := by
          rw [ntt_sum Finset.univ
            (fun k i => g k * polyMulCoeffs (delta j) (delta k) i)]
      _ = ∑ k : Fin n,
            f j * (g k * ntt (polyMulCoeffs (delta j) (delta k)) i) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by
            rw [congrFun (ntt_smul (g k) (polyMulCoeffs (delta j) (delta k))) i]
  have hnf : ntt f = fun i => ∑ j : Fin n, f j * ntt (delta j) i := by
    conv_lhs => rw [eq_sum_delta f]
    rw [ntt_sum]
    funext i
    exact Finset.sum_congr rfl fun j _ => congrFun (ntt_smul (f j) (delta j)) i
  have hng : ntt g = fun i => ∑ k : Fin n, g k * ntt (delta k) i := by
    conv_lhs => rw [eq_sum_delta g]
    rw [ntt_sum]
    funext i
    exact Finset.sum_congr rfl fun k _ => congrFun (ntt_smul (g k) (delta k)) i
  have hR : multiplyNTTs (ntt f) (ntt g)
      = fun i => ∑ j : Fin n, ∑ k : Fin n,
          f j * (g k * multiplyNTTs (ntt (delta j)) (ntt (delta k)) i) := by
    rw [hnf, hng, multiplyNTTs_sum_left]
    funext i
    refine Finset.sum_congr rfl fun j _ => ?_
    calc multiplyNTTs (fun i => f j * ntt (delta j) i)
            (fun i => ∑ k : Fin n, g k * ntt (delta k) i) i
        = f j * multiplyNTTs (ntt (delta j))
            (fun i => ∑ k : Fin n, g k * ntt (delta k) i) i :=
          congrFun (multiplyNTTs_smul_left (f j) (ntt (delta j))
            (fun i => ∑ k : Fin n, g k * ntt (delta k) i)) i
      _ = f j * ∑ k : Fin n,
            multiplyNTTs (ntt (delta j)) (fun i => g k * ntt (delta k) i) i := by
          rw [multiplyNTTs_sum_right Finset.univ
            (ntt (delta j)) (fun k i => g k * ntt (delta k) i)]
      _ = ∑ k : Fin n,
            f j * (g k * multiplyNTTs (ntt (delta j)) (ntt (delta k)) i) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by
            rw [congrFun (multiplyNTTs_smul_right (g k)
              (ntt (delta j)) (ntt (delta k))) i]
  rw [hL, hR]
  funext i
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by
    rw [ntt_polyMul_delta]


/-! ## Derived round-trip theorems -/

/-- `invNtt ∘ ntt = id` (function composition form). -/
theorem invNtt_comp_ntt : invNtt ∘ ntt = (id : (Fin n → Zq) → Fin n → Zq) := by
  ext f i; simp only [Function.comp, id]; exact congrFun (invNtt_ntt f) i

/-- `ntt ∘ invNtt = id` (function composition form). -/
theorem ntt_comp_invNtt : ntt ∘ invNtt = (id : (Fin n → Zq) → Fin n → Zq) := by
  ext f i; simp only [Function.comp, id]; exact congrFun (ntt_invNtt f) i

/-- `ntt` is injective. -/
theorem ntt_injective : Function.Injective (ntt : (Fin n → Zq) → Fin n → Zq) := by
  intro f g h; have := congrArg invNtt h; rwa [invNtt_ntt, invNtt_ntt] at this

/-- `invNtt` is injective. -/
theorem invNtt_injective : Function.Injective (invNtt : (Fin n → Zq) → Fin n → Zq) := by
  intro f g h; have := congrArg ntt h; rwa [ntt_invNtt, ntt_invNtt] at this

/-- `ntt` is surjective. -/
theorem ntt_surjective : Function.Surjective (ntt : (Fin n → Zq) → Fin n → Zq) :=
  fun fh => ⟨invNtt fh, ntt_invNtt fh⟩

/-- `invNtt` is surjective. -/
theorem invNtt_surjective : Function.Surjective (invNtt : (Fin n → Zq) → Fin n → Zq) :=
  fun f => ⟨ntt f, invNtt_ntt f⟩

/-- `ntt` is bijective. -/
theorem ntt_bijective : Function.Bijective (ntt : (Fin n → Zq) → Fin n → Zq) :=
  ⟨ntt_injective, ntt_surjective⟩

/-- `invNtt` is bijective. -/
theorem invNtt_bijective : Function.Bijective (invNtt : (Fin n → Zq) → Fin n → Zq) :=
  ⟨invNtt_injective, invNtt_surjective⟩

/-- `invNtt` is the left inverse of `ntt`. -/
theorem invNtt_leftInverse :
    Function.LeftInverse invNtt (ntt : (Fin n → Zq) → Fin n → Zq) :=
  invNtt_ntt

/-- `invNtt` is the right inverse of `ntt`. -/
theorem invNtt_rightInverse :
    Function.RightInverse invNtt (ntt : (Fin n → Zq) → Fin n → Zq) :=
  ntt_invNtt

/-! ## Multiplicative homomorphism: derived forms -/

/-- Compute `f * g` in `R_q` via the NTT pipeline. -/
theorem polyMulCoeffs_eq (f g : Fin n → Zq) :
    polyMulCoeffs f g = invNtt (multiplyNTTs (ntt f) (ntt g)) := by
  have h := ntt_polyMul f g
  have := congrArg invNtt h
  rwa [invNtt_ntt] at this

/-- Alias: `ntt(f * g) = multiplyNTTs(ntt f)(ntt g)`. -/
theorem ntt_mul_eq_multiplyNTTs (f g : Fin n → Zq) :
    ntt (polyMulCoeffs f g) = multiplyNTTs (ntt f) (ntt g) :=
  ntt_polyMul f g

/-! ## NTT pipeline end-to-end correctness -/

/-- The NTT-based multiplication pipeline computes `polyMulCoeffs`. -/
theorem ntt_pipeline_eq_polyMul (f g : Fin n → Zq) :
    invNtt (multiplyNTTs (ntt f) (ntt g)) = polyMulCoeffs f g :=
  (polyMulCoeffs_eq f g).symm

end Fips203
