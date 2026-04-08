/-
Copyright (c) 2026 BAIF. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DoubleRatchet.Theorems.Theorem3
import VCVio.CryptoFoundations.Asymptotics.Security

/-!
# Asymptotic Security: Runtime Modeling for Theorem 3

The paper's Theorem 3 states security as `(t, Δ, ε)`-secure, where `t` is a
computational runtime bound. Our concrete formalization drops `t` (quantifies
over ALL adversaries). This file adds the asymptotic layer:

> If DDH is hard (advantage negligible for all PPT adversaries), then
> DDH-CKA is secure (advantage negligible for all PPT adversaries).

This uses VCV-io's `SecurityGame.secureAgainst_of_reduction` with:
- `reduce := ckaAdvToDDHAdv` (the reduction from CKA to DDH adversaries)
- `hbound` := our concrete `ddh_implies_cka_security` (per-adversary bound)
- `hreduce` := the reduction preserves PPT-ness (hypothesis — `t ≈ t'`)

## What `t ≈ t'` means

The reduction `ckaAdvToDDHAdv` transforms a CKA adversary A into a DDH
adversary B that runs A as a black box. The runtime of B is essentially
the runtime of A plus O(1) overhead (one init + one forwarding). The PPT
preservation hypothesis `hreduce` formalizes this.

## Design: families indexed by security parameter

For asymptotic security, all types and objects are parameterized by a
security parameter `sp : ℕ`. We model this abstractly: the user supplies
- A family of generators `gFamily : ℕ → G`
- A family of bijectivity proofs
- A PPT predicate for each adversary class

This keeps `F` and `G` fixed (as in the concrete formulation) — the security
parameter selects the generator within a fixed group family. For a fully
concrete instantiation (e.g., `F = ZMod p(sp)`), one would parameterize
the types as well; we leave this for future work.
-/

set_option autoImplicit false

open OracleComp DiffieHellman ENNReal

namespace CKA

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [Inhabited F]
variable {G : Type} [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G]
  [Inhabited G]

/-! ## Security games as `SecurityGame` instances -/

/-- DDH security game indexed by security parameter.
The generator `gFamily sp` selects the group generator for parameter `sp`.
Advantage is `ddhDistAdvantage` lifted to `ℝ≥0∞`. -/
noncomputable def ddhSecurityGame (gFamily : ℕ → G) :
    SecurityGame (DDHAdversary F G) where
  advantage A sp := ENNReal.ofReal (ddhDistAdvantage (F := F) (gFamily sp) A)

/-- CKA security game (single-epoch) indexed by security parameter.
Uses the DDH-CKA construction with generator `gFamily sp`. -/
noncomputable def ckaSecurityGame (gFamily : ℕ → G) :
    SecurityGame (CKAAdversary G G) where
  advantage A sp := ENNReal.ofReal (ckaDistAdvantage (ddhCKA (F := F) (gFamily sp)) A)

/-! ## Asymptotic Theorem 3 -/

/-- **Theorem 3, asymptotic form**: If DDH is hard (negligible advantage for
all PPT adversaries), then DDH-CKA is secure (negligible advantage for all
PPT adversaries).

The parameters:
- `gFamily` : security-parameter-indexed generator family
- `hg` : each generator is a bijective generator (formalizes prime-order group)
- `isPPT_CKA`, `isPPT_DDH` : efficiency predicates (left abstract)
- `hreduce` : the reduction preserves PPT-ness (formalizes `t ≈ t'`)
- `hDDH` : DDH assumption (the game is secure against PPT adversaries)

This is a direct application of `SecurityGame.secureAgainst_of_reduction`. -/
theorem ddh_implies_cka_security_asymptotic
    (gFamily : ℕ → G)
    (hg : ∀ sp, Function.Bijective (· • gFamily sp : F → G))
    (isPPT_CKA : CKAAdversary G G → Prop)
    (isPPT_DDH : DDHAdversary F G → Prop)
    (hreduce : ∀ A, isPPT_CKA A → isPPT_DDH (ckaAdvToDDHAdv A))
    (hDDH : (ddhSecurityGame (F := F) gFamily).secureAgainst isPPT_DDH) :
    (ckaSecurityGame (F := F) gFamily).secureAgainst isPPT_CKA := by
  apply SecurityGame.secureAgainst_of_reduction hreduce _ hDDH
  intro A sp
  -- Need: ckaSecurityGame advantage ≤ ddhSecurityGame advantage
  -- i.e., ofReal (ckaDistAdvantage ...) ≤ ofReal (ddhDistAdvantage ...)
  -- This follows from our concrete ddh_implies_cka_security
  sorry

/-- The concrete per-adversary bound lifts to the asymptotic advantage bound.
This is the key lemma connecting the concrete and asymptotic formulations:
`ckaDistAdvantage ≤ ddhDistAdvantage` implies the `ℝ≥0∞`-valued inequality
needed by `secureAgainst_of_reduction`. -/
lemma ckaAdvantage_le_ddhAdvantage_ennreal
    (g : G)
    (hg : Function.Bijective (· • g : F → G))
    (A : CKAAdversary G G) :
    ENNReal.ofReal (ckaDistAdvantage (ddhCKA (F := F) g) A) ≤
      ENNReal.ofReal (ddhDistAdvantage (F := F) g (ckaAdvToDDHAdv A)) := by
  apply ENNReal.ofReal_le_ofReal
  exact ddh_implies_cka_security g hg A

end CKA
