/-
Copyright (c) 2026 BAIF. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DoubleRatchet.CKA.Security
import DoubleRatchet.CKA.MultiEpochGame
import DoubleRatchet.CKA.Figure3Game
import DoubleRatchet.Constructions.DDHCKA

/-!
# Theorem 3: DDH Security Implies CKA Security

Theorem 3 from Alwen-Coretti-Dodis (2020), Section 4.1.2, page 22.

**Statement**: If group G is (t,ε)-DDH-secure, then the DDH-based CKA scheme
is (t,Δ,ε)-secure for t ≈ t' and Δ = 1.

## Proof idea (reduction)

Given a CKA adversary `A` that distinguishes real from random CKA output,
construct a DDH adversary `B` as follows:

- `B` receives `(g, a • g, b • g, c • g)` from the DDH challenger
- `B` interprets `a • g` as the peer's public key `h` (from `init` with `k = a`)
- `B` interprets `b • g` as the CKA message `T` (from `send` with `x = b`)
- `B` interprets `c • g` as the candidate output `I`
- `B` feeds `(T, I) = (b • g, c • g)` to the CKA adversary `A`

If `c = a * b` (real DDH triple), then `c • g = (a * b) • g = b • (a • g) = b • h`,
which is the genuine CKA output. If `c` is random, then `c • g` is random.
So `B`'s DDH advantage equals `A`'s CKA advantage.

## Why `F`, `Module F G`, and `Function.Bijective (· • g)`?

A cyclic group G of order n with generator g is abstractly ℤ/nℤ acting on G
by repeated addition: `k • g = g + g + ⋯ + g` (k times). The group G is
naturally a ℤ-module, but the action `(· • g : ℤ → G)` is NOT injective
(k and k + n give the same element).

In cryptography, we work with prime-order groups: n = p is prime, so ℤ/pℤ
is a field. That field is `F`. The type-class `[Module F G]` says "F acts on
G by scalar multiplication". The hypothesis

    `hg : Function.Bijective (· • g : F → G)`

encodes BOTH:
- **Surjectivity**: g generates all of G (every element is a • g for some a)
- **Injectivity**: |F| = |G| and g has trivial stabilizer

Together these say G ≅ F as an F-module via `a ↦ a • g`, which is exactly
"G = ⟨g⟩ is a cyclic group of prime order |F|."

This hypothesis is needed for `ckaRandExp_eq_ddhExpRand`: the CKA random game
samples uniformly from G, while the DDH random game samples `c ← F` and
computes `c • g`. These are the same distribution iff `(· • g)` is bijective.
-/

set_option autoImplicit false

open OracleComp DiffieHellman

namespace CKA

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [Inhabited F]
variable {G : Type} [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G]
  [Inhabited G]

/-- Given a CKA adversary, construct a DDH adversary with the same advantage.
The DDH adversary ignores `g` and `a • g` (the setup), and feeds
`(b • g, c • g)` = `(T, I_candidate)` to the CKA adversary. -/
def ckaAdvToDDHAdv (adversary : CKAAdversary G G) : DDHAdversary F G :=
  fun _g _aG bG cG => adversary bG cG

/-- The CKA real game with the DDH-CKA scheme produces the same distribution
as the DDH real game with the reduced adversary.

CKA real: sample `k ← F`, `x ← F`, adversary sees `(x • g, x • (k • g))`.
DDH real: sample `a ← F`, `b ← F`, adversary sees `(b • g, (a * b) • g)`.
These are identical (with `k = a`, `x = b` and using `smul_smul`). -/
lemma ckaRealExp_eq_ddhExpReal (g : G) (adversary : CKAAdversary G G) :
    ckaRealExp (SharedKey := F) (SenderState := G) (ReceiverState := F)
      (ddhCKA (F := F) g) adversary =
      ddhExpReal (F := F) g (ckaAdvToDDHAdv adversary) := by
  sorry

/-- The CKA random game with the DDH-CKA scheme produces the same distribution
as the DDH random game with the reduced adversary.

Requires `hg : Function.Bijective (· • g)` (i.e., g generates G): the CKA
random game samples uniformly from `G` via `$ᵗ G`, while the DDH random game
samples `c ← $ᵗ F` and computes `c • g`. These distributions coincide iff
`(· • g : F → G)` is bijective. -/
lemma ckaRandExp_eq_ddhExpRand (g : G)
    (hg : Function.Bijective (· • g : F → G))
    (adversary : CKAAdversary G G) :
    ckaRandExp (SharedKey := F) (SenderState := G) (ReceiverState := F)
      (ddhCKA (F := F) g) adversary =
      ddhExpRand (F := F) g (ckaAdvToDDHAdv adversary) := by
  sorry

/-- **Theorem 3** (Alwen-Coretti-Dodis 2020), concrete per-adversary form:

For every CKA adversary `A`, its advantage against the DDH-CKA scheme is
bounded by the DDH advantage of the reduced adversary `ckaAdvToDDHAdv A`.

The hypothesis `hg` formalizes "G = ⟨g⟩ is cyclic of prime order |F|".
See the module docstring for why this is needed and how it relates to the
standard mathematical definition of a cyclic group. -/
theorem ddh_implies_cka_security (g : G)
    (hg : Function.Bijective (· • g : F → G))
    (adversary : CKAAdversary G G) :
    ckaDistAdvantage (ddhCKA (F := F) g) adversary ≤
      ddhDistAdvantage (F := F) g (ckaAdvToDDHAdv adversary) := by
  sorry

/-- **Theorem 3** (Alwen-Coretti-Dodis 2020), single-epoch epsilon form:

If every DDH adversary has advantage ≤ ε, then every single-epoch CKA
adversary has advantage ≤ ε. This follows from `ddh_implies_cka_security`
by instantiation.

**Note**: This targets `CKASecure` (single-epoch game), not the full
Figure 3 adaptive game. For the paper-faithful Figure 3 statement, see
`ddh_implies_figure3_cka_security`. -/
theorem ddh_implies_cka_security_paper_form (g : G)
    (hg : Function.Bijective (· • g : F → G))
    (ε : ℝ)
    (hDDH : ∀ B : DDHAdversary F G, ddhDistAdvantage g B ≤ ε) :
    CKASecure (ddhCKA (F := F) g) ε := by
  sorry

/-- **Theorem 3** (restricted multi-epoch game, auxiliary, Δ=1):

If every DDH adversary has advantage ≤ ε, then the DDH-CKA scheme is
`CKASecureDelta` with Δ=1 in the restricted non-adaptive multi-epoch game.

**Note**: This targets `CKASecureDelta` from `MultiEpochGame.lean` — a
restricted non-adaptive game where the adversary commits upfront. This is
NOT the paper's full Figure 3 model. For the paper-faithful adaptive
statement, see `ddh_implies_figure3_cka_security`. -/
theorem ddh_implies_cka_security_delta (g : G)
    (hg : Function.Bijective (· • g : F → G))
    (ε : ℝ)
    (hDDH : ∀ B : DDHAdversary F G, ddhDistAdvantage g B ≤ ε) :
    CKASecureDelta (ddhCKA (F := F) g) 1 ε := by
  sorry

/-- **Theorem 3** (Figure 3 formulation with adaptive oracles):

If G is (t,ε)-DDH-secure, then the DDH-based CKA scheme is (t, Δ=1, ε)-secure
in the full Figure 3 game with adaptive oracle interaction, party-specific
corruption, and bad-randomness oracles.

This is the paper-faithful statement over the upgraded game model. The proof
(when filled in) embeds the DDH challenge at epoch `t*` and simulates all
other epochs honestly. -/
theorem ddh_implies_figure3_cka_security (g : G)
    (hg : Function.Bijective (· • g : F → G))
    (ε : ℝ)
    (hDDH : ∀ B : DDHAdversary F G, ddhDistAdvantage g B ≤ ε) :
    Figure3.Figure3CKASecure (ddhCKAWithCoins (F := F) g) 1 ε := by
  sorry

end CKA
