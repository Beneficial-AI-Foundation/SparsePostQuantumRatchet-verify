/-
Copyright (c) 2026 BAIF. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DoubleRatchet.CKA.Defs
import VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman

/-!
# DDH-based CKA Construction

Section 4.1.2 from Alwen-Coretti-Dodis (2020).

A CKA scheme built from the DDH assumption in a cyclic group `G = ⟨g⟩`.
Uses additive notation (matching VCV-io / Mathlib conventions):
`g^a` in the paper becomes `a • g` here.

## Construction

- **Initial shared state**: `k = x₀ : F` (a random scalar).
  Party A (sender first) gets state `h = x₀ • g : G`.
  Party B (receiver) gets state `x₀ : F`.

- **Send** (`CKA-S`): Given state `h : G` (the peer's public key),
  pick a random scalar `x ← F`, compute:
  - Message: `T = x • g`
  - Output key: `I = x • h`
  - New state: `x : F` (own secret, for next receive)

- **Receive** (`CKA-R`): Given state `x : F` (own secret) and message `T : G`,
  compute:
  - Output key: `I = x • T`
  - New state: `T : G` (peer's public key, for next send)

Correctness follows from `smul_smul`: both parties compute `(x * x₀) • g`.
-/

set_option autoImplicit false

open OracleComp

namespace CKA

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G]

/-- The DDH-based CKA scheme in a cyclic group `G` with generator `g` and
scalar field `F`.

Types:
- `SharedKey = F` (initial random scalar `x₀`)
- `SenderState = G` (peer's public key `h`)
- `ReceiverState = F` (own secret scalar `x`)
- `Msg = G` (DH public value `T = x • g`)
- `Output = G` (agreed key `I`) -/
def ddhCKA (g : G) : CKAScheme F G F G G where
  init k := pure (k • g, k)
  send h := do
    let x ← $ᵗ F
    pure (x, x • g, x • h)
  recv x msg := pure (msg, x • msg)

/-- DDH-CKA with explicit sender coins. `SendCoins = F` (the random exponent).

This exposes the deterministic core of `send`: given state `h : G` and coins `x : F`,
produce `(x, x • g, x • h)` without sampling. Used by the Figure 3 game's
`send-P'(r)` oracle where the adversary supplies the coins. -/
noncomputable def ddhCKAWithCoins (g : G) : CKASchemeWithCoins F G F G G F where
  init k := pure (k • g, k)
  sendDet h x := (x, x • g, x • h)
  recv x msg := pure (msg, x • msg)

/-- The derived `CKAScheme` from `ddhCKAWithCoins` equals `ddhCKA`. -/
lemma ddhCKAWithCoins_toCKAScheme (g : G) :
    (ddhCKAWithCoins (F := F) g).toCKAScheme = ddhCKA (F := F) g := by
  sorry

end CKA
