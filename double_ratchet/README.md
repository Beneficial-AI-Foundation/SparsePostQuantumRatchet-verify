# DoubleRatchet

Lean 4 formalization of the double ratchet protocol security analysis from:

> Alwen, Coretti, Dodis. "The Double Ratchet: Security Notions, Proofs, and
> Modularization for the Signal Protocol" (2020).

## Current Scope

**Theorem 3** (Section 4.1.2, p22): If group G is DDH-secure, then the
DDH-based Continuous Key Agreement (CKA) scheme is secure with healing
parameter Delta = 1.

This is the core theorem connecting the DDH assumption to CKA security —
the "public-key ratchet" building block of Signal's double ratchet.

Status: **paper-oriented Theorem 3 skeleton** — Figure 3 oracle game implemented
with adaptive adversary, party-specific corruption, bad-randomness oracles, and
explicit ping-pong enforcement. Proofs use `sorry`.

## Project Structure

```
DoubleRatchet/
  CKA/
    Defs.lean              Definition 12: CKAScheme + CKASchemeWithCoins
    SecurityGame.lean      Single-epoch real-or-random game
    Security.lean          Definition 13: CKASecure predicate (single-epoch)
    Figure3Game.lean       Figure 3: adaptive oracle game, Figure3CKASecure with Δ
    MultiEpochGame.lean    Restricted multi-epoch game (auxiliary, non-adaptive)
  Constructions/
    DDHCKA.lean            DDH-based CKA + ddhCKAWithCoins (Section 4.1.2)
  Theorems/
    Theorem3.lean          Reduction + concrete, paper-form, Δ=1, and Figure 3 theorems
    AsymptoticSecurity.lean  Runtime modeling via SecurityGame + secureAgainst_of_reduction
doc/
  paper-to-lean-correspondence.md   Notation map and 1:1 definition correspondence
  vcv-io-dependency.md              Analysis of VCV-io dependency tradeoffs
  TODO.md                           Sorry proof strategy, remaining work
```

## Dependencies

- **VCV-io** (commit `a3d6c41`): Provides DDH definitions, probability monad
  (`ProbComp`), uniform sampling (`SampleableType`), and probability notation.
  VCV-io transitively brings Mathlib v4.28.0.
- **Lean**: v4.28.0

## Building

```bash
lake exe cache get   # download prebuilt mathlib oleans (required first time)
lake build           # compile — expect sorry warnings, no errors
```

## Future Work

- **Prove the sorry's**: 7 core sorry's (distribution equalities + theorem variants),
  2 structural sorry's (Figure 3 layer). See `doc/TODO.md` for strategy.
- **Full paper formalization**: FS-AEAD, PRF-PRNG, SM scheme, Theorems 1/6/8/12
- **VCV-io dependency**: May simplify to direct ZMod p formulation
  (see `doc/vcv-io-dependency.md`)
