# TODO

## Prove the sorry's

Nine `sorry` declarations across the formalization:

### Core (Theorem3.lean) — 4 sorry's

1. `ckaRealExp_eq_ddhExpReal` — distribution equality via `smul_smul` + `mul_comm`
2. `ckaRandExp_eq_ddhExpRand` — distribution equality using bijectivity `hg`
3. `ddh_implies_cka_security` — follows from (1) and (2) by rewriting advantage
4. `ddh_implies_cka_security_paper_form` — follows from (3) by instantiation

### Structural (follow mechanically from the core sorry's) — 3 sorry's

5. `ddh_implies_cka_security_delta` (Theorem3.lean) — multi-epoch Δ=1 form;
   follows from (3) + bridge showing single-epoch reduction extends to multi-epoch
6. `CKASecureDelta_implies_CKASecure` (MultiEpochGame.lean) — lift single-epoch
   adversary to 1-epoch multi-epoch adversary
7. `ddh_implies_cka_security_asymptotic` (AsymptoticSecurity.lean) — applies
   `secureAgainst_of_reduction` with (3) as the bound; needs `ENNReal.ofReal` lift

### Figure 3 game layer — 2 sorry's

8. `ddhCKAWithCoins_toCKAScheme` (DDHCKA.lean) — derived CKAScheme equals
   original `ddhCKA`; follows by unfolding definitions
9. `ddh_implies_figure3_cka_security` (Theorem3.lean) — Theorem 3 over the
   full Figure 3 oracle game with Δ=1; the main paper-faithful statement

### Proof strategy

Start with (1) and (2): unfold both sides, show monadic computations produce
identical distributions. Key Mathlib lemmas:
- `smul_smul : (a * b) • x = a • (b • x)` (Module axiom)
- `mul_comm` (Field is commutative)
- `probOutput_map_bijective_uniform_cross` (VCV-io, for bijectivity in (2))

Then (3) follows by rewriting the advantage definition, (4)-(7) are mechanical.
(8) is definitional. (9) requires a reduction from Figure 3 adversaries to DDH.

## ✅ Runtime Modeling (DONE)

Implemented in `Theorems/AsymptoticSecurity.lean`:
- `ddhSecurityGame` / `ckaSecurityGame` — `SecurityGame` instances indexed by `sp : ℕ`
- `ddh_implies_cka_security_asymptotic` — applies `secureAgainst_of_reduction`
- `ckaAdvantage_le_ddhAdvantage_ennreal` — lifts concrete bound to `ℝ≥0∞`
- `isPPT` left abstract (hypothesis); `hreduce` formalizes `t ≈ t'`

## ✅ Figure 3 oracle game (DONE — semantics repaired)

Implemented in `CKA/Figure3Game.lean` — paper-faithful oracle-based game:
- `Figure3Adversary` — adaptive `OracleComp` adversary with game oracle access
- `CKAQueryIdx` — oracle index: `sendHonest`, `sendBadRand`, `receive`,
  `challenge`, `corrupt` (all party-specific)
- `ckaOracleSpec` / `ckaGameQueryImpl` — oracle spec and stateful implementation
- All oracle return types wrapped in `Option` — failed `req` guards return `none`
  with state unchanged (paper's rollback semantics, not game-abort)
- `send-P'(r)` checks `allowCorrPostIncrement` (post-increment epoch), matching
  the paper's `t_A++` then `req allow-corr` ordering
- End-of-game tracked via `corruptedPostChalA`/`corruptedPostChalB`; all queries
  return `none` after both parties corrupted post-challenge
- `CKAGameState` — party states, epoch counters, ping-pong phase tracking
- `allowCorrFig3` / `finishedParty` / `corruptionPermittedFig3` — party-specific
  corruption predicates matching Figure 3
- `figure3Exp` / `figure3Advantage` / `Figure3CKASecure` — game and security def
- `CKASchemeWithCoins` in `Defs.lean` — exposes `sendDet` for `send-P'(r)`
- `ddhCKAWithCoins` in `DDHCKA.lean` — DDH-CKA with `SendCoins = F`
- `ddh_implies_figure3_cka_security` in `Theorem3.lean` — Theorem 3 over Figure 3

## Restricted multi-epoch game (auxiliary)

`CKA/MultiEpochGame.lean` — non-adaptive transcript-level approximation.
Kept as auxiliary reduction kernel. Not the paper's full Figure 3 model:
- Non-adaptive adversary (commits upfront to `tStar`, epoch count, corruption)
- Corruption not party-specific (no separate `corr-A`/`corr-B`)
- Only sender-side state snapshots tracked
- No bad-randomness oracle (`send-P'(r)` absent)
- `CKASecureDelta` / `ddh_implies_cka_security_delta` target this restricted game

## Lift asymptotic wrapper to Figure 3 adaptive game

`AsymptoticSecurity.lean` currently targets the single-epoch `ckaDistAdvantage`,
not the full Figure 3 adaptive game. To complete the asymptotic story:

- Define a `figure3SecurityGame` using `figure3Advantage` from `Figure3Game.lean`
- Prove `ddh_implies_figure3_cka_security_asymptotic` by lifting
  `ddh_implies_figure3_cka_security` via `secureAgainst_of_reduction`
- State clearly what remains abstract: adversary efficiency, runtime preservation,
  security-parameter indexing

This is blocked on proving `ddh_implies_figure3_cka_security` (currently `sorry`).

## Additional building blocks for the full paper

To formalize the complete double ratchet:
- FS-AEAD (Definition 14, Section 4.2) — forward-secure authenticated encryption
- PRF-PRNG (Definition 16, Section 4.3) — dual-purpose hash function
- SM scheme (Definition 6, Section 3.1) — secure messaging syntax
- SM security game (Figure 2, Section 3.2) — the main security definition
- Theorem 1 (Section 3.3) — correctness + authenticity + privacy ⟹ SM security
- Theorem 6 (Section 5.3) — main composition theorem

## VCV-io dependency decision

See `doc/vcv-io-dependency.md` for analysis. Current decision: keep VCV-io.
Revisit if API friction becomes blocking.
