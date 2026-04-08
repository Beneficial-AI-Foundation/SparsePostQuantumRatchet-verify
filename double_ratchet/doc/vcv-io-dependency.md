# VCV-io Dependency Analysis

Should we keep VCV-io as a dependency, copy the infrastructure we need,
or rewrite from scratch using Mathlib directly?

## The Mathematical Observation

A cyclic group of prime order p IS ℤ/pℤ, canonically. The whole
`Module F G` + `hg : Bijective` dance is just saying "G ≅ F via a ↦ a • g"
with extra steps.

The reason VCV-io uses this API: they want to keep F (scalars/exponents) and
G (group elements) as separate types so you can instantiate G with an
elliptic curve group where the representations differ (Curve25519 points vs.
ZMod p scalars). The bijectivity hypothesis is the tax on that abstraction.

For pure math, you could just write DDH directly in ZMod p: "distinguish
(a, b, a*b) from (a, b, c) for uniform a, b, c ∈ ZMod p." No Module, no
bijectivity, no generator. That's cleaner and equivalent.

## What We Actually Import

Our 5 Lean files use exactly 4 VCV-io modules:

```
CKA/Defs.lean            → VCVio.OracleComp.ProbComp
CKA/SecurityGame.lean    → VCVio.EvalDist.Bool
                           VCVio.OracleComp.Constructions.SampleableType
Constructions/DDHCKA.lean → VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman
Theorems/Theorem3.lean   → (nothing extra, via transitive imports)
```

## What We Actually Use From Each Import

### 1. `VCVio.OracleComp.ProbComp` (41 lines in VCV-io)

We use:
- `ProbComp α` — type abbreviation for `OracleComp unifSpec α`
- `do` notation, `pure`, `>>=` on ProbComp

This is a **free monad** over oracle queries, specialized to uniform sampling.
Under the hood: `OracleComp` is a polynomial-functor free monad with an
"oracle spec" indexing the available queries. `unifSpec` provides uniform
sampling from `Fin n`.

What we actually need: a probability monad. Mathlib has `PMF` (probability
mass functions) but no monadic `do` notation for it. VCV-io's value is
providing `ProbComp` with `do` notation + probability evaluation.

### 2. `VCVio.EvalDist.Bool` (imports chain)

We use:
- `Pr[= x | computation]` — probability notation
- `ENNReal.toReal` — converting probabilities to ℝ for the advantage

This is the "evaluation semantics" that interprets `ProbComp α` as an actual
probability distribution and lets you compute `Pr[event | computation]`.

Transitive chain: `EvalDist.Bool` → `EvalDist.Defs.Basic` → `OracleComp.EvalDist`
→ Mathlib's SPMF/PMF infrastructure.

### 3. `VCVio.OracleComp.Constructions.SampleableType` (~300 lines)

We use:
- `SampleableType β` — typeclass for types with uniform sampling
- `$ᵗ T` — notation for `uniformSample T`
- Instances for `Bool`, `Fin n`, products, `ZMod`

This is the bridge between "sample uniformly from type T" and the oracle
framework. It provides `selectElem : ProbComp β` that samples uniformly.

### 4. `VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman` (~330 lines)

We use:
- `DDHAdversary F G` — type alias `G → G → G → G → ProbComp Bool`
- `ddhExpReal g adversary` — real DDH game
- `ddhExpRand g adversary` — random DDH game
- `ddhDistAdvantage g adversary` — `|Pr[real=1] - Pr[rand=1]|`

We do NOT use:
- `DLogAdversary`, `dlogExp` — discrete log
- `CDHAdversary`, `cdhExp` — computational DH
- `ddhExp` (single-game formulation), `ddhGuessAdvantage`
- `ddhDistAdvantage_eq_two_mul_ddhGuessAdvantage` — relating formulations
- `dlogGenerable`, `NondegenerateGenerator` — cyclic group helpers
- `cdhToDDHReduction` and related theorems — CDH-to-DDH reduction

## What VCV-io Brings Transitively

VCV-io depends on Mathlib v4.28.0. Through our 4 imports, we pull in:
- The entire `OracleComp` framework (~16 files, ~3K lines)
- `EvalDist` probability semantics (~12 files, ~2K lines)
- `CryptoFoundations` base (~500 lines of SecExp, etc.)
- Mathlib's `Probability.ProbabilityMassFunction` module
- Mathlib's `MeasureTheory` (transitively, for SPMF)
- `ToMathlib/` extensions (~1K lines of extra Mathlib lemmas)

Total VCV-io surface: ~50K lines. We use ~55 lines directly.

## Three Options

### Option A: Keep VCV-io (status quo)

**Pros:**
- Already working, builds clean
- DDH definitions are battle-tested (used in ElGamal proof, CDH reduction)
- If we later formalize Theorem 6 (full SM), VCV-io's KEM, PRF, PRG
  definitions and the program logic tactics become valuable
- Proven lemmas available (e.g., `ddhDistAdvantage_eq_two_mul_ddhGuessAdvantage`)

**Cons:**
- Pulls 50K+ lines of VCV-io + 400K lines of Mathlib for 55 lines of usage
- We don't control the API; changes upstream could break us
- The `Module F G` + bijectivity abstraction is heavier than needed
- `OracleComp` free monad is more complex than a simple probability monad
- Lake dependency management pain (as we experienced)

**Effort:** 0 (done)

### Option B: Copy ~200 lines, still depend on Mathlib

Copy only what we need:
1. `ProbComp` as a wrapper around Mathlib's `PMF` with do-notation (~50 lines)
2. `SampleableType` with instances for `ZMod p`, `Bool` (~50 lines)
3. DDH definitions rewritten for `ZMod p` directly (~30 lines)
4. Probability notation `Pr[= x | comp]` (~30 lines)
5. Advantage definition (~10 lines)

The DDH definitions become dramatically simpler:

```lean
-- Instead of Module F G + bijectivity:
variable (p : ℕ) [Fact (Nat.Prime p)]

def DDHAdversary := ZMod p → ZMod p → ZMod p → ProbComp Bool

def ddhRealExp (adversary : DDHAdversary p) : ProbComp Bool := do
  let a ← $ᵗ (ZMod p)
  let b ← $ᵗ (ZMod p)
  adversary a b (a * b)

def ddhRandExp (adversary : DDHAdversary p) : ProbComp Bool := do
  let a ← $ᵗ (ZMod p)
  let b ← $ᵗ (ZMod p)
  let c ← $ᵗ (ZMod p)
  adversary a b c
```

No generator, no Module, no bijectivity hypothesis. The CKA construction
becomes:

```lean
def ddhCKA (p : ℕ) [Fact (Nat.Prime p)] : CKAScheme ... where
  init k := pure (k, k)         -- both parties know k ∈ ZMod p
  send h := do
    let x ← $ᵗ (ZMod p)
    pure (x, x, x * h)          -- msg = x, output = x * h
  recv x msg := pure (msg, x * msg)
```

**Pros:**
- Mathematically transparent: DDH is just multiplication in ZMod p
- No bijectivity hypothesis needed
- No `Module F G` indirection
- Still use Mathlib for `ZMod`, `PMF`, algebraic lemmas
- We control everything

**Cons:**
- Need to build the `ProbComp` monad + notation from scratch (~200 lines)
- Lose connection to VCV-io's proven lemmas
- If we later want EC group instantiations, we'd need to add abstraction back
- Mathlib dependency remains (for ZMod, PMF, etc.)

**Effort:** ~1-2 days

**Risk:** The ProbComp monad is the hardest part. VCV-io's `OracleComp` has
subtle design choices (SPMF for partial computations, support tracking, etc.)
that may be needed for the distribution equality proofs. Rolling our own
could hit unexpected walls when proving `ckaRealExp_eq_ddhExpReal`.

### Option C: Minimal, Mathlib-only

Same as Option B but also avoid building a custom ProbComp monad.
Use Mathlib's `PMF` directly as a type, define games as PMF-valued functions.

```lean
def DDHRealDist (p : ℕ) [Fact (Nat.Prime p)] : PMF (ZMod p × ZMod p × ZMod p) :=
  PMF.uniformOfFintype (ZMod p) >>= fun a =>
  PMF.uniformOfFintype (ZMod p) >>= fun b =>
  PMF.pure (a, b, a * b)
```

**Pros:**
- Zero external dependencies beyond Mathlib
- Maximally transparent
- Mathlib's PMF has good automation (simp lemmas, etc.)

**Cons:**
- PMF doesn't have nice do-notation in Lean 4 (awkward bind chains)
- All VCV-io probability lemmas need re-proving from Mathlib primitives
- No `Pr[= x | comp]` notation without building it
- Higher effort for less ergonomic code

**Effort:** ~3-5 days

## What VCV-io Might Be Useful For Later

If we formalize beyond Theorem 3:
- **KEM definitions** (`KeyEncapMech.lean`) — for Theorem 2 (KEM → CKA)
- **PRF definitions** (`PRF.lean`) — for PRF-PRNG (Section 4.3)
- **PRG definitions** (`PRG.lean`) — for FS-AEAD (Section 4.2)
- **Program logic tactics** (`rvcstep`, `vcstep`) — for distribution proofs
- **Asymptotic security** (`Security.lean`) — for runtime modeling
- **ElGamal example** — reference for DDH-based proofs

## Current Recommendation

**Keep VCV-io for now, but document the escape hatch.**

The concrete risk of rewriting is the ProbComp monad: VCV-io's probability
evaluation semantics (evalDist, support tracking, SPMF) are ~2K lines of
subtle code. We need these for the distribution equality proofs (the sorry's).
Re-implementing risks getting stuck on exactly those proofs.

However, if VCV-io's API friction becomes blocking (e.g., the Module F G
abstraction makes proofs harder than they should be), Option B is viable
and well-scoped. The DDH simplification to ZMod p is particularly attractive
for mathematical clarity.

**Concrete trigger for switching:** If proving `ckaRealExp_eq_ddhExpReal` is
significantly harder with the Module F G API than it would be with ZMod p,
switch to Option B.
