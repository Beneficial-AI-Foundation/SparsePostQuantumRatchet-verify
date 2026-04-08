# FromVCVio — Reference Copies

Read-only copies of VCV-io source files we depend on, for easy browsing.
These are NOT compiled — the real dependency comes from `.lake/packages/VCV-io/`.

Mirrors the original directory structure under `VCVio/` so paths match the
upstream repo at https://github.com/Verified-zkEVM/VCV-io (commit `a3d6c41`).

## What's Here

### Direct imports (used by our Lean files)

| File | Our import | What we use |
|------|-----------|-------------|
| `OracleComp/ProbComp.lean` | `CKA/Defs.lean` | `ProbComp` type, `do` notation |
| `OracleComp/Constructions/SampleableType.lean` | `CKA/SecurityGame.lean` | `SampleableType`, `$ᵗ T` notation |
| `EvalDist/Bool.lean` | `CKA/SecurityGame.lean` | `Pr[= x \| comp]` notation |
| `CryptoFoundations/HardnessAssumptions/DiffieHellman.lean` | `Constructions/DDHCKA.lean` | `DDHAdversary`, `ddhExpReal`, `ddhExpRand`, `ddhDistAdvantage` |

### Key transitive deps (define the core abstractions)

| File | What it defines |
|------|----------------|
| `OracleComp/OracleComp.lean` | `OracleComp` free monad (the computation type) |
| `OracleComp/OracleSpec.lean` | `OracleSpec` (polynomial functor indexing oracles) |
| `OracleComp/OracleQuery.lean` | `OracleQuery` (single oracle query type) |
| `EvalDist/Defs/Basic.lean` | `evalDist`, `probOutput`, `Pr[...]` — probability semantics |
| `CryptoFoundations/SecExp.lean` | `SecExp`, advantage definitions |

### For runtime modeling (TODO)

| File | What it defines |
|------|----------------|
| `CryptoFoundations/Asymptotics/Security.lean` | `SecurityGame`, `secureAgainst`, `isPPT`, hybrid argument |
