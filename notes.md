# Extracting Rust to Lean using Aeneas - Process Notes

## Project: SparsePostQuantumRatchet (spqr)
- Rust crate, edition 2021, rust-version 1.83.0
- Dependencies include: curve25519-dalek, hax-lib, libcrux-ml-kem, prost, sha2, etc.
- Already has hax proof infrastructure (`proofs/` dir, `hax-lib` dependency, `hax.py`)

## Goal
Extract the Rust code to Lean 4 using Aeneas for formal verification.

## Steps

### 1. Fork and clone (done)
- Forked the repo on GitHub
- Cloned locally and opened in VSCode

### 2. Initialize aeneas-config.yml
- Ran `npx aeneas-cli init` (interactive wizard)
- Set crate directory to `.` (current dir)
- Aeneas pinned to `main` branch of `https://github.com/AeneasVerif/aeneas.git`
- Charon preset: `aeneas`
- Aeneas options: `loops-to-rec`, `split-files`
- Output destination: `LeanOutput/`
- Fixed crate name from `SparsePostQuantumRatchet` to `spqr` (must match `Cargo.toml` package name)

### 3. Configure module-by-module extraction
- Listed all crate modules in `aeneas-config.yml` under `charon.start_from`
- Modules (in planned extraction order):
  1. `spqr::util` (active)
  2. `spqr::kdf`
  3. `spqr::chain`
  4. `spqr::encoding`
  5. `spqr::authenticator`
  6. `spqr::serialize`
  7. `spqr::incremental_mlkem768`
  8. `spqr::v1`
  9. `spqr::proto`
- All commented out except `spqr::util` to start with the simplest module

### 4. Install Aeneas and attempt extraction
- Ran `npx aeneas-cli install` to build Aeneas locally in `.aeneas/`
- Ran `npx aeneas-cli extract` for each module

### 5. Extraction results (module by module)

| Module | Charon | Aeneas | Notes |
|--------|--------|--------|-------|
| `spqr::util` | OK | OK | Clean extraction |
| `spqr::kdf` | Hangs | - | Charon runs indefinitely |
| `spqr::chain` | Hangs | - | Charon runs indefinitely |
| `spqr::encoding` | OK | Partial | Funs.lean generated but 7 functions have `sorry` |
| `spqr::authenticator` | OK | ? | Currently active alongside util |
| `spqr::serialize` | Not tried | - | |
| `spqr::incremental_mlkem768` | Not tried | - | |
| `spqr::v1` | Not tried | - | |
| `spqr::proto` | Not tried | - | |

### 6. Current output (util + authenticator + encoding)
- `LeanOutput/Types.lean` - 267 lines, type definitions extracted cleanly
- `LeanOutput/Funs.lean` - 3807 lines, function definitions
- `LeanOutput/TypesExternal_Template.lean` - external type stubs
- `LeanOutput/FunsExternal_Template.lean` - external function stubs

### 7. Functions with `sorry` (Aeneas couldn't fully extract)
1. `cpufeatures` init_inner (external crate inline asm)
2. `GF16.div_impl` (GF16 division, src/encoding/gf.rs:548)
3. `Poly.compute_at` (polynomial evaluation, src/encoding/polynomial.rs:255)
4. `Poly.from_complete_points` (src/encoding/polynomial.rs:291)
5. `PolyEncoder.from_pb` (protobuf deserialization)
6. `PolyDecoder.from_pb` (protobuf deserialization)
7. `PolyDecoder.decoded_message` (src/encoding/polynomial.rs:883)

### Observations
- Charon hanging on `kdf` and `chain` may be due to heavy use of external crypto crates (hkdf, libcrux-hmac) pulling in large dependency graphs
- `sorry` functions tend to involve: loops with complex control flow, inline asm (cpufeatures), or iterator patterns
- The `encoding` module extracted the most code successfully since it's mostly pure math (GF16 arithmetic, polynomial ops)
