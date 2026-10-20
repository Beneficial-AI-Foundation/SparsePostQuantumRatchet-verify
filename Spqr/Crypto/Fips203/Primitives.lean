/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module
public import Spqr.Crypto.Fips203.Params
/-!
# FIPS 203 § 4.1: the symmetric primitives `G`, `H`, `J`, `PRF`, `XOF`

NIST FIPS 203 (ML-KEM, August 2024), § 4.1, builds ML-KEM on five symmetric primitives, all
instantiated from FIPS 202:

| name    | instantiation | input                     | output              |
|---------|---------------|---------------------------|---------------------|
| `G`     | SHA3-512      | arbitrary bytes           | 64 bytes            |
| `H`     | SHA3-256      | arbitrary bytes           | 32 bytes            |
| `J`     | SHAKE-256     | arbitrary bytes           | 32 bytes            |
| `PRF_η` | SHAKE-256     | 33 bytes `σ ‖ N`          | `64·η` bytes        |
| `XOF`   | SHAKE-128     | 34 bytes `ρ ‖ i ‖ j`      | unbounded stream    |

This development does **not** model Keccak.  Instead the five primitives are bundled into the
record `Primitives`, and every algorithm of FIPS 203 (`sampleNTT`, `kpkeKeyGen`, `kpkeEncrypt`,
`mlkemKeyGen`, `mlkemEncaps`, `mlkemDecaps`, …) takes a `prims : Primitives` argument.
Consequently every theorem proved about them (round-trip correctness, layout lemmas, the
incremental-encapsulation decomposition, …) is stated and proved for **every** instantiation of
the primitives — the statements quantify over `prims`, rather than referring to a fixed,
unspecified global oracle.

The design mirrors the parametrisation of other ML-KEM formalisations (e.g. VCVio's), so that a
future correspondence between this specification and another parametric one can be expressed by
instantiating both with the same (or provably related) record, instead of by postulating
equalities between opaque global constants.

## The concrete instantiation

The refinement of libcrux (`Spqr/Crypto/Fips203/Refinement/`, `SrcTranslated/FunsExternal.lean`)
models libcrux's `from_seed` / `encapsulate1` / `encapsulate2` / `decapsulate`, which use the
real SHA3/SHAKE.  Those models must be closed terms, so they are instantiated with
`stdPrimitives`, the single axiomatised constant of this file standing for the FIPS 202
instantiation.  Nothing is assumed about `stdPrimitives` beyond its type; this is the only
place where the hash functions are left uninterpreted.

**Source**: NIST FIPS 203, § 4.1
-/

@[expose] public section

namespace Fips203

/-- The symmetric primitives of ML-KEM (FIPS 203, § 4.1), abstracted as a record so that the
specification is parametric in their instantiation. -/
structure Primitives where
  /-- `G` — SHA3-512 in FIPS 203; 64 output bytes. -/
  G : List UInt8 → Fin 64 → UInt8
  /-- `H` — SHA3-256 in FIPS 203; 32 output bytes. -/
  H : List UInt8 → Fin 32 → UInt8
  /-- `J` — SHAKE-256 in FIPS 203; 32 output bytes. -/
  J : List UInt8 → Fin 32 → UInt8
  /-- `PRF_η(σ, N)` — SHAKE-256 in FIPS 203 on the 33-byte input `σ ‖ N`, modelled as an
  unbounded byte stream of which `SamplePolyCBD_η` reads the first `64·η` bytes.  The third
  argument is `η`. -/
  PRF : (Fin 32 → UInt8) → UInt8 → ℕ → ℕ → UInt8
  /-- `XOF` — SHAKE-128 in FIPS 203 on a 34-byte seed `ρ ‖ i ‖ j`, modelled as an unbounded
  byte stream consumed by `SampleNTT`. -/
  XOF : (Fin 34 → UInt8) → ℕ → UInt8
  deriving Inhabited

/-- The FIPS 202 instantiation of the primitives (SHA3-512, SHA3-256, SHAKE-256, SHAKE-128),
**axiomatised**: this constant is the model of the hash functions used by libcrux in the
refinement layer, and nothing beyond its type is assumed about it. -/
opaque stdPrimitives : Primitives

end Fips203
