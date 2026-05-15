# SPQR Correctness Properties: Lean Proofs via Aeneas Extraction

This directory organizes the correctness obligations of the SPQR protocol
according to the three-layer architecture of `mlkembraid.pdf`:

| File | Spec sections | Scope |
|------|--------------|-------|
| [1_scka_interface.md](1_scka_interface.md) | §1.1, §3.8 | SCKA-level goals + chain invariants |
| [2_incremental_kem.md](2_incremental_kem.md) | §1.2, §1.3 | KEM roundtrip, erasure coding, GF16 arithmetic |
| [3_protocol.md](3_protocol.md) | §2.2–§2.6 | Parameters, messages, authenticator, state machine, initialization, serialization |

Lean verification operates directly on the production codebase via Aeneas:
the extraction covers `chain.rs`, `authenticator.rs`, `v1/`, `encoding/`,
`incremental_mlkem768.rs`, and `kdf.rs`. Proofs target the shipped code,
but idioms like VecDeque, opaque HKDF, and Result-monadic WP reasoning
replace simpler annotation-based proof styles.

Each property is tagged with its **source** (see [Property Source Taxonomy](#property-source-taxonomy))
and its **status** (see [Status Legend](#status-legend)).

---

## Status Legend

| Tag | Meaning |
|-----|---------|
| ✅ PROVED | Lean theorem discharged (no sorry, no axiom dependency for the core claim) |
| ⚠️ FEASIBLE | Code is extracted; proof is tractable but not yet written |
| 🔶 AXIOM-BACKED | Proof depends on an explicit axiom (crypto modelling or opaque function) |
| 🚫 BLOCKED | Cannot be proved until an infrastructure issue is resolved |

---

## Aeneas Extraction Status

### What Is Extracted (available in `Spqr/Code/Funs.lean`)

| Module | Coverage | Notes |
|--------|----------|-------|
| `spqr::util` | Full | Clean extraction |
| `spqr::serialize` | Full | Clean extraction |
| `spqr::encoding` (GF16, polynomial) | Full | `mul2_u16`, `MulAssign<&GF16>`, `PolyDecoder::decoded_message` opaque via config |
| `spqr::incremental_mlkem768` | Partial | `encaps2` opaque via config (calls excluded `potentially_fix_state*` helper) |
| `spqr::proto` (protobuf types) | Full types | `Message` trait impls opaque; `merge` function bodies sorry'd |
| `spqr::kdf` | Partial | `hkdf_to_slice` opaque via config; `hkdf_to_vec` opaque via Rust annotation |
| `spqr::authenticator` | Full | All functions: `update`, `new`, `mac_ct/hdr`, `verify_ct/hdr` |
| `spqr::chain` | Full | `KeyHistory.*`, `ChainEpochDirection.*`, `Chain.*` including `into_pb`/`from_pb` |
| `spqr::v1` (chunked + unchunked) | Full | All state transitions, `States.send`, `States.recv` |
| `spqr::lib` (top-level `send`/`recv`) | **Not extracted** | `send`/`recv`/`initial_state` absent; not in `start_from` in `aeneas-config.yml` |

### Opaque Items (axiom stubs in `FunsExternal.lean`)

There are two sources of opacity, and they are **not the same set**:

1. **`aeneas-config.yml` `opaque:` list** — items the config forces to axiom stubs
   regardless of Rust annotations.
2. **`#[hax_lib::opaque]` Rust annotations** — items the Rust source marks opaque.

Some items have both; some have only one. Items with `#[hax_lib::opaque]` in Rust
but **not** in the config's `opaque:` list are extracted as full `def`s (the config
overrides the annotation). This is why `KeyHistory::get/gc` and `Chain::into_pb/from_pb`
are fully extracted despite their Rust annotations.

| Item | Opaque via | Lean representation |
|------|-----------|-------------------|
| `kdf::hkdf_to_slice` | Config + Rust annotation | `axiom kdf.hkdf_to_slice` |
| `kdf::hkdf_to_vec` | Rust annotation only | `axiom kdf.hkdf_to_vec` (wraps `hkdf_to_slice`) |
| `incremental_mlkem768::encaps2` | Config only | `axiom incremental_mlkem768.encaps2` |
| `encoding::gf::mul2_u16` | Config only | `axiom encoding.gf.mul2_u16` |
| `encoding::gf::MulAssign<&GF16>` | Config only | `axiom ...MulAssignShared0GF16.mul_assign` |
| `encoding::polynomial::PolyDecoder::decoded_message` | Config only | `axiom ...Decoder.decoded_message` |
| Proto `Message` impls | Config | Multiple `axiom`s for `encode_raw`, `merge_field`, etc. |

Total: ~100 axiom declarations in `FunsExternal.lean` (including std/core/prost/libcrux pieces).

### Sorry Budget

**`Spqr/Code/Funs.lean`** — 43 sorry instances:

| Category | Count | Impact |
|----------|-------|--------|
| `take := sorry` in `Iterator` trait instances | 2 | Low — `take` unused in proofs |
| `call_once := sorry` in FnOnce closure stubs | 18 | Low — closures unused in proofs |
| Proto enum `PartialOrd`/`Ord` method bodies | 16 | Low — proto comparison unused |
| Loop bodies sorry'd (complex Aeneas typing) | 4 | Medium — erasure-coding helpers |
| Proto `merge` function bodies | 3 | Medium — merge unused in core proofs |

None of these block the main protocol-level properties (PROP-1 through PROP-44).
The 4 sorry'd loop bodies block LEAN-ENC-2 (erasure-code roundtrip).

**`Spqr/Specs/`** — 3 sorry instances (all GF16 multiplication):

| File | Sorry'd item |
|------|-------------|
| `Encoding/Gf/Unaccelerated/Mul.lean` | `mul_spec'`, `mul_spec` |
| `Encoding/Gf/Reduce/PolyReduce.lean` | `poly_reduce_poly_mul_spec` |

---

## Property Source Taxonomy

| Tag | Meaning |
|-----|---------|
| `hax-kat` | Known-answer test in `signal-spqr-hax/tests/kat_vectors.rs` (toy model) |
| `hax-proptest` | Property test in `signal-spqr-hax/tests/proptest_equiv.rs` (empirical) |
| `hax-cross` | Cross-library test in `signal-spqr-hax/tests/cross_lib.rs` |
| `production-test` | Test in `src/test/` suite or inline `#[cfg(test)]` modules |
| `production-code` | Runtime assertion or guard in the production code |
| `spec-mlkembraid` | Derived from `mlkembraid.pdf` |
| `spec-2025-2267` | Derived from the SCKA security framework paper |
| `lean-specific` | Identified during Lean extraction/proof work |

### Evidence Strength Scale

1. **Lean theorem over extracted production code** (strongest)
2. **Production code guard/invariant** (`assert!`, explicit `Err` branch)
3. **Production tests / upstream interop tests**
4. **Cross-library and proptest results** (empirical, non-exhaustive)
5. **Toy-model KAT evidence** (`ToySpqr`)
6. **Spec citation only** (normative target, not implementation evidence)

---

## Lean-Specific Proof Context

### WP (weakest precondition) style

All Aeneas-extracted functions live in the `Result` monad. Postcondition
theorems use the WP operator `⦃ result => P result ⦄`:

```lean
theorem add_epoch_spec (c : chain.Chain) (es : EpochSecret)
    (h : es.epoch = c.current_epoch + 1) :
    chain.Chain.add_epoch c es ⦃ c' =>
      c'.current_epoch = es.epoch ⦄ := by ...
```

### Mathlib Integration

`Spqr/Math/Basic.lean` defines `abbrev GF216 := GaloisField 2 16` and connects
the extracted GF16 arithmetic to Mathlib's algebraic hierarchy.

### Liveness Axioms (`Spqr/Specs/External.lean`)

The proof files use a structured axiom approach with two categories:

1. **Opaque function axioms** — for functions with no Lean definition
   (e.g., `kdf.hkdf_to_slice_spec`, `VecDeque.push_back_spec`).
2. **Deep defined function axioms** — pragmatic shortcuts for functions with
   long call chains where the postcondition does not depend on their output
   (e.g., `PolyEncoder.next_chunk_spec`, `KeysUnsampled.send_hdr_chunk_spec`,
   `HeaderReceived.send_ct1_chunk_spec`).

---

## Axiom-Set Coherence

The Lean development relies on these axiom families:

1. **HKDF axioms:** `hkdf_to_slice_deterministic`, `hkdf_to_slice_succeeds`
   (PROP-18), `hkdf_no_collision_modelling_assumption` (PROP-4).
2. **KEM axioms:** `kem_roundtrip` with `(dk, ek_seed, ek_vector) = generate(seed)`
   binding (PROP-3).
3. **SHA3 axiom:** `validate_pk_bytes` spec equivalence (PROP-3b).
4. **Opaque function stubs** in `FunsExternal.lean`.

The PROP-4/7/8/24b modelling assumptions adopt *collision infeasibility* for HKDF,
which is standard in symbolic (Dolev-Yao) models but technically inconsistent
with HKDF's PRF nature. These must be kept strictly separated (in a dedicated
axiom file) and clearly labeled as cryptographic modelling assumptions.

---

## Blockers

| Blocker | Impact | Fix |
|---------|--------|-----|
| `lib.rs` not in `start_from` | PROP-1 (API level), PROP-16, PROP-27 blocked | Add `"spqr"` to `start_from` in `aeneas-config.yml` |
| `encaps2` opaque (config) | PROP-3 must be axiom, not theorem | Fix `potentially_fix_state*` helper opacity |
| `hkdf_to_slice` opaque (config + Rust) | HKDF proofs need axioms | Create `#[cfg(hax)]` wrapper or accept permanent axiom set |
| GF16 sorry chain (3 sorries) | LEAN-GF-6, LEAN-GF-7 blocked | Close `poly_reduce_spec` → `mul_spec` chain |

---

## Master Cross-Reference Table

| PROP | Statement (short) | Spec § | File | Status |
|------|-------------------|--------|------|--------|
| PROP-1 | Session key consistency | §1.1 | [1_scka](1_scka_interface.md) | 🚫 blocked (lib.rs) / ⚠️ feasible (v1 layer) |
| PROP-3 | KEM roundtrip | §1.2 | [2_kem](2_incremental_kem.md) | 🔶 axiom |
| PROP-3b | EK header SHA3 binding | §1.2 | [2_kem](2_incremental_kem.md) | 🔶 axiom |
| PROP-4 | KDF domain separation | §2.2 | [3_proto](3_protocol.md) | 🔶 modelling assumption |
| PROP-7 | Chain advancement | §2.2 | [3_proto](3_protocol.md) | 🔶 modelling assumption |
| PROP-8 | Root key ratchet | §2.2 | [3_proto](3_protocol.md) | 🔶 modelling assumption |
| PROP-9 | Epoch monotonicity | §1.1 | [1_scka](1_scka_interface.md) | ✅ proved |
| PROP-10 | Structural key erasure | §1.1 | [1_scka](1_scka_interface.md) | ⚠️ feasible |
| PROP-12a | KeyHistory length invariant | §1.1 | [1_scka](1_scka_interface.md) | ⚠️ feasible |
| PROP-12b | KeyHistory get-after-add | §1.1 | [1_scka](1_scka_interface.md) | ⚠️ feasible (unblocked) |
| PROP-14 | Send epoch guard | §1.1 | [1_scka](1_scka_interface.md) | ✅ proved |
| PROP-15 | MAC-ct roundtrip | §2.4 | [3_proto](3_protocol.md) | ⚠️ feasible |
| PROP-15b | MAC-hdr roundtrip | §2.4 | [3_proto](3_protocol.md) | ⚠️ feasible |
| PROP-16 | Version negotiation | §2.6 | [3_proto](3_protocol.md) | 🚫 blocked (lib.rs) |
| PROP-17 | Key jump guard | §1.1 | [1_scka](1_scka_interface.md) | ✅ proved |
| PROP-17b | Key already requested | §1.1 | [1_scka](1_scka_interface.md) | ✅ proved |
| PROP-18 | HKDF expand safety | §2.2 | [3_proto](3_protocol.md) | 🔶 axiom |
| PROP-21 | Only two transitions emit key | §2.5 | [1_scka](1_scka_interface.md) / [3_proto](3_protocol.md) | ✅ proved |
| PROP-22a | Send output reflects state epoch | §1.1 | [1_scka](1_scka_interface.md) | ⚠️ feasible |
| PROP-22b | Recv success epoch discipline | §1.1 | [1_scka](1_scka_interface.md) | ⚠️ feasible |
| PROP-23 | Sender/receiver epoch knowledge | §1.1 | [1_scka](1_scka_interface.md) | ⚠️ feasible |
| PROP-24a | KDF_OK structural | §2.2 | [3_proto](3_protocol.md) | ⚠️ feasible |
| PROP-24b | KDF_OK epoch binding | §2.2 | [3_proto](3_protocol.md) | 🔶 modelling assumption |
| PROP-25 | EK integrity verification | §2.5 | [3_proto](3_protocol.md) | ⚠️ feasible |
| PROP-26 | Ct2Sampled epoch guard | §2.5 | [3_proto](3_protocol.md) | ✅ proved |
| PROP-27 | Initialization correctness | §2.6 | [3_proto](3_protocol.md) | 🚫 blocked (lib.rs) |
| PROP-29 | `epoch_idx` correspondence | §1.1 | [1_scka](1_scka_interface.md) | ⚠️ feasible |
| PROP-30 | Less-branch no-op | §2.5 | [3_proto](3_protocol.md) | ✅ proved |
| PROP-31 | Authenticator Init ≡ zero+update | §2.4 | [3_proto](3_protocol.md) | ⚠️ feasible |
| PROP-32 | Authenticator update derivation | §2.4 | [3_proto](3_protocol.md) | ⚠️ feasible |
| PROP-33 | Deviation: Ct1Ack emission | §2.5 | [3_proto](3_protocol.md) | ✅ proved |
| PROP-34 | Deviation: Ct1Ack acceptance | §2.5 | [3_proto](3_protocol.md) | ⚠️ feasible |
| PROP-35 | Wire-format roundtrip | §2.3 | [3_proto](3_protocol.md) | ⚠️ feasible |
| PROP-36 | Epoch-zero rejection | §2.3 | [3_proto](3_protocol.md) | ⚠️ feasible |
| PROP-37 | Protobuf state roundtrip | §2.3 | [3_proto](3_protocol.md) | ⚠️ feasible |
| PROP-38 | Chain protobuf roundtrip | §2.3 | [3_proto](3_protocol.md) | ⚠️ feasible (unblocked) |
| PROP-39 | Greater-branch EpochOutOfRange | §2.5 | [3_proto](3_protocol.md) | ✅ proved |
| PROP-40a | MAC-hdr input byte-form | §2.4 | [3_proto](3_protocol.md) | ⚠️ feasible |
| PROP-40b | MAC-ct input byte-form | §2.4 | [3_proto](3_protocol.md) | ⚠️ feasible |
| PROP-41 | PROTOCOL_INFO bytes | §2.2 | [3_proto](3_protocol.md) | ⚠️ feasible |
| PROP-42 | KDF_AUTH info-string | §2.2 | [3_proto](3_protocol.md) | ⚠️ feasible |
| PROP-43 | MAC failure state preservation | §2.4 | [3_proto](3_protocol.md) | ⚠️ feasible |
| PROP-44 | Deviation: Ek chunk acceptance | §2.5 | [3_proto](3_protocol.md) | ⚠️ feasible |
| LEAN-GF-1..5 | GF16 add/sub/eq/mul loop | §1.3 | [2_kem](2_incremental_kem.md) | ✅ proved |
| LEAN-GF-6 | GF16 polynomial reduction | §1.3 | [2_kem](2_incremental_kem.md) | ⚠️ partial (3 sorries) |
| LEAN-GF-7 | GF16 multiplication e2e | §1.3 | [2_kem](2_incremental_kem.md) | 🚫 blocked (LEAN-GF-6) |
| LEAN-ENC-1 | Pt serialize/deserialize | §1.3 | [2_kem](2_incremental_kem.md) | ✅ proved |
| LEAN-ENC-2 | PolyDecoder full decode | §1.3 | [2_kem](2_incremental_kem.md) | 🚫 blocked (opaque) |

---

## Priority Ranking

### Already proved

LEAN-GF-1..5, LEAN-ENC-1, PROP-9, PROP-14, PROP-17, PROP-17b, PROP-21,
PROP-26, PROP-30, PROP-33, PROP-39.

### Phase 1: Next Tier-1 proofs (~10 days, no axioms needed)

PROP-29 (epoch_idx), PROP-31 (Authenticator Init), PROP-32 (Authenticator
update), PROP-15/15b (MAC roundtrip), PROP-40a/b (MAC byte-form), PROP-25
(EK integrity), PROP-22a/b (epoch agreement), PROP-34 (deviation: Ct1Ack
acceptance), PROP-44 (deviation: Ek acceptance), PROP-43 (MAC failure
preservation), PROP-12a (KeyHistory structural), PROP-36 (epoch-zero
rejection), PROP-41 (PROTOCOL_INFO bytes).

### Phase 2: Newly unblocked properties (~6 days)

PROP-12b (KeyHistory get-after-add — was blocked, now feasible), PROP-38
(Chain protobuf roundtrip — was blocked, now feasible).

### Phase 3: Axiom-backed protocol properties (~7 days)

PROP-3 + PROP-3b (KEM axioms), PROP-18 (HKDF safety), PROP-24a/b (KDF_OK),
PROP-42 (KDF_AUTH info-string), PROP-10 (structural erasure).

### Phase 4: SCKA correspondence (~4 days)

PROP-23 (sender/receiver epoch knowledge).

### Phase 5: Serialization layer (~6 days)

PROP-37 (States protobuf roundtrip), PROP-35 (wire-format roundtrip).

### Phase 6: Close GF16 sorries (~5 days)

LEAN-GF-6 (polynomial reduction), LEAN-GF-7 (multiplication end-to-end).

### Phase 7: Infrastructure + top-level API (~9 days)

Extract `lib.rs`, then: PROP-1 (chain key agreement at v1 layer), PROP-27
(initialization), PROP-16 (version negotiation).

---

## Proof Files

| File | Proved theorems |
|------|----------------|
| `Spqr/Specs/Chain/AddEpoch.lean` | PROP-9 (+ helpers: Direction.switch, KeyHistory.KEY_SIZE/new, ChainEpochDirection.new, Chain.ced_for_direction) |
| `Spqr/Specs/Chain/SendKey.lean` | PROP-14 |
| `Spqr/Specs/Chain/Key.lean` | PROP-17, PROP-17b (+ OrdU32.cmp helper) |
| `Spqr/Specs/States/Send.lean` | PROP-33, PROP-21 (all 11 variants) |
| `Spqr/Specs/States/Recv.lean` | PROP-26, PROP-39 (10 variants), PROP-30 (11 variants) |
| `Spqr/Specs/External.lean` | Liveness axioms (opaque + deep-defined) |
| `Spqr/Specs/Encoding/Gf/GF16/AddAssign.lean` | LEAN-GF-1 (`add_assign_spec`) |
| `Spqr/Specs/Encoding/Gf/GF16/Add.lean` | LEAN-GF-2 (`add_spec`) |
| `Spqr/Specs/Encoding/Gf/GF16/Sub.lean` | LEAN-GF-3 (`sub_spec`) |
| `Spqr/Specs/Encoding/Gf/GF16/Eq.lean` | LEAN-GF-4 (`eq_spec`, `gf16_eq_iff`) |
| `Spqr/Specs/Encoding/Gf/Unaccelerated/PolyMul.lean` | LEAN-GF-5 (`poly_mul_loop_spec`, `poly_mul_spec`, `clmul_eq_clmul_poly`, `clmul_poly_eq_mul`) |
| `Spqr/Specs/Encoding/Gf/Unaccelerated/Mul.lean` | LEAN-GF-7 partial (`mul_spec` — 2 sorries) |
| `Spqr/Specs/Encoding/Gf/Reduce/PolyReduce.lean` | LEAN-GF-6 partial (`poly_reduce_spec` — 1 sorry) |
| `Spqr/Specs/Encoding/Polynomial/Pt/Serialize.lean` | LEAN-ENC-1 part (`serialize_spec`, `to_be_bytes_spec`) |
| `Spqr/Specs/Encoding/Polynomial/Pt/Deserialize.lean` | LEAN-ENC-1 part (`deserialize_spec`, `from_be_bytes_spec`, `try_from_spec`) |
