# SPQR Correctness Properties: Lean Proofs via Aeneas Extraction

## Purpose

This document inventories the meaningful correctness obligations of the SPQR protocol, and
separates them from explicit modelling assumptions, deviation sentinels, and proof
infrastructure. Each item is mapped to the Aeneas-extracted Lean code in `Spqr/Code/Funs.lean`
and `Spqr/Code/Types.lean`, with an assessment of whether and how it can be proven in Lean
given the current extraction state.

Lean verification operates directly on the production codebase via Aeneas: the extraction
covers `chain.rs`, `authenticator.rs`, `v1/`, and `incremental_mlkem768.rs`. This is a
strength (proofs target the shipped code) but also shifts the complexity: idioms like
VecDeque, opaque HKDF, and Result-monadic WP reasoning replace simpler annotation-based
proof styles.

Each property is tagged with its **source** — how the property was identified and where it
is already expressed in the codebase. See [Property Source Taxonomy](#property-source-taxonomy)
for the classification.

---

## Aeneas Extraction Status

### What Is Extracted (available in `Spqr/Code/Funs.lean`)

| Module | Coverage | Notes |
|--------|----------|-------|
| `spqr::util` | Full | Clean extraction |
| `spqr::serialize` | Full | Clean extraction |
| `spqr::encoding` (GF16, polynomial) | Full | `mul2_u16`, `MulAssign<&GF16>`, `PolyDecoder::decoded_message` opaque |
| `spqr::incremental_mlkem768` | Partial | `encaps2` opaque (calls `#[hax_lib::opaque]` helper `potentially_fix_state*` which contains `log::*` macros under `#[cfg(not(hax))]`) |
| `spqr::proto` (protobuf types) | Full types | `Message` trait impls opaque; `merge` function bodies sorry'd |
| `spqr::kdf` | Partial | `hkdf_to_slice` opaque (HKDF/SHA2 deep generics); `hkdf_to_vec` extracted |
| `spqr::authenticator` | Full | All functions: `update`, `new`, `mac_ct/hdr`, `verify_ct/hdr` |
| `spqr::chain` | Full | `KeyHistory.*`, `ChainEpochDirection.*`, `Chain.*` |
| `spqr::v1` (chunked + unchunked) | Full | All state transitions, `States.send`, `States.recv` |
| `spqr::lib` (top-level `send`/`recv`) | **Top-level API not extracted** | `send`/`recv`/`initial_state` absent; some types/impls (`Direction.switch`, `Error` conversions) pulled in transitively. Not in `start_from` in `aeneas-config.yml`. |

### Opaque Items (axiom stubs in Lean)

Opaque Rust items are represented as `axiom` declarations in `Spqr/Code/FunsExternal.lean`
(not Lean `opaque` definitions — the distinction matters for consistency reasoning).

| Item | Reason | Lean representation |
|------|--------|-------------------|
| `kdf::hkdf_to_slice` | Deep HKDF/SHA2 generic traits | `axiom kdf.hkdf_to_slice` in `FunsExternal.lean` |
| `incremental_mlkem768::encaps2` | Calls `potentially_fix_state*` which is `#[hax_lib::opaque]` (contains `log::*` under `#[cfg(not(hax))]`) | `axiom incremental_mlkem768.encaps2` in `FunsExternal.lean` |
| `encoding::gf::mul2_u16` | Dispatches to excluded SIMD intrinsics | `axiom encoding.gf.mul2_u16` in `FunsExternal.lean` |
| `encoding::gf::MulAssign<&GF16> for GF16` | Same dispatch | `axiom ...MulAssignShared0GF16.mul_assign` in `FunsExternal.lean` |
| `encoding::polynomial::PolyDecoder::decoded_message` | Aeneas internal error | `axiom ...Decoder.decoded_message` in `FunsExternal.lean` |
| Proto `Message` impls | Prost internals | Multiple `axiom`s for `encode_raw`, `merge_field`, etc. in `FunsExternal.lean` |

### Sorry Budget in Generated Code (`Spqr/Code/Funs.lean`)

43 sorry instances total, grouped by category:

| Category | Count | Impact |
|----------|-------|--------|
| `take := sorry` in `Iterator` trait instances | 2 | Low — `take` unused in proofs |
| `call_once := sorry` in FnOnce closure stubs | 18 | Low — closures unused in proofs |
| Proto enum `PartialOrd`/`Ord` method bodies (`partial_cmp`, `lt`/`le`/`gt`/`ge`, `max`/`min`/`clamp`) | 16 | Low — proto comparison unused |
| Loop bodies sorry'd (complex Aeneas typing) | 4 | Medium — `parallel_mult_loop`, `lagrange_polys_for_complete_points_loop0`, `PolyEncoder::from_pb_loop1`, `PolyEncoder::encode_bytes_base_loop` |
| Proto `merge` function bodies | 3 | Medium — merge unused in core proofs |

None of these sorry's block the main cryptographic property proofs (PROP-1 through PROP-44).
The 4 sorry'd loop bodies are in erasure-coding helpers that are not on the critical path
for protocol correctness. However, these loop-body sorries **do** block LEAN-ENC-2 (full
erasure-code roundtrip) and any proof that needs to reason about polynomial encoding/decoding
internals. Any theorem whose proof path flows through a sorry'd definition is unsound until
that sorry is closed.

### Sorry Budget in Proof Files (`Spqr/Specs/`)

| File | Sorry'd theorem | Gap description |
|------|----------------|----------------|
| `Encoding/Gf/Unaccelerated/Mul.lean` | `mul_spec` | Full GF16 mul correctness (compose poly_mul + poly_reduce) |
| `Encoding/Gf/Reduce/PolyReduce.lean` | `poly_reduce_spec` | Table-based reduction ≡ bit-level `polyMod` |
| `Encoding/Gf/Reduce/PolyReduce.lean` | `polyMod_eq_polyMod_poly` | `polyMod` (Nat) ↔ `polyMod_poly` (GF2[X]) |
| `Encoding/Gf/Reduce/PolyReduce.lean` | `polyMod_poly_eq_modByMonic` | `polyMod_poly p n = p %ₘ POLY_GF2` |

These 4 sorries all concern GF16 multiplication correctness. Everything else in Specs is fully
closed.

---

## Lean-Specific Proof Context

### WP (weakest precondition) style

All Aeneas-extracted functions live in the `Result` monad. Postcondition theorems use the WP
operator `⦃ result => P result ⦄`:

```lean
theorem add_epoch_monotone (c : chain.Chain) (es : EpochSecret)
    (h : es.epoch = c.current_epoch + 1) :
    chain.Chain.add_epoch c es ⦃ result =>
      result.current_epoch = c.current_epoch + 1 ⦄ := by ...
```

### Mathlib Integration

`Spqr/Math/Basic.lean` defines `abbrev GF216 := GaloisField 2 16` and connects the extracted GF16
arithmetic to Mathlib's algebraic hierarchy. The proven `add_assign_spec` and `sub_spec` already
express their results in terms of `GF216` field arithmetic.

### Axioms for Opaque Functions

For functions that are opaque in the extraction (represented as `axiom` stubs in
`FunsExternal.lean`), Lean proofs must introduce additional `@[step]` axioms to reason
about their behavior:

```lean
-- Axiom: HKDF-SHA256 with same inputs yields same output
axiom hkdf_to_slice_deterministic (salt ikm info : Slice U8) (len : Usize) :
    kdf.hkdf_to_slice salt ikm info len ⦃ result1 =>
    kdf.hkdf_to_slice salt ikm info len ⦃ result2 =>
      result1 = result2 ⦄ ⦄ := ...
```

---

## Property Source Taxonomy

Each property is annotated with one or more source tags indicating how it was identified:

| Tag | Meaning |
|-----|---------|
| `hax-kat` | Known-answer test in `signal-spqr-hax/tests/kat_vectors.rs`. All KATs run over `ToySpqr` (the file is gated on `#[cfg(feature = "kani-proofs")]`) and pin specific input/output bytes. |
| `hax-proptest` | Property test in `signal-spqr-hax/tests/proptest_equiv.rs`. Tests `HkdfSpqr` (real HKDF-SHA256 + toy KEM) over random sampling — empirical, not exhaustive. |
| `hax-cross` | Cross-library test in `signal-spqr-hax/tests/cross_lib.rs` against the `ml-kem`, `hkdf`, `sha2` crates and (under `--features upstream-spqr`) the production `signalapp/sparsepostquantumratchet` crate. Note: `cross_spqr_protocol_with_hkdf_kdf` uses `HkdfSpqr` (real HKDF-SHA256 KDF but toy KEM/encrypt), not full production crypto. |
| `production-test` | Property is tested in the SPQR `src/test/` suite or inline `#[cfg(test)]` modules in `chain.rs`, `lib.rs`, etc. |
| `production-code` | Property is visible as a runtime assertion or guard in the production code itself (e.g., `assert!`, error-return branches) |
| `production-comment` | Property is documented in code comments but not explicitly tested or asserted |
| `spec-mlkembraid` | Property derives from the ML-KEM Braid protocol specification (`mlkembraid.pdf`, Rolfe Schmidt). Section references (§1.1, §2.x, §3.x) refer to this document. |
| `spec-2025-2267` | Property derives from the SCKA security framework paper (`2025-2267.pdf`, Auerbach et al.). Covers formal security definitions, vulnerable message sets, and the SCKA model — higher-level than the protocol spec. |
| `lean-specific` | Property was identified during Lean extraction/proof work (not present in other property catalogs) |

Multiple sources can apply to a single property.

### Evidence Strength Scale (for triage)

To avoid over-weighting toy-model evidence, each property should be read with the
following evidence-strength ordering:

1. **Lean theorem over extracted production code** (strongest within this artifact).
2. **Production code guard/invariant** (`assert!`, explicit `Err` branch).
3. **Production tests / upstream interop tests** (strong regression signal, not proof).
4. **Cross-library and proptest results** (empirical coverage, non-exhaustive).
5. **Toy-model KAT evidence** (`ToySpqr`) — useful for scaffolding shape only.
6. **Spec citation only** (normative target, not implementation evidence).

When a property depends on opaque functions or cryptographic collision assumptions,
it must be explicitly labeled as such even if it has strong test evidence.

**Inclusion rule for `hax-*` evidence.** We keep `hax-*`-derived properties in the
main SPQR correctness set only when the stated obligation still targets
production SPQR behaviour (same API-level semantics, guards, or invariants). If a
`hax-*` property is about toy-only operations (`ToySpqr` encrypt/decrypt, XOR KEM,
or fixed-size abstraction artefacts), it is excluded from the production
correctness set.

### Correctness Taxonomy

The correctness set is split into:

- **Core correctness properties:** PROP-9, PROP-14, PROP-17, PROP-17b, PROP-21, PROP-22a,
  PROP-22b, PROP-25, PROP-26, PROP-29, PROP-30, PROP-31, PROP-32, PROP-36, PROP-10
  (structural erasure only), PROP-12a, PROP-12b, PROP-15, PROP-15b, PROP-35, PROP-37,
  PROP-38, PROP-39, PROP-40a, PROP-40b, PROP-43.
- **Blocked top-level API goals:** PROP-1, PROP-16, PROP-27.
- **Axiom-backed proof goals:** PROP-3, PROP-3b, PROP-18, PROP-24a.
- **Spec correspondence / constant checks:** PROP-41, PROP-42.
- **Explicit modelling assumptions used by proofs, but not counted as correctness properties:**
  PROP-4, PROP-7, PROP-8, PROP-24b.
- **Deviation sentinels:** PROP-33, PROP-34, PROP-39 (also a core property), PROP-44.
- **Proof infrastructure / open proof work:** LEAN-GF-6, LEAN-GF-7, LEAN-ENC-2.

---

## Property Catalog: Lean Assessment

PROP identifiers are intentionally non-contiguous and are used as
cross-reference handles.

### Encoding Layer: GF16 Field Arithmetic & Erasure Coding

Source: `lean-specific` — all properties identified during Lean extraction and proof work.

**Already proved** (see [Appendix: Proved Properties](#appendix-proved-properties) for details):
LEAN-GF-1 (add), LEAN-GF-2 (add by value), LEAN-GF-3 (sub), LEAN-GF-4 (eq),
LEAN-GF-5 (carry-less mul loop), LEAN-ENC-1 (Pt serialize/deserialize roundtrip).

#### LEAN-GF-6: GF16 Polynomial Reduction [OPEN]

**Status:** ⚠️ **PARTIAL** — spec structure defined, 3 sorries remain.

- `poly_reduce_spec`: table-based reduction ≡ spec-level `polyMod` — **sorry**
- `polyMod_eq_polyMod_poly`: Nat ↔ GF2[X] correspondence — **sorry**
- `polyMod_poly_eq_modByMonic`: `polyMod_poly p n = p %ₘ POLY_GF2` — **sorry**

The mathematical framework is in place (definitions of `polyMod`, `reduceFromByte`,
`POLY_GF2`, `polyMod_poly`). The remaining work is connecting the precomputed `REDUCE_BYTES`
table to the recursive spec.

#### LEAN-GF-7: GF16 Multiplication End-to-End [OPEN]

**Status:** ⚠️ **BLOCKED by LEAN-GF-6** — `mul_spec` has one sorry, awaiting `poly_reduce_spec`.

#### LEAN-GF-8: GF16 MulAssign [FOLDED INTO LEAN-GF-7]

**Status:** 🔁 **NOT A STANDALONE OBLIGATION.** This is one-line axiomatic glue
(`(a *= b).value = mul(a.value, b.value)`) connecting the opaque
`MulAssign<&GF16>` instance to the proven `mul_spec`. It's best treated as a
single `axiom` line within the LEAN-GF-7 development.

#### LEAN-ENC-2: PolyDecoder Full Decode [BLOCKED]

**Status:** 🚫 **OPAQUE** — `PolyDecoder::decoded_message` is opaque. The full erasure-code
decoding roundtrip (encode then decode recovers message) cannot be proven without an axiom
for `decoded_message`.

---

### PROP-1: Chain Key Agreement [CORRESPONDENCE PROPERTY]

**Source:** `production-test` (`directions_match` in `chain.rs:464`, `ratchet` and
`lockstep_run_with_logging` in `lib.rs`, orchestrator key-history checks) +
`spec-mlkembraid` (§1.1: session key consistency — "if ep = ep' then k = k'").

*Alice's send chain matches Bob's recv chain after protocol execution.*

**Available in Lean extraction:**

- `chain.Chain.send_key` — extracted (`Funs.lean:6278`)
- `chain.Chain.recv_key` — extracted (`Funs.lean:6323`)
- `v1.chunked.states.States.send` — extracted (`Funs.lean:13897`)
- `v1.chunked.states.States.recv` — extracted (`Funs.lean:14019`)
- `lib.rs` top-level `send`/`recv` — **NOT extracted**

**Lean provability:**

| Aspect | Assessment |
|--------|------------|
| **Difficulty** | Hard |
| **Lean encoding** | Relational `theorem` taking both parties' post-states and proving `send_key epoch = recv_key epoch`, given shared `EpochSecret` input. Uses `⦃ result => ... ⦄` WP postconditions. |
| **Within v1 state machine** | `States.send` and `States.recv` ARE available. Agreement can be stated at the `EpochSecret` layer: when both parties process a completed epoch, their `EpochSecret.secret` fields are equal (since both run `encaps1`/`decaps` with the same ciphertext). |
| **Top-level API** | Blocked — `lib.rs` send/recv not extracted. Would require extending `start_from` in `aeneas-config.yml`. |
| **Key axioms needed** | KEM roundtrip axiom for `encaps1`/`encaps2`/`decaps` (PROP-3), HKDF determinism axiom for `hkdf_to_slice`, `encaps2` roundtrip axiom |
| **Status** | ⚠️ **FEASIBLE WITHIN v1 LAYER** — blocked at top-level API; requires axioms |
| **Estimated effort** | 5-7 days |

### PROP-3: KEM Roundtrip [ALGEBRAIC SPECIFICATION]

**Source:** `hax-cross`
(`cross_mlkem768_roundtrip`, `cross_mlkem768_multiple_roundtrips` in
`signal-spqr-hax/tests/cross_lib.rs:31,40`) +
`production-test` (`incremental_mlkem768_round_trip` in
`src/incremental_mlkem768.rs:178`).

*Given `(dk, ek_seed, ek_vector) = generate(seed)`, the chain
`encaps1` → `encaps2` → `decaps` preserves the shared secret.*

**Why the binding matters.** A naïve formulation
`encaps1(hdr) = ok (es, ct1, ss) ∧ encaps2(es, ek) = ok ct2 → decaps(dk, ct1, ct2) = ok ss`
is **underspecified**: it does not constrain how `dk`, `ek`, and `hdr` relate.
A consistent KEM roundtrip requires all three to come from the same `generate`
call and the header to match the spec construction
`hdr = ek_seed || SHA3-256(ek_seed || ek_vector)`. The axiom must say so
explicitly, otherwise it can be instantiated with mismatched `dk`/`ek` and is
either vacuous or wrong.

**Available in Lean extraction:**

- `incremental_mlkem768.generate` — extracted
- `incremental_mlkem768.encaps1` — extracted
- `incremental_mlkem768.decaps` — extracted
- `incremental_mlkem768.encaps2` — **OPAQUE** (see Blocker 2)

**Lean provability:**

| Aspect | Assessment |
|--------|------------|
| **Difficulty** | Axiom-only |
| **Axiom form** | `axiom kem_roundtrip (rng_seed : RngSeed) : let (dk, ek_seed, ek_vec) := incremental_mlkem768.generate rng_seed; let hdr := ek_seed ++ sha3_256 (ek_seed ++ ek_vec); let ek  := ek_seed ++ ek_vec; ∀ enc_seed, encaps1 hdr enc_seed = ok (es, ct1, ss) → encaps2 es ek = ok ct2 → decaps dk ct1 ct2 = ok ss` |
| **What this rules out** | Mismatched `dk`/`ek` (different generate calls), tampered headers, header without the SHA3-256 binding, all of which would otherwise satisfy the old underspecified axiom vacuously. |
| **Status** | 🔶 **AXIOM REQUIRED** — `encaps2` opaque; roundtrip must be asserted as an axiom |
| **Estimated effort** | 0.5 days (axiom statement, with binding) |

**Companion property PROP-3b: EK header binding** — verify that
`incremental_mlkem768::ek_matches_header(ek, hdr)` is equivalent to the spec's
`hdr[32..64] = SHA3-256(hdr[0..32] || ek)`. The Rust code delegates to
`libcrux_ml_kem::mlkem768::incremental::validate_pk_bytes` (`src/incremental_mlkem768.rs:28-30`)
which is opaque from this codebase's perspective. This property must therefore
also be axiomatised, with a clear statement that we are taking libcrux's check
on faith. Effort: 0.5 days (axiom statement). See also §3.7 / spec §2.5.

**To replace the axiom with a theorem:** the `potentially_fix_state*` helper
that `encaps2` calls needs to be made transparent to Aeneas. The helper is
`#[hax_lib::opaque]` because it contains `log::*` macros under `#[cfg(not(hax))]`.
Providing a `#[cfg(hax)]` alternative of the helper (without logging) or
removing `#[hax_lib::opaque]` and gating the log calls would allow Aeneas to
extract the full `encaps2` body. The axiom approach is the interim.

---

### PROP-4: KDF Domain Separation [ALGEBRAIC SPECIFICATION — modelling assumption]

**Source:** `hax-cross`
(`cross_hkdf_domain_separation`, `tests/cross_lib.rs:245`) +
`production-code` (distinct HKDF info strings in `chain.rs:237,334,360`).

*Outputs of HKDF derived under different `info` labels behave as
domain-separated (different one-time keys).*

**⚠ Soundness flag.** A naïve Lean axiom of the form
`info₁ ≠ info₂ → hkdf salt ikm info₁ len = ok r₁ → hkdf salt ikm info₂ len = ok r₂ → r₁ ≠ r₂`
would assert that **HKDF is injective in `info`**, which is **false** as a
property of HKDF: HKDF is a pseudo-random function, and any PRF can have
collisions with negligible-but-nonzero probability. Adopting strict-inequality
as a Lean `axiom` therefore introduces an unsound assumption.

The `ToySpqr` KAT `kdf_rk_domain_separation` (in `signal-spqr-hax`) verifies
the strict-inequality form, but only because `ToySpqr::kdf_rk` is
`xor(root, CONST_R) || xor(root, CONST_C)` for two distinct public constants —
strict injectivity is structural there, not a property of HKDF.

**Sound replacements (choose one):**

1. **Modelling cheat (recommended for now).** Axiomatise an
   *"infeasibility of finding a collision"* postulate scoped to call sites.
   At every protocol call site we show the `(salt, ikm, info)` triples are
   syntactically distinct and postpone the cryptographic argument:

   ```
   axiom hkdf_no_collision_modelling_assumption :
       ∀ (s₁ s₂ i₁ i₂ inf₁ inf₂ len),
       (s₁, i₁, inf₁) ≠ (s₂, i₂, inf₂) →
       hkdf_to_slice s₁ i₁ inf₁ len = ok r₁ →
       hkdf_to_slice s₂ i₂ inf₂ len = ok r₂ →
       r₁ ≠ r₂
   ```

   This **must** be flagged as a cryptographic-modelling assumption, not a
   theorem, with a comment that it is technically inconsistent with HKDF's
   PRF nature in the same way that "PRF outputs are unpredictable" is
   inconsistent with HMAC's deterministic mathematical structure.

2. **Game-style axiom.** State the property as
   `Pr[hkdf collision] ≤ negl(λ)` using a probabilistic relation. Closer to
   the truth, but harder to use mechanically in Lean.

**Lean provability:**

| Aspect | Assessment |
|--------|------------|
| **Difficulty** | Axiom-dependent + **soundness disclaimer required** |
| **Status** | 🔶 **AXIOM REQUIRED, EXPLICITLY UNSOUND IN A CRYPTOGRAPHIC MODEL** — discharge under modelling assumption (1) above. |
| **Estimated effort** | 1 day (axiom statement + call-site distinctness checks). |

### PROP-7: Chain Advancement [PROGRESS / INJECTIVITY — modelling assumption]

**Source:** `hax-cross`
(`cross_hkdf_chain_advancement`, `tests/cross_lib.rs:128`) + `production-test`
(`directions_match`, orchestrator tests with 10k+ distinct keys).

*Successive chain keys are distinct (distinct counter inputs ⇒ distinct outputs).*

**⚠ Soundness flag (same as PROP-4).** "Distinct inputs ⇒ distinct HKDF
outputs" is a strict-injectivity claim about HKDF that is technically false in
the cryptographic model. The axiom is a *modelling cheat* (collision
infeasibility), not a theorem of HKDF.

**Available in Lean extraction:**

- `chain.ChainEpochDirection.next_key_internal` — extracted
- `chain.ChainEpochDirection.next_key` — extracted

Both call `kdf::hkdf_to_vec`, which calls `hkdf_to_slice` (opaque).

**Lean provability:**

| Aspect | Assessment |
|--------|------------|
| **Difficulty** | Axiom-dependent (PROP-4 modelling assumption) |
| **Required axiom** | Reuses the PROP-4 collision-infeasibility postulate, instantiated for `(info ++ counter₁) ≠ (info ++ counter₂)`. |
| **Status** | 🔶 **AXIOM REQUIRED, MODELLING ASSUMPTION** |
| **Estimated effort** | 1.5 days |

---

### PROP-8: Root Key Ratchet [PROGRESS / INJECTIVITY — modelling assumption]

**Source:** `hax-cross`
(`cross_spqr_multiple_epochs_hkdf`, `tests/cross_lib.rs:314`) +
`production-code` (`add_epoch` derives new root via HKDF, `chain.rs:357-364`).

*Root key changes on each epoch.*

**⚠ Soundness flag (same as PROP-4).** Strict inequality of HKDF outputs across
distinct epochs is a cryptographic modelling assumption, not a theorem.

**Available in Lean extraction:**

- `chain.Chain.add_epoch` — extracted

Uses `hkdf_to_vec` (with `info = b"Signal PQ Ratchet V1 Chain Add Epoch"`)
for deriving the new `next_root` and per-direction chain seeds.

**Lean provability:**

| Aspect | Assessment |
|--------|------------|
| **Difficulty** | Axiom-dependent (PROP-4 modelling assumption) |
| **Status** | 🔶 **AXIOM REQUIRED, MODELLING ASSUMPTION** |
| **Estimated effort** | 2 days |

---

### PROP-9: Epoch Monotonicity [STATE INVARIANT]

**Source:** `production-code` (`hax_lib::assume!` and `assert!` in `add_epoch`,
`chain.rs:352-355`) + `production-test` (`directions_match` in `chain.rs:464`,
`ratchet` and `lockstep_run_with_logging` in `lib.rs` exercise the invariant in
composite flows).

*Given precondition `es.epoch = c.current_epoch + 1 ∧ c.current_epoch < U64.max`,
the post-state satisfies `c'.current_epoch = es.epoch`.*

**Note on signature.** `Chain::add_epoch` returns `()` and mutates `self`
(`chain.rs:350: pub fn add_epoch(&mut self, epoch_secret: EpochSecret)`). The
Aeneas extraction models this as a state-passing function returning the new
`Chain`. The Lean postcondition is over the *post-state*, not over a `result`
field.

**Caveat on tests.** No SPQR production test directly asserts `current_epoch += 1`;
the invariant is exercised only through composite tests like
`directions_match` (`chain.rs:464`) and `lockstep_run_with_logging`
(`lib.rs`). The nearby test `clear_old_send_keys` (`chain.rs:528-543`)
exercises `SendKeyEpochDecreased` (PROP-14), not epoch monotonicity, so it is
not a witness here.

**Available in Lean extraction:**

`chain.Chain.add_epoch` (in `Spqr/Code/Funs.lean`, generated; line numbers drift
on re-extraction) is fully extracted. The body assigns `self.current_epoch =
epoch_secret.epoch` after the `hax_lib::assume!` precondition fixes
`epoch_secret.epoch == self.current_epoch + 1`.

**Lean provability:**

| Aspect | Assessment |
|--------|------------|
| **Difficulty** | Easy — structural postcondition under explicit precondition |
| **Lean encoding** | `theorem add_epoch_ok (c : chain.Chain) (es : EpochSecret) (h_epoch : es.epoch = c.current_epoch + 1) (h_no_overflow : c.current_epoch < U64.max) : chain.Chain.add_epoch c es ⦃ c' => c'.current_epoch = es.epoch ⦄` |
| **Proof approach** | `unfold chain.Chain.add_epoch; step*` — the extracted code directly assigns the new epoch under the assumed precondition. |
| **Dependencies** | None — no opaque functions involved in the epoch counter update. (The HKDF call updating `next_root` happens under the same precondition; the chain-counter postcondition does not depend on the HKDF output.) |
| **Status** | ✅ **PROVABLE NOW** — Tier-1 quick win |
| **Estimated effort** | 0.5 days |

This obligation **subsumes the epoch-overflow safety obligation**: the
`h_no_overflow` precondition is exactly the spec's §3.8 condition, and the
extracted `U64`-arithmetic in Aeneas only succeeds when this holds.

---

### PROP-10: Structural Key Erasure [HISTORY / ERASURE PROPERTY]

**Source:** `production-code` (`links.pop_front()` and `clear_next()` in `send_key`,
`chain.rs:391-399`; `EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH = 1`, `chain.rs:125`)
+ `production-test` (`very_old_keys_are_trimmed`, `chain.rs:500-510`).

*Old chain keys are erased after epoch advancement; this is the structural half of forward
secrecy only.*

**Note on scope:** The full forward-secrecy property has two aspects: (1) **structural erasure** —
old key material is removed from the data structure after epoch advancement; and
(2) **cryptographic non-derivability** — knowledge of an old chain key does not allow deriving
future message keys. The Lean proof targets only the structural erasure (aspect 1). The
cryptographic aspect would require HKDF one-wayness axioms, which are out of scope here.

**Available in Lean extraction:**

- `chain.Chain.send_key` — extracted (`Funs.lean:6278`); includes `send_key_loop0/1` with
  `VecDeque` operations (`pop_front`, `push_back`)
- `chain.KeyHistory.gc` — extracted (`Funs.lean:5800`); clears old key history entries

**Lean provability:**

| Aspect | Assessment |
|--------|------------|
| **Difficulty** | Medium |
| **Lean encoding** | History/erasure property: `theorem send_key_erases_old (c : chain.Chain) (epoch : U64) ... : chain.Chain.send_key c epoch ⦃ result => ∀ i < epoch - EPOCHS_TO_KEEP, result.links[i].send.next.length = 0 ⦄` |
| **Challenges** | Lean's `VecDeque` model (represented as `alloc.collections.vec_deque.VecDeque`) and its `pop_front` semantics need to be reasoned about. Aeneas provides `VecDeque` specs in its standard library. |
| **Dependencies** | No opaque functions in the deletion path — `pop_front`, index operations are available |
| **Status** | ⚠️ **FEASIBLE** — requires VecDeque reasoning, no axioms needed for the structural erasure |
| **Estimated effort** | 2-3 days |

### PROP-12: Out-of-Order Key Retrieval [STATE INVARIANT + CONDITIONAL BEHAVIORAL SPEC]

**Source:** `production-code` (`KeyHistory::add`/`get`/`gc`/`remove` in
`chain.rs:130-208`, runtime
`assert_eq!(self.data.len() % Self::KEY_SIZE, 0)` at `chain.rs:191`) +
`production-test` (`out_of_order_keys` at `chain.rs:512-526`,
`previously_returned_key` at `:489-497`, `very_old_keys_are_trimmed` at
`:499-510`, `key_history_prop_test` at `:565+`, `ced_prop_test` further down).

**Structure of this entry.** PROP-12 covers two obligations of very different
difficulty (structural invariant vs. functional get-after-add roundtrip). They
are split below as **PROP-12a** and **PROP-12b**.

*Keys within `max_ooo_keys` window are correctly returned; outside window → `KeyTrimmed`.*

**Available in Lean extraction:**

- `chain.KeyHistory.add` — extracted (`Funs.lean:5710`)
- `chain.KeyHistory.get` — extracted (`Funs.lean:5882`)
- `chain.KeyHistory.gc` — extracted (`Funs.lean:5800`)
- `chain.KeyHistory.remove` — extracted (`Funs.lean:5731`)
- `chain.ChainEpochDirection.next_key` (drives key advancement) — extracted

**Lean provability:**

| Aspect | Assessment |
|--------|------------|
| **Difficulty** | **12a structural: easy. 12b functional: hard.** |
| **PROP-12a (structural)** | `KeyHistory.data.length % KEY_SIZE == 0` is preserved by `add`, `remove`, `gc`. KEY_SIZE = `4 + 32 = 36` (`chain.rs:130`). Provable by inspection of the loop invariants. **1 day.** |
| **PROP-12b (functional)** | `theorem kh_get_add_roundtrip (kh : chain.KeyHistory) (k : U32) (v : Array U8 32) (params : ChainParams) (h_fresh : ¬ kh.contains k) (h_size : kh.data.length < params.trim_size * KEY_SIZE) : KeyHistory.get (KeyHistory.add kh (k, v) params) k ⦃ r => r = ok (some v) ⦄` — requires byte-level indexing, the linear-scan loop in `get_loop`, and the trim-size precondition that suppresses the GC path in `add`. **3 days.** |
| **Key challenge** | `KeyHistory.data` is a flat `Vec<u8>` used as a byte-addressable key-value store. Lean must reason about byte-level indexing. |
| **Dependencies** | **⚠ Blocker for 12b:** `KeyHistory.get` and `KeyHistory.gc` are `#[hax_lib::opaque]` in the Rust source, making them `axiom` stubs in the Lean extraction. 12b **cannot be proved** without either (a) removing the `#[hax_lib::opaque]` annotations and re-extracting, or (b) introducing explicit axioms modelling `get`'s linear-scan semantics and `gc`'s trim behavior. This is a hard blocker, not a soft difficulty issue. |
| **Status** | ✅ 12a **PROVABLE NOW** + 🚫 12b **BLOCKED** by `KeyHistory.get`/`gc` opacity — requires de-opaquing or axiomatisation |
| **Estimated effort** | 4–5 days for 12a + 12b combined |

**Dropped candidate.** The earlier ordering-invariant idea is intentionally excluded: `remove`
can swap the tail record into the deleted slot, so `KeyHistory.data` is not globally ordered,
and `get` does not rely on sorted order.

### PROP-14: Send Epoch Cannot Decrease [STATE INVARIANT]

**Source:** `production-code` (`if epoch < self.send_epoch` guard in `send_key`, chain.rs:385-387) + `production-test` (`clear_old_send_keys`)

*`send_key(epoch)` returns `Error::SendKeyEpochDecreased` if `epoch < self.send_epoch`.*

**Available in Lean extraction:**

`chain.Chain.send_key` (`Funs.lean:6278`) — fully extracted. The check appears directly.

**Lean provability:**

| Aspect | Assessment |
|--------|------------|
| **Difficulty** | Easy |
| **Lean encoding** | `theorem send_key_epoch_guard (c : chain.Chain) (epoch : U64) (h : epoch < c.send_epoch) : chain.Chain.send_key c epoch ⦃ r => ∃ e s, r = Err (.SendKeyEpochDecreased e s) ⦄` |
| **Dependencies** | None |
| **Status** | ✅ **PROVABLE NOW** |
| **Estimated effort** | 0.5 days |

---

### PROP-15: Authenticator MAC Correctness [ALGEBRAIC SPECIFICATION]

**Source:** `production-code` (`verify_ct`/`mac_ct` in `authenticator.rs:57-79`)
+ `production-test` (indirect support via serialization stability in
`src/authenticator/serialize.rs::round_trip`; the direct MAC-correctness witness
is the code path itself) +
`hax-cross` (`upstream_spqr_auth_key_mismatch` in
`signal-spqr-hax/tests/cross_lib.rs:528`, gated on
`--features upstream-spqr`).

*`verify_ct(epoch, ct, mac_ct(epoch, ct))` succeeds for length-matched inputs.*

**Available in Lean extraction:**

- `authenticator.Authenticator.mac_ct` — extracted
- `authenticator.Authenticator.verify_ct` — extracted
- Both use `util::compare` (extracted, with hax precondition
  `lhs.len() == rhs.len()` at `src/util.rs:22-23`) for constant-time comparison
- `libcrux_hmac::hmac` — **opaque** (confirmed as `axiom` in `FunsExternal.lean`,
  same deep-generic-trait family as `hkdf_to_slice`). However, **no HMAC axiom
  is needed for PROP-15/15b**: in Lean's pure-functional model every term
  (including `axiom` stubs) is referentially transparent, so
  `hmac(k, m) = hmac(k, m)` holds by `rfl`. The proof only requires
  `compare(a, a) = 0` and `mac_ct`'s output-length postcondition.

**Lean provability:**

| Aspect | Assessment |
|--------|------------|
| **Difficulty** | Easy — `hmac` is opaque but irrelevant (see Key insight) |
| **Key lemma** | `compare(a, a) = 0` for `util::compare`. Provable by structural induction on the byte array. |
| **Lean encoding** | `theorem verify_ct_mac_roundtrip (auth : authenticator.Authenticator) (epoch : U64) (ct : Slice U8) : auth.mac_ct epoch ct >>= fun mac => auth.verify_ct epoch ct mac ⦃ r => r = ok () ⦄` (where `mac.len() == MACSIZE` follows from the `mac_ct` postcondition annotation, satisfying `compare`'s length precondition) |
| **Key insight** | `verify_ct` calls `util::compare(self.mac_ct(ep, ct), mac)`. When `mac = mac_ct(ep, ct)`, we compare a value to itself. In Lean's pure-functional model every term (including `axiom` stubs) is referentially transparent, so `mac_ct ep ct = mac_ct ep ct` by `rfl`, and `compare(a, a) = 0` follows from the extracted body of `compare`. `libcrux_hmac::hmac` is confirmed opaque (axiom in `FunsExternal.lean`), but **no HMAC axiom is needed** — referential transparency suffices. The proof does require checking that `compare`'s length precondition is met. |
| **Dependencies** | `util::compare(a, a) = 0` lemma; `mac_ct` returns `MACSIZE` bytes (visible from `#[hax_lib::ensures]` annotation at `authenticator.rs:65`). |
| **Status** | ✅ **PROVABLE NOW** — `hmac` opacity confirmed but does not block the proof |
| **Estimated effort** | 1 day |

**Companion property PROP-15b: header-MAC roundtrip** —
`verify_hdr(epoch, hdr, mac_hdr(epoch, hdr)) = ok ()`, parallel to PROP-15.
Same proof shape; 0.5 days.

---

### PROP-16: Version Negotiation Safety [CONDITIONAL BEHAVIORAL SPEC]

**Source:** `production-code` (version check in `recv`, `lib.rs`) + `production-test` (`negotiation_refused_a2b`, `negotiation_refused_b2a`)

*If `min_version = V1` and the peer sends V0, `recv` returns `Error::MinimumVersion`.*

**Available in Lean extraction:**

`lib.rs` `recv` function — **NOT extracted**.

**Lean provability:**

| Aspect | Assessment |
|--------|------------|
| **Status** | 🚫 **BLOCKED** — requires extracting `lib.rs`. The fix is to add `"spqr"` (the crate root) to `start_from` in `aeneas-config.yml` and handle any resulting Charon issues. |
| **Estimated effort** | 2 days (after lib.rs extraction) |

---

### PROP-17: Key Jump Limit [CONDITIONAL BEHAVIORAL SPEC]

**Source:** `production-code` (`if at - self.ctr > params.max_jump_or_default()`
guard in `key()`, `chain.rs:247-251`) +
`production-test` (`ced_prop_test` `TooHigh` action, in `chain.rs` test module).

*`ChainEpochDirection::key(at, params)` returns `Err(Error::KeyJump(ctr, at))`
when `at > ctr` **and** `at - ctr > max_jump`.*

**Note on precondition.** The `at - ctr` subtraction is unsigned. It is
well-defined only on the `Ordering::Greater` branch of the `match at.cmp(&self.ctr)`
in `chain.rs:248`. The other branches go elsewhere:

- `at < ctr` → returns `prev.get(at, ctr, params)` (out-of-order key lookup,
  may return `Error::KeyTrimmed`, never `KeyJump`).
- `at == ctr` → returns `Err(Error::KeyAlreadyRequested(at))`.

The Lean theorem must state the `at > ctr` precondition explicitly, otherwise
the `at - ctr` term in the antecedent underflows.

**Available in Lean extraction:**

`chain.ChainEpochDirection.key` — fully extracted.

**Lean provability:**

| Aspect | Assessment |
|--------|------------|
| **Difficulty** | Easy |
| **Lean encoding** | `theorem key_jump_guard (ced : chain.ChainEpochDirection) (at_ : U32) (params : chain.ChainParams) (h_gt : at_ > ced.ctr) (h_jump : at_ - ced.ctr > params.max_jump_or_default) : chain.ChainEpochDirection.key ced at_ params ⦃ r => ∃ c a, r = Err (.KeyJump c a) ∧ c = ced.ctr ∧ a = at_ ⦄` |
| **Dependencies** | None |
| **Status** | ✅ **PROVABLE NOW** |
| **Estimated effort** | 0.5 days |

**Companion guard PROP-17b:** prove the `Ordering::Equal` branch:

```
theorem key_already_requested (ced ...) (h : at_ = ced.ctr) :
    chain.ChainEpochDirection.key ced at_ params ⦃ r =>
      r = Err (.KeyAlreadyRequested at_) ⦄
```

This completes the case-analysis trio (Greater/Equal/Less); 0.25 days.

---

### PROP-18: HKDF Expand Safety / Panic Freedom [CONDITIONAL BEHAVIORAL SPEC]

**Source:** `production-code`
(`.expect("all lengths should work for SHA256")` in `src/kdf.rs:17`).

*All HKDF expand calls succeed (output length within SHA-256 limits).*

**Available in Lean extraction:**

- `kdf.hkdf_to_vec` — extracted; calls `hkdf_to_slice` (opaque)
- Call sites request 32, 64, or 96 bytes (all well within the 8160-byte SHA-256 limit)

**Lean provability:**

| Aspect | Assessment |
|--------|------------|
| **Difficulty** | Easy (given axiom) |
| **Lean encoding** | Axiom: `axiom hkdf_to_slice_succeeds (salt ikm info : Slice U8) (len : Usize) (h : len ≤ 8160) : hkdf_to_slice salt ikm info len ⦃ r => r.isOk ⦄` |
| **Verification** | Show all call sites pass lengths ≤ 8160: `chain.rs` uses 96 bytes in `add_epoch`/`new`, 64 bytes in `next_key_internal`; `authenticator.rs` uses 64 bytes in `update`; `v1/unchunked/send_ct.rs` and `v1/unchunked/send_ek.rs` use 32 bytes. All ≤ 8160. |
| **Status** | 🔶 **AXIOM REQUIRED** — one `hkdf_to_slice_succeeds` axiom suffices for all call sites |
| **Estimated effort** | 0.5 days |

### PROP-21: Only Two Transitions Emit a Key [STATE INVARIANT]

**Source:** `spec-mlkembraid` (§1.1: "each party outputs at most one key per epoch").

**Why this form.** The naïve reading "each party outputs at most one key per
epoch" reduces directly to PROP-9 (epoch monotonicity, with its
`current_epoch < U64.max` precondition, ensures `add_epoch` cannot process the
same epoch twice) plus the structural fact below. The structural fact is the
non-trivial obligation worth proving in Lean.

**Statement:** in `v1.chunked.states.States`, the `Send.key` field is `Some _`
only for the `HeaderReceived.send_ct1` transition, and the `Recv.key` field is
`Some _` only for the `EkSentCt1Received.recv_ct2_chunk` transition (its `Done`
branch). All other transitions produce `key = None`.

This is a **case-by-case syntactic check** on the 22 send-arms + 22 recv-arms
of `States.send` / `States.recv` (`src/v1/chunked/states.rs:115-273` for send,
`:275-533` for recv), pairing into a "key is None" obligation for everything
except the two cited transitions.

**Lean provability:**

| Aspect | Assessment |
|--------|------------|
| **Difficulty** | Easy (mechanical case analysis) |
| **Lean encoding** | `theorem only_two_transitions_emit_key : ∀ s r, (States.send s = ok r ∧ r.key.isSome) → (s = HeaderReceived _) ; symmetric for recv` |
| **Dependencies** | None |
| **Status** | ✅ **PROVABLE NOW** — structural |
| **Estimated effort** | 1 day |

Combined with PROP-9, this gives the spec's "at most one key per epoch"
guarantee at both the SCKA layer (per-state) and the SM layer (per-chain).

---

### PROP-22: Epoch Agreement [CORRESPONDENCE PROPERTY]

**Source:** `spec-mlkembraid` (§1.1: "`sending_epoch` from Send() equals
`receiving_epoch` from the corresponding Receive()") +
`production-code` (sending_epoch / receiving_epoch defined as `msg.epoch - 1`,
`src/test/v1_impls.rs:25,40`).

**Why the structural form is the right one.** A naïve encoding
`msg.epoch - 1 = msg.epoch - 1` after pinning `send_res.msg = msg` reduces to
`rfl` — not a theorem, just the definition. The non-trivial obligation is the
two-part state-machine claim below: *the wire-level `msg.epoch` faithfully
reflects the sender's state, and the receiver only succeeds for messages whose
epoch matches its expected window.*

**Statement (two parts):**

PROP-22a — *send output reflects sender state*: for every `States` variant `s`,
`States.send s = ok (Send { msg, .. }) → msg.epoch = s.epoch`.

PROP-22b — *recv success epoch discipline*: for every `States` variant
`s` and message `msg`, **whenever `recv` succeeds** (returns `ok`, not `Err`),
the message epoch is within the expected window:
`States.recv s msg = ok (Recv { state = s', .. }) → msg.epoch ≤ s.epoch ∨ (s = Ct2Sampled _ ∧ msg.epoch = s.epoch + 1)`.
The `= ok` precondition is essential: for non-`Ct2Sampled` states, `msg.epoch > s.epoch`
returns `Err(EpochOutOfRange)` (see PROP-39), so the property holds vacuously for
those error cases. For `Ct2Sampled`, `msg.epoch > s.epoch + 1` also returns an error
(PROP-26). The non-trivial content is that the `ok` branches only admit epochs
in `{≤ s.epoch} ∪ {s.epoch + 1 if Ct2Sampled}`.

**Together these give epoch agreement:** if Alice executes `send` from state
`s_A` and Bob executes `recv` of Alice's emitted `msg` from state `s_B`, then
`msg.epoch = s_A.epoch` (by 22a) and `s_B`'s epoch is consistent with that value
(by 22b). The spec-level `sending_epoch` and `receiving_epoch`
(both `msg.epoch - 1`) are then equal *by construction at the SCKA layer*.

**Available in Lean extraction:**

- `v1.chunked.states.States.send` — extracted (all 11 variants).
- `v1.chunked.states.States.recv` — extracted (all 11 variants).

**Lean provability:**

| Aspect | Assessment |
|--------|------------|
| **Difficulty** | Easy-Medium (structural induction over the 11 variants) |
| **Lean encoding (22a)** | `theorem send_msg_epoch (s : States) (r : Send) (h : States.send s = ok r) : r.msg.epoch = s.epoch_of` (where `epoch_of` extracts the epoch from any variant) |
| **Lean encoding (22b)** | `theorem recv_msg_epoch_discipline (s : States) (msg : Message) (r : Recv) (h : States.recv s msg = ok r) : msg.epoch ≤ s.epoch_of ∨ (s = Ct2Sampled _ ∧ msg.epoch = s.epoch_of + 1)` |
| **Dependencies** | None (no opaque functions on this path) |
| **Status** | ⚠️ **FEASIBLE** — structural case-split on 11 variants |
| **Estimated effort** | 2 days for 22a + 22b combined |

---

### PROP-23: Sender/Receiver Epoch Knowledge [HISTORY PROPERTY]

**Source:** `spec-mlkembraid` (§1.1: "When Send() returns `sending_epoch`, the sender possesses, or has possessed, the key for that epoch and all earlier epochs"; symmetric for Receive)

*When Send returns `sending_epoch = ep`, the sender has emitted keys for all epochs ≤ ep.
Symmetrically for Receive.*

**Available in Lean extraction:**

- `chain.Chain.send_key(epoch)` — extracted; returns `(index, msg_key)` for the given epoch.
  The chain must already have the epoch's secret loaded via `add_epoch`.
- `chain.KeyHistory` tracks per-epoch keys with `add`/`get` operations.

**Lean provability:**

| Aspect | Assessment |
|--------|------------|
| **Difficulty** | Medium-Hard |
| **Lean encoding** | `theorem sender_epoch_knowledge (c : chain.Chain) (ep : U64) (h : c.send_key ep ⦃ r => r.isOk ⦄) : ∀ ep' ≤ ep, c.has_epoch_secret ep'` — requires defining a `has_epoch_secret` predicate over the chain's link structure. |
| **Proof approach** | Follows from chain's structural invariant: `add_epoch` adds epochs monotonically (PROP-9/13), and `send_key` fails for epochs not yet added. Show that `∀ ep' < current_epoch`, a link exists. |
| **Dependencies** | PROP-9, chain structural invariant |
| **Status** | ⚠️ **FEASIBLE** — requires chain invariant formalization |
| **Estimated effort** | 3-4 days |

---

### PROP-24: KDF_OK Post-Processing [ALGEBRAIC SPECIFICATION]

**Source:** `spec-mlkembraid` (§2.2: `KDF_OK(shared_secret, epoch)` — "32 bytes of output from HKDF with salt=zeros, ikm=shared_secret, info=PROTOCOL_INFO||':SCKA Key'||ToBytes(epoch)")

*The raw KEM shared secret from encaps1/decaps is post-processed via HKDF before being used
as an epoch secret, keyed by the epoch identifier.*

**Available in Lean extraction:**

- `kdf.hkdf_to_vec` — extracted (wraps opaque `hkdf_to_slice`)
- `v1.unchunked.send_ct` (`HeaderReceived.send_ct1`) — calls
  `hkdf_to_vec(&[0u8; 32], &secret, &info, 32)` where `info = b"Signal_PQCKA_V1_MLKEM768:SCKA Key" || epoch.to_be_bytes()`
- `v1.unchunked.send_ek` (`EkSentCt1Received.recv_ct2`) — same HKDF call on decaps'd secret

**Lean provability:**

| Aspect | Assessment |
|--------|------------|
| **Difficulty** | Medium |
| **Lean encoding** | (a) **Structural** (no axioms needed): both call sites use the same HKDF parameterization — verify info-string equality byte-for-byte: `b"Signal_PQCKA_V1_MLKEM768:SCKA Key" || epoch.to_be_bytes()`. (b) **Functional** (modelling assumption): the epoch is bound into the KDF output via the info string, so different epochs yield "different" keys — under the PROP-4 collision-infeasibility postulate. |
| **Key insight** | This property is what makes the raw KEM output into a *usable* epoch secret. Without it, the shared secret has no epoch binding and could be confused across epochs. |
| **Dependencies** | (a) is independent. (b) reuses the PROP-4 modelling assumption. |
| **Status** | 🟢 **(a) PROVABLE NOW** (call-site syntactic equality) + 🔶 **(b) MODELLING ASSUMPTION** for the differs-across-epochs claim |
| **Estimated effort** | 0.5 days for (a); 1 day for (b) |

---

### PROP-25: EK Integrity Verification [CONDITIONAL BEHAVIORAL SPEC]

**Source:** `spec-mlkembraid` (§2.5, Ct1Sampled.Receive and Ct1Acknowledged.Receive:
"if SHA3-256(ek_seed || ek_vector) != hek: raise Error").

*When the encapsulation key vector is received, its integrity against the
previously received header is verified before use.*

**Available in Lean extraction:**

- `incremental_mlkem768::ek_matches_header` — extracted (`src/incremental_mlkem768.rs:28-30`); delegates to `incremental::validate_pk_bytes(hdr, ek)`.
- `v1.unchunked.send_ct.Ct1Sent.recv_ek` — calls `ek_matches_header` and
  returns `Error::ErroneousDataReceived` on mismatch
  (`src/v1/unchunked/send_ct.rs:152-172`).
- This guard fires on **three spec transitions** (all routing through `Ct1Sent::recv_ek`):
  - **Transition (9):** `Ct1Sampled::recv_ek_chunk` when `EkCt1Ack` completes the `ek_decoder` in the same call (`src/v1/chunked/send_ct.rs:177-178`)
  - **Transition (10):** `Ct1Sampled::recv_ek_chunk` when `Ek` completes the `ek_decoder` (`src/v1/chunked/send_ct.rs:177-178`, different payload branch)
  - **Transition (11):** `Ct1Acknowledged::recv_ek_chunk` when `EkCt1Ack` completes the `ek_decoder` (`src/v1/chunked/send_ct.rs:266-267`)
  All three must be covered.
- The Rust delegates the SHA3-256 check to libcrux's `validate_pk_bytes`,
  which is opaque from this codebase's perspective. See PROP-3b for the
  axiomatisation.

**Lean provability:**

| Aspect | Assessment |
|--------|------------|
| **Difficulty** | Easy at the call-site level; axiom-dependent for the SHA3-256 spec equivalence |
| **Lean encoding (guard)** | `theorem recv_ek_rejects_mismatched (s : v1.unchunked.send_ct.Ct1Sent) (ek : EncapsulationKey) (h : ¬ ek_matches_header ek s.hdr) : s.recv_ek epoch ek ⦃ r => r = Err Error.ErroneousDataReceived ⦄` |
| **Lean encoding (chunked variants)** | Three parallel theorems for transitions (9), (10), and (11): `Ct1Sampled.recv_ek_chunk` (two payload cases) and `Ct1Acknowledged.recv_ek_chunk` showing the same guard fires up the call stack. |
| **Challenge** | `ek_matches_header` wraps `validate_pk_bytes`. The guard is visible at the call site even when `validate_pk_bytes` is opaque. The *spec correspondence* (that `ek_matches_header ek hdr ↔ hdr[32..] = SHA3-256(hdr[..32] ++ ek)`) is the separate PROP-3b obligation. |
| **Dependencies** | `ek_matches_header` extraction status; PROP-3b for spec equivalence |
| **Status** | ⚠️ **FEASIBLE** at call-site level; PROP-3b is the missing spec link |
| **Estimated effort** | 1 day for both chunked call paths + the unchunked direct call |

---

### PROP-26: Ct2Sampled Epoch Guard [CONDITIONAL BEHAVIORAL SPEC]

**Source:** `spec-mlkembraid` (§2.5, Ct2Sampled.Receive: `if msg.epoch == state.epoch + 1` → transition to KeysUnsampled; implicit: reject epochs > epoch+1)

*In the Ct2Sampled state, only messages from exactly the next epoch (`epoch + 1`) trigger the
transition to KeysUnsampled. Messages from further-future epochs are rejected.*

**Available in Lean extraction:**

- `v1.chunked.states.States.recv` — extracted; includes `Ct2Sampled` match arm.
- Implementation: `msg.epoch == state.epoch() + 1` → `KeysUnsampled`; else for
  `msg.epoch > state.epoch() + 1` → `Error::EpochOutOfRange`

**Lean provability:**

| Aspect | Assessment |
|--------|------------|
| **Difficulty** | Easy |
| **Lean encoding** | `theorem ct2_sampled_future_epoch_guard (s : Ct2Sampled) (msg : Message) (h : msg.epoch > s.epoch + 1) : States.Ct2Sampled(s).recv msg ⦃ r => ∃ e, r = Err (.EpochOutOfRange e) ⦄` |
| **Dependencies** | None |
| **Status** | ✅ **PROVABLE NOW** |
| **Estimated effort** | 0.5 days |

---

### PROP-27: Initialization Correctness [STATE INVARIANT]

**Source:** `spec-mlkembraid` (§2.6: "Alice = KeysUnsampled(epoch=1, auth=Init(1, shared_secret))", "Bob = NoHeaderReceived(epoch=1, auth=Init(1, shared_secret), header_decoder)")

*Protocol initialization produces the correct starting states: Alice as `KeysUnsampled` and
Bob as `NoHeaderReceived`, both at epoch 1, with authenticators initialized from the
preshared secret.*

**Available in Lean extraction:**

- `v1.chunked.states.States` and individual unchunked state types — extracted.
- `authenticator.Authenticator.new` — extracted; takes `root_key` and `epoch`, zero-fills
  internal keys, then calls `update`.
- The actual initialization is in `lib.rs` (`initial_state`), which is **not extracted**.

**Lean provability:**

| Aspect | Assessment |
|--------|------------|
| **Difficulty** | Easy (once `lib.rs` is extracted) |
| **Lean encoding** | `theorem init_alice (ss : Vec U8) : initial_state Direction.Alice ss ⦃ r => r.scka_state = States.KeysUnsampled ∧ r.epoch = 1 ⦄` (and symmetric for Bob) |
| **Dependencies** | Blocker 1 (`lib.rs` extraction) |
| **Status** | 🚫 **BLOCKED** — requires `lib.rs` extraction |
| **Estimated effort** | 0.5 days (after extraction) |

---

## Additional structural properties

The properties below complete the catalog with obligations on `epoch_idx`,
`KeyHistory` ordering, the v1 state-machine guards, deviation flags against
`mlkembraid.pdf`, and protobuf / wire-format roundtrips.

### PROP-29: `epoch_idx` ↔ `current_epoch` correspondence [STATE INVARIANT]

**Source:** `production-code` (`Chain::epoch_idx`, `chain.rs:372-382`) +
`lean-specific`.

*The `epoch_idx` helper is the linchpin between numeric epochs and `links`
positions. Every `send_key` / `recv_key` call goes through it; correctness of
the chain depends on its specification.*

**Available in Lean extraction:** `chain.Chain.epoch_idx` — extracted.

**Lean encoding:**

```
theorem epoch_idx_spec (c : chain.Chain) (epoch : Epoch) :
    chain.Chain.epoch_idx c epoch ⦃ r =>
      match r with
      | Ok i =>
          epoch ≤ c.current_epoch
          ∧ c.current_epoch - epoch < c.links.length
          ∧ i = c.links.length - 1 - (c.current_epoch - epoch)
      | Err (.EpochOutOfRange e) => e = epoch ∧ (epoch > c.current_epoch ∨ (epoch ≤ c.current_epoch ∧ c.current_epoch - epoch ≥ c.links.length))
      | _ => False ⦄
```

**Status:** ✅ **PROVABLE NOW** — Tier 1, ~1 day.

### PROP-30: Less-branch no-op of `States.recv` [STATE INVARIANT]

**Source:** `spec-mlkembraid` (§2.5: every state's pseudocode falls through
when `msg.epoch ≠ state.epoch`) + `production-code`
(`src/v1/chunked/states.rs` Less branches under each `match msg.epoch.cmp(...)`).

*For every state variant `s` and message with `msg.epoch < s.epoch`, `recv s msg`
returns `state = s` and `key = None`.*

**Note.** This is the dual of PROP-26 (Greater-branch guard). Together they
characterise the full `match msg.epoch.cmp(&state.epoch())` behaviour for the
ten non-`Ct2Sampled` variants.

**Available in Lean extraction:** `States.recv` — extracted.

**Lean encoding:** case-split over the 10 non-`Ct2Sampled` variants; each Less
branch is a literal `Self::X(state)` re-construction. Effort: 1 day.

**Status:** ✅ **PROVABLE NOW**.

### PROP-31: `Authenticator::new` ≡ Init from spec §2.6 [STATE INVARIANT]

**Source:** `spec-mlkembraid` (§2.6 `InitAlice` / `InitBob` definitions:
`auth = Authenticator.Init(epoch, shared_secret)`, where `Init` is `update` over
zero-state).

*`Authenticator::new(k, ep)` produces an authenticator equivalent to a fresh
zero-state authenticator followed by `update(ep, k)`.*

**Available in Lean extraction:** `authenticator.Authenticator.new`
(`src/authenticator.rs:35-43`) — extracted; literally implemented as
"start with zero `root_key` and `mac_key`, then call `update(ep, &root_key_in)`".

**Lean encoding:**

```
theorem authenticator_new_eq_zero_then_update (k : Slice U8) (ep : Epoch) :
    authenticator.Authenticator.new k ep =
    let zero := { root_key := List.replicate 32 0, mac_key := List.replicate 32 0 }
    Authenticator.update zero ep k
```

**Status:** ✅ **PROVABLE NOW** — Tier 1, ~0.5 days.

### PROP-32: `Authenticator::update` derives root and mac keys [ALGEBRAIC SPECIFICATION]

**Source:** `production-code` (`src/authenticator.rs:44-54`) +
`spec-mlkembraid` (§2.4 `KDF_AUTH`).

*`update(ep, k)` derives `root_key` and `mac_key` from a single 64-byte HKDF
output, splitting `[..32]` and `[32..]`.*

**⚠ Spec deviation flag.** The actual implementation uses
`salt = [0u8; 32]`, `ikm = root_key || k`, **deviating from spec §2.2**
which prescribes `salt = root_key`, `ikm = k`. The Lean theorem captures the
*implementation's* derivation; a separate "code matches spec" obligation would
fail and should be flagged as a known deviation.

**Lean encoding:**

```
theorem authenticator_update_derivation (auth : Authenticator) (ep : Epoch) (k : Slice U8) :
    Authenticator.update auth ep k ⦃ auth' =>
      let info := b"Signal_PQCKA_V1_MLKEM768:Authenticator Update" ++ ep.to_be_bytes
      let kdf_out := hkdf_to_vec [0u8; 32] (auth.root_key ++ k.toList) info 64
      auth'.root_key = kdf_out[..32] ∧ auth'.mac_key = kdf_out[32..] ⦄
```

**Status:** ✅ **PROVABLE NOW** (modulo `hkdf_to_vec` opacity, but the splitting
structure is visible without unfolding HKDF). Effort: 1 day.

### PROP-33: Spec deviation — `EkSentCt1Received.send` emits `Ct1Ack(true)` [DEVIATION FLAG]

**Source:** `production-code` (`src/v1/chunked/states.rs:178-184`) +
`spec-mlkembraid` (§2.5, `EkSentCt1Received.Send` pseudocode emits `None`).

*The Rust code emits `MessagePayload::Ct1Ack(true)` from
`EkSentCt1Received.Send`, where mlkembraid §2.5 specifies `None`. This deviation
is intentional and prevents a spec-level deadlock (see PROP-34).*

**Purpose.** A formally-stated deviation lets the Lean artifact serve as
documentation: if a future spec revision aligns the spec with the code, this
property would still hold; if a future Rust patch reverts to spec behaviour, the
property would fail and signal the change.

**Lean encoding:**

```
theorem ek_sent_ct1_received_send_emits_ct1ack (s : send_ek.EkSentCt1Received) :
    States.send (States.EkSentCt1Received s) ⦃ r =>
      r.msg.payload = MessagePayload.Ct1Ack true ⦄
```

**Status:** ✅ **PROVABLE NOW** — structural, 0.25 days.

### PROP-34: Spec deviation — `EkReceivedCt1Sampled.recv` accepts `Ct1Ack(true)` [DEVIATION FLAG]

**Source:** `production-code` (`src/v1/chunked/states.rs:464-477`) +
`spec-mlkembraid` (§2.5, `EkReceivedCt1Sampled.Receive` pseudocode accepts only
`EkCt1Ack`).

*The Rust code transitions to `Ct2Sampled` on either `Ct1Ack(true)` or
`EkCt1Ack(_)` from `EkReceivedCt1Sampled`, where mlkembraid §2.5 specifies only
`EkCt1Ack`. Combined with PROP-33, this prevents a spec deadlock in certain
reachable state pairs.*

**Lean encoding:**

```
theorem ek_received_ct1_sampled_accepts_ct1ack (s : send_ct.EkReceivedCt1Sampled) (msg : Message) (h : msg.epoch = s.epoch ∧ msg.payload = MessagePayload.Ct1Ack true) :
    States.recv (States.EkReceivedCt1Sampled s) msg ⦃ r =>
      ∃ s', r.state = States.Ct2Sampled s' ⦄
```

**Status:** ✅ **PROVABLE NOW** — structural, 0.25 days.

### PROP-35: Wire-format roundtrip for `Message` [SERIALIZATION]

**Source:** `production-code` (`src/v1/chunked/states/serialize.rs:204-279`).

*`Message.deserialize(Message.serialize(m, idx)) = ok (m, idx, _)` for every
valid message.*

**Available in Lean extraction:** `Message.serialize` and `Message.deserialize`
— extracted (loop bodies have one sorry'd block in `encode_chunk`/`decode_chunk`
internals; the property is provable above the sorry boundary if those bodies are
treated as pre-axiom-friendly).

**Lean encoding:**

```
theorem message_roundtrip (m : Message) (idx : U32) (h_epoch : m.epoch > 0) :
    Message.deserialize (Message.serialize m idx) ⦃ r =>
      r = ok (m, idx, _) ⦄
```

**Status:** ⚠️ **FEASIBLE** — depends on closing varint/chunk encode/decode loop
sorries. Effort: 2-3 days.

### PROP-36: `Message.deserialize` rejects `epoch == 0` [SERIALIZATION GUARD]

**Source:** `production-code` (`src/v1/chunked/states/serialize.rs:253-256`:
`if epoch == 0 { return Err(Error::MsgDecode); }`).

*Wire-format epoch 0 is rejected. Combined with the rest of the protocol's
`msg.epoch - 1` arithmetic (in `lib.rs:300, 427`), this prevents underflow on
the SM-layer index calculation.*

**Lean encoding:**

```
theorem deserialize_rejects_zero_epoch (bytes : SerializedMessage) (h : bytes[..].extracts_to_epoch_0) :
    Message.deserialize bytes ⦃ r => r = Err Error.MsgDecode ⦄
```

**Status:** ✅ **PROVABLE NOW** — Tier 1, 0.25 days.

### PROP-37: Protobuf state roundtrip for v1 chunked [SERIALIZATION]

**Source:** `production-code` (`into_pb`/`from_pb` in
`src/v1/chunked/states/serialize.rs:11-93` and per-variant
`src/v1/chunked/{send_ek,send_ct}/serialize.rs`,
`src/v1/unchunked/{send_ek,send_ct}/serialize.rs`).

*For every `States` variant `s`, `States.from_pb(States.into_pb s) = ok s`.*

**Why.** Serialization bugs are a classic source of interoperability failures
and are worth catching formally.

**Available in Lean extraction:** `States.into_pb` and `States.from_pb` —
extracted.

**Lean encoding:**

```
theorem states_pb_roundtrip (s : States) :
    States.from_pb (States.into_pb s) = ok s
```

**Status:** ⚠️ **FEASIBLE** — case split over 11 `States` variants × 2
substructures (chunked/unchunked) each. Effort: 3-4 days.

### PROP-38: Chain protobuf roundtrip [SERIALIZATION — BLOCKED]

**Source:** `production-code` (`Chain::into_pb` / `Chain::from_pb`,
`src/chain.rs:415-452`).

**Status:** 🚫 **BLOCKED** — both methods are `#[hax_lib::opaque]` (use
`into_iter`/`map` over `VecDeque`), so the Lean extraction has them as axioms.
Lifting opacity needs a `#[cfg(hax)]` alternative that uses indexed loops.

### PROP-39: Greater-branch `EpochOutOfRange` for non-`Ct2Sampled` states [CONDITIONAL BEHAVIORAL SPEC + DEVIATION FLAG]

**Source:** `production-code` (`Ordering::Greater` branches in
`src/v1/chunked/states.rs:282-528`, every `recv` arm except `Ct2Sampled`) +
`spec-mlkembraid` (§2.5: every state's pseudocode falls through on epoch
mismatch — the spec treats `msg.epoch > state.epoch` as a no-op, not an error).

*For every state variant `s` except `Ct2Sampled`, if `msg.epoch > s.epoch`,
`States.recv s msg` returns `Err(Error::EpochOutOfRange(msg.epoch))`.*

**⚠ Spec deviation flag.** The spec (§2.5) treats epoch-mismatched messages as
silent no-ops returning `(receiving_epoch, output_key = None)` with the state
preserved. The Rust code instead treats `msg.epoch > state.epoch` as a hard
error that terminates the SPQR session (the caller in `lib.rs::recv` propagates
the `Err`). This is a behavioral tightening that reduces liveness under
adversarial message scheduling but may be the correct choice for Signal's
ordered transport. This property documents the code's actual behavior; the
deviation from the spec is intentional and should be flagged.

This is the dual of PROP-30 (Less-branch no-op). Together PROP-30 and PROP-39
fully characterize the `msg.epoch.cmp(&state.epoch())` dispatch for all 10
non-`Ct2Sampled` states. PROP-26 handles `Ct2Sampled`.

**Available in Lean extraction:** `States.recv` — extracted (all 11 variants).

**Lean encoding:**

```
theorem recv_future_epoch_error (s : States) (msg : Message)
    (h_not_ct2 : ¬ ∃ c, s = States.Ct2Sampled c)
    (h_gt : msg.epoch > s.epoch_of) :
    States.recv s msg ⦃ r =>
      ∃ e, r = Err (.EpochOutOfRange e) ∧ e = msg.epoch ⦄
```

**Status:** ✅ **PROVABLE NOW** — structural case-split on 10 variants. Effort: 1 day.

### PROP-40: MAC Input Byte-Form Correspondence [SPEC CORRESPONDENCE]

**Source:** `spec-mlkembraid` (§2.4: `MacHdr(state, epoch, hdr) = MAC(state.mac_key,
PROTOCOL_INFO ‖ ":ekheader" ‖ epoch ‖ hdr, MAC_SIZE)` and `MacCt(state, epoch, ct) =
MAC(state.mac_key, PROTOCOL_INFO ‖ ":ciphertext" ‖ epoch ‖ ct, MAC_SIZE)`) +
`production-code` (`mac_hdr`/`mac_ct` in `authenticator.rs:68-79`).

*The MAC input byte sequences assembled by `mac_hdr` and `mac_ct` match the
spec's § 2.4 recipes byte-for-byte.*

PROP-15/15b prove that `Vfy(Mac(..)) = ok` (the functional roundtrip), but they
do **not** verify that the MAC input bytes are `PROTOCOL_INFO ‖ ":ekheader" ‖
epoch ‖ hdr` per the spec. This property closes that gap.

**Statement (two parts):**

PROP-40a — *header MAC input form*:

```
theorem mac_hdr_input_form (auth : Authenticator) (ep : Epoch) (hdr : Slice U8) :
    let expected := PROTOCOL_INFO ++ b":ekheader" ++ ep.to_be_bytes ++ hdr.toList
    Authenticator.mac_hdr auth ep hdr =
      hmac auth.mac_key expected MAC_SIZE
```

PROP-40b — *ciphertext MAC input form*:

```
theorem mac_ct_input_form (auth : Authenticator) (ep : Epoch) (ct : Slice U8) :
    let expected := PROTOCOL_INFO ++ b":ciphertext" ++ ep.to_be_bytes ++ ct.toList
    Authenticator.mac_ct auth ep ct =
      hmac auth.mac_key expected MAC_SIZE
```

**Available in Lean extraction:** `authenticator.Authenticator.mac_hdr` and
`mac_ct` — both extracted. The info-string construction is visible in the
extracted body.

**Lean provability:**

| Aspect | Assessment |
|--------|------------|
| **Difficulty** | Easy — unfold the extracted body and verify byte concatenation |
| **Dependencies** | `hmac` is opaque, so the theorem asserts the input bytes match the spec form up to the `hmac` call boundary. The HMAC internals are not unfolded. |
| **Status** | ✅ **PROVABLE NOW** |
| **Estimated effort** | 0.5 days for 40a + 40b combined |

### PROP-41: PROTOCOL_INFO Byte-Form Check [CONSTANT REGRESSION + DEVIATION FLAG]

**Source:** `spec-mlkembraid` (§2.2: `PROTOCOL_INFO` is "the concatenation of a
protocol identifier, a string representation of KEM, and a string
representation of MAC, separated with the delimiter '_', such as
`MyProtocol_MLKEM768_SHA-256`") + `production-code` (all HKDF and MAC info
strings use the prefix `b"Signal_PQCKA_V1_MLKEM768"`).

*The `PROTOCOL_INFO` string used by the implementation is
`b"Signal_PQCKA_V1_MLKEM768"`, which omits the MAC algorithm identifier
(`_HMAC-SHA256` or `_SHA-256`) that the spec's example pattern includes.*

**⚠ Spec deviation flag.** The spec says "The string representations of the
ML-KEM Braid parameters are defined by the implementer", so this is technically
permitted. However, the omission means that if a future variant swaps MAC
primitives the wire/KDF context won't differentiate them. This property serves
as a regression check on the constant and documents the deviation.

**Lean encoding:**

```
theorem protocol_info_bytes :
    PROTOCOL_INFO = "Signal_PQCKA_V1_MLKEM768".toUTF8
```

**Status:** ✅ **PROVABLE NOW** — constant evaluation. Effort: 0.25 days.

### PROP-42: KDF_AUTH Info-String Structural Equality [SPEC CORRESPONDENCE]

**Source:** `spec-mlkembraid` (§2.2: `KDF_AUTH` info = `PROTOCOL_INFO ‖
":Authenticator Update" ‖ ToBytes(epoch)`) + `production-code`
(`authenticator.rs:47-48`).

*The HKDF info string assembled by `Authenticator::update` at each call site
matches the spec's § 2.2 `KDF_AUTH` recipe byte-for-byte.*

This is the parallel of PROP-24a (which covers `KDF_OK` info-string equality)
for the `KDF_AUTH` derivation. PROP-32 captures the *parameter deviation*
(salt/IKM swap); this property captures the *info-string correctness* —
orthogonal to the deviation.

**Lean encoding:**

```
theorem authenticator_update_info_form (auth : Authenticator) (ep : Epoch) (k : Slice U8) :
    let info := PROTOCOL_INFO ++ b":Authenticator Update" ++ ep.to_be_bytes
    -- Authenticator.update calls hkdf_to_vec with this info
    Authenticator.update auth ep k ⦃ auth' =>
      auth'.was_derived_with_info info ⦄
```

(The exact Lean encoding depends on whether the info string is extracted as a
visible intermediate or needs to be reconstructed from the `hkdf_to_vec` call
arguments.)

**Status:** ⚠️ **FEASIBLE** — requires inspecting the extracted
`Authenticator.update` body to confirm the info bytes are visible. Effort:
0.5 days.

### PROP-43: Authentication Failure State Preservation [CONDITIONAL BEHAVIORAL SPEC]

**Source:** `spec-mlkembraid` (§2.4: "In the event of a verification failure,
protocol participants should not proceed with the ML-KEM Braid session and
should negotiate a new ML-KEM Braid session") + `production-code`
(MAC failure returns `Err`, and Rust ownership semantics consume `self` by
value in `recv_ct2`/`recv_header`, preventing partial state mutation from
leaking).

*When `verify_ct` or `verify_hdr` fails (MAC mismatch), the SPQR state is not
advanced — the error propagates and the pre-call state is preserved.*

**Available in Lean extraction:**

- `v1.unchunked.send_ek.EkSentCt1Received.recv_ct2` — extracted; calls
  `auth.update(...)` then `auth.verify_ct(...)`. If `verify_ct` fails, the
  function returns `Err` and the consumed `self` is dropped.
- `v1.unchunked.send_ct.NoHeaderReceived.recv_header` — extracted; similar
  pattern with `verify_hdr`.

**Lean encoding:**

```
theorem recv_ct2_mac_failure_no_state_change
    (s : send_ek.EkSentCt1Received) (msg : Message)
    (h_mac_fail : auth.verify_ct epoch ct mac = Err e) :
    States.recv (States.EkSentCt1Received s) msg ⦃ r =>
      r = Err e ⦄
```

**Lean provability:**

| Aspect | Assessment |
|--------|------------|
| **Difficulty** | Easy-Medium — follows from the `Result` monad's short-circuit semantics |
| **Key insight** | In Lean's pure-functional model, `Err` in the `Result` monad propagates without modifying state. The Aeneas extraction makes this explicit: `verify_ct` failure causes a `bind` to return `Err`, skipping all subsequent state mutations. |
| **Dependencies** | None — purely structural over the extracted monadic code |
| **Status** | ✅ **PROVABLE NOW** |
| **Estimated effort** | 1 day (covers both `recv_ct2` and `recv_header` paths) |

### PROP-44: `Ct1Acknowledged.Receive` Accepts `Ek` Chunks [DEVIATION FLAG]

**Source:** `production-code` (`src/v1/chunked/states.rs:489-510`, with in-code
comment: "If we got all messages in order, we would never receive a msg.ek at
this point ... However, we can get messages out of order, so let's use the
msg.ek chunks if we get them.") + `spec-mlkembraid` (§2.5,
`Ct1Acknowledged.Receive`: only `EkCt1Ack` is handled; `Ek` payloads are not
mentioned).

*The Rust code in `Ct1Acknowledged.Receive` accepts `Ek` payload chunks and
feeds them to the `ek_decoder`, where the spec only describes handling
`EkCt1Ack` payloads.*

**⚠ Spec deviation flag.** This is a conservative extension: accepting
out-of-order `Ek` chunks in `Ct1Acknowledged` can only help recovery and
cannot cause incorrect decapsulation (the SHA3-256 integrity check on the
reassembled `ek_vector` is still performed before `Encaps2`, per PROP-25).
However, the spec does not describe this behavior, so a spec-compliant peer
that logs or counts unexpected message types would see messages the spec says
should not appear in this state. The deviation is worth documenting — either
in the spec as a permitted optimization or in the code as a justified extension.

**Lean encoding:**

```
theorem ct1_acknowledged_accepts_ek (s : Ct1Acknowledged) (msg : Message)
    (h_epoch : msg.epoch = s.epoch)
    (h_payload : msg.payload = MessagePayload.Ek chunk) :
    States.recv (States.Ct1Acknowledged s) msg ⦃ r =>
      ∃ s', r = ok (Recv { state = States.Ct1Acknowledged s', key = None, .. }) ⦄
```

**Status:** ✅ **PROVABLE NOW** — structural, 0.5 days.

---

## Missing Pieces and Blockers

### Blocker 1: `lib.rs` Not Extracted

The top-level `send` / `recv` / `initial_state` functions in `src/lib.rs` are not in the
`start_from` list of `aeneas-config.yml`. This blocks:

- PROP-1 at the API level (chain key agreement)
- PROP-16 (version negotiation)
- PROP-27 (initialization correctness)

**Fix:** Add `"spqr::lib"` or the specific function paths to `start_from`, then resolve any
Charon issues (version negotiation branches are complex but don't use deep generic crates).

### Blocker 2: `encaps2` Opaque

`incremental_mlkem768::encaps2` is opaque because it calls
`potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275`, which is marked
`#[hax_lib::opaque]`. That helper contains `log::info!` / `log::warn!` macros under
`#[cfg(not(hax))]`. The `encaps2` function body itself has no logging. This blocks PROP-3
(KEM roundtrip as a theorem rather than axiom).

**Fix:** Address the `potentially_fix_state*` helper's opacity — either provide a
`#[cfg(hax)]` alternative that omits the logging side-effects, or remove `#[hax_lib::opaque]`
from the helper and gate the `log::*` calls so Charon/Aeneas can extract the body. Since the
endianness fix is cryptographically relevant (it affects the encapsulation state), the correct
approach is to make the fix logic visible to the extraction while omitting only the logging.

### Blocker 3: `hkdf_to_slice` Opaque

HKDF/SHA2 generic trait hierarchies cause Charon to hang at MIR analysis before config flags
are applied. This makes `hkdf_to_slice` opaque. This blocks PROP-18 (panic
freedom) as a theorem and means any future theorem trying to discharge the
HKDF modelling assumptions would need an explicit axiom set.

**Fix:** Create a thin `#[cfg(hax)]` wrapper around `hkdf::Hkdf::expand` that gives Charon a
simpler type signature. Alternatively, accept `hkdf_to_slice` as a permanently opaque function
and specify its properties via a small axiom set (determinism + domain separation + success).

### Blocker 4: GF16 Multiplication Open Sorries

`mul_spec`, `poly_reduce_spec`, `polyMod_eq_polyMod_poly`, and `polyMod_poly_eq_modByMonic` are
sorry'd in the Specs. These block:

- `LEAN-GF-7` (GF16 mul end-to-end correctness)
- Any proof that depends on GF16 multiplication being a field operation

**Fix:** The mathematical framework is in place. The remaining work:
1. Connect the precomputed `REDUCE_BYTES` table to `reduceFromByte` (concrete computation).
2. Prove `polyMod_poly p n = p %ₘ POLY_GF2` using `Polynomial.modByMonic_eq_iff_isRoot` or
   degree-induction in Mathlib.
3. Prove `polyMod_eq_polyMod_poly` by induction on `n`.
4. Compose to get `mul_spec` from `poly_mul_spec` + `poly_reduce_spec`.

### Open Gaps Beyond the Numbered Catalog

**GAP-A: Full v1 state-machine transition matrix.**
The numbered properties cover the most critical guards (PROP-22a/b, PROP-26,
PROP-30) and the `Ct1Ack` deviations (PROP-33, PROP-34). What is *not* yet
enumerated is the full 11×11 reachable-state-pair matrix — i.e., a mechanical
witness that every reachable pair has the spec's prescribed transition (or, for
the deviation pairs, the code's prescribed transition). This would be roughly
22 send-arms × 22 recv-arms ≈ 500 case obligations, most of them trivial. Worth
deferring until the targeted state-machine properties are stable.

**GAP-B: `hkdf_to_vec` / `hkdf_to_slice` relationship.**
`kdf::hkdf_to_vec` wraps `kdf::hkdf_to_slice` (the latter being opaque). Any
HKDF proof that flows through `hkdf_to_vec` needs a one-line unfolding lemma
`hkdf_to_vec salt ikm info len = (hkdf_to_slice salt ikm info buf).toVec` at
the start. This is mechanical and best handled inline at each proof site rather
than as a standalone property.

**GAP-C: Per-message-key uniqueness.**
The chain produces per-message keys via `(epoch, index)` indexing. No property
asserts that distinct `(epoch, index)` pairs produce distinct `MessageKey`
outputs from `Chain::send_key` / `Chain::recv_key`. This reduces to
`KeyHistory` well-formedness (PROP-12a/PROP-12b) plus the HKDF collision-
infeasibility assumption (PROP-4 modelling assumption); no separate ordering
invariant is needed because `KeyHistory::remove` is not order-preserving.

**GAP-D: SHA3-256 spec equivalence of `validate_pk_bytes`.**
PROP-3b axiomatises this; if libcrux's `validate_pk_bytes` is brought under the
extraction (or a stub model is provided), it can become a discharged theorem.

---

## Soundness Notes

### Axiom-Set Coherence

The Lean development relies on the following axiom families:

1. **HKDF axioms:** `hkdf_to_slice_deterministic`, `hkdf_to_slice_succeeds`
   (PROP-18), `hkdf_no_collision_modelling_assumption` (PROP-4).
2. **KEM axioms:** `kem_roundtrip` with `(dk, ek_seed, ek_vector) = generate(seed)`
   binding (PROP-3).
3. **SHA3 axiom:** `validate_pk_bytes` spec equivalence (PROP-3b).
4. **Opaque function stubs:** `hkdf_to_slice`, `encaps2`, `decoded_message`,
   `validate_pk_bytes`, `libcrux_hmac::hmac`, `mul2_u16`, `MulAssign<&GF16>`,
   plus proto `Message` impls — all `axiom` declarations in `FunsExternal.lean`.

These axioms must be checked for mutual consistency. For example, the KEM
roundtrip axiom (PROP-3) combined with the HKDF collision-infeasibility
axiom (PROP-4) should not together imply a contradiction. No specific
inconsistency has been identified, but the following risks warrant attention:

- **PROP-4/7/8/24b modelling assumptions are technically inconsistent with
  a mathematical model of HKDF.** HKDF is a deterministic function, so
  `distinct inputs → distinct outputs` (strict injectivity) is false — collisions
  exist with nonzero probability. The axioms adopt the *infeasibility* of finding
  such a collision, which is standard in symbolic (Dolev-Yao) models but is
  technically unsound in a computational model. The key risk: if these axioms are
  ever composed with a proof that derives a contradiction from `r₁ ≠ r₂` for PRF
  outputs, the entire Lean development becomes unsound. **Mitigation:** keep
  these axioms strictly separated (in a dedicated `Axioms/HKDFModel.lean` file)
  and clearly labeled as cryptographic modelling assumptions.

- **Opaque `axiom` stubs in `FunsExternal.lean`** can be inhabited by `sorry`
  under the hood (they are `axiom` declarations, not Lean `opaque` definitions —
  the distinction matters). If any opaque stub is accidentally inconsistent with
  the rest of the development (e.g., an axiom that fixes a return type to `ok`
  when the real function can return `Err`), proofs using that stub are unsound.

### Sorry Scope in `Funs.lean`

The 43 sorry instances in `Funs.lean` are claimed not to block main proofs.
This is correct for the protocol-level properties (PROP-1 through PROP-44),
none of which depend on the sorry'd definitions (iterators, closures, proto
comparison/merge, and 4 erasure-coding loop bodies). However:

- Any proof whose unfolding path reaches a sorry'd definition is **unsound**
  even if it type-checks. Lean will accept `sorry`-dependent proofs without
  warning unless `#check_no_sorry` is used.
- The 4 sorry'd loop bodies (`parallel_mult_loop`, `lagrange_polys_for_complete_points_loop0`,
  `PolyEncoder::from_pb_loop1`, `PolyEncoder::encode_bytes_base_loop`) **do block**
  LEAN-ENC-2 (erasure-code roundtrip) and any proof that reasons about
  polynomial encoding/decoding internals.
- Recommendation: add `#check_no_sorry` guards to all proof files in
  `Spqr/Specs/` to catch accidental sorry-dependency.

---

## Priority Ranking for Lean Proofs

### Tier 1: Provable Now (no axioms, code is fully extracted)

Already proved (see [Appendix: Proved Properties](#appendix-proved-properties)):
LEAN-GF-1 to GF-4, LEAN-GF-5, LEAN-ENC-1.

| Property | Statement | Source | Effort | Status |
|----------|-----------|--------|--------|--------|
| PROP-9 | `add_epoch`: post-state has `current_epoch = es.epoch` (includes epoch-overflow safety precondition) | `production-code` + `production-test` | 0.5 d | **Start here** |
| PROP-14 | `send_key` rejects decreasing epoch | `production-code` | 0.5 d | **Start here** |
| PROP-17 | `key` rejects key jump (with `at > ctr` precondition) | `production-code` | 0.5 d | **Start here** |
| PROP-17b | `key` returns `KeyAlreadyRequested` on `at == ctr` | `production-code` | 0.25 d | quick win |
| PROP-26 | Ct2Sampled rejects `msg.epoch > epoch + 1` | `spec-mlkembraid` | 0.5 d | **Start here** |
| PROP-29 | `epoch_idx` ↔ `current_epoch` correspondence | `production-code` | 1 d | high priority |
| PROP-30 | `States.recv` Less-branch is no-op | `spec-mlkembraid` | 1 d | high priority |
| PROP-31 | `Authenticator::new` ≡ zero-state.update | `spec-mlkembraid` | 0.5 d | quick win |
| PROP-32 | `Authenticator::update` derivation + spec-deviation flag | `production-code` | 1 d | high priority |
| PROP-33 | Deviation flag: `EkSentCt1Received.send → Ct1Ack(true)` | `production-code` | 0.25 d | quick win |
| PROP-34 | Deviation flag: `EkReceivedCt1Sampled.recv` accepts `Ct1Ack(true)` | `production-code` | 0.25 d | quick win |
| PROP-15 | `verify_ct(mac_ct(ep, ct))` succeeds | `production-code` | 1 d | high priority |
| PROP-15b | `verify_hdr(mac_hdr(ep, hdr))` succeeds | `production-code` | 0.5 d | quick win |
| PROP-25 | `recv_ek` rejects mismatched EK/header (call-site level, all 3 transitions) | `spec-mlkembraid` | 1 d | high priority |
| PROP-22 | Epoch agreement (22a + 22b structural state-machine claim) | `spec-mlkembraid` | 2 d | high priority |
| PROP-21 | Only `HeaderReceived.send_ct1` + `EkSentCt1Received.recv_ct2` emit a key | `spec-mlkembraid` | 1 d | medium priority |
| PROP-12a | `KeyHistory.data.length % KEY_SIZE == 0` invariant | `production-code` | 1 d | medium priority |
| PROP-36 | `Message.deserialize` rejects `epoch == 0` | `production-code` | 0.25 d | quick win |
| PROP-39 | `States.recv` Greater-branch returns `EpochOutOfRange` (10 non-`Ct2Sampled` variants) + deviation flag | `production-code` + `spec-mlkembraid` | 1 d | high priority |
| PROP-40a/b | MAC input byte-form matches spec §2.4 for `mac_hdr` and `mac_ct` | `spec-mlkembraid` + `production-code` | 0.5 d | high priority |
| PROP-41 | `PROTOCOL_INFO` byte-form regression check + deviation flag | `production-code` + `spec-mlkembraid` | 0.25 d | quick win |
| PROP-43 | MAC failure → state preserved (no partial advance) | `spec-mlkembraid` + `production-code` | 1 d | high priority |
| PROP-44 | Deviation flag: `Ct1Acknowledged.recv` accepts `Ek` chunks | `production-code` | 0.5 d | quick win |

### Tier 2: Axiom-backed Proof Goals (code extracted)

**Soundness reminder.** Properties marked **🔶 modelling** depend on
collision-infeasibility postulates flagged as cryptographic-modelling
assumptions; those assumptions are listed separately below.

| Property | Source | Required axiom(s) / effort | Effort |
|----------|--------|---------------------------|--------|
| PROP-3 | `hax-cross` + `production-test` | KEM roundtrip with `(dk, ek_seed, ek_vector) = generate(seed)` binding | 0.5 d |
| PROP-3b | `spec-mlkembraid` | `ek_matches_header ↔ SHA3-256(ek_seed‖ek_vector) = hek` axiom on libcrux's `validate_pk_bytes` | 0.5 d |
| PROP-24a | `spec-mlkembraid` | none (call-site syntactic equality) | 0.5 d |
| PROP-18 | `production-code` | `hkdf_to_slice` succeeds for `len ≤ 8160` | 0.5 d |
| PROP-10 | `production-code` + `production-test` | none (structural erasure proof) | 2-3 d |
| PROP-12b | `production-code` | **BLOCKED** by `KeyHistory.get`/`gc` opacity — requires de-opaquing or axiomatisation | 3 d (after unblocking) |
| PROP-42 | `spec-mlkembraid` + `production-code` | none (KDF_AUTH info-string structural equality) | 0.5 d |
| PROP-23 | `spec-mlkembraid` | Chain structural invariant + PROP-9, PROP-29 | 3-4 d |
| PROP-37 | `production-code` | none (case-split over 11 variants) | 3-4 d |
| PROP-35 | `production-code` | none above the encode/decode loop sorries | 2-3 d |

**Modelling assumptions (not counted as correctness properties).**

| Assumption | Source | Role |
|------------|--------|------|
| PROP-4 | `hax-cross` + `production-code` | HKDF collision-infeasibility / domain-separation model for authenticator and chain HKDF uses. |
| PROP-7 | `hax-cross` + `production-test` | Same modelling assumption, specialized to successive chain keys. |
| PROP-8 | `hax-cross` + `production-code` | Same modelling assumption, specialized to the root-key ratchet across epochs. |
| PROP-24b | `spec-mlkembraid` + `production-code` | Same modelling assumption, specialized to epoch-bound `KDF_OK` outputs. |

### Tier 3: Feasible with Infrastructure Work

| Property | Source | Required infrastructure | Effort |
|----------|--------|------------------------|--------|
| LEAN-GF-6/7 | `lean-specific` | Close `poly_reduce_spec` sorry chain | 3-5 d |
| PROP-1 (v1 layer) | `production-test` + `spec-mlkembraid` | Axioms (PROP-3, PROP-3b) + `EpochSecret` equality proof | 5-7 d |
| LEAN-ENC-2 | `lean-specific` | Lift `PolyDecoder::decoded_message` opacity or axiomatize | 2-3 d |

### Tier 4: Blocked by Missing Extraction

| Property | Source | Blocker | Fix |
|----------|--------|---------|-----|
| PROP-1 (API level) | `production-test` + `spec-mlkembraid` | `lib.rs` not extracted | Add to `start_from` |
| PROP-16 | `production-code` + `production-test` | `lib.rs` not extracted | Add to `start_from` |
| PROP-27 | `spec-mlkembraid` (§2.6) | `lib.rs` not extracted | Add to `start_from` |
| PROP-12b | `production-code` | `KeyHistory.get` / `KeyHistory.gc` are `#[hax_lib::opaque]` | Remove `#[hax_lib::opaque]` and re-extract, or axiomatise |
| PROP-38 | `production-code` | `Chain::into_pb` / `Chain::from_pb` are `#[hax_lib::opaque]` | Provide indexed-loop alternative under `#[cfg(hax)]` |

---

## Recommended Approach

### Phase 1: Production & Spec Guards (≈ 12 days, no axioms)

Highest-value, fully-extracted, all Tier-1:

1. **PROP-9** (`add_epoch_ok` — post-state has `current_epoch = es.epoch`, includes overflow-safety precondition) — 0.5 d
2. **PROP-14** (`send_key_epoch_guard`) — 0.5 d
3. **PROP-17** (`key_jump_guard` with `at > ctr` precondition) + **PROP-17b** (`KeyAlreadyRequested` on equality) — 0.75 d
4. **PROP-26** (`ct2_sampled_future_epoch_guard`) — 0.5 d
5. **PROP-29** (`epoch_idx` correspondence) — 1 d
6. **PROP-30** (`States.recv` Less-branch no-op) + **PROP-39** (Greater-branch `EpochOutOfRange` + deviation flag) — 2 d
7. **PROP-31** (`Authenticator::new ≡ zero-state.update`) — 0.5 d
8. **PROP-32** (`Authenticator::update` derivation + spec-deviation flag) — 1 d
9. **PROP-15** (`verify_ct_mac_roundtrip`) + **PROP-15b** (`verify_hdr_mac_roundtrip`) — 1.5 d
10. **PROP-40a/b** (MAC input byte-form correspondence with spec §2.4) — 0.5 d
11. **PROP-25** (`recv_ek_rejects_mismatched` on all 3 spec transitions) — 1 d
12. **PROP-22** (epoch agreement: 22a + 22b deeper form) — 2 d
13. **PROP-21** (only two transitions emit a key) — 1 d
14. **PROP-33** + **PROP-34** + **PROP-44** (deviation flags: Ct1Ack routing, Ek acceptance) — 0.75 d
15. **PROP-43** (MAC failure state preservation) — 1 d
16. **PROP-12a** (`KeyHistory.data.length` invariant) — 1 d
17. **PROP-36** (`deserialize` rejects `epoch == 0`) — 0.25 d
18. **PROP-41** (`PROTOCOL_INFO` byte-form regression check + deviation flag) — 0.25 d

### Phase 2: Axiom-Based Protocol Properties (≈ 7 days)

19. **Axiom set**: HKDF-Expand `len ≤ 8160` succeeds; KEM-roundtrip (PROP-3) with binding; SHA3-256-equivalence of `validate_pk_bytes` (PROP-3b). Separate modelling assumptions: PROP-4, PROP-7, PROP-8, PROP-24b — 1.5 d
20. **PROP-3** + **PROP-3b** axioms — 1 d
21. **PROP-18** (HKDF expand safety) — 0.5 d
22. **PROP-24** (KDF_OK post-processing: 24a structural + 24b modelling) — 1.5 d
23. **PROP-42** (KDF_AUTH info-string structural equality) — 0.5 d
24. **PROP-10** (forward-secrecy structural erasure) — 2-3 d

### Phase 3: SCKA Correspondence Properties (≈ 4 days)

25. **PROP-23** (sender/receiver epoch knowledge) — 3-4 d

### Phase 4: KeyHistory and Serialization Layer (≈ 8-10 days)

26. **PROP-12b** (functional roundtrip of `get` after `add` — **blocked** until `KeyHistory.get`/`gc` de-opaqued) — 3 d
27. **PROP-37** (`States.from_pb ∘ into_pb = id`) — 3-4 d
28. **PROP-35** (`Message` wire-format roundtrip, modulo encode/decode loop sorries) — 2-3 d

### Phase 5: Close Open Sorries (≈ 5 days)

29. **LEAN-GF-6**: `polyMod_eq_polyMod_poly` by induction — 2 d
30. **LEAN-GF-6**: `polyMod_poly_eq_modByMonic` via Mathlib — 2 d
31. **LEAN-GF-7**: `poly_reduce_spec` + `mul_spec` — 1-2 d (depends on 29-30)

### Phase 6: Infrastructure for Top-Level API (≈ 9 days)

32. Add `lib.rs` to `start_from` in `aeneas-config.yml` and resolve issues — 2 d
33. Fix `encaps2` opacity via `potentially_fix_state*` helper (see Blocker 2) — 1 d
34. Provide indexed-loop variants for `Chain::into_pb` / `from_pb` to lift opacity — 1 d
35. De-opaque `KeyHistory.get` / `KeyHistory.gc` (unblocks PROP-12b) — 1 d
36. **PROP-1** (chain key agreement at v1 layer) — 5-7 d
37. **PROP-27** (initialization correctness, unlocked by lib.rs) — 0.5 d
38. **PROP-38** (`Chain` proto roundtrip, after step 34) — 1 d

### Phase 7: Erasure Code Layer (≈ 3 days)

39. **LEAN-ENC-2** (full erasure-code roundtrip) — 2-3 d

### Total estimated effort: 48-57 days

This produces (on top of the already-proved LEAN-GF-1..5 and LEAN-ENC-1):

- **21 Tier-1 fully-discharged proofs** (Phase 1), including the 6 new properties
  (PROP-39 through PROP-44) that close gaps identified in the spec-coverage analysis.
- **Axiom-backed protocol goals**, with explicit HKDF modelling assumptions separated out
  (Phase 2), plus KDF_AUTH info-string verification (PROP-42).
- **1 SCKA spec-correspondence proof** (PROP-23, Phase 3).
- **1 functional KeyHistory proof** (blocked until de-opaqued) and **2 serialization roundtrips** (Phase 4).
- Closed GF16 multiplication sorry chain (Phase 5).
- **1 chain-key-agreement correspondence proof** at the v1 layer (PROP-1),
  **3 lib.rs-level properties** unblocked by the extraction work, and
  `KeyHistory.get`/`gc` de-opaquing to unblock PROP-12b (Phase 6).
- **1 erasure-code roundtrip** (Phase 7).

**Five properties marked as deviation flags** (PROP-32, PROP-33, PROP-34, PROP-39,
PROP-44) provide a *change-detection* artifact: if the production code is brought
into line with the spec, or the spec is amended, these properties will fail and
signal the change. Two more (PROP-35 wire format, PROP-37 proto roundtrip)
serve the same purpose for serialization regressions. PROP-41 (PROTOCOL_INFO
byte-form) serves as a constant-regression check and deviation flag.

---

## Appendix: Lean Code Pointers

### Generated Files (Aeneas output, `Spqr/Code/`)

| File | Content |
|------|---------|
| `Types.lean` | All struct/enum type definitions (chain, authenticator, v1 states, proto, encoding) |
| `Funs.lean` | All function definitions (~14 000 lines); 43 sorry instances |
| `FunsExternal.lean` | External (opaque) function stubs |
| `TypesExternal.lean` | External type stubs |

### Proof Files (hand-written, `Spqr/Specs/`)

| File | Proved theorems |
|------|----------------|
| `Encoding/Gf/GF16/AddAssign.lean` | `add_assign_spec` (GF216 add = XOR) ✅ |
| `Encoding/Gf/GF16/Add.lean` | `add_spec` (by-value add) ✅ |
| `Encoding/Gf/GF16/Sub.lean` | `sub_spec` (GF216 sub = XOR) ✅ |
| `Encoding/Gf/GF16/Eq.lean` | `eq_spec`, `gf16_eq_iff` ✅ |
| `Encoding/Gf/Unaccelerated/PolyMul.lean` | `poly_mul_loop_spec`, `poly_mul_spec`, `poly_mul_spec'`, `clmul_eq_clmul_poly`, `clmul_poly_eq_mul` ✅ |
| `Encoding/Gf/Reduce/PolyReduce.lean` | `polyMod_eq_polyMod_poly` ⚠️ sorry, `polyMod_poly_eq_modByMonic` ⚠️ sorry, `poly_reduce_spec` ⚠️ sorry |
| `Encoding/Gf/Unaccelerated/Mul.lean` | `mul_spec` ⚠️ sorry |
| `Encoding/Polynomial/Pt/Serialize.lean` | `serialize_spec`, `to_be_bytes_spec` ✅ |
| `Encoding/Polynomial/Pt/Deserialize.lean` | `deserialize_spec`, `from_be_bytes_spec`, `try_from_spec` ✅ |
| `Math/Basic.lean` | `abbrev GF216 := GaloisField 2 16` definition (uses `abbrev`, not `def`) |

### Key Lean Functions to Target Next

Function paths are stable (Rust source); line numbers reference Rust source
files where possible. `Funs.lean` line numbers were dropped from this revision
because they drift on every Aeneas re-extraction.

| Priority | Rust source | Property to prove |
|----------|-------------|-------------------|
| High | `src/chain.rs::Chain::add_epoch` (`:350-369`) | PROP-9 |
| High | `src/chain.rs::Chain::send_key` (`:384-407`) | PROP-14 |
| High | `src/chain.rs::Chain::epoch_idx` (`:372-382`) | PROP-29 |
| High | `src/chain.rs::ChainEpochDirection::key` (`:247-296`) | PROP-17, PROP-17b |
| High | `src/authenticator.rs::Authenticator::verify_ct/verify_hdr` (`:57-103`) | PROP-15, PROP-15b |
| High | `src/authenticator.rs::Authenticator::new/update` (`:35-54`) | PROP-31, PROP-32 |
| High | `src/v1/chunked/states.rs::States::recv` Ct2Sampled arm (`:513-526`) | PROP-26 |
| High | `src/v1/chunked/states.rs::States::recv` Less-branches + Greater-branches | PROP-30, PROP-39 |
| High | `src/v1/unchunked/send_ct.rs::Ct1Sent::recv_ek` (`:152-172`) and chunked call paths in `src/v1/chunked/send_ct.rs:177,266` | PROP-25 |
| High | `src/v1/chunked/states.rs::States::send` / `States::recv` (all arms) | PROP-21, PROP-22 |
| High | `src/authenticator.rs::Authenticator::mac_hdr/mac_ct` (`:68-79`) | PROP-40a, PROP-40b |
| High | `src/v1/unchunked/send_ek.rs::recv_ct2` (`:155-160`) and `send_ct.rs::recv_header` | PROP-43 |
| Medium | `src/v1/chunked/states.rs::States::send` `EkSentCt1Received` arm (`:178-184`) and `States::recv` `EkReceivedCt1Sampled` arm (`:464-477`) | PROP-33, PROP-34 |
| Medium | `src/v1/chunked/states.rs::States::recv` `Ct1Acknowledged` arm (`:489-510`) | PROP-44 |
| Medium | `src/chain.rs::KeyHistory::*` (`:130-208`) | PROP-12a, PROP-12b |
| Medium | `src/chain.rs::Chain::send_key` `links.pop_front` / `clear_next` (`:391-399`) | PROP-10 |
| Medium | `src/chain.rs::Chain::*` + `src/chain.rs::KeyHistory::*` | PROP-23 |
| Medium | `src/v1/chunked/states/serialize.rs::Message::serialize/deserialize` (`:204-279`) | PROP-35, PROP-36 |
| Medium | `src/v1/chunked/states/serialize.rs::States::into_pb/from_pb` (`:11-93`) | PROP-37 |
| Low | `src/v1/chunked/states.rs::States::send/recv` (top-level) | PROP-1 v1 layer |

---

## Appendix: Proved Properties

The following properties have been fully proved in Lean. They are included here for
completeness; the main catalog above focuses on unverified properties.

### LEAN-GF-1: GF16 Addition Correctness [COMPLETE]

**Source:** `lean-specific` — derived from `encoding/gf.rs` during Lean extraction and proof work.

**Statement:** `GF16::add_assign(a, b).value = a.value + b.value` in GF(2¹⁶).

**Lean file:** `Spqr/Specs/Encoding/Gf/GF16/AddAssign.lean`

**Status:** ✅ **PROVED** — `add_assign_spec`

```lean
theorem add_assign_spec (self other : spqr.encoding.gf.GF16) :
    add_assign self other ⦃ result =>
      (result.value : GF216) = self.value + other.value ⦄
```

The proof connects `self.value ^= other.value` (bitwise XOR) to `+` in `GaloisField 2 16`
via `CharP.natCast_eq_natCast'` and `Nat.xor_mod_two_eq`.

### LEAN-GF-2: GF16 Addition by Value [COMPLETE]

**Source:** `lean-specific`

**Status:** ✅ **PROVED** — `add_spec` in `Add.lean`

### LEAN-GF-3: GF16 Subtraction Correctness [COMPLETE]

**Source:** `lean-specific`

**Status:** ✅ **PROVED** — `sub_spec` in `Sub.lean`. GF(2¹⁶) subtraction = addition (XOR).

### LEAN-GF-4: GF16 Equality [COMPLETE]

**Source:** `lean-specific`

**Status:** ✅ **PROVED** — `eq_spec` + `gf16_eq_iff` in `Eq.lean`.

### LEAN-GF-5: GF16 Carry-Less Multiplication Loop [COMPLETE]

**Source:** `lean-specific`

**Status:** ✅ **PROVED** — `poly_mul_loop_spec`, `poly_mul_spec`, and `poly_mul_spec'` in
`Unaccelerated/PolyMul.lean`.

The key lemmas `clmul_eq_clmul_poly` and `clmul_poly_eq_mul` connect the bit-level loop to
polynomial multiplication in `(ZMod 2)[X]`, using Mathlib's polynomial ring theory.
`poly_mul_spec'` additionally relates `poly_mul` to bit-level `clmul` with width 16.

### LEAN-ENC-1: Point Serialize/Deserialize Roundtrip [COMPLETE]

**Source:** `lean-specific` — derived from `encoding/polynomial.rs` during extraction work.

**Statements:**
- `serialize_spec`: result encodes x/y as big-endian `u16` bytes
- `deserialize_spec`: result reconstructs x/y from big-endian bytes
- Roundtrip: `deserialize(serialize(pt)) = ok pt`

**Lean files:** `Specs/Encoding/Polynomial/Pt/Serialize.lean`, `…/Deserialize.lean`

**Status:** ✅ **PROVED** — both specs proven; roundtrip follows by composition.
