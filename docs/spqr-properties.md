# SPQR correctness properties

This document lists the correctness properties of the SPQR implementation
(`src/`), each grounded in the ML-KEM Braid specification, the SCKA paper, or
the code itself, together with its verification status in Lean.

References:

- **Spec**: R. Schmidt, *The ML-KEM Braid Protocol*, Rev. 1, last updated
  2025-09-26 (`mlkembraid.pdf`). Section numbers below refer to it.
- **SCKA**: Auerbach, Dodis, Jost, Katsumata, Schmidt, *How to Compare
  Bandwidth Constrained Two-Party Secure Messaging Protocols* (`2025-2267.pdf`).
  Def. 3.1 and Fig. 1 give the formal SCKA interface and correctness game the
  spec defers to in §1.1.
- **Code**: `src/` at `dd8e6b9`, which carries Signal SPQR v1.6.0 (upstream `06959b4`).
  Line numbers refer to that commit. Until 2026-10-15 the catalog cited `d47083c`.
- **Lean**: `Spqr/Specs/` at the same commit. Aeneas output is in `SrcTranslated/`.

Status values:

| Status | Meaning |
|--------|---------|
| Proved | Theorem on `main`, no `sorry`, and no hand-written axiom beyond the six §1 documents: `hkdf_to_slice_spec`, `encode_state_pb_spec`, `decode_state_pb_total`, `libcrux_hmac.hmac_sha256_tag32_spec`, `KeyPairCompressedBytes.from_seed_spec` and `alloc.fmt.format_spec`. Closures can also contain the Aeneas library's `core.fmt.Formatter` axiom and `native_decide` artifacts of extracted definitions, and `bv_decide` artifacts (ruling S-16, extended 2026-10-15). §1 carries each one's location, postcondition and whether it is avoidable; this cell names them only so that a `Proved` row can be checked against its own definition |
| Proved (branch) | Theorem exists only on a branch, not on `main`: `la/lean-v1-protocol-proofs` (draft PR #46) or a property branch (`la/prop-<n>`). The proofs on `la/lean-v1-protocol-proofs` also use the liveness axioms in that branch's `Spqr/Specs/External.lean`, three of which assert that defined functions (`PolyEncoder.next_chunk`, `KeysUnsampled.send_hdr_chunk`, `HeaderReceived.send_ct1_chunk`) never fail. The last two are false as stated, since both reach `generate`, which can fail; they need a premise, not just a proof. Merging them requires replacing all three with theorems. A property branch adds no axiom; its row says what its closure contains. |
| Open | Statement fixed, no theorem yet |
| Axiom | Cannot be a theorem: the code calls an opaque library function |

One case needs saying, because `Open` as defined above assumes the statement is
settled. An `Open` row that also carries a `Finding:` annotation has a statement
that is **known wrong** and is being restated in a named later phase, so `Open`
there means "no theorem *and* no settled statement". PROP-37 is the row this
covers. No new status value is introduced: the §12 index vocabulary is unchanged,
and a `Domain:` or `Finding:` line never changes a row's status by itself.

Property IDs are stable identifiers shared with the issue tracker. Gaps in
the numbering are retired items.

---

## 1. Verification setup

Aeneas extracts the whole crate (`aeneas-config.yml` has no `start_from`),
including `lib.rs` `initial_state`, `send`, `recv`. The extracted code is `src/`
with the 25 patches in `translation-patches/` applied (each states why and claims
identical behaviour, apart from logging), and without the items listed under
`[package.metadata.charon] exclude` in `Cargo.toml` (`gf::accelerated`,
`gf::check_accelerated`, `log`, some prost-derived impls). The patches'
"identical behaviour" claims are reviewed, not proved, and belong to the trusted
base. Specs are written in
weakest-precondition style over the `Result` monad:
`f args ⦃ r => P r ⦄` means `f args` succeeds and its value satisfies `P`.

Opaque items and how they are handled:

| Item | Handling |
|------|----------|
| `kdf::hkdf_to_slice` | Lean `noncomputable opaque` (`SrcTranslated/FunsExternal.lean:2336`); behaviour given by `axiom hkdf_to_slice_spec` (`Spqr/Specs/Kdf/HkdfToSlice.lean:29`) in terms of an RFC 5869 model with `opaque HMAC_SHA256`. One of three hand-written axioms under `Spqr/` (the other two are in the prost row below). |
| `incremental_mlkem768::potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275` | Opaque stub (`noncomputable opaque`, `SrcTranslated/FunsExternal.lean:2343`; contains `log::*` under `cfg(not(hax))`). `encaps2` itself is extracted. |
| `PolyDecoder::decoded_message` | Extracted (`SrcTranslated/Funs.lean:8804`) from a patched body (`translation-patches/polynomial-PolyDecoder-decoded_message.patch`). No spec yet; LEAN-ENC-2 is no longer blocked by an axiom. |
| libcrux `validate_pk_bytes`, `decapsulate_compressed_key`, `encapsulate1/2`, `hmac`, size constants | Opaque stubs (`noncomputable opaque` in `SrcTranslated/FunsExternal.lean`), not axioms: `hmac` (`:1626`), `encapsulate1/2` (`:1872`, `:1734`), `decapsulate_compressed_key` (`:1884`), `validate_pk_bytes` (`:1863`), and the size constants `pk1_len`, `pk2_len`, `encaps_state_len`, `Ciphertext1/2::len`, `SHARED_SECRET_SIZE` (`:1684-1728`). Built against libcrux-ml-kem 0.0.10 and libcrux-hmac 0.0.8. |
| `libcrux_hmac.hmac_sha256_tag32_spec` | **Hand-written** `@[step] axiom` at `SrcTranslated/FunsExternal.lean:1673`, not an aeneas signature stub: it carries a postcondition, namely that the returned tag is 32 bytes (`⦃ (r : alloc.vec.Vec U8) => r.length = 32 ⦄`). **Unavoidable**: `libcrux_hmac.hmac` is itself opaque, so there is nothing to prove the postcondition from. Specialised to `.Sha256` with `some 32#usize`, the only shapes the crate calls, so it adds no surplus assumption. Not unsound. It is in the axiom closure of `mac_hdr_spec` and `mac_ct_spec`, which carry PROP-40's **Proved** status. |
| `KeyPairCompressedBytes.from_seed_spec` | **Hand-written** `@[step] axiom` at `SrcTranslated/FunsExternal.lean:1751`, postcondition `⦃ fun kp => kp.value.length = mlkem768Params.decapsulationKeyBytes ⦄`. **Avoidable**: `from_seed` is a `def` returning `ok default`, and `value` is a length-indexed array (`SrcTranslated/TypesExternal.lean:140`), so the postcondition follows from `Array.length_eq` — the same one-liner already used at `SrcTranslated/FunsExternal.lean:1769`. It is an axiom today only because it was written as the `-- TODO: add cryptographic properties of from_seed_spec` placeholder, not because of any obstruction; it is true, hence not unsound. It is in the axiom closure of `generate_spec`, which `docs/proof-targets.md:97` records as discharged at baseline. **Retiring it is Phase 4 work under AXIOM-01..06.** |
| prost `Message` impls for `PqRatchetState` | Not reached by any proof. `lib.rs` routes all state encoding and decoding through `encode_state_pb` / `decode_state_pb` (patch `lib-state_pb.patch`; `noncomputable opaque` at `SrcTranslated/FunsExternal.lean:2352,2357`). **Hand-written** axioms `encode_state_pb_spec` (`Spqr/Specs/Lib/StatePb.lean:40`: encoding succeeds and decodes back to the encoded state) and `decode_state_pb_total` (`:45`: decoding never panics). **Unavoidable** while prost is opaque. That prost's encode/decode round-trips `PqRatchetState` is assumed, not checked here. Admitted to the gate-4 allowlist 2026-10-15 (user decision; block "Trusted base added on main, admitted 2026-10-15"). |
| `alloc::fmt::format` | **Hand-written** `@[step] axiom alloc.fmt.format_spec` at `SrcTranslated/FunsExternal.lean:1209`: formatting succeeds, the string is unspecified. Needed because upstream v1.6.0 builds error strings with `format!` (`src/v1/chunked/states/serialize.rs:116`, `src/lib.rs:183`, both formatting a `u8`). Avoidable only by modelling `alloc.fmt.format`. In the closure of `Message.deserialize_spec` (PROP-35). Admitted to the gate-4 allowlist 2026-10-15 (user decision; block "Trusted base added on main, admitted 2026-10-15"). |

Hand-written `sorry`s on `main`: none (`grep -rn sorry Spqr SrcTranslated` is empty
at `dd8e6b9`). The map-iterator `next := sorry` instance (aeneas#1043) is gone since
the re-extraction (#658). Closures can also contain `bv_decide` artifacts
(`spqr.util.inz_spec._native.bv_decide.ax_1_14`, in `inz_spec` and through it
`verify_hdr_spec` / `verify_ct_spec`). These are covered by ruling S-16 as extended
2026-10-15 to `._native.bv_decide.ax_*` artifacts (user decision).

Layers, from the spec's point of view:

1. **SCKA interface** (§1.1): the properties any SCKA must satisfy.
2. **ML-KEM Braid** (§1.2–§2.6): `src/v1/`, `src/authenticator.rs`,
   `src/incremental_mlkem768.rs`, `src/encoding/`.
3. **Chain and API** (`src/chain.rs`, `src/lib.rs`): the SCKA-to-secure-messaging
   compiler of SCKA §3 / Fig. 2. Outside the spec; properties there are
   grounded in the code only.

How the layers relate to the SCKA paper: ML-KEM Braid is the concrete form of
Opp-UniKEM-CKA (SCKA §4.1, Fig. 16), with the paper's offline/online
encapsulation split into `encaps1` (needs only the header) and `encaps2` (needs
the full key), which is what produces the 11 states. The internal
authenticator (§2.4) has no counterpart in Fig. 16, which relies on the outer
AEAD. In the Fig. 2 compiler, `chain.add_epoch` is the key mix-in,
`chain.send_key`/`recv_key` are the per-epoch sending and receiving chains, and
`ChainParams { max_jump: 25_000, max_ooo_keys: 2_000 }` (`chain.rs:35`) are
its tuning constants.

Provenance (PROV-01). Every property row below carries a `Source:` field, and
every citation in that field must resolve. There are exactly three forms:

- `Source: Spec §x.y` — a section of the ML-KEM Braid document above. Resolved
  against `docs/spec-sections.txt`, which lists every section number of the
  document, transcribed from its table of contents.
- `Source: SCKA Def. n` / `Source: SCKA Fig. n` — a numbered definition or
  figure of the SCKA paper. Resolved against `docs/scka-refs.txt`, transcribed
  the same way.
- `Source: src/path.rs:a-b` — the code at `dd8e6b9`. Resolved by checking that
  the file exists and that lines `a..b` are within it.

A row with more than one ground cites each, semicolon-separated. **Every**
listed citation must resolve: one good citation does not rescue a broken one
beside it. Anything outside the three forms — a `Spqr/Specs/**` lemma, a
planning document — belongs on a separate `Evidence:` line, which is recorded
but not gated. The ML-KEM Braid document's own figures have no citation form of
their own; cite the section that contains the figure.

Gate 5 (`scripts/check-provenance.py`, run by `scripts/check-gates.sh`)
resolves every citation of every row and cross-checks the row IDs against the
§12 index. A row whose provenance cannot be established is marked
`Source: Unsourced - <why>`, which fails the gate deliberately: an unresolvable
row is a finding, not a pass.

---

## 2. SCKA interface (§1.1)

The spec lists five informal properties. SCKA Def. 3.1 gives their formal
shape: `Send → ((t, K), ρ, t_snd)`, `Receive(ρ) → ((t, K), t_rcv)`, where
`(t, K)` is an optional epoch/key pair. In the code the v1 layer returns the
optional key as `EpochSecret { epoch, secret }` and never returns `t_snd` or
`t_rcv`; both are computed in `lib.rs` as `msg.epoch - 1`
(`lib.rs:299`, `lib.rs:462`). On the receive side, `msg` is the preamble that
`msg_preamble` parses (`lib.rs:563-590`). One exception: when the peer's version
byte is above ours, `recv` does not run the v1 machine and returns the chain key of
epoch 0 at the message's index (`lib.rs:383-420`).

### PROP-1 Session key consistency

If both parties output `(t, K)` and `(t, K')`, then `K = K'`.

Source: Spec §1.1; SCKA Def. 3.1

Reduces to: both parties' `EpochSecret.secret` for epoch `t` equal
`KDF_OK(ss, t)` for the same ML-KEM shared secret `ss`, which needs PROP-3
(KEM roundtrip) and PROP-24 (both KDF_OK sites identical). Status: **Open**.
Requires the KEM axiom of PROP-3.

### PROP-21 Per-participant epoch uniqueness

Each party outputs at most one key per epoch.

Source: Spec §1.1; SCKA Fig. 1; src/v1/chunked/states.rs:203-220; src/v1/chunked/states.rs:361-369

Structural part: exactly two arms of the state machine return a key,
`HeaderReceived.send` (spec transition 7, `states.rs:203-220`) and
`EkSentCt1Received.recv` on a completing `Ct2` chunk (transition 5,
`states.rs:361-369`). All other `send` arms and all other `recv` arms return
`key = None`. Trace part: over any run of successful `send`/`recv` calls by one
party, from any starting state, no two emitted keys carry the same epoch (SCKA
Fig. 1, `Send-P` line 14 and `Receive-P` line 7; App. B.1 "Unique epochs"). The
keys come out at consecutive epochs: `HeaderReceived@e` emits `e` and moves to
`Ct1Sampled@e`, whose next key can only be at `e + 1`, and `EkSentCt1Received@e`
emits `e` and moves to `NoHeaderReceived@(e + 1)`.

Theorem: PROP-21 is `spqr.v1.chunked.states.epochs_nodup`, in
`Spqr/Specs/Braid/Scka/EpochUniqueness.lean`. The Lean names and docstrings do not
carry the ID; this row is the mapping.

Status: **Proved** (#574, on `main`) in `Spqr/Specs/Braid/Scka/EpochUniqueness.lean`. The structural part is
`send_key_epoch` and `recv_key_epoch` (only these arms can emit) with their converses
`send_HeaderReceived_key_isSome` and `recv_EkSentCt1Received_key_isSome` (those arms always
emit when they succeed); the trace part is `epochs_nodup`, via
`epochs_consecutive` (keys at `keyFloor s, keyFloor s + 1, …`) and
`epochs_strictly_increase`. No theorem depends on `sorryAx`: since the re-extraction at
`dd8e6b9` the closures contain only the Lean core axioms, the Aeneas `core.fmt.Formatter`
axiom and `native_decide` artifacts of extracted definitions. Scope: the crate with overflow checks, or a release run in which no call
overflows (Spec §3.8); `States`, not the public API. Statement ACCEPT:
`docs/statement-reviews/PROP-21-trace-and-recv-half-3.md` (round 3; round 2 also ACCEPT).

### PROP-22 Epoch agreement

`t_snd` returned by `Send` equals `t_rcv` returned by the matching `Receive`.

Source: Spec §1.1; src/lib.rs:299; src/lib.rs:462

In the code both equal `msg.epoch - 1`, so the property holds by
construction once the wire epoch is the sender's state epoch:
for every `States` variant, `send` puts `state.epoch()` in `msg.epoch`
(`states.rs:120-271`), and no `send` arm changes the epoch.
This covers the equal-version path. When the peer's version is above ours, `recv`
returns the epoch-0 chain key (`lib.rs:383-420`) and no `t_rcv` is computed from
`msg.epoch`.
Status: **Open**. Note that the spec's own pseudocode computes `t_rcv` as
`state.epoch - 1` of the receiver, which differs from `t_snd` for delayed
messages; the code's choice is the one that satisfies the property.

### PROP-23 Sender and receiver epoch knowledge

When `Send` returns `t_snd` (resp. `Receive` returns `t_rcv`), the caller has
emitted keys for that epoch and all earlier ones.

Source: Spec §1.1; src/lib.rs:297; src/lib.rs:465

With `t_snd = msg.epoch - 1` this says: a party at state epoch `e` has emitted
keys for epochs `1..e-1`. Trace property over the v1 machine plus the chain
(`chain.add_epoch` is called with every emitted key, `lib.rs:297,465`).
Status: **Open**. PROP-21's `epochs_consecutive` is groundwork: it already says a
run's keys come out at consecutive epochs from `keyFloor s`, with no gaps.

---

## 3. Incremental KEM (§1.2)

Code interface (`incremental_mlkem768.rs`): `generate(rng) → Keys { hdr, ek, dk }`
with `hdr` (64 bytes) and `ek` (1152 bytes) built inside libcrux;
`encaps1(hdr, rng) → (ct1, es, ss)` (960, 2080, 32 bytes);
`encaps2(ek, es) → ct2` (128 bytes); `decaps(dk, ct1, ct2) → ss`;
`ek_matches_header(ek, hdr) = validate_pk_bytes(hdr, ek).is_ok()` (`:28-30`).
The crate never computes SHA3 itself.

### PROP-3 KEM roundtrip

For `Keys { hdr, ek, dk } = generate(r)`, `(ct1, es, ss) = encaps1(hdr, r')`,
`ct2 = encaps2(ek, es)`: `decaps(dk, ct1, ct2) = ss`.

Source: Spec §1.2; src/incremental_mlkem768.rs:34-171

The three key components must be bound to one `generate` call; an axiom
quantifying over independent `hdr`, `ek`, `dk` is too strong. Status:
**Axiom** (`encapsulate1`, `encapsulate2`, `decapsulate_compressed_key` are
libcrux stubs). `generate_spec` (`Spqr/Specs/IncrementalMlkem768/Generate.lean`)
is **Proved**: `ek` and `hdr` are the corresponding slices of `dk`, with the
sizes above.

### PROP-3b Header binding

`ek_matches_header(ek, hdr)` holds iff `hdr` is the header libcrux derives
from the key pair whose vector part is `ek` (§1.2.1: `hdr = ek_seed ‖
SHA3-256(ek)` for the FIPS 203 encoding of `ek`).

Source: Spec §1.2.1; src/incremental_mlkem768.rs:28-30

Status: **Axiom** (`validate_pk_bytes` is a libcrux stub). The crate now builds
against libcrux-ml-kem 0.0.10; whether `validate_pk_bytes` changed since 0.0.7 is not
checked. The exact byte string hashed must be taken from libcrux, not from the spec prose
"`ek_seed || ek_vector`": FIPS 203 places the seed last in the encoded key.

---

## 4. Erasure code and field arithmetic (§1.3, §2.2 Encode/Decode, §3.6)

### LEAN-ENC-1 Point roundtrip

`Pt.deserialize(Pt.serialize(p)) = ok p`. **Proved**
(`Spqr/Specs/Encoding/Polynomial/Pt/{Serialize,Deserialize}.lean`).

Source: src/encoding/polynomial.rs:30-48
Evidence: Spqr/Specs/Encoding/Polynomial/Pt/{Serialize,Deserialize}.lean

### LEAN-ENC-2 Decode from any N chunks

If a message fits in `N` codewords, `PolyDecoder` reconstructs it from any
`N` distinct codewords (§3.6). Status: **Open**. `decoded_message` is extracted
(from the patched body in `translation-patches/polynomial-PolyDecoder-decoded_message.patch`)
but has no spec; the surrounding encoder/decoder functions have specs
(`Spqr/Specs/Encoding/{Encoder,Decoder,Polynomial}/`).

Source: Spec §3.6; src/encoding/polynomial.rs:918-976
Evidence: Spqr/Specs/Encoding/{Encoder,Decoder,Polynomial}/

### LEAN-GF GF(2^16) arithmetic

`GF16` add, sub, eq, mul, div and their assign forms agree with
`GaloisField 2 16` (`Spqr/Math/Gf16/Field.lean:36`). **Proved**
(`Spqr/Specs/Encoding/Gf/`, no `sorry`). `mul2_u16` and `mul_assign` are extracted
with their SIMD branches removed (`translation-patches/gf-mul2_u16.patch`,
`gf-MulAssign_ref-mul_assign.patch`); `mul2_u16_spec_poly` specifies the portable
path. Upstream `div_impl` now calls `mul2_u16` (`gf.rs:548-557`). The accelerated
code (`gf::accelerated`) is excluded from extraction and unverified.

Source: Spec §2.2; src/encoding/gf.rs:16-196; src/encoding/gf.rs:216-225; src/encoding/gf.rs:548-557
Evidence: Spqr/Math/Gf16/Field.lean:36; Spqr/Specs/Encoding/Gf/

---

## 5. Parameters (§2.2)

### PROP-45 KEM constants

`HEADER_SIZE = 64`, `EK_SIZE = 1152`, `CT1_SIZE = 960`, `CT2_SIZE = 128` for
ML-KEM-768. Code: `HEADER_SIZE = pk1_len()`, `ENCAPSULATION_KEY_SIZE = pk2_len()`
(`incremental_mlkem768.rs:13,15`), `ensures` clauses 960/2080/32/128 on
`encaps1`/`encaps2`. Status: **Open** (constant evaluation).

Source: Spec §2.2; src/incremental_mlkem768.rs:8-15

### PROP-24 KDF_OK

Both derivation sites, `HeaderReceived::send_ct1` (`unchunked/send_ct.rs:129-135`)
and `EkSentCt1Received::recv_ct2` (`unchunked/send_ek.rs:150-158`), call
`hkdf_to_vec(salt = [0u8; 32], ikm = ss, info = "Signal_PQCKA_V1_MLKEM768:SCKA Key" ‖ epoch_be, 32)`.
This is the spec recipe (salt = zero block of hash length, IKM = shared
secret, info = `PROTOCOL_INFO ‖ ":SCKA Key" ‖ ToBytes(epoch)`, length 32).
Status: **Open**; `hkdf_to_vec_spec` (**Proved**) gives the HKDF value.

Source: Spec §2.2; src/v1/unchunked/send_ct.rs:129-135; src/v1/unchunked/send_ek.rs:150-158

### PROP-42 KDF_AUTH info and length

Decided behaviour (D1): `Authenticator::update(ep, k)`, on an authenticator whose
`root_key ‖ k` fits in memory, calls HKDF-SHA256 with `salt = [0u8; 32]`,
`ikm = root_key ‖ k`,
`info = "Signal_PQCKA_V1_MLKEM768:Authenticator Update" ‖ ep_be` and length 64,
and sets `root_key = out[..32]`, `mac_key = out[32..]`, each 32 bytes
(`authenticator.rs:43-54`).

Info and length are the spec's: §2.2 defines
`KDF_AUTH(root_key, update_key, epoch)` with
`info = PROTOCOL_INFO ‖ ":Authenticator Update" ‖ ToBytes(epoch)` and length 64.
Salt and IKM are not. The spec sets `salt = root_key` and `ikm = update_key`; the
code passes a zero salt and concatenates the two into the IKM. The statement above
asserts the **code**, per the provisional D1 decision in §11. HKDF is not symmetric
in its salt and its IKM, so this is a different derived `root_key` and `mac_key`,
not a re-association of the same inputs, and a spec-conformant peer cannot
interoperate.

**Proved** as `update_spec`
(`Spqr/Specs/Authenticator/Authenticator/Update.lean`), whose postcondition is the
decided behaviour verbatim — `root_key.val ++ mac_key.val = hkdf (replicate 32 0#u8)
(self.root_key.val ++ k.val) (updateLabel ++ to_be_bytes ep) 64` with both halves 32
bytes, under the hypothesis `self.root_key.length + k.length ≤ Usize.max`. The
decided wording and the proved theorem agree, so no theorem is restated here; the
memory-size hypothesis is the "fits in memory" clause above.

Source: Spec §2.2; src/authenticator.rs:43-54
Evidence: Spqr/Specs/Authenticator/Authenticator/Update.lean

### PROP-18 HKDF output lengths

Every production HKDF call requests 32, 64 or 96 bytes
(`authenticator.rs:51`; `unchunked/send_ct.rs:135`; `unchunked/send_ek.rs:156`;
`chain.rs:233,335,363`), within the HKDF-SHA256 limit of 8160. `hkdf_to_vec_spec`
(**Proved**) needs `okm_len ≤ 255 * 32`; each call site discharges it by
evaluation.

Source: Spec §2.2; src/authenticator.rs:51; src/v1/unchunked/send_ct.rs:135; src/v1/unchunked/send_ek.rs:156; src/chain.rs:233; src/chain.rs:335; src/chain.rs:363

### PROP-41 Label prefix

The five info/MAC labels (`authenticator.rs:47,68,93`,
`unchunked/send_ct.rs:131`, `unchunked/send_ek.rs:152`) share the prefix
`Signal_PQCKA_V1_MLKEM768`. There is no `PROTOCOL_INFO` constant in the code.

Decided behaviour (D6): §2.2 prescribes `PROTOCOL_INFO` as the concatenation of a
protocol identifier, a string representation of KEM and a string representation of
MAC, and leaves only the string *representations* to the implementer. The
prefix above carries the first two components and no MAC representation, so the
component set is prescribed by §2.2 rather than left to the implementer, and
the omission is not an implementer choice. That gap is recorded as **D6** in
§11, and the statement above asserts the **code** as implemented, per the
provisional D6 decision, pending a Signal ruling.

Status: **Proved** indirectly via the label constants
in `update_spec`, `mac_hdr_spec`, `mac_ct_spec`; the KDF_OK literal is not yet
covered.

Source: Spec §2.2; src/authenticator.rs:47; src/authenticator.rs:68; src/authenticator.rs:93; src/v1/unchunked/send_ct.rs:131; src/v1/unchunked/send_ek.rs:152

---

## 6. Messages (§2.3)

### PROP-35 Wire format

`Message::serialize(m, index)` produces `messageBytes m index`
(`v1/chunked/states/serialize.rs:171-197`). Parsing is split in two. `msg_preamble`
(`lib.rs:563-590`) reads the version byte, the varint epoch (rejecting `0`) and the varint
index, and returns the remaining bytes. `Message::deserialize(epoch, from)`
(`v1/chunked/states/serialize.rs:199-219`) reads the payload tag and chunk from those bytes and
returns `Message { epoch, payload }`, ignoring trailing bytes. **Proved** as
`Message.serialize_spec`, `msg_preamble_spec` and `Message.deserialize_spec`
(`Spqr/Specs/V1/Chunked/States/Serialize/Message/`, `Spqr/Specs/Lib/MsgPreamble.lean`). The
composed roundtrip is **Proved (branch)** on `la/prop-35` (`57fc83c`, 2026-10-27, stacked on
`la/struct-02a`; draft PR #755, closes #754), all five gates PASS: for `m` with `0 < m.epoch` and a `Ct1Ack` flag, if any, equal
to `true`, `serialize m i` succeeds, `msg_preamble` parses its output to a preamble with
version `1`, epoch `m.epoch` and index `i`, and `Message::deserialize` on that epoch and the
remaining bytes returns `m` (`Message.serialize_parse_roundtrip`,
`docs/statements/PROP-35-roundtrip.md`; REV-01 ACCEPT 2026-10-27, round 3 (docstring only,
matching the Lean file), `docs/statement-reviews/PROP-35-roundtrip-3.md`, SHA `8e29d7d0`; round 2
ACCEPT 2026-10-27 (docstring only),
`docs/statement-reviews/PROP-35-roundtrip-2.md`, SHA `7a07bc59`; round 1 ACCEPT 2026-10-15,
`docs/statement-reviews/PROP-35-roundtrip-1.md`, SHA `0c426d60`). The proof is in
`Spqr/Specs/V1/Chunked/States/Serialize/Message/Roundtrip.lean`; its encoder-to-decoder bridge
is `varintBlockAt_of_map` (`Serialize/EncodedBlocks.lean`), and its completeness lemmas are
`decode_varint_of_block`,
`msg_preamble_of_blocks`, `decode_chunk_of_block` and `Message.deserialize_of_bytes`.

Source: Spec §2.3; src/v1/chunked/states/serialize.rs:171-219; src/lib.rs:563-590
Evidence: Spqr/Specs/V1/Chunked/States/Serialize/Message/; Spqr/Specs/Lib/MsgPreamble.lean
Domain: the composed roundtrip is **false unrestricted**, so it is asserted on the
domain the code round-trips. The two restrictions are (1) `0 < m.epoch`: `msg_preamble`
rejects a zero wire epoch (`MsgPreamble.lean:66`, `lib.rs:575-577`); and (2) for
`payload = Ct1Ack b`, `b = true`: `deserialize` always rebuilds `Ct1Ack(true)`
(`Deserialize.lean:73`, `serialize.rs:208`). Outside them the composition is false, not
merely unproved. No length hypothesis is needed: the proof uses the completeness lemmas
`Message.deserialize_of_bytes` and `decode_chunk_of_block`, not the length-bounded
`Message.deserialize_spec` (`Deserialize.lean:65`), because a chunk block ends inside the slice;
`msg_preamble_spec` has no length hypothesis. A whole message is at most
**52 bytes** (`1 + 10 + 5 + 1 + 3 + 32`: version byte, `u64` epoch varint, `u32` index
varint, tag, `u16` chunk-index varint, 32 data bytes; model in
`Message/Serialize.lean:65-67`, `EncodeChunk.lean:45-46`, `EncodeVarint.lean:36-37`,
`SrcTranslated/Types.lean:730-732`), which is still true but no hypothesis consumes it now.
The proof also needs a `varintBytes`-to-`varintBlockAt` agreement lemma, a support lemma and
not a domain restriction. Restated 2026-10-15 for the pin move: at `d47083c` the roundtrip
was `deserialize(serialize(m, i)) = ok (m, i, _)` over a one-stage parse.
Evidence: Spqr/Specs/V1/Chunked/States/Serialize/Message/Deserialize.lean:65,66-75; Spqr/Specs/Lib/MsgPreamble.lean:59

The `index` field is the chain layer's per-message key index from
`chain.send_key` (`lib.rs:299`). §2.3 lists only `{epoch, type, data}` and
leaves the encoding to the implementer, so this is permitted, but the wire
format is SPQR-specific rather than a pure ML-KEM Braid message.

### STRUCT-02a Wire format is not injective

The converse of PROP-35 (does a byte string have at most one parse, and does a message
have at most one encoding?) is **false** for this wire format. `Message::serialize` is not
injective on messages, and the parse `msg_preamble` followed by `Message::deserialize` is not
injective on byte strings. The parse output is judged on version, epoch, index and message,
as in STRUCT-02b. Both are witnessed:

1. **Tag collapse.** `Message { epoch: 1, payload: Ct1Ack(false) }` and
   `Message { epoch: 1, payload: Ct1Ack(true) }` have the same serialization:
   `serialize` writes only the type tag, and `MessageType::from_payload`
   (`serialize.rs:122`) maps both Booleans to `MessageType::Ct1Ack`, while
   `deserialize` always rebuilds `Ct1Ack(true)` (`serialize.rs:208`).
2. **Non-minimal LEB128.** `01 01 00 00` and `01 81 00 00 00` both parse to the preamble
   `(version 1, epoch 1, index 0, remaining [00])` and to
   `Message { epoch: 1, payload: None }`, because `decode_varint` (`lib.rs:524`) accepts a
   non-minimal block. Here even `remaining` agrees; there is no cursor since
   `dd8e6b9`. The ten-byte truncation pair (`… 80 00 …` against `… 80 02 …` in the tenth
   septet) collides the same way.
3. **Trailing bytes.** Appending bytes after the message changes only the preamble's
   `remaining`, not the version, epoch, index or message: `Message::deserialize` ignores data past the chunk
   deliberately, for forward compatibility (`serialize.rs:215-218`).

No parse stage checks the version byte (it is returned in the preamble and read by `recv`'s
negotiation, `lib.rs:365-382`), so this adds no further collision.

A negative result **discharges** this row; that is why it is stated separately from
STRUCT-02b: what is to be recorded is that the converse fails, with the witnesses
named. Status: **Proved (branch)** on `la/struct-02a` (`2ddd203`, 2026-10-27), all five gates
PASS: `Message.serialize_parse_not_injective` in
`Spqr/Specs/V1/Chunked/States/Serialize/Message/NotInjective.lean`, docstring and signature identical to the
ACCEPTed statement (round 5, 2026-10-27, docstring-only change from round 4). Support:
`recv_eq_of_parse_eq` (`Spqr/Specs/Lib/Recv/ParseEq.lean`) and the corollary
`recv_on_witnesses_eq`, the witness lemmas `msg_preamble_minimal_witness`,
`msg_preamble_nonminimal_witness`, `msg_preamble_trailing_witness`, and the completeness lemmas `decode_varint_of_block`,
`msg_preamble_of_blocks`, `Message.deserialize_none`.

What is *not* claimed: this is a functional-correctness row, not a security claim.
Whether the non-injectivity is exploitable depends on what is MAC'd against what is parsed
(v2 SEC-01). A code reading on 2026-10-27 (`docs/sec-01-wire-malleability.md`, libsignal
`fc90b90`) found it is not exploitable in libsignal: the `SignalMessage` MAC covers the exact
serialized bytes, including `pq_ratchet`, and the SPQR state is stored only after the MAC
check. It matters for an integrator that does not authenticate the exact bytes, or that uses
them as an identity. That result is outside the extraction and stays a cited code reading.
The SPQR half is provable: `lib.recv` depends on the bytes only through the parsed
version, epoch, index and message (a parse-equivalence support lemma for this row).

Source: src/v1/chunked/states/serialize.rs:93-153; src/v1/chunked/states/serialize.rs:171-219; src/lib.rs:507-590
Evidence: Spqr/Specs/V1/Chunked/States/Serialize/DecodeVarint.lean:46-48
Review: ACCEPT 2026-10-27 (round 5, docstring only) — docs/statement-reviews/STRUCT-02a-witness-5.md, statement docs/statements/STRUCT-02a-witness.md SHA 69dd7624957d856773fdf778c517fa25ab5fe77452e13daa6c7103583403b434. Earlier: ACCEPT 2026-10-27 (round 4, docstring only) — docs/statement-reviews/STRUCT-02a-witness-4.md, SHA 3dc598f9e220376441e3c5687e4c9d017934f775d7121e762168c8f000195b78. Earlier: ACCEPT 2026-10-15 (round 3, restated for the pin move) — docs/statement-reviews/STRUCT-02a-witness-3.md, SHA cda0cf1278c41d930b5523e53997d69d462a2bb73d7f6230ef988bda78b4269f. Earlier: ACCEPT 2026-09-15 (round 2; round 1 REVISE) against `d47083c`, docs/statement-reviews/STRUCT-02a-witness-2.md, SHA c67dbc81074ec89b10b03529bbe27c842eca9434c7a51467fdef6cdc26323f6c; all rounds logged in docs/spec-review-log.md

### STRUCT-02b Canonical encodings deserialize injectively

Restricted to canonical encodings (the varint blocks minimal, no trailing bytes, and the
byte string in the image of `Message::serialize`), the parse `msg_preamble` followed by
`Message::deserialize` is injective: if two such byte strings parse to the same version,
epoch, index and message, they are equal. Canonicity is a predicate to be written down, not
an adjective; it is what excludes each of STRUCT-02a's three witness families. "No trailing
bytes" means the preamble's `remaining` ends after the tag byte for the chunkless payloads and
after the chunk block for the others.

This is the half of PROP-35's converse that is true and useful, and it rests on the
same `varintBytes`-to-`varintBlockAt` agreement lemma PROP-35's roundtrip needs, which is why
both sit in Phase 3. That lemma is now `varintBlockAt_of_map` on `la/prop-35`. Status: **Open**; the restated statement has an ACCEPT
(round 3, against `dd8e6b9`).

Source: src/v1/chunked/states/serialize.rs:93-153; src/v1/chunked/states/serialize.rs:171-219; src/lib.rs:507-590
Evidence: Spqr/Specs/V1/Chunked/States/Serialize/DecodeVarint.lean:46-48
Review: ACCEPT 2026-10-15 (round 3, restated for the pin move) — docs/statement-reviews/STRUCT-02b-canonicity-3.md, statement docs/statements/STRUCT-02b-canonicity.md SHA 2576b7560a4dc6fb3c44acc42c6de29cf47fadb13572ac515d816a3c07b05619. Earlier: ACCEPT 2026-09-15 (round 2; round 1 REVISE) against `d47083c`, docs/statement-reviews/STRUCT-02b-canonicity-2.md, SHA 07ec125c878134612cf0cce59860fe38d9a44b6890bfc218c42ec96a8a6454e0; all rounds logged in docs/spec-review-log.md

Both rows are grounded in the code, not in the spec: §2.3 lists only
`{epoch, type, data}` and leaves the encoding to the implementer, so canonicity is
not mandated by the spec. The cited range `serialize.rs:93-153` carries the `MessageType`
enum and its `try_from` (`:95`, `:107`), `from_payload` (`:122`), and
`encode_chunk`/`decode_chunk` (`:135`, `:141`). `encode_varint` and `decode_varint` moved to
`lib.rs:509` and `lib.rs:524`, next to `msg_preamble` (`lib.rs:563`). `serialize.rs:171-219`
carries `serialize` (`:172`) and `deserialize` (`:200`).

### PROP-36 Epoch zero rejected

`msg_preamble` returns `Err(MsgDecode)` when a non-empty message's wire epoch is 0
(`lib.rs:575-577`). **Proved** (part of `msg_preamble_spec`,
`Spqr/Specs/Lib/MsgPreamble.lean:59`: `0 < p.epoch` for a non-empty message). An empty
message yields epoch 0 with version 0 (`lib.rs:564-571`). That `msg.epoch - 1` in `recv`
(`lib.rs:462`) still cannot underflow follows from version negotiation
(`lib.rs:365-447`), which never reaches the v1 branch with version 0; that half is
**Open**.

Source: src/lib.rs:563-590; src/lib.rs:462

---

## 7. Ratcheted authenticator (§2.4)

Constants: `MACSIZE = 32` (`authenticator.rs:33`), HMAC-SHA256.

### PROP-31 Init

`Authenticator::new(k, ep)` equals `update(ep, k)` applied to
`{ root_key: 0^32, mac_key: 0^32 }` (`authenticator.rs:34-41`; spec
`Authenticator.Init`). **Proved**: `new_spec` gives the same HKDF expression
as `update_spec` on the zero state.

Source: Spec §2.4; src/authenticator.rs:34-41

### PROP-40 MAC inputs

`mac_hdr(ep, hdr) = HMAC(mac_key, "…:ekheader" ‖ ep_be ‖ hdr)` and
`mac_ct(ep, ct) = HMAC(mac_key, "…:ciphertext" ‖ ep_be ‖ ct)`, both 32 bytes
(`authenticator.rs:66-105`). The ciphertext argument is always `ct1 ‖ ct2`
(`unchunked/send_ct.rs:192-193`, `unchunked/send_ek.rs:160`), as in the spec's
`MacCt(epoch, ct1 || ct2)`; this is why `Ct1` chunks carry no MAC of their own.
**Proved**: `mac_hdr_spec`, `mac_ct_spec`.

Source: Spec §2.4; src/authenticator.rs:66-105; src/v1/unchunked/send_ct.rs:192-193; src/v1/unchunked/send_ek.rs:160

### PROP-15 Verify accepts own MAC

`verify_hdr(ep, hdr, mac_hdr(ep, hdr)) = Ok(())` and likewise for `ct`.
`verify_*` uses the constant-time `util::compare` (`util.rs:25-33`) and returns
`InvalidHdrMac` / `InvalidCtMac` otherwise. **Proved**: `verify_ct_spec` and
`verify_hdr_spec` state `Ok ↔ mac_* = ok expected_mac`.

Source: Spec §2.4; src/authenticator.rs:57; src/authenticator.rs:82; src/util.rs:25-33

### PROP-43 MAC failure

Decided behaviour (D5): on a failed `verify_hdr` (transition 6,
`unchunked/send_ct.rs:107`) or a failed `verify_ct` (transition 5,
`unchunked/send_ek.rs:160`), `States::recv` returns `Err`, and `lib.rs::recv`
propagates it to the caller without producing a new serialized state and without
producing an epoch key. In transition 5 the check runs after `decaps` and after
`auth.update`, matching the spec's order. §2.4 asks for more — a participant
"should not proceed with the ML-KEM Braid session and should negotiate a new
ML-KEM Braid session" — and the library does none of that. The statement above
asserts the **code**, per the provisional D5 decision in §11, which leaves the
library weaker than the spec until Signal rules. Status: **Open**.

**The caller contract (D5).** This is the single copy; the D5 row in §11 points
here rather than restating it.

1. *What the caller sees.* Both internal causes — `Error::InvalidCtMac` and
   `Error::InvalidHdrMac` (`authenticator.rs:13`, `authenticator.rs:15`) — become
   the one public `Error::MacVerifyFailed` through the
   `From<authenticator::Error>` impl at `lib.rs:144-148`. A caller cannot
   distinguish a header-MAC failure from a ciphertext-MAC failure and must not
   branch on the difference.
2. *What happens to the caller's state.* `lib.rs:355` takes the state by
   immutable reference (`state: &SerializedState`), and a successful
   `Recv { state, key }` is built only at the four returns `lib.rs:376-379`,
   `:408-419`, `:453-456` and `:469-483`. A MAC failure leaves `States::recv`
   through `?` at `lib.rs:460`, before the v1 return, so on the error path none is
   built: the caller's serialized state is unchanged bytes,
   no state and no key are returned, and the caller may retry the same message or
   another one against that same state.
3. *What happens to the already-updated authenticator.* This is the question the
   deviation actually raises, and the two failure paths answer it differently. In
   transition 5, `recv_ct2` consumes `self` and destructures its authenticator into
   a local `mut auth` (`send_ek.rs:144-149`), calls `auth.update(epoch, &ss)` at
   `send_ek.rs:158`, and only then calls `auth.verify_ct(epoch, &ct1, &mac)?` at
   `send_ek.rs:160`. The authenticator is therefore ratcheted before the check —
   but only in that local value, which `?` drops on failure, so it never reaches
   the caller and the caller's serialized state still holds the pre-update
   authenticator. In transition 6, `recv_header` verifies first and constructs
   `HeaderReceived` only afterwards (`send_ct.rs:107-112`), so nothing is
   advanced at all.
4. *What is not claimed.* Dropping a local value is **not** zeroization. This
   contract claims only that the updated `root_key` and `mac_key` are unreachable
   from the returned state; it makes no claim that their bytes are erased from
   memory. Nor is it a session-abort claim: the library neither tears the session
   down nor signals that a new one should be negotiated. A deployment that wants
   §2.4's behaviour must implement it in the caller — on `Error::MacVerifyFailed`,
   stop using this state and negotiate a new session — and no property in this
   catalog asserts that any caller does.

Source: Spec §2.4; src/authenticator.rs:13; src/authenticator.rs:15; src/v1/unchunked/send_ct.rs:107-112; src/v1/unchunked/send_ek.rs:144-160; src/lib.rs:144-148; src/lib.rs:355; src/lib.rs:460; src/lib.rs:469-483

---

## 8. State machine (§2.5)

`States` (`src/v1/chunked/states.rs:16-29`) has the spec's 11 variants.
Side A (`send_ek`): KeysUnsampled, KeysSampled, HeaderSent, Ct1Received,
EkSentCt1Received. Side B (`send_ct`): NoHeaderReceived, HeaderReceived,
Ct1Sampled, EkReceivedCt1Sampled, Ct1Acknowledged, Ct2Sampled. The unchunked
types in `src/v1/unchunked/` are the inner core (`uc` field) of these states,
not a separate protocol mode; `lib.rs` uses only `v1::chunked`.

### PROP-30 Epoch and type dispatch

Every `recv` arm compares `msg.epoch` with `state.epoch()`. The table's
`msg.epoch > epoch` rows assert the **code**, not the spec's no-op, per the
provisional D2 decision in §11.

Source: Spec §2.5; src/v1/chunked/states.rs:275-533; src/v1/chunked/states.rs:514-527

| Case | Code | Spec |
|------|------|------|
| `msg.epoch < epoch` | state unchanged, `key = None` | no-op |
| `msg.epoch == epoch`, unexpected payload type | state unchanged, `key = None` | no-op |
| `msg.epoch == epoch`, expected type | transition (table below) | transition |
| `msg.epoch > epoch`, not Ct2Sampled | `Err(EpochOutOfRange)` | no-op (D2) |
| Ct2Sampled, `msg.epoch == epoch + 1` | `KeysUnsampled(epoch + 1)`, payload ignored | transition 13 |
| Ct2Sampled, `msg.epoch > epoch + 1` | `Err(EpochOutOfRange)` | no-op (D2) |

Decided statement (D2), quotable as a theorem: for every one of the eleven
`States` variants, `States::recv(state, msg)` with `msg.epoch > state.epoch()`
returns `Err(Error::EpochOutOfRange(msg.epoch))`, with the single exception of
`Ct2Sampled` at `msg.epoch == state.epoch() + 1`, which returns
`Ok { state = KeysUnsampled(state.epoch() + 1), key = None }` and ignores
`msg.payload` (`states.rs:514-527`); and with `msg.epoch < state.epoch()` it
returns `Ok { state, key = None }`, the state unchanged, for every variant. The
spec's no-op on a future epoch is asserted nowhere in this catalog.

Status: **Proved** (#663, on `main`, merged 2026-10-27 as `c32a6d8`, closes #662), over all variants,
no axioms beyond `States::recv`'s own closure. Less and Greater rows: `recv_of_lt`, `recv_of_gt`, `recv_Ct2Sampled_next_epoch`. Equal
rows: `recv_of_eq_unexpected` and `recv_of_eq_refines`. All five are in
`Spqr/Specs/Braid/StateMachine/EpochDispatch.lean`. The equal-epoch theorems compare against the
spec's `Receive` at state name and key presence; `recv_of_eq_unexpected` is total, and
`recv_of_eq_refines` holds in the if-it-returns form, with the checks stated by the code's own calls
(REV-01 ACCEPT round 10, `docs/statement-reviews/PROP-30-equal-10.md`).

### PROP-47 Transition refinement

Each spec transition is implemented by the named code path with the same
effect on the state's epoch, authenticator and payload. Transitions 11 and 12
and the `EkSentCt1Received` send arm assert the **code**'s emission and
acceptance sets, not the spec's, per the provisional D3 and D4 decisions in §11.

Source: Spec §2.5; src/v1/chunked/states.rs:115-533; src/v1/chunked/states.rs:175-186; src/v1/chunked/states.rs:465-468; src/v1/chunked/states.rs:485-496

| # | Spec | Code entry | Notes |
|---|------|-----------|-------|
| 1 | KeysUnsampled.Send | `states.rs` KeysUnsampled arm → `unchunked/send_ek.rs` `send_header` | header = `hdr ‖ mac_hdr(epoch, hdr)` |
| 2 | KeysSampled.Receive Ct1 | `states.rs:294` | |
| 3 | HeaderSent.Receive Ct1 (complete) | `states.rs:312` | |
| 4 | Ct1Received.Receive Ct2 | `states.rs:337` | |
| 5 | EkSentCt1Received.Receive Ct2 (complete) | `states.rs:355` → `recv_ct2` | decaps, KDF_OK, `auth.update`, `verify_ct(ct1 ‖ ct2)`, key emitted, epoch + 1 |
| 6 | NoHeaderReceived.Receive Hdr (complete) | `states.rs:386` → `recv_header` | `verify_hdr` before constructing HeaderReceived |
| 7 | HeaderReceived.Send | `states.rs:203` → `send_ct1` | encaps1, KDF_OK, `auth.update`, key emitted |
| 8–10 | Ct1Sampled.Receive Ek / EkCt1Ack | `states.rs:418` → `recv_ek_chunk` | PROP-25 on completion |
| 11 | Ct1Acknowledged.Receive EkCt1Ack | `states.rs:485` | decided (D4): accepts `Ek` as well as `EkCt1Ack`, both routed to `recv_ek_chunk` (`states.rs:490-496`) |
| 12 | EkReceivedCt1Sampled.Receive EkCt1Ack | `states.rs:464` | decided (D3): accepts `Ct1Ack(true)` as well as `EkCt1Ack` (`states.rs:465-468`) |
| 13 | Ct2Sampled.Receive epoch + 1 | `states.rs:514-527` | |

Status: **Open** for all 13.

Decided statement for the send arms (D3), quotable as a theorem: every send arm
other than 1 and 7 emits the payload type the spec prescribes, except
`EkSentCt1Received::send`, which emits `MessagePayload::Ct1Ack(true)` at the
state's own epoch and leaves the state and key unchanged (`states.rs:175-186`)
where the spec emits `None`; `Ct1Ack(false)` is emitted by no arm. Decided
statement for the receive arms (D3, D4): transition 12 accepts
`Ct1Ack(true) | EkCt1Ack(_)` and transition 11 accepts `Ek | EkCt1Ack`, in both
cases a strict superset of the spec's single accepted type, with any other
payload at the matching epoch leaving the state unchanged. The `EkSentCt1Received` send
arm is partly proved on `la/lean-v1-protocol-proofs` (draft PR #46) as
`send_EkSentCt1Received_ct1_ack`: `Ok`, payload `Ct1Ack(true)`, `key = None`, state and
rng unchanged. It does not state the message epoch.

State contents match the spec's per-state lists, with one representational
difference: `ek_seed` and `hek` are held as a single 64-byte `hdr`
(`chunked/send_ct.rs:95-97` copies `hdr ‖ mac` into two vectors at `HEADER_SIZE`; libcrux reads
the seed and hash out of `hdr`).

### PROP-50 Structural liveness

Decided statement (D2), quotable as a theorem: from
`(KeysUnsampled_A(e), NoHeaderReceived_B(e))`, every fair **in-order**
interleaving of `send`/`recv` with every message eventually delivered reaches
`(NoHeaderReceived_A(e+1), KeysUnsampled_B(e+1))`, and every reachable state pair
has a next step (§2.6: "Alice and Bob will always be able to make forward
progress as long as fresh messages are delivered"; Fig. 2 gives the reachable
pairs).

In-order delivery is a hypothesis of that statement, not a caveat on it. Under
the provisional D2 decision in §11 the properties assert the code, where a
message with `msg.epoch > state.epoch()` is `Err(EpochOutOfRange)` rather than
the spec's no-op, so a delivery that runs ahead of the receiver's epoch ends the
run in an error instead of leaving the state untouched, and liveness cannot be
claimed for it. One `Greater` arm is exceptional and the claim depends on it:
`Ct2Sampled` at exactly `msg.epoch == epoch + 1` transitions to
`KeysUnsampled(epoch + 1)` (`states.rs:514-527`), which is how side B carries the
epoch forward and reaches `KeysUnsampled_B(e+1)`. Status: **Open**.

Source: Spec §2.6; src/v1/chunked/states.rs:115-533

### PROP-52 A premature acknowledgement stalls the epoch

PROP-50 covers honest runs only. This row records what happens off them: one
acknowledgement that B gets before A decoded ct1 stops the epoch for good. The
row is a negative result, like STRUCT-02a, and a witness discharges it.

Take A in `HeaderSent(e)`, which still decodes ct1, and B in
`EkReceivedCt1Sampled(e)`, which has all of ek. If A sends every `Ek` chunk before
enough `Ct1` chunks arrive, an honest run reaches this pair. If B now receives
`Ct1Ack(true)` or `EkCt1Ack` at epoch `e`, it moves to `Ct2Sampled(e)`
(`states.rs:459-479`). After that:

1. B's `send` emits only `Ct2` chunks (`states.rs:259-271`).
2. A's `send` in `HeaderSent` emits only `Ek` chunks (`states.rs:150-161`).
3. A's `recv` in `HeaderSent` at epoch `e` acts only on `Ct1` and leaves the state
   unchanged otherwise (`states.rs:307-332`).
4. B's `recv` in `Ct2Sampled` at epoch `e` leaves the state unchanged for every
   payload (`states.rs:514-530`). Only a message at `e + 1` moves it, and A never
   sends one from `HeaderSent`.

Take any run that delivers only messages sent after the acknowledgement, in any
order and any number of times. In it A stays in `HeaderSent(e)`, B stays in
`Ct2Sampled(e)`, and neither emits a key. If a `Ct1` chunk that B sent earlier is
still in flight and completes A's decoder, the run does not stall. The statement
excludes those messages.

The spec has the same exposure. §2.5 transition 12 accepts `EkCt1Ack` in
`EkReceivedCt1Sampled`, so a forged `EkCt1Ack` leads to the same deadlock under the
spec. D3 adds `Ct1Ack(true)` as a second trigger. It does not add a failure mode.

Neither trigger comes from the peer's `send` in a normal run (PR #663, Deviation
`ct1ack-accepted`), because the peer emits `Ct1Ack(true)` and `EkCt1Ack` only after it
decoded ct1. The examples in that PR have the peer in `EkSentCt1Received`. There §2.5
stalls, while the code takes transition 12 and sends `Ct2` chunks that the peer
accepts. Those examples are a different case from this row. So the
trigger is a forged message or a call with an older state. Signal authenticates
SPQR messages in the outer ratchet, and SCKA Def. 3.1 is stated over honest runs,
so this is outside the SCKA model. The row records what one off-run message does,
for the D3 ruling. It is not a security claim.

What is not claimed: first, that a run of successful calls from `initial_state`
reaches the pair. That needs PROP-27 and the success of the sends that sample keys.
Second, that no other off-run message has the same effect.

Status: **Open**; statement drafted
(`docs/statements/PROP-52-premature-ack-stall.md`), review pending.

Source: Spec §2.5; src/v1/chunked/states.rs:150-161; src/v1/chunked/states.rs:259-271; src/v1/chunked/states.rs:307-332; src/v1/chunked/states.rs:459-479; src/v1/chunked/states.rs:514-530

### PROP-25 Encapsulation-key integrity

Whenever the `ek_decoder` completes, `ek_matches_header(ek, hdr)` is checked
before `ek` is used, and failure returns `Err(ErroneousDataReceived)`.
Single call site `Ct1Sent::recv_ek` (`unchunked/send_ct.rs:160-169`), reached
from `Ct1Sampled` and `Ct1Acknowledged` with either `Ek` or `EkCt1Ack`
chunks (four combinations). Status: **Open**; the meaning of the check is
PROP-3b.

Source: Spec §2.5; src/v1/unchunked/send_ct.rs:160-169

### PROP-48 Decoder sizes

Decoders are created with the spec's message sizes: header
`HEADER_SIZE + MACSIZE` (`chunked/send_ct.rs:72-73`, `chunked/send_ek.rs:212-213`),
ek `ENCAPSULATION_KEY_SIZE` (`chunked/send_ct.rs:99`), ct1 `CIPHERTEXT1_SIZE`
(`chunked/send_ek.rs:87`), ct2 `CIPHERTEXT2_SIZE + MACSIZE`
(`chunked/send_ek.rs:171-172`). Status: **Open**.

Source: Spec §2.2; src/v1/chunked/send_ct.rs:72-73; src/v1/chunked/send_ct.rs:99; src/v1/chunked/send_ek.rs:87; src/v1/chunked/send_ek.rs:171-172; src/v1/chunked/send_ek.rs:212-213

### PROP-49 Key epoch

The emitted `EpochSecret.epoch` is the epoch being negotiated: in
transition 7 it is `state.epoch`; in transition 5 it is the pre-increment
epoch while the new state carries `epoch + 1` (`unchunked/send_ek.rs:163-166`).
This is the value `chain.add_epoch` asserts to be `current_epoch + 1`
(PROP-9). Status: **Proved** (#574, on `main`) as support lemmas of
PROP-21 (`send_key_epoch`, `recv_key_epoch`), not as a target of its own: each theorem is
about one call, which the statement review ruled Single path
(`docs/statement-reviews/PROP-49-key-epoch-1.md`).

Source: Spec §2.5; src/v1/chunked/states.rs:203-220; src/v1/chunked/states.rs:361-369; src/v1/unchunked/send_ek.rs:163-166

---

## 9. Initialization (§2.6)

### PROP-27 Initial states

`initial_state` with direction A2B yields `KeysUnsampled { epoch: 1, auth:
Authenticator::new(k, 1) }`, with B2A `NoHeaderReceived { epoch: 1, auth:
Authenticator::new(k, 1), header_decoder }` (`initial_state`, `lib.rs:211-235`, which
calls `init_inner`, `lib.rs:197-208`; `unchunked/send_ek.rs:78-79`,
`unchunked/send_ct.rs:94-95`). Status: **Open**.

Source: Spec §2.6; src/lib.rs:197-235; src/v1/unchunked/send_ek.rs:78-79; src/v1/unchunked/send_ct.rs:94-95

### PROP-16 Version negotiation

Not in the spec. Let `cur` be our state's version and `min` the negotiation
record's `min_version`, or `cur` when there is no record. `recv` returns
`Error::MinimumVersion` if the peer's version byte is below `min` (an empty message
is version 0, `lib.rs:564-571`). It returns `Error::VersionMismatch` if the peer's
version differs from `cur`, there is no record and `cur ≠ 0`. It returns `Ok` with an
empty state and no key if `cur = 0`. Otherwise a peer version above ours returns the
chain key of epoch 0 at the message's index and keeps the record (`lib.rs:383-420`),
and a peer version below ours re-initialises the inner state at the peer's version and
drops the record (`lib.rs:422-446`). With no record, a lower peer version therefore gets
`MinimumVersion`, not `VersionMismatch` as at `d47083c`. Status: **Open**.

Source: src/lib.rs:365-447

---

## 10. Chain layer (`chain.rs`, outside the spec)

The chain turns each SCKA key into per-message keys (SCKA Fig. 2). Properties
here are grounded in the code.

| ID | Statement | Source | Status |
|----|-----------|--------|--------|
| PROP-9 | `add_epoch(es)` with `es.epoch = current_epoch + 1` sets `current_epoch = es.epoch`, derives `next_root` and the new link's send/recv seeds from HKDF(`next_root`, `es.secret`, 96), appends one link, leaves `dir`, `send_epoch`, `params` unchanged | `src/chain.rs:356-375` | **Proved** `add_epoch_spec` (`Spqr/Specs/Chain/Chain/AddEpoch.lean`) |
| PROP-14 | `send_key(epoch)` with `epoch < send_epoch` returns `Err(SendKeyEpochDecreased(send_epoch, epoch))` | `src/chain.rs:390-393` | **Proved** `send_key_spec`, first case (`Spqr/Specs/Chain/Chain/SendKey.lean`, #546) |
| PROP-17 | `ChainEpochDirection::key(at)`: `at > ctr ∧ at - ctr > max_jump` → `Err(KeyJump(ctr, at))`; `at = ctr` → `Err(KeyAlreadyRequested(at))`; `at < ctr` → `prev.get` | `src/chain.rs:248-261` | **Proved** `key_spec_greater_jump`, `key_spec_equal`, `key_spec_less` (`Spqr/Specs/Chain/ChainEpochDirection/Key.lean`) |
| PROP-29 | `epoch_idx(e)`: `Ok(links.len() - 1 - (current_epoch - e))` iff `e ≤ current_epoch` and the difference is below `links.len()`, else `Err(EpochOutOfRange(e))` | `src/chain.rs:378-388` | **Proved** `epoch_idx_spec` (`Spqr/Specs/Chain/Chain/EpochIdx.lean`) |
| PROP-10 | When `send_key` moves `send_epoch` forward it pops links older than `EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH = 1` and clears the send seed of every earlier link; receive seeds are untouched, and `KeyHistory` entries are removed on `get` or trimmed by `gc` | `src/chain.rs:395-406`; `src/chain.rs:318`; `src/chain.rs:145-168`; `src/chain.rs:200` | **Open** |
| PROP-12a | `KeyHistory.data.len() % 36 = 0` (`KEY_SIZE = 4 + 32`, `chain.rs:130`) is preserved by `add`, `get`, `gc` | `src/chain.rs:128-208` | **Proved** (`add_spec`, `get_loop_spec`, `gc_loop_spec` carry the alignment) |
| PROP-12b | `get` after `add` of a fresh counter returns the stored 32-byte key and removes the entry | `src/chain.rs:184-207` | **Open**; `get_loop_spec` gives the per-slot behaviour |
| PROP-37 | `States::from_pb(States::into_pb(s)) = ok s` for all 11 variants | `src/v1/chunked/states/serialize.rs:10-90`; `src/v1/chunked/send_ek/serialize.rs:10-112`; `src/v1/chunked/send_ct/serialize.rs:11-151` | **Open**; per-state `into_pb`/`from_pb` specs exist for all unchunked states and for chunked `KeysUnsampled` and `KeysSampled`; model-level `roundtrip_fromPb_intoPb` theorems exist for several states, some under a `WellFormed` field-length hypothesis |
| PROP-38 | `Chain::from_pb(c.into_pb()) = ok c` for every `c` whose links each hold an empty or 32-byte `next` in both directions (`chain.rs:308-310` rejects any other length) | `src/chain.rs:299-316`; `src/chain.rs:424-462` | **Open** over the extracted functions. Proved on the functional models (`roundtrip_fromPb_intoPb`, `Spqr/Specs/Chain/Chain/FunctionalModels.lean:206`), which `from_pb_spec` and `into_pb_spec` link to the code; the composition is not stated. The model theorem also assumes `links.head = 0` and `links.length = links.buf.length`: these are hypotheses about the Lean `VecDeque` layout, not part of the Rust statement, since Rust `VecDeque` equality ignores layout. The code-level theorem must remove them or compare up to layout |
| PROP-51 | Along any run of one party's state machine, feeding the emitted keys in order to `add_epoch` never fails, the `assert!(epoch_secret.epoch == self.current_epoch + 1)` included, provided the chain starts one epoch behind the run (`current_epoch + 1 = keyFloor s`, true for `Chain::new` with either init state) and the link buffer has room; the chain ends one behind the run. Over the state machine and `add_epoch` only: no `send_key`/`recv_key`, no serialization, chain present | `src/lib.rs:295-299`; `src/lib.rs:463-466`; `src/chain.rs:356-375`; `src/chain.rs:333-354` | **Open**; statement drafted (`docs/statements/PROP-51-chain-epoch-sync.md`), review pending; needs PROP-21 and PROP-9 |

Finding: PROP-37's statement above is **false as written** (found 2026-09-15), for
two independent reasons (a third was found later, #567). The row is annotated rather than restated: its corrected
statement is deferred to Phase 7 (STRUCT-03, ROADMAP Phase 7 criterion 3), its
asserted conclusion is left untouched, and its status stays `Open` in the sense the
§1 legend now records — no theorem *and* no settled statement.

1. `PolyDecoder::into_pb` narrows `pts_needed` with `as u32`
   (`src/encoding/polynomial.rs:819`), and the merged `into_pb_spec` carries the
   hypothesis `h_cast : self.pts_needed.val ≤ U32.max`
   (`Spqr/Specs/Encoding/Polynomial/PolyDecoder/IntoPb.lean:300`). A decoder above
   that bound has no roundtrip.
2. The unchunked deserializers gate on stored byte-vector lengths while `into_pb`
   copies those vectors verbatim. `Ct1SentEkReceived::from_pb` requires
   `pb.es.len() == 2080 && pb.ct1.len() == 960 && pb.ek.len() == 1152`
   (`src/v1/unchunked/send_ct/serialize.rs:85`) whereas `into_pb` copies `es`, `ek`
   and `ct1` as they stand (`src/v1/unchunked/send_ct/serialize.rs:75-81`).
   Concretely: a `Ct1SentEkReceived` whose `es`, `ek` and `ct1` are empty vectors
   serializes successfully and then fails to deserialize with `Error::StateDecode` —
   with no `PolyDecoder` involved.
3. (#567) `Poly::deserialize` rejects the empty byte string, and `Poly::serialize` of a
   polynomial with no coefficients produces it (`deserialize_empty_is_err`,
   `Spqr/Specs/Encoding/Polynomial/Poly/Deserialize.lean:202`). A `PolyEncoder` in the
   `Polys` state holding such a polynomial does not round-trip through
   `into_pb`/`from_pb`. Whether `encode_bytes` can reach that encoder state is not
   checked; the state is inhabited in the Lean type.

Reason 2 is why representability alone does not rescue the row. The corrected
statement needs a full state-validity invariant — per-deserializer field lengths, the
variant-specific decoder-size checks such as
`src/v1/chunked/send_ct/serialize.rs:20-26`, and representability — which is Phase 7's
design work, where the per-variant specs are written anyway. Phase 7 does not start
from nothing on the field-length half: the source already states it. The
`Ct1SentEkReceived` struct sits under `#[hax_lib::attributes]` and carries
`#[hax_lib::refine(es.len() == 2080)]`,
`#[hax_lib::refine(ek.len() == 1152)]` and
`#[hax_lib::refine(ct1.len() == 960)]`
at `src/v1/unchunked/send_ct.rs:76,78,80` — exactly reason 2's three lengths. Aeneas does not carry `refine` into the extracted
Lean type, which is why the empty-vector term is inhabited there and the
counterexample stands, so Phase 7's work on this half is transporting an invariant the
code already asserts rather than inventing one. The variant-specific decoder-size
checks and representability are still open design. `States` protobuf injectivity is a
corollary of this row on whatever domain Phase 7 designs, not a separate property.

PROP-38 was **false as originally written** after upstream v1.6.0:
`ChainEpochDirection::from_pb` (`src/chain.rs:307-316`) rejects a `next` that is neither
empty nor 32 bytes, while `into_pb` copies it verbatim (`src/chain.rs:299-305`), so a
chain holding such a link does not round-trip. The restated row adds that domain.
`roundtrip_fromPb_intoPb` (#578) proves it on the functional models, under two further
`VecDeque` layout hypotheses that the row records but does not adopt as domain. `params` is already the protobuf type (`src/chain.rs:120`), so no
default-collapsing applies.

Note on §3.8 (epoch wraparound). Epochs are `u64`. The code excludes
wraparound by assumption (`hax_lib::assume!(current_epoch < u64::MAX)` in
`add_epoch`, `assume!(epoch < u64::MAX)` in `recv_ct2`), `Cargo.toml` sets no
`overflow-checks`, and the Lean theorems take non-overflow as a hypothesis. It
is not proved anywhere and does not need to be at 64 bits; state it as an
assumption.

---

## 11. Deviations from the spec

Each deviation has a stable ID and a short name. Lean comments and PR text use the name,
because readers there do not have this catalog.

| ID | Name | Where | Spec | Code | Impact | Source |
|----|------|-------|------|------|--------|--------|
| D1 | `kdf-auth-salt` | `Authenticator::update` (`authenticator.rs:43-54`) | KDF_AUTH: salt = `root_key`, IKM = `update_key` | salt = `[0u8; 32]`, IKM = `root_key ‖ update_key` | Different key bytes. Not a weakness, but a spec-conformant peer cannot interoperate. Needs a decision from Signal on which side is authoritative. | Spec §2.2; `src/authenticator.rs:43-54` |
| D2 | `future-epoch-error` | every `recv` arm | `msg.epoch > epoch` ignored | `Err(EpochOutOfRange)` (except Ct2Sampled at `epoch + 1`) | Tightening; a future-epoch message is an error instead of a no-op. | Spec §2.5; `src/v1/chunked/states.rs:275-533` |
| D3 | `ct1ack-accepted` | `EkSentCt1Received.send` (`states.rs:182`), `EkReceivedCt1Sampled.recv` (`states.rs:465-468`) | sends `None`; accepts only `EkCt1Ack` | sends `Ct1Ack(true)`; accepts `Ct1Ack(true)` too | §2.3 defines the `Ct1Ack` type but §2.5 never uses it; the code does. `Ct1Ack(false)` is never emitted. Motivation is robustness to a lost acknowledgement; no reachable state pair of the spec machine deadlocks without it. | Spec §2.3; Spec §2.5; `src/v1/chunked/states.rs:182`; `src/v1/chunked/states.rs:465-468` |
| D4 | `late-ek-chunk` | `Ct1Acknowledged.recv` (`states.rs:485-493`) | accepts `EkCt1Ack` | also accepts `Ek` chunks | Out-of-order delivery; comment at `states.rs:486-489`. Integrity still checked by PROP-25. | Spec §2.5; `src/v1/chunked/states.rs:485-493` |
| D5 | `mac-failure-no-abort` | MAC failure (§2.4) | "should not proceed with the session and should negotiate a new session" | returns `Err`; caller keeps the previous state and may retry | Weaker than the spec; the session is not aborted by the library. | Spec §2.4; `src/v1/unchunked/send_ct.rs:107`; `src/v1/unchunked/send_ek.rs:160` |
| D6 | `protocol-info-no-mac` | the `PROTOCOL_INFO` label literal, at its five sites (`authenticator.rs:47,68,93`, `unchunked/send_ct.rs:131`, `unchunked/send_ek.rs:152`) | §2.2 prescribes `PROTOCOL_INFO` as the concatenation of a protocol identifier, a string representation of KEM and a string representation of MAC, `_`-delimited — the spec's own example is `MyProtocol_MLKEM768_SHA-256`. Only the string *representations* are defined by the implementer; the component set is prescribed. | `Signal_PQCKA_V1_MLKEM768` — a protocol identifier and a KEM representation, and no MAC representation | `PROTOCOL_INFO` feeds both KDF_AUTH and KDF_OK, so a spec-conformant peer building a three-component literal derives a different `root_key`, a different `mac_key` and different session keys, and **cannot interoperate** — the same class as D1, not a naming preference. A second, latent consequence: with the MAC component omitted, two deployments that differ only in their MAC derive identical keys, so the literal does not domain-separate them. That one is dormant today because SPQR fixes MAC = HMAC-SHA256. | Spec §2.2; `src/authenticator.rs:47`; `src/v1/unchunked/send_ct.rs:131`; `src/v1/unchunked/send_ek.rs:152` |

Decisions recorded for the six rows. Each is a **project** decision taken so the
properties have one side to assert; none of them is a Signal ruling, and none of them
authorises a `src/` change:

| ID | Name | Decision | Status |
|----|------|----------|--------|
| D1 | `kdf-auth-salt` | The properties assert the code: KDF_AUTH is HKDF with salt = `[0u8; 32]` and IKM = `root_key ‖ update_key`, not the spec's salt = `root_key`, IKM = `update_key`. HKDF is not symmetric in its salt and its IKM, so the derived `root_key` and `mac_key` differ from the spec's and **a spec-conformant peer cannot interoperate** — this row and D6 are the two where adopting the code accepts a real interoperability cost rather than a bookkeeping one. Provisional and pending a Signal ruling; settling it needs either a code fix or a spec erratum, and Phase 1 does not speak for Signal on which. | Provisional (2026-09-15) |
| D2 | `future-epoch-error` | The properties assert the code: a message with `msg.epoch > state.epoch()` is `Err(EpochOutOfRange)` in every `recv` arm, except `Ct2Sampled` at exactly `epoch + 1`, which transitions to `KeysUnsampled(epoch + 1)` and ignores the payload. Provisional and pending a Signal ruling, not a finding that the tightening is right; settling it needs the spec to mandate strictness or the code to adopt the spec's no-op. | Provisional (2026-09-15) |
| D3 | `ct1ack-accepted` | The properties assert the code: `EkSentCt1Received.send` emits `Ct1Ack(true)` where the spec emits `None`, and `EkReceivedCt1Sampled.recv` accepts `Ct1Ack(true)` alongside `EkCt1Ack`; `Ct1Ack(false)` is never emitted. Provisional and pending a Signal ruling; settling it needs the spec to document the extra message handling or the code to drop it. | Provisional (2026-09-15) |
| D4 | `late-ek-chunk` | The properties assert the code: `Ct1Acknowledged.recv` also accepts `Ek` chunks, for out-of-order delivery, with encapsulation-key integrity still checked on completion (PROP-25). Provisional and pending a Signal ruling; settling it needs the spec to document the extra accepted type or the code to drop it. | Provisional (2026-09-15) |
| D5 | `mac-failure-no-abort` | The properties assert the code: MAC failure returns `Err` — `Error::MacVerifyFailed` at the public API — and the library does not abort the session, so the caller keeps its previous serialized state and may retry. The obligations this puts on the caller are written out once, as the caller contract in **PROP-43, section 7**; this row does not restate it. Provisional and pending a Signal ruling, and the code remains weaker than §2.4 until then; settling it needs the written contract adopted, or the library to abort the session itself. | Provisional (2026-09-15) |
| D6 | `protocol-info-no-mac` | The properties assert the code: the two-component literal `Signal_PQCKA_V1_MLKEM768` at all five label sites, carrying a protocol identifier and a KEM representation and no MAC representation. §2.2 prescribes the component set — a protocol identifier, a string representation of KEM and a string representation of MAC — and leaves only the string representations to the implementer, so the omission is a deviation and not an implementer choice. This row and D1 are the two where adopting the code accepts a real interoperability cost rather than a bookkeeping one. Provisional and pending a Signal ruling; settling it needs either a code fix adding the MAC representation to the literal, or a spec erratum permitting a two-component literal. | Provisional (2026-09-16) |

Resolution for each is a decision, not a proof: D1 needs either a code fix
or a spec erratum; D2 needs the spec to mandate strictness or the code to
adopt the no-op; D3 and D4 need the spec to document the extra message
handling or the code to drop it; D5 needs the caller's contract written down;
D6 needs either a code fix adding the MAC representation or a spec erratum
permitting a two-component literal.
Those candidate resolutions stand, and are retained for the outward-facing note
to Signal (DEV-05, deferred). What has changed is that each row now carries a
provisional decision in the second table above: the properties assert the code as
implemented, which is a recorded project decision pending a Signal ruling and not a
finding that the code is right. If Signal rules otherwise, the affected property
statements — PROP-42 (D1), PROP-30, PROP-47 and PROP-50 (D2, D3, D4), PROP-43
(D5) and PROP-41 (D6) — are restated, which is why each of them names its D-row
inline.

---

## 12. Index

| ID | Section | Status |
|----|---------|--------|
| PROP-1 | 2 | Open (needs PROP-3 axiom) |
| PROP-3 | 3 | Axiom; `generate_spec` proved |
| PROP-3b | 3 | Axiom |
| PROP-9 | 10 | Proved |
| PROP-10 | 10 | Open |
| PROP-12a | 10 | Proved |
| PROP-12b | 10 | Open |
| PROP-14 | 10 | Proved |
| PROP-15 | 7 | Proved |
| PROP-16 | 9 | Open |
| PROP-17 | 10 | Proved |
| PROP-18 | 5 | Proved |
| PROP-21 | 2 | Proved |
| PROP-22 | 2 | Open |
| PROP-23 | 2 | Open |
| PROP-24 | 5 | Open |
| PROP-25 | 8 | Open |
| PROP-27 | 9 | Open |
| PROP-29 | 10 | Proved |
| PROP-30 | 8 | Proved |
| PROP-31 | 7 | Proved |
| PROP-35 | 6 | Proved (components); roundtrip Proved (branch) |
| PROP-36 | 6 | Proved (preamble check); underflow half Open |
| PROP-37 | 10 | Open |
| PROP-38 | 10 | Open (restated domain); proved on the functional models |
| PROP-40 | 7 | Proved |
| PROP-41 | 5 | Proved (labels); KDF_OK literal Open |
| PROP-42 | 5 | Proved |
| PROP-43 | 7 | Open |
| PROP-45 | 5 | Open |
| PROP-47 | 8 | Open |
| PROP-48 | 8 | Open |
| PROP-49 | 8 | Proved, support lemmas of PROP-21 |
| PROP-50 | 8 | Open |
| PROP-51 | 10 | Open; statement drafted, review pending |
| PROP-52 | 8 | Open; statement drafted, review pending |
| LEAN-ENC-1 | 4 | Proved |
| LEAN-ENC-2 | 4 | Open |
| LEAN-GF | 4 | Proved |
| STRUCT-02a | 6 | Proved (branch) |
| STRUCT-02b | 6 | Open |
| D1–D6 | 11 | Deviations; a provisional decision recorded per row, pending Signal |

---

## 13. Changes from the previous draft

Removed: PROP-4, PROP-7, PROP-8 (universally quantified HKDF collision-freeness
axioms are false for a fixed-length output and would make the environment
inconsistent); PROP-22b (restated the epoch dispatch, not epoch agreement);
the claim that PROP-9 covers §3.8; the deadlock justification for D3; PROP-41
as a `PROTOCOL_INFO` theorem (no such constant exists).

Restated: PROP-21 (two emitting arms, trace part separate), PROP-22 (both
epochs are `msg.epoch - 1`), PROP-10 (erasure is in `send_key`), PROP-40
(`ct = ct1 ‖ ct2`), PROP-43 (order of checks, where state is preserved),
PROP-3 (actual code interface), PROP-3b (byte layout from libcrux).

Added: PROP-45, PROP-47, PROP-48, PROP-49, PROP-50 for spec content that had
no property. Statuses refreshed against `main`: `lib.rs` is extracted; GF16
multiplication, Authenticator, KeyHistory, Message serialization and
`hkdf_to_vec` are proved; the state-machine theorems are on
`la/lean-v1-protocol-proofs` only.

Dropped on purpose: the source-tag taxonomy and evidence scale (each property
now names its spec section or code location directly), effort estimates and
phase plans, and the coverage percentages of the former
`SPQR_SPEC_COVERAGE.md`. The former `code-vs-spec.md`, `gaps-vs-spec.md` and
`gaps_impl_vs_spec_refined.md` are folded into sections 1 and 11; their
longer discussion is in git history.
