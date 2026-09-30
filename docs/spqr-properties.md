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
- **Code**: `src/` at `d47083c`. Line numbers refer to that commit.
- **Lean**: `Spqr/Specs/` at the same commit. Aeneas output is in `SrcTranslated/`.

Status values:

| Status | Meaning |
|--------|---------|
| Proved | Theorem on `main`, no `sorry`, and no hand-written axiom beyond the three §1 documents: `hkdf_to_slice_spec`, `libcrux_hmac.hmac_sha256_tag32_spec` and `KeyPairCompressedBytes.from_seed_spec`. §1 carries each one's location, postcondition and whether it is avoidable; this cell names them only so that a `Proved` row can be checked against its own definition |
| Proved (branch) | Theorem exists only on `la/lean-v1-protocol-proofs` (draft PR #46); not merged. Those proofs also use the liveness axioms in that branch's `Spqr/Specs/External.lean`, three of which assert that defined functions (`PolyEncoder.next_chunk`, `KeysUnsampled.send_hdr_chunk`, `HeaderReceived.send_ct1_chunk`) never fail. The last two are false as stated, since both reach `generate`, which can fail; they need a premise, not just a proof. Merging requires replacing all three with theorems. |
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
including `lib.rs` `initial_state`, `send`, `recv`. Specs are written in
weakest-precondition style over the `Result` monad:
`f args ⦃ r => P r ⦄` means `f args` succeeds and its value satisfies `P`.

Opaque items and how they are handled:

| Item | Handling |
|------|----------|
| `kdf::hkdf_to_slice` | Lean `opaque`; behaviour given by `axiom hkdf_to_slice_spec` (`Spqr/Specs/Kdf/HkdfToSlice.lean:25`) in terms of an RFC 5869 model with `opaque HMAC_SHA256`. The only hand-written axiom under `Spqr/`; the two rows below record the hand-written weakest-precondition specifications in `SrcTranslated/FunsExternal.lean`. |
| `incremental_mlkem768::potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275` | Axiom stub (contains `log::*` under `cfg(not(hax))`). `encaps2` itself is extracted. |
| `PolyDecoder::decoded_message` | Axiom stub. Blocks the erasure-code roundtrip (LEAN-ENC-2). |
| libcrux `validate_pk_bytes`, `decapsulate_compressed_key`, `encapsulate1/2`, `hmac` | Axiom stubs (`SrcTranslated/FunsExternal.lean`). |
| `libcrux_hmac.hmac_sha256_tag32_spec` | **Hand-written** `@[step] axiom` at `SrcTranslated/FunsExternal.lean:1795`, not an aeneas signature stub: it carries a postcondition, namely that the returned tag is 32 bytes (`⦃ (r : alloc.vec.Vec U8) => r.length = 32 ⦄`). **Unavoidable**: `libcrux_hmac.hmac` is itself opaque, so there is nothing to prove the postcondition from. Specialised to `.Sha256` with `some 32#usize`, the only shapes the crate calls, so it adds no surplus assumption. Not unsound. It is in the axiom closure of `mac_hdr_spec` and `mac_ct_spec`, which carry PROP-40's **Proved** status. |
| `KeyPairCompressedBytes.from_seed_spec` | **Hand-written** `@[step] axiom` at `SrcTranslated/FunsExternal.lean:1873`, postcondition `⦃ fun kp => kp.value.length = mlkem768Params.decapsulationKeyBytes ⦄`. **Avoidable**: `from_seed` is a `def` returning `ok default`, and `value` is a length-indexed array (`SrcTranslated/TypesExternal.lean:144`), so the postcondition follows from `Array.length_eq` — the same one-liner already used at `SrcTranslated/FunsExternal.lean:1891`. It is an axiom today only because it was written as the `-- TODO: add cryptographic properties of from_seed_spec` placeholder, not because of any obstruction; it is true, hence not unsound. It is in the axiom closure of `generate_spec`, which `docs/proof-targets.md:94` records as discharged at baseline. **Retiring it is Phase 4 work under AXIOM-01..06.** |
| prost `Message` impls | `sorry`. `spqr.send`, `spqr.recv`, `States.send`, `Chain.into_pb/from_pb` depend on them transitively (see `sorry-manifest.txt`). |

Hand-written `sorry`s on `main`: `Spqr/Specs/Aeneas/MapCollectBridge.lean:70`
(aeneas#1043) and `Spqr/Specs/Lib/DecodeState.lean:54`.

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
- `Source: src/path.rs:a-b` — the code at `d47083c`. Resolved by checking that
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
(`lib.rs:300`, `lib.rs:427`).

### PROP-1 Session key consistency

If both parties output `(t, K)` and `(t, K')`, then `K = K'`.

Source: Spec §1.1; SCKA Def. 3.1

Reduces to: both parties' `EpochSecret.secret` for epoch `t` equal
`KDF_OK(ss, t)` for the same ML-KEM shared secret `ss`, which needs PROP-3
(KEM roundtrip) and PROP-24 (both KDF_OK sites identical). Status: **Open**.
Requires the KEM axiom of PROP-3.

### PROP-21 Per-participant epoch uniqueness

Each party outputs at most one key per epoch.

Source: Spec §1.1; SCKA Fig. 1; src/v1/chunked/states.rs:203-220; src/v1/chunked/states.rs:361-368

Structural part: exactly two arms of the state machine return a key,
`HeaderReceived.send` (spec transition 7, `states.rs:203-220`) and
`EkSentCt1Received.recv` on a completing `Ct2` chunk (transition 5,
`states.rs:361-368`). All other `send` arms and all other `recv` arms return
`key = None`. Trace part: over any run of successful `send`/`recv` calls by one
party, from any starting state, no two emitted keys carry the same epoch (SCKA
Fig. 1, `Send-P` line 14 and `Receive-P` line 7; App. B.1 "Unique epochs"). The
keys come out at consecutive epochs: `HeaderReceived@e` emits `e` and moves to
`Ct1Sampled@e`, whose next key can only be at `e + 1`, and `EkSentCt1Received@e`
emits `e` and moves to `NoHeaderReceived@(e + 1)`.

Theorem: PROP-21 is `spqr.v1.chunked.states.epochs_nodup`, in
`Spqr/Specs/V1/Chunked/States/EpochUniqueness.lean`. The Lean names and docstrings do not
carry the ID; this row is the mapping.

Status: **Proved (draft PR #574, branch `la/prop-21`, not yet on `main`)**, conditional on
aeneas#1043, in `Spqr/Specs/V1/Chunked/States/EpochUniqueness.lean`. The structural part is
`send_key_epoch` and `recv_key_epoch` (only these arms can emit) with their converses
`send_HeaderReceived_key_isSome` and `recv_EkSentCt1Received_key_isSome` (those arms always
emit when they succeed); the trace part is `epochs_nodup`, via
`epochs_consecutive` (keys at `keyFloor s, keyFloor s + 1, …`) and
`epochs_strictly_increase`. Every theorem over runs inherits `sorryAx` from
`States.send` through the map-iterator `next := sorry` (aeneas#1043); `recv_key_epoch`
does not. Scope: the crate with overflow checks, or a release run in which no call
overflows (Spec §3.8); `States`, not the public API. Statement ACCEPT:
`docs/statement-reviews/PROP-21-trace-and-recv-half-2.md`.

### PROP-22 Epoch agreement

`t_snd` returned by `Send` equals `t_rcv` returned by the matching `Receive`.

Source: Spec §1.1; src/lib.rs:300; src/lib.rs:427

In the code both equal `msg.epoch - 1`, so the property holds by
construction once the wire epoch is the sender's state epoch:
for every `States` variant, `send` puts `state.epoch()` in `msg.epoch`
(`states.rs:120-271`), and no `send` arm changes the epoch.
Status: **Open**. Note that the spec's own pseudocode computes `t_rcv` as
`state.epoch - 1` of the receiver, which differs from `t_snd` for delayed
messages; the code's choice is the one that satisfies the property.

### PROP-23 Sender and receiver epoch knowledge

When `Send` returns `t_snd` (resp. `Receive` returns `t_rcv`), the caller has
emitted keys for that epoch and all earlier ones.

Source: Spec §1.1; src/lib.rs:298; src/lib.rs:430

With `t_snd = msg.epoch - 1` this says: a party at state epoch `e` has emitted
keys for epochs `1..e-1`. Trace property over the v1 machine plus the chain
(`chain.add_epoch` is called with every emitted key, `lib.rs:298,430`).
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

Source: Spec §1.2; src/incremental_mlkem768.rs:34-156

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

Status: **Axiom** (`validate_pk_bytes` is a libcrux stub). The exact byte
string hashed must be taken from libcrux, not from the spec prose
"`ek_seed || ek_vector`": FIPS 203 places the seed last in the encoded key.

---

## 4. Erasure code and field arithmetic (§1.3, §2.2 Encode/Decode, §3.6)

### LEAN-ENC-1 Point roundtrip

`Pt.deserialize(Pt.serialize(p)) = ok p`. **Proved**
(`Spqr/Specs/Encoding/Polynomial/Pt/{Serialize,Deserialize}.lean`).

Source: src/encoding/polynomial.rs:26-44
Evidence: Spqr/Specs/Encoding/Polynomial/Pt/{Serialize,Deserialize}.lean

### LEAN-ENC-2 Decode from any N chunks

If a message fits in `N` codewords, `PolyDecoder` reconstructs it from any
`N` distinct codewords (§3.6). Status: **Axiom** required for
`decoded_message`; the surrounding encoder/decoder functions have specs
(`Spqr/Specs/Encoding/{Encoder,Decoder,Polynomial}/`).

Source: Spec §3.6; src/encoding/polynomial.rs:905-911
Evidence: Spqr/Specs/Encoding/{Encoder,Decoder,Polynomial}/

### LEAN-GF GF(2^16) arithmetic

`GF16` add, sub, eq, mul, div and their assign forms agree with
`GaloisField 2 16` (`Spqr/Math/Gf16/Field.lean:31`). **Proved**
(`Spqr/Specs/Encoding/Gf/`, no `sorry`). `mul2_u16` (SIMD dispatch) remains a
stub; the unaccelerated path is the one verified.

Source: Spec §2.2; src/encoding/gf.rs:16-196
Evidence: Spqr/Math/Gf16/Field.lean:31; Spqr/Specs/Encoding/Gf/

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
`chain.rs:232,331,357`), within the HKDF-SHA256 limit of 8160. `hkdf_to_vec_spec`
(**Proved**) needs `okm_len ≤ 255 * 32`; each call site discharges it by
evaluation.

Source: Spec §2.2; src/authenticator.rs:51; src/v1/unchunked/send_ct.rs:135; src/v1/unchunked/send_ek.rs:156; src/chain.rs:232; src/chain.rs:331; src/chain.rs:357

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

`Message::serialize(m, index)` produces `messageBytes m index` and
`Message::deserialize` parses version byte, varint epoch, varint index, payload
tag, and chunk, returning `(m, index, bytes_consumed)`
(`v1/chunked/states/serialize.rs:221,248`). **Proved** as
`Message.serialize_spec` and `Message.deserialize_spec`
(`Spqr/Specs/V1/Chunked/States/Serialize/Message/`). The composed roundtrip
`deserialize(serialize(m, i)) = ok (m, i, _)` is **Open**.

Source: Spec §2.3; src/v1/chunked/states/serialize.rs:221; src/v1/chunked/states/serialize.rs:248
Evidence: Spqr/Specs/V1/Chunked/States/Serialize/Message/
Domain: the composed roundtrip is **false unrestricted**, so it is asserted on the
domain the code round-trips. The domain is derived from `Message.deserialize_spec`
(`Deserialize.lean:59-80`) by taking every hypothesis it carries plus every success
conjunct the composition has to establish: (1) `0 < m.epoch` — `deserialize` rejects
a zero wire epoch (`Deserialize.lean:66`, `serialize.rs:254-256`); (2) for
`payload = Ct1Ack b`, `b = true` — `deserialize` always rebuilds `Ct1Ack(true)`
(`Deserialize.lean:76`, `serialize.rs:267`); (3) the length bound
`hlen : from.length + 32 ≤ usize::MAX` (`Deserialize.lean:61`) instantiated at
`serialize`'s output, which `Message.serialize_spec` has no precondition to supply
(`Serialize.lean:75-77`) and which is therefore discharged from the model's own
length bound rather than assumed. That bound is **52 bytes**, and it is recorded here
with the derivation that produces it so a later reader re-derives it rather than
trusting it. The model is
`messageBytes msg index = 1 :: (varintBytes msg.epoch.val ++ varintBytes index ++
payloadTag msg.payload :: payloadChunkBytes msg.payload)`
(`Spqr/Specs/V1/Chunked/States/Serialize/Message/Serialize.lean:61-63`), whose payload
block is `chunkBytes c = varintBytes c.index.val ++ c.data.val.map UScalar.val`
(`Spqr/Specs/V1/Chunked/States/Serialize/EncodeChunk.lean:41-42`), and
`varintBytes a = if a < 128 then [a] else (a % 128 + 128) :: varintBytes (a / 128)`
(`Spqr/Specs/V1/Chunked/States/Serialize/EncodeVarint.lean:32-33`) is the base-128
LEB128 recursion, which emits `ceil(w / 7)` bytes for a `w`-bit argument and so fixes
each summand from its argument's type width alone. Term by term: **1** for the version
byte; **10** for `varintBytes msg.epoch.val`, since `msg.epoch : U64` and
`ceil(64 / 7) = 10`; **5** for `varintBytes index`, since `index : U32` is the argument
type of `Message.serialize_spec` (`Serialize.lean:75`) and `ceil(32 / 7) = 5`; **1** for
the payload tag; **3** for `varintBytes c.index.val`, since `c.index : U16` and
`ceil(16 / 7) = 3`; and **32** for `c.data`, an `Array U8 32`
(`SrcTranslated/Types.lean:904-906`) — in total `1 + 10 + 5 + 1 + 3 + 32 = 52`.
`docs/statement-reviews/STRUCT-02b-canonicity-2.md:87` computes the same 52
independently. This replaces an earlier `57`, and it is not a typo correction: 57
happened to be a true bound, since 52 ≤ 57, but it was an unsourced literal inside the
document whose stated purpose is that every number resolves, and this phase's own
ACCEPT artifact contradicted it. Items (1) and
(2) are genuine restrictions — outside them the composition is false, not merely
unproved; item (3) is an obligation the proof must discharge. The proof also needs a
`varintBytes`-to-`varintBlockAt` agreement lemma, which is a support lemma and not a
domain restriction. This is a domain qualification on a false claim, not a
restatement: the asserted conclusion is unchanged and the row stays **Open**.
Evidence: Spqr/Specs/V1/Chunked/States/Serialize/Message/Deserialize.lean:61,65-77

The `index` field is the chain layer's per-message key index from
`chain.send_key` (`lib.rs:300`). §2.3 lists only `{epoch, type, data}` and
leaves the encoding to the implementer, so this is permitted, but the wire
format is SPQR-specific rather than a pure ML-KEM Braid message.

### STRUCT-02a Wire format is not injective

The converse of PROP-35 — does a byte string have at most one parse, and does a
message have at most one encoding? — is nowhere in the catalog, and for this wire
format it is **false**. `Message::serialize` is not injective on messages and
`Message::deserialize` is not injective on byte strings, and both are witnessed:

1. **Tag collapse.** `Message { epoch: 1, payload: Ct1Ack(false) }` and
   `Message { epoch: 1, payload: Ct1Ack(true) }` have the same serialization:
   `serialize` writes only the type tag, and `MessageType::from_payload`
   (`serialize.rs:124`) maps both Booleans to `MessageType::Ct1Ack`, while
   `deserialize` always rebuilds `Ct1Ack(true)` (`serialize.rs:267`).
2. **Non-minimal LEB128.** Two sub-families, and the distinction matters because
   `deserialize`'s successful result is a triple whose third component is the
   consumed-byte cursor. *On the projection:* `01 01 00 00` and `01 81 00 00 00`
   deserialize to the same `(message, index)` — `Message { epoch: 1, payload: None }`
   with index `0` — and differ only in the cursor (`4` against `5`), because
   `decode_varint` (`serialize.rs:152`) accepts a non-minimal block. *On the whole
   result, cursor included:* a ten-byte varint block truncates `% 2^64`, so
   `01 81 80 80 80 80 80 80 80 80 00 00 00` and
   `01 81 80 80 80 80 80 80 80 80 02 00 00` both decode to
   `(Message { epoch: 1, payload: None }, 0, 13)`. It is the second sub-family that
   carries the unqualified claim above; the first carries only the projection form.
3. **Trailing bytes** are a further, separate source of non-injectivity:
   `deserialize` accepts data past the consumed prefix deliberately, for forward
   compatibility (`serialize.rs:274-277`), so every accepted byte string extends to
   unboundedly many others with the same `(message, index)`.

A negative result **discharges** this row — that is why it is stated separately from
STRUCT-02b: what is to be recorded is that the converse fails, with the witnesses
named. Status: **Open**.

What is *not* claimed: whether the non-injectivity is exploitable depends on what is
MAC'd against what is parsed, which has not been checked and is recorded as v2
SEC-01. This is a functional-correctness row, not a security claim.

Source: src/v1/chunked/states/serialize.rs:95-202; src/v1/chunked/states/serialize.rs:221-280
Evidence: Spqr/Specs/V1/Chunked/States/Serialize/DecodeVarint.lean:43-44
Review: ACCEPT 2026-09-15 (round 2 of 2; round 1 REVISE) — docs/statement-reviews/STRUCT-02a-witness-2.md, statement docs/statements/STRUCT-02a-witness.md SHA c67dbc81074ec89b10b03529bbe27c842eca9434c7a51467fdef6cdc26323f6c; both rounds logged in docs/spec-review-log.md

### STRUCT-02b Canonical encodings deserialize injectively

Restricted to canonical encodings — the varint blocks minimal, no trailing bytes,
and the byte string in the image of `Message::serialize` — `Message::deserialize` is
injective: if two such byte strings deserialize to the same `(message, index)` then
they are equal, and so are their cursors. Canonicity is a predicate to be written
down, not an adjective; it is what excludes each of STRUCT-02a's three witness
families.

This is the half of PROP-35's converse that is true and useful, and it rests on the
same `varintBytes`-to-`varintBlockAt` agreement lemma PROP-35's roundtrip needs,
which is why both sit in Phase 3. Status: **Open**.

Source: src/v1/chunked/states/serialize.rs:95-202; src/v1/chunked/states/serialize.rs:221-280
Evidence: Spqr/Specs/V1/Chunked/States/Serialize/DecodeVarint.lean:43-44
Review: ACCEPT 2026-09-15 (round 2 of 2; round 1 REVISE) — docs/statement-reviews/STRUCT-02b-canonicity-2.md, statement docs/statements/STRUCT-02b-canonicity.md SHA 07ec125c878134612cf0cce59860fe38d9a44b6890bfc218c42ec96a8a6454e0; both rounds logged in docs/spec-review-log.md

Both rows are grounded in the code, not in the spec: §2.3 lists only
`{epoch, type, data}` and leaves the encoding to the implementer, so canonicity is
not mandated by the spec. The cited range `serialize.rs:95-202` carries the
primitives the two rows are about — the `MessageType` enum and its `try_from`
(`:97`, `:109`), `from_payload` (`:124`), `encode_varint` (`:139`), `decode_varint`
(`:152`) and `encode_chunk`/`decode_chunk` (`:184`, `:190`) — and `:221-280` carries
`serialize` and `deserialize` themselves.

### PROP-36 Epoch zero rejected

`deserialize` returns `Err(MsgDecode)` when the wire epoch is 0
(`v1/chunked/states/serialize.rs:254-256`), so `msg.epoch - 1` in `lib.rs`
cannot underflow. **Proved** (part of `deserialize_spec`: `0 < msg.epoch`).

Source: src/v1/chunked/states/serialize.rs:254-256; src/lib.rs:427

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
   `From<authenticator::Error>` impl at `lib.rs:145-149`. A caller cannot
   distinguish a header-MAC failure from a ciphertext-MAC failure and must not
   branch on the difference.
2. *What happens to the caller's state.* `lib.rs:356` takes the state by
   immutable reference (`state: &SerializedState`), and the successful
   `Recv { state, key }` is constructed only at `lib.rs:438-445`. On the error
   path it is never constructed: the caller's serialized state is unchanged bytes,
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

Source: Spec §2.4; src/authenticator.rs:13; src/authenticator.rs:15; src/v1/unchunked/send_ct.rs:107-112; src/v1/unchunked/send_ek.rs:144-160; src/lib.rs:145-149; src/lib.rs:356; src/lib.rs:438-445

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

Source: Spec §2.5; src/v1/chunked/states.rs:275-532; src/v1/chunked/states.rs:513-526

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
`msg.payload` (`states.rs:513-526`); and with `msg.epoch < state.epoch()` it
returns `Ok { state, key = None }`, the state unchanged, for every variant. The
spec's no-op on a future epoch is asserted nowhere in this catalog.

Status: Less and Greater rows **Proved (branch)** (`Spqr/Specs/States/Recv.lean` on
`la/lean-v1-protocol-proofs`, draft PR #46, one theorem per variant); Equal rows **Open**.

### PROP-47 Transition refinement

Each spec transition is implemented by the named code path with the same
effect on the state's epoch, authenticator and payload. Transitions 11 and 12
and the `EkSentCt1Received` send arm assert the **code**'s emission and
acceptance sets, not the spec's, per the provisional D3 and D4 decisions in §11.

Source: Spec §2.5; src/v1/chunked/states.rs:115-532; src/v1/chunked/states.rs:175-186; src/v1/chunked/states.rs:464-467; src/v1/chunked/states.rs:484-495

| # | Spec | Code entry | Notes |
|---|------|-----------|-------|
| 1 | KeysUnsampled.Send | `states.rs` KeysUnsampled arm → `unchunked/send_ek.rs` `send_header` | header = `hdr ‖ mac_hdr(epoch, hdr)` |
| 2 | KeysSampled.Receive Ct1 | `states.rs:294` | |
| 3 | HeaderSent.Receive Ct1 (complete) | `states.rs:312` | |
| 4 | Ct1Received.Receive Ct2 | `states.rs:337` | |
| 5 | EkSentCt1Received.Receive Ct2 (complete) | `states.rs:355` → `recv_ct2` | decaps, KDF_OK, `auth.update`, `verify_ct(ct1 ‖ ct2)`, key emitted, epoch + 1 |
| 6 | NoHeaderReceived.Receive Hdr (complete) | `states.rs:385` → `recv_header` | `verify_hdr` before constructing HeaderReceived |
| 7 | HeaderReceived.Send | `states.rs:203` → `send_ct1` | encaps1, KDF_OK, `auth.update`, key emitted |
| 8–10 | Ct1Sampled.Receive Ek / EkCt1Ack | `states.rs:417` → `recv_ek_chunk` | PROP-25 on completion |
| 11 | Ct1Acknowledged.Receive EkCt1Ack | `states.rs:484` | decided (D4): accepts `Ek` as well as `EkCt1Ack`, both routed to `recv_ek_chunk` (`states.rs:489-495`) |
| 12 | EkReceivedCt1Sampled.Receive EkCt1Ack | `states.rs:463` | decided (D3): accepts `Ct1Ack(true)` as well as `EkCt1Ack` (`states.rs:464-467`) |
| 13 | Ct2Sampled.Receive epoch + 1 | `states.rs:513-526` | |

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
(`chunked/send_ct.rs:94` splits `hdr ‖ mac` at `HEADER_SIZE`; libcrux reads
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
`KeysUnsampled(epoch + 1)` (`states.rs:513-526`), which is how side B carries the
epoch forward and reaches `KeysUnsampled_B(e+1)`. Status: **Open**.

Source: Spec §2.6; src/v1/chunked/states.rs:115-532

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
`HEADER_SIZE + MACSIZE` (`chunked/send_ct.rs:72-73`, `chunked/send_ek.rs:208-209`),
ek `ENCAPSULATION_KEY_SIZE` (`chunked/send_ct.rs:96`), ct1 `CIPHERTEXT1_SIZE`
(`chunked/send_ek.rs:86`), ct2 `CIPHERTEXT2_SIZE + MACSIZE`
(`chunked/send_ek.rs:170-171`). Status: **Open**.

Source: Spec §2.2; src/v1/chunked/send_ct.rs:72-73; src/v1/chunked/send_ct.rs:96; src/v1/chunked/send_ek.rs:86; src/v1/chunked/send_ek.rs:170-171; src/v1/chunked/send_ek.rs:208-209

### PROP-49 Key epoch

The emitted `EpochSecret.epoch` is the epoch being negotiated: in
transition 7 it is `state.epoch`; in transition 5 it is the pre-increment
epoch while the new state carries `epoch + 1` (`unchunked/send_ek.rs:163-166`).
This is the value `chain.add_epoch` asserts to be `current_epoch + 1`
(PROP-9). Status: **Proved (draft PR #574, branch `la/prop-21`)** as support lemmas of
PROP-21 (`send_key_epoch`, `recv_key_epoch`), not as a target of its own: each theorem is
about one call, which the statement review ruled Single path
(`docs/statement-reviews/PROP-49-key-epoch-1.md`).

Source: Spec §2.5; src/v1/chunked/states.rs:203-220; src/v1/chunked/states.rs:361-368; src/v1/unchunked/send_ek.rs:163-166

---

## 9. Initialization (§2.6)

### PROP-27 Initial states

`initial_state` with direction A2B yields `KeysUnsampled { epoch: 1, auth:
Authenticator::new(k, 1) }`, with B2A `NoHeaderReceived { epoch: 1, auth:
Authenticator::new(k, 1), header_decoder }` (`lib.rs:198-209`,
`unchunked/send_ek.rs:78-79`, `unchunked/send_ct.rs:94-95`). Status: **Open**.

Source: Spec §2.6; src/lib.rs:198-209; src/v1/unchunked/send_ek.rs:78-79; src/v1/unchunked/send_ct.rs:94-95

### PROP-16 Version negotiation

Not in the spec. If the peer's version is below ours and below
`min_version`, `recv` returns `Error::MinimumVersion`; if below ours with no
`version_negotiation` record, `VersionMismatch` (`lib.rs:373-389`). Status:
**Open**.

Source: src/lib.rs:373-389

---

## 10. Chain layer (`chain.rs`, outside the spec)

The chain turns each SCKA key into per-message keys (SCKA Fig. 2). Properties
here are grounded in the code.

| ID | Statement | Source | Status |
|----|-----------|--------|--------|
| PROP-9 | `add_epoch(es)` with `es.epoch = current_epoch + 1` sets `current_epoch = es.epoch`, derives `next_root` and the new link's send/recv seeds from HKDF(`next_root`, `es.secret`, 96), appends one link, leaves `dir`, `send_epoch`, `params` unchanged | `src/chain.rs:350-368` | **Proved** `add_epoch_spec` (`Spqr/Specs/Chain/Chain/AddEpoch.lean`) |
| PROP-14 | `send_key(epoch)` with `epoch < send_epoch` returns `Err(SendKeyEpochDecreased(send_epoch, epoch))` | `src/chain.rs:384-387` | **Proved** `send_key_spec`, first case (`Spqr/Specs/Chain/Chain/SendKey.lean`, #546) |
| PROP-17 | `ChainEpochDirection::key(at)`: `at > ctr ∧ at - ctr > max_jump` → `Err(KeyJump(ctr, at))`; `at = ctr` → `Err(KeyAlreadyRequested(at))`; `at < ctr` → `prev.get` | `src/chain.rs:247-260` | **Proved** `key_spec_greater_jump`, `key_spec_equal`, `key_spec_less` (`Spqr/Specs/Chain/ChainEpochDirection/Key.lean`) |
| PROP-29 | `epoch_idx(e)`: `Ok(links.len() - 1 - (current_epoch - e))` iff `e ≤ current_epoch` and the difference is below `links.len()`, else `Err(EpochOutOfRange(e))` | `src/chain.rs:372-382` | **Open** |
| PROP-10 | When `send_key` moves `send_epoch` forward it pops links older than `EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH = 1` and clears the send seed of every earlier link; receive seeds are untouched, and `KeyHistory` entries are removed on `get` or trimmed by `gc` | `src/chain.rs:389-399`; `src/chain.rs:314`; `src/chain.rs:145-168`; `src/chain.rs:200` | **Open** |
| PROP-12a | `KeyHistory.data.len() % 36 = 0` (`KEY_SIZE = 4 + 32`, `chain.rs:130`) is preserved by `add`, `get`, `gc` | `src/chain.rs:130-210` | **Proved** (`add_spec`, `get_loop_spec`, `gc_loop_spec` carry the alignment) |
| PROP-12b | `get` after `add` of a fresh counter returns the stored 32-byte key and removes the entry | `src/chain.rs:184-210` | **Open**; `get_loop_spec` gives the per-slot behaviour |
| PROP-37 | `States::from_pb(States::into_pb(s)) = ok s` for all 11 variants | `src/v1/chunked/states/serialize.rs:12-49`; `src/v1/chunked/send_ek/serialize.rs:10-112`; `src/v1/chunked/send_ct/serialize.rs:11-151` | **Open**; per-state `into_pb`/`from_pb` specs exist for all unchunked states and for `KeysUnsampled` |
| PROP-38 | `Chain::from_pb(c.into_pb()) = ok c` | `src/chain.rs:414-452` | **Open**; both functions depend on prost `sorry`s |
| PROP-51 | Along any run of one party's state machine, feeding the emitted keys in order to `add_epoch` never fails, the `assert!(epoch_secret.epoch == self.current_epoch + 1)` included, provided the chain starts one epoch behind the run (`current_epoch + 1 = keyFloor s`, true for `Chain::new` with either init state) and the link buffer has room; the chain ends one behind the run. Over the state machine and `add_epoch` only: no `send_key`/`recv_key`, no serialization, chain present | `src/lib.rs:296-300`; `src/lib.rs:428-431`; `src/chain.rs:350-368`; `src/chain.rs:329-350` | **Open**; statement drafted (`docs/statements/PROP-51-chain-epoch-sync.md`), review pending; needs PROP-21 and PROP-9 |

Finding: PROP-37's statement above is **false as written** (found 2026-09-15), for
two independent reasons. The row is annotated rather than restated: its corrected
statement is deferred to Phase 7 (STRUCT-03, ROADMAP Phase 7 criterion 3), its
asserted conclusion is left untouched, and its status stays `Open` in the sense the
§1 legend now records — no theorem *and* no settled statement.

1. `PolyDecoder::into_pb` narrows `pts_needed` with `as u32`
   (`src/encoding/polynomial.rs:795`), and the merged `into_pb_spec` carries the
   hypothesis `h_cast : self.pts_needed.val ≤ U32.max`
   (`Spqr/Specs/Encoding/Polynomial/PolyDecoder/IntoPb.lean:289`). A decoder above
   that bound has no roundtrip.
2. The unchunked deserializers gate on stored byte-vector lengths while `into_pb`
   copies those vectors verbatim. `Ct1SentEkReceived::from_pb` requires
   `pb.es.len() == 2080 && pb.ct1.len() == 960 && pb.ek.len() == 1152`
   (`src/v1/unchunked/send_ct/serialize.rs:85`) whereas `into_pb` copies `es`, `ek`
   and `ct1` as they stand (`src/v1/unchunked/send_ct/serialize.rs:75-81`).
   Concretely: a `Ct1SentEkReceived` whose `es`, `ek` and `ct1` are empty vectors
   serializes successfully and then fails to deserialize with `Error::StateDecode` —
   with no `PolyDecoder` and no prost `sorry` involved.

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

PROP-38 was checked in the same pass and is **sound as written**: `Chain::into_pb`
and `Chain::from_pb` copy every field verbatim, `params` is already the protobuf
type (`src/chain.rs:120`) so no default-collapsing applies, and
`ChainEpochDirection::from_pb` (`src/chain.rs:306-312`) has no length gate. Its
dependence on the prost `Message` `sorry`s is unchanged and is AXIOM-05's business.

Note on §3.8 (epoch wraparound). Epochs are `u64`. The code excludes
wraparound by assumption (`hax_lib::assume!(current_epoch < u64::MAX)` in
`add_epoch`, `assume!(epoch < u64::MAX)` in `recv_ct2`), `Cargo.toml` sets no
`overflow-checks`, and the Lean theorems take non-overflow as a hypothesis. It
is not proved anywhere and does not need to be at 64 bits; state it as an
assumption.

---

## 11. Deviations from the spec

| ID | Where | Spec | Code | Impact | Source |
|----|-------|------|------|--------|--------|
| D1 | `Authenticator::update` (`authenticator.rs:43-54`) | KDF_AUTH: salt = `root_key`, IKM = `update_key` | salt = `[0u8; 32]`, IKM = `root_key ‖ update_key` | Different key bytes. Not a weakness, but a spec-conformant peer cannot interoperate. Needs a decision from Signal on which side is authoritative. | Spec §2.2; `src/authenticator.rs:43-54` |
| D2 | every `recv` arm | `msg.epoch > epoch` ignored | `Err(EpochOutOfRange)` (except Ct2Sampled at `epoch + 1`) | Tightening; a future-epoch message is an error instead of a no-op. | Spec §2.5; `src/v1/chunked/states.rs:275-532` |
| D3 | `EkSentCt1Received.send` (`states.rs:182`), `EkReceivedCt1Sampled.recv` (`states.rs:464-467`) | sends `None`; accepts only `EkCt1Ack` | sends `Ct1Ack(true)`; accepts `Ct1Ack(true)` too | §2.3 defines the `Ct1Ack` type but §2.5 never uses it; the code does. `Ct1Ack(false)` is never emitted. Motivation is robustness to a lost acknowledgement; no reachable state pair of the spec machine deadlocks without it. | Spec §2.3; Spec §2.5; `src/v1/chunked/states.rs:182`; `src/v1/chunked/states.rs:464-467` |
| D4 | `Ct1Acknowledged.recv` (`states.rs:484-492`) | accepts `EkCt1Ack` | also accepts `Ek` chunks | Out-of-order delivery; comment at `states.rs:485-488`. Integrity still checked by PROP-25. | Spec §2.5; `src/v1/chunked/states.rs:484-492` |
| D5 | MAC failure (§2.4) | "should not proceed with the session and should negotiate a new session" | returns `Err`; caller keeps the previous state and may retry | Weaker than the spec; the session is not aborted by the library. | Spec §2.4; `src/v1/unchunked/send_ct.rs:107`; `src/v1/unchunked/send_ek.rs:160` |
| D6 | the `PROTOCOL_INFO` label literal, at its five sites (`authenticator.rs:47,68,93`, `unchunked/send_ct.rs:131`, `unchunked/send_ek.rs:152`) | §2.2 prescribes `PROTOCOL_INFO` as the concatenation of a protocol identifier, a string representation of KEM and a string representation of MAC, `_`-delimited — the spec's own example is `MyProtocol_MLKEM768_SHA-256`. Only the string *representations* are defined by the implementer; the component set is prescribed. | `Signal_PQCKA_V1_MLKEM768` — a protocol identifier and a KEM representation, and no MAC representation | `PROTOCOL_INFO` feeds both KDF_AUTH and KDF_OK, so a spec-conformant peer building a three-component literal derives a different `root_key`, a different `mac_key` and different session keys, and **cannot interoperate** — the same class as D1, not a naming preference. A second, latent consequence: with the MAC component omitted, two deployments that differ only in their MAC derive identical keys, so the literal does not domain-separate them. That one is dormant today because SPQR fixes MAC = HMAC-SHA256. | Spec §2.2; `src/authenticator.rs:47`; `src/v1/unchunked/send_ct.rs:131`; `src/v1/unchunked/send_ek.rs:152` |

Decisions recorded for the six rows. Each is a **project** decision taken so the
properties have one side to assert; none of them is a Signal ruling, and none of them
authorises a `src/` change:

| ID | Decision | Status |
|----|----------|--------|
| D1 | The properties assert the code: KDF_AUTH is HKDF with salt = `[0u8; 32]` and IKM = `root_key ‖ update_key`, not the spec's salt = `root_key`, IKM = `update_key`. HKDF is not symmetric in its salt and its IKM, so the derived `root_key` and `mac_key` differ from the spec's and **a spec-conformant peer cannot interoperate** — this row and D6 are the two where adopting the code accepts a real interoperability cost rather than a bookkeeping one. Provisional and pending a Signal ruling; settling it needs either a code fix or a spec erratum, and Phase 1 does not speak for Signal on which. | Provisional (2026-09-15) |
| D2 | The properties assert the code: a message with `msg.epoch > state.epoch()` is `Err(EpochOutOfRange)` in every `recv` arm, except `Ct2Sampled` at exactly `epoch + 1`, which transitions to `KeysUnsampled(epoch + 1)` and ignores the payload. Provisional and pending a Signal ruling, not a finding that the tightening is right; settling it needs the spec to mandate strictness or the code to adopt the spec's no-op. | Provisional (2026-09-15) |
| D3 | The properties assert the code: `EkSentCt1Received.send` emits `Ct1Ack(true)` where the spec emits `None`, and `EkReceivedCt1Sampled.recv` accepts `Ct1Ack(true)` alongside `EkCt1Ack`; `Ct1Ack(false)` is never emitted. Provisional and pending a Signal ruling; settling it needs the spec to document the extra message handling or the code to drop it. | Provisional (2026-09-15) |
| D4 | The properties assert the code: `Ct1Acknowledged.recv` also accepts `Ek` chunks, for out-of-order delivery, with encapsulation-key integrity still checked on completion (PROP-25). Provisional and pending a Signal ruling; settling it needs the spec to document the extra accepted type or the code to drop it. | Provisional (2026-09-15) |
| D5 | The properties assert the code: MAC failure returns `Err` — `Error::MacVerifyFailed` at the public API — and the library does not abort the session, so the caller keeps its previous serialized state and may retry. The obligations this puts on the caller are written out once, as the caller contract in **PROP-43, section 7**; this row does not restate it. Provisional and pending a Signal ruling, and the code remains weaker than §2.4 until then; settling it needs the written contract adopted, or the library to abort the session itself. | Provisional (2026-09-15) |
| D6 | The properties assert the code: the two-component literal `Signal_PQCKA_V1_MLKEM768` at all five label sites, carrying a protocol identifier and a KEM representation and no MAC representation. §2.2 prescribes the component set — a protocol identifier, a string representation of KEM and a string representation of MAC — and leaves only the string representations to the implementer, so the omission is a deviation and not an implementer choice. This row and D1 are the two where adopting the code accepts a real interoperability cost rather than a bookkeeping one. Provisional and pending a Signal ruling; settling it needs either a code fix adding the MAC representation to the literal, or a spec erratum permitting a two-component literal. | Provisional (2026-09-16) |

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
| PROP-21 | 2 | Proved (PR branch), conditional on aeneas#1043 |
| PROP-22 | 2 | Open |
| PROP-23 | 2 | Open |
| PROP-24 | 5 | Open |
| PROP-25 | 8 | Open |
| PROP-27 | 9 | Open |
| PROP-29 | 10 | Open |
| PROP-30 | 8 | Proved (branch), Less/Greater rows; Equal rows Open |
| PROP-31 | 7 | Proved |
| PROP-35 | 6 | Proved (components); roundtrip Open |
| PROP-36 | 6 | Proved |
| PROP-37 | 10 | Open |
| PROP-38 | 10 | Open |
| PROP-40 | 7 | Proved |
| PROP-41 | 5 | Proved (labels); KDF_OK literal Open |
| PROP-42 | 5 | Proved |
| PROP-43 | 7 | Open |
| PROP-45 | 5 | Open |
| PROP-47 | 8 | Open |
| PROP-48 | 8 | Open |
| PROP-49 | 8 | Proved (PR branch), support lemmas of PROP-21 |
| PROP-50 | 8 | Open |
| PROP-51 | 10 | Open; statement drafted, review pending |
| LEAN-ENC-1 | 4 | Proved |
| LEAN-ENC-2 | 4 | Axiom |
| LEAN-GF | 4 | Proved |
| STRUCT-02a | 6 | Open |
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
