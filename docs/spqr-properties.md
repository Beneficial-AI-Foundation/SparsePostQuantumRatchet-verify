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
| Proved | Theorem on `main`, no `sorry`, no hand-written axiom beyond `hkdf_to_slice_spec` |
| Proved (branch) | Theorem exists only on `la/lean-v1-protocol-proofs`; not merged. Those proofs also use the liveness axioms in that branch's `Spqr/Specs/External.lean`, three of which assert that defined functions (`PolyEncoder.next_chunk`, `KeysUnsampled.send_hdr_chunk`, `HeaderReceived.send_ct1_chunk`) never fail. Merging requires replacing them with theorems. |
| Open | Statement fixed, no theorem yet |
| Axiom | Cannot be a theorem: the code calls an opaque library function |

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
| `kdf::hkdf_to_slice` | Lean `opaque`; behaviour given by `axiom hkdf_to_slice_spec` (`Spqr/Specs/Kdf/HkdfToSlice.lean:25`) in terms of an RFC 5869 model with `opaque HMAC_SHA256`. The only hand-written axiom. |
| `incremental_mlkem768::potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275` | Axiom stub (contains `log::*` under `cfg(not(hax))`). `encaps2` itself is extracted. |
| `PolyDecoder::decoded_message` | Axiom stub. Blocks the erasure-code roundtrip (LEAN-ENC-2). |
| libcrux `validate_pk_bytes`, `decapsulate_compressed_key`, `encapsulate1/2`, `hmac` | Axiom stubs (`SrcTranslated/FunsExternal.lean`). |
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

Reduces to: both parties' `EpochSecret.secret` for epoch `t` equal
`KDF_OK(ss, t)` for the same ML-KEM shared secret `ss`, which needs PROP-3
(KEM roundtrip) and PROP-24 (both KDF_OK sites identical). Status: **Open**.
Requires the KEM axiom of PROP-3.

### PROP-21 Per-participant epoch uniqueness

Each party outputs at most one key per epoch.

Structural part: exactly two arms of the state machine return a key,
`HeaderReceived.send` (spec transition 7, `states.rs:203-220`) and
`EkSentCt1Received.recv` on a completing `Ct2` chunk (transition 5,
`states.rs:361-368`). All other `send` arms and all other `recv` arms return
`key = None`. Trace part: a party never re-enters either state at the same
epoch, because `HeaderReceived` leaves to `Ct1Sampled` on send and
`EkSentCt1Received` leaves to `NoHeaderReceived(epoch + 1)` on emission.

Status: send half **Proved (branch)** (`Send.lean`, one theorem per variant);
recv half and trace part **Open**.

### PROP-22 Epoch agreement

`t_snd` returned by `Send` equals `t_rcv` returned by the matching `Receive`.

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

With `t_snd = msg.epoch - 1` this says: a party at state epoch `e` has emitted
keys for epochs `1..e-1`. Trace property over the v1 machine plus the chain
(`chain.add_epoch` is called with every emitted key, `lib.rs:298,430`).
Status: **Open**.

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

Status: **Axiom** (`validate_pk_bytes` is a libcrux stub). The exact byte
string hashed must be taken from libcrux, not from the spec prose
"`ek_seed || ek_vector`": FIPS 203 places the seed last in the encoded key.

---

## 4. Erasure code and field arithmetic (§1.3, §2.2 Encode/Decode, §3.6)

### LEAN-ENC-1 Point roundtrip

`Pt.deserialize(Pt.serialize(p)) = ok p`. **Proved**
(`Spqr/Specs/Encoding/Polynomial/Pt/{Serialize,Deserialize}.lean`).

### LEAN-ENC-2 Decode from any N chunks

If a message fits in `N` codewords, `PolyDecoder` reconstructs it from any
`N` distinct codewords (§3.6). Status: **Axiom** required for
`decoded_message`; the surrounding encoder/decoder functions have specs
(`Spqr/Specs/Encoding/{Encoder,Decoder,Polynomial}/`).

### LEAN-GF GF(2^16) arithmetic

`GF16` add, sub, eq, mul, div and their assign forms agree with
`GaloisField 2 16` (`Spqr/Math/Gf16/Field.lean:31`). **Proved**
(`Spqr/Specs/Encoding/Gf/`, no `sorry`). `mul2_u16` (SIMD dispatch) remains a
stub; the unaccelerated path is the one verified.

---

## 5. Parameters (§2.2)

### PROP-45 KEM constants

`HEADER_SIZE = 64`, `EK_SIZE = 1152`, `CT1_SIZE = 960`, `CT2_SIZE = 128` for
ML-KEM-768. Code: `HEADER_SIZE = pk1_len()`, `ENCAPSULATION_KEY_SIZE = pk2_len()`
(`incremental_mlkem768.rs:13,15`), `ensures` clauses 960/2080/32/128 on
`encaps1`/`encaps2`. Status: **Open** (constant evaluation).

### PROP-24 KDF_OK

Both derivation sites, `HeaderReceived::send_ct1` (`unchunked/send_ct.rs:129-135`)
and `EkSentCt1Received::recv_ct2` (`unchunked/send_ek.rs:150-158`), call
`hkdf_to_vec(salt = [0u8; 32], ikm = ss, info = "Signal_PQCKA_V1_MLKEM768:SCKA Key" ‖ epoch_be, 32)`.
This is the spec recipe (salt = zero block of hash length, IKM = shared
secret, info = `PROTOCOL_INFO ‖ ":SCKA Key" ‖ ToBytes(epoch)`, length 32).
Status: **Open**; `hkdf_to_vec_spec` (**Proved**) gives the HKDF value.

### PROP-42 KDF_AUTH info and length

`Authenticator::update(ep, k)` calls HKDF with
`info = "Signal_PQCKA_V1_MLKEM768:Authenticator Update" ‖ ep_be` and length 64,
splitting the output into `root_key = out[..32]`, `mac_key = out[32..]`
(`authenticator.rs:43-54`). Info and length match §2.2. Salt and IKM do not:
see deviation D1. **Proved** as `update_spec`
(`Spqr/Specs/Authenticator/Authenticator/Update.lean`).

### PROP-18 HKDF output lengths

Every production HKDF call requests 32, 64 or 96 bytes
(`authenticator.rs:51`; `unchunked/send_ct.rs:135`; `unchunked/send_ek.rs:156`;
`chain.rs:232,331,357`), within the HKDF-SHA256 limit of 8160. `hkdf_to_vec_spec`
(**Proved**) needs `okm_len ≤ 255 * 32`; each call site discharges it by
evaluation.

### PROP-41 Label prefix

The five info/MAC labels (`authenticator.rs:47,68,93`,
`unchunked/send_ct.rs:131`, `unchunked/send_ek.rs:152`) share the prefix
`Signal_PQCKA_V1_MLKEM768`. There is no `PROTOCOL_INFO` constant in the code.
§2.2 leaves the string representation to the implementer, so omitting a MAC
name is not a deviation. Status: **Proved** indirectly via the label constants
in `update_spec`, `mac_hdr_spec`, `mac_ct_spec`; the KDF_OK literal is not yet
covered.

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

The `index` field is the chain layer's per-message key index from
`chain.send_key` (`lib.rs:300`). §2.3 lists only `{epoch, type, data}` and
leaves the encoding to the implementer, so this is permitted, but the wire
format is SPQR-specific rather than a pure ML-KEM Braid message.

### PROP-36 Epoch zero rejected

`deserialize` returns `Err(MsgDecode)` when the wire epoch is 0
(`v1/chunked/states/serialize.rs:254-256`), so `msg.epoch - 1` in `lib.rs`
cannot underflow. **Proved** (part of `deserialize_spec`: `0 < msg.epoch`).

---

## 7. Ratcheted authenticator (§2.4)

Constants: `MACSIZE = 32` (`authenticator.rs:33`), HMAC-SHA256.

### PROP-31 Init

`Authenticator::new(k, ep)` equals `update(ep, k)` applied to
`{ root_key: 0^32, mac_key: 0^32 }` (`authenticator.rs:34-41`; spec
`Authenticator.Init`). **Proved**: `new_spec` gives the same HKDF expression
as `update_spec` on the zero state.

### PROP-40 MAC inputs

`mac_hdr(ep, hdr) = HMAC(mac_key, "…:ekheader" ‖ ep_be ‖ hdr)` and
`mac_ct(ep, ct) = HMAC(mac_key, "…:ciphertext" ‖ ep_be ‖ ct)`, both 32 bytes
(`authenticator.rs:66-105`). The ciphertext argument is always `ct1 ‖ ct2`
(`unchunked/send_ct.rs:192-193`, `unchunked/send_ek.rs:160`), as in the spec's
`MacCt(epoch, ct1 || ct2)`; this is why `Ct1` chunks carry no MAC of their own.
**Proved**: `mac_hdr_spec`, `mac_ct_spec`.

### PROP-15 Verify accepts own MAC

`verify_hdr(ep, hdr, mac_hdr(ep, hdr)) = Ok(())` and likewise for `ct`.
`verify_*` uses the constant-time `util::compare` (`util.rs:25-33`) and returns
`InvalidHdrMac` / `InvalidCtMac` otherwise. **Proved**: `verify_ct_spec` and
`verify_hdr_spec` state `Ok ↔ mac_* = ok expected_mac`.

### PROP-43 MAC failure

On a failed `verify_hdr` (transition 6, `unchunked/send_ct.rs:107`) or
`verify_ct` (transition 5, `unchunked/send_ek.rs:160`) `States::recv` returns
`Err`, and `lib.rs` writes no new state (it re-decodes state from bytes and
stores only on `Ok`, `lib.rs:356-425`). In transition 5 the check runs after
`decaps` and after `auth.update`, matching the spec's order. Status: **Open**.
See deviation D5 for the spec's stronger requirement.

---

## 8. State machine (§2.5)

`States` (`src/v1/chunked/states.rs:16-29`) has the spec's 11 variants.
Side A (`send_ek`): KeysUnsampled, KeysSampled, HeaderSent, Ct1Received,
EkSentCt1Received. Side B (`send_ct`): NoHeaderReceived, HeaderReceived,
Ct1Sampled, EkReceivedCt1Sampled, Ct1Acknowledged, Ct2Sampled. The unchunked
types in `src/v1/unchunked/` are the inner core (`uc` field) of these states,
not a separate protocol mode; `lib.rs` uses only `v1::chunked`.

### PROP-30 Epoch and type dispatch

Every `recv` arm compares `msg.epoch` with `state.epoch()`:

| Case | Code | Spec |
|------|------|------|
| `msg.epoch < epoch` | state unchanged, `key = None` | no-op |
| `msg.epoch == epoch`, unexpected payload type | state unchanged, `key = None` | no-op |
| `msg.epoch == epoch`, expected type | transition (table below) | transition |
| `msg.epoch > epoch`, not Ct2Sampled | `Err(EpochOutOfRange)` | no-op (D2) |
| Ct2Sampled, `msg.epoch == epoch + 1` | `KeysUnsampled(epoch + 1)`, payload ignored | transition 13 |
| Ct2Sampled, `msg.epoch > epoch + 1` | `Err(EpochOutOfRange)` | no-op (D2) |

Status: Less and Greater rows **Proved (branch)** (`Recv.lean`, one theorem
per variant); Equal rows **Open**.

### PROP-47 Transition refinement

Each spec transition is implemented by the named code path with the same
effect on the state's epoch, authenticator and payload.

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
| 11 | Ct1Acknowledged.Receive EkCt1Ack | `states.rs:484` | also accepts Ek (D4) |
| 12 | EkReceivedCt1Sampled.Receive EkCt1Ack | `states.rs:463` | also accepts Ct1Ack(true) (D3) |
| 13 | Ct2Sampled.Receive epoch + 1 | `states.rs:513-526` | |

Status: **Open** for all 13. Send arms other than 1 and 7 emit the payload
type the spec prescribes, except `EkSentCt1Received.send`, which emits
`Ct1Ack(true)` where the spec emits `None` (D3).

State contents match the spec's per-state lists, with one representational
difference: `ek_seed` and `hek` are held as a single 64-byte `hdr`
(`chunked/send_ct.rs:94` splits `hdr ‖ mac` at `HEADER_SIZE`; libcrux reads
the seed and hash out of `hdr`).

### PROP-50 Structural liveness

From `(KeysUnsampled_A(e), NoHeaderReceived_B(e))`, every fair interleaving of
`send`/`recv` with every message eventually delivered reaches
`(NoHeaderReceived_A(e+1), KeysUnsampled_B(e+1))`, and every reachable state
pair has a next step (§2.6: "Alice and Bob will always be able to make forward
progress as long as fresh messages are delivered"; Fig. 2 gives the reachable
pairs). D2 matters here: a future-epoch message is an error rather than a
no-op, so the property holds only for in-order delivery across epochs.
Status: **Open**.

### PROP-25 Encapsulation-key integrity

Whenever the `ek_decoder` completes, `ek_matches_header(ek, hdr)` is checked
before `ek` is used, and failure returns `Err(ErroneousDataReceived)`.
Single call site `Ct1Sent::recv_ek` (`unchunked/send_ct.rs:160-169`), reached
from `Ct1Sampled` and `Ct1Acknowledged` with either `Ek` or `EkCt1Ack`
chunks (four combinations). Status: **Open**; the meaning of the check is
PROP-3b.

### PROP-48 Decoder sizes

Decoders are created with the spec's message sizes: header
`HEADER_SIZE + MACSIZE` (`chunked/send_ct.rs:72-73`, `chunked/send_ek.rs:208-209`),
ek `ENCAPSULATION_KEY_SIZE` (`chunked/send_ct.rs:96`), ct1 `CIPHERTEXT1_SIZE`
(`chunked/send_ek.rs:86`), ct2 `CIPHERTEXT2_SIZE + MACSIZE`
(`chunked/send_ek.rs:170-171`). Status: **Open**.

### PROP-49 Key epoch

The emitted `EpochSecret.epoch` is the epoch being negotiated: in
transition 7 it is `state.epoch`; in transition 5 it is the pre-increment
epoch while the new state carries `epoch + 1` (`unchunked/send_ek.rs:163-166`).
This is the value `chain.add_epoch` asserts to be `current_epoch + 1`
(PROP-9). Status: **Open**.

---

## 9. Initialization (§2.6)

### PROP-27 Initial states

`initial_state` with direction A2B yields `KeysUnsampled { epoch: 1, auth:
Authenticator::new(k, 1) }`, with B2A `NoHeaderReceived { epoch: 1, auth:
Authenticator::new(k, 1), header_decoder }` (`lib.rs:198-209`,
`unchunked/send_ek.rs:78-79`, `unchunked/send_ct.rs:94-95`). Status: **Open**.

### PROP-16 Version negotiation

Not in the spec. If the peer's version is below ours and below
`min_version`, `recv` returns `Error::MinimumVersion`; if below ours with no
`version_negotiation` record, `VersionMismatch` (`lib.rs:373-389`). Status:
**Open**.

---

## 10. Chain layer (`chain.rs`, outside the spec)

The chain turns each SCKA key into per-message keys (SCKA Fig. 2). Properties
here are grounded in the code.

| ID | Statement | Code | Status |
|----|-----------|------|--------|
| PROP-9 | `add_epoch(es)` with `es.epoch = current_epoch + 1` sets `current_epoch = es.epoch`, derives `next_root` and the new link's send/recv seeds from HKDF(`next_root`, `es.secret`, 96), appends one link, leaves `dir`, `send_epoch`, `params` unchanged | `chain.rs:350-368` | **Proved** `add_epoch_spec` (`Spqr/Specs/Chain/Chain/AddEpoch.lean`) |
| PROP-14 | `send_key(epoch)` with `epoch < send_epoch` returns `Err(SendKeyEpochDecreased(send_epoch, epoch))` | `chain.rs:384-387` | **Proved (branch)** |
| PROP-17 | `ChainEpochDirection::key(at)`: `at > ctr ∧ at - ctr > max_jump` → `Err(KeyJump(ctr, at))`; `at = ctr` → `Err(KeyAlreadyRequested(at))`; `at < ctr` → `prev.get` | `chain.rs:247-260` | **Proved** `key_spec_greater_jump`, `key_spec_equal`, `key_spec_less` (`Spqr/Specs/Chain/ChainEpochDirection/Key.lean`) |
| PROP-29 | `epoch_idx(e)`: `Ok(links.len() - 1 - (current_epoch - e))` iff `e ≤ current_epoch` and the difference is below `links.len()`, else `Err(EpochOutOfRange(e))` | `chain.rs:372-382` | **Open** |
| PROP-10 | When `send_key` moves `send_epoch` forward it pops links older than `EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH = 1` and clears the send seed of every earlier link; receive seeds are untouched, and `KeyHistory` entries are removed on `get` or trimmed by `gc` | `chain.rs:389-399, 314, 145-168, 200` | **Open** |
| PROP-12a | `KeyHistory.data.len() % 36 = 0` (`KEY_SIZE = 4 + 32`, `chain.rs:130`) is preserved by `add`, `get`, `gc` | `chain.rs:130-210` | **Proved** (`add_spec`, `get_loop_spec`, `gc_loop_spec` carry the alignment) |
| PROP-12b | `get` after `add` of a fresh counter returns the stored 32-byte key and removes the entry | `chain.rs:184-210` | **Open**; `get_loop_spec` gives the per-slot behaviour |
| PROP-37 | `States::from_pb(States::into_pb(s)) = ok s` for all 11 variants | `chunked/{send_ek,send_ct}/serialize.rs` | **Open**; per-state `into_pb`/`from_pb` specs exist for all unchunked states and for `KeysUnsampled` |
| PROP-38 | `Chain::from_pb(c.into_pb()) = ok c` | `chain.rs:414-452` | **Open**; both functions depend on prost `sorry`s |

Note on §3.8 (epoch wraparound). Epochs are `u64`. The code excludes
wraparound by assumption (`hax_lib::assume!(current_epoch < u64::MAX)` in
`add_epoch`, `assume!(epoch < u64::MAX)` in `recv_ct2`), `Cargo.toml` sets no
`overflow-checks`, and the Lean theorems take non-overflow as a hypothesis. It
is not proved anywhere and does not need to be at 64 bits; state it as an
assumption.

---

## 11. Deviations from the spec

| ID | Where | Spec | Code | Impact |
|----|-------|------|------|--------|
| D1 | `Authenticator::update` (`authenticator.rs:43-54`) | KDF_AUTH: salt = `root_key`, IKM = `update_key` | salt = `[0u8; 32]`, IKM = `root_key ‖ update_key` | Different key bytes. Not a weakness, but a spec-conformant peer cannot interoperate. Needs a decision from Signal on which side is authoritative. |
| D2 | every `recv` arm | `msg.epoch > epoch` ignored | `Err(EpochOutOfRange)` (except Ct2Sampled at `epoch + 1`) | Tightening; a future-epoch message is an error instead of a no-op. |
| D3 | `EkSentCt1Received.send` (`states.rs:182`), `EkReceivedCt1Sampled.recv` (`states.rs:464-467`) | sends `None`; accepts only `EkCt1Ack` | sends `Ct1Ack(true)`; accepts `Ct1Ack(true)` too | §2.3 defines the `Ct1Ack` type but §2.5 never uses it; the code does. `Ct1Ack(false)` is never emitted. Motivation is robustness to a lost acknowledgement; no reachable state pair of the spec machine deadlocks without it. |
| D4 | `Ct1Acknowledged.recv` (`states.rs:484-492`) | accepts `EkCt1Ack` | also accepts `Ek` chunks | Out-of-order delivery; comment at `states.rs:485-488`. Integrity still checked by PROP-25. |
| D5 | MAC failure (§2.4) | "should not proceed with the session and should negotiate a new session" | returns `Err`; caller keeps the previous state and may retry | Weaker than the spec; the session is not aborted by the library. |

Resolution for each is a decision, not a proof: D1 needs either a code fix
or a spec erratum; D2 needs the spec to mandate strictness or the code to
adopt the no-op; D3 and D4 need the spec to document the extra message
handling or the code to drop it; D5 needs the caller's contract written down.
Until decided, the properties above describe the code as it is.

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
| PROP-14 | 10 | Proved (branch) |
| PROP-15 | 7 | Proved |
| PROP-16 | 9 | Open |
| PROP-17 | 10 | Proved |
| PROP-18 | 5 | Proved |
| PROP-21 | 2 | Proved (branch), send half; recv half and trace part Open |
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
| PROP-49 | 8 | Open |
| PROP-50 | 8 | Open |
| LEAN-ENC-1 | 4 | Proved |
| LEAN-ENC-2 | 4 | Axiom |
| LEAN-GF | 4 | Proved |
| D1–D5 | 11 | Deviations |

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
