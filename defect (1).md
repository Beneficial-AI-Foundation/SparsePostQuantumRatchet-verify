# Security-related defects exposed by the specification theorems

This document lists the security-relevant defects of the Rust crate in `src/` (and of its
trusted Lean models) that the spec theorems under `Spqr/Specs/` reveal. A theorem reveals a
defect in one of three ways:

1. **Preconditions the code never establishes.** A spec theorem needs a hypothesis
   (`h_ooo_no_overflow`, `h_epoch`, `h_prev_ctr`, …) that no constructor, deserializer or
   caller in the crate checks. The theorem then describes the code only on a sub-domain; outside
   that sub-domain the code panics, wraps, or returns a wrong value. These hypotheses are the
   invariants the code *should* maintain but does not.
2. **Postconditions that state an unwanted behaviour.** The theorem is proved, but what it
   proves is that the code does something a security property forbids (an unauthenticated state
   change, a non-injective wire format, a lossy comparison).
3. **Explicit deviations and scope exclusions.** The Braid-level files
   (`Spqr/Specs/Braid/**`) name where the code departs from the ML-KEM Braid specification, or
   where a stated security property does **not** cover realistic behaviour.

Every theorem cited below is proved (no `sorry`); the defects are in the Rust source, its
`hax_lib` annotations, or the hand-written externals in `SrcTranslated/FunsExternal.lean`, not
in the proofs.

Severity: **HIGH** = key divergence, reachable panic in a realistic deployment, or an unsound
trusted model; **MEDIUM** = denial of service, downgrade, silently wrong result; **LOW** = latent
or needs an unrealistic precondition. Reach qualifiers: `message` (an on-path attacker suffices),
`blob` (needs influence over the persisted state), `local-config` (needs a bad `ChainParams`),
`32-bit`, `spec` (soundness of models/annotations).

## Identifier scheme

Findings are identified as `SPQR-<CLASS>-<slug>`, not by a running number, so that an ID
encodes *what kind* of defect it is and stays stable when findings are added, split, merged
or withdrawn between revisions of this document.

| Class | Meaning | Section |
|---|---|---|
| `AUTH` | a state change or decision driven by unauthenticated input | Part I |
| `ARITH` | integer/width arithmetic that a spec hypothesis has to assume away | Part II |
| `DESER` | persisted state, parameters or inputs accepted without validation | Part III |
| `CRYPT` | cryptographic hygiene (constant-time, ordering, zeroisation) | Part IV |
| `SPEC` | soundness or scope limits of the trusted base and theorems | Part V |

The slug names the mechanism (`chunk-poison`, `minversion-cast`), never a severity or a
position, so re-scoring or reordering does not change an ID. A withdrawn finding keeps its
ID in the legacy map below with a note; a split finding gets new slugs and the parent is
listed as withdrawn. New findings go into the class they belong to, at the end of that Part.

### Legacy map (revision ≤ 2 used `D1`–`D37`)

| Old | New | Old | New |
|---|---|---|---|
| D1 | SPQR-AUTH-epoch-advance | D20 | SPQR-DESER-is-complete |
| D2 | SPQR-AUTH-ct1ack-accepted | D21 | SPQR-DESER-zero-poly-roundtrip |
| D3 | SPQR-AUTH-late-ek-chunk | D22 | SPQR-DESER-encaps2-endian |
| D4 | SPQR-AUTH-chunk-poison | D23 | SPQR-DESER-ct2sent-assert |
| D5 | SPQR-AUTH-v0-downgrade | D24 | SPQR-DESER-send-assert |
| D6 | SPQR-AUTH-index0-nokey | D25 | SPQR-CRYPT-compare-length |
| D7 | SPQR-AUTH-index-cpu-amp | D26 | SPQR-CRYPT-ratchet-before-verify |
| D8 | SPQR-AUTH-wire-noninjective | D27 | SPQR-CRYPT-no-zeroise |
| D9 | SPQR-ARITH-ooo-u32-overflow | D28 | SPQR-SPEC-pk-hash-order |
| D10 | SPQR-ARITH-params-unchecked | D29 | SPQR-SPEC-future-epoch-err |
| D11 | SPQR-ARITH-trimsize-usize32 | D30 | SPQR-SPEC-rollback-scope |
| D12 | SPQR-ARITH-keyhistory-invariant | D31 | SPQR-SPEC-liveness |
| D13 | SPQR-ARITH-epochidx-trunc32 | D32 | SPQR-AUTH-a-encoder-drop |
| D14 | SPQR-ARITH-encoder-idx-u16 | D33 | SPQR-AUTH-b-encoder-drop |
| D15 | SPQR-DESER-chain-frompb | D34 | SPQR-AUTH-v1-lockin |
| D16 | SPQR-DESER-auth-keylen | D35 | SPQR-DESER-authkey-length |
| D17 | SPQR-DESER-epoch-zero | D36 | SPQR-AUTH-chain-advance-persist |
| D18 | SPQR-DESER-epoch-max | D37 | SPQR-DESER-minversion-cast |
| D19 | SPQR-DESER-poly-points | | |

---

## Part I — Unauthenticated control plane

### SPQR-AUTH-epoch-advance. `Ct2Sampled → KeysUnsampled` epoch advance is unauthenticated (MEDIUM; message, protocol DoS)

**Theorems.** `Spqr/Specs/Braid/StateMachine/EpochDispatch.lean`:
`recv_Ct2Sampled_next_epoch` (total, `@[correctness_spec]`) states

```
States.recv (.Ct2Sampled st) msg = ok (.Ok { key := none, state := .KeysUnsampled ⟨⟨msg.epoch, st.uc.auth⟩⟩ })
```

whenever `msg.epoch.val = st.uc.epoch.val + 1`, **and the payload is not read** (the theorem
holds for every `msg.payload`). `Spqr/Specs/V1/Unchunked/SendCt/Ct2Sent/RecvNextEpoch.lean`
(`recv_next_epoch_spec`) and `Spqr/Specs/V1/Chunked/SendCt/Ct2Sampled/RecvNextEpoch.lean`
confirm that the transition is a pure record construction: no MAC, no hash, no decaps.

**Rust.** `src/v1/chunked/states.rs:514-526`: `if msg.epoch == state.epoch() + 1 { …
Self::KeysUnsampled(state.recv_next_epoch(msg.epoch)) }`. The 4-byte message
`[version, varint(e+1), varint(0), tag]` suffices.

**Why a defect.** The only input to the transition is the epoch field of an unauthenticated
message. An on-path attacker who knows the current epoch (it is in cleartext in every message)
can force B out of `Ct2Sampled` — dropping the `ct2 ‖ mac` encoder that B still needs to stream
to A (`SendCt2Chunk.lean` docstring: "the chunk encoder `sending_ct2` is simply dropped"). If A
has not yet completed `ct2`, A waits forever in `EkSentCt1Received` while B has moved on; the
ratchet deadlocks. In libsignal the outer message MAC would reject the forged message, but
nothing in the SPQR API requires the embedder to authenticate before calling `recv`
(`recv_spec`, `Spqr/Specs/Lib/Recv.lean`, has no such hypothesis).

### SPQR-AUTH-ct1ack-accepted. `Ct1Ack` is accepted in `EkReceivedCt1Sampled` though §2.5 never sends it (MEDIUM; message — sibling of SPQR-AUTH-epoch-advance)

**Theorems.** `Spqr/Specs/Braid/Deviations.lean`, `Braid.Deviation.ct1AckAccepted` (the
deviation docstrings were moved there from `EpochDispatch.lean`; theorems that follow the code
at a deviation carry `@[braid_deviation …]`): `recv_of_eq_refines` (`EpochDispatch.lean`) on
`EkReceivedCt1Sampled` with payload `Ct1Ack true` returns `Ok` with next state `Ct2Sampled`
and no key. `Spqr/Specs/Braid/StateMachine/Refinement.lean` (`send_refines`, `recv_refines`,
`run_refines`) is tagged with the same deviation: the abstract §2.5 machine of `Model.lean`
*follows the code* here rather than the specification. `Spqr/Specs/V1/Chunked/States/Serialize/Message/NotInjective.lean`
(`Message.serialize_ct1Ack_eq`) proves the flag is not even on the wire.

**Rust.** `src/v1/chunked/states.rs:465-474`; the ML-KEM Braid spec (p. 21) acts only on
`EkCt1Ack`.

**Why a defect.** A one-tag-byte unauthenticated message moves the receiver from
`EkReceivedCt1Sampled` to `Ct2Sampled`. The receiver then starts streaming `ct2` for an `ek`
that it has *not* finished receiving, and the module doc notes that whether the session then
completes "is not analyzed". Example (b) in the deviation shows a second reachable path through
state replay (see SPQR-SPEC-rollback-scope).

### SPQR-AUTH-late-ek-chunk. `Ek` chunks are still absorbed in `Ct1Acknowledged` (LOW–MEDIUM; message)

**Theorems.** `Spqr/Specs/Braid/Deviations.lean`, `Braid.Deviation.lateEkChunk`:
`recv_of_eq_refines` (`EpochDispatch.lean`) on `Ct1Acknowledged` with an `Ek` payload adds the
chunk to the `ek` decoder; §2.5 (pp. 21–22) drops it. `Refinement.lean` (`recv_refines`,
`run_refines`) carries `@[braid_deviation Deviation.lateEkChunk]`.

**Why a defect.** Outside a normal run an attacker-supplied `Ek` chunk is fed to the decoder of
a state that, per spec, should accept only `EkCt1Ack`. Because `add_chunk` keeps a low-index
point even when the slot is already full (see SPQR-AUTH-chunk-poison), a forged point can displace a legitimate
one; the decoder then interpolates a wrong `ek`, `ek_matches_header` fails, and `recv`
returns `Err` for the rest of the epoch.

### SPQR-AUTH-chunk-poison. Chunk poisoning is persistent: a forged low-index chunk is never evicted (MEDIUM; message, protocol DoS)

**Theorems.** `Spqr/Specs/Encoding/Polynomial/PolyDecoder/AddChunk.lean` (`add_chunk_spec`,
`IsSortedPushResult`): a point with `x = chunk.index` is inserted when
`poly_idx < necessary_points ∨ pts[poly].len() < necessary_points`, and the push result may be
`old.take j ++ [p] ++ old.drop (j+1)` — a **replacement** of an existing point with the same
`x`. `DecodedMessage.lean` (`decoded_message_spec`): the decoded bytes are the Lagrange
interpolant through the **first** `necessary_points` stored points of each slot. No theorem —
and no code — verifies individual chunks; the only checks are on the *completed* message
(`States.CheckPasses` in `EpochDispatch.lean`: `verify_hdr`, `recv_ct2`, `ek_matches_header`).

**Rust.** `src/encoding/polynomial.rs:905-913`.

**Why a defect.** Chunks are unauthenticated (`KeysSampled/RecvCt1Chunk.lean` docstring: "`ct1`
cannot be authenticated on its own"). An attacker injects one chunk with a small index and
arbitrary data; it displaces the legitimate point at that index, later legitimate chunks are
not accepted once the slot is full, the completed message fails its check, and the state keeps
the poisoned decoder because `recv` returns `Err` without a new state (`lib.rs:460`). The epoch
never completes.

### SPQR-AUTH-v0-downgrade. Empty message finalises a V0 downgrade while `min_version == V0` (LOW–MEDIUM; message, downgrade)

**Theorems.** `Spqr/Specs/Lib/MsgPreamble.lean` (`msg_preamble_spec`): the empty message
parses to `version = 0, epoch = 0, index = 0`. `Spqr/Specs/Lib/Recv.lean`
(`recv_spec_less_v0`, `recvLessPost`): with a V1 state still negotiating and a message of
version `0`, the new state has `inner = None` and `version_negotiation = None`, i.e. the
post-quantum ratchet is **permanently disabled** for the session.

**Rust.** `src/lib.rs:564-571` (empty preamble), `lib.rs:422-445` (`Ordering::Less` arm).

**Why a defect.** A zero-length, unauthenticated message is enough to downgrade a session to V0
as long as the local `min_version` is still `V0`. The downgrade clears `version_negotiation`,
so it cannot be undone. Nothing binds the downgrade decision to the peer.

### SPQR-AUTH-index0-nokey. `index == 0` on an epoch-0 lookup returns an empty key (LOW–MEDIUM; message, downgrade-adjacent)

**Theorems.** `Spqr/Specs/Chain/Chain/RecvKey.lean` (`recv_key_spec`, step 0): `epoch = 0 ∧
index = 0 → Ok(vec![])`, chain unchanged. `Recv.lean` (`recvV1Post`): an empty key is mapped to
`key = none`. The `Ordering::Greater` path (`recvGreaterPost`) always reads from `ZERO_EPOCH`.

**Rust.** `src/chain.rs:417-419`, `src/lib.rs:401-406`, `lib.rs:478-480`.

**Why a defect.** The attacker-controlled `index` field decides whether the caller receives a
message key or `None`. An on-path attacker who rewrites `index` to `0` on a message that
exercises epoch 0 makes the receiver skip the PQ key for that message without any error, and
the chain is untouched so the untampered original is still accepted later. The host sees only
`key: None`, which is also the legitimate V0 answer.

### SPQR-AUTH-index-cpu-amp. Pre-authentication computational amplification via `index` (LOW–MEDIUM; message, CPU DoS)

**Theorems.** `Spqr/Specs/Chain/ChainEpochDirection/Key.lean` (`key_spec`, `KeyLoopInv`):
for `ctr < ats ≤ ctr + max_jump`, `key` performs `ats − ctr` iterations of
`next_key_internal`, each one HKDF-SHA256 (`NextKeyInternal.lean`), plus up to `max_ooo`
`KeyHistory::add`s. `Spqr/Specs/Chain/ChainParams/MaxJumpOrDefault.lean`: default
`max_jump = 25 000`.

**Rust.** `src/lib.rs:435` calls `chain.recv_key(epoch, index)` before any MAC in the system is
checked (`verify_hdr`/`verify_ct` run only on chunk-completion edges).

**Why a defect.** Rewriting the `index` varint of each message to `ctr + 25 000` forces
25 000 HKDFs per message; since the host MAC subsequently fails and the clone is dropped,
`ctr` does not advance and the cost can be re-imposed indefinitely. Work per unauthenticated
message should be bounded by the authenticated state, not by a field the attacker writes.

### SPQR-AUTH-wire-noninjective. The wire format is not injective and `recv` cannot tell encodings apart (LOW; message)

**Theorems.** `NotInjective.lean`: `Message.serialize_parse_not_injective` and
`recv_on_witnesses_eq`. Three distinct collisions are proved: (a) `Ct1Ack false` and
`Ct1Ack true` serialize identically; (b) `decode_varint` accepts non-minimal LEB128
(`01 01 00 00` ≡ `01 81 00 00 00`); (c) trailing bytes after the message are ignored.
`Spqr/Specs/V1/Chunked/States/Serialize/DecodeVarint.lean` additionally shows the 10th byte's
high bits are **silently truncated** (`varintVal … % 2 ^ 64`).

**Why a defect.** A message can be re-encoded by an attacker into a different byte string
with the same meaning. Any outer logic that hashes, deduplicates or signs the *bytes* of the
SPQR message can be confused, and replay-detection keyed on bytes fails. Non-canonical varints
and trailing data should be rejected.

### SPQR-AUTH-a-encoder-drop. A's encoders are dropped on the *first* chunk of the next flow: `sending_hdr` on `Ct1`, `sending_ek` on `Ct2` (HIGH; message, protocol deadlock)

**Theorems.** `Spqr/Specs/V1/Chunked/SendEk/KeysSampled/RecvCt1Chunk.lean`
(`recv_ct1_chunk_spec`): the result is `HeaderSent { uc, sending_ek, receiving_ct1 }` with a
*fresh* 480-point decoder holding exactly the 16 points of the one chunk received; the docstring
states "The header encoder `sending_hdr` is dropped: once B sends `ct1` chunks it has
necessarily decoded the whole header." `Spqr/Specs/V1/Chunked/SendEk/Ct1Received/RecvCt2Chunk.lean`
(`recv_ct2_chunk_spec`): "Returns `{ uc := self.uc, receiving_ct2 }`; the encoder
`self.sending_ek` is dropped." Neither theorem has any hypothesis on the chunk's contents, and
`EpochDispatch.lean` (`recv_of_eq_refines`) confirms the dispatcher fires both transitions on
the payload *tag* alone.

**Rust.** `src/v1/chunked/send_ek.rs:85-98` (`KeysSampled::recv_ct1_chunk`),
`send_ek.rs:164-180` (`Ct1Received::recv_ct2_chunk`); dispatch at
`src/v1/chunked/states.rs:294-305` and `337-347`.

**Why a defect.** The inference "B sent `ct1`, so B has the header" is only valid if the `ct1`
chunk came from B. A single forged message `[1, varint(e), varint(i), tag=Ct1, varint(0), 32
bytes]` sent to A in `KeysSampled` makes A discard the header encoder and start streaming `ek`.
If B has not yet decoded the 96-byte header‖MAC (B is in `NoHeaderReceived`, which accepts only
`Hdr`; `states.rs:386-404`), B never leaves that state and A never sends another header chunk:
the epoch deadlocks. The `Ct2` variant is the same one state later — A in `Ct1Received` stops
streaming `ek` and starts sending `Ct1Ack`, which B in `Ct1Sampled`/`Ct1Acknowledged` ignores,
while B still needs `ek` chunks. Unlike SPQR-AUTH-epoch-advance, no epoch field has to be guessed: the current epoch
and any index are in cleartext in every message. The forged chunk is also absorbed into the
fresh decoder (a SPQR-AUTH-chunk-poison poison, now at index 0 of a brand-new decoder).

### SPQR-AUTH-b-encoder-drop. A forged `EkCt1Ack` chunk makes B drop `sending_ct1` before A has `ct1` (HIGH; message, protocol deadlock)

**Theorems.** `Spqr/Specs/V1/Chunked/SendCt/Ct1Sampled/RecvEkChunk.lean`:
`recv_ek_chunk_spec` and `recv_ek_chunk_spec_still_receiving`. With `ct1_ack = true` and the
`ek` decoder still incomplete the result is `StillReceiving (Ct1Acknowledged { uc, receiving_ek
})`; the postcondition for that arm has **no** conjunct about `sending_ct1`, whereas the
`StillReceivingStillSending` and `StillSending` arms carry `st.sending_ct1 = self.sending_ct1`.
`EpochDispatch.lean` shows `ct1_ack` is set from the message tag alone (`EkCt1Ack ⇒ true`).

**Rust.** `src/v1/chunked/send_ct.rs:191-192`; dispatch `src/v1/chunked/states.rs:418-457`;
`Ct1Acknowledged::send` emits `MessagePayload::None` (`states.rs:247-257`).

**Why a defect.** `EkCt1Ack` is A's statement "I have your `ct1`". Nothing authenticates it:
one forged `EkCt1Ack` message in the current epoch moves B to `Ct1Acknowledged`, where B sends
nothing but `None`. If A is still in `HeaderSent` collecting `ct1` chunks, A can never reach
`Ct1Received`, never sends the real `EkCt1Ack`, and the epoch deadlocks. This is the B-side
mirror of SPQR-AUTH-a-encoder-drop and is independent of SPQR-AUTH-ct1ack-accepted (which concerns the *later* state
`EkReceivedCt1Sampled` and the `Ct1Ack` flag).

### SPQR-AUTH-v1-lockin. Any same-version message locks a negotiating session to V1; a genuine V0 peer is then rejected forever (MEDIUM; message — dual of SPQR-AUTH-v0-downgrade)

**Theorems.** `Spqr/Specs/Lib/Recv.lean` `recvV1Post`: the persisted state of the same-version
V1 path is `{ version_negotiation := none, chain := some …, inner := some (.V1 vs) }` for every
successful `States.recv`; `minVersionU8_none_v1`: once `version_negotiation = none` with a V1
inner state the minimum version is `1`, and `recv_spec_minimum_version_*` returns `Err
MinimumVersion` for any message with version `< 1`. `EpochDispatch.lean` (`recv_of_eq_refines`)
shows that a `None` payload is accepted unchanged by every state.

**Rust.** `src/lib.rs:470-476` (`// Receiving clears our version negotiation.`),
`lib.rs:366-372`.

**Why a defect.** The clearing of `version_negotiation` is meant to record "the peer has proven
it speaks V1". The proof is a message with version byte `1` and a trivially acceptable `None`
tag — 4 bytes that anyone can send. If the real peer is a V0-only client (the case `min_version
= V0` exists for), one forged message during negotiation makes every subsequent genuine V0
message fail with `MinimumVersion`; nothing in the API can re-open negotiation. SPQR-AUTH-v0-downgrade is the
opposite direction (forced downgrade to V0); SPQR-AUTH-v1-lockin is a forced *upgrade* that the honest peer
cannot satisfy. Both stem from version negotiation being decided by unauthenticated bytes.

### SPQR-AUTH-chain-advance-persist. Receive-chain advance driven by the unauthenticated `index` is persisted; legitimate keys become unrecoverable (HIGH; message, key loss)

**Theorems.** `Spqr/Specs/Lib/Recv.lean` `recvV1Post`: after a successful `States.recv` the
result is `chain.recvKeyPost c1 (msg.epoch − 1) mp.index kr c2` and the **updated chain `c2` is
re-encoded into the returned state**; `recvGreaterPost` (newer-version path): the same with
`recv_key c 0 mp.index`, and the state *keeps* `version_negotiation`, so the path stays open.
`Spqr/Specs/Chain/Chain/Defs.lean` `cedKeyAdvancePost`: for `ctr < ats ≤ ctr + max_jump` the
counter becomes `ats`, the history is **cleared** when `ats > ctr + max_ooo`, and GC retains
only records within `max_ooo` of the new counter; `cedKeyLessPost`: a later request below
`ctr − max_ooo` is `Err (KeyTrimmed)`, one at a consumed index is `Err (KeyAlreadyRequested)`;
`cedKeyPost`: `ats = ctr → KeyAlreadyRequested`. `recv_of_eq_refines` (`EpochDispatch.lean`)
shows `States.recv` succeeds without state change on a `None` payload in every state, so the
chain step is reached by any 4-byte message.

**Rust.** `src/lib.rs:462-476` (`recv_key` then `chain.into_pb()` into the persisted state),
`lib.rs:401-419` (`Greater` arm), `src/chain.rs:248-297`.

**Why a defect.** SPQR-AUTH-index-cpu-amp records the *CPU* cost of a forged `index` and notes that in libsignal
"`ctr` does not advance" because the host MAC fails and the clone is dropped. For the crate as
specified, the opposite is true: `recv` returns the advanced chain in `Recv.state` and nothing
tells the embedder to discard it. One message `[1, varint(e), varint(ctr + 25 000), tag=None]`
moves the receive counter of epoch `e − 1` forward by `max_jump`, clears the key history, and
leaves only the last `max_ooo = 2 000` keys; every legitimate message of that epoch with index
`< ctr + 23 000` is then `KeyTrimmed` and the one at exactly `ctr + 25 000` is
`KeyAlreadyRequested`. Repeating the message sweeps the epoch entirely. On the newer-version
path the victim need not even be past negotiation, and the message needs no valid payload at
all (`remaining` is never parsed). The chain for the live epoch is irreversibly damaged — a
confidentiality-preserving but availability-destroying attack on the one direction the attacker
cannot otherwise touch. Any embedder that persists `Recv.state` before an outer MAC check (the
API documents no such ordering) is affected.


---

## Part II — Arithmetic and parameter bounds the specs cannot discharge

**Common root cause.** `src/chain.rs` guards its `u32`/`usize` arithmetic with
`hax_lib::assume!` and `#[hax_lib::requires]`, which are erased at runtime. In the Aeneas
translation they become *hypotheses* of every spec theorem. Nothing in the crate establishes
them.

### SPQR-ARITH-ooo-u32-overflow. `u32` overflow in `KeyHistory::get` trimmed-check (MEDIUM; message + local-config)

**Theorems.** `Spqr/Specs/Chain/KeyHistory/Get.lean` (`get_spec`) and
`Spqr/Specs/Chain/ChainEpochDirection/Key.lean` (`key_spec`) require
`h_ooo_no_overflow : at1 + (maxOoo params).val ≤ U32.max`. `Spqr/Specs/Chain/Chain/Defs.lean`
propagates it into `recvKeyPre` (`index.val + (maxOoo params).val ≤ U32.max`), and
`Recv.lean` into `recvKeyReady`.

**Rust.** `src/chain.rs:192`: `if at + (params.max_ooo_keys_or_default()) < current_ctr`.

**Why a defect.** `at` is the attacker-supplied message `index`. With `index` near `u32::MAX`
the addition overflows: debug builds panic (crash on an unauthenticated message), release
builds wrap so the comparison becomes `small < current_ctr`, and a *valid* out-of-order key is
reported `KeyTrimmed` — the key is silently lost. The spec can only be proved by assuming the
overflow away.

### SPQR-ARITH-params-unchecked. `ChainParams` are never range-checked; `Error::InvalidParams` is dead (MEDIUM; local-config)

**Theorems.** Every chain theorem carries `h_maxooo_bound : (maxOoo params).val < 390451572`
(`key_spec`, `gc_spec`, `trim_size_spec`, `recvKeyPre`) and the 32-bit variants carry
`< 108458770` (`key_spec_32` in `Key32.lean`, `recv_key_spec_32` in `RecvKey32.lean`; the GC
side has no 32-bit variant — `gc_spec_core`'s `h_fit` is the only statement of the bound). `Spqr/Specs/Chain/Chain/New.lean`
(`new_spec`) and `Spqr/Specs/Lib/ChainFromVersionNegotiation.lean` accept any `params`.

**Rust.** `src/chain.rs:84-86` (`assume!(max_ooo < 390451572)`), `src/lib.rs:127`
(`InvalidParams` variant is never constructed).

**Why a defect.** A `ChainParams` with `max_ooo_keys ≥ 390451572` (or `≥ 108458770` on 32-bit)
makes `trim_size` (`max_ooo * 11 / 10 + 1`) overflow `u32`/`usize`. The bound is a documented
precondition that the API neither validates nor exposes; the error variant that exists for it is
unreachable. Note that on 64-bit targets `trim_size` itself computes in `usize` and
`390451572 * 11` fits, so the overflow that `assume!(max_ooo < 390451572)` guards is the
`u32` addition `self.ctr + max_ooo` at `chain.rs:280` and `at + max_ooo` at `chain.rs:192`
(SPQR-ARITH-ooo-u32-overflow), plus the GC threshold `trim_size() * KEY_SIZE` at
`chain.rs:146`; the 64-bit arithmetic in `trim_size` is safe for any `u32` input.

### SPQR-ARITH-trimsize-usize32. `usize` overflow in `trim_size` and the GC threshold on 32-bit (LOW; local-config, 32-bit)

**Theorems.** `Gc.lean` (`gc_spec_core`) needs `h_fit : (max_ooo * 11 / 10 + 1) * 36 ≤
Usize.max`; the 32-bit files exist only because the 64-bit bound `390451572` "would yield
`trim_threshold ≈ 15.4B`, overflowing 32-bit `usize`" (`Gc.lean` docstring).

**Why a defect.** Same parameter, platform-dependent failure: a configuration that works on
64-bit panics or wraps on a 32-bit target.

### SPQR-ARITH-keyhistory-invariant. `KeyHistory` size invariant `data.len() ≤ KEY_SIZE * trim_size()` is not maintained (MEDIUM; spec)

**Theorems.** `Key.lean` requires `h_prev_ctr : self.prev.data.length ≤ 36 * self.ctr.val`
and `h_kh_cap : self.prev.data.length + 36 * (ats − ctr) ≤ Usize.max`;
`Spqr/Specs/Chain/KeyHistory/Add.lean` (`add_spec`) requires `self.data.length + 36 ≤
Usize.max` and grows the history unconditionally. `Gc.lean` only trims when `trim_threshold ≤
data.length`, and `gc_spec_core` needs `h_key_ge` (`max_ooo ≤ current_key`) to say anything
about the trimmed result.

**Rust.** `src/chain.rs:138, 174` (`#[hax_lib::requires(... self.data.len() <= KEY_SIZE *
_params.trim_size())]`).

**Why a defect.** The hax annotation claims an invariant that no theorem could prove from the
code; it has to be assumed at every call. If it is false (e.g. a blob with a long `prev`), `get`
and `remove` operate outside their verified domain.

### SPQR-ARITH-epochidx-trunc32. `u64 → usize` truncation in `Chain::epoch_idx` on 32-bit (MEDIUM; 32-bit)

**Theorems.** `Spqr/Specs/Chain/Chain/EpochIdx.lean` (`epoch_idx_spec`) requires
`h_diff_fits : epoch ≤ current_epoch → current_epoch − epoch ≤ Usize.max`; `RecvKey.lean`,
`SendKey.lean`, and `Recv.lean` (`recvKeyReady`) all inherit it.

**Rust.** `src/chain.rs:382`: `let back = (self.current_epoch - epoch) as usize;`.

**Why a defect.** On a 32-bit target an `epoch` more than `2³²` below `current_epoch` is
truncated; `back` can become small, pass `back < links`, and the wrong link is selected.
The theorem is simply not stated for that input.

### SPQR-ARITH-encoder-idx-u16. `PolyEncoder` index truncation `u32 → u16` (LOW; blob or long-running session)

**Theorems.** `Spqr/Specs/V1/Chunked/SendCt/Ct2Sampled/SendCt2Chunk.lean`
(`send_ct2_chunk_spec`) requires `h_idx_fits : idx ≤ U16.max`, with the docstring: "Rust's
`self.idx as u16` (`src/encoding/polynomial.rs:759`) truncates silently".

**Why a defect.** After 65 536 chunks of one `ct2` (or a blob with `idx ≥ 2¹⁶`), chunk
`index` wraps and the encoder re-emits points at already-used abscissae, so the receiver's
decoder (`add_chunk`) discards or replaces them; the message can never complete.


---

## Part III — Deserialisation without validation

### SPQR-DESER-chain-frompb. `ChainEpochDirection::from_pb` / `Chain::from_pb` accept malformed blobs that later panic (HIGH; blob)

**Theorems.** `Spqr/Specs/Chain/ChainEpochDirection/FromPb.lean` (`from_pb_spec`): the result
is `FunctionalModels.fromPb pb`, which rejects only a `next` of length `∉ {0, 32}`; `ctr` and
`prev` are copied verbatim. `Spqr/Specs/Chain/Chain/FromPb.lean`: `next_root` length, `links`
non-emptiness, `current_epoch ≥ send_epoch`, and per-link `prev.data.length % 36 = 0` are not
checked. Downstream, `key_spec` needs `h_next_len : next.length = 32`, `h_prev_aligned :
prev.data.length % 36 = 0`, `h_prev_ctr`; `add_epoch_spec` needs `h_epoch :
epoch_secret.epoch = current_epoch + 1`; `send_key_spec` needs `ce.send.ctr < U32.max`.

**Rust.** `src/chain.rs:306-312`, `445-460`; `chain.rs:191` `assert_eq!(self.data.len() %
KEY_SIZE, 0)`; `chain.rs:361` `assert!(epoch_secret.epoch == self.current_epoch + 1)`.

**Why a defect.** The persisted state is parsed with prost and converted without any
range/length validation. A corrupted or attacker-influenced blob reaches `assert_eq!` (panic),
a `u32` `ctr` overflow in `next_key_internal`, or the `add_epoch` `assert!`. None of these is an
`Err`; all are crashes from state that `from_pb` accepted.

### SPQR-DESER-auth-keylen. `Authenticator::from_pb` does not validate key lengths (LOW; blob)

**Theorems.** `Spqr/Specs/Authenticator/Serialize/Authenticator/FromPb.lean`: `from_pb_spec`
is the identity on both vectors. `VerifyHdr.lean`/`VerifyCt.lean` need `h_key :
mac_key.length ≤ U32.max`; `Update.lean` (`update_spec`) needs `root_key.length + k.length ≤
Usize.max` and *establishes* `root_key.length = 32 ∧ mac_key.length = 32`.

**Why a defect.** An over-long or empty `mac_key` is accepted and used as an HMAC key. An
empty key is a valid HMAC key, so a blob with `mac_key = []` makes every header/ciphertext MAC
computable by anyone who knows the public labels. The invariant "both keys are 32 bytes" is
established by `new`/`update` but not re-established on load.

### SPQR-DESER-epoch-zero. `epoch == 0` is accepted by every `*::from_pb`; `msg.epoch − 1` underflows in `send` (LOW; blob)

**Theorems.** `Spqr/Specs/Lib/Send.lean`: `SendAssumptions` has to assume `0 <
ss.msg.epoch.val`. `Recv.lean` `recvV1ChainReady` assumes `1 ≤ mp.epoch.val`.
`Spqr/Specs/V1/**/Serialize/*/FromPb.lean` theorems accept any `epoch`.

**Rust.** `src/lib.rs:298` `chain.send_key(msg.epoch - 1)`.

**Why a defect.** A blob with a state at epoch 0 makes `send` compute `0 − 1` (debug panic;
release wraps to `u64::MAX`, then `EpochOutOfRange`). `msg_preamble` rejects epoch 0 on the
*wire* (`msg_preamble_spec`) but the *state* side has no such check.

### SPQR-DESER-epoch-max. `epoch < u64::MAX` is assumed, not checked, in the epoch-advancing transitions (LOW–MEDIUM; blob)

**Theorems.** `RecvNextEpoch.lean` (`recv_next_epoch_spec`) requires `h_next : next_epoch =
epoch + 1`; `RecvCt2.lean` (`recv_ct2_spec`) requires `h_epoch : self.epoch < U64.max`;
`Spqr/Specs/Braid/Scka/EpochUniqueness.lean` ("Hypotheses and trusted base"): "The results
therefore hold for the crate built with overflow checks, or for a release run in which no call
overflows." `States.Rejects` in `EpochDispatch.lean` explicitly includes "the check call
panicking (for example, the epoch increment in `recv_ct2` at `U64.max`)".

**Why a defect.** A blob with `epoch = u64::MAX` turns a completed `ct2` into a panic
(debug) or a wrap to epoch 0 (release), which breaks `epochs_strictly_increase` outside its
hypotheses and collides with the `ZERO_EPOCH` logic of SPQR-AUTH-index0-nokey.


### SPQR-DESER-poly-points. `PolyEncoder::from_pb` / `PolyDecoder::from_pb` do not bound point counts (MEDIUM; blob)

**Theorems.** `Spqr/Specs/Encoding/Polynomial/PolyEncoder/FromPb.lean`
(`from_pb_spec_postcond`, formerly `from_pb_spec`; `from_pb_spec` now states `result =
FunctionalModels.fromPb pb`) checks only `pts.len() == 16` and evenness, and
`PolyEncoder.FunctionalModels.WellFormed` bounds only `2 * len ≤ Usize.max` per point; the consumer `send_ct2_chunk_spec` then has to
assume `h_admissible : len ∈ {0,1,3,5,30,34,36}` for every slot. `PolyDecoder/FromPb.lean`
(`from_pb_spec`) checks `pts.len() == 16` and `% 4 == 0` only; consumers assume `h_push_cap :
(pts[k]).length + 17 ≤ Usize.max`, and `recvV1StatesOk` in `Recv.lean` has to assume the
`States.from_pb` no-panic obligations outright.

**Why a defect.** A blob with a point vector of unexpected length drives `next_chunk` into
`Poly::from_complete_points` (`polynomial.rs:297-330`), whose `match pts.len()` has a
`debug_assert!(false, "missing precomputed poly …")` fallback for every length outside
`{0,1,3,5,30,34,36}` — a panic in debug builds, and in release a slow generic Lagrange path
(`lagrange_interpolate_pt` per point) that the `hax_lib::assume!(res.is_ok())` at
`polynomial.rs:677` treats as unreachable; a decoder slot with hundreds of points is accepted
and causes quadratic work per `decoded_message` call.

### SPQR-DESER-is-complete. `PolyDecoder::is_complete` is never set; a blob can permanently disable a decoder (LOW; blob)

**Theorems.** `DecodedMessage.lean` (`decoded_message_spec`): result is `none` whenever
`self.is_complete = true`. `AddChunk.lean`: `add_chunk` preserves `is_complete`.
`PolyDecoder/FromPb.lean`: `decoder.is_complete = pb.is_complete`. No theorem (and no line of
`polynomial.rs`) sets it to `true`.

**Why a defect.** The field is write-never in the crate but blob-controlled on load. A state
blob with `is_complete = true` makes every later `decoded_message` return `none`, so the epoch
never completes — a stall that survives every subsequent legitimate chunk.

### SPQR-DESER-zero-poly-roundtrip. `Poly::serialize`/`deserialize` are not inverses on the zero polynomial (LOW; API, latent)

**Theorems.** `Spqr/Specs/Encoding/Polynomial/Poly/Serialize.lean` (`serialize_zero_eq_nil`)
and `Deserialize.lean` (`deserialize_empty_is_err`): `deserialize (serialize zero) = Err
SerializationInvalid`. `Poly/FunctionalModels.lean` makes the exclusion explicit: its round-trip
laws hold only under `WellFormed p := p.coefficients.val ≠ [] ∧ …`, so the zero polynomial is
outside the proved `serialize`/`deserialize` bijection.

**Rust.** `src/encoding/polynomial.rs:347` `if serialized.is_empty() || …`.

**Why a defect.** A `PolyEncoder` in the `Polys` phase whose polynomial is zero cannot be
restored from its own serialisation: `PolyEncoder::from_pb` fails with `StateDecode` on a
state that `into_pb` produced. The session is lost after a benign save/restore.

**Reachability (revision 4).** Re-reading `PolyEncoder::point_at` (`polynomial.rs:645-686`):
the `Polys` phase is built by `Poly::from_complete_points` over the point vector of each slot,
which is `vec![]` — the zero polynomial — exactly when a slot holds **zero** points
(`polynomial.rs:307`). `encode_bytes_base` (`polynomial.rs:700-707`) distributes `msg.len()/2`
elements round-robin over 16 slots, so a slot is empty only if the message has fewer than 32
bytes. All three V1 messages (`hdr‖mac` 96 B, `ek` 1152 B, `ct2‖mac` 160 B) are longer, so in
a normal V1 run every slot is non-empty and the zero polynomial is never serialised. The
finding is therefore an API/latent defect of `Poly::{serialize, deserialize}` and of
`PolyEncoder::from_pb` on blobs with an all-`polys` encoder containing an empty entry, not a
save/restore failure of a live V1 session. The severity is downgraded to **LOW** accordingly;
the CVSS entry (1.9, Low) already reflected this.

### SPQR-DESER-encaps2-endian. `encaps2` endianness heuristic can silently produce a wrong `ct2` (MEDIUM; blob)

**Theorems.** `Spqr/Specs/IncrementalMlkem768/Encaps2.lean` (`Encaps2Post`,
`encaps2EffectiveState`): the ciphertext is computed from the state **after** the opaque
`potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275`; the only axiom about it is
a length bound (`SrcTranslated/FunsExternal.lean:2688`).

**Rust.** `src/incremental_mlkem768.rs:71-110`: the swap is triggered by whether the `error2`
coefficients lie in `[-2, 2]`.

**Why a defect.** A corrupted `es` whose `error2` coefficients happen to pass (or fail) the
range check is byte-swapped (or not) and encapsulates to a shared secret that the peer cannot
decapsulate. The spec cannot say anything stronger because the function is opaque.

### SPQR-DESER-ct2sent-assert. Unchunked `Ct2Sent::recv_next_epoch` asserts rather than errors (LOW–MEDIUM; blob)

**Theorems.** `RecvNextEpoch.lean`: total only under `h_next : next_epoch = epoch + 1`. The
chunked caller `recv_Ct2Sampled_next_epoch` discharges it, but the unchunked function is `pub`
and `assert!`s otherwise.

**Why a defect.** A contract violation becomes a panic instead of `Err`; combined with SPQR-DESER-epoch-max, a
blob with `epoch = u64::MAX` is a crash.

### SPQR-DESER-send-assert. `lib::send` panics on `assert!(key.is_none())` on the no-chain path (LOW–MEDIUM; blob)

**Theorems.** `Send.lean` `SendAssumptions` (b): "The first `assert!` of `send` (no epoch
secret on the no-chain path)" must be *assumed*; the theorem cannot show it.

**Rust.** `src/lib.rs:291-292`.

**Why a defect.** A V1 state with `chain = None`, `version_negotiation.min_version = V0` and
an inner state that emits an epoch secret (`EkSentCt1Received` completing `ct2`) crashes
`send`. That combination is constructible from a blob.

### SPQR-DESER-authkey-length. `auth_key` of any length — including empty — is accepted as the root of both the chain and the authenticator (MEDIUM–HIGH; local-config, blob)

**Theorems.** `Spqr/Specs/Lib/InitialState.lean` (`initial_state_spec_v1`) and
`Spqr/Specs/Lib/InitInner.lean` (`init_inner_spec_v1_*`) require only `auth_key.length + 32 ≤
Usize.max` and copy the key verbatim into `vn.auth_key`
(`VersionNegotiationMatchesParams`). `Spqr/Specs/Chain/Chain/New.lean` (`new_spec`): the chain
root is `newHkdfOutput initial_key` for *any* `initial_key : Slice U8`.
`Spqr/Specs/Authenticator/Authenticator/New.lean` (`new_spec`): requires only `root_key.length +
32 ≤ Usize.max`, and the authenticator's first `update` folds `[0u8; 32] ‖ root_key` into
HKDF. `Spqr/Specs/Lib/ChainFromVersionNegotiation.lean` (`chain_from_version_negotiation_spec`)
rebuilds the chain from the *persisted* `vn.auth_key` with the same absence of checks. No
theorem anywhere states a lower bound or entropy requirement on the key.

**Rust.** `src/lib.rs:211-235` (`initial_state`), `lib.rs:332-340`, `src/chain.rs:333-354`,
`src/authenticator.rs:35-42`; `Error::InvalidParams` is never constructed (SPQR-ARITH-params-unchecked).

**Why a defect.** `auth_key` is the only secret input to the whole construction: epoch-0 send
and receive chains, `next_root`, the authenticator root and the first `mac_key` are all derived
from it. An empty or short key makes every epoch-0 message key and every header/ciphertext MAC
computable by anyone, and the ML-KEM-Braid security argument (which assumes a uniformly random
32-byte key) does not apply. The API neither documents nor enforces the requirement; the
error variant that exists for parameter validation is dead. Because `vn.auth_key` is persisted
and re-used by `chain_from_version_negotiation` on *every* `send`/`recv` until negotiation
ends, a blob with `auth_key = []` also retroactively replaces a good key: the epoch-0 chain is
re-derived from the empty key, and the resulting message keys are public. This is the
construction-side counterpart of SPQR-DESER-auth-keylen (which is about `Authenticator::from_pb`).

### SPQR-DESER-minversion-cast. `recv` truncates `vn.min_version` with `as u8` while `current_version` validates it with `try_from` (LOW–MEDIUM; blob)

**Theorems.** `Spqr/Specs/Lib/Recv.lean` `minVersionU8`: "`recv` does **not** validate
`vn.min_version` … the Rust code casts the `i32` with `as u8`, so `IScalar.hcast` — a
truncating cast — is the faithful model. E.g. `min_version = 256` gives `0` and `min_version =
-1` gives `255`." `Spqr/Specs/Lib/CurrentVersion.lean` (`current_version_spec`): the same field
through `Version::try_from` yields `Err StateDecode` for values other than `0`/`1`.
`Spqr/Specs/Lib/Send.lean` (`send_spec`) uses a third interpretation, the signed comparison
`vn.min_version > 0`.

**Rust.** `src/lib.rs:368` (`vn.min_version as u8`), `lib.rs:258` (`try_into`), `lib.rs:277`
(`> Version::V0 as i32`).

**Why a defect.** Three API entry points disagree about whether a blob is well-formed. With
`min_version = -1`: `current_version` says the state is corrupt; `send` treats it as
`min_version ≤ 0` (no chain, no keys — the SPQR-DESER-send-assert path); `recv` computes `min_version = 255` and
rejects **every** message with `MinimumVersion`, including the peer's genuine V1 messages.
With `min_version = 256`: `recv` accepts V0 downgrades (`min_version = 0`) that `send`'s check
(`256 > 0`) says are forbidden — a downgrade (SPQR-AUTH-v0-downgrade) enabled by a blob that `current_version`
would have rejected. An embedder that uses `current_version` to validate stored state before
calling `recv` gets no protection, because `recv` does not call it.


---

## Part IV — Cryptographic hygiene

### SPQR-CRYPT-compare-length. `compare` silently truncates / panics when slice lengths differ (MEDIUM; latent)

**Theorems.** `Spqr/Specs/Util/Compare.lean` (`compare_spec`) is stated only under `hlen :
lhs.length = rhs.length`. `VerifyHdr.lean`/`VerifyCt.lean` need `h_mac : expected_mac.length =
MACSIZE`.

**Rust.** `src/util.rs:25-33`: loops `for i in 0..lhs.len()` and reads `rhs[i]`.

**Why a defect.** If `lhs` is shorter, only a prefix of `rhs` is compared (a tag with fewer
bytes passes with proportionally less work for a forger); if `lhs` is longer, `rhs[i]` panics.
A constant-time equality primitive must either take fixed-size arrays or fold the length into
the result. The `#[hax_lib::requires(expected_mac.len() == MACSIZE)]` on `verify_*` is erased at
runtime, so the only thing keeping `expected_mac` at 32 bytes is the decoder's `pts_needed`
(`recv_hdr_chunk_spec`'s `h_decoded_len : msg.length = 96`), which is itself blob-controlled
(SPQR-DESER-poly-points).

### SPQR-CRYPT-ratchet-before-verify. `Authenticator::update` ratchets *before* `verify_ct`; authenticator errors are flattened (LOW; hygiene)

**Theorems.** `RecvCt2.lean` docstring step 3: "ratchets `auth.update(epoch, &secret)`
*before* checking the tag"; `recv_ct2_spec` returns `Err MacVerifyFailed` and the ratcheted
authenticator is dropped only because the function consumes `self` and the caller discards the
state on `Err`. `Spqr/Specs/Lib/Error/From.lean` (`from_spec`): every `authenticator::Error`
maps to `MacVerifyFailed`.

**Why a defect.** The ordering is fragile: any refactor that keeps `self` on `Err` (or the
replay path of SPQR-AUTH-ct1ack-accepted/SPQR-SPEC-rollback-scope) would persist a ratchet step driven by an unverified ciphertext.
Flattening `InvalidHdrMac`/`InvalidCtMac` to one variant is defensible against oracle leakage
but removes the information an embedder needs to distinguish a corrupted header stream from a
corrupted ciphertext stream.

### SPQR-CRYPT-no-zeroise. No zeroisation of secrets (LOW; hygiene)

**Theorems.** `Spqr/Specs/Chain/ChainEpochDirection/ClearNext.lean`: `clear_next` is
`Vec::clear` — "zeroing its length while preserving `ctr` and `prev`" — the bytes remain in
the allocation. `SendKey.lean` loop 1 clears `next` of older epochs this way.

**Why a defect.** Forward secrecy at the API level (`send_key` clears old chain secrets) is
not forward secrecy in memory: the old `next` keys stay in freed/unused heap until overwritten.
The ratchet's own security argument (ML-KEM Braid §3.8) assumes they are gone.

---

## Part V — Soundness of the trusted base and limits of the verified surface

### SPQR-SPEC-pk-hash-order. `validate_pk_bytes` model differs from the ML-KEM Braid check (LOW; spec)

**Theorems.** `EpochDispatch.lean`, `States.CheckPasses` docstring: the libcrux model in
`SrcTranslated/FunsExternal.lean:2024-2055` "hashes `ek_vector || ek_seed`, the order of FIPS
203, and it also checks the input lengths and that `ek_vector` is a canonical encoding",
whereas §2.5 (pp. 19, 22) checks `SHA3-256(ek_seed || ek_vector) = hek`.
`Spqr/Specs/Braid/StateMachine/Refinement.lean` (module doc, `CodePrims.ekMatches`) restates it:
the abstract machine "uses the code's `ek` check … not the check `SHA3-256(ek_seed ||
ek_vector) = hek` of §2.5". The same docstring records two further code/§2.2 mismatches that
the refinement inherits: `KDF_AUTH` (salt `[0u8; 32]`, key `root_key ‖ update_key`) and
`PROTOCOL_INFO` (`Signal_PQCKA_V1_MLKEM768`, no MAC component) are the code's choices, not
§2.2's, and `CodePrims.keyGen`/`encaps1` "do not satisfy a KEM correctness law".

**Why a defect.** The theorems compare the code against the *model's* check, not the spec's;
"That the code's decoder and checks compute the spec's decoder and checks is not proved."
Either the written spec or the implementation uses the wrong concatenation order, and the Lean
development cannot tell which.

### SPQR-SPEC-future-epoch-err. `future-epoch-error`: messages from a later epoch are errors, not drops (LOW; message)

**Theorems.** `EpochDispatch.lean` `recv_of_gt`: every state returns
`Err(EpochOutOfRange msg.epoch)` for `msg.epoch > e` (except SPQR-AUTH-epoch-advance's case). §2.5 ignores such
messages.

**Why a defect.** An attacker can make every `recv` call fail by sending a message with a
large epoch; the error propagates to the host (`lib.rs:460`) without a new state. An embedder
that treats `Err` as "session broken" is DoS-able with one unauthenticated message per call.

### SPQR-SPEC-rollback-scope. Epoch-uniqueness results exclude rollback and serialized-state replay (LOW; spec scope)

**Theorems.** `Spqr/Specs/Braid/Scka/EpochUniqueness.lean` "Scope": the results do not cover
"states serialized and restored between calls" or "a party rolled back to an older stored
state". `Deviations.lean`, `Braid.Deviation.ct1AckAccepted` example (b): because `spqr::send`/`recv` take
the serialized state **by reference** (`lib.rs:264, 355`), a caller can call `recv` again with
an earlier state; `encaps2` and `mac_ct` are deterministic so "the new `ct2` encoder equals the
first one".

**Why a defect.** `epochs_nodup` ("each party outputs at most one key per epoch") is the
central SCKA safety property, yet the API makes the excluded scenario trivial: the same
`EpochSecret` can be emitted twice from two `recv` calls on the same stored bytes, and the
chain then derives identical message keys twice. The property holds for a *threaded* run only.

### SPQR-SPEC-liveness. Emitting transitions are only conditionally total; liveness is unproved (INFO; spec scope)

**Theorems.** `EpochUniqueness.lean`: "none of them shows that a call emitting a key can
succeed … a machine whose emitting calls always fail satisfies every result here." `Recv.lean`
`recvV1StatesOk` and `Send.lean` `SendAssumptions` (a) assume no-panic of `States::from_pb`,
`States::send`, `States::into_pb`. `Spqr/Specs/Braid/StateMachine/Refinement.lean`
(`run_refines`): "The results cover successful code steps only. They say nothing about calls
that the code rejects, about progress, or about agreement between the two parties."

**Why it matters.** The verified surface establishes safety (no duplicate epochs, exact result
shapes) but not that a legitimate session makes progress. Combined with the `SPQR-AUTH-*` control-plane items and SPQR-SPEC-future-epoch-err, the gap
is precisely where an attacker operates: forcing the "always fail" machine.


---

## Summary table

| ID | Severity | Reach | Theorem(s) that expose it | Rust location |
|---|---|---|---|---|
| SPQR-AUTH-epoch-advance | MEDIUM | message | `recv_Ct2Sampled_next_epoch` | `v1/chunked/states.rs:514-526` |
| SPQR-AUTH-ct1ack-accepted | MEDIUM | message | `recv_of_eq_refines` (`ct1ack-accepted`) | `v1/chunked/states.rs:465-474` |
| SPQR-AUTH-late-ek-chunk | LOW–MED | message | `recv_of_eq_refines` (`late-ek-chunk`) | `v1/chunked/states.rs:486-507` |
| SPQR-AUTH-chunk-poison | MEDIUM | message | `add_chunk_spec`, `decoded_message_spec` | `encoding/polynomial.rs:905-913` |
| SPQR-AUTH-v0-downgrade | LOW–MED | message | `msg_preamble_spec`, `recv_spec_less_v0` | `lib.rs:564-571, 422-445` |
| SPQR-AUTH-index0-nokey | LOW–MED | message | `recv_key_spec`, `recvGreaterPost` | `chain.rs:417-419`, `lib.rs:401-406` |
| SPQR-AUTH-index-cpu-amp | LOW–MED | message | `key_spec`, `MaxJumpOrDefault` | `lib.rs:435`, `chain.rs:248-297` |
| SPQR-AUTH-wire-noninjective | LOW | message | `serialize_parse_not_injective`, `recv_on_witnesses_eq` | `lib.rs:524-554`, `serialize.rs:128,208` |
| SPQR-ARITH-ooo-u32-overflow | MEDIUM | message+config | `get_spec` (`h_ooo_no_overflow`) | `chain.rs:192` |
| SPQR-ARITH-params-unchecked | MEDIUM | local-config | `h_maxooo_bound` everywhere | `chain.rs:84-86`, `lib.rs:127` |
| SPQR-ARITH-trimsize-usize32 | LOW | 32-bit | `gc_spec_core` (`h_fit`), `*_32` files | `chain.rs:84-86` |
| SPQR-ARITH-keyhistory-invariant | MEDIUM | spec | `key_spec` (`h_prev_ctr`), `add_spec` | `chain.rs:138,174` |
| SPQR-ARITH-epochidx-trunc32 | MEDIUM | 32-bit | `epoch_idx_spec` (`h_diff_fits`) | `chain.rs:382` |
| SPQR-ARITH-encoder-idx-u16 | LOW | blob | `send_ct2_chunk_spec` (`h_idx_fits`) | `encoding/polynomial.rs:759` |
| SPQR-DESER-chain-frompb | HIGH | blob | `ChainEpochDirection.from_pb_spec`, `Chain.from_pb_spec` | `chain.rs:306-312, 445-460` |
| SPQR-DESER-auth-keylen | LOW | blob | `Authenticator.from_pb_spec`, `update_spec` | `authenticator/serialize.rs:16` |
| SPQR-DESER-epoch-zero | LOW | blob | `SendAssumptions`, `recvV1ChainReady` | `lib.rs:298` |
| SPQR-DESER-epoch-max | LOW–MED | blob | `recv_next_epoch_spec`, `recv_ct2_spec` | `v1/unchunked/send_ct.rs:201-208` |
| SPQR-DESER-poly-points | MEDIUM | blob | `PolyEncoder.from_pb_spec`, `PolyDecoder.from_pb_spec` | `encoding/polynomial.rs:596-640, 840-870` |
| SPQR-DESER-is-complete | LOW | blob | `decoded_message_spec`, `add_chunk_spec` | `encoding/polynomial.rs:784, 924` |
| SPQR-DESER-zero-poly-roundtrip | LOW | API, latent | `serialize_zero_eq_nil`, `deserialize_empty_is_err` | `encoding/polynomial.rs:347, 307` |
| SPQR-DESER-encaps2-endian | MEDIUM | blob | `Encaps2Post`, axiom at `FunsExternal.lean:2688` | `incremental_mlkem768.rs:71-110` |
| SPQR-DESER-ct2sent-assert | LOW–MED | blob | `recv_next_epoch_spec` | `v1/unchunked/send_ct.rs:201-208` |
| SPQR-DESER-send-assert | LOW–MED | blob | `SendAssumptions` (b) | `lib.rs:291-292` |
| SPQR-CRYPT-compare-length | MEDIUM | latent | `compare_spec` (`hlen`) | `util.rs:25-33` |
| SPQR-CRYPT-ratchet-before-verify | LOW | hygiene | `recv_ct2_spec`, `Error.from_spec` | `v1/unchunked/send_ek.rs:139-172` |
| SPQR-CRYPT-no-zeroise | LOW | hygiene | `clear_next_spec` | `chain.rs:318-320` |
| SPQR-SPEC-pk-hash-order | LOW | spec | `States.CheckPasses` docstring, `Refinement.lean` module doc | `FunsExternal.lean:2024-2055` |
| SPQR-SPEC-future-epoch-err | LOW | message | `recv_of_gt` | `v1/chunked/states.rs:283-285` |
| SPQR-SPEC-rollback-scope | LOW | spec scope | `EpochUniqueness` "Scope" | `lib.rs:264, 355` |
| SPQR-SPEC-liveness | INFO | spec scope | `EpochUniqueness` "Hypotheses", `Refinement.lean` `run_refines` | — |
| SPQR-AUTH-a-encoder-drop | HIGH | message | `KeysSampled.recv_ct1_chunk_spec`, `Ct1Received.recv_ct2_chunk_spec` | `v1/chunked/send_ek.rs:85-98, 164-180` |
| SPQR-AUTH-b-encoder-drop | HIGH | message | `recv_ek_chunk_spec_still_receiving` | `v1/chunked/send_ct.rs:191-192` |
| SPQR-AUTH-v1-lockin | MEDIUM | message | `recvV1Post`, `minVersionU8_none_v1` | `lib.rs:470-476` |
| SPQR-DESER-authkey-length | MED–HIGH | local-config, blob | `Chain.new_spec`, `Authenticator.new_spec`, `initial_state_spec_v1` | `lib.rs:211-235`, `chain.rs:333-354`, `authenticator.rs:35-42` |
| SPQR-AUTH-chain-advance-persist | HIGH | message | `recvV1Post`, `recvGreaterPost`, `cedKeyAdvancePost`, `cedKeyLessPost` | `lib.rs:462-476, 401-419`, `chain.rs:248-297` |
| SPQR-DESER-minversion-cast | LOW–MED | blob | `minVersionU8`, `current_version_spec`, `send_spec` | `lib.rs:368, 258, 277` |

## Progression chains

[`defect-chains.dot`](./defect-chains.dot) draws the dependencies between findings (which
defect enables which, and the outcome each chain ends in) as a Graphviz graph; render with
`dot -Tsvg doc/defect-chains.dot -o defect-chains.svg`. Every edge is a relation stated in a
"Why a defect" paragraph above. The ASCII summary:

```
 ROOT: no MAC before States::recv / recv_key (lib.rs:460-467)
   ├─ epoch-advance 7.5 ─────────────┐
   ├─ a-encoder-drop 7.5 ──┐         ├─▶ protocol deadlock
   ├─ b-encoder-drop 7.5 ──┼─────────┘
   │                       └╌▶ chunk-poison 7.5 ◀── late-ek-chunk 5.9 ─▶ epoch never completes
   ├─ chain-advance-persist 8.2 ──▶ legitimate keys KeyTrimmed / KeyAlreadyRequested
   └─ index-cpu-amp 5.3 ──────────▶ repeatable CPU DoS (not mitigated by libsignal MAC order)

 minversion-cast 5.1 ──(256→0)──▶ v0-downgrade 4.8 ──▶ PQ disabled   ‖ dual: v1-lockin 5.9 ──▶ V0 peer locked out
                     ──(-1→255)─▶ every message MinimumVersion

 params-unchecked 4.4 ─┬─▶ authkey-length 6.0 ─┬─▶ CHAINED 9.1: epoch-0 keys + MAC forgery
                       │   auth-keylen 4.4 ────┘
                       ├─▶ ooo-u32-overflow 4.8 ─▶ valid key reported KeyTrimmed
                       └─▶ trimsize-usize32 4.1
 chain-frompb 4.4 / epoch-zero 4.4 / send-assert 4.1 / epoch-max 4.7 ─▶ ct2sent-assert 4.1 ─▶ panic from accepted blob
 epoch-max ╌╌▶ index0-nokey 5.3 (wrap to ZERO_EPOCH)

 poly-points 5.1 ─┬─▶ from_complete_points debug_assert / quadratic decode
                  └╌▶ compare-length (5.9 potential) ─▶ prefix-only MAC compare
 is-complete 4.4 / encoder-idx-u16 1.9 ─▶ decoder never completes
 zero-poly-roundtrip 1.9 ─▶ StateDecode on crafted blob

 rollback-scope ─┬─▶ ct1ack-accepted 5.9 ╌▶ (deadlock, not analysed)
                 ├─▶ ratchet-before-verify
                 └─▶ same EpochSecret twice
 future-epoch-err 5.3 ─▶ liveness unproved ╌▶ back to ROOT (proofs stop where the attacker operates)
```

## Priorities

| Priority | Items | Fix sketch |
|---|---|---|
| 1 | SPQR-DESER-chain-frompb, SPQR-ARITH-ooo-u32-overflow, SPQR-CRYPT-compare-length, SPQR-AUTH-chain-advance-persist | Validate every `from_pb` field (lengths, alignment, `ctr`, `epoch`, `params` ranges); use checked/saturating arithmetic in `KeyHistory::get`; give `compare` fixed-size inputs or fold the length into the result. For SPQR-AUTH-chain-advance-persist: do not persist a receive-chain advance until the message is authenticated — either take the host's MAC verdict as an input to `recv`, or return the chain delta separately so the embedder can commit it after verification, and document that `Recv.state` must be discarded on outer-MAC failure. |
| 2 | SPQR-AUTH-epoch-advance, SPQR-AUTH-ct1ack-accepted, SPQR-AUTH-chunk-poison, SPQR-AUTH-v0-downgrade, SPQR-AUTH-index0-nokey, SPQR-AUTH-a-encoder-drop, SPQR-AUTH-b-encoder-drop, SPQR-AUTH-v1-lockin | Require a MAC (or the host's MAC verdict) before any state transition that drops an encoder, downgrades, decides key presence, or closes version negotiation; never replace an existing decoder point; bound retries. For SPQR-AUTH-a-encoder-drop/SPQR-AUTH-b-encoder-drop specifically: keep the previous-flow encoder alive (or re-derivable from `uc`) until the *authenticated* completion of the next flow, rather than dropping it on the first unauthenticated chunk. |
| 3 | SPQR-ARITH-params-unchecked, SPQR-ARITH-epochidx-trunc32, SPQR-DESER-epoch-zero, SPQR-DESER-epoch-max, SPQR-DESER-ct2sent-assert, SPQR-DESER-send-assert, SPQR-DESER-authkey-length, SPQR-DESER-minversion-cast | Turn every `hax_lib::assume!`/`requires` in `chain.rs`, `send_ct.rs`, `lib.rs` into a runtime `Err`; construct `InvalidParams` — including for `auth_key.len() < 32` in `initial_state` and `chain_from_version_negotiation`; route `vn.min_version` through `Version::try_from` in `recv` and `send` as `current_version` already does. |
| 4 | SPQR-AUTH-wire-noninjective, SPQR-DESER-poly-points, SPQR-DESER-is-complete, SPQR-DESER-zero-poly-roundtrip, SPQR-ARITH-encoder-idx-u16 | Reject non-minimal varints and trailing bytes; validate point counts; remove or set `is_complete`; special-case the zero polynomial; cap `idx` explicitly. |
| 5 | SPQR-AUTH-index-cpu-amp, SPQR-DESER-encaps2-endian, SPQR-CRYPT-ratchet-before-verify, SPQR-CRYPT-no-zeroise, SPQR-SPEC-pk-hash-order, SPQR-SPEC-future-epoch-err, SPQR-SPEC-rollback-scope, SPQR-SPEC-liveness | Bound pre-auth work by `max_ooo`; replace the endianness heuristic; zeroise; align model and §2.5 on hash input order; extend Braid results to serialized runs. |

## Method

All spec files under `Spqr/Specs/` were surveyed for hypotheses of the form `h_* :` and for
postconditions describing `Err`/panic arms; each was traced to the Rust source in `src/` and,
where relevant, to the externals in `SrcTranslated/FunsExternal.lean`. Theorems named here were
checked to exist with the stated hypotheses, e.g. `compare_spec`
(`Spqr/Specs/Util/Compare.lean:69`), `get_spec` (`Spqr/Specs/Chain/KeyHistory/Get.lean:348`),
`key_spec` (`Spqr/Specs/Chain/ChainEpochDirection/Key.lean:661`),
`recv_Ct2Sampled_next_epoch` (`Spqr/Specs/Braid/StateMachine/EpochDispatch.lean:151`),
`serialize_parse_not_injective` / `recv_on_witnesses_eq`
(`Spqr/Specs/V1/Chunked/States/Serialize/Message/NotInjective.lean`), `recv_key_spec`
(`Spqr/Specs/Chain/Chain/RecvKey.lean:55`), `send_ct2_chunk_spec`
(`Spqr/Specs/V1/Chunked/SendCt/Ct2Sampled/SendCt2Chunk.lean:54`). The report is a reading of
what the proved statements and their explicit scope notes imply; it adds no new proofs.

The six second-pass findings (SPQR-AUTH-a-encoder-drop, SPQR-AUTH-b-encoder-drop,
SPQR-AUTH-v1-lockin, SPQR-AUTH-chain-advance-persist, SPQR-DESER-authkey-length,
SPQR-DESER-minversion-cast) were found by looking specifically for (i) postconditions in which a
field of the input state is *absent* from the output (`sending_hdr`, `sending_ek`,
`sending_ct1`, `version_negotiation`), i.e. state that is irrevocably discarded by a transition
whose trigger is unauthenticated; (ii) persisted outputs that depend on an attacker-controlled
message field (`recvV1Post`/`recvGreaterPost` re-encode the advanced chain); (iii) constructor
specs whose only hypothesis is an overflow bound (`Chain.new_spec`, `Authenticator.new_spec`,
`initial_state_spec_v1`); and (iv) the same protobuf field modelled differently in different
entry points (`minVersionU8` vs `current_version_spec` vs `send_spec`). Theorems cited were
checked to exist with the stated shape, e.g. `recv_ct1_chunk_spec`
(`Spqr/Specs/V1/Chunked/SendEk/KeysSampled/RecvCt1Chunk.lean:137`), `recv_ct2_chunk_spec`
(`Spqr/Specs/V1/Chunked/SendEk/Ct1Received/RecvCt2Chunk.lean:161`),
`recv_ek_chunk_spec_still_receiving`
(`Spqr/Specs/V1/Chunked/SendCt/Ct1Sampled/RecvEkChunk.lean:341`), `recvV1Post`
(`Spqr/Specs/Lib/Recv.lean:767`), `recvGreaterPost` (`Recv.lean:143`), `minVersionU8`
(`Recv.lean:124`), `cedKeyAdvancePost` (`Spqr/Specs/Chain/Chain/Defs.lean:240`), `cedKeyPost`
(`Defs.lean:278`), `Chain.new_spec` (`Spqr/Specs/Chain/Chain/New.lean:34`),
`Authenticator.new_spec` (`Spqr/Specs/Authenticator/Authenticator/New.lean:35`).

Revision 4 (re-check after the upstream merge at `17b3b5d3`): `src/` is unchanged since
revision 3, so every finding and Rust line reference stands. On the Lean side the §2.5
deviation docstrings moved from `EpochDispatch.lean` to `Spqr/Specs/Braid/Deviations.lean`
(`Braid.Deviation.{futureEpochError, ct1AckAccepted, lateEkChunk}`), `Model.lean` and
`Refinement.lean` were added (the abstract machine follows the code at all three deviations),
`PolyEncoder/FromPb.lean`'s `from_pb_spec` was renamed `from_pb_spec_postcond`, and
`Ct1Acknowledged/RecvEkChunk.lean` dropped `recv_ek_chunk_spec_done` because `IsSortedPushResult`
allows a *replace* step (further confirmation of SPQR-AUTH-chunk-poison). References above were
updated accordingly. Every finding was then re-validated against the Rust source directly
(not only via the Lean hypotheses), including the `sorted-vec 0.8.6` `SortedSet::push`
(replace-on-equal `x`, confirming SPQR-AUTH-chunk-poison) and libcrux-ml-kem 0.0.7
`validate_pk_parts` (hashes `pk2 ‖ pk1_seed`, i.e. `ek_vector ‖ ek_seed`, confirming the
model of SPQR-SPEC-pk-hash-order is faithful to the *implementation*). Outcome: 36 findings
confirmed as stated; SPQR-DESER-zero-poly-roundtrip downgraded MEDIUM → LOW (not reachable
in a V1 run, see its "Reachability" note); the panic site cited by SPQR-DESER-poly-points
corrected to `from_complete_points`'s `debug_assert!` fallback; and SPQR-ARITH-params-unchecked
clarified as to which arithmetic the `390451572` bound actually protects.
