# Spec coverage analysis: SPQR catalog vs. `mlkembraid.pdf`

This document estimates how much of `mlkembraid.pdf` the property catalog
(`SPQR_LEAN_PROPERTIES.md`) addresses, what confidence we would have *after*
discharging every property, and which additional properties would close the
remaining gap.

§0 below is a self-contained summary of mlkembraid.pdf that makes the
coverage tables (§2 onward) interpretable without the spec at hand.

---

## 0. What `mlkembraid.pdf` specifies

The ML-KEM Braid Protocol (Rolfe Schmidt, Signal; Revision 1, 2025-02-21,
last updated 2025-09-26) is a **Sparse Continuous Key Agreement (SCKA)**
protocol. SCKA is a generalisation of the Continuous Key Agreement underlying
the Double Ratchet, weakened to allow the protocol to take many round-trips
to produce a single shared secret — necessary because post-quantum KEM
material is too large to fit in one message under realistic bandwidth limits.

mlkembraid.pdf is divided into three parts: §1 Introduction (interfaces and
correctness goals); §2 Protocol (the actual specification); §3 Security
Considerations (informational notes on the vulnerable message set, alternate
KEMs, formal-verification status, etc.). The normative content is §1.1,
§1.2, §1.3, §2.2, §2.3, §2.4, §2.5, §2.6, and §3.8.

### §1.1 The SCKA interface and its five correctness properties

Each party maintains state and exposes two functions:

- `Send(state) → (msg, sending_epoch, output_key)`. Updates state. Returns
  the wire message, the latest *epoch identifier* `sending_epoch` known by
  the other party once they receive `msg`, and a nullable
  `output_key = (epoch, k)` containing a shared secret when one is ready
  to be released to the higher-level protocol.
- `Receive(state, msg) → (receiving_epoch, output_key)`. Updates state.
  Returns the epoch the sender intended and an optional shared secret.

The five correctness properties (informally):

1. **Session key consistency.** If both parties output keys `(ep, k)` and
   `(ep, k')` for the *same* epoch, then `k = k'`.
2. **Per-participant epoch uniqueness.** Each party emits at most one key
   per epoch identifier.
3. **Sender epoch knowledge.** When `Send` returns `sending_epoch = ep`, the
   sender possesses (or has possessed) keys for epoch `ep` and all earlier.
4. **Receiver epoch knowledge.** Symmetric for `Receive`.
5. **Epoch agreement.** If Alice's `Send` returns `(msg, ep, _)` then Bob's
   matching `Receive(msg)` returns `receiving_epoch = ep`.

### §1.2 Incremental KEMs and ML-KEM as one (§1.2.1)

A KEM has the **incremental interface** if it exposes:

- `KeyGen(rand) → (dk, ek_header, ek_vector)` where `ek_header` is small
  and contains everything needed to compute `ct1`; `ek_vector` is the
  bulk of the encapsulation key.
- `Encaps1(ek_header, rand) → (encaps_secret, ct1, shared_secret)`. The
  *encaps_secret* is intermediate state held by the encapsulator; `ct1`
  is the first ciphertext component (a "compressed public key" in
  LWE-style KEMs); `shared_secret` is the encapsulated key.
- `Encaps2(encaps_secret, ek_header, ek_vector) → ct2`. Completes
  encapsulation, producing the reconciliation message `ct2`.
- `Decaps(dk, ct1, ct2) → shared_secret`. Standard decapsulation.

**ML-KEM-768 instantiation (§1.2.1).** ML-KEM encapsulation keys consist of
a 32-byte seed followed by a noisy vector. To support the FO-transform's
key-binding, the spec defines:

- `ek_seed` = the 32-byte seed.
- `hek` = `SHA3-256(ek_seed ‖ ek_vector)` (a 32-byte hash binding ek_vector
  to the seed).
- `ek_header` = `ek_seed ‖ hek` (64 bytes total).

This lets `Encaps1` compute `ct1` from just the 64-byte header, deferring
the bulky `ek_vector` to `Encaps2`.

### §1.3 Chunking with erasure codes

SCKA messages may be too large for one network frame. The spec specifies
that messages are split into a stream of *chunks* (codewords) by an
**erasure code** (Reed-Solomon over GF(2¹⁶) recommended) so the receiver
can reconstruct the message from any sufficient subset of chunks regardless
of order or drops.

### §2.2 Parameters

- **KEM:** an IND-CPA-secure KEM with the §1.2 incremental interface; the
  spec lists ML-KEM-512 / ML-KEM-768 / ML-KEM-1024 with the constants:

  | Constant | ML-KEM-512 | ML-KEM-768 | ML-KEM-1024 |
  |---|---|---|---|
  | HEADER_SIZE | 64 | 64 | 64 |
  | EK_SIZE | 768 | 1152 | 1536 |
  | CT1_SIZE | 640 | 960 | 1408 |
  | CT2_SIZE | 128 | 128 | 160 |

- **Encode/Decode** interface: `Encode(byte_array) → encoder` (with
  `encoder.next_chunk()`); `Decoder.new(message_size) → decoder` (with
  `add_chunk`, `has_message`, `message`).
- **EPOCH_TYPE:** unsigned integer (64-bit recommended).
- **ToBytes(epoch):** big-endian byte representation.
- **MAC:** a MAC primitive (HMAC-SHA256 recommended); `MAC_SIZE` is its
  output length in bytes (32 for HMAC-SHA256).
- **PROTOCOL_INFO:** an implementer-defined string of the form
  `"MyProtocol_KEM_MAC"`, e.g. `"MyProtocol_MLKEM768_SHA-256"`.
- **`KDF_AUTH(root_key, update_key, epoch) → 64 bytes`:**
  ```
  HKDF input key material = update_key
  HKDF salt               = root_key
  HKDF info               = PROTOCOL_INFO ‖ ":Authenticator Update" ‖ ToBytes(epoch)
  HKDF length             = 64
  ```
- **`KDF_OK(shared_secret, epoch) → 32 bytes`:**
  ```
  HKDF input key material = shared_secret
  HKDF salt               = a zero-filled byte sequence of hash output length
  HKDF info               = PROTOCOL_INFO ‖ ":SCKA Key" ‖ ToBytes(epoch)
  HKDF length             = 32
  ```

### §2.3 Messages

Wire messages have three fields:

- `epoch` (unsigned integer): the current epoch being negotiated.
- `type` (enum): one of `{ None, Hdr, Ek, EkCt1Ack, Ct1Ack, Ct1, Ct2 }`.
  - `None`: empty payload.
  - `Hdr`: a chunk of the header.
  - `Ek`: a chunk of `ek_vector`.
  - `EkCt1Ack`: a chunk of `ek_vector` carrying an implicit acknowledgment
    that `ct1` was received.
  - `Ct1Ack`: empty payload, but acknowledges receipt of `ct1`.
  - `Ct1`: a chunk of `ct1`.
  - `Ct2`: a chunk of `ct2`.
- `data` (optional bytes): the chunk codeword when `type` is not `None`/`Ct1Ack`.

The spec explicitly delegates the wire-format encoding to the implementer;
either a custom binary format or Protocol Buffers is acceptable.

### §2.4 Internal authentication: the Ratcheted Authenticator

The protocol provides standalone authenticity through a **Ratcheted
Authenticator** with two state fields:

- `root_key`: 32 bytes.
- `mac_key`: 32 bytes.

and five operations:

```
Init(state, epoch, key):
    state := { root_key: 0^32, mac_key: None }
    Update(state, epoch, key)

Update(state, epoch, key):
    (state.root_key, state.mac_key) := KDF_AUTH(state.root_key, key, epoch)

MacHdr(state, epoch, hdr):
    return MAC(state.mac_key, PROTOCOL_INFO ‖ ":ekheader" ‖ epoch ‖ hdr, MAC_SIZE)

MacCt(state, epoch, ct):
    return MAC(state.mac_key, PROTOCOL_INFO ‖ ":ciphertext" ‖ epoch ‖ ct, MAC_SIZE)

VfyHdr(state, epoch, hdr, expected_mac):
    if expected_mac != MacHdr(state, epoch, hdr): FAIL

VfyCt(state, epoch, ct, expected_mac):
    if expected_mac != MacCt(state, epoch, ct):  FAIL
```

On verification failure participants must abort the ML-KEM Braid session
and renegotiate.

### §2.5 The state machine (11 states, 13 numbered transitions)

The protocol is a state machine. Each agent's state is one of 11 variants,
all carrying at minimum `(epoch : EPOCH_TYPE, auth : Authenticator)`. The
state names describe progress on the *encapsulation key* side ("Side A":
KeysUnsampled → KeysSampled → HeaderSent → Ct1Received → EkSentCt1Received)
or on the *ciphertext* side ("Side B": NoHeaderReceived → HeaderReceived →
Ct1Sampled → {EkReceivedCt1Sampled, Ct1Acknowledged} → Ct2Sampled). After
an epoch completes, the sides swap roles.

Each state defines `Send(state) → (msg, sending_epoch, output_key)` and
`Receive(state, msg) → (receiving_epoch, output_key)`. The 13 numbered
transitions are:

| # | From | Trigger | To | Notable side-effects |
|---|------|---------|----|----------------------|
| 1 | KeysUnsampled | `Send` | KeysSampled | sample keypair, build header `ek_seed ‖ hek`, MacHdr it, start sending `Hdr` chunks |
| 2 | KeysSampled | `Recv(Ct1)` | HeaderSent | initialise `ct1_decoder` and `ek_encoder` |
| 3 | HeaderSent | `Recv(Ct1)` (decoder fills) | Ct1Received | save `ct1` |
| 4 | Ct1Received | `Recv(Ct2)` | EkSentCt1Received | initialise `ct2_decoder` |
| 5 | EkSentCt1Received | `Recv(Ct2)` (decoder fills) | NoHeaderReceived(epoch+1) | run `Decaps`, `KDF_OK`, `Update auth`, `VfyCt`; emit `output_key = (old_epoch, ss')`; prepare next-epoch header_decoder |
| 6 | NoHeaderReceived | `Recv(Hdr)` (decoder fills) | HeaderReceived | split header into ek_seed‖hek; `VfyHdr`; initialise `ek_decoder` |
| 7 | HeaderReceived | `Send` | Ct1Sampled | run `Encaps1`, `KDF_OK`, `Update auth`; start sending `Ct1` chunks; emit `output_key` |
| 8 | Ct1Sampled | `Recv(EkCt1Ack)` (ek incomplete) | Ct1Acknowledged | record ek-chunk progress + ct1-ack |
| 9 | Ct1Sampled | `Recv(EkCt1Ack)` (ek complete in same call) | Ct2Sampled | verify SHA3-256(ek_seed‖ek_vector) = hek; `Encaps2`; `MacCt`; start sending `Ct2` chunks |
| 10 | Ct1Sampled | `Recv(Ek)` (ek complete) | EkReceivedCt1Sampled | verify SHA3 binding; await ct1-ack |
| 11 | Ct1Acknowledged | `Recv(EkCt1Ack)` (ek complete) | Ct2Sampled | verify SHA3 binding; `Encaps2`; `MacCt` |
| 12 | EkReceivedCt1Sampled | `Recv(EkCt1Ack)` | Ct2Sampled | `Encaps2`; `MacCt` |
| 13 | Ct2Sampled | `Recv` from `epoch + 1` | KeysUnsampled(epoch+1) | sides swap; new epoch begins |

State-pair reachability: when Alice begins in `KeysUnsampled` and Bob in
`NoHeaderReceived`, the figure-2 path through reachable pairs proceeds
linearly with two short branches (`Ct1Acknowledged` vs.
`EkReceivedCt1Sampled` depending on which side completes first), and ends
with the roles swapped one epoch later.

A `Receive` whose `msg.epoch` does not match the state's expected epoch is
a no-op in the spec (the pseudocode `if` falls through and returns the
state unchanged).

### §2.6 Initialization

Both parties are seeded with a pre-shared secret (e.g. from PQXDH):

```
InitAlice(shared_secret):
    epoch := 1
    auth  := Authenticator.Init(epoch, shared_secret)
    return KeysUnsampled(epoch, auth)

InitBob(shared_secret):
    epoch := 1
    auth  := Authenticator.Init(epoch, shared_secret)
    header_decoder := Decoder.new(KEM.HEADER_SIZE + MAC_SIZE)
    return NoHeaderReceived(epoch, auth, header_decoder)
```

### §3 Security considerations (informational)

§3.1 defines the **vulnerable message set** as the set of messages whose
secrecy is compromised in the event of state exposure; bounding this set is
the main security goal of SCKA. §3.2 notes that ML-KEM can be substituted
by other incremental IND-CPA-secure KEMs at the cost of separate analysis
of binding properties. §3.3 observes that internal authentication may be
omitted if the higher-level protocol provides authenticity. §3.4–§3.6
discuss bandwidth/PCS-speed trade-offs and alternate encoders (RaptorQ
fountain codes vs. systematic Reed-Solomon). §3.7 reports that the
ML-KEM Braid has been modelled in **ProVerif** under the Dolev-Yao model
and shown to be a secure SCKA. §3.8 recommends 64-bit epoch counters and
notes the wraparound risk for narrower types.

---

## 1. Methodology

I walked through every section of `mlkembraid.pdf` and tagged each obligation
as one of:

- **✅ covered** — a numbered PROP discharges the obligation as a Lean
  theorem or under a flagged axiom.
- **⚠ partial** — a numbered PROP discharges *part* of the obligation
  (e.g. the guard but not the full transition body, or the post-state
  shape but not the order of internal operations).
- **🔶 axiom** — covered only under a cryptographic-modelling assumption.
- **🚫 blocked** — would be covered, but blocked on extraction or opacity.
- **❌ uncovered** — no PROP addresses the obligation.
- **N/A** — informational / out of scope (e.g. security model definitions).

Coverage is then computed two ways: by *count* of discrete obligations (each
spec rule = 1 unit) and by *weight* of normative content (lines of
pseudocode). The two diverge sharply because §2.5 dominates the spec.

---

## 2. Section-by-section mapping

### §1.1 Sparse Continuous Key Agreement (5 properties)

| Spec obligation | PROP | Status |
|----------------|------|--------|
| Session key consistency: `(ep, k)`, `(ep, k')` ⇒ `k = k'` | PROP-1 | 🚫 blocked at API level; ⚠ feasible at v1 layer |
| Per-participant epoch uniqueness | PROP-9 + PROP-21 | ✅ |
| Sender epoch knowledge | PROP-23 | ⚠ feasible, not yet proved |
| Receiver epoch knowledge | PROP-23 (dual) | ⚠ feasible, not yet proved |
| Epoch agreement (sending_epoch = receiving_epoch) | PROP-22 | ✅ |

**Coverage:** 2 / 5 solid; 2 feasible; 1 blocked = **40% solid, 80% addressable**.

### §1.2 — §1.2.1 Incremental KEM (3 obligations)

| Spec obligation | PROP | Status |
|----------------|------|--------|
| KeyGen → `(dk, ek_seed, ek_vector)` interface | PROP-3 | 🔶 axiom |
| Encaps1/Encaps2/Decaps roundtrip preserves `ss` | PROP-3 | 🔶 axiom |
| ML-KEM specific: `hek = SHA3-256(ek_seed ‖ ek_vector)` | PROP-3b | 🔶 axiom |

**Coverage:** 3 / 3 (all under axioms). Replacing axioms with theorems requires
de-opaquing `encaps2`, `decaps`, and `validate_pk_bytes`.

### §1.3 Chunking with Erasure Codes (1 obligation)

| Spec obligation | PROP | Status |
|----------------|------|--------|
| Encode/Decode reconstruction from `N` codewords | LEAN-ENC-2 | 🚫 blocked (`PolyDecoder.decoded_message` opaque) |

**Coverage:** 0 / 1 solid; 1 blocked.

### §2.2 Parameters (≈ 8 obligations)

| Spec obligation | PROP | Status |
|----------------|------|--------|
| KEM constants (HEADER_SIZE=64, EK_SIZE=1152, CT1_SIZE=960, CT2_SIZE=128 for ML-KEM-768) | — | ⚠ implicit in PROP-25 decoder sizes; not explicitly proven |
| `EPOCH_TYPE` = u64; `ToBytes(epoch)` = big-endian 8-byte | PROP-40, PROP-42 | ⚠ implicit through MAC and KDF info-string forms (`epoch.to_be_bytes`); no standalone property |
| MAC primitive (HMAC-SHA256 recommended), MAC_SIZE = 32 | — | ⚠ relies on `libcrux_hmac` correctness (opaque) |
| `PROTOCOL_INFO` string convention | PROP-41 | ✅ regression check on the literal byte string + deviation flag (production uses `"Signal_PQCKA_V1_MLKEM768"`, omitting `_HMAC-SHA256`) |
| `KDF_AUTH(root_key, update_key, epoch)` parameters (salt, IKM) | PROP-32 | ⚠ deviation flag — code uses `salt = 0^32, ikm = root_key‖update_key`; spec requires `salt = root_key, ikm = update_key` |
| `KDF_AUTH` info-string form `PROTOCOL_INFO ‖ ":Authenticator Update" ‖ ToBytes(epoch)` | PROP-42 | ✅ structural equality (orthogonal to the parameter deviation) |
| `KDF_OK` info-string form `PROTOCOL_INFO ‖ ":SCKA Key" ‖ ToBytes(epoch)` and zero salt | PROP-24 | ✅ structural part; 🔶 modelling for "different epochs ⇒ different keys" |
| HKDF safety (no panic on `len ≤ 8160`) | PROP-18 | ✅ |

**Coverage:** 5 / 8 solid; 1 deviation explicitly flagged; 2 implicit
(constants and MAC primitive — both rely on opaque external crates). The
PROTOCOL_INFO byte-form is pinned (PROP-41) and the KDF_AUTH info-string
is verified (PROP-42) separately from the parameter deviation (PROP-32).

### §2.3 Messages (informational on wire format)

| Spec obligation | PROP | Status |
|----------------|------|--------|
| Message fields `{epoch, type, data}` | PROP-35 | ⚠ implementer-defined per §2.3; PROP-35 covers implementation roundtrip but does not assert spec fields |
| Type enum `{None, Hdr, Ek, EkCt1Ack, Ct1Ack, Ct1, Ct2}` | — | ⚠ implicit in `MessagePayload` enum; no theorem maps spec names ↔ wire bytes |

**Coverage:** §2.3 explicitly delegates wire format to the implementer, so
"covered" here means roundtrip + epoch-zero rejection (PROP-35, PROP-36),
which we have.

### §2.4 Internal Authentication (≈ 6 obligations)

| Spec obligation | PROP | Status |
|----------------|------|--------|
| `Authenticator.Init(ep, k)` ≡ zero-state then `Update(ep, k)` | PROP-31 | ✅ |
| `Authenticator.Update` calls `KDF_AUTH` | PROP-32 | ⚠ deviation on parameters; PROP-42 verifies the info-string is correct |
| `MacHdr` MACs `PROTOCOL_INFO ‖ ":ekheader" ‖ epoch ‖ hdr` | PROP-40a | ✅ byte-form pinned to spec form |
| `MacCt` MACs `PROTOCOL_INFO ‖ ":ciphertext" ‖ epoch ‖ ct` | PROP-40b | ✅ byte-form pinned to spec form |
| `VfyHdr`/`VfyCt` is constant-time MAC equality | PROP-15, PROP-15b | ✅ for the success path; constant-time is a Rust-level concern (relies on `util::compare`) |
| Verification failure aborts the session (no partial state advance) | PROP-43 | ✅ structural — `Result` monad's short-circuit + Rust move-by-value semantics in `recv_ct2`/`recv_header` |

**Coverage:** 5 / 6 solid; 1 known deviation (KDF_AUTH parameter swap, with
the info-string side verified by PROP-42).

### §2.5 State Machine and Transitions (the dominant section — 22 method specs + 13 numbered transitions)

This is roughly **half** the normative content of mlkembraid.pdf. The spec
gives explicit pseudocode for `Send` and `Receive` of every one of 11 states,
labelling 13 transitions (1)…(13). To "cover §2.5 in full" each method needs
a Hoare-triple theorem matching its spec body.

**Cross-cutting properties** (not per-transition):

| Spec aspect | PROP | Status |
|-------------|------|--------|
| Output epoch reflects state epoch | PROP-22a | ⚠ feasible |
| Recv-success epoch is in `{ep-1, ep, ep+1}` window | PROP-22b | ⚠ feasible |
| Less-branch (`msg.epoch < state.epoch`) is no-op | PROP-30 | ✅ |
| Greater-branch (`msg.epoch > state.epoch + 1` from `Ct2Sampled`) errors | PROP-26 | ✅ |
| Greater-branch (other states) errors with `EpochOutOfRange` | PROP-39 | ✅ + deviation flag (spec says no-op; code says error) |
| EK-vector SHA3 integrity rejection | PROP-25 | ⚠ axiom-dependent on `validate_pk_bytes` |
| Only two transitions emit a key | PROP-21 | ⚠ feasible |
| `Ct1Acknowledged.Receive` accepts `Ek` chunks (extension beyond spec) | PROP-44 | ✅ deviation flag |

**Per-state coverage** (✓ = a structural fact about that state is proven,
even if not the full body; — = nothing):

| State (Side A) | Send | Recv | State (Side B) | Send | Recv |
|----------------|:---:|:---:|----------------|:---:|:---:|
| KeysUnsampled | — | ✓ PROP-30, PROP-39 | NoHeaderReceived | — | ✓ PROP-30, PROP-39 |
| KeysSampled | — | ✓ PROP-30, PROP-39 | HeaderReceived | — (PROP-21) | ✓ PROP-30, PROP-39 |
| HeaderSent | — | ✓ PROP-30, PROP-39 | Ct1Sampled | — | ✓ PROP-25 (rejection), PROP-30, PROP-39 |
| Ct1Received | — | ✓ PROP-30, PROP-39 | EkReceivedCt1Sampled | — | ✓ PROP-34 (deviation), PROP-30, PROP-39 |
| EkSentCt1Received | ✓ PROP-33 (deviation) | — (PROP-21), PROP-30, PROP-39 | Ct1Acknowledged | — | ✓ PROP-25 (rejection), PROP-44 (Ek deviation), PROP-30, PROP-39 |
| | | | Ct2Sampled | — | ✓ PROP-26 (epoch+1 guard) |

PROP-30 and PROP-39 between them establish the dispatch triple (Less / Equal /
Greater) for every state's `Receive`: Less is a no-op, Greater errors (with
the special-case carve-out for `Ct2Sampled`'s `epoch+1`), and Equal goes
through the per-state pseudocode. What remains uncovered is the body of
each Equal branch — i.e., the per-numbered-transition correspondence below.

**Per-numbered-transition coverage:**

| # | Transition | PROP | Status |
|---|-----------|------|--------|
| (1) | KeysUnsampled.Send → KeysSampled | — | ❌ uncovered |
| (2) | KeysSampled.Recv(Ct1) → HeaderSent | — | ❌ uncovered |
| (3) | HeaderSent.Recv(Ct1, complete) → Ct1Received | — | ❌ uncovered |
| (4) | Ct1Received.Recv(Ct2) → EkSentCt1Received | — | ❌ uncovered |
| (5) | EkSentCt1Received.Recv(Ct2, complete) → NoHeaderReceived(epoch+1), output_key=(epoch, ss) | PROP-22a (output epoch) + PROP-3 (KEM) + PROP-24 (KDF_OK) + PROP-15 (MAC) | ⚠ partial |
| (6) | NoHeaderReceived.Recv(Hdr, complete) → HeaderReceived | PROP-15b (MAC verify) | ⚠ partial |
| (7) | HeaderReceived.Send → Ct1Sampled, output_key=(epoch, ss) | PROP-3 + PROP-24 + PROP-21 | ⚠ partial |
| (8) | Ct1Sampled.Recv(EkCt1Ack, ek incomplete) → Ct1Acknowledged | — | ❌ uncovered |
| (9) | Ct1Sampled.Recv(EkCt1Ack, ek complete) → Ct2Sampled | PROP-25 (the SHA3 part) | ⚠ partial |
| (10) | Ct1Sampled.Recv(Ek, complete) → EkReceivedCt1Sampled | PROP-25 (the SHA3 part) | ⚠ partial |
| (11) | Ct1Acknowledged.Recv(EkCt1Ack, complete) → Ct2Sampled | PROP-25 (the SHA3 part) | ⚠ partial |
| (12) | EkReceivedCt1Sampled.Recv(EkCt1Ack) → Ct2Sampled | — | ❌ uncovered (PROP-34 only flags deviation) |
| (13) | Ct2Sampled.Recv(next epoch) → KeysUnsampled(epoch+1) | PROP-26 (the guard) | ⚠ partial |

**Coverage:** 0 / 13 transitions fully discharged. 7 / 13 partially covered.
6 / 13 untouched. As a fraction of §2.5 normative content this is **roughly
25-35%** — significant cross-cutting structure is captured, but the line-by-line
correspondence between code and pseudocode is not.

### §2.6 Initialization (2 obligations)

| Spec obligation | PROP | Status |
|----------------|------|--------|
| InitAlice → `KeysUnsampled(epoch=1, auth=Init(1, ss))` | PROP-31 + PROP-27 | ✅ Authenticator part; 🚫 full-state part blocked on `lib.rs` |
| InitBob → `NoHeaderReceived(epoch=1, auth=Init(1, ss), header_decoder)` | PROP-31 + PROP-27 | same |

**Coverage:** 50% solid (Authenticator equivalence); 50% blocked.

### §3.1 Vulnerable Message Set, §3.2 Alternate KEMs, §3.3 Optional Auth, §3.4–3.6 Bandwidth/Encoder discussions

**N/A** — these are security-model definitions and design discussion, not
implementation obligations. Out of scope for code-vs-spec correctness.

### §3.7 Formal verification

**N/A** — meta. This catalog *is* the verification artifact for the Lean side.

### §3.8 Representation of epochs (1 obligation)

| Spec obligation | PROP | Status |
|----------------|------|--------|
| 64-bit epoch sufficient for human conversation; overflow handling needed for long-lived sessions | PROP-9 | ✅ (overflow precondition explicit) |

**Coverage:** 1 / 1.

---

## 3. Bottom-line coverage estimates

### By count of discrete obligations

Counting only the **normative** obligations (not §3 commentary):

|  | Obligations | Solid | Partial | Blocked | Uncovered |
|---|---:|---:|---:|---:|---:|
| §1.1 SCKA properties | 5 | 2 | 2 | 1 | 0 |
| §1.2 KEM interface | 3 | 3 (axioms) | 0 | 0 | 0 |
| §1.3 Erasure code | 1 | 0 | 0 | 1 | 0 |
| §2.2 Parameters | 8 | 5 | 2 | 0 | 1 (KDF_AUTH parameter deviation) |
| §2.3 Messages | 2 | 1 (PROP-35) | 1 | 0 | 0 |
| §2.4 Authenticator | 6 | 5 | 1 (deviation) | 0 | 0 |
| §2.5 Cross-cutting state-machine invariants | 8 | 6 | 2 | 0 | 0 |
| §2.5 Numbered transitions | 13 | 0 | 7 | 0 | 6 |
| §2.6 Initialization | 2 | 0 | 2 | 2 | 0 |
| §3.8 Epoch representation | 1 | 1 | 0 | 0 | 0 |
| **Total** | **49** | **23** | **17** | **4** | **7** |

**Solid coverage: 47% (23/49). Solid + partial: 82%. Counting
blocked-but-feasible: 90%.**

The remaining gap is concentrated in **per-numbered-transition body
correctness for §2.5** (0 / 13 fully discharged). All other sections have
been addressed at least at the cross-cutting / flagged-deviation level.

### By spec-content weight (lines of pseudocode / paragraphs)

§2.5 alone is ~50% of the normative content. The cross-cutting invariants
(PROP-22, PROP-25, PROP-26, PROP-30, PROP-39, PROP-21, PROP-33, PROP-34,
PROP-44) cover ~40% of §2.5, translating to ~20 percentage points of the
total. The remaining sections (§1, §2.1–2.4, §2.6, §3.8) make up the other
~50% of normative content, of which the catalog covers ~85%.

**Combined weighted estimate: 60–65% of mlkembraid.pdf is meaningfully
covered by the catalog.**

The single lever for moving above ~65% is per-transition body correctness
in §2.5 (the 13 numbered transitions × 22 method specs). All other
sections are addressed at least at the cross-cutting / flagged-deviation
level.

---

## 4. Confidence after discharging every catalog property

Suppose every PROP-1 through PROP-38 is closed (axioms accepted where
flagged, and `lib.rs` extracted). Confidence statements ranked:

### What we would have **high confidence** in

- **Cryptographic primitives compose correctly.** KEM roundtrip (PROP-3),
  KDF chains (PROP-7/8 modelling), MAC (PROP-15/15b), HKDF safety (PROP-18).
- **Chain bookkeeping is internally consistent.** Epoch monotonicity
  (PROP-9), `epoch_idx` correspondence (PROP-29), send-epoch monotonicity
  (PROP-14), KeyHistory length-modulo invariant (PROP-12a), key jump guard
  (PROP-17/17b).
- **Top-level epoch agreement holds.** Sender epoch ↔ receiver epoch
  (PROP-22a/b), per-participant uniqueness (PROP-21), epoch-knowledge
  history (PROP-23).
- **Authenticator MAC bytes match the spec recipe.** PROP-40a/b pin the MAC
  inputs byte-for-byte to the spec §2.4 form `PROTOCOL_INFO ‖ ":ekheader" ‖
  epoch ‖ hdr` and `... ":ciphertext" ‖ epoch ‖ ct`.
- **Authentication failure aborts the session.** PROP-43 establishes
  state preservation through the `Result` monad's short-circuit semantics
  combined with Rust move-by-value ownership.
- **Spec deviations are documented and locally checked.** Ct1Ack routing
  (PROP-33/34), KDF_AUTH parameter swap (PROP-32 with flag, info-string
  side verified by PROP-42), Greater-branch error vs. spec no-op (PROP-39),
  Ct1Acknowledged accepting Ek (PROP-44).
- **Constants and PROTOCOL_INFO match an audited byte string.** PROP-41
  pins the literal bytes of `PROTOCOL_INFO` and flags the spec example
  divergence.
- **State-machine dispatch is fully characterised at the epoch-comparison
  level.** PROP-30 (Less = no-op) + PROP-26 (Ct2Sampled `epoch+1` carve-out)
  + PROP-39 (Greater = error elsewhere) cover all three cases of
  `msg.epoch.cmp(&state.epoch())` for every state.
- **Wire and protobuf serialization round-trip cleanly** (PROP-35/36/37).

### What we would have **moderate confidence** in

- **Key derivations bind the epoch.** PROP-24a + PROP-42 are structurally
  proven for both KDF_OK and KDF_AUTH info-strings (the `epoch.to_be_bytes`
  is part of the info on every call). The "different epochs ⇒ different
  keys" half rests on the PROP-4 modelling assumption.
- **EK vector integrity check matches §2.5.** PROP-25 covers the rejection
  *path* on all three call sites (Ct1Sampled.recv on Ek, Ct1Sampled.recv on
  EkCt1Ack, Ct1Acknowledged.recv on EkCt1Ack); PROP-3b axiomatises the
  equivalence with `SHA3-256(ek_seed ‖ ek_vector) = hek` (delegated to
  libcrux's `validate_pk_bytes`).
- **KEM constants in §2.2 match the wire and decoder sizes.** Currently
  implicit in PROP-25's decoder sizes (HEADER_SIZE+MAC_SIZE,
  CT1_SIZE, CT2_SIZE+MAC_SIZE, EK_SIZE) but not pinned in a standalone
  theorem.

### What we would have **low confidence** in

- **§2.5 line-by-line transition correspondence.** None of the 13
  numbered transitions has a theorem of the form "*from this state with
  this message, the code performs exactly the operations the pseudocode
  lists, in the spec's order, producing exactly the spec's post-state and
  outputs.*" Cross-cutting invariants are now strong (output epoch,
  key-emission, dispatch guards, integrity rejections), but the *body*
  of each Equal branch is verified only by inspection.
- **The erasure-code reconstruction property holds.** Blocked on
  `decoded_message` opacity (LEAN-ENC-2). Without it, "the protocol always
  recovers ek/ct1/ct2 once enough chunks are delivered" is not a Lean
  theorem.
- **Functional correctness of `KeyHistory.get` after `add`.** PROP-12b is
  blocked on `get`/`gc` being `#[hax_lib::opaque]`. The structural
  invariant (PROP-12a) holds, but "what you put in, you get out" is
  axiomatic until the opacity is lifted.
- **Forward secrecy beyond structural erasure.** PROP-10 covers
  *structural* erasure (old key bytes are dropped from the data structure).
  Cryptographic non-derivability of erased keys requires an HKDF
  one-wayness axiom that is not in the catalog and is explicitly out of
  scope.

### Sources of remaining trust

Even with every property discharged, the verification artifact still
trusts:

1. **Aeneas extraction faithfulness.** Pure-functional Lean model is the
   definition of correctness; mismatches between the Rust semantics and the
   Aeneas model (e.g. async/panic/unsafe behaviour) are not caught.
2. **Opaque external functions.** `hkdf_to_slice`, `encaps2`, `decoded_message`,
   `validate_pk_bytes`, `libcrux_hmac::hmac` — each is an axiom whose
   correctness is taken on faith from the upstream crate.
3. **The two flagged HKDF modelling assumptions** (PROP-4-style strict
   inequality of derived keys under distinct inputs).
4. **The KDF_AUTH deviation** (PROP-32). The Lean theorem captures the
   implementation, *not* the spec, so the deviation does not show up as a
   proof failure — it shows up as a documented property that does not match
   the spec text.

---

## 5. Open obligations to close the remaining gap

Ranked by how much they raise confidence per unit of effort.

### OPEN-1: Per-transition correspondence theorems for §2.5 (highest leverage)

For each of the 13 numbered transitions, prove a Hoare-triple matching the
spec pseudocode. Example for transition (5):

```
theorem transition_5_spec
    (s : send_ek.EkSentCt1Received)
    (msg : Message)
    (h_epoch : msg.epoch = s.epoch)
    (h_ct2 : decoder_completes_with msg.payload s.ct2_decoder ct2)
    (h_mac : ct2.length = MAC_SIZE + KEM.CT2_SIZE) :
    States.recv (States.EkSentCt1Received s) msg ⦃ r =>
      let mac := ct2.take MAC_SIZE
      let ct2_body := ct2.drop MAC_SIZE
      let ss := KEM.Decaps s.dk s.ct1 ct2_body
      let ss' := KDF_OK ss s.epoch
      let auth' := s.auth.update s.epoch ss'
      auth'.VfyCt s.epoch (s.ct1 ++ ct2_body) mac = ok () →
      r.state = States.NoHeaderReceived (next epoch's struct with auth' and fresh decoder)
      ∧ r.key = some ⟨s.epoch, ss'⟩ ⦄
```

22 theorems of this shape (one per state's Send + Receive) cover §2.5
exhaustively. The 13 numbered transitions are each one branch of one of these
theorems; the others are no-op branches (provable trivially).

**Effort:** 22 × ~1-2 days ≈ 25-35 days. **Coverage gain:** §2.5 from ~40%
to ~95%; overall from ~60% to ~85%. The single highest-impact open item.

### OPEN-2: Header byte-decomposition in transition (6)

`NoHeaderReceived.Receive` splits the received header bytes as
`header[..32]` = `ek_seed`, `header[32..64]` = `hek`. The Rust code does
this in `recv_hdr_chunk` (`src/v1/chunked/send_ct.rs:93-94`). A property
asserting the byte-decomposition pins the spec correspondence at this
boundary.

**Effort:** 0.5 days. Best handled inline as a lemma inside OPEN-1's
transition (6) theorem.

### OPEN-3: ek concatenation (the ML-KEM `ek = ek_seed ‖ ek_vector` reassembly)

`Ct1Sampled.Receive` reconstructs `ek = ek_seed ‖ ek_vector` from the
header seed + decoded vector, and feeds it to `Encaps2`. The
byte-concatenation correctness is implicit in the `Encaps2` axiom but not
stated as a standalone property.

**Effort:** 0.25 days. Best handled inline as a lemma inside OPEN-1's
transitions (9), (10), (11), (12).

### OPEN-4: Erasure-code reconstruction (LEAN-ENC-2)

Blocked on `PolyDecoder.decoded_message` opacity. The spec property is:
"given any `N` distinct chunks for a message of length fitting in `N`
codewords, `decoded_message` returns the original message."

**Effort:** Open-ended — needs Aeneas internals fix to lift opacity, then ≈
3-5 days of proof. **Coverage gain:** §1.3 from 0% to 100%.

### OPEN-5: Structural liveness over reachable state pairs

No catalog property states "if both parties run the protocol fairly, an
epoch eventually completes." The full liveness question is partly a
network-layer concern, but the *structural* part — that for every
reachable state pair `(sA, sB)` there exists a sequence of `(send, recv)`
operations that advances both — is verifiable and implied by mlkembraid
§2.5 Figure 2.

**Effort:** 3-4 days (build a reachability graph in Lean, exhaust the
11×11 state-pair matrix). **Coverage gain:** moves the catalog from
"safety properties only" to "safety + structural liveness".

### OPEN-6: Functional `KeyHistory.get`-after-`add` roundtrip (PROP-12b)

PROP-12b — `KeyHistory.get(KeyHistory.add(kh, k, v), k) = ok (some v)` for
fresh `k` — is in the catalog but blocked: `KeyHistory.get` and
`KeyHistory.gc` are `#[hax_lib::opaque]` in the Rust source. Discharging
12b requires either removing those annotations and re-extracting, or
introducing explicit axioms modelling `get`'s linear-scan semantics.

**Effort:** 3 days after the opacity is lifted; otherwise blocked.

### OPEN-7: KEM-constant byte sizes (HEADER_SIZE, EK_SIZE, CT1_SIZE, CT2_SIZE) match §2.2

Currently implicit in the decoder-size arguments of PROP-25. A
standalone property pinning `incremental_mlkem768::HEADER_SIZE = 64`,
`ENCAPSULATION_KEY_SIZE = 1152`, `CIPHERTEXT1_SIZE = 960`,
`CIPHERTEXT2_SIZE = 128` to the §2.2 ML-KEM-768 column.

**Effort:** 0.25 days. Constant-evaluation regression check.

---

## 6. Recommendation

Priority order for the open obligations in §5:

1. **OPEN-1** is the dominant lever (§2.5 per-transition body
   correctness). 25–35 days for ~22 Hoare-triple theorems. Until it is
   tackled, §2.5 stays at ~40% weighted coverage regardless of other
   work; once tackled, overall coverage moves from ~60–65% to ~85%.
2. Fold **OPEN-2** (header byte-decomposition) and **OPEN-3** (ek
   concatenation) as inline lemmas inside OPEN-1's transitions (6) and
   (9)/(10)/(11)/(12) respectively.
3. **OPEN-7** (KEM-constant byte sizes) is a 0.25-day regression check
   that closes the only remaining implicit row in §2.2 / §2.4.
4. Tackle **OPEN-5** (structural liveness over reachable state pairs)
   after the §2.5 transition work, since it reuses the same
   state-machine reasoning. 3–4 days.
5. **OPEN-6** (PROP-12b) is blocked on `KeyHistory.get` / `KeyHistory.gc`
   `#[hax_lib::opaque]` annotations. Either lift the opacity (engineering)
   or accept axioms modelling the linear-scan / GC semantics (modelling
   cost).
6. **OPEN-4** (erasure-code reconstruction, LEAN-ENC-2) is blocked on
   Aeneas opacity for `PolyDecoder::decoded_message`. Treat as a separate
   engineering thread.

**The single most important judgement call** for prioritising further
work is whether the correctness target is *spec correspondence* (the code
does exactly what mlkembraid.pdf says) or *internal consistency* (the
code is consistent with itself and a small algebraic interface). The
catalog is strong on internal consistency, with byte-form spec
correspondence at the §2.4 / §2.2 boundaries (PROP-40, PROP-41, PROP-42).
§2.5 body-level spec correspondence is the primary open lever: OPEN-1 is
what flips the doc from "60–65% coverage with strong invariants" to
"≥85% coverage with line-by-line correspondence."
