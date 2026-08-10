# Layer 3: ML-KEM Braid Protocol (§2.2–§2.6)

> See [README.md](README.md) for extraction status, axiom conventions, and
> the master cross-reference table.

This file covers the concrete ML-KEM Braid protocol: parameters (§2.2),
messages (§2.3), the ratcheted authenticator (§2.4), the 11-state
state machine with 13 numbered transitions (§2.5), initialization (§2.6),
and cross-cutting serialization properties.

This is the largest layer, mirroring the fact that §2.5 alone is roughly
half the normative content of `mlkembraid.pdf`.

---

## §2.2 — Parameters

### PROP-18: HKDF Expand Safety [CONDITIONAL BEHAVIORAL SPEC] 🔶 AXIOM

**Source:** `production-code` (`.expect("all lengths should work for SHA256")`
in `src/kdf.rs:17`).

*All HKDF expand calls succeed (output length within SHA-256 limits).*

All call sites request 32, 64, or 96 bytes (well within the 8160-byte limit).

```lean
axiom hkdf_to_slice_succeeds (salt ikm info : Slice U8) (len : Usize)
    (h : len ≤ 8160) :
    hkdf_to_slice salt ikm info len ⦃ _ => True ⦄
```

| Aspect | Assessment |
|--------|------------|
| **Status** | 🔶 **AXIOM REQUIRED** — `hkdf_to_slice` opaque |
| **Estimated effort** | 0.5 days |

### PROP-24a: KDF_OK Structural Equality [SPEC CORRESPONDENCE]

**Source:** `spec-mlkembraid` (§2.2).

*Both call sites (in `send_ct1` and `recv_ct2`) use the same HKDF
parameterization with info = `PROTOCOL_INFO ‖ ":SCKA Key" ‖ epoch.to_be_bytes`.*

| Aspect | Assessment |
|--------|------------|
| **Status** | ⚠️ **FEASIBLE** — call-site syntactic equality, no axioms needed |
| **Estimated effort** | 0.5 days |

### PROP-24b: KDF_OK Epoch Binding [MODELLING ASSUMPTION] 🔶

**Source:** `spec-mlkembraid` (§2.2).

*Different epochs produce different keys.* Depends on the PROP-4
collision-infeasibility postulate.

| Aspect | Assessment |
|--------|------------|
| **Status** | 🔶 **MODELLING ASSUMPTION** |

### PROP-41: PROTOCOL_INFO Byte-Form [CONSTANT REGRESSION + DEVIATION FLAG]

**Source:** `production-code` + `spec-mlkembraid` (§2.2).

*The implementation uses `b"Signal_PQCKA_V1_MLKEM768"`, omitting the MAC
algorithm identifier the spec's example pattern includes.*

```lean
theorem protocol_info_bytes :
    PROTOCOL_INFO = "Signal_PQCKA_V1_MLKEM768".toUTF8
```

| Aspect | Assessment |
|--------|------------|
| **Status** | ⚠️ **FEASIBLE** — constant evaluation |
| **Estimated effort** | 0.25 days |

### PROP-42: KDF_AUTH Info-String Structural Equality [SPEC CORRESPONDENCE]

**Source:** `spec-mlkembraid` (§2.2) + `production-code`.

*The HKDF info string in `Authenticator::update` matches the spec's
§2.2 `KDF_AUTH` recipe: `PROTOCOL_INFO ‖ ":Authenticator Update" ‖ ToBytes(epoch)`.*

Orthogonal to the PROP-32 parameter deviation (salt/IKM swap).

| Aspect | Assessment |
|--------|------------|
| **Status** | ⚠️ **FEASIBLE** |
| **Estimated effort** | 0.5 days |

### Modelling Assumptions (PROP-4, PROP-7, PROP-8)

These are **not** correctness properties but cryptographic modelling assumptions
used by other proofs. Each axiomatises *collision infeasibility* for HKDF outputs
under distinct inputs. They are technically inconsistent with a mathematical
model of HKDF (which is a PRF, not an injection) and must be clearly labeled.

| ID | Scope | Used by |
|----|-------|---------|
| PROP-4 | HKDF domain separation (general) | PROP-7, PROP-8, PROP-24b |
| PROP-7 | Successive chain keys are distinct | Chain advancement proofs |
| PROP-8 | Root key changes on each epoch | Root ratchet proofs |

---

## §2.3 — Messages

### PROP-35: Wire-Format Roundtrip [SERIALIZATION]

**Source:** `production-code`.

*`Message.deserialize(Message.serialize(m, idx)) = ok (m, idx, _)` for every
valid message.*

| Aspect | Assessment |
|--------|------------|
| **Status** | ⚠️ **FEASIBLE** — depends on closing varint/chunk encode/decode loop sorries |
| **Estimated effort** | 2–3 days |

### PROP-36: Epoch-Zero Rejection [SERIALIZATION GUARD]

**Source:** `production-code` (`serialize.rs:253-256`).

*Wire-format epoch 0 is rejected. Combined with `msg.epoch - 1` arithmetic
in `lib.rs`, this prevents underflow.*

| Aspect | Assessment |
|--------|------------|
| **Status** | ⚠️ **FEASIBLE** |
| **Estimated effort** | 0.25 days |

### PROP-37: Protobuf State Roundtrip [SERIALIZATION]

**Source:** `production-code`.

*For every `States` variant `s`, `States.from_pb(States.into_pb s) = ok s`.*

| Aspect | Assessment |
|--------|------------|
| **Status** | ⚠️ **FEASIBLE** — case split over 11 variants × 2 substructures |
| **Estimated effort** | 3–4 days |

### PROP-38: Chain Protobuf Roundtrip [SERIALIZATION]

**Source:** `production-code` (`Chain::into_pb`/`Chain::from_pb`, `chain.rs:415-452`).

*`Chain.from_pb(c.into_pb()) = ok c`.*

| Aspect | Assessment |
|--------|------------|
| **Previous status** | Was **BLOCKED** — `into_pb`/`from_pb` believed opaque |
| **Current status** | ⚠️ **FEASIBLE** — both are full `def`s in `Funs.lean` (extracted despite `#[hax_lib::opaque]` Rust annotation; not in config's `opaque:` list) |
| **Estimated effort** | 2–3 days |

---

## §2.4 — Internal Authentication (Ratcheted Authenticator)

### PROP-15: Authenticator MAC-ct Roundtrip [ALGEBRAIC SPECIFICATION]

**Source:** `production-code` + `hax-cross`.

*`verify_ct(epoch, ct, mac_ct(epoch, ct))` succeeds for length-matched inputs.*

In Lean's pure-functional model, `hmac(k, m) = hmac(k, m)` holds by `rfl`
(even for opaque `hmac`), so the proof only requires `compare(a, a) = 0`
and `mac_ct`'s output-length postcondition. No HMAC axiom is needed.

```lean
theorem verify_ct_mac_roundtrip (auth : Authenticator) (epoch : U64) (ct : Slice U8) :
    auth.mac_ct epoch ct >>= fun mac =>
    auth.verify_ct epoch ct mac ⦃ r => r = ok () ⦄
```

| Aspect | Assessment |
|--------|------------|
| **Status** | ⚠️ **FEASIBLE** |
| **Estimated effort** | 1 day |

### PROP-15b: Authenticator MAC-hdr Roundtrip [ALGEBRAIC SPECIFICATION]

Parallel to PROP-15 for header MACs.

| Aspect | Assessment |
|--------|------------|
| **Status** | ⚠️ **FEASIBLE** |
| **Estimated effort** | 0.5 days |

### PROP-31: `Authenticator::new` ≡ Init from Spec §2.6 [STATE INVARIANT]

**Source:** `spec-mlkembraid` (§2.6).

*`Authenticator::new(k, ep)` produces an authenticator equivalent to a fresh
zero-state followed by `update(ep, k)`.*

```lean
theorem authenticator_new_eq_zero_then_update (k : Slice U8) (ep : Epoch) :
    authenticator.Authenticator.new k ep =
    let zero := { root_key := List.replicate 32 0, mac_key := List.replicate 32 0 }
    Authenticator.update zero ep k
```

| Aspect | Assessment |
|--------|------------|
| **Status** | ⚠️ **FEASIBLE** — structurally visible in extracted code |
| **Estimated effort** | 0.5 days |

### PROP-32: `Authenticator::update` Derivation [ALGEBRAIC SPECIFICATION + DEVIATION FLAG]

**Source:** `production-code` + `spec-mlkembraid` (§2.4).

*`update(ep, k)` derives `root_key` and `mac_key` from a single 64-byte HKDF
output, splitting `[..32]` and `[32..]`.*

**Spec deviation:** The implementation uses `salt = [0u8; 32]`,
`ikm = root_key || k`, deviating from spec §2.2 which prescribes
`salt = root_key`, `ikm = k`. The Lean theorem captures the *implementation's*
derivation; the deviation is documented, not hidden.

| Aspect | Assessment |
|--------|------------|
| **Status** | ⚠️ **FEASIBLE** |
| **Estimated effort** | 1 day |

### PROP-40a: MAC-hdr Input Byte-Form [SPEC CORRESPONDENCE]

**Source:** `spec-mlkembraid` (§2.4) + `production-code`.

*The MAC input bytes assembled by `mac_hdr` match:
`PROTOCOL_INFO ‖ ":ekheader" ‖ epoch ‖ hdr`.*

```lean
theorem mac_hdr_input_form (auth : Authenticator) (ep : Epoch) (hdr : Slice U8) :
    let expected := PROTOCOL_INFO ++ b":ekheader" ++ ep.to_be_bytes ++ hdr.toList
    Authenticator.mac_hdr auth ep hdr =
      hmac auth.mac_key expected MAC_SIZE
```

| Aspect | Assessment |
|--------|------------|
| **Status** | ⚠️ **FEASIBLE** — unfold extracted body, verify byte concatenation |
| **Estimated effort** | 0.25 days |

### PROP-40b: MAC-ct Input Byte-Form [SPEC CORRESPONDENCE]

Parallel to PROP-40a for `mac_ct`:
`PROTOCOL_INFO ‖ ":ciphertext" ‖ epoch ‖ ct`.

| Aspect | Assessment |
|--------|------------|
| **Status** | ⚠️ **FEASIBLE** |
| **Estimated effort** | 0.25 days |

### PROP-43: Authentication Failure State Preservation [CONDITIONAL BEHAVIORAL SPEC]

**Source:** `spec-mlkembraid` (§2.4) + `production-code`.

*When `verify_ct` or `verify_hdr` fails, the SPQR state is not advanced.
The error propagates via the `Result` monad's short-circuit, and Rust's
move-by-value ownership prevents partial state mutation from leaking.*

```lean
theorem recv_ct2_mac_failure_no_state_change
    (s : send_ek.EkSentCt1Received) (msg : Message)
    (h_mac_fail : auth.verify_ct epoch ct mac = Err e) :
    States.recv (States.EkSentCt1Received s) msg ⦃ r =>
      r = Err e ⦄
```

| Aspect | Assessment |
|--------|------------|
| **Status** | ⚠️ **FEASIBLE** — follows from `Result` monad short-circuit |
| **Estimated effort** | 1 day (covers both `recv_ct2` and `recv_header` paths) |

---

## §2.5 — State Machine (11 states, 13 numbered transitions)

### Cross-cutting epoch dispatch (PROP-26, PROP-30, PROP-39)

These three properties fully characterize the `msg.epoch.cmp(&state.epoch())`
dispatch for every state:

#### PROP-26: Ct2Sampled Future Epoch Guard ✅ PROVED

*Messages from epochs > `state.epoch + 1` are rejected with `EpochOutOfRange`.*

**Proof file:** `Spqr/Specs/States/Recv.lean`

```lean
@[step]
theorem v1.chunked.states.States.recv_Ct2Sampled_future_epoch_guard
    (state : v1.chunked.send_ct.Ct2Sampled)
    (msg : v1.chunked.states.Message)
    (h : msg.epoch.val > state.uc.epoch.val + 1) :
    v1.chunked.states.States.recv
      (v1.chunked.states.States.Ct2Sampled state) msg ⦃ r =>
      r = core.result.Result.Err (Error.EpochOutOfRange msg.epoch) ⦄
```

#### PROP-39: Greater-Branch EpochOutOfRange (Non-Ct2Sampled) ✅ PROVED

*For all 10 non-Ct2Sampled states, `msg.epoch > state.epoch` returns
`Err(EpochOutOfRange)`.*

**Spec deviation:** The spec treats epoch-mismatched messages as silent no-ops;
the code treats `msg.epoch > state.epoch` as a hard error. This is a behavioral
tightening documented as a deviation flag.

**Proof file:** `Spqr/Specs/States/Recv.lean` — 10 per-variant theorems, all
following the same pattern: unfold `recv`, `step*`, dismiss impossible `.lt`
branch by contradiction.

#### PROP-30: Less-Branch No-Op ✅ PROVED

*For every state variant (all 11 including Ct2Sampled), `msg.epoch < state.epoch`
returns `Ok { key := none, state := self }` — the state is unchanged.*

**Proof file:** `Spqr/Specs/States/Recv.lean` — 11 per-variant theorems.

### Key emission (PROP-21) ✅ PROVED

See [1_scka_interface.md](1_scka_interface.md) for the full table. Only
`HeaderReceived.send` (Side B, transition 7) emits `key = some _`.

**Proof file:** `Spqr/Specs/States/Send.lean`

### PROP-25: EK Integrity Verification [CONDITIONAL BEHAVIORAL SPEC]

**Source:** `spec-mlkembraid` (§2.5).

*When the encapsulation key vector is received, its integrity against the
header is verified before use.* The guard fires on three spec transitions:

- **Transition (9):** `Ct1Sampled.recv_ek_chunk` when `EkCt1Ack` completes ek
- **Transition (10):** `Ct1Sampled.recv_ek_chunk` when `Ek` completes ek
- **Transition (11):** `Ct1Acknowledged.recv_ek_chunk` when `EkCt1Ack` completes ek

All three route through `v1.unchunked.send_ct.Ct1Sent.recv_ek` (note: the
correct struct path is `Ct1Sent`, not `Ct1SentChunking`).

```lean
theorem recv_ek_rejects_mismatched
    (s : v1.unchunked.send_ct.Ct1Sent) (ek : EncapsulationKey)
    (h : ¬ ek_matches_header ek s.hdr) :
    s.recv_ek epoch ek ⦃ r => r = Err Error.ErroneousDataReceived ⦄
```

| Aspect | Assessment |
|--------|------------|
| **Status** | ⚠️ **FEASIBLE** at call-site level; PROP-3b is the missing spec link |
| **Estimated effort** | 1 day for all 3 call paths |

### Deviation flags

#### PROP-33: `EkSentCt1Received.send` Emits `Ct1Ack(true)` ✅ PROVED

*The spec's `EkSentCt1Received.Send` emits `None`; the code emits
`Ct1Ack(true)`. This prevents a spec-level deadlock.*

**Proof file:** `Spqr/Specs/States/Send.lean`

```lean
theorem v1.chunked.states.States.send_EkSentCt1Received_ct1_ack ... :
    ... ⦃ r =>
      ∃ s, r.1 = core.result.Result.Ok s ∧
      s.msg.payload = v1.chunked.states.MessagePayload.Ct1Ack true ∧
      s.key = none ∧
      s.state = v1.chunked.states.States.EkSentCt1Received state ∧
      r.2 = rng ⦄
```

#### PROP-34: `EkReceivedCt1Sampled.recv` Accepts `Ct1Ack(true)` [DEVIATION FLAG]

*The code transitions to `Ct2Sampled` on either `Ct1Ack(true)` or
`EkCt1Ack(_)`; the spec only describes `EkCt1Ack`. Combined with PROP-33,
this prevents a spec deadlock in certain reachable state pairs.*

| Aspect | Assessment |
|--------|------------|
| **Status** | ⚠️ **FEASIBLE** — structural |
| **Estimated effort** | 0.25 days |

#### PROP-44: `Ct1Acknowledged.Receive` Accepts `Ek` Chunks [DEVIATION FLAG]

*The code accepts `Ek` payload chunks in `Ct1Acknowledged` and feeds them to
the `ek_decoder`, where the spec only describes handling `EkCt1Ack`.
This is a conservative extension that helps recovery under out-of-order delivery.*

| Aspect | Assessment |
|--------|------------|
| **Status** | ⚠️ **FEASIBLE** — structural |
| **Estimated effort** | 0.5 days |

---

## §2.6 — Initialization

### PROP-27: Initialization Correctness [STATE INVARIANT]

**Source:** `spec-mlkembraid` (§2.6).

*Protocol initialization produces: Alice as `KeysUnsampled(epoch=1, auth=Init(1, ss))`
and Bob as `NoHeaderReceived(epoch=1, auth=Init(1, ss), header_decoder)`.*

| Aspect | Assessment |
|--------|------------|
| **At v1 layer** | The v1-level state types and `Authenticator.new` are extracted. |
| **At API level** | 🚫 **BLOCKED** — `initial_state` in `lib.rs` not extracted |
| **Estimated effort** | 0.5 days (after `lib.rs` extraction) |

### PROP-16: Version Negotiation Safety [CONDITIONAL BEHAVIORAL SPEC]

**Source:** `production-code` + `production-test`.

*If `min_version = V1` and the peer sends V0, `recv` returns `Error::MinimumVersion`.*

| Aspect | Assessment |
|--------|------------|
| **Status** | 🚫 **BLOCKED** — `lib.rs` `recv` not extracted |
| **Estimated effort** | 2 days (after `lib.rs` extraction) |
