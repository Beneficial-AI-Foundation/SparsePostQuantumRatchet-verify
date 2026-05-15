# Spec–code mismatches in SPQR: findings from verification work

This report documents mismatches between `mlkembraid.pdf` (Revision 1, 2025-02-21 / updated 2025-09-26) and the Rust implementation at [signalapp/sparsepostquantumratchet](https://github.com/signalapp/sparsepostquantumratchet).

Only items where the spec and code disagree in a way that affects interoperability, protocol liveness, the error model, or the set of accepted messages are included. Implementation-discretionary choices (wire format, `PROTOCOL_INFO` composition, code hygiene) are omitted.

---

## 1. `KDF_AUTH` parameter mapping: spec and code disagree on HKDF salt / IKM

**Spec** (§2.2, `KDF_AUTH`):

```
HKDF input key material = update_key
HKDF salt               = root_key
HKDF info               = PROTOCOL_INFO || ":Authenticator Update" || ToBytes(epoch)
HKDF length             = 64
```

**Code** (`src/authenticator.rs`, `Authenticator::update`):

```rust
let ikm = [self.root_key.as_slice(), k].concat();   // root_key || update_key
let kdf_out = kdf::hkdf_to_vec(&[0u8; 32], &ikm, &info, 64);
//                               ^^^^^^^^^^  ^^^
//                               salt=zeros   ikm=root_key||update_key
```

`kdf::hkdf_to_vec` forwards directly to `hkdf::Hkdf::<Sha256>::new(Some(salt), ikm)`, so the Extract step computes `HMAC(zeros, root_key || update_key)` instead of the spec's `HMAC(root_key, update_key)`.

**Impact.** A peer implementing `KDF_AUTH` as written in the spec would derive different `root_key` and `mac_key` values after the first `Update`, causing every subsequent MAC to fail. The code is self-consistent (both peers run the same derivation), so internal tests pass.

**Suggested resolution.** Either amend the spec to match the code's `salt = zeros, ikm = root_key || update_key` convention (and document the rationale), or update the code to use `salt = root_key, ikm = update_key` per the current spec text.

---

## 2. `Ct1Ack` is defined in the spec but never produced; code adds undocumented behavior

This is a spec-internal inconsistency combined with an unexplained code deviation.

### 2a. `EkSentCt1Received.Send` — spec sends `None`, code sends `Ct1Ack`

**Spec** (page 15, `EkSentCt1Received.Send`):

```python
msg = {epoch: state.epoch, type: None}
```

**Code** (`src/v1/chunked/states.rs:178–183`):

```rust
Self::EkSentCt1Received(state) => {
    let epoch = state.epoch();
    Ok(Send {
        state: Self::EkSentCt1Received(state),
        msg: Message { epoch, payload: MessagePayload::Ct1Ack(true) },
        key: None,
    })
}
```

### 2b. `EkReceivedCt1Sampled.Receive` — spec accepts only `EkCt1Ack`, code also accepts `Ct1Ack`

**Spec** (page 20–21, `EkReceivedCt1Sampled.Receive`):

```python
if msg.epoch == state.epoch and msg.type == EkCt1Ack:
    # Transition (12) → Ct2Sampled
```

**Code** (`src/v1/chunked/states.rs:464–467`):

```rust
if matches!(msg.payload, MessagePayload::Ct1Ack(true) | MessagePayload::EkCt1Ack(_)) {
    Self::Ct2Sampled(state.recv_ct1_ack(msg.epoch))
}
```

### 2c. §2.3 defines `Ct1Ack` but no `Send` function in §2.5 ever produces it

§2.3 lists `Ct1Ack` as a message type ("No payload, but the sender has completely received ct1"). However, inspecting every `Send` function in §2.5 shows that none ever emits a `Ct1Ack` message. The type is defined but has no producer in the spec.

### Assessment

The spec inconsistency (2c) is real: `Ct1Ack` is a dead definition.

The code deviations (2a and 2b) are also real: the code sends and accepts `Ct1Ack` in a way the spec does not describe. However, the state pair `(EkSentCt1Received_A, EkReceivedCt1Sampled_B)` that this code targets appears to be **unreachable** under the spec's own causal structure:

- A can only enter `EkSentCt1Received` by receiving a `Ct2` chunk (transition 4).
- B can only produce `Ct2` chunks from `Ct2Sampled` (transition 12 or 11).
- B can only enter `Ct2Sampled` from `EkReceivedCt1Sampled` by first receiving `EkCt1Ack`.
- Therefore, by the time A has received `Ct2` and entered `EkSentCt1Received`, B has already received `EkCt1Ack` and left `EkReceivedCt1Sampled`.

The code's extra `Ct1Ack` production and acceptance is therefore adding behavior for a state pair that cannot be reached. It is harmless — the extra `Ct1Ack` messages will never be received by a counterpart in `EkReceivedCt1Sampled`, and accepting `Ct1Ack` in that state will never trigger a spurious transition — but its motivation is unclear. A comment explaining the rationale would help auditors.

**Suggested resolution.**
- Clarify the spec: explain why `Ct1Ack` is listed in §2.3 if no state produces it, or remove the dead definition.
- Add a comment in the code explaining why `EkSentCt1Received.Send` emits `Ct1Ack` and why `EkReceivedCt1Sampled.Receive` accepts it, given that the target state pair appears unreachable.

---

## 3. `Ct1Acknowledged.Receive` accepts `Ek` chunks not described by the spec

**Spec** (page 21–22, `Ct1Acknowledged.Receive`): the only handled message type is `EkCt1Ack`. Any other message is a silent no-op.

**Code** (`src/v1/chunked/states.rs`, `Ct1Acknowledged` receive branch): also accepts `Ek` payload chunks and feeds them to the `ek_decoder`, with an explicit in-code comment: *"If we got all messages in order, we would never receive a msg.ek at this point … However, we can get messages out of order, so let's use the msg.ek chunks if we get them."*

**Assessment.** This is a conservative extension: accepting out-of-order `Ek` chunks in `Ct1Acknowledged` can only help recovery and cannot cause incorrect decapsulation (the SHA3-256 integrity check on the reassembled `ek_vector` is still performed before `Encaps2`). However, the spec does not describe this behavior, so a spec-compliant peer that logs or counts unexpected message types would see messages the spec says should not appear in this state. The deviation is worth documenting — either in the spec as a permitted optimization or in the code as a justified extension.

---

## 4. Future-epoch messages: spec ignores, code errors

**Spec.** Every state's `Receive` function is guarded by `if msg.epoch == state.epoch and msg.type == ...` and falls through (no-op, returns `output_key = None`) otherwise. A message with `msg.epoch > state.epoch` is silently ignored and the state is preserved.

**Code** (`src/v1/chunked/states.rs`, every receive branch):

```rust
match msg.epoch.cmp(&state.epoch()) {
    Ordering::Greater => return Err(Error::EpochOutOfRange(msg.epoch)),
    Ordering::Less    => /* stay in current state */,
    Ordering::Equal   => /* dispatch on payload */,
}
```

The one exception is `Ct2Sampled`, which accepts `state.epoch + 1` (transition 13). All other states treat `msg.epoch > state.epoch` as a hard error that terminates the SPQR session.

**Impact.** Under message reordering or delivery of a message from a future epoch, the spec would preserve the session (no-op), while the code terminates it. This is a tightening that reduces liveness. It may be the correct choice for Signal's transport (which provides ordering), but the divergence from the spec should be documented.

**Suggested resolution.** Either:
- Amend the spec to mandate the stricter behavior and document the rationale (e.g. Signal's transport guarantees ordering, so future-epoch messages are delivery errors, not benign reorderings), or
- Relax the code to match the spec's no-op semantics for future-epoch messages.
