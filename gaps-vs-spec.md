# Gaps and unjustified misalignments: `src/` vs. `mlkembraid.pdf`

This list comes from reading mlkembraid.pdf cover-to-cover and walking the Rust state machine (`src/v1/chunked/` and `src/v1/unchunked/`) and the cryptographic helpers (`src/authenticator.rs`, `src/kdf.rs`, `src/incremental_mlkem768.rs`, `src/v1/chunked/states/serialize.rs`).

Severity ratings:
- 🔴 **Cryptographic deviation** — output bytes differ from a spec-compliant implementation
- 🟠 **Behavioral deviation** — observable protocol behavior differs (states reachable / messages sent / errors raised)
- 🟡 **Tightening** — code is stricter than spec; affects liveness/robustness, not correctness
- 🔵 **Looseness** — code accepts more than spec; could enable unspec'd interleavings
- ⚪ **Spec-silent / cosmetic** — spec doesn't say; code chose; worth flagging

---

## 🔴 1. `Authenticator.Update` uses HKDF wrong — different output bytes than spec

**Spec** (mlkembraid.pdf §2.2, `KDF_AUTH`):

```
HKDF input key material = update_key
HKDF salt                = root_key
HKDF info                = PROTOCOL_INFO || ":Authenticator Update" || ToBytes(epoch)
HKDF length              = 64
```

**Code** (`src/authenticator.rs:44-54`):

```rust
let ikm = [self.root_key.as_slice(), k].concat();   // root_key || update_key
let info = [b"Signal_PQCKA_V1_MLKEM768:Authenticator Update".as_slice(),
            &ep.to_be_bytes()].concat();
let kdf_out = kdf::hkdf_to_vec(&[0u8; 32], &ikm, &info, 64);  // salt = 32 zero bytes
```

The code feeds `salt = 32 zero bytes` and `ikm = root_key || update_key`. The spec demands `salt = root_key` and `ikm = update_key`. Since `HKDF-Extract = HMAC(salt, ikm)`, the Extract step computes a different value, and therefore `root_key`, `mac_key`, and every downstream MAC differ between a spec-compliant peer and this code.

**Consequence:** any peer running the spec verbatim cannot interoperate with this implementation — every header/ciphertext MAC will fail to verify after the first epoch. Within this codebase both sides agree (they're both wrong the same way), so internal tests pass.

This is the single most material deviation. Either the code should be fixed to match the spec, or the spec should be amended to match the code (and the rationale for `salt = zeros, ikm = root||update` documented).

The same critique does **not** apply to `KDF_OK`: `src/v1/unchunked/send_{ek,ct}.rs` correctly uses `salt = [0u8; 32]`, `ikm = shared_secret`, `info = PROTOCOL_INFO || ":SCKA Key" || epoch_be8`, exactly as §2.2 requires.

---

## 🟠 2. `EkSentCt1Received.Send` emits `Ct1Ack` instead of `None` — fixes a spec deadlock

**Spec** (page 15):

```python
def EkSentCt1Received.Send(state):
  # No data to send
  msg = {epoch: state.epoch, type: None}
```

**Code** (`src/v1/chunked/states.rs:178-184`):

```rust
Self::EkSentCt1Received(state) => Ok(Send {
    msg: Message { epoch, payload: MessagePayload::Ct1Ack(true) },  // <-- not None
    ...
})
```

This is paired with §3 below.

---

## 🟠 3. `EkReceivedCt1Sampled.Receive` accepts `Ct1Ack(true)` to advance — spec accepts only `EkCt1Ack`

**Spec** (page 21):

```python
if msg.epoch == state.epoch and msg.type == EkCt1Ack:
    ... transition (12) → Ct2Sampled
```

**Code** (`src/v1/chunked/states.rs:464-477`):

```rust
if matches!(msg.payload, MessagePayload::Ct1Ack(true) | MessagePayload::EkCt1Ack(_)) {
    Self::Ct2Sampled(state.recv_ct1_ack(msg.epoch))
}
```

**Why these two together matter.** Walk the figure-2 reachable pairs:

1. `(HeaderSent_A, EkReceivedCt1Sampled_B)` is reachable: A finished sending the full ek_vector (so B's `ek_decoder` completed), but A has not yet received B's first `Ct1` chunk.
2. A then receives ct1 chunks → `Ct1Received` → eventually `EkSentCt1Received` (after B's `Ct2` chunks).
3. But for B to ever leave `EkReceivedCt1Sampled`, the spec requires an incoming `EkCt1Ack` — and that message type is only sent by `Ct1Received.Send`, never by `EkSentCt1Received.Send` (which emits `None`).

Per the spec, once A has progressed past `Ct1Received`, B can never receive `EkCt1Ack` again. If B happens to be in `EkReceivedCt1Sampled` at that moment, **the protocol deadlocks**.

The Rust code dodges this by (a) having `EkSentCt1Received` keep emitting `Ct1Ack(true)` payloads and (b) having `EkReceivedCt1Sampled.recv` advance on a bare `Ct1Ack(true)`. This is a behaviorally meaningful fix that is not in the spec. Either the spec needs a correction (most likely add `Ct1Ack` to the message type list of `EkSentCt1Received.Send` and accept it in `EkReceivedCt1Sampled.Receive`), or the code needs to come back to the spec — but the code's behavior here is the safer of the two and the spec is buggy.

---

## 🟠 4. `Ct1Sampled.Receive` of `EkCt1Ack` with no decoded ek transitions `Ct1Acknowledged` instead of accepting more `Ek` chunks afterward — spec is silent on follow-up `Ek`

**Spec** Ct1Acknowledged.Receive (page 21-22) only specifies the `EkCt1Ack` case.

**Code** `src/v1/chunked/states.rs:489-510` accepts both `Ek` and `EkCt1Ack` payloads in `Ct1Acknowledged` (the in-code comment says: "If we got all messages in order, we would never receive a msg.ek at this point ... However, we can get messages out of order, so let's use the msg.ek chunks if we get them.").

This is a defensive choice that helps with reordering but is not derivable from the spec. It is conservative (it can only help recovery), but it is not what the spec describes.

---

## 🟡 5. `msg.epoch > state.epoch` raises `Error::EpochOutOfRange` instead of being silently ignored

**Spec.** Every state's pseudocode is wrapped in `if msg.epoch == state.epoch and msg.type == ...` and falls through (no-op) otherwise. The spec returns `(receiving_epoch, output_key=None)` rather than failing on out-of-range epochs.

**Code** (`src/v1/chunked/states.rs:282-528`). Every receiving state has:

```rust
match msg.epoch.cmp(&state.epoch()) {
    Ordering::Greater => return Err(Error::EpochOutOfRange(msg.epoch)),
    Ordering::Less => /* stay */,
    Ordering::Equal => /* dispatch on payload */,
}
```

Only `Ct2Sampled` makes an exception for `state.epoch + 1` (transition 13). Anything further-future-than-that errors out.

**Consequence.** Under message reordering, a delivery that arrives "too far ahead" terminates the SPQR session at the caller (`lib.rs::recv` propagates the error). The spec would treat the same delivery as a no-op, leaving the state intact for the eventually-arriving in-window message. This is a tightening that hurts liveness under adversarial scheduling.

---

## 🟠 6. SHA3-256 ek_vector integrity check is delegated to libcrux, not performed inline

**Spec** Ct1Sampled.Receive transitions (10) and (11), and Ct1Acknowledged.Receive transition (11):

```python
if SHA3-256(state.ek_seed || ek_vector) != state.hek:
    raise Error("EK integrity check failed")
```

**Code** (`src/v1/unchunked/send_ct.rs::recv_ek`, `src/incremental_mlkem768.rs:28-30`):

```rust
pub fn ek_matches_header(ek: &EncapsulationKey, hdr: &Header) -> bool {
    incremental::validate_pk_bytes(hdr, ek).is_ok()
}
```

The check is hidden behind `libcrux_ml_kem::mlkem768::incremental::validate_pk_bytes`, which is presumed to perform `SHA3-256(ek_seed || ek_vector) =?= hek`. The behavior should be equivalent if libcrux is correct, but for a verification project this opacity is a blocker — the Lean/F\* extraction needs to either model `validate_pk_bytes` axiomatically or unfold it. Worth either:

1. Verifying `validate_pk_bytes` does exactly the spec check, in a comment / Lean spec, or
2. Performing the check inline (`SHA3-256(hdr[..32] || ek) == hdr[32..]`) so the spec correspondence is local and auditable.

---

## ⚪ 7. `PROTOCOL_INFO` in code omits the MAC algorithm identifier suggested by the spec example

**Spec** §2.2: *"PROTOCOL_INFO: The concatenation of a protocol identifier, a string representation of KEM, and a string representation of MAC, separated with the delimiter '_', such as `MyProtocol_MLKEM768_SHA-256`. The string representations of the ML-KEM Braid parameters are defined by the implementer."*

**Code:** `Signal_PQCKA_V1_MLKEM768`. The MAC identifier (`HMAC-SHA256` / `SHA-256`) is missing.

This is allowed (implementer-defined), but if a future variant wants to swap MAC primitives the wire/KDF context won't differentiate them. Worth aligning to the spec example pattern (e.g. `Signal_PQCKA_V1_MLKEM768_HMAC-SHA256`).

---

## 🟠 8. Auth state is mutated *before* MAC verification in `recv_ct2`

**Spec** (page 15) is fine with `Update → VfyCt` order.

**Code** (`src/v1/unchunked/send_ek.rs:155-160`) matches that order:

```rust
auth.update(epoch, &ss);
ct1.extend_from_slice(&ct2);
auth.verify_ct(epoch, &ct1, &mac)?;
```

That's spec-compliant for the order. The non-trivial subtlety is what happens on `verify_ct` failure: the in-memory `auth` already advanced. The spec says (§2.4) "should not proceed with the ML-KEM Braid session and should negotiate a new ML-KEM Braid session." The Rust code propagates `Err`, which by Rust move semantics drops the consumed `self` — so the SPQR caller never installs the post-update state. **Net effect matches the spec**, but only because `recv_ct2` consumes `self` by value. If a future refactor changes this to `&mut self`, the partially-advanced authenticator could leak into subsequent calls. Worth a comment or a defensive pattern (compute the new auth in a local, only commit if `verify_ct` succeeds).

The exact same shape applies to `recv_header` (consumes `self`, returns `HeaderReceived`); fine for now, fragile to refactors.

---

## 🟡 9. Epoch overflow is asserted, not checked

`src/v1/unchunked/send_ek.rs:161` and `send_ct.rs:200`:

```rust
hax_lib::assume!(epoch < u64::MAX);
```

`hax_lib::assume!` is a verifier hint, not a runtime guard. Spec §3.8 says: *"Using a 64-bit integer to represent the epoch will prevent this wraparound from ever happening in a human conversation, but for other applications of the ML-KEM Braid this wraparound should be considered."* For long-lived non-human sessions (machine-to-machine, archival), an actual `checked_add(1)` returning an explicit `Error::EpochOutOfRange` (or new `Error::EpochOverflow`) would close this.

---

## ⚪ 10. `MessagePayload::Ct1Ack(bool)` parameter is vestigial

**Spec §2.3:** `Ct1Ack`: "No payload, but the sender has completely received ct1." No data.

**Code:** `enum MessagePayload { ... Ct1Ack(bool), ... }`. Every construction is `Ct1Ack(true)`. Deserialization always produces `Ct1Ack(true)`. The bool is never `false` and never inspected — receivers match `MessagePayload::Ct1Ack(true)` only (e.g. `states.rs:466`), so `Ct1Ack(false)` would be silently ignored.

This is dead encoding capacity. Either remove the bool (`Ct1Ack` unit variant), or document what `false` would mean and use it. As-is it's a small but pure cruft point.

---

## ⚪ 11. Wire format embeds the SM-layer chunk index in the SCKA message

`src/v1/chunked/states/serialize.rs::serialize` writes:

```
[version u8][epoch varint][index varint][message_type u8][chunk?]
```

The second `index` (between epoch and type) is the SM-layer per-message key index, computed by `chain.send_key(...)` in `lib.rs:300`. Spec §2.3 lists message fields as `{epoch, type, data}` — no SM-index. Spec §2.3 also says implementers may design their own format, so this is permitted.

This blurs the SCKA/SM layering: deserializing an SCKA message in isolation now requires knowing the SM-layer's index field exists. If a future ML-KEM-Braid consumer wants to reuse the SCKA layer in a different SM compiler, this format is not portable. Worth either calling out in `code-vs-spec.md` that the wire format is SPQR-specific (not pure ML-KEM-Braid), or factoring it so the SCKA wire format is spec-clean and the SM index lives in a wrapping envelope.

---

## ⚪ 12. mlkembraid says `Ct1Ack` is a message type but no spec state ever sends one

Cross-referencing the spec's own contents:

- §2.3 lists `Ct1Ack: No payload, but the sender has completely received ct1.`
- No state's `Send` function in §2.5 ever produces a `Ct1Ack` message.

This is a spec-internal inconsistency, made visible by the code. It is consistent with §2 ("Behavioral deviation that fixes a spec deadlock"): the missing producer should be `EkSentCt1Received.Send`, and the missing consumer should be `EkReceivedCt1Sampled.Receive`. The code already implements both — the spec just needs to document them.

---

## Aspects checked and confirmed clean

These were verified to match the spec:

- **State variable contents.** Each chunked state's struct fields cover the spec's "additional state includes" list (with `hdr = ek_seed || hek` collapsed to one 64-byte buffer instead of two 32-byte fields — semantically equivalent).
- **Decoder sizes.** `header_decoder = HEADER_SIZE + MAC_SIZE`, `ct1_decoder = CT1_SIZE`, `ct2_decoder = CT2_SIZE + MAC_SIZE`, `ek_decoder = EK_SIZE`. All match §2.2 / §2.5.
- **MAC inputs.** `mac_hdr` MACs `PROTOCOL_INFO || ":ekheader" || epoch_be8 || hdr`. `mac_ct` MACs `PROTOCOL_INFO || ":ciphertext" || epoch_be8 || (ct1 || ct2)`. Order and labels match §2.4.
- **`KDF_OK` info string and parameters.** Match §2.2 (`PROTOCOL_INFO || ":SCKA Key" || epoch_be8`, salt = 32 zero bytes, length = 32).
- **Epoch increment timing.** Output keys are tagged with the *old* epoch (`output_key = (state.epoch - 1, ss)` after the state was rebound to `state.epoch + 1`); the Rust `EpochSecret { epoch, secret }` uses the pre-increment epoch.
- **Initialization.** `InitAlice → KeysUnsampled(1, auth)`, `InitBob → NoHeaderReceived(1, auth, header_decoder)`. Both run `Authenticator.Init(1, shared_secret) ≡ Update(1, shared_secret)` over a zeroed Authenticator. ✓
- **No-action receive in `KeysUnsampled` and `HeaderReceived`** (states whose Receive is documented as a no-op): code matches.

---

## Items that look like deviations but turn out to be out-of-scope of mlkembraid.pdf (so not gaps)

- The whole `chain.rs` / `chain.add_epoch` / per-message AEAD key derivation: that is the SCKA→SM compiler from 2025-2267 §3, *above* the mlkembraid layer.
- `Version::V0`/`V1` negotiation in `lib.rs`: SPQR deployment plumbing, not in mlkembraid.
- `ChainParams { max_jump = 25_000, max_ooo_keys = 2_000 }`: SM-layer tuning.
- `potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275`: workaround for an external libcrux bug.
- The `src/v1/unchunked/` variant: simplified non-chunked SCKA used internally by chunked; mlkembraid only describes the chunked protocol.

---

## Recommended actions, in priority order

1. **Fix `Authenticator::update`** to use `salt = root_key, ikm = update_key` per §2.2, *or* file a spec erratum and document the deviation. (#1 — only item that breaks interoperability.)
2. **Document the `Ct1Ack`-from-`EkSentCt1Received` path** in either the spec or a code comment; today it's an undocumented behavioral fix for a spec deadlock. (#2, #3, #12.)
3. **Decide on epoch out-of-range policy:** strict failure (current) vs. spec-style no-op. If keeping strict, add a comment justifying the divergence. (#5.)
4. **Make the SHA3-256 ek-vector integrity check explicit** (inline check, or a one-line lemma reference to `validate_pk_bytes`) so verification doesn't have to take libcrux on faith. (#6.)
5. **Tighten `Authenticator::update` against partial-advance failures** by computing into locals and committing only on success — defensive against future refactors. (#8.)
6. **Cosmetic cleanups:** remove the `Ct1Ack(bool)` parameter (#10), align `PROTOCOL_INFO` to `Signal_PQCKA_V1_MLKEM768_HMAC-SHA256` (#7), document the SM-layer index in the wire format (#11), make epoch overflow a runtime error (#9).
