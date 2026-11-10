# CVSS v3.1 scoring of the defects in `defect.md`

This file scores every finding of [`defect.md`](./defect.md) (identifiers `SPQR-<CLASS>-<slug>`;
see its "Identifier scheme" section and legacy `D<n>` map) using
**CVSS v3.1** (FIRST.org Common Vulnerability Scoring System) base metrics, with CWE
identifiers for classification. Scores were computed with the standard CVSS v3.1 equations.

## Scoring assumptions

CVSS scores an *attack on a deployed system*, so the attacker models of `defect.md` map to
CVSS metrics as follows:

| Reach qualifier | CVSS mapping | Rationale |
|---|---|---|
| `message` (on-path) | **AV:N / PR:N / UI:N** | The SPQR message travels over the network; `recv` runs on it before any MAC in the crate is checked. |
| `blob` (persisted state) | **AV:L / PR:H** | Writing the `pq_ratchet_state` protobuf requires control of local storage or of a state-sync channel — high-privilege in CVSS terms. Deployments that sync state across devices may warrant AV:N. |
| `local-config` | **AV:L / PR:H** | Requires the embedder to construct a bad `ChainParams`. |
| `spec` / scope | **not scored** | Soundness of annotations, models or theorem scope; no runtime attack surface of its own. |

Two scores are given where they differ materially:

* **Base** — the crate (`spqr`) evaluated standalone, as any embedder other than libsignal
  would use it. This is the headline score.
* **Adjusted (libsignal)** — an environmental note reflecting that libsignal clones the
  session, calls `pq_ratchet_recv` before `verify_mac`, and drops the clone on MAC failure,
  so network forgeries are not persisted there.

CVSS measures exploitability and impact, not protocol-design quality: several MEDIUM items in
`defect.md` (downgrade, verification-soundness) score low here because their *direct* impact
is availability-only or not runtime-reachable. The qualitative severities in `defect.md`
remain the primary triage signal; this file adds a standardized, comparable number.

## Scores

### Part I — unauthenticated control plane (network attacker)

| ID | Finding | CVSS v3.1 vector | Base | Adjusted (libsignal) | CWE |
|---|---|---|---|---|---|
| SPQR-AUTH-epoch-advance | Unauthenticated `Ct2Sampled → KeysUnsampled` epoch advance | `AV:N/AC:L/PR:N/UI:N/S:U/C:N/I:N/A:H` | **7.5 (High)** | ~0 vs. network (outer MAC); unchanged vs. malicious peer | CWE-306 (Missing Authentication for Critical Function) |
| SPQR-AUTH-ct1ack-accepted | `Ct1Ack` accepted in `EkReceivedCt1Sampled` | `AV:N/AC:H/PR:N/UI:N/S:U/C:N/I:N/A:H` | **5.9 (Medium)** | mitigated vs. network | CWE-306 |
| SPQR-AUTH-late-ek-chunk | `Ek` chunks absorbed in `Ct1Acknowledged` | `AV:N/AC:H/PR:N/UI:N/S:U/C:N/I:N/A:H` | **5.9 (Medium)** | mitigated vs. network | CWE-345 (Insufficient Verification of Data Authenticity) |
| SPQR-AUTH-chunk-poison | Persistent chunk poisoning (point never evicted) | `AV:N/AC:L/PR:N/UI:N/S:U/C:N/I:N/A:H` | **7.5 (High)** | mitigated vs. network; unchanged vs. malicious peer | CWE-345 / CWE-400 |
| SPQR-AUTH-v0-downgrade | Empty message finalises V0 downgrade | `AV:N/AC:H/PR:N/UI:N/S:U/C:L/I:L/A:N` | **4.8 (Medium)** | mitigated (MAC + v1.6.0 version hardening) | CWE-757 (Algorithm Downgrade) |
| SPQR-AUTH-index0-nokey | `index == 0` skips the epoch-0 PQ key | `AV:N/AC:L/PR:N/UI:N/S:U/C:N/I:L/A:N` | **5.3 (Medium)** | mitigated vs. network | CWE-757 / CWE-20 |
| SPQR-AUTH-index-cpu-amp | Pre-auth HKDF amplification via `index` | `AV:N/AC:L/PR:N/UI:N/S:U/C:N/I:N/A:L` | **5.3 (Medium)** | **not** mitigated (work happens before host MAC); rises toward 7.5 with libsignal's self-session `max_jump = u32::MAX` | CWE-400 (Uncontrolled Resource Consumption) |
| SPQR-AUTH-wire-noninjective | Non-injective wire format (non-minimal varints, trailing bytes, `Ct1Ack` flag) | `AV:N/AC:H/PR:N/UI:N/S:U/C:N/I:L/A:N` | **3.7 (Low)** | — | CWE-436 (Interpretation Conflict) / CWE-228 |
| SPQR-AUTH-a-encoder-drop | A drops `sending_hdr` / `sending_ek` on the first unauthenticated `Ct1` / `Ct2` chunk | `AV:N/AC:L/PR:N/UI:N/S:U/C:N/I:N/A:H` | **7.5 (High)** | mitigated vs. network; unchanged vs. malicious peer | CWE-306 / CWE-345 |
| SPQR-AUTH-b-encoder-drop | B drops `sending_ct1` on a forged `EkCt1Ack` | `AV:N/AC:L/PR:N/UI:N/S:U/C:N/I:N/A:H` | **7.5 (High)** | mitigated vs. network; unchanged vs. malicious peer | CWE-306 / CWE-345 |
| SPQR-AUTH-v1-lockin | Any V1 message closes version negotiation; genuine V0 peer locked out | `AV:N/AC:H/PR:N/UI:N/S:U/C:N/I:N/A:H` | **5.9 (Medium)** | mitigated vs. network | CWE-306 / CWE-757 |
| SPQR-AUTH-chain-advance-persist | Receive-chain advance from unauthenticated `index` is persisted (key loss) | `AV:N/AC:L/PR:N/UI:N/S:U/C:N/I:L/A:H` | **8.2 (High)** | mitigated vs. network by clone-and-drop; **unchanged** for any embedder that persists `Recv.state` before the outer MAC, and vs. a malicious peer | CWE-306 / CWE-345 / CWE-400 |

AC on SPQR-AUTH-ct1ack-accepted/SPQR-AUTH-late-ek-chunk/SPQR-AUTH-v0-downgrade/SPQR-AUTH-wire-noninjective/SPQR-AUTH-v1-lockin is High because exploitation needs the victim in a specific state
(negotiating, `EkReceivedCt1Sampled`, `Ct1Acknowledged`) or depends on outer-protocol use of
message bytes. SPQR-AUTH-epoch-advance/SPQR-AUTH-chunk-poison/SPQR-AUTH-index0-nokey/SPQR-AUTH-index-cpu-amp/SPQR-AUTH-chain-advance-persist need only the cleartext epoch/index of any observed message:
AC:Low. SPQR-AUTH-a-encoder-drop/SPQR-AUTH-b-encoder-drop are AC:Low as well: `KeysSampled`, `Ct1Received` and `Ct1Sampled` are the
*normal* states of every epoch while the header, `ek` and `ct1` are in flight — the attacker
does not need to wait for an unusual condition, only to send one chunk-shaped message during
the window, which the cleartext tag of the victim's own outgoing messages reveals.

SPQR-AUTH-chain-advance-persist scores above SPQR-AUTH-epoch-advance/SPQR-AUTH-chunk-poison because its impact is not only availability: `I:L` records that the
victim's persisted chain is modified (counter advanced, history cleared) by an unauthenticated
input, which is an integrity loss of the state even though no key is disclosed.

### Part II — arithmetic / parameter bounds

| ID | Finding | CVSS v3.1 vector | Base | CWE |
|---|---|---|---|---|
| SPQR-ARITH-ooo-u32-overflow | `u32` overflow in `KeyHistory::get` trimmed-check | `AV:N/AC:H/PR:N/UI:N/S:U/C:N/I:L/A:L` | **4.8 (Medium)**; `A:H` → **6.5** in debug builds (panic) | CWE-190 (Integer Overflow) |
| SPQR-ARITH-params-unchecked | `ChainParams` never range-checked | `AV:L/AC:L/PR:H/UI:N/S:U/C:N/I:N/A:H` | **4.4 (Medium)** | CWE-20 (Improper Input Validation) |
| SPQR-ARITH-trimsize-usize32 | 32-bit `trim_size` / GC-threshold overflow | `AV:L/AC:H/PR:H/UI:N/S:U/C:N/I:N/A:H` | **4.1 (Medium)** | CWE-190 |
| SPQR-ARITH-keyhistory-invariant | `KeyHistory` size invariant unmaintained | *not scored* (spec/annotation defect; runtime effects are counted under SPQR-ARITH-ooo-u32-overflow/SPQR-DESER-chain-frompb) | — | CWE-1068 (spec/implementation mismatch) |
| SPQR-ARITH-epochidx-trunc32 | `u64 → usize` truncation in `epoch_idx` (32-bit) | `AV:L/AC:H/PR:H/UI:N/S:U/C:N/I:H/A:N` | **4.1 (Medium)** | CWE-197 (Numeric Truncation) |
| SPQR-ARITH-encoder-idx-u16 | `PolyEncoder` `u32 → u16` index truncation | `AV:L/AC:H/PR:H/UI:N/S:U/C:N/I:N/A:L` | **1.9 (Low)** | CWE-197 |

### Part III — deserialisation without validation (blob attacker)

| ID | Finding | CVSS v3.1 vector | Base | CWE |
|---|---|---|---|---|
| SPQR-DESER-chain-frompb | `Chain*::from_pb` accepts blobs that later panic | `AV:L/AC:L/PR:H/UI:N/S:U/C:N/I:N/A:H` | **4.4 (Medium)**; AV:N → **4.9** where state is synced over a network channel | CWE-502 (Deserialization of Untrusted Data) / CWE-617 (Reachable Assertion) |
| SPQR-DESER-auth-keylen | `Authenticator::from_pb` accepts empty/over-long `mac_key` | `AV:L/AC:L/PR:H/UI:N/S:U/C:N/I:H/A:N` | **4.4 (Medium)**; chains with a network attacker to MAC forgery once set | CWE-502 / CWE-1390 (Weak Authentication) |
| SPQR-DESER-epoch-zero | `epoch == 0` state → `msg.epoch − 1` underflow in `send` | `AV:L/AC:L/PR:H/UI:N/S:U/C:N/I:N/A:H` | **4.4 (Medium)** (debug panic; release `A:L` ≈ 2.3) | CWE-191 (Integer Underflow) |
| SPQR-DESER-epoch-max | `epoch = u64::MAX` panics/wraps the epoch advance | `AV:L/AC:H/PR:H/UI:N/S:U/C:N/I:L/A:H` | **4.7 (Medium)** | CWE-190 / CWE-617 |
| SPQR-DESER-poly-points | Polynomial `from_pb` does not bound point counts | `AV:L/AC:L/PR:H/UI:N/S:U/C:N/I:L/A:H` | **5.1 (Medium)** | CWE-502 / CWE-400 |
| SPQR-DESER-is-complete | Blob-controlled `is_complete = true` permanently disables decoder | `AV:L/AC:L/PR:H/UI:N/S:U/C:N/I:N/A:H` | **4.4 (Medium)** | CWE-502 |
| SPQR-DESER-zero-poly-roundtrip | `deserialize ∘ serialize ≠ id` on zero polynomial | `AV:L/AC:H/PR:H/UI:N/S:U/C:N/I:N/A:L` | **1.9 (Low)** (latent: a zero polynomial needs an empty encoder slot, which no V1 message produces; only a crafted blob reaches it) | CWE-754 (Improper Check for Unusual Conditions) |
| SPQR-DESER-encaps2-endian | `encaps2` endianness heuristic → wrong shared secret | `AV:L/AC:H/PR:H/UI:N/S:U/C:N/I:L/A:H` | **4.7 (Medium)** | CWE-440 (Expected Behavior Violation) |
| SPQR-DESER-ct2sent-assert | `Ct2Sent::recv_next_epoch` asserts instead of erroring | `AV:L/AC:H/PR:H/UI:N/S:U/C:N/I:N/A:H` | **4.1 (Medium)** | CWE-617 |
| SPQR-DESER-send-assert | `send` panics on `assert!(key.is_none())` | `AV:L/AC:H/PR:H/UI:N/S:U/C:N/I:N/A:H` | **4.1 (Medium)** | CWE-617 |
| SPQR-DESER-authkey-length | `auth_key` of any length (incl. empty) accepted as chain + authenticator root | `AV:L/AC:L/PR:H/UI:N/S:U/C:H/I:H/A:N` | **6.0 (Medium)**; AV:N → **6.5** where state is synced over a network channel. Once a weak key is in `vn.auth_key`, a *network* attacker can derive epoch-0 message keys and forge header/ciphertext MACs: chained `AV:N/AC:L/PR:N/UI:N/S:U/C:H/I:H/A:N` → **9.1 (Critical)** for that session | CWE-1240 (Use of a Cryptographic Primitive with a Risky Implementation) / CWE-20 / CWE-321 |
| SPQR-DESER-minversion-cast | `recv` truncates `vn.min_version` (`as u8`) while `current_version` validates it | `AV:L/AC:L/PR:H/UI:N/S:U/C:N/I:L/A:H` | **5.1 (Medium)** (`min_version = -1` → every message `MinimumVersion`; `256` → silent V0 downgrade window that `send` believes closed) | CWE-197 (Numeric Truncation) / CWE-436 |

SPQR-DESER-authkey-length is scored for the *standalone* crate: `initial_state` is a public API that documents no
key-length requirement, and the persisted `vn.auth_key` is re-read on every call until
negotiation ends. For embedders that always pass a fresh 32-byte key (libsignal does) only the
blob vector applies. The chained Critical score is the consequence, not the entry point, and
is noted to show why `InvalidParams` should be enforced at construction.

### Part IV — cryptographic hygiene

| ID | Finding | CVSS v3.1 vector | Base | CWE |
|---|---|---|---|---|
| SPQR-CRYPT-compare-length | `compare` truncates/panics on unequal lengths | latent: no vector today (all call sites pin lengths). If a short `expected_mac` ever reaches it (e.g. via SPQR-DESER-poly-points): `AV:N/AC:H/PR:N/UI:N/S:U/C:N/I:H/A:N` → **5.9 (Medium)** potential | CWE-697 (Incorrect Comparison) / CWE-125 (Out-of-bounds Read) |
| SPQR-CRYPT-ratchet-before-verify | Ratchet-before-verify in `recv_ct2`; flattened errors | *not scored* (no reachable impact in current code; hardening/refactor hazard) | — | CWE-696 (Incorrect Behavior Order) |
| SPQR-CRYPT-no-zeroise | No zeroisation of retired secrets | `AV:L/AC:H/PR:H/UI:N/S:U/C:H/I:N/A:N` | **4.1 (Medium)** (needs local memory disclosure as a chained primitive) | CWE-226 / CWE-459 (Sensitive Information in Released Memory) |

### Part V — verification soundness and scope

| ID | Finding | Score | CWE |
|---|---|---|---|
| SPQR-SPEC-pk-hash-order | `validate_pk_bytes` model vs. §2.5 hash-order mismatch | *not scored* — a defect in the trusted verification base, not a runtime vulnerability. If the *implementation* turned out to be the wrong one, impact would be a broken binding of `ek` to the header (potentially High); currently undetermined. | CWE-1068 |
| SPQR-SPEC-future-epoch-err | Future-epoch messages return `Err` instead of being dropped | `AV:N/AC:L/PR:N/UI:N/S:U/C:N/I:N/A:L` → **5.3 (Medium)** only for embedders that tear down a session on `Err`; otherwise negligible | CWE-754 |
| SPQR-SPEC-rollback-scope | Epoch-uniqueness excludes rollback/replayed state; API takes state by reference | caller-induced: `AV:L/AC:H/PR:H/UI:N/S:U/C:H/I:N/A:N` → **4.1 (Medium)** where an embedder replays stored state (duplicate `EpochSecret` → key reuse) | CWE-323 (Key/Nonce Reuse) |
| SPQR-SPEC-liveness | Liveness unproved; emitting calls only conditionally total | *not scored* (verification-scope note, no vector) | — |


## Summary

| Band | Findings |
|---|---|
| **High (7.0–8.9)** | **SPQR-AUTH-chain-advance-persist (8.2)**, SPQR-AUTH-epoch-advance (7.5), SPQR-AUTH-chunk-poison (7.5), **SPQR-AUTH-a-encoder-drop (7.5)**, **SPQR-AUTH-b-encoder-drop (7.5)** — standalone crate only; reduced to negligible against a network-only attacker by libsignal's MAC-before-persist ordering, but **not** against an authenticated-but-malicious peer, and (for SPQR-AUTH-chain-advance-persist) not for any embedder that commits `Recv.state` before its own MAC check. |
| **Medium (4.0–6.9)** | **SPQR-DESER-authkey-length (6.0/6.5)**, SPQR-AUTH-ct1ack-accepted (5.9), SPQR-AUTH-late-ek-chunk (5.9), **SPQR-AUTH-v1-lockin (5.9)**, SPQR-AUTH-v0-downgrade (4.8), SPQR-AUTH-index0-nokey (5.3), SPQR-AUTH-index-cpu-amp (5.3), SPQR-ARITH-ooo-u32-overflow (4.8/6.5), SPQR-ARITH-params-unchecked (4.4), SPQR-ARITH-trimsize-usize32 (4.1), SPQR-ARITH-epochidx-trunc32 (4.1), SPQR-DESER-chain-frompb (4.4), SPQR-DESER-auth-keylen (4.4), SPQR-DESER-epoch-zero (4.4), SPQR-DESER-epoch-max (4.7), SPQR-DESER-poly-points (5.1), SPQR-DESER-is-complete (4.4), SPQR-DESER-encaps2-endian (4.7), SPQR-DESER-ct2sent-assert (4.1), SPQR-DESER-send-assert (4.1), SPQR-CRYPT-no-zeroise (4.1), SPQR-SPEC-future-epoch-err (5.3), SPQR-SPEC-rollback-scope (4.1), **SPQR-DESER-minversion-cast (5.1)**; SPQR-CRYPT-compare-length (5.9 potential). |
| **Low (0.1–3.9)** | SPQR-AUTH-wire-noninjective (3.7), SPQR-ARITH-encoder-idx-u16 (1.9), SPQR-DESER-zero-poly-roundtrip (1.9). |
| **Not scored** | SPQR-ARITH-keyhistory-invariant, SPQR-CRYPT-ratchet-before-verify, SPQR-SPEC-pk-hash-order, SPQR-SPEC-liveness (spec/annotation/scope defects without their own runtime vector). |

No finding reaches Critical as an *entry point*: none yields key recovery, decryption, or
message forgery against the deployed Signal configuration. (SPQR-DESER-authkey-length reaches 9.1 only as a chained
consequence once a weak `auth_key` has been accepted; the entry vector is local/blob.) The High
band is availability (protocol deadlock: SPQR-AUTH-epoch-advance, SPQR-AUTH-chunk-poison, SPQR-AUTH-a-encoder-drop, SPQR-AUTH-b-encoder-drop) and persisted key-chain damage
(SPQR-AUTH-chain-advance-persist) for embedders without a MAC-before-`recv` discipline; the Medium band is dominated by
panic/DoS-from-blob items whose fixes are pending in upstream PR #18
(signalapp/SparsePostQuantumRatchet) and by the pre-authentication CPU amplification (SPQR-AUTH-index-cpu-amp),
which is the one network-reachable item libsignal's ordering does **not** mitigate.

The second-pass items SPQR-AUTH-a-encoder-drop/SPQR-AUTH-b-encoder-drop/SPQR-AUTH-chain-advance-persist raise the count of network-reachable High findings from two
to five. All five share one root cause — `recv` commits irreversible state changes (encoder
drops, chain advance) on inputs that the crate has not authenticated — and would be closed
together by a single API change: make `recv` take (or return and require) an authentication
verdict before any state that cannot be regenerated is discarded or persisted.

Scores are for the crate at the pinned commit `06959b4` (v1.6.0, the current upstream tip;
`src/` in this repository is unchanged through local commit `17b3b5d3`, so the scores remain
valid after the Lean-side refactors noted in `defect.md`, Method, revision 4);
re-score after the PR #18 defensive checks land, which should eliminate or downgrade the `SPQR-ARITH-*` items (except
SPQR-ARITH-keyhistory-invariant) and SPQR-DESER-chain-frompb, SPQR-DESER-epoch-zero,
SPQR-DESER-epoch-max, SPQR-DESER-poly-points, SPQR-DESER-encaps2-endian and
SPQR-DESER-ct2sent-assert.

## Notes on method

* Vectors follow the CVSS v3.1 specification and were computed with the standard base-score
  equations (verified programmatically for every vector in this file); representative values:
  `AV:N/AC:L/PR:N/UI:N/S:U/C:N/I:N/A:H` = 7.5, `AV:N/AC:H/PR:N/UI:N/S:U/C:N/I:N/A:H` = 5.9,
  `AV:L/AC:L/PR:H/UI:N/S:U/C:N/I:N/A:H` = 4.4, `AV:N/AC:L/PR:N/UI:N/S:U/C:N/I:L/A:N` = 5.3,
  `AV:N/AC:H/PR:N/UI:N/S:U/C:N/I:L/A:N` = 3.7, `AV:N/AC:L/PR:N/UI:N/S:U/C:N/I:L/A:H` = 8.2,
  `AV:L/AC:L/PR:H/UI:N/S:U/C:H/I:H/A:N` = 6.0.
* Scope is `S:U` throughout: the ratchet and its host run in one security authority; no
  finding crosses a privilege boundary by itself.
* CVSS v4.0 would not change the ordering materially; v3.1 was chosen because it is what
  NVD, GitHub advisories and most coordinated-disclosure programs still expect.
* The libsignal "Adjusted" column is informal environmental guidance, not a computed
  Environmental score, because the mitigation (MAC-ordering plus clone-and-drop) is a property
  of the embedder's code, not of a CVSS environmental metric.
