# Code vs. Spec: SPQR `src/` ↔ 2025-2267.pdf ↔ mlkembraid.pdf

## Short answer

- `mlkembraid.pdf` is the **direct specification** of `src/`. The Rust code is a 1-to-1 implementation of the state machine in §2.5 of mlkembraid.
- `2025-2267.pdf` Fig. 16 (Opp-UniKEM-CKA) is the **academic abstraction** that mlkembraid concretizes. The states/transitions in `src/v1/chunked/states.rs` are a *refinement* of Fig. 16 — they handle ML-KEM's incremental structure that Fig. 16's generic offline-online KEM glosses over.
- `2025-2267.pdf` Fig. 2 (SCKA→SM compiler) corresponds to `src/lib.rs` + `src/chain.rs`, which wrap the SCKA core (the Fig. 16 / mlkembraid state machine) into a secure-messaging API.

## Layered correspondence

### Layer 1 — Abstract SCKA from offline-online KEM (Fig. 16, §4.1 / App. D of 2025-2267)

Fig. 16 assumes `KEM = (KeyGen, Enc.Off, Enc.On, Dec)` where:
- `Enc.Off → (st_ct, ct_0)` (offline, no `ek` needed)
- `Enc.On(st_ct, ek) → ct_1` (online, completes encapsulation)

Encapsulation key is just `ek`, ciphertext is `(ct_0, ct_1)`. A's states track `(dk_A, ek_A, ct_0, ack)`; B's track `(ek_A, ct=(ct_0,ct_1), st_ct, ack)`. The state machine has only the implicit phases "first message of epoch" / "ek_A not yet recovered" / "ct_1 not yet recovered" / "ek/ct fully delivered".

### Layer 2 — ML-KEM Braid (mlkembraid.pdf)

Specializes Fig. 16 to ML-KEM-768. Key change: ML-KEM has an *incremental* interface:
- `KeyGen → (dk, ek_seed, ek_vector)`
- `Encaps1(ek_header) → (es, ct1, ss)`
- `Encaps2(es, ek_vector) → ct2`

where `ek_header = ek_seed || hek` and `hek = SHA3-256(ek_seed || ek_vector)` (needed for FO key-binding, §1.2.1). `ct1` is the ciphertext computable from just the header; `ct2` is the reconciliation message that needs the full `ek_vector`.

So Fig. 16's two-piece `(ek, (ct_0, ct_1))` becomes a three-piece `(header, ek_vector, (ct1, ct2))` — which forces an extra round-section. Hence the 11 states of the code (§2.5):

| Side A (send_ek)                          | Side B (send_ct)                                       |
|-------------------------------------------|--------------------------------------------------------|
| `KeysUnsampled` → sample `(dk, ek_seed, ek_vector)` | `NoHeaderReceived`                              |
| `KeysSampled` (sending `Hdr` chunks)      | `HeaderReceived` (got header → can run `Encaps1`)      |
| `HeaderSent` (now sending `Ek` chunks)    | `Ct1Sampled` (sending `Ct1` chunks)                    |
| `Ct1Received`                             | `EkReceivedCt1Sampled` / `Ct1Acknowledged`             |
| `EkSentCt1Received`                       | `Ct2Sampled` (sending `Ct2` chunks)                    |

This is exactly `pub enum States { ... }` in `src/v1/chunked/states.rs:16`.

### Layer 3 — Concrete Rust implementation (`src/`)

- `src/v1/chunked/states.rs` — top-level state-machine dispatch matching mlkembraid Figure 1 (state diagram) and the `Send`/`Receive` pseudocode per state.
- `src/v1/chunked/send_ek.rs` and `src/v1/chunked/send_ct.rs` — per-state transition logic (one file per role: A vs B).
- `src/v1/chunked/send_ek/serialize.rs`, `.../send_ct/serialize.rs`, `.../states/serialize.rs` — message encoding (`MessagePayload::{None, Hdr, Ek, EkCt1Ack, Ct1Ack, Ct1, Ct2}` matches §2.3 verbatim).
- `src/incremental_mlkem768.rs` — the incremental ML-KEM interface (`generate`, `encaps1`, `encaps2`, `decapsulate`) with sizes `HEADER_SIZE=64, EK_SIZE=1152, CT1_SIZE=960, CT2_SIZE=128` matching the ML-KEM-768 column of mlkembraid §2.2.
- `src/encoding/` (`polynomial.rs`, `round_robin.rs`, `gf.rs`) — Reed-Solomon erasure code over GF(2¹⁶), as recommended in mlkembraid §2.2 ("Encode/Decode").
- `src/authenticator.rs` — Ratcheted Authenticator (mlkembraid §2.4): `update` ≡ `Authenticator.Update` with HKDF info `"Signal_PQCKA_V1_MLKEM768:Authenticator Update"`; `mac_hdr`/`mac_ct` use `:ekheader`/`:ciphertext` exactly as in the spec. **Note:** this internal MAC is mlkembraid-specific — Fig. 16 of 2025-2267 has no internal authentication and instead relies on the AEAD layer (mlkembraid §3.3 explicitly discusses this as an extension).
- `src/chain.rs` + `src/lib.rs::send/recv` — the SM-side wrapper. This is the SCKA→SM compiler of **Fig. 2** of 2025-2267.pdf:
  - `Mixin-CKA-Keys` ≈ `chain.add_epoch(epoch_secret)` in `lib.rs:298`.
  - `Expand-Chain` / `KS[t]` / `KR[t]` ≈ `chain.send_key` / `chain.recv_key` in `lib.rs:300, 435`.
  - `K_root`/`K_CKA` chain split is implemented inside `chain.rs`.

## Caveats / where the code goes beyond the papers

1. **Version negotiation** (`Version::V0`/`V1`, `min_version`, `init_inner`, the `version_negotiation` field of `pqrpb::PqRatchetState`) — pure deployment plumbing, not in either PDF.
2. **`incremental_mlkem768.rs::potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275`** — workaround for a libcrux serialization bug, not in the spec.
3. **Internal Ratcheted Authenticator** — present in mlkembraid §2.4, *not* in 2025-2267 Fig. 16 (which leaves authentication to the outer SM/AEAD).
4. **`v1/unchunked/`** — a non-chunked variant; the SCKA paper considers only chunked Opp-UniKEM-CKA, so this is an extra simplified mode.
5. **`hax_lib::*` annotations** — for hax extraction to F\*/Lean, since this repo is the verification project (`Spqr.lean`, `lakefile.toml`, `proofs/`).

## Bottom line

If you want to verify the code matches a paper, **compare line-by-line against mlkembraid.pdf §2.5**, not against Fig. 16 of 2025-2267. The states, message types, MAC labels, and HKDF info strings are word-for-word identical. Then read 2025-2267 Fig. 16 + Fig. 2 to understand *why* the protocol is shaped this way (the SCKA framework, opportunistic sending, the SCKA→SM compiler, and the security model in terms of vulnerable epoch sets).
