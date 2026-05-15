# Layer 1: SCKA Interface (§1.1, §3.8)

> See [README.md](README.md) for extraction status, axiom conventions, and
> the master cross-reference table.

This file covers the five abstract correctness goals of the **Sparse Continuous
Key Agreement** interface (§1.1 of `mlkembraid.pdf`) and the chain-level
invariants that support them. It also covers the epoch-representation
recommendation from §3.8.

The SCKA goals are *stated* at the top level but *proved via* the state-machine
and chain layers. Cross-references to the protocol-layer proofs in
[3_protocol.md](3_protocol.md) are noted where relevant.

---

## §1.1 — The five SCKA correctness properties

### PROP-1: Session Key Consistency [CORRESPONDENCE]

**Source:** `production-test` + `spec-mlkembraid` (§1.1).

*If both parties output keys `(ep, k)` and `(ep, k')` for the same epoch,
then `k = k'`.*

| Aspect | Assessment |
|--------|------------|
| **Difficulty** | Hard |
| **At v1 layer** | ⚠️ **FEASIBLE** — `States.send` and `States.recv` are extracted. Agreement can be stated at the `EpochSecret` layer: when both parties process a completed epoch, their `EpochSecret.secret` fields are equal. |
| **At API level** | 🚫 **BLOCKED** — `lib.rs` `send`/`recv`/`initial_state` not extracted. |
| **Key axioms** | KEM roundtrip (PROP-3), HKDF determinism, `encaps2` roundtrip |
| **Estimated effort** | 5–7 days (v1 layer) |

### PROP-21: Per-Participant Epoch Uniqueness [STATE INVARIANT] ✅ PROVED

**Source:** `spec-mlkembraid` (§1.1).

*Each party emits at most one key per epoch.*

This reduces to PROP-9 (epoch monotonicity ensures `add_epoch` cannot process
the same epoch twice) plus the structural fact that only two transitions
emit a key. The structural fact is proved as PROP-21 in
`Spqr/Specs/States/Send.lean`: for all 11 `States` variants, `Send.key` is
`Some _` only for `HeaderReceived`, and `None` for the other 10.

**Proof file:** `Spqr/Specs/States/Send.lean`

| Variant | Theorem | key |
|---------|---------|-----|
| KeysUnsampled | `send_KeysUnsampled_key_none` | `none` |
| KeysSampled | `send_KeysSampled_key_none` | `none` |
| HeaderSent | `send_HeaderSent_key_none` | `none` |
| Ct1Received | `send_Ct1Received_key_none` | `none` |
| EkSentCt1Received | `send_EkSentCt1Received_ct1_ack` | `none` |
| NoHeaderReceived | `send_NoHeaderReceived_noop` | `none` |
| HeaderReceived | `send_HeaderReceived_key_some` | `some _` |
| Ct1Sampled | `send_Ct1Sampled_key_none` | `none` |
| EkReceivedCt1Sampled | `send_EkReceivedCt1Sampled_key_none` | `none` |
| Ct1Acknowledged | `send_Ct1Acknowledged_noop` | `none` |
| Ct2Sampled | `send_Ct2Sampled_key_none` | `none` |

### PROP-22: Epoch Agreement [CORRESPONDENCE]

**Source:** `spec-mlkembraid` (§1.1).

*`sending_epoch` from `Send()` equals `receiving_epoch` from the corresponding
`Receive()`.*

**Statement (two parts):**

**PROP-22a** — *send output reflects sender state*: for every `States` variant `s`,
`States.send s = ok r → r.msg.epoch = s.epoch`.

**PROP-22b** — *recv success epoch discipline*: for every `States` variant `s`
and message `msg`, whenever `recv` succeeds:
`States.recv s msg = ok r → msg.epoch ≤ s.epoch ∨ (s = Ct2Sampled _ ∧ msg.epoch = s.epoch + 1)`.

Together these give epoch agreement: if Alice sends from state `s_A` and Bob
receives from `s_B`, then `msg.epoch = s_A.epoch` (by 22a), and `s_B`'s epoch
is consistent with that value (by 22b).

| Aspect | Assessment |
|--------|------------|
| **Difficulty** | Easy-Medium (structural case-split on 11 variants) |
| **Dependencies** | None (no opaque functions on this path) |
| **Status** | ⚠️ **FEASIBLE** |
| **Estimated effort** | 2 days for 22a + 22b combined |

### PROP-23: Sender/Receiver Epoch Knowledge [HISTORY]

**Source:** `spec-mlkembraid` (§1.1).

*When `Send` returns `sending_epoch = ep`, the sender has emitted keys for
all epochs ≤ ep. Symmetrically for `Receive`.*

| Aspect | Assessment |
|--------|------------|
| **Difficulty** | Medium-Hard |
| **Lean encoding** | Requires defining a `has_epoch_secret` predicate over the chain's link structure. |
| **Dependencies** | PROP-9, PROP-29 (chain structural invariant) |
| **Status** | ⚠️ **FEASIBLE** |
| **Estimated effort** | 3–4 days |

---

## Chain invariants supporting SCKA

### PROP-9: Epoch Monotonicity [STATE INVARIANT] ✅ PROVED

**Source:** `production-code` + `production-test`.

*Given precondition `es.epoch = c.current_epoch + 1 ∧ c.current_epoch < U64.max`,
the post-state satisfies `c'.current_epoch = es.epoch`.*

This subsumes the epoch-overflow safety obligation from §3.8: the
`h_no_overflow` precondition is exactly the spec's §3.8 condition.

**Proof file:** `Spqr/Specs/Chain/AddEpoch.lean`

```lean
@[step]
theorem chain.Chain.add_epoch_spec
  (self : chain.Chain) (epoch_secret : EpochSecret)
  (h_no_overflow : self.current_epoch.val + 1 ≤ U64.max)
  (h_epoch : epoch_secret.epoch.val = self.current_epoch.val + 1) :
    chain.Chain.add_epoch self epoch_secret
      ⦃ c' => c'.current_epoch = epoch_secret.epoch ⦄ := by
  unfold chain.Chain.add_epoch
  step*
```

The proof also includes helper specs for `Direction.switch`,
`KeyHistory.KEY_SIZE`, `KeyHistory.new`, `ChainEpochDirection.new`,
and `Chain.ced_for_direction`.

### PROP-14: Send Epoch Cannot Decrease [STATE INVARIANT] ✅ PROVED

**Source:** `production-code`.

*`send_key(epoch)` returns `Error::SendKeyEpochDecreased` if `epoch < self.send_epoch`.*

**Proof file:** `Spqr/Specs/Chain/SendKey.lean`

```lean
@[step]
theorem chain.Chain.send_key_epoch_guard
  (self : chain.Chain) (epoch : Std.U64)
  (h : epoch < self.send_epoch) :
    chain.Chain.send_key self epoch
      ⦃ r => r.1 = core.result.Result.Err
               (Error.SendKeyEpochDecreased self.send_epoch epoch)
             ∧ r.2 = self ⦄ := by
  unfold chain.Chain.send_key
  simp only [h, ite_true]
  simp [WP.spec, WP.theta, WP.wp_return]
```

### PROP-17: Key Jump Limit [CONDITIONAL BEHAVIORAL SPEC] ✅ PROVED

**Source:** `production-code`.

*`ChainEpochDirection::key(at, params)` returns `Err(Error::KeyJump(ctr, at))`
when `at > ctr` **and** `at - ctr > max_jump`.*

**Proof file:** `Spqr/Specs/Chain/Key.lean`

The theorem requires both `h_gt : at1 > self.ctr` (the unsigned subtraction
is well-defined only on the Greater branch) and the jump-size hypothesis
covering both branches of `max_jump_or_default`.

### PROP-17b: Key Already Requested [CONDITIONAL BEHAVIORAL SPEC] ✅ PROVED

**Source:** `production-code`.

*`ChainEpochDirection::key(at, params)` returns `Err(Error::KeyAlreadyRequested(at))`
when `at = ctr`.*

**Proof file:** `Spqr/Specs/Chain/Key.lean`

Together PROP-17 and PROP-17b complete the Greater/Equal case analysis for
`ChainEpochDirection::key`. The Less case delegates to `prev.get` (out-of-order
key lookup).

### PROP-29: `epoch_idx` Correspondence [STATE INVARIANT]

**Source:** `production-code` + `lean-specific`.

*`epoch_idx` is the linchpin between numeric epochs and `links` positions.
Every `send_key`/`recv_key` call goes through it.*

```lean
theorem epoch_idx_spec (c : chain.Chain) (epoch : Epoch) :
    chain.Chain.epoch_idx c epoch ⦃ r =>
      match r with
      | Ok i =>
          epoch ≤ c.current_epoch
          ∧ c.current_epoch - epoch < c.links.length
          ∧ i = c.links.length - 1 - (c.current_epoch - epoch)
      | Err (.EpochOutOfRange e) =>
          e = epoch ∧ (epoch > c.current_epoch
            ∨ c.current_epoch - epoch ≥ c.links.length)
      | _ => False ⦄
```

| Aspect | Assessment |
|--------|------------|
| **Status** | ⚠️ **FEASIBLE** |
| **Estimated effort** | 1 day |

### PROP-10: Structural Key Erasure [HISTORY / ERASURE]

**Source:** `production-code` + `production-test`.

*Old chain keys are erased after epoch advancement; this is the structural half
of forward secrecy only.* The cryptographic non-derivability aspect (HKDF
one-wayness) is out of scope.

| Aspect | Assessment |
|--------|------------|
| **Difficulty** | Medium — requires VecDeque `pop_front` reasoning |
| **Dependencies** | No opaque functions in the deletion path |
| **Status** | ⚠️ **FEASIBLE** |
| **Estimated effort** | 2–3 days |

### PROP-12a: KeyHistory Length Invariant [STATE INVARIANT]

**Source:** `production-code`.

*`KeyHistory.data.length % KEY_SIZE == 0` is preserved by `add`, `remove`, `gc`.*
(`KEY_SIZE = 4 + 32 = 36`, `chain.rs:130`.)

| Aspect | Assessment |
|--------|------------|
| **Status** | ⚠️ **FEASIBLE** |
| **Estimated effort** | 1 day |

### PROP-12b: KeyHistory Get-After-Add Roundtrip [CONDITIONAL BEHAVIORAL SPEC]

**Source:** `production-code`.

*`KeyHistory.get(KeyHistory.add(kh, k, v), k) = ok (some v)` for fresh `k`.*

| Aspect | Assessment |
|--------|------------|
| **Difficulty** | Hard — byte-level indexing, linear-scan loop in `get_loop` |
| **Previous status** | Was **BLOCKED** — `KeyHistory.get` and `KeyHistory.gc` were believed opaque |
| **Current status** | ⚠️ **FEASIBLE** — both are full `def`s in `Funs.lean` (extracted despite `#[hax_lib::opaque]` Rust annotation; not in `aeneas-config.yml` `opaque:` list) |
| **Estimated effort** | 3 days |

---

## §3.8 — Epoch Representation

The spec recommends 64-bit epoch counters and notes wraparound risk for
narrower types. This is covered by PROP-9's `h_no_overflow` precondition:
the extracted `U64` arithmetic in Aeneas only succeeds when
`current_epoch < U64.max`.
