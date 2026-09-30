/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Lacramioara Astefanoaei
-/
import Spqr.Specs.V1.Chunked.States.EpochUniqueness.KeyFloor

/-! # Per-participant epoch uniqueness

"Each party outputs at most one key per epoch" ([ML-KEM Braid] §1.1, p. 4; [SCKA] Fig. 1,
`Send-P` line 14 and `Receive-P` line 7, and App. B.1 *Unique epochs*), for the chunked
`States` machine.

The claim is about one party's run. A *run* from a state `σ₀` is a finite sequence of calls
`σ₀ →[o₁] σ₁ →[o₂] ⋯ →[oₙ] σₙ` (`n ≥ 0`), where each step `σᵢ₋₁ →[oᵢ] σᵢ` is either
`Send(σᵢ₋₁, rngᵢ)` or `Receive(σᵢ₋₁, msgᵢ)`, that call succeeds, and it returns the new state
`σᵢ` and `output_key = oᵢ`, which is either `None` or a pair `(eᵢ, ssᵢ)` of an epoch and a
shared secret. Here `σ₀`, the randomness `rngᵢ` and the messages `msgᵢ` are arbitrary. Then
`eᵢ ≠ eⱼ` for all `i ≠ j` such that `oᵢ` and `oⱼ` are both not `None`.

## Main results

* `epochs_nodup`: the keys a run emits carry pairwise distinct epochs. This is the claim above.
* `epochs_disjoint`: two consecutive runs emit keys at disjoint sets of epochs.
* `epochs_strictly_increase`: the epochs of the keys a run emits strictly increase.
* `epochs_from_init_a`, `epochs_from_init_b`: a run from an initial state emits its `m` keys at
  epochs `1, 2, …, m`.
* `emitted_epochs_below_keyFloor`: a run from a state with `keyFloor = 1`, such as either initial
  state, has emitted exactly the epochs `1, …, keyFloor s' - 1`, where `s'` is where it ends.

The per-call case analysis and the induction over runs they rest on are in
`Spqr.Specs.V1.Chunked.States.EpochUniqueness.KeyFloor`, together with the structural facts:
`send_key_epoch`, `recv_key_epoch` and their converses `send_HeaderReceived_key_isSome`,
`recv_EkSentCt1Received_key_isSome` say that a call emits a key exactly in transitions (7)
and (5).

The result meant to be built on is `epochs_consecutive` in that module, with its one-step form
`Step.keyFloor_step`. `lib.rs` passes every emitted key to `Chain::add_epoch`
(`src/lib.rs:298`, `:430`), which asserts that the key's epoch is `current_epoch + 1`
(`src/chain.rs:355`); `add_epoch_spec` takes this as its premise `h_epoch`. If
`chain.current_epoch + 1 = keyFloor s` before a step, `Step.keyFloor_step` discharges `h_epoch`
for the key the step emits and restores the equation afterwards. Keeping a chain in step with
the state machine through `lib.rs` is not proved here.

## Why it holds

We use the notation of [ML-KEM Braid] §2.5. Every state `σ` has a field `σ.epoch`.
Transitions are numbered as in Fig. 1 (p. 10) and marked `# Transition (n)` in the
pseudocode. The eleven states fall into two groups:

* *pending*: `KeysUnsampled`, `KeysSampled`, `HeaderSent`, `Ct1Received`,
  `EkSentCt1Received`, `NoHeaderReceived`, `HeaderReceived`. The key for `σ.epoch` has
  not been output yet.
* *emitted*: `Ct1Sampled`, `EkReceivedCt1Sampled`, `Ct1Acknowledged`, `Ct2Sampled`.
  These are entered through transition (7), which has already output the key for
  `σ.epoch`.

Let `next(σ)` be the epoch of the next key `σ` can output. Then `next(σ) = σ.epoch` if `σ`
is pending, and `next(σ) = σ.epoch + 1` if `σ` is emitted. In Lean, `next` is `keyFloor`.

The diagram below is Fig. 1 with its numbered transitions, each labeled `S` (`Send`) or
`R` (`Receive`), and annotated where it outputs a key or changes the epoch; `e` is the
epoch before the transition. Calls that make no transition are not drawn.

```text
┌─→ KeysUnsampled                                             ┐
│     │ (1) S                                                 │
│     ↓                                                       │
│   KeysSampled                                               │
│     │ (2) R                                                 │
│     ↓                                                       │
│   HeaderSent                                                │
│     │ (3) R                                                 │
│     ↓                                                       │
│   Ct1Received                                               │  pending:
│     │ (4) R                                                 │  next(σ) = σ.epoch
│     ↓                                                       │
│   EkSentCt1Received                                         │
│     │ (5) R, last Ct2 chunk: outputs (e, ss),               │
│     │     epoch e → e + 1                                   │
│     ↓                                                       │
│   NoHeaderReceived                                          │
│     │ (6) R                                                 │
│     ↓                                                       │
│   HeaderReceived                                            ┘
│     │ (7) S: outputs (e, ss)
│     ↓
│   Ct1Sampled ─────────┬─── (10) R ──→ EkReceivedCt1Sampled  ┐
│     │                 │                         │           │
│   (8) R             (9) R                    (12) R         │  emitted:
│     ↓                 │                         │           │  next(σ) = σ.epoch + 1
│   Ct1Acknowledged     │                         │           │
│     │ (11) R          │                         │           │
│     ↓                 │                         │           │
│   Ct2Sampled ←────────┴─────────────────────────┘           ┘
│     │ (13) R, message of epoch e + 1:
│     │      epoch e → e + 1
└─────┘
```

The pseudocode gives three facts:

* Only transitions (5) and (7) output a key. Transition (7) (*HeaderReceived.Send*,
  p. 18) goes from `HeaderReceived` at epoch `e` to `Ct1Sampled` at `e` and outputs
  `(e, ss)`. Transition (5) (*EkSentCt1Received.Receive*, p. 16, on the last `Ct2` chunk)
  goes from `EkSentCt1Received` at `e` to `NoHeaderReceived` at `e + 1` and outputs
  `(e, ss)`. In both cases the key is at `next(σ) = e`, and `next` goes from `e` to
  `e + 1`.
* Only transitions (5) and (13) change the epoch. Transition (13)
  (*Ct2Sampled.Receive*, p. 23) goes from `Ct2Sampled` at `e` to `KeysUnsampled` at
  `e + 1`, so `next` stays at `e + 1`.
* Every other transition, and every call that makes no transition, keeps both the epoch
  and the group, so `next` does not change.

So every call `σ →[o] σ'` satisfies one of:

* `o = None` and `next(σ') = next(σ)`, or
* `o = (e, ss)` with `e = next(σ)` and `next(σ') = next(σ) + 1`.

Now take a run `σ₀ →[o₁] ⋯ →[oₙ] σₙ` and let `i₁ < ⋯ < iₘ` be the steps with `oᵢ ≠ None`.
By induction on `n`, `e_{iⱼ} = next(σ₀) + (j − 1)` for `j = 1, …, m`, and
`next(σₙ) = next(σ₀) + m`. So the epochs of the output keys strictly increase along the
run, and in particular are pairwise distinct.

For a whole session this gives the epochs exactly. `InitAlice` and `InitBob`
([ML-KEM Braid] §2.6, p. 23; `States.init_a`, `States.init_b`) return `KeysUnsampled` and
`NoHeaderReceived` at epoch 1, both pending, so `next(σ₀) = 1` and the keys of a session are
at epochs `1, 2, …, m`.

## Hypotheses and trusted base

Every result is conditional on each call returning `Ok` (see `Step`). The extraction
implements epoch increments as checked additions. The results therefore hold for the crate
built with overflow checks, or for a release run in which no call overflows
([ML-KEM Braid] §3.8, p. 28).

The results are safety facts about successful calls; none of them shows that a call emitting a
key can succeed. Both emitting transitions go through opaque stubs with no success guarantee
(`encapsulate1` and the map iterator on the send side; `decoded_message`, decapsulation and the
MAC check on the recv side), so a machine whose emitting calls always fail satisfies every result
here. A key cannot be dropped silently, though: a successful emitting transition that returned
no key would raise `keyFloor`, which the no-key case of `Step.keyFloor_step` forbids.

`#print axioms epochs_nodup` includes `sorryAx`, as does every declaration stated over `Step`
or `Run`, `Run.append` and their recursors included. It comes from one `sorry`, the
extraction's map-iterator stub `next := sorry` (aeneas#1043). The chunk encoders of all eight
send callees reach it, so `States.send` does too. The `Step.send` constructor names
`States.send` in its type, so every result about steps or runs inherits it. The send proofs use
no fact about the iterator's output: they read the epoch off the state built around the
encoder. The recv lemmas, `recv_step` and `recv_key_epoch` among them, are free of `sorryAx`.

## Scope

The results concern only the `EpochSecret`s emitted along one threaded run of the `States`
machine. They do not cover:
* the message keys that `lib.rs` derives from these secrets through the chain;
* states serialized and restored between calls;
* a party rolled back to an older stored state.

## References

* [ML-KEM Braid] R. Schmidt, *The ML-KEM Braid Protocol*, Rev. 1, last updated 2025-09-26.
  <https://signal.org/docs/specifications/mlkembraid/mlkembraid.pdf>
* [SCKA] B. Auerbach, Y. Dodis, D. Jost, S. Katsumata, R. Schmidt, *How to Compare
  Bandwidth Constrained Two-Party Secure Messaging Protocols: A Quest for A More Efficient
  and Secure Post-Quantum Protocol*, IACR ePrint 2025/2267.
  <https://eprint.iacr.org/2025/2267>

**Source**: spqr/src/v1/chunked/states.rs:203-220, spqr/src/v1/chunked/states.rs:361-368 -/

open Aeneas Aeneas.Std Result

namespace spqr.v1.chunked.states

variable {s s' : States} {ks : List EpochSecret}

/-- Each party outputs at most one key per epoch: the keys a run emits carry pairwise
distinct epochs. This is ML-KEM Braid spec §1.1, p. 4, and SCKA Fig. 1, `Send-P` line 14
and `Receive-P` line 7. -/
theorem epochs_nodup (h : Run s s' ks) : (ks.map (·.epoch)).Nodup := by
  apply List.Nodup.of_map (fun e : Std.U64 => e.val)
  rw [List.map_map]
  change (ks.map (·.epoch.val)).Nodup
  rw [(epochs_consecutive h).1]
  exact List.nodup_range'

/-- If a run from `s₀` to `s` is followed by a run from `s` to `s'`, no epoch is carried both by
a key of the first run and by a key of the second. -/
theorem epochs_disjoint {s₀ : States} {ks₀ : List EpochSecret} (h₁ : Run s₀ s ks₀)
    (h₂ : Run s s' ks) : (ks₀.map (·.epoch)).Disjoint (ks.map (·.epoch)) := by
  have := epochs_nodup (h₁.append h₂)
  rw [List.map_append] at this
  exact List.disjoint_of_nodup_append this

/-- The epochs of the keys a run emits strictly increase. -/
theorem epochs_strictly_increase (h : Run s s' ks) :
    (ks.map (·.epoch.val)).Pairwise (· < ·) := by
  rw [(epochs_consecutive h).1]
  exact List.pairwise_lt_range'

/-- A run from the state `init_a` returns emits its `n` keys at epochs `1, 2, …, n`. -/
theorem epochs_from_init_a {k : Slice Std.U8} {s₀ : States} (hi : States.init_a k = ok s₀)
    (h : Run s₀ s' ks) : ks.map (·.epoch.val) = List.range' 1 ks.length := by
  rw [(epochs_consecutive h).1, keyFloor_init_a hi]

/-- A run from the state `init_b` returns emits its `n` keys at epochs `1, 2, …, n`. -/
theorem epochs_from_init_b {k : Slice Std.U8} {s₀ : States} (hi : States.init_b k = ok s₀)
    (h : Run s₀ s' ks) : ks.map (·.epoch.val) = List.range' 1 ks.length := by
  rw [(epochs_consecutive h).1, keyFloor_init_b hi]

/-- A run from a state with `keyFloor = 1`, such as either initial state, has emitted exactly the
epochs `1, …, keyFloor s' - 1`, in order, where `s'` is the state it ends in. -/
theorem emitted_epochs_below_keyFloor {s₀ : States} (hinit : keyFloor s₀ = 1)
    (h : Run s₀ s' ks) : ks.map (·.epoch.val) = List.range' 1 (keyFloor s' - 1) := by
  obtain ⟨hepochs, hfloor⟩ := epochs_consecutive h
  simpa [hinit, hfloor] using hepochs

end spqr.v1.chunked.states
