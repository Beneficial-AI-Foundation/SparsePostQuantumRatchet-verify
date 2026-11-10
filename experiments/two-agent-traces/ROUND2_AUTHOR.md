# Agent 1: call-index epoch semantics (round 2)

## Proposal

Round 1 retained every successful call in an optional-output trace. Round 2 gives those call
boundaries a protocol-specific observable: the next-key epoch. The existing repository theorem
`epochs_consecutive` supplies endpoint epoch accounting, while `Step.keyFloor_step` supplies the
epoch emitted by one successful call. We transport these established invariants to call positions.

The source is `EpochTrace.lean`, in the existing `TraceExperiment` namespace. The round-1 source
`TraceRun.lean` remains unchanged. This is a local experiment, not a production specification
replacement or a submitted PR. No claim of global novelty is made.

## Definition and conventions

For initial state `s`, optional-output list `trace`, and natural number `n`, define

```text
epochClock s trace n = keyFloor s + length (outputs (take n trace)).
```

Boundary 0 is before the first successful call; boundary `n` is after `n` successful calls.
The call following a prefix of length `n` therefore has zero-based position `n`. Indices beyond
the trace length saturate because `take` returns the entire trace. `keyFloor` and the clock are
natural numbers; this definition does not perform machine-word arithmetic or assert success of
an overflow-producing call.

The clock is defined for arbitrary lists. Its equality to an actual state's `keyFloor` requires
a successful `TraceRun` witness. The trace records optional key outputs, not failed attempts.

## Results

1. `TraceRun.keyFloor_eq`: the endpoint floor equals the starting floor plus the number of
   emitted keys. This is a direct application of the existing `epochs_consecutive` theorem
   after erasing a trace to `Run`.
2. `TraceRun.cut_epochClock`: every boundary has an intermediate state witnessing the
   prefix and suffix traces, with `keyFloor` equal to `epochClock` at that boundary.
3. `TraceRun.boundary_keyFloor_unique`: any two states reached from the same initial state
   by the same optional-output prefix have equal `keyFloor`. This does not assert equality
   of the states themselves or uniqueness of the underlying execution.
4. `TraceRun.emission_epoch`: if an executable trace is `pre ++ some k :: suffix`, then
   `k.epoch.val = keyFloor s + length (outputs pre)`.
5. `epochClock_prefix`: the clock at the end of an explicit prefix equals its emission count
   plus the initial floor.
6. `TraceRun.emission_epochClock`: under the same executable-trace hypothesis as 4, the
   key's epoch equals the clock immediately before that call.
7. `epochClock_interval`: in `pre ++ middle ++ suffix`, the clock after `middle` equals
   the clock before `middle` plus `length (outputs middle)`. These boundaries are ordered
   by construction, so no subtraction or underflow convention is required.
8. `outputs_eq_nil_iff`: erasure is empty exactly when every list entry is `none`.
9. `epochClock_interval_eq_iff`: the clock is unchanged across `middle` exactly when
   every entry of `middle` is `none`. This is a list-level identity for the defined clock.
10. `TraceRun.keyFloor_eq_iff_silent`: for an executable trace, the endpoint floor equals
    the starting floor exactly when every successful call in that trace emits no key.

The main proof chain is:

```text
TraceRun.toRun + epochs_consecutive -> TraceRun.keyFloor_eq
TraceRun.cut + TraceRun.keyFloor_eq -> TraceRun.cut_epochClock
TraceRun.split + Step.keyFloor_step -> TraceRun.emission_epoch
outputs_append + list take identities -> epochClock_interval
outputs_eq_nil_iff + interval accounting -> epochClock_interval_eq_iff
```

## Initial validation and reproducibility

From the repository root, with the existing experiment `build` directory:

```sh
lake env lean -o experiments/two-agent-traces/build/TraceRun.olean \
  experiments/two-agent-traces/TraceRun.lean
lake env bash -c 'export LEAN_PATH="$PWD/experiments/two-agent-traces/build:$LEAN_PATH"; lean experiments/two-agent-traces/EpochTrace.lean'
```

Both commands completed with exit status 0. The round-2 source produced no compiler diagnostics.
It adds no `sorry`, `admit`, or axioms. It imports the existing implementation-level epoch
invariants and inherits their trust dependencies; no claim of axiom-free verification is made.
Agent 2 independently audits these dependencies against the existing invariants and reviews the
paper's distinction between arbitrary trace-list identities and executable-trace properties.

Agent 2 accepted the proof review without a source correction and independently compiled
zero-boundary, saturation, sample, and first-call checks. Its axiom audit found the six
protocol-connected theorems have exactly the same 23 axiom constants as both
`epochs_consecutive` and `Step.keyFloor_step`; no additional axioms or `sorryAx` were found.
The four pure trace-list results use only standard Lean axioms. See the separate round-2
review report for the audited names and full interpretation of this trust boundary.

## Limits

The result identifies an observable shared by all witnesses at a boundary, not a unique state.
Silent calls can change internal state while leaving this observable unchanged. The silent-interval
characterization does not imply that silent intervals are empty, that they terminate, or that a
key will eventually be emitted. Two-party agreement, secrecy, security against adversaries, and
success of future calls remain outside this experiment.
