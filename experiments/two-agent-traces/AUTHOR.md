# Agent 1: definition and theorem proposal

## Scope and motivation

This is a local research experiment on the branch `experiment/two-agent-trace-definitions`.
It does not change the production specification, generated translation, or Rust implementation.
Its reference is `Spqr/Specs/Braid/StateMachine/Run.lean` at base commit
`e38c4ce87a10c12d709a79962d75ac03ec295182`.

The existing `Run s t ks` records only emitted keys in its list index. Its derivation includes
silent steps, but the list index does not expose their number or positions. For reasoning about a
boundary after a specified number of successful calls, an optional-output trace is more suitable.
The proposed `TraceRun` adds this information while reusing the exact existing `Step` relation.
This is an improvement for that particular purpose, not a claim that one definition is universally
best or that the mathematical construction is historically novel.

## Definitions

All experiment declarations are in namespace
`spqr.v1.chunked.states.TraceExperiment` in `TraceRun.lean`.

- `outputs [] = []`; `outputs (k :: trace) = k.toList ++ outputs trace`.
- `TraceRun.nil : TraceRun s s []`.
- `TraceRun.cons : Step s u k → TraceRun u t trace → TraceRun s t (k :: trace)`.
- `silentCount` counts `none` entries.

A `none` entry is a successful call that emits no key, not a failed call. `TraceRun` is a relation
in `Prop`, as is the original `Run`; it is not an executable logger. The index records optional
outputs, not whether each call was a send or receive, its input message, or its random coins.

## Theorems and proof ideas

1. `outputs_append`: erasure commutes with list concatenation. Induction on the first list.
2. `TraceRun.toRun`: a trace erases to an existing run with identical endpoints. Induction on
   the trace derivation, applying the original constructors.
3. `Run.exists_trace`: every existing run admits an optional-output trace with identical
   endpoints whose erasure is its key list. Induction on the original run derivation.
4. `run_iff_exists_trace`: combines 2 and 3 into exact existential conservativity.
5. `TraceRun.append`: two adjacent traces concatenate. Induction on the first derivation.
6. `TraceRun.split`: for specified lists `xs` and `ys`, a trace of `xs ++ ys` has an intermediate
   state with a trace of `xs` followed by one of `ys`. Induction on `xs`, inverting the trace
   constructor at each nonempty prefix.
7. `traceRun_append_iff`: exact equivalence of concatenation and existential decomposition.
8. `TraceRun.cut`: for every natural `n`, a trace can be cut into `take n` and `drop n`, with
   an intermediate state. This follows from 6 and the list take/drop identity. For `n` greater
   than the trace length, the suffix is empty.
9. `length_eq_outputs_add_silent`: the number of successful calls is exactly the emitted-key
   count plus the silent-call count. Induction on the trace list and case analysis on its head.
10. `outputs_length_le`: emitted-key count is at most successful-call count, by 9.
11. `outputs_not_injective`: erasure of raw trace lists is not injective: `[]` and `[none]`
    both erase to `[]`. This does not assert that both are executable at particular endpoints.

## Initial validation

From the repository root:

```sh
lake env lean experiments/two-agent-traces/TraceRun.lean
```

The initial implementation compiled with exit status 0 and no diagnostics on 2026-11-10,
using the pinned `leanprover/lean4:v4.35.0-rc4` environment. No `sorry`, new `axiom`, or `admit`
is present. Agent 2 independently reviews the definitions, proof claims, compilation, and
axiom dependencies. Its result is recorded separately in `REVIEW.md`.

Agent 2 found no proof correction necessary and confirmed independent compilation. Its axiom
audit found that run-related results inherit `Aeneas.Std.core.fmt.Formatter`, 19
`SrcTranslated` native-decision axiom constants, and standard Lean axioms; no `sorryAx` was
reported. Thus “no new axioms” does not mean these theorems are axiom-free. The inherited
translation and external-model trust boundary remains in force.

## Limitations

These are structural theorems about finite runs of one party from arbitrary states. They do not
prove termination, fairness, success of a requested call, a finite upper bound on silent calls,
cryptographic security, correspondence of two parties, or uniqueness of an intermediate state.
Conservativity preserves the existing relation's observational scope and assumptions; it does
not repair or audit the underlying Rust-to-Lean translation or external cryptographic models.
The trace list cannot in general be uniquely reconstructed from the emitted-key list.
No claim of global mathematical novelty or optimality is made.
