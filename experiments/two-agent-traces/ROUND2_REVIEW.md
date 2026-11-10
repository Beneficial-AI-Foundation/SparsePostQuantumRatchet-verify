# Round 2: independent review of the call-index epoch clock

## Scope

This review concerns the second experiment round. The first-round review in
`REVIEW.md` remains a historical record. Round 2 should connect the optional-output
trace to the existing SPQR `keyFloor` and `epochs_consecutive` theorem rather than
claim a new protocol invariant independent of those existing proofs.

The reviewer communicated these criteria before implementation:

- Use explicit zero-based call indices and distinguish an index from a number of
  completed calls.
- Account for `take`/`drop` saturation beyond the trace length.
- Require a valid trace and an actual key at the selected call before identifying
  that key's epoch.
- State ordered-index conditions for interval identities involving natural-number
  subtraction, or explicitly justify truncated subtraction without those conditions.
- Separate list identities from protocol-specific consequences.
- Compare axiom dependencies with `epochs_consecutive` and `Step.keyFloor_step`,
  since new imports may change the first-round trust boundary.

## Findings

1. **Clock interpretation (checked).** `epochClock s trace n` is the source
   `keyFloor` plus the erased prefix length. It is defined on every optional-output
   list. Only valid-trace hypotheses connect it to an actual intermediate state.
   Boundary zero precedes the first call, and oversized indices saturate.
2. **Preservation of existing invariant (checked).** `TraceRun.keyFloor_eq` is
   precisely the endpoint component of `epochs_consecutive` applied after erasure.
   The results derive a new call-index presentation of that invariant; they do not
   independently prove the underlying transition case analysis.
3. **Uniqueness claim (checked).** `boundary_keyFloor_unique` identifies only the
   natural-number observable, not the full state. The proof compares two instances
   of endpoint accounting and assumes the same source and prefix.
4. **Positioned emission (checked).** `emission_epoch` requires a valid trace with
   an explicit `some k` after the given prefix. Splitting yields a real step, and
   `Step.keyFloor_step` identifies its key epoch. The clock is evaluated before the
   emitting call, at zero-based call position `pre.length`.
5. **Interval order and silence (checked).** Intervals use an explicit
   `pre ++ middle ++ suffix` decomposition. Boundary order is guaranteed by list
   lengths, and the equation uses addition rather than truncated subtraction.
   The two silence equivalences follow from nonnegative counts and the fact that
   erasure is empty exactly for all-`none` lists. Empty intervals are included.
6. **Trust boundary (checked).** The stronger import does not enlarge the reported
   dependency sets beyond the existing epoch invariant. Exact results are below.

No mathematical correction was requested. The author reports and paper distinguish
conditional execution claims from arbitrary-list identities and avoid liveness,
security, and full-state uniqueness claims.

## Independent validation

All ten theorem proofs were reviewed. The reviewer independently compiled the two
experiment modules and the standalone `Round2ReviewChecks.lean` module. Additional
checks cover boundary zero, a list with silence/emission/silence, saturation beyond
its end, and a valid trace emitting a key at its first call. They do not assert
that the sample arbitrary list is executable.

Reproduce from the repository root:

```sh
lake env lean -o experiments/two-agent-traces/build/TraceRun.olean \
  experiments/two-agent-traces/TraceRun.lean
lake env bash -c 'export LEAN_PATH="$PWD/experiments/two-agent-traces/build:$LEAN_PATH"; lean -o experiments/two-agent-traces/build/EpochTrace.olean experiments/two-agent-traces/EpochTrace.lean && lean experiments/two-agent-traces/Round2ReviewChecks.lean'
```

Both commands completed with exit status 0. The complete `build.sh` also includes
these module compilations and this standalone audit. `#print axioms` inspects every
new theorem and both baseline invariant theorems:

| Theorems in `spqr.v1.chunked.states.TraceExperiment` | Reported dependency set |
| --- | --- |
| `TraceRun.keyFloor_eq`, `TraceRun.cut_epochClock`, `TraceRun.boundary_keyFloor_unique`, `TraceRun.emission_epoch`, `TraceRun.emission_epochClock`, `TraceRun.keyFloor_eq_iff_silent` | Exactly the same 23 constants as both `epochs_consecutive` and `Step.keyFloor_step` |
| `epochClock_prefix`, `epochClock_interval`, `epochClock_interval_eq_iff` | `propext`, `Classical.choice`, `Quot.sound` |
| `outputs_eq_nil_iff` | `propext`, `Quot.sound` |

The 23 constants comprise the three standard axioms listed above,
`Aeneas.Std.core.fmt.Formatter`, and 19 inherited translated native-decision
constants. None of the audited results lists `sorryAx`; the experiment adds no
axioms. The baseline comparison is exact set equality, not just a comparison of
counts. These facts do not independently validate the imported translation or
external models.

Reviewed `EpochTrace.lean` SHA-256:

```text
1ba26c4ba0cb8ea249431a7c72b4d6f3bc86354c476ca5bc059d4148a19a56ac
```

## Verdict and paper review

**Accepted as a scoped, machine-checked extension.** No unresolved correctness
defect was found in the ten round-two theorem statements or proofs. The central
contribution is transporting the existing next-key epoch invariant to explicitly
indexed successful-call boundaries, including an observable uniqueness result and
an exact silence characterization.

The round-two paper section was compared with the source and proof dependencies.
Its mathematical claims are supported. The paper's auxiliary notation `C(f,τ,n)`
accepts a natural initial floor, while Lean's `epochClock` accepts a state; the
paper explicitly reconciles them as `C(keyFloor s,τ,n)`. The prose correctly
distinguishes floor equality from full-state equality and places no upper bound on
silent intervals. The coordinator added the exact six-theorem dependency-set
comparison and clarified that the positioned emission is at zero-based call index
`pre.length`, with its clock evaluated immediately before the call. Both additions
were checked against the independent audit and source.

**Final paper verdict: accepted.** No unresolved mathematical or trust-disclosure
issue remains in the reviewed draft. Reviewed `paper.tex` SHA-256:

```text
4ebe334853a1470adf3dc5d314da3ae294cd1fc6ccad832ea583649f10fcbfe3
```

The coordinator reports a successful full proof/audit/PDF build. PDF rendering and
typography are checked separately by the coordinator. This review is independent
agent review inside the same experiment, not external peer review.
