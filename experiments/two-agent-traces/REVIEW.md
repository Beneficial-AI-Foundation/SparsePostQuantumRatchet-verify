# Independent review of the trace-definition experiment

## Scope and review standard

Agent 2 reviews Agent 1's definition and proofs against the repository's existing
`Spqr/Specs/Braid/StateMachine/Run.lean`. The baseline commit is
`e38c4ce87a10c12d709a79962d75ac03ec295182`.

The existing `Step` relates a source state, destination state, and optional epoch
secret. Each constructor requires a successful translated send or receive call.
`Run` retains emitted secrets in order, dropping `none` outputs. The proposed
refinement is useful if it retains one optional output per successful call and
has a precise bridge to this existing relation.

Review criteria communicated to the author before implementation:

- Erasure must imply the existing run relation without strengthening `Step`.
- Lifting must recover some trace; it must not claim unique reconstruction.
- Splitting at a fixed optional-output prefix must retain silent steps and
  existentially quantify the intermediate state.
- Trace length counts successful calls, not failed attempts or network events.
- Noninjectivity of erasure on arbitrary lists does not by itself prove that two
  different such lists are both realizable SPQR runs with fixed endpoints.
- The work must not claim cryptographic security, liveness, optimality, or global
  mathematical novelty from structural run lemmas.

## Findings and resolutions

1. **Trust boundary (material documentation finding, resolved).** Independent
   `#print axioms` inspection found inherited axioms in the run-related results.
   Saying that these proofs are axiom-free would be incorrect. The author updated
   `AUTHOR.md` to state the dependencies and distinguish absence of new axioms
   from absence of all axioms. No mathematical proof change was needed.
2. **Existential versus unique reconstruction (checked, no defect).**
   `run_iff_exists_trace` quantifies an existing trace; it does not claim that its
   list is unique. `TraceRun.split` quantifies an intermediate state, without
   asserting determinism. The hypotheses retain the exact existing `Step`.
3. **Silent-step semantics (checked, no defect).** The new constructor adds one
   list element for every successful step, including `none`. `outputs` removes
   precisely these silent entries. Failed calls remain outside the model.
4. **Cut boundaries (checked, no defect).** The `cut` theorem holds for every
   natural index. Zero yields an empty prefix; the trace length yields an empty
   suffix. Larger indices saturate under the usual list `take` and `drop`
   definitions. There is no hidden `n ≤ length` precondition.
5. **Noninjectivity scope (checked, no defect).** `outputs_not_injective` proves a
   fact about arbitrary lists using `[]` and `[none]`. Neither the source nor the
   author's report treats this as evidence of two executable runs with fixed
   endpoints. That stronger claim is not established by this experiment.
6. **Improvement criterion (checked, no defect).** The definition exposes silent
   call positions in the index and supports a cut after a specified call count.
   This is a concrete representational benefit. It establishes neither a
   universally best definition nor a historical novelty claim.

## Independent validation

Reviewed `TraceRun.lean` SHA-256:

```text
4ec633ffb7d1706c44698c87dd1201e570dea7853b77c78a80cd38d1e24c85fa
```

All eleven theorem proofs were read and independently elaborated with the pinned
Lean environment (`leanprover/lean4:v4.35.0-rc4`). The separate review fragment
checks zero-length and full-length cuts and silent-output examples, and audits
every theorem plus the baseline `Run.append`. Reproduce from the repository root:

```sh
cat experiments/two-agent-traces/TraceRun.lean \
    experiments/two-agent-traces/ReviewChecks.lean > /tmp/spqr-trace-review-checks.lean
lake env lean /tmp/spqr-trace-review-checks.lean
```

This command completed with exit status 0 on 2026-11-10. `ReviewChecks.lean` is an
append-only audit fragment, not a standalone importable module. No `sorryAx`
appeared. Dependency output was:

| Theorem(s), in `spqr.v1.chunked.states.TraceExperiment` | Reported axioms |
| --- | --- |
| `outputs_append`, `outputs_not_injective` | `propext` |
| `length_eq_outputs_add_silent`, `outputs_length_le` | `propext`, `Quot.sound` |
| `TraceRun.toRun`, `Run.exists_trace`, `run_iff_exists_trace`, `TraceRun.append`, `TraceRun.split`, `traceRun_append_iff`, `TraceRun.cut` | 23 constants: `propext`, `Classical.choice`, `Quot.sound`, `Aeneas.Std.core.fmt.Formatter`, and 19 inherited `SrcTranslated.Funs` native-decision axioms |
| Baseline `spqr.v1.chunked.states.Run.append` | The same 23 constants |

The native-decision constants are printed in full by the reproducible audit;
their names have prefix `_private.SrcTranslated.Funs.0.spqr.` and suffix
`._native.decide.ax_N`. Matching the baseline dependencies confirms that the
experiment does not enlarge this reported axiom set. This does not independently
validate the translated implementation, the native computation trust mechanism,
or external models.

## Verdict

**Accepted as a scoped, machine-checked structural refinement experiment.** No
unresolved correctness defect was found in the eleven stated theorems. All
statements are conditional on finite successful-call traces of one party from
arbitrary states. They do not establish liveness, call success, an upper bound on
silent calls, cryptographic security, or uniqueness of states or traces.

This is an independent agent review within one shared experiment, not external
peer review. Acceptance is limited to the source hash and claims above.

## Paper review

The reviewer compared `paper.tex` against the definitions, all mathematical proof
statements, the author's report, and the independent axiom audit. Three precision
edits were requested and confirmed in the revised source:

- State that intermediate-state uniqueness is not asserted, rather than implying
  that actual nonunique intermediate states have been exhibited.
- Spell the translated axiom suffix pattern `_native.decide.ax_N` consistently
  with the dependency output.
- Label the emitted-key inequality as a lower bound on call count.

**Paper verdict: accepted after these edits.** The paper accurately states the
conservativity equivalence, specified-boundary splitting, saturated natural-number
cuts, list accounting, and unrestricted-list noninjectivity. Its examples remain
conditional on trace realizability. It discloses the inherited trust dependencies,
does not claim axiom-free proofs, and does not claim liveness, security, optimality,
or mathematical novelty. The workflow is described as independent agent review
within one experiment rather than external peer review.

Reviewed `paper.tex` SHA-256:

```text
dabc2b7647021ac79f4f0b13fa38d0df2c78f0d59ffebd66d6e4436280455323
```

The coordinator's `build.sh` reproduces the proof compilation, combined reviewer
fragment and axiom audit, and two-pass PDF build. This paper review concerns the
mathematical content and trust claims; final PDF rendering is checked by the
coordinator.
