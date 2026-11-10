# Two-agent definition experiment

Branch: `experiment/two-agent-trace-definitions`

Base: `e38c4ce87a10c12d709a79962d75ac03ec295182`

- [Paper PDF](paper.pdf) and [TeX source](paper.tex).
- [Author's results](AUTHOR.md) and [Lean definitions/proofs](TraceRun.lean).
- [Independent review](REVIEW.md) and [review checks](ReviewChecks.lean).
- Round 2: [epoch-clock proofs](EpochTrace.lean), [author report](ROUND2_AUTHOR.md),
  [review](ROUND2_REVIEW.md), and [review checks](Round2ReviewChecks.lean).

The author agent introduced an optional-output trace retaining silent successful
calls. Eleven checked theorems establish exact erasure to the existing `Run`,
existential lifting, composition, splitting at any call boundary, and exact call
accounting. The reviewer accepted the scoped results and required explicit
inherited-axiom disclosure. No global novelty, best-definition, or new
cryptographic-security claim is made.

Round 2 adds ten checked theorems connecting call boundaries to SPQR's existing
`keyFloor` invariant: boundary floor agreement, positioned-emission epochs, exact
interval progress, and unchanged-floor equivalence with silence. The definition
`epochClock` exposes the epoch after each prefix. This derives new trace-indexed
consequences of the existing invariant, rather than claiming a new security proof.
The original `TraceRun.lean` remains unchanged.

Run from the repository root:

```sh
bash experiments/two-agent-traces/build.sh
```

Prerequisites: this repository's pinned Lean dependencies and cached/buildable
`Spqr.Specs.Braid.StateMachine.Run` and
`Spqr.Specs.Braid.Scka.EpochUniqueness.KeyFloor`, plus `pdflatex` with the packages used in
`paper.tex`. The script checks the proof module, appends the review fragment to a
temporary build file, compiles the second-round module and its standalone review
checks, prints all theorem axioms, and compiles the PDF twice.
Logs are retained in ignored `build/`; the deliverable `paper.pdf` is retained.
`ReviewChecks.lean` is intentionally an append-only fragment, not a standalone
module. The experiment is outside the production Lake libraries and requires no
changes to their imports. `lake exe mk_all --git` reported no update necessary.

The run-related results inherit exactly the same 23 reported axiom constants as
the baseline `Run.append`, including translated native-decision constants. There
are no new axioms or admitted proofs; see the review for the precise trust scope.
The six protocol-connected round-two results have exactly the same reported
23-axiom set as the existing `epochs_consecutive` and `Step.keyFloor_step`; the
remaining four have only standard axiom subsets.
This is local experimental work. No PR was submitted; the repository contribution
guide prohibits PRs introducing AI-generated specifications.
