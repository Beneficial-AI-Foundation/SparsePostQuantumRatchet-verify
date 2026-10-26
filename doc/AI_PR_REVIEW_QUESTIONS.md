# Questions for AI review of SPQR pull requests

Use these questions to review a PR in `SparsePostQuantumRatchet-verify`. Answer them from the
current diff, Rust source, theorem statements, dependencies, and validation results, then report
only the problems found, grouped and tagged as described in
[Reporting the review](#reporting-the-review). Ask the author only when a material question
remains unresolved after that inspection. A passing Lean proof
establishes its formal statement under its assumptions; review must also assess whether those
assumptions and that statement describe the intended implementation.

This guide supplements the [reviewer guide](REVIEWER_GUIDE.md), [style guide](STYLE_GUIDE.md), and
[workflow guide](WORKFLOW_AND_PR_GUIDE.md). Recheck those policies when reviewing future changes.
The workflow prohibits AI-generated specifications and permits AI-generated proofs under human
responsibility. This checklist supports review; it does not authorize generating specifications
or substitute for a human approval. The limits on what an AI review may propose are stated in
[Reporting the review](#reporting-the-review).

The principles in each section are meant to stay valid as the repository evolves. The
[appendix](#appendix-historical-examples) ties them to past issues and PRs, as read on
2026-10-23. Append newer examples there rather than rewriting the principles.

## Procedure

Perform these steps before answering the questions. They produce the evidence the questions
refer to.

1. **Fix the revision.** Record the base and head commits of the PR and review exactly that diff:

   ```bash
   git fetch origin main pull/<N>/head:pr-<N>
   git merge-base origin/main pr-<N>          # base commit
   git rev-parse pr-<N>                       # head commit
   git diff <base>...pr-<N> --stat
   git diff <base>...pr-<N>
   ```

   If the author pushes after the review starts, re-record the head and re-read the changed hunks.
2. **Read the PR metadata.** Check title, body, footer, labels, and closed issues against the
   [workflow guide](WORKFLOW_AND_PR_GUIDE.md#pr-workflow-and-formatting): one issue per PR unless
   related, `Closes #...` in the footer, body starting with "This PR", roughly 500 LOC, and no
   meaningful pushes after the PR was marked ready for review.
3. **Build and lint the head.** For Lean changes the baseline is:

   ```bash
   lake build
   lake exe runLinter Spqr
   ```

   Stale `.lake` build artifacts can hide a missing import or an unbuilt module. When in doubt,
   build the changed modules explicitly, for example `lake build Spqr.Specs.Lib.InitialState`. For
   added, removed, or renamed Lean files, run `lake exe mk_all --git` and confirm the root import
   files in the diff match the result.
4. **Audit the trust base on base and head.** The audit scans every module reachable from
   `Spqr.lean` and writes `sorry-manifest.txt` into the working tree. It overwrites that file; do
   not commit it. Run it on both revisions and diff the manifests the same way CI does:

   ```bash
   lake env lean scripts/Audit.lean          # at base; then rename the manifest
   mv sorry-manifest.txt sorry-manifest-base.txt
   lake env lean scripts/Audit.lean          # at head
   python3 scripts/sorry-diff.py sorry-manifest-base.txt sorry-manifest.txt
   ```

   The manifest covers `sorry`. For other axioms, including `native_decide` and `bv_decide`
   auxiliary axioms, read section 3 of the audit output and, for each changed theorem, run
   `#print axioms <theorem>` in a scratch file. Expected builtin axioms are `propext`,
   `Classical.choice`, and `Quot.sound`; anything else is a trust change to report under
   question 6.
5. **Check extraction inputs when they change.** For diffs touching `translation-patches/`,
   `Cargo.toml` charon metadata, `src/`, or generated `Types.lean`, `Funs.lean`, or
   `translation.json`, follow [scripts/README.md](../scripts/README.md) for the patch, extraction,
   and source-diff checks. Run mutation-producing checks in a separate working tree.
6. **Read existing performance results.** The [performance guide](PERFORMANCE.md) documents
   `!radar`. Read results that are already posted. Posting `!radar` is a GitHub comment, so an AI
   should post it only when authorized to comment.

## Which sections apply

Answer the eight core questions on every PR. Then select topic sections by the kind of change.
A PR that touches several kinds needs each applicable section.

| Kind of change | Typical files | Sections to apply |
| --- | --- | --- |
| Specification and proof of one function | `Spqr/Specs/**` | Specification strength; Proof maintainability; Validation |
| Extraction, patch, or pinned Rust update | `translation-patches/`, `Cargo.toml`, `src/`, `SrcTranslated/**` | Extraction and handwritten external models; Axioms; Validation |
| Handwritten external model or axiom | `SrcTranslated/FunsExternal.lean`, `SrcTranslated/TypesExternal.lean`, `axiom` declarations | Extraction and handwritten external models; Axioms and cryptographic boundaries |
| Serialization, protobuf, or encoding | `Spqr/Specs/**/Serialize/**`, `*Pb.lean`, `Spqr/Specs/Encoding/**` | Serialization and round trips; Specification strength |
| Protocol or multi-function property | `Spqr/Specs/Braid/**` or theorems composing several `@[step]` specs | Protocol properties and composition; Axioms |
| Mathematics or shared lemma library | `Spqr/Math/**`, shared helpers | Proof maintainability; Validation |
| CI, scripts, benchmarks, documentation | `.github/`, `scripts/`, `doc/` | Validation and performance; question 8 |

## Questions to answer on every PR

1. **What exact claim is this PR meant to establish?** Identify the issue, Rust function or
   protocol property, changed theorem, and intended observable behavior. Do the title, body, and
   closing references match the actual code, and does the PR meet the format checked in procedure
   step 2? A closure belongs with its enclosing function, not merely its return type.
2. **Am I reviewing the right revision?** Use the base and head from procedure step 1, inspect
   the complete diff, and distinguish new changes from inherited problems. Have subsequent
   commits changed the code covered by an earlier approval or build?
3. **Could a plausible wrong implementation satisfy this postcondition?** Try returning a
   default, deleting all keys, duplicating an entry, keeping stale state, or accepting malformed
   input. Identify the clause that excludes each relevant counterexample.
4. **Are the premises satisfiable and justified at the call sites?** Look for inconsistent
   universal bounds, assumptions equivalent to the desired conclusion, and hypotheses that
   exclude valid inputs merely to simplify the proof.
5. **Does the Lean model faithfully represent the Rust behavior?** Confirm the theorem is stated
   about the extracted definition in `Funs.lean` or the registered external signature, with the
   full name and arity current after the latest re-extraction, not about a local copy or a
   convenient replacement definition. Then check success, error, panic, arithmetic, mutation,
   and external calls against the Rust source.
6. **What changed in the trust assumptions?** Use the audit and `#print axioms` results from
   procedure step 4 to inspect direct and transitive `sorry`, custom axioms, opaque
   declarations, compiler-based proof dependencies, and external definitions. Determine whether
   an apparent reduction in axioms merely moved assumptions into model bodies.
7. **Can callers actually use this result?** Check whether the postcondition provides the
   bounds, values, invariants, and preserved fields needed by the next operation. Check theorem
   registration and imports as well as logical strength.
8. **What validation supports my conclusion?** Report the commands from the procedure that
   actually ran on the head revision and their results. Separate command results from claims in
   the PR body, and separate successful compilation from performance measurements.

Historical examples for each question are listed in the [appendix](#appendix-historical-examples).

## Specification strength and state changes

- Does the theorem relate output values to the actual input, beyond length, existence, or a
  type-implied property? Could its main clause hold for every function of the same type?
- Does every mutable output describe both changed fields and fields that must remain unchanged?
  For collection updates, are content, order, multiplicity, and unaffected entries constrained?
- Are success, application-level `Err`, and Aeneas failure/panic distinguished correctly? Does
  the contract cover all intended branches, and are excluded branches justified?
- Are bounds attached to the original parsed value, rather than only its narrowed or truncated
  representation? Aeneas defines the `Usize` width as `System.Platform.numBits`, so a statement
  about `usize` must hold for both 32 and 64 bits unless a hypothesis fixes the width.
- Does a loop invariant describe accumulated results and progress? Are its initial state,
  maintained fields, and termination measure tied to the actual loop inputs?
- Is a mathematical abstraction clearer and more useful than repeating implementation steps?
  Conversely, does an abstraction erase details needed by callers?
- Are existential witnesses sufficiently constrained? An existential is not inherently weak:
  inspect whether its predicate determines the relevant values before requesting a rewrite.

## Extraction and handwritten external models

- Was generated output regenerated from pinned tools and configuration? Were `Types.lean`,
  `Funs.lean`, or `translation.json` edited by hand contrary to the workflow?
- Does a translation patch preserve behavior, including errors and panics? Does its header
  explain the rewrite, tool limitation, any behavior difference, and external facts it relies on?
- Are pinned upstream Rust files preserved outside the authorized upstream-update process?
  Are new `exclude` or `opaque` entries justified and their verification consequences visible?
- Does a handwritten model use a consistent representation across all operations? For example,
  for a deque, trace `push_back`, `pop_front`, indexing, and iteration with a nonzero head and an
  empty tail.
- Do iterator models update state and terminate? Do checked arithmetic and overflow behavior
  match the extraction configuration rather than silently using wrapping arithmetic?
- Does a sorted collection preserve ordering and handle equal keys correctly? If binary search
  may select any matching element, does a valid-input invariant justify the chosen result?
- If a type alias removes Rust invariants, where are those invariants restored as predicates,
  established by constructors, and preserved by operations?
- Does a proposed codegen fix actually match Rust, or is the problem in a theorem's premises?

## Axioms and cryptographic boundaries

- For each axiom, what precise external result or implementation behavior justifies it? Does
  the source establish this statement for these parameters and this version?
- Is an external function represented by a `noncomputable opaque` signature, with behavioral
  assumptions separately named, as required by the workflow? If it becomes a concrete model,
  where is the justification that the external implementation computes that model?
- Are direct and transitive dependencies audited, including dependencies in statement types?
  Does a "no new sorry" claim compare the same base and head declarations accurately?
- Is every deferred proof linked to a tracking issue next to its `sorry`? Are stale axioms
  removed when superseded by extracted definitions or proved results?
- Does `native_decide` or another compiler-dependent mechanism change the accepted trust base?
  Is a temporary performance workaround described as temporary with an explicit follow-up?
- Are cryptographic claims about functional behavior, model correctness, probabilistic security,
  or their refinement? Does the final theorem mention the implementation entry points it claims
  to verify, or only abstract model functions?
- For ML-KEM changes, do byte order, signed coefficients, matrix indices, lengths, validation,
  error variants, and compatibility repair paths match the pinned implementation?
- Are randomness witnesses tied to the actual RNG output and successor state? Does a conditional
  noise/recovery theorem clearly state its hypothesis rather than imply unconditional success?
- Are claims of "any primitive instantiation" supported by actual parameters, rather than a
  single fixed collection of opaque constants?

## Serialization and round trips

- What is the domain of valid internal states? Is validity explicit, and do actual callers
  establish it? Include empty data, zero polynomials, maximum lengths, and malformed fields.
- Are encoder outputs accepted by the decoder under exactly the established postconditions?
  Does any required length, nonzero, sorting, or uniqueness premise disappear between the two?
- Does decoding an encoded valid state recover the original state? If the representation admits
  irrelevant storage or normalized fields, what equality is intended?
- Does re-encoding a successfully decoded protobuf recover the original protobuf, or only a
  canonical version? Consider defaults, omitted fields, duplicates, normalization, and discarded
  information before asserting literal equality.
- Do pure functional models describe both success and errors, and are the extracted functions
  separately proved to implement those models?
- Are round-trip theorems stated at the intended layer? If only pure models are covered, is the
  connection to extracted code available and the documentation precise about that boundary?

## Protocol properties and composition

- Does the theorem quantify over one party or both, arbitrary states or initialized states,
  and individual calls or traces? Are those choices explicit in its documentation?
- If successful calls are hypotheses, is the result accurately described as conditional?
  Where, if anywhere, are success, progress, and reachability established?
- Are old, equal, and future epochs covered, including wrong payload types and overflow at the
  next epoch? Is the next state, emitted key, and error outcome specified in each relevant case?
- Is a claimed protocol correspondence exact, or are implementation deviations explicitly
  enumerated against a named revision and section?
- Does every composition step connect one function's postcondition to the next function's
  precondition? Is a shared pure model or reusable predicate preferable to duplicated contracts?
- Are protocol-level theorems placed and tagged as Braid properties rather than forced into
  the per-function `@[step]` convention?

## Proof maintainability and discoverability

- Is there an existing Mathlib, Aeneas, or local lemma that avoids rebuilding infrastructure?
  Is a new helper actually used or needed by this change?
- Are reusable mathematics, external models, and implementation-specific proofs placed in
  appropriate layers? Are duplicate instances centralized rather than added again?
- Do function spec paths mirror the Rust module tree, including closure ownership? Does the
  theorem use the full function name plus `_spec`, with a useful natural-language description?
- Are function contracts registered with `@[step]` when appropriate? Can a downstream caller
  use them? A documented tactic-performance exception merits inspection rather than automatic
  rejection. Pure constants may appropriately use equation/simp lemmas instead of artificial WP.
- Are imports minimal while exposing the definitions consumers actually need under the module
  system? Were root imports regenerated when Lean files were added, renamed, or removed?
- Are flexible nonterminal tactics replaced by explicit lemma sets where practical? Are
  heartbeat increases justified, local, and consistent with the style guide?
- Do docstrings explain the statement and relevant source rather than narrate proof development?
  Are warnings fixed, and any exceptional linter suppression justified?

## Validation and performance

The commands are in the [procedure](#procedure). These questions interpret their results.

- Did checks use the PR's current sources and pinned dependencies, without stale build artifacts
  masking a missing import or unbuilt module?
- Does CI preserve the failing exit code through pipes and invoke every required job for fork
  and branch PRs? Do caches contain completed build outputs with appropriate keys?
- Does the proof's cost come from repeated arguments, broad imports, expensive automation,
  or computation that could be replaced by a symbolic argument?
- Are benchmark base and head builds both successful and comparable in toolchain, runner, and
  configuration? Are instruction counts, memory, and elapsed time being interpreted correctly?
- Is a regression acceptable, should it block, or does it need a specifically tracked follow-up?
  The reviewer guide lists the three outcomes: accept, accept with a follow-up issue, or block.

## Reporting the review

The questions above are the investigation checklist, not the outline of the report. The report
lists only problems. Do not answer the questions one by one, do not restate what the PR does, and
do not list the checks that passed except in the validation footer. A reader should be able to
see the verdict and every finding, grouped by severity, without reading anything else.

### Severity groups

Group findings under these three headings, in this order, using the vocabulary of the
[reviewer guide](REVIEWER_GUIDE.md). Omit a heading that has no findings.

- **Blocking:** a demonstrated counterexample to a specification, an unsatisfiable or
  question-begging premise, an unfaithful model of the Rust behavior, an unjustified change to
  the trust base, or validation that did not actually pass on the head revision.
- **Judgment (blocking or non-blocking):** level of abstraction, usability by callers,
  composition gaps, and performance regressions, in proportion to their impact.
- **Non-blocking:** naming, placement, reuse, comments, PR format, and style, unless the style
  guide makes the point mandatory or the problem is pervasive.

A historical disagreement or keyword match is a prompt to investigate, not a finding by itself.
State the group explicitly so the human reviewer can override it.

### Category tags

Tag each finding with one category so that findings of the same kind can be compared across
PRs. The tag names the section of this guide that produced the finding:

| Tag | Source section |
| --- | --- |
| `spec` | Specification strength and state changes; core question 3 |
| `premise` | Core question 4 |
| `model` | Core question 5; Extraction and handwritten external models |
| `trust` | Core question 6; Axioms and cryptographic boundaries |
| `usability` | Core question 7; Protocol properties and composition |
| `serialization` | Serialization and round trips |
| `validation` | Core question 8; Validation and performance |
| `maintainability` | Proof maintainability and discoverability |
| `format` | Core questions 1 and 2; PR title, body, footer, revision |

### Finding format

Write each finding as one bullet in this shape:

```text
- [`tag`] `path/to/File.lean:LINE` `theorem_name` — one-sentence defect.
  Evidence: counterexample, dependency argument, or Rust lines that define the intended behavior.
  Consequence: what callers, proof meaning, or verification scope lose.
  Ask: the focused question or requested correction, and what evidence would resolve it.
```

Keep the first line short enough to scan. Put the reviewed head commit once in the footer, not
in every finding. If the same defect appears at several places, report it once and list the
locations.

**What an AI review may propose.** The workflow prohibits AI-generated specifications. In a
review this means: an AI may present a counterexample, name the property that is missing in
words, point to the Rust lines that define the intended behavior, and cite existing repository
definitions that could be reused. It should not post replacement theorem statements or
postcondition clauses in Lean. The author writes the clause and remains responsible for it. An
AI may propose proof text, since AI-generated proofs are permitted under human responsibility.

Useful author-facing questions after investigation include:

- "Which established invariant excludes this input? I could not find it in the caller's contract."
- "This postcondition also permits deleting all live entries. Which clause is meant to preserve them?"
- "This axiom disappeared when the external became a definition. Where is correspondence with
  the pinned Rust implementation justified?"
- "Is this inverse intended for every accepted protobuf value, or only canonical encodings?"
- "This theorem assumes successful calls. Should the PR's progress claim be narrowed, or is
  there a separate success theorem?"
- "The benchmark compares against a failed base build. Is a successful comparable baseline available?"

### Report layout

```text
Verdict: <no blocking finding | N blocking finding(s)> on <head commit> (base <base commit>).

Blocking
- ...

Judgment
- ...

Non-blocking
- ...

Validation: <commands from the procedure that ran on the head, each with pass/fail>.
Unverified: <material boundaries not checked, or "none">.
```

The verdict line comes first. If no blocking problem is demonstrated, say so without claiming
full protocol security. The validation line names the commands that actually ran and their
results; it does not repeat the PR body's claims. Recheck claimed fixes against the updated diff
rather than accepting an author reply. An AI review remains assistance for the responsible human
reviewer.

## Appendix: historical examples

Each entry illustrates a principle above; it is not a finding about the current code. The
entries were read from the linked issues and PRs on 2026-10-23. A historical statement may be
superseded or disputed, and an author saying a finding is fixed is not independent verification.
Add newer examples below the existing ones.

**Core questions.**

- Q1, claim and placement: #562 filed a closure spec under its return type instead of its
  enclosing function; #570 corrected a mismatched title and closing reference. [#562][562], [#570][570]
- Q2, revision: #654 and #712 had later commits change code covered by an earlier build or
  approval. [#654][654], [#712][712]
- Q3, counterexamples: #491 used a "delete all keys" and a "duplicate a live key" implementation
  to show a `gc` postcondition was too weak; #550 found unconstrained chain state; #678 found that
  parameter presence did not imply correct parameter values. [#491][491], [#550][550], [#678][678]
- Q4, premises: #389 exposed an inconsistent bound; #491 had a precondition that excluded valid
  `current_key` values. [#389][389], [#491][491]
- Q5, model fidelity: #153 reported that the `clone_from_slice` model omitted the
  length-mismatch panic; #618 and #661 concerned models diverging from Rust behavior.
  [#153][153], [#618][618], [#661][661]
- Q6, trust base: #48, #574, #661, and #718 involved transitive stubs, hidden model
  assumptions, or compiler trust. [#48][48], [#574][574], [#661][661], [#718][718]
- Q7, usability: #249 and #550 concerned postconditions too weak for callers; #715 corrected
  registration. [#249][249], [#550][550], [#715][715]
- Q8, validation: #549 found the CI lint step discarding the linter's exit code, and #676 found
  the build cache saved before the build ran, so green CI did not demonstrate what it appeared
  to; #718 weighed compiler trust against proof performance. [#549][549], [#676][676], [#718][718]

**Specifications must rule out plausible wrong implementations.** Review of key-history garbage
collection supplied two counterexamples: deleting every key, and duplicating a live key while
losing another entry. Saying that remaining keys are valid did not capture preservation or
multiplicity. Review of `recv_key` found that constraints on returned values and scalar fields
left the updated `links` unconstrained. Initialization review required direction, minimum
version, serialized parameters, and the direction-specific initial state to be tied to the
inputs; a later pass caught that "parameters are present" still permitted the wrong parameters.
Other discussions rejected a representability clause that was always true, a missing lower bound
on decoder progress, and a hypothesis strong enough to imply `False`. Discussion in #542 explains
why an existential and a match formulation can be equivalent. [#320][320], [#373][373],
[#389][389], [#491][491], [#542][542], [#550][550], [#678][678]

**Handwritten external models need their own fidelity review.** The original `clone_from_slice`
model ignored destination length and omitted the mismatch panic. Deque discussions exposed
inconsistent choices between a physical ring-buffer layout and a logical list model; a later
iterator issue showed nontermination and wrong output after `pop_front`. Sorted-set review caught
append behavior where replacement was required. Decoder review questioned a binary-search model
that always chose the first match when the Rust behavior needed an explicit uniqueness invariant
to justify that choice. In #272 an issue proposed changing an extracted record update to force
`y = ONE`; later comments showed the Rust loop preserves `y` and the "fix" would make the
translation unfaithful. Check the source and the invariant before repairing generated code to
make a proof work. [#153][153], [#183][183], [#200][200], [#234][234], [#272][272], [#365][365],
[#618][618], [#619][619], [#683][683]

**Trust assumptions must remain visible.** The workflow discussion settled on `sorry` for
intended future proofs, with a linked issue, and `axiom` for externally justified properties,
with a source. Auditing must inspect transitive dependencies, not merely search the edited file
for `sorry`; #574's PR body reported `sorryAx` inherited through an extraction iterator stub in
its statements about runs, and that qualification should accompany any summary of its result.
In #661 reviewers questioned moving external behavior into concrete definition bodies, which can
make correspondence lemmas reflexive while hiding the implementation-to-model assumption from an
axiom count, and questioned end-to-end wording for a round-trip theorem about model functions.
HMAC generalization needed algorithm-specific lengths. #718 merged a temporary switch to
`native_decide`; #721 remains open to decide a lasting solution. [#39][39], [#48][48], [#89][89],
[#243][243], [#574][574], [#661][661], [#714][714], [#718][718], [#721][721]

**Serialization requires valid domains and explicit normalization.** The zero-polynomial
discussion identified serialization to an empty sequence that deserialization rejects.
Participants argued that V1 execution invariants exclude this case; that is a claim about
reachable protocol states, not a universal round-trip theorem for the type. #568 and its
implementation PRs developed a common architecture: pure functional models, proofs that extracted
conversions implement them, and model-level round trips. Discussion distinguished decoding an
encoded valid state from re-encoding arbitrary accepted protobuf data, which may normalize
defaults or discard information, so literal equality requires canonical input or a normalization
statement. Encoder postconditions must imply decoder preconditions. [#566][566], [#567][567],
[#568][568], [#571][571], [#578][578]

**Composition and protocol claims need precise scope.** Function contracts need enough
information for their callers: interpolation required degree information, authentication
required input/output relationships, and state operations required frame conditions for
unchanged fields. A pure model can make these contracts clearer and easier to compose than
equations between opaque computations; #645 proposes further work in this direction and is not a
ban on equational specifications. The Braid documentation discussion required stating whether a
theorem covers one or both parties, arbitrary or initialized states, and only successful calls.
Assuming a call succeeds does not prove it succeeds. Draft #663 compares receive dispatch with
ML-KEM Braid Rev. 1 §2.5 and lists three deviations. [#247][247], [#249][249], [#546][546],
[#550][550], [#574][574], [#576][576], [#645][645], [#662][662], [#663][663]

**Performance and CI evidence need interpretation.** Reviews encouraged profiling but challenged
comparisons involving failed builds, changed benchmark configurations, or apparent noise. Early
discussion found that registering a loop lemma for `step` could sharply increase proof time;
later work extracted repeated proof arguments and reduced import cost. Infrastructure history
includes required checks that did not run for PRs, fork-token failures, duplicate runs, lint
errors missed by text matching, and caches saved before the build they were supposed to cache. A
green check is useful only if the intended command ran on the intended revision and its failure
status was preserved. [#55][55], [#84][84], [#86][86], [#98][98], [#100][100], [#548][548],
[#549][549], [#647][647], [#660][660], [#670][670], [#676][676], [#677][677], [#718][718]

**Maintainability and review process are recurring concerns.** Reviewers repeatedly requested
shared helpers and instances, source-aligned file placement, accurate docstrings, discoverable
theorem names, `@[step]` where applicable, narrower imports, stable tactics, and removal of
unused declarations. #140 and #326 discussed pure constants; #276 recorded a real type
annotation/elaboration exception. Reviewers also asked authors to keep PRs focused, match issue
references to the actual function, and obtain renewed review after meaningful updates; the
roughly 500-line target was discussed as guidance, with exceptions for coherent larger work.
[#30][30], [#31][31], [#89][89], [#140][140], [#276][276], [#326][326], [#362][362], [#560][560],
[#562][562], [#570][570], [#661][661], [#712][712], [#715][715]

**Reporting.** In #678 an author reply claimed a fix, but the re-review of the updated diff still
found the chain parameters untied to the input; only the next revision resolved it. Recent AI
review comments presented themselves as assistance to human review; the workflow prohibiting
AI-generated specifications is unchanged by this guide. [#678][678], [#714][714], [#715][715]

[30]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/30
[31]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31
[39]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/39
[48]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/48
[55]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/55
[84]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/84
[86]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/86
[89]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/89
[98]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/98
[100]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/100
[140]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/140
[153]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/153
[183]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/183
[200]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/200
[234]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/234
[243]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/243
[247]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/247
[249]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/249
[272]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/272
[276]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/276
[320]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/320
[326]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/326
[362]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/362
[365]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/365
[373]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/373
[389]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/389
[491]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/491
[542]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/542
[546]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/546
[548]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/548
[549]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/549
[550]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/550
[560]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/560
[562]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/562
[566]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/566
[567]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/567
[568]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/568
[570]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/570
[571]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/571
[574]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/574
[576]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/576
[578]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/578
[618]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/618
[619]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/619
[645]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/645
[647]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/647
[654]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/654
[660]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/660
[661]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/661
[662]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/662
[663]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/663
[670]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/670
[676]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/676
[677]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/677
[678]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/678
[683]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/683
[712]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/712
[714]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/714
[715]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/715
[718]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/718
[721]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/721
