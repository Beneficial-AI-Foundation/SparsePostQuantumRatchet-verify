# Repository history and review lessons

The history of `Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify` shows a progression from
Rust extraction and finite-field proofs to serialization, chain state, and protocol-level properties.
Its recurring review lesson is that a compiling Lean proof is only as useful as its statement and
the fidelity of the model it reasons about. Reviewers repeatedly found missing state constraints,
unfaithful external models, overly strong premises, and verification claims broader than the theorem.

This is a snapshot of GitHub history retrieved on **2026-10-23**, covering work items created from
2026-03-18 through 2026-10-23. Use the
[AI PR review questions](AI_PR_REVIEW_QUESTIONS.md) for a practical review procedure, the
[complete catalog](history/GITHUB_HISTORY_CATALOG.md) for every issue, PR, comment, and review,
and the linked GitHub pages for complete source text. The raw JSON snapshot behind the catalog is
not committed to the repository.

## Coverage and status

| Record type | Total | Snapshot status |
| --- | ---: | --- |
| Issues | 405 | 331 closed, 74 open |
| Pull requests | 320 | 296 merged, 13 closed unmerged, 11 open |
| Issue and PR conversation comments | 442 | Includes human discussion and automation |
| Inline PR comments | 414 | Includes replies and historical review comments |
| Submitted PR reviews | 663 | 301 approved, 322 commented, 6 changes requested, 34 dismissed |
| Commit comments | 2 | Both concern the workflow guide |

Review counts count submissions, not unique reviewers or currently approved PRs. Inline comments
are counted separately from their parent reviews. Of the 663 reviews, 83 have nonempty bodies;
empty review bodies still record a review action and may have inline discussion.

All REST collections were paginated. The GraphQL review collection covers the same 320 PRs; each
PR's returned reviews matches its `totalCount`. Each issue/PR's conversation-comment count matches
its retrieved comments. The catalog has one entry for every returned issue/PR and every discussion
record. GitHub numbering reaches #726, but only 725 issue/PR records were returned; #664 was not
returned, and no content or explanation is inferred for that gap.

Scope is this repository, including open, closed, merged, and draft work. It excludes the upstream
Signal repository's independent issue history, Slack/Zulip conversations, deleted or inaccessible
content, comment edit histories, private pending reviews, reactions, and timeline events. Bodies
reflect their latest API-visible versions at retrieval. Collection was paginated rather than atomic.
Linked attachments and external references are not archived. Historical review findings below are
reported as findings made at the time, not as assertions that the current code still has those defects.

## Development history

### March and April 2026

The first extraction and Lean project setup arrived in #1 and #2, followed by early verification,
workflow setup, ownership, and contribution infrastructure. The period created 8 PRs and 3 issues.
The initial focus was making the extracted crate and its proofs build and establishing how changes
would be reviewed. [#1][1], [#2][2], [#3][3], [#8][8], [#9][9]

### May 2026

Work expanded into GF(2¹⁶) arithmetic, reduction, and mathematical foundations. A large arithmetic
PR was closed and split into smaller units. Review of the foundational work asked for reusable
mathematics separate from implementation-specific proofs, useful invariants, existing Mathlib
lemmas, and tracked deferred proofs. Contribution/style rules, sorry auditing, fork-compatible
reporting, warning/lint gates, source consistency, and licensing were developed alongside it.
There were 47 issues and 40 PRs created. [#30][30], [#31][31], [#39][39], [#41][41], [#55][55],
[#81][81], [#89][89], [#95][95]

### June and July 2026

The project built out external models for Rust containers, slices, iterators, and result/option
types, then polynomial arithmetic, interpolation, encoding, and serialization proofs. Review
discovered that plausible Lean models could omit Rust panics, mishandle deque representation, or
misrepresent sorted insertion. HMAC and ML-KEM boundary discussions distinguished minimal useful
contracts from broader cryptographic behavior. Tooling began using Aeneas's `translation.json`
to connect Lean declarations with Rust. The period created 153 issues and 121 PRs.
[#153][153], [#183][183], [#197][197], [#234][234], [#235][235], [#243][243], [#249][249], [#365][365]

### August and September 2026

Verification broadened to public library functions, key history, chain operations, and protobuf
conversion. Reviews became especially concerned with preserving live keys, describing mutated
state, avoiding vacuous predicates, and matching actual caller needs. Serialization work moved
toward pure functional models and round-trip properties. An end-to-end erasure-code refinement
remained draft work; it should not be counted as a merged verification result. The period created
151 issues and 94 PRs. [#491][491], [#503][503], [#508][508], [#542][542], [#550][550], [#557][557],
[#568][568], [#571][571], [#578][578]

### October 2026 through October 23

Major infrastructure changes included Lean's module system, narrower imports, translation patches,
an upstream v1.6.0 update, and extended translation coverage. Braid epoch uniqueness and substantial
ML-KEM work merged, with important qualifications about dependency trust and the relationship
between abstract models and actual externals. Several performance PRs reduced expensive proofs;
eight kernel-computed proofs were temporarily changed to `native_decide`, leaving an explicit
follow-up about trust. Unchunked and chunked state-function proofs continued. The period created
51 issues and 57 PRs. [#574][574], [#651][651], [#656][656], [#657][657], [#658][658], [#660][660],
[#661][661], [#668][668], [#718][718], [#721][721]

## What the discussions established

### Specifications must rule out plausible wrong implementations

Review of key-history garbage collection supplied two concrete counterexamples: deleting every
key, and duplicating a live key while losing another entry. Merely saying that remaining keys are
valid did not capture preservation or multiplicity. Reviews of `recv_key` likewise found that
constraints on returned values and scalar fields left the updated `links` insufficiently
constrained. Initialization review required direction, minimum version, serialized parameters,
and the direction-specific initial state to be tied to the inputs. A later pass caught that
“parameters are present” still permitted the wrong parameters. [#491][491], [#550][550], [#678][678]

Other discussions rejected tautological representability clauses, missing lower bounds on decoder
progress, and hypotheses strong enough to imply `False`. These are reasons to inspect theorem
statements even when proofs compile. [#320][320], [#373][373], [#389][389]

### Handwritten external models need their own fidelity review

The original `clone_from_slice` model ignored destination length and omitted the mismatch panic.
Deque discussions exposed inconsistent choices between physical ring-buffer layout and a logical
list model; a later iterator issue showed nontermination and incorrect output after `pop_front`.
Sorted-set review caught append behavior where replacement was required. Decoder review questioned
a binary-search model that always chose the first match when the Rust behavior required an explicit
uniqueness invariant to justify that choice. [#153][153], [#183][183], [#234][234], [#365][365],
[#618][618], [#619][619], [#683][683]

An especially instructive correction occurred in #272. The issue initially proposed changing an
extracted record update to force `y = ONE`. Later comments explained that the Rust loop preserves
`y`, and that the proposed fix would make the translation unfaithful. They supplied a counterexample
to a loop specification over arbitrary input arrays. The general lesson is to check the source and
the invariant before “repairing” generated code to make a proof work. [#272][272]

### Trust assumptions must remain visible

The workflow discussion settled on `sorry` for intended future proofs, with a linked issue, and
`axiom` for externally justified properties, with a source. Auditing needs to inspect transitive
dependencies, not merely search the edited file for `sorry`. #574's PR body explicitly reported
`sorryAx` inherited through an extraction iterator stub in statements about runs. That historical
qualification should accompany any summary of its no-repeat-epoch result. [#39][39], [#48][48],
[#89][89], [#574][574]

In #661, reviewers questioned moving external behavior into concrete definition bodies, which can
make correspondence lemmas reflexive while hiding the implementation-to-model assumption from an
axiom count. They also questioned end-to-end wording for a round-trip theorem about model functions.
The author described follow-up revisions, including parameterized primitives and revised naming;
this history summary does not certify resolution of every inline finding. Later #718 merged a
temporary switch to `native_decide`; #721 remains open to decide a lasting solution.
[#661][661], [#714][714], [#718][718], [#721][721]

### Serialization requires valid domains and explicit normalization

The zero-polynomial discussion identified serialization to an empty sequence that deserialization
rejects. Participants argued that V1 execution invariants exclude this case; that is a claim about
reachable protocol states, not a universal round-trip theorem for the underlying type. [#566][566],
[#567][567]

#568 and its implementation PRs developed a common architecture: pure functional models, proofs
that extracted conversions implement them, and model-level round trips. Discussion distinguished
decoding an encoded valid state from re-encoding arbitrary accepted protobuf data. The latter may
normalize defaults or discard information, so literal equality requires canonical input or a
normalization statement. Participants also emphasized checking that encoder postconditions imply
decoder preconditions. [#568][568], [#571][571], [#578][578]

### Composition and protocol claims need precise scope

Function contracts need enough information for their callers: interpolation required degree
information, authentication required input/output relationships, and state operations required
frame conditions for unchanged fields. A pure model can make these contracts clearer and easier
to compose than equations between opaque computations. #645 proposes further work in this
direction and is still open; it is not a blanket ban on equational specifications.
[#247][247], [#249][249], [#546][546], [#550][550], [#645][645]

The Braid documentation discussion required stating whether a theorem covers one or both parties,
arbitrary or initialized states, and only successful calls. Assuming a call succeeds does not prove
it succeeds. Draft #663 compares receive dispatch with ML-KEM Braid Rev. 1 §2.5 and explicitly
describes three deviations; it remains open. [#576][576], [#662][662], [#663][663]

### Performance and CI evidence need interpretation

Reviews encouraged profiling but also challenged comparisons involving failed builds, changed
benchmark configurations, or apparent noise. Early discussions found that registering a loop lemma
for `step` could sharply increase proof time; later work extracted repeated proof arguments and
reduced import cost. Current profiling documentation uses `!radar`, whereas the older reviewer
guide still mentions `!bench`. [#98][98], [#647][647], [#660][660], [#670][670], [#718][718],
[Performance guide](PERFORMANCE.md)

Infrastructure history includes required checks that did not run for PRs, fork-token failures,
duplicate runs, lint errors missed by text matching, and caches saved before the build they were
supposed to cache. A green check is useful only if the intended command ran on the intended revision
and its failure status was preserved. [#55][55], [#84][84], [#86][86], [#100][100], [#548][548],
[#549][549], [#676][676], [#677][677]

### Maintainability and review process are recurring concerns

Reviewers repeatedly requested shared helpers and instances, source-aligned file placement,
accurate docstrings, discoverable theorem names, `@[step]` where applicable, narrower imports,
stable tactics, and removal of unused declarations. They also asked authors to keep PRs focused,
match issue references to the actual function, and obtain renewed review after meaningful updates.
The roughly 500-line target was discussed as guidance, with exceptions for coherent larger work.
[#30][30], [#31][31], [#89][89], [#276][276], [#362][362], [#560][560], [#562][562], [#570][570],
[#661][661], [#712][712], [#715][715]

The current workflow prohibits AI-generated specifications and allows AI-generated proofs under
human responsibility. Recent AI review comments explicitly presented themselves as assistance to
human review. Use the generated question guide to inspect and challenge proposed changes; it does
not change the contribution policy. [Workflow guide](WORKFLOW_AND_PR_GUIDE.md), [#714][714], [#715][715]

## Open work at the snapshot

There are 74 open issues, including overlapping umbrella issues and individual tasks. They are
not 74 independent missing theorems. The complete open-work list is in the
[catalog index](history/GITHUB_HISTORY_CATALOG.md#open-work-index).

| Area | Open work and relevant history |
| --- | --- |
| Trust and proof cost | #721 tracks the eight temporary `native_decide` proofs; #48 compares auditing approaches. |
| Public API and state machine | #434 (`send`), #623 (`recv`), #622 (closure), #662 (dispatch), and umbrella #44. |
| Serialization | #568 and remaining harmonization tasks, especially chunked states and encoder/decoder pairs. |
| Chunked and unchunked functions | #685 and #693 organize remaining state operations; individual tasks include #688, #690, and #696–#710. |
| Contracts and models | #645 proposes compositional contracts; #248 tracks `from_seed` behavior; #245 considers HMAC generalization. |
| Organization and tooling | #43 coverage catalog, #281 elaboration problem, #364 instance consolidation, #659 import reduction. |

The eleven open PRs are #277 (draft ML-KEM external models), #304 (Rustdoc verification panels),
#407 (draft iterator proof reuse), #503 (draft erasure-code refinement), #643 (draft encapsulation
contract), #663 (draft receive dispatch), #719 (`recv_ct2`), #723 (`send_ct2_chunk`), and
#724–#726 (chunked-state epoch functions). Their exact titles and discussions are in the catalog.

Some trackers may need reconciliation: #587 remains open despite merged #680 covering the named
harmonization task; #702 remains open while merged #712 addresses the named `send_ct1` function.
Treat these as candidates for human tracker review, not automatic evidence of missing proofs or
authorization to close issues. [#587][587], [#680][680], [#702][702], [#712][712]

## How to use the record

For a new PR, start with its changed layer: mathematical foundations, extracted functions,
handwritten externals, serialization, protocol properties, or tooling. Read the matching historical
discussion, then check the current diff and current policy. Earlier proposals, closed unmerged
PRs, author replies, and historical approvals are context rather than substitutes for inspection.
The catalog deliberately retains these distinctions and the full text snapshot preserves the
arguments behind the short excerpts.

[1]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/1
[2]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/2
[3]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/3
[8]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/8
[9]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/9
[30]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/30
[31]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31
[39]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/39
[41]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/41
[48]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/48
[55]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/55
[81]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/81
[84]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/84
[86]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/86
[89]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/89
[95]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/95
[98]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/98
[100]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/100
[153]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/153
[183]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/183
[197]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/197
[234]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/234
[235]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/235
[243]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/243
[247]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/247
[249]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/249
[272]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/272
[276]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/276
[320]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/320
[362]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/362
[365]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/365
[373]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/373
[389]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/389
[491]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/491
[503]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/503
[508]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/508
[542]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/542
[546]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/546
[548]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/548
[549]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/549
[550]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/550
[557]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/557
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
[587]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/587
[618]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/618
[619]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/619
[645]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/645
[647]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/647
[651]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/651
[656]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/656
[657]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/657
[658]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/658
[660]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/660
[661]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/661
[662]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/662
[663]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/663
[668]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/668
[670]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/670
[676]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/676
[677]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/677
[678]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/678
[680]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/680
[683]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/683
[702]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/702
[712]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/712
[714]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/714
[715]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/715
[718]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/718
[721]: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/721
