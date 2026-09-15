<!--
Provenance
  reviewer:   Codex CLI (OpenRouter), cross-engine (not the planning engine)
  effort:     model_reasoning_effort = high
  sandbox:    read-only (bwrap, kernel-enforced)
  rubric:     docs/rubrics/spqr-plan-review.md (appended verbatim to the prompt)
  prompt:     /tmp/phase01-review-assignment-3.md
  raw output: /tmp/phase01-codex-review-3.md
  log:        /tmp/phase01-codex-review-3-log.txt
  date:       2026-09-15
  phase:      01-gates-provenance-and-target-list (plans 01-01 .. 01-09)
  branch:     la/spec-catalog @ d7cf202, working-tree revisions reviewed
  round:      3 (round 1 = 01-CODEX-REVIEW.md, REJECT; round 2 = 01-CODEX-REVIEW-2.md, APPROVE-WITH-EDITS)
  note:       The Codex review below is verbatim and never edited. Planning-seat
              triage is appended after the --- separator.
-->

# SPQR Plan Review

- Phase: 01 — Gates, Provenance and the Reviewed Target List
- Plans reviewed: `01-01-PLAN.md` through `01-09-PLAN.md`, as one set, in `.planning/phases/01-gates-provenance-and-target-list/`
- Date: 2026-09-15
- Branch/base verified: `la/spec-catalog`, HEAD `d7cf202a02c69ddc7d33f4c870293199b3f36cd6`; pinned source `d47083cd3abf2906229efa38ae2bfb1121498af0`. Working-tree revisions reviewed. Local `origin/main` is now `995436c44a27f8543812fea9e0b0bffb405d546c`, not the source pin.
- VERDICT: REJECT

## Findings

Phase-local filenames below are relative to `.planning/phases/01-gates-provenance-and-target-list/`. The missing deliverables are not findings. The problems concern their specified statements, interfaces and execution order.

### F-1 — MAJOR

**Claim:** STRUCT-02 conflates different inverse properties and commits to a wire-format characterisation contradicted by the decoder and serializer.

**Evidence:** `01-07-PLAN.md:113` equates uniqueness of a value whose serialization prefixes a buffer with injectivity of `deserialize`; `01-07-PLAN.md:116` then specifies equality of decoded results **iff** the inputs differ only by non-minimal varint padding.

These are different properties, and the proposed characterisation misses actual behaviours:

- The serializer discards the Boolean in `Ct1Ack`: `src/v1/chunked/states/serialize.rs:124`, `src/v1/chunked/states/serialize.rs:226`. The decoder always reconstructs `Ct1Ack(true)`, at `src/v1/chunked/states/serialize.rs:267`.
- Trailing bytes are explicitly accepted, at `src/v1/chunked/states/serialize.rs:274`.
- The actual decoded result contains the consumed-byte cursor, not merely `(message, index)`: `SrcTranslated/Funs.lean:14163`.
- Ten-byte varints truncate to 64 bits, rather than accepting only zero-extension padding: `Spqr/Specs/V1/Chunked/States/Serialize/DecodeVarint.lean:44` and `SrcTranslated/Funs.lean:14048`.

Hand traces, with hexadecimal byte strings and successful Rust results corresponding to outer Lean `ok (.Ok …)`:

| Input or operation | Result | Consequence |
|---|---|---|
| Serialize epoch `1`, index `0`, payload `Ct1Ack(false)` | `01 01 00 04` | Same serialization as `Ct1Ack(true)` |
| Deserialize `01 01 00 04` | `(Message(1, Ct1Ack(true)), 0, 4)` | The unrestricted message roundtrip is false |
| Deserialize `01 01 00 00` | `(Message(1, None), 0, 4)` | Baseline |
| Deserialize `01 01 00 00 FF` | `(Message(1, None), 0, 4)` | Equal complete results without any varint-padding difference |
| Deserialize `01 81 00 00 00` | `(Message(1, None), 0, 5)` | Varint padding changes the complete result’s cursor |

There is also a same-length varint collision: the ten-byte blocks `81 [80 × 8] 00` and `81 [80 × 8] 02` both decode to `1`, because the latter adds `2^64` before truncation. This is not merely adding zero-valued padding.

The existing component theorem explicitly records both nonzero epochs and `Ct1Ack`’s Boolean restriction: `Spqr/Specs/V1/Chunked/States/Serialize/Message/Deserialize.lean:65`. Consequently, the unrestricted roundtrip advertised in `docs/spqr-properties.md:243` also needs a domain qualification. Plan 01-07 currently forbids that accompanying correction, at `01-07-PLAN.md:159`.

Finally, the prescribed Rust citation ends at line 256 (`01-07-PLAN.md:124`), excluding the payload reconstruction and trailing-data behaviour that refute the statement. ML-KEM Braid §2.3 does not supply the missing byte-level contract.

**Minimal suggested edit:** Re-specify the reviewed obligation before dispatch: identify the valid message domain, successful-decoding domain, treatment of suffixes and consumed cursors, and the actual varint equivalence relation. Expand the cited source to cover the relevant implementation. Authorize the corresponding PROP-35 qualification and index synchronization in the same PR.

**Non-binding alternative:** Make the first new obligation a precise non-injectivity witness rather than an unbounded “iff” characterisation, subject to an explicit scope ruling.

### F-2 — MAJOR

**Claim:** STRUCT-04’s universal `States.into_pb` injectivity statement is false without a state invariant.

**Evidence:** `01-07-PLAN.md:134` quantifies over all `States`. The extracted type imposes no decoder-size invariant: `SrcTranslated/Types.lean:919` gives `PolyDecoder.pts_needed : Usize`.

Serialization narrows that field to `u32`:

- `src/encoding/polynomial.rs:795`: `pts_needed: self.pts_needed as u32`.
- `SrcTranslated/Funs.lean:9346`: `UScalar.cast .U32 self.pts_needed`.
- The existing serialization theorem therefore requires `self.pts_needed.val ≤ U32.max`, at `Spqr/Specs/Encoding/Polynomial/PolyDecoder/IntoPb.lean:289`.

This decoder is embedded unchanged through `NoHeaderReceived.into_pb`, at `SrcTranslated/Funs.lean:10712`, and then through `States.into_pb`, at `SrcTranslated/Funs.lean:10723`.

Concrete counterexample on the permitted 64-bit `usize` platform:

| Field | State A | State B |
|---|---|---|
| Variant | `NoHeaderReceived` | `NoHeaderReceived` |
| Unchunked state | Same epoch and authenticator | Same epoch and authenticator |
| Decoder point sets | Sixteen empty sets | Sixteen empty sets |
| Decoder `is_complete` | `false` | `false` |
| Decoder `pts_needed` | `48` | `48 + 2^32` |
| Serialized decoder `pts_needed` | `48` | `48` |
| Remaining serialized fields | Identical | Identical |

Both serialization paths succeed on these small collections and produce the same protobuf value, although the states differ. This counterexample does not depend on a prost `sorry`.

The related universal roundtrip in `docs/spqr-properties.md:419` also lacks a valid-state hypothesis. Moreover, the per-variant decoder checks the expected size, not merely representability: `src/v1/chunked/send_ct/serialize.rs:18` requires the header decoder’s `pts_needed` to be `48`.

Calling encoder injectivity the “converse” of a decoder-after-encoder roundtrip is also inaccurate: encoder injectivity is a consequence of a left-inverse law, not byte/protobuf canonicity.

**Minimal suggested edit:** Specify the invariant under which this property is intended—covering representability, variant-specific decoder sizes and necessary collection invariants—and formulate equality of successful encoding values. Include the polynomial serialization path in the review evidence. Correct PROP-37’s corresponding domain in the same PR, and distinguish encoder injectivity from decoder canonicity.

### F-3 — MAJOR

**Claim:** The provenance checker’s catalog identity/count contract cannot satisfy its consumers and omits a new property heading.

**Evidence:** `01-02-PLAN.md:255` requires enumeration of PROP/LEAN headings plus every ID-bearing row in §10 and §11. `01-03-PLAN.md:181` requires that count to equal the §12 index length, allegedly 39.

The actual working-tree counts are:

```text
Catalog headings:          28
Section 10 property rows:   9
Deviation rows:             5
Index entries:            38
```

Thus the specified enumeration yields **42**, while the index contains **38**, because §12 represents D1–D5 as one aggregate entry (`docs/spqr-properties.md:490`). Even excluding individual deviations leaves 37 properties, not 39.

The subsequent mutations worsen the mismatch:

- STRUCT-02 is a new §6 heading, but the enumerator only specifies PROP/LEAN headings (`01-07-PLAN.md:110`; `01-02-PLAN.md:255`).
- The second §11 table adds another five ID-bearing D rows without Source fields (`01-08-PLAN.md:105`), which the prescribed enumeration would treat as additional rows requiring provenance.
- Literal `grep -c 'Source:'` checks do not reliably count fields represented by a table’s `Source` column (`01-03-PLAN.md:147`, `01-03-PLAN.md:180`).

These are identity/schema defects, not merely an off-by-one threshold.

**Minimal suggested edit:** Define one normalized property/deviation ID registry, including STRUCT IDs and explicit handling of the aggregate D1–D5 index entry. Join decision-table rows to existing deviation records rather than enumerating them twice. Require exact normalized ID-set agreement with the index, and validate Source fields through the parser rather than literal-token counts.

### F-4 — MAJOR

**Claim:** Plan 01-07 requires a provenance citation that the fail-closed checker is expressly required to reject.

**Evidence:** The only accepted forms in `01-02-PLAN.md:260` are ML-KEM Braid sections, SCKA definitions/figures, and `src/` Rust ranges; unrecognized forms must fail, at `01-02-PLAN.md:268`.

Nevertheless, `01-07-PLAN.md:124` mandates:

```text
Source: src/v1/chunked/states/serialize.rs:221-256;
Spqr/Specs/V1/Chunked/States/Serialize/DecodeVarint.lean:43
```

The second citation is outside all three forms. `01-03-PLAN.md:80` explicitly says every listed citation must resolve; one valid Rust citation therefore cannot rescue it. Plan 01-07 nevertheless requires gate 5 to pass, at `01-07-PLAN.md:152`.

The single/multiple-citation grammar also needs reconciliation with `.planning/REQUIREMENTS.md:21`; it cannot remain an implicit executor choice.

**Minimal suggested edit:** Keep primary PROV-01 citations within the accepted source classes and put Lean corroboration in a distinct evidence field. Specify the list delimiter and all-citations validation rule consistently across the requirement, checker, retrofit and review skill. Do not make this example pass by weakening rejection of unknown forms.

### F-5 — MAJOR

**Claim:** Two mandatory workflows consume deliverables before their producers are ordered to supply them.

**Evidence:**

1. Plans 01-02 and 01-03 both declare wave 1 and no dependencies (`01-02-PLAN.md:5`, `01-03-PLAN.md:5`). Yet 01-03 must read and run the checker produced by 01-02 (`01-03-PLAN.md:144`, `01-03-PLAN.md:177`). Conversely, 01-02 must demonstrate failure **before** 01-03 adds Source fields (`01-02-PLAN.md:288`). A legal parallel execution can violate either obligation.

2. The statement-review skill must stop unless its property is already a target in `docs/proof-targets.md` (`01-06-PLAN.md:258`). Plan 01-06 populates that table from the existing catalog. Plan 01-07 task 1 adds the new rows only to `docs/spqr-properties.md` (`01-07-PLAN.md:97`), then task 2 immediately invokes the skill (`01-07-PLAN.md:175`). Its only explicit target-table update is **after ACCEPT**, at `01-07-PLAN.md:184`. The new IDs therefore lack a specified registration step before the mandatory lookup.

**Minimal suggested edit:** Order 01-03 after 01-02’s checker and pre-retrofit negative control, then recompute dependent waves. Register and classify the two new candidate rows before invoking their reviews; distinguish “selected candidate” from “review accepted.”

### F-6 — MAJOR

**Claim:** The selection and review eligibility rules exclude open halves and support work that the project explicitly permits.

**Evidence:** `.planning/PROJECT.md:26` says partially proved rows qualify for their open half. But `01-06-PLAN.md:139` assigns them `C1 = partial`, while `01-06-PLAN.md:144` permits `Target? = yes` **only if all three criteria pass**. No rule turns the named open half into an eligible target.

PROP-35 is a concrete affected row: its component theorems exist, but its composed roundtrip is open (`docs/spqr-properties.md:235`). The target list must describe that open obligation rather than reject the entire partially proved row.

There is a related support-work dead end. `.planning/PROJECT.md:43` permits excluded-band support lemmas to be proved when a target needs them. The skill refuses every non-target (`01-06-PLAN.md:258`), while the checklist requires an ACCEPT before property proof work (`01-01-PLAN.md:119`). No support-review route is specified.

The “22 targets” figure also counts work units rather than a simple set of catalog rows: `.planning/REQUIREMENTS.md:172` includes three axiom-removal obligations, while PROP-47 spans two refinement requirements. The plan legitimately allows count disagreements to be reported, but its table still needs an explicit representation of those units.

**Minimal suggested edit:** Make eligibility operate on named open obligations within rows; permit an open-half C1 pass. Define how support statements receive review without being promoted to phase targets. Represent split and non-row obligations explicitly when reconciling the target count.

### F-7 — MAJOR

**Claim:** The statement-review demonstration does not specify the actual Lean statement packet whose acceptance and hash it promises to record.

**Evidence:** The rubric/log contract requires a proposed Lean statement verbatim, as it will appear in the file, with a SHA of that exact text (`01-06-PLAN.md:189`, `01-06-PLAN.md:219`).

Plan 01-07 task 1 supplies prose questions and Rust-style expressions, not complete Lean declarations. Task 2 says the assignment is assembled from the Source field and catalog text (`01-07-PLAN.md:178`). The skill accepts property IDs, but no specified statement argument or statement-record location (`01-06-PLAN.md:253`).

This matters concretely:

- `States.into_pb` returns `Result V1State`, not a plain protobuf value (`SrcTranslated/Funs.lean:10723`).
- `Message.deserialize` returns nested results and a cursor (`SrcTranslated/Funs.lean:14163`).
- Necessary domain predicates are absent, as F-1/F-2 demonstrate.

Hashing the prose would not identify the eventual theorem statement or its hypotheses.

The packet also gives the reviewer only the cited source while demanding a C1 ruling about existing theorems on `main` (`01-06-PLAN.md:191`, `01-06-PLAN.md:201`). It does not define how the reviewer obtains that independent novelty evidence.

**Minimal suggested edit:** Require a complete proposed Lean declaration, including relevant namespace/type/hypothesis context, stored in a named Markdown statement record if Lean files must remain untouched. Specify how the skill selects and hashes it. Define the permitted pinned declaration/signature evidence for C1 and type checking without exposing neighboring catalog arguments or the proposed proof; missing evidence must prevent ACCEPT.

### F-8 — MAJOR

**Claim:** The CLAUDE.md preservation gates require a marker count incompatible with the current file.

**Evidence:** Plans 01-01 and 01-06 repeatedly require exactly eight `GSD:` marker lines while forbidding restructuring of the marked blocks (`01-01-PLAN.md:178`, `01-01-PLAN.md:183`, `01-06-PLAN.md:286`).

The read-only probe gives:

```text
grep -c 'GSD:' CLAUDE.md
14
```

The seven existing pairs are project, stack, conventions, architecture, skills, workflow and profile; see `CLAUDE.md:1`, `CLAUDE.md:55`, `CLAUDE.md:65`, `CLAUDE.md:75`, `CLAUDE.md:83`, `CLAUDE.md:92`, `CLAUDE.md:107`.

Preserving them cannot satisfy the required count. Furthermore, `CLAUDE.md:89` already contains the statement-review skill row that `01-06-PLAN.md:282` and `01-06-PLAN.md:297` require adding.

**Minimal suggested edit:** Validate preservation of the existing named marker pairs, rather than the stale count of eight. Update the already-advertised skill row in place instead of requiring another row.

### F-9 — MAJOR

**Claim:** The final validation contract still contains partial and nonexistent command paths that cannot establish the promised five-gate boundary result.

**Evidence:** This reintroduces the incomplete-boundary-check problem from **round 1, F-7**.

- Plan 01-09’s final record command is bare `./scripts/check-gates.sh` (`01-09-PLAN.md:77`).
- `01-VALIDATION.md:48` explicitly says a bare invocation skips gate 4 and **may not** be cited as a boundary check.
- Plan 01-02 says SKIP counts as failure, not success (`01-02-PLAN.md:124`).
- The validation quick/full suite commands still require the removed `scripts/create-property-issues.sh` (`01-VALIDATION.md:37`), despite the re-scope dropping that deliverable.
- `01-VALIDATION.md:5` already sets `nyquist_compliant: true`, whereas the wrapped-control instructions say the flags remain false without the required evidence (`01-VALIDATION.md:153`; `01-04-PLAN.md:284`).

The mandatory wrapped-list control itself is now properly non-waivable; **round-2 F-6’s control wording is repaired**. The remaining defect is the inconsistent completion/validation interface.

**Minimal suggested edit:** Give every boundary invocation explicit axiom targets; synchronize no-target/SKIP handling across the runner and validation contract. Remove issue-script commands from the active validation paths. Assign an owner for validation-state updates and leave evidence-dependent flags unset until their stated conditions hold.

### F-10 — MAJOR

**Claim:** PR B’s head branch is still conflated with its base, leaving the two-PR reporting contract incomplete.

**Evidence:** This is the remaining head/base portion of **round-1 F-4 and round-2 F-1**.

The repaired guard correctly defines `PR B branch:` as the branch **on which PR B commits are made** (`01-05-PLAN.md:136`, `01-06-PLAN.md:79`). That is the head branch.

But `01-09-PLAN.md:104` instructs the user to open PR B **based on** that same branch. Its diff command separately expects a `<PR B base>` recorded in the earlier summary (`01-09-PLAN.md:80`), although 01-05’s required recorded fields do not distinguish a B head from a B base (`01-05-PLAN.md:154`).

Using the verified B head as `<PR B base>` makes `<base>...HEAD` empty and can falsely certify both the change set and frozen-path check.

The base assumptions also need remeasurement, not literal reuse. Plan 01-05 asserts an empty `origin/main..HEAD` Lean diff (`01-05-PLAN.md:115`), but the current probe returns:

```text
Spqr.lean
Spqr/Specs/Chain/Chain/EpochIdx.lean
Spqr/Specs/Chain/Chain/New.lean
```

Local `origin/main` is `995436c`, whose latest commit adds the epoch-index specification. The working-tree code still matches `d47083c`; upstream movement is not a Phase 1 code-freeze violation.

**Minimal suggested edit:** Record PR A and PR B head/base refs separately, with fixed reporting SHAs. Use the B head for the branch guard and B base for the PR target and range checks. Include PR A’s completed summary commit when defining a stacked base, and remeasure current ancestry without “repairing” immutable code to satisfy a stale diff assertion.

### F-11 — MINOR

**Claim:** Several required writes remain absent from their plans’ declared file maps.

**Evidence:** This recurs from the undeclared-write portion of **round-2 F-5**, although the previous README same-wave collision is resolved.

- Plan 01-07 produces `docs/statement-reviews/<ID>-<n>.md` (`01-07-PLAN.md:180`), but those artifacts are absent from its frontmatter and task file lists (`01-07-PLAN.md:7`, `01-07-PLAN.md:168`).
- Plan 01-06 conditionally requires updates to REQUIREMENTS and ROADMAP (`01-06-PLAN.md:329`) without declaring them.
- Plan 01-07 likewise conditionally updates REQUIREMENTS and ROADMAP (`01-07-PLAN.md:249`) without declaring them.

These omissions obscure the actual PR scope and executor write permissions; they are not merely prose formatting.

**Minimal suggested edit:** Declare the append-only review artifact family and conditional planning-record writes in the owning plans. Keep the maps synchronized with any additional same-PR catalog corrections required by F-1/F-2.

## Cleared surfaces

### 1. Catalog fidelity

The D1 and D5 implementation readings survive independent source inspection:

- ML-KEM Braid §2.2 specifies KDF_AUTH with root-key salt and update-key IKM. Rust instead uses zero salt and concatenated IKM, at `src/authenticator.rs:44`. The existing `update_spec` states that implemented behaviour and includes its memory-size hypothesis, at `Spqr/Specs/Authenticator/Authenticator/Update.lean:48`. Plan 01-08 preserves the theorem and explicitly routes disagreement to a finding.
- ML-KEM Braid §2.4 prescribes abandoning the session after verification failure. The library’s public error is `MacVerifyFailed`, at `src/lib.rs:145`; it does not implement that session-abandonment policy. The revised D5 wording correctly distinguishes this.
- The two new rows do not survive fidelity review as written; F-1/F-2 identify concrete counterexamples and the corresponding existing-row corrections.

### 2. Internal consistency

The declared README ownership now separates 01-02 and 01-04 into different dependent waves, repairing the particular overlap from round 2. The PR B branch guard also now prevents an unanswered “skip” from silently authorizing work on an unnamed branch.

No new Lean module is committed by this phase, so no new `Spqr.lean` export is missing from its file maps. The checker/retrofit dependency and new-row registration order remain defective under F-5.

### 3. Statement-level soundness

The relevant extracted interfaces were read, not inferred from Rust notation:

- `States.into_pb : States → Result V1State`.
- `Message.deserialize : Vec U8 → Result (core.result.Result (Message × U32 × Usize) Error)`.
- `Message.deserialize_spec` requires a buffer-size bound and records nonzero epochs and `Ct1Ack(true)`.
- `PolyDecoder.into_pb_spec` requires a non-truncating `pts_needed` cast.

No theorem elaboration or proof attempt was performed. F-1/F-2 concern hand-traceable counterexamples and missing hypotheses, not guessed proof difficulty.

### 4. Semantic closure

The D5 failure trace is consistent with both Rust and extraction, conditioned on successful preceding decoding/KEM/KDF operations:

| Step | Local authenticator | Caller’s serialized input | Outcome |
|---|---|---|---|
| Decode caller state | `A` | `S` | Local state obtained |
| Derive epoch secret | `A` | `S` | Local key material obtained |
| Update authenticator | `A′` | `S` | Local update only |
| Ciphertext MAC fails | `A′` | `S` | Error propagates |
| Return to caller | Updated local value not returned | `S` unchanged | `MacVerifyFailed`; no returned state/key |

Sources: `SrcTranslated/Funs.lean:13241`, `SrcTranslated/Funs.lean:13248`, `src/lib.rs:356`, `src/lib.rs:425`, `src/lib.rs:438`. Header verification instead precedes construction of the next state, at `SrcTranslated/Funs.lean:13585`. Dropping the local value is not evidence of zeroization.

The terminal epoch transition also preserves D2’s necessary exception:

| Step | Party A | Party B | Result |
|---|---|---|---|
| Starting completing pair | `EkSentCt1Received(7)` | `Ct2Sampled(7)` | Assume a valid completing Ct2 |
| A receives completion | `NoHeaderReceived(8)` | `Ct2Sampled(7)` | A returns epoch-7 secret |
| A sends | Unchanged | Unchanged | Epoch 8, payload `None`, no key |
| B receives that message | `NoHeaderReceived(8)` | `KeysUnsampled(8)` | Greater arm succeeds, no key |

Sources: `SrcTranslated/Funs.lean:13251`, `SrcTranslated/Funs.lean:11289`, `SrcTranslated/Funs.lean:13971`. This is not a proof of the full liveness claim.

### 5. Precedent and interface realism

The cited `@[step]` declarations for authenticator update, HKDF, message serialization/deserialization and decoder serialization exist with the relevant signatures. The missing encoder/decoder agreement obligation is correctly distinguished from the existing relational decoder specification.

The local ML-KEM Braid PDF identifies Revision 1, last updated September 26, 2025. The local SCKA paper contains Def. 3.1, Fig. 1’s correctness/security games and Fig. 2’s SCKA-to-messaging construction. No new theorem about those games is authorized here.

The old claim that `origin/main` and the branch have identical Lean trees is no longer current; F-10 records the measured difference.

### 6. Trusted-base discipline

No permanent new axiom, opaque declaration, sorry or native-decision trust is authorized by the phase’s committed changes.

The selected allowlist’s naming repairs survive inspection: external stubs are root-level names, while `spqr.kdf.hkdf_to_slice_spec` is namespaced. The multiline libcrux-1275 declaration exists at `SrcTranslated/FunsExternal.lean:3687`; the revised plan explicitly validates that form, repairing round-2 F-4. The dead bare `initial_state`, `send` and `recv` stubs remain excluded.

No axiom-closure result was certified without execution.

### 7. Gates

The existing build/lint command strings and filters match `.github/workflows/lean.yml:47` and `.github/workflows/lean.yml:57`. The workflow sets `LEAN_ABORT_ON_PANIC: 1`.

`Audit.lean` scans imported modules and writes a fresh manifest; `sorry-diff.py` compares declarations by name and fails on new spec entries only when requested. The plan correctly distinguishes that stricter local policy from CI’s comment-only invocation at `.github/workflows/sorry-delta-comment.yml:43`.

The typo, wrapped-list and malformed-report requirements are substantive and appropriate. Their runtime success remains unverified. F-3/F-4/F-8/F-9 prevent certification of the complete planned gate contract.

### 8. Boundedness and safety

The examined source, extraction, specs, scripts and toolchain files have no diff from `d47083c`. All repository actions during this review were read-only; PDF extraction wrote to stdout.

The plans explicitly prohibit committed Lean/source/extraction changes and confine destructive negative controls to disposable worktrees. No proof work is scheduled before the new-row review. The required statement-domain corrections must not be implemented by changing Rust, extraction or existing merged theorem statements.

### 9. Roadmap and catalog coherence

The new two-PR scope is reflected in the nine plans, and obsolete issue-filing work is no longer a deliverable. Provisional, code-authoritative D1–D5 decisions are supported by the recorded decision at `01-CONTEXT.md:105`, not invented by plan 01-08.

The planned endpoint does not yet satisfy ROADMAP criteria 1–4: the registry and validation interfaces conflict, the target eligibility model rejects permitted work, and the demonstrated review lacks specified typed statements. Criteria 5–6 have a sound overall direction, subject to the marker and validation repairs.

The statement domains and the target/review lifecycle require re-planning before dispatch; this is not merely an implementation cleanup list.

## Probe log

All commands below were read-only. Broad reads sometimes exceeded the tool’s output limit; narrower follow-up reads are included. No build, elaboration, test execution, network mutation, file write, staging or commit was performed.

### Checkout and initial plan reads

Result: confirmed branch, HEAD, pin, staged phase-directory rename and uncommitted revisions. No applicable AGENTS.md was found inside this repository.

```bash
pwd; git status --short; git rev-parse --abbrev-ref HEAD; git rev-parse HEAD; git rev-parse d47083c; rg --files -g AGENTS.md -g '*01*PLAN.md' -g '*REVIEW*' .planning .claude docs scripts; git diff --stat; find .. -name AGENTS.md -print
```

Result: read plans 01-01 through 01-03; followed truncated output with narrower reads.

```bash
for f in .planning/phases/01-gates-provenance-and-target-list/01-0{1,2,3}-PLAN.md; do echo "===== $f"; nl -ba "$f"; done
```

```bash
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-01-PLAN.md
```

```bash
sed -n '100,145{=;p;}' .planning/phases/01-gates-provenance-and-target-list/01-01-PLAN.md; nl -ba .planning/phases/01-gates-provenance-and-target-list/01-02-PLAN.md | sed -n '1,150p'
```

```bash
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-02-PLAN.md | sed -n '35,65p;150,235p'
```

```bash
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-02-PLAN.md | sed -n '236,365p'
```

```bash
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-03-PLAN.md | sed -n '1,175p'
```

Result: read runtime controls and PR A boundary requirements.

```bash
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-04-PLAN.md | sed -n '1,125p'
```

```bash
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-04-PLAN.md | sed -n '126,245p'
```

```bash
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-04-PLAN.md | sed -n '246,365p'; nl -ba .planning/phases/01-gates-provenance-and-target-list/01-05-PLAN.md | sed -n '1,75p'
```

```bash
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-05-PLAN.md | sed -n '75,220p'
```

Result: read target-selection, rubric, skill and checkpoint contracts.

```bash
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-06-PLAN.md | sed -n '1,125p'
```

```bash
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-06-PLAN.md | sed -n '126,245p'
```

```bash
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-06-PLAN.md | sed -n '245,380p'
```

Result: read both new statements and their review workflow.

```bash
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-07-PLAN.md | sed -n '1,135p'
```

```bash
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-07-PLAN.md | sed -n '132,265p'
```

Result: read deviation decisions and final boundary contract.

```bash
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-07-PLAN.md | sed -n '267,300p'; nl -ba .planning/phases/01-gates-provenance-and-target-list/01-08-PLAN.md | sed -n '1,117p'
```

```bash
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-08-PLAN.md | sed -n '118,245p'
```

```bash
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-09-PLAN.md | sed -n '1,150p'
```

### Review history and accepted planning records

Result: located earlier findings and triage, inspected working-tree planning changes, and completed remaining plan excerpts.

```bash
rg -n '^#|^\*\*Claim|^\*\*Minimal|F-[0-9]|Applied|applied|Accept|accept' .planning/phases/01-gates-provenance-and-target-list/01-CODEX-REVIEW{,-2}.md; git diff d7cf202 -- .planning/PROJECT.md .planning/REQUIREMENTS.md .planning/ROADMAP.md .planning/STATE.md CLAUDE.md | head -100; nl -ba .planning/phases/01-gates-provenance-and-target-list/01-09-PLAN.md | tail -8; nl -ba .planning/phases/01-gates-provenance-and-target-list/01-03-PLAN.md | sed -n '103,112p;175,195p'
```

```bash
wc -l .planning/phases/01-gates-provenance-and-target-list/{01-RESEARCH,01-CONTEXT,01-DISCUSSION-LOG,01-VALIDATION,01-CODEX-REVIEW,01-CODEX-REVIEW-2}.md .planning/{PROJECT,ROADMAP,REQUIREMENTS,STATE}.md CLAUDE.md; nl -ba .planning/phases/01-gates-provenance-and-target-list/01-CODEX-REVIEW-2.md | sed -n '1,27p;240,370p'
```

```bash
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-CODEX-REVIEW-2.md | sed -n '660,813p'
```

Result: checked C1/C2/C3, bands, phase criteria, proof definition, target requirements and current CLAUDE.md.

```bash
nl -ba .planning/PROJECT.md | sed -n '1,145p'
```

```bash
nl -ba .planning/ROADMAP.md | sed -n '1,113p'; nl -ba .planning/PROJECT.md | sed -n '72,100p'
```

```bash
nl -ba .planning/ROADMAP.md | sed -n '65,88p'; nl -ba .planning/REQUIREMENTS.md | sed -n '1,102p'
```

```bash
nl -ba .planning/REQUIREMENTS.md | sed -n '24,56p;110,178p'; nl -ba CLAUDE.md | sed -n '1,60p'
```

### Catalog and mechanical counts

Result: read catalog statements, deviation table and index.

```bash
nl -ba docs/spqr-properties.md | sed -n '1,125p'
```

```bash
nl -ba docs/spqr-properties.md | sed -n '126,270p'
```

```bash
nl -ba docs/spqr-properties.md | sed -n '269,396p'
```

```bash
nl -ba docs/spqr-properties.md | sed -n '396,505p'; nl -ba CLAUDE.md | sed -n '70,112p'
```

Result: pinned-code diff empty; 14 GSD markers; 28 prose properties, nine §10 properties, five individual deviations and 38 index entries. Local main differs from the branch in three Lean paths.

```bash
git diff d47083c -- src SrcTranslated Spqr scripts lakefile.toml lean-toolchain Spqr.lean; printf 'GSD markers: '; grep -c 'GSD:' CLAUDE.md; rg -n 'GSD:' CLAUDE.md; printf 'Catalog headings: '; grep -cE '^### (PROP-|LEAN-)' docs/spqr-properties.md; printf 'Section 10 property rows: '; sed -n '410,420p' docs/spqr-properties.md | grep -c '^| PROP-'; printf 'Index entries: '; sed -n '449,491p' docs/spqr-properties.md | grep -cE '^\| (PROP-|LEAN-|D1)'; printf 'Deviation rows: '; sed -n '431,440p' docs/spqr-properties.md | grep -c '^| D'; git ls-tree -r --name-only origin/main -- .planning docs/ISSUE_TEMPLATE.md docs/spqr-properties.md; git rev-parse origin/main; git diff --name-only origin/main..HEAD -- '*.lean' lakefile.toml lean-toolchain lake-manifest.json; rg -n 'axiom|sorry|step|theorem' Spqr/Specs/Authenticator/Authenticator/Update.lean Spqr/Specs/Kdf/HkdfToSlice.lean
```

### Gate implementation and source discovery

Result: located both PDFs under `/tmp/props-review/`; checked existing build/lint commands and workflow configuration.

```bash
rg -n '^#|2026-09-15|Source:|STRUCT|22|partial|C1|C2|C3' .planning/phases/01-gates-provenance-and-target-list/01-RESEARCH.md | tail -95; find /home/lacra /tmp -iname 'mlkembraid*.pdf' -o -iname '*2267*.pdf' 2>/dev/null; nl -ba scripts/check-lint.sh; nl -ba .github/workflows/lean.yml | sed -n '1,95p'
```

Result: inspected live/superseded research framing and Audit’s imported-module selection.

```bash
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-RESEARCH.md | sed -n '1,100p'; nl -ba scripts/Audit.lean | sed -n '1,125p'
```

### Serialization evidence

Result: inspected all relevant Rust wire serialization/deserialization branches and the States protobuf wrapper.

```bash
nl -ba src/v1/chunked/states/serialize.rs | sed -n '1,135p'
```

```bash
nl -ba src/v1/chunked/states/serialize.rs | sed -n '137,312p'
```

Result: confirmed varint truncation predicate, serializer model, decoder hypotheses, cursor and acknowledgment restrictions.

```bash
nl -ba Spqr/Specs/V1/Chunked/States/Serialize/DecodeVarint.lean | sed -n '20,100p'; nl -ba Spqr/Specs/V1/Chunked/States/Serialize/Message/Serialize.lean | sed -n '20,90p'; nl -ba Spqr/Specs/V1/Chunked/States/Serialize/Message/Deserialize.lean | sed -n '15,84p'
```

Result: located extracted interfaces; inspected payload model and protobuf composition; checked target-count accounting.

```bash
rg -n '^def .*Message\.(serialize|deserialize)|^def .*States\.(into_pb|from_pb)|^def .*MessageType\.(from_payload)|^inductive .*MessagePayload|^structure .*Message|^inductive .*States' SrcTranslated/{Funs,Types}.lean; nl -ba Spqr/Specs/V1/Chunked/States/Serialize/Message/Serialize.lean | sed -n '35,77p'; nl -ba src/v1/chunked/send_ek/serialize.rs | sed -n '1,80p'; nl -ba .planning/REQUIREMENTS.md | sed -n '122,178p'
```

### PDFs, decisions and validation

Result: verified the ML-KEM Braid PDF revision/contents and located specification passages and SCKA Def. 3.1.

```bash
pdftotext -f 1 -l 3 /tmp/props-review/mlkembraid.pdf - | head -125; pdftotext /tmp/props-review/mlkembraid.pdf - | rg -n -A8 -B5 'KDF_AUTH|KDFAuth|should not proceed|Ct1Ack|fresh messages|Authenticate|salt'; pdftotext /tmp/props-review/2025-2267.pdf - | rg -n -A15 -B3 'Definition 3.1|Fig. 1:|Fig. 2:' | head -135
```

Result: checked provisional-decision authority, discussion history and current STATE.md.

```bash
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-CONTEXT.md | sed -n '1,125p'; nl -ba .planning/phases/01-gates-provenance-and-target-list/01-DISCUSSION-LOG.md | tail -34; nl -ba .planning/STATE.md | sed -n '45,90p'
```

Result: found obsolete validation commands and inspected manifest comparison semantics.

```bash
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-VALIDATION.md | sed -n '1,95p'; nl -ba scripts/sorry-diff.py | sed -n '1,110p'
```

```bash
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-VALIDATION.md | sed -n '96,189p'; nl -ba scripts/sorry-diff.py | sed -n '105,165p'; nl -ba scripts/Audit.lean | sed -n '1,31p;198,263p'
```

### Extracted types, trusted base and review precedent

Result: confirmed unrestricted message/state constructors and nested result signatures.

```bash
nl -ba SrcTranslated/Types.lean | sed -n '1125,1203p'; nl -ba SrcTranslated/Funs.lean | sed -n '10715,10748p;11415,11492p;14155,14240p'
```

Result: inspected selected allowlist evidence, multiline declaration, authenticator theorem and HKDF axiom.

```bash
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-RESEARCH.md | sed -n '542,623p'; nl -ba SrcTranslated/FunsExternal.lean | sed -n '14,20p;3580,3698p'; nl -ba Spqr/Specs/Authenticator/Authenticator/Update.lean | sed -n '41,58p'; nl -ba Spqr/Specs/Kdf/HkdfToSlice.lean | sed -n '18,32p'
```

Result: inspected sorry exceptions, empirical-probe assumptions and the existing review skill as data.

```bash
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-RESEARCH.md | sed -n '608,624p;1426,1440p'; nl -ba .claude/skills/spqr-plan-review/SKILL.md | sed -n '1,118p'
```

### D1–D5 and repository interfaces

Result: verified zero-salt KDF_AUTH, local update-before-MAC ordering, public error conversion and immutable caller input.

```bash
nl -ba src/authenticator.rs | sed -n '8,56p'; nl -ba src/v1/unchunked/send_ek.rs | sed -n '138,172p'; nl -ba src/v1/unchunked/send_ct.rs | sed -n '94,143p'; nl -ba src/lib.rs | sed -n '138,150p;350,359p;415,448p'
```

Result: checked key-emitting arms, dispatch deviations and extracted MAC-failure propagation.

```bash
nl -ba src/v1/chunked/states.rs | sed -n '175,225p;280,322p;348,374p;454,533p'; nl -ba SrcTranslated/Funs.lean | sed -n '13216,13265p;13565,13602p'
```

Result: read script documentation, linter exceptions, Lake configuration, pinned toolchain, related workflow commands and root imports.

```bash
nl -ba scripts/README.md | sed -n '1,155p'; cat scripts/nolints.json; cat lakefile.toml; cat lean-toolchain; nl -ba .github/workflows/sorry-delta-comment.yml | sed -n '30,60p'; rg -n 'run:|working-directory:|src/|SrcTranslated|lake|push|workflow' .github/workflows/{aeneas,src-diff}.yml; rg -n 'Serialize.Message|HkdfToSlice|Authenticator.Update|States.Send|States.Recv|Chain.Chain' Spqr.lean
```

### Protobuf counterexample and final cross-checks

Result: located decoder-size casts and inspected polynomial/state serialization paths; checked the final negative-control contract.

```bash
rg -n 'struct PolyEncoder|struct PolyDecoder|fn into_pb|fn from_pb|pts_needed|next_point' src/encoding/polynomial.rs; nl -ba src/encoding/polynomial.rs | sed -n '659,766p'; nl -ba src/v1/unchunked/send_ek/serialize.rs | sed -n '1,45p'; nl -ba .planning/phases/01-gates-provenance-and-target-list/01-VALIDATION.md | sed -n '144,189p'
```

```bash
nl -ba src/encoding/polynomial.rs | sed -n '742,760p;790,853p'; rg -n '^def encoding.polynomial.PolyDecoder.into_pb|^structure encoding.polynomial.PolyDecoder|^def v1.chunked.states.States.recv|^def v1.chunked.states.States.send' SrcTranslated/{Funs,Types}.lean; nl -ba src/v1/chunked/send_ct/serialize.rs | sed -n '1,30p'; nl -ba Spqr/Specs/Encoding/Polynomial/PolyDecoder/IntoPb.lean | sed -n '1,95p'
```

Result: confirmed the cast in extraction and the existing theorem’s `h_cast` hypothesis.

```bash
nl -ba SrcTranslated/Types.lean | sed -n '912,928p'; nl -ba SrcTranslated/Funs.lean | sed -n '9340,9361p;10705,10718p;11280,11320p;14066,14114p;14275,14297p'; rg -n -A35 '^theorem.*into_pb|^theorem into_pb_spec|hcast|pts_needed' Spqr/Specs/Encoding/Polynomial/PolyDecoder/IntoPb.lean | tail -62; nl -ba src/v1/chunked/send_ct/serialize.rs | sed -n '8,34p'
```

Result: inspected template/rubric, confirmed main’s new epoch-index commit, rechecked frozen paths and located the head/base conflation.

```bash
nl -ba docs/ISSUE_TEMPLATE.md | sed -n '1,38p;85,127p'; nl -ba docs/rubrics/spqr-plan-review.md | sed -n '1,118p'; git log -3 --oneline origin/main; git status --porcelain -- src SrcTranslated '*.lean'; rg -n 'branch:|base|implementation tip' .planning/phases/01-gates-provenance-and-target-list/01-0{5,6,9}-PLAN.md
```

Result: confirmed platform-dependent Usize width; read chain/KEM source excerpts and extracted varint arithmetic.

```bash
rg -n '^def cast|theorem cast_val_eq|Usize.*numBits|usize.*64|def numBits' .lake/packages/aeneas/backends/lean/Aeneas/Std/Scalar* .lake/packages/aeneas/backends/lean/Aeneas/Std/**/*.lean | head -45; nl -ba src/chain.rs | sed -n '350,383p'; nl -ba src/incremental_mlkem768.rs | sed -n '10,38p;62,88p'; nl -ba SrcTranslated/Funs.lean | sed -n '14004,14046p'; nl -ba .planning/phases/01-gates-provenance-and-target-list/01-CONTEXT.md | sed -n '103,110p;127,148p'
```

Result: rechecked specification passages, statement-packet requirements, allowlist declaration names and table-check precedent.

```bash
pdftotext -layout /tmp/props-review/mlkembraid.pdf - | rg -n -A12 -B3 'KDF_AUTH\(|salt equal|should not proceed|2.3 Messages|3.6 Alternate'; pdftotext -layout /tmp/props-review/2025-2267.pdf - | rg -n -A13 -B3 'Definition 3.1.|Figure 1:|Figure 2:|Figure 16:|Fig. 1\.|Fig. 2\.' | head -90; rg -n 'Statement SHA|sha256|proposed Lean|C1|only' .planning/phases/01-gates-provenance-and-target-list/01-0{6,7}-PLAN.md; rg -n '^axiom (libcrux_hmac|libcrux_ml_kem)' SrcTranslated/FunsExternal.lean | head -25; nl -ba .planning/phases/01-gates-provenance-and-target-list/01-RESEARCH.md | sed -n '1310,1325p'
```

Result: checked recurrence labels against round 1, active validation rows, extracted dispatch/varint operations and working-tree plan scope.

```bash
rg -n '^### F-|^\*\*Claim:' .planning/phases/01-gates-provenance-and-target-list/01-CODEX-REVIEW.md | head -28; nl -ba .planning/phases/01-gates-provenance-and-target-list/01-VALIDATION.md | sed -n '69,80p'; nl -ba SrcTranslated/Funs.lean | sed -n '14044,14059p;13922,13962p'; pdftotext -layout /tmp/props-review/2025-2267.pdf - | rg -n -m 6 'Definition 3.1|Figure 1|Figure 2|Figure 16'; git diff --numstat d7cf202 -- .planning/phases/01-gates-provenance-and-target-list; git status --short | tail -12
```

Result: confirmed Ct2Sampled’s next-epoch exception, read SCKA interface/compiler excerpts and sorry-delta failure semantics. The attempted scalar `Cast.lean` path does not exist; no finding relies on it. Final pinned-code comparison exited 0.

```bash
nl -ba SrcTranslated/Funs.lean | sed -n '13968,13994p'; pdftotext -layout /tmp/props-review/2025-2267.pdf - | sed -n '367,406p;548,578p'; nl -ba .planning/phases/01-gates-provenance-and-target-list/01-03-PLAN.md | sed -n '196,217p'; nl -ba scripts/sorry-diff.py | sed -n '105,143p'; rg -n 'def cast|theorem UScalar.cast_val_eq|def UScalar.cast' .lake/packages/aeneas/backends/lean/Aeneas/Std/Scalar/Cast.lean; git diff --quiet d47083c -- src SrcTranslated Spqr scripts lakefile.toml lean-toolchain Spqr.lean; printf 'Pinned-code comparison exit: %s\n' "$?"
```

## Resolution map

| Finding | Suggested edit | Destination plan/section |
|---|---|---|
| F-1 | Re-specify wire domain, observation and equivalence; correct PROP-35 and expand source evidence | 01-07 task 1; catalog §6/§12; corresponding STRUCT-01/02 wording |
| F-2 | Add a valid-state domain and successful-result formulation; correct PROP-37 | 01-07 task 1; catalog §10/§12; STRUCT-03/04 wording |
| F-3 | Normalize IDs, aggregate deviations and companion tables; check exact ID sets | 01-02 task 3; 01-03 task 2; 01-06 task 1; 01-08 task 1; validation |
| F-4 | Separate primary provenance from Lean corroboration; fix citation-list grammar | 01-02 task 3; 01-03 context; 01-07 task 1; PROV-01 |
| F-5 | Order checker before retrofit; register new candidates before review | 01-02/03 dependencies and waves; 01-07 tasks 1–2 |
| F-6 | Select named open obligations and provide a support-review route | 01-06 tasks 1–3; checklist preconditions; target-count reconciliation |
| F-7 | Specify complete Lean statement records, hashing input and novelty/type evidence | 01-06 tasks 2–3; 01-07 tasks 1–2 |
| F-8 | Preserve existing marker pairs and update the existing skill row | 01-01 task 2; 01-06 task 3 |
| F-9 | Use explicit boundary targets; remove obsolete validation paths; fix evidence flags | 01-02 runner contract; 01-04 validation ownership; 01-09 record commands; 01-VALIDATION |
| F-10 | Separate PR heads/bases and fixed reporting SHAs; remeasure ancestry | 01-05 boundary record; 01-06 branch guard; 01-09 boundary report |
| F-11 | Declare review artifacts and conditional planning-record writes | 01-06/07 frontmatter and task file maps |
---

## 1. Codex's review

**VERDICT: REJECT** — 10 MAJOR, 1 MINOR, no BLOCKER. I re-verified every finding against the
tree before acting; **all eleven are confirmed**. Two of them I had already found independently
while reading the plan set, before Codex returned (F-3 and F-8), and I add one finding of my own
that Codex missed (PS-1).

| # | Sev | Claim | My verification |
|---|-----|-------|-----------------|
| F-1 | MAJOR | STRUCT-02 conflates prefix-uniqueness with `deserialize` injectivity, and its varint-padding characterisation is contradicted by the code | **Confirmed.** `src/v1/chunked/states/serialize.rs:267` always rebuilds `Ct1Ack(true)`, so the Boolean is discarded; `:274-277` explicitly accepts trailing data; the result is `(Message, U32, Usize)` — it carries the cursor; `DecodeVarint.lean:44` truncates with `% 2^64`, so the 10-byte blocks `81 80×8 00` and `81 80×8 02` both decode to `1`. The existing `Message.deserialize_spec` already carries the matching domain restrictions (`0 < msg.epoch.val`, `Ct1Ack b => b = true`) at `Deserialize.lean:65-77` |
| F-2 | MAJOR | STRUCT-04's universal `into_pb` injectivity is false without a state invariant | **Confirmed.** `SrcTranslated/Types.lean:920` has `pts_needed : Std.Usize`; `src/encoding/polynomial.rs:795` narrows it with `as u32`; the existing `into_pb_spec` therefore carries the hypothesis `h_cast : self.pts_needed.val ≤ U32.max` at `Spqr/Specs/Encoding/Polynomial/PolyDecoder/IntoPb.lean:289`. Two states differing by `2^32` in `pts_needed` serialize identically, with no prost `sorry` involved |
| F-3 | MAJOR | The provenance checker's row-identity contract is unsatisfiable and misses `STRUCT-` | **Confirmed independently before reading the review.** 28 `###` headings + 9 §10 rows + 5 §11 rows = **42** enumerable entries; §12 has **38** rows because D1–D5 is one aggregate. The figure "39" in 01-02/01-03 matches neither, and 01-03's "count equal to the §12 index length" cannot ever hold |
| F-4 | MAJOR | 01-07 prescribes a `Source:` citation the fail-closed checker must reject | **Confirmed.** 01-02 admits exactly three forms and must fail on anything unparseable; 01-07 wrote `Source: src/...serialize.rs:221-256; Spqr/Specs/.../DecodeVarint.lean:43` and then required gate 5 to pass |
| F-5 | MAJOR | Two workflows consume deliverables before their producers run | **Confirmed.** 01-02 and 01-03 were both `wave: 1, depends_on: []`, yet 01-03 runs 01-02's checker and 01-02 must observe a pre-retrofit failure. Separately, the review skill stops on a non-target while 01-07 invoked it on two rows whose only target-table write happened *after* ACCEPT |
| F-6 | MAJOR | Eligibility excludes open halves and support work that PROJECT.md permits | **Confirmed.** `PROJECT.md:26` — "Partially proved rows qualify for their open half" — against 01-06's `C1 = partial` plus "`Target?` yes only if all three pass". PROP-35 is exactly such a row and is a Phase 3 target in ROADMAP. The support-lemma review route is likewise undefined |
| F-7 | MAJOR | The review packet is prose, not the Lean statement whose SHA the log records | **Confirmed.** 01-06 requires "the proposed Lean statement verbatim, as it will appear in the file" and a SHA of that text; 01-07 supplies prose questions and the skill takes only property IDs. `States.into_pb` returns `Result V1State` and `Message.deserialize` returns a nested result with a cursor, so the prose is not typeable as written. The reviewer is also asked for a C1 ruling with no evidence about `main` |
| F-8 | MAJOR | The CLAUDE.md marker gate demands a count the file cannot have | **Confirmed independently before reading the review.** `grep -c 'GSD:' CLAUDE.md` = 14 (seven pairs), not 8. And `CLAUDE.md:89` already carries the `spqr-statement-review` row that 01-06 wanted to add |
| F-9 | MAJOR | The validation contract has partial and nonexistent command paths | **Confirmed.** `01-VALIDATION.md:37,38` still invoke `scripts/create-property-issues.sh`, dropped in the re-scope; 01-09's boundary command was a bare `./scripts/check-gates.sh`, which `01-VALIDATION.md:48` forbids citing as a boundary check; `nyquist_compliant` was already `true` with the controls unrun |
| F-10 | MAJOR | PR B's head is conflated with its base, and the "no Lean diff" assertion is stale | **Confirmed.** 01-05 recorded only `PR B branch:` while 01-09 consumed a `<PR B base>` it never defines — using the head makes `<base>...HEAD` empty and vacuously passes the code-freeze check. `git diff --name-only origin/main..HEAD -- '*.lean' …` now returns four files, not empty. *Correction to the finding:* Codex reports `origin/main` as `995436c`; it is `e8f6689` here, which is why it saw three files and I see four. Wrong SHA, right conclusion — and `git diff --name-only d47083c..HEAD -- src` is empty, so the code freeze holds |
| F-11 | MINOR | Required writes missing from declared file maps | **Confirmed.** `docs/statement-reviews/` absent from 01-07's map; the conditional REQUIREMENTS/ROADMAP writes absent from 01-06's and 01-07's |

### Planning-seat finding Codex missed

| # | Sev | Claim |
|---|-----|-------|
| PS-1 | MAJOR | 01-04 task 3 gated on `test -z "$(git stash list)"` and asserted "`git stash list` is empty — no breakage was parked in a stash". **This machine has five pre-existing stashes**, none related to this phase (`stash@{0}`…`stash@{4}`, oldest from `la/add_props_cov`). The gate could never pass, and the obvious way for an executor to make it pass is to drop the user's stashes. A verification gate must not be satisfiable by destroying user work |

## 2. What I did in response

Applied to the plan files, all mechanical corrections that no pending user ruling changes:

- **PS-1** — `01-04-PLAN.md`: the gate now records `STASH_BASELINE=$(git stash list | wc -l)`
  before the first control and compares against it, so the check is "no *new* stash". Added an
  explicit prohibition on dropping, popping or clearing a pre-existing stash.
- **F-8** — `01-01-PLAN.md`, `01-06-PLAN.md`: replaced both `grep -c 'GSD:' … = 8` assertions
  with a loop checking the seven marker pairs by name (`project`, `stack`, `conventions`,
  `architecture`, `skills`, `workflow`, `profile`). 01-06 task 3 now **updates** the existing
  `spqr-statement-review` row at `CLAUDE.md:89` in place instead of adding a duplicate.
- **F-9** — `01-VALIDATION.md`: `nyquist_compliant` set back to `false` with a `flag_owner`
  naming plan 01-04 task 3 as the only thing that may flip it; both `create-property-issues.sh`
  invocations removed from the quick and full suite commands; "all four gates" corrected to
  five. `01-09-PLAN.md`: the boundary command now passes an explicit `#print axioms` target and
  states that only `ALL GATES PASSED` discharges a boundary.
- **F-10** — `01-05-PLAN.md` now records `PR B head:` and `PR B base:` as two separate literal
  lines, and its stale "the Lean diff is empty" assertion is replaced by a
  re-measure instruction that records what the command actually returns today and states that
  the four differing files are upstream commits, not Phase 1 edits. `01-06-PLAN.md`'s guard
  reads `PR B head:`; `01-09-PLAN.md` reads `PR B base:` and says why the head would make the
  range empty.
- **F-5** — `01-03-PLAN.md` moved to `wave: 2, depends_on: ["01-02"]`; 01-04→3, 01-05→4,
  01-06→5, 01-07→6, 01-08→7, 01-09→8. `01-07-PLAN.md` task 1 now registers both new rows in
  `docs/proof-targets.md` with `Target? = candidate` before task 2 invokes the review, and the
  skill in `01-06-PLAN.md` accepts `candidate` as sufficient to proceed.
- **F-3** (mechanical half) — `01-02-PLAN.md` task 3 now builds a **normalised ID registry**
  that includes `### STRUCT-` headings, joins a deviation ID appearing in both §11 tables into
  one entry, and checks **ID-set agreement** with §12 rather than count equality, with a floor
  of 37 non-deviation entries as the backstop. The measured 42-vs-38 figures and the reason they
  differ are written into the plan. `01-03-PLAN.md`'s unsatisfiable criterion is replaced;
  its `grep -c 'Source:' … -ge 39` check is removed, because §10/§11 citations live in a table
  column where a token count cannot see them. `01-08-PLAN.md` states the decision table carries
  no `Source:` column and must not create five new citation-bearing rows.
- **F-4** (mechanical half) — `01-07-PLAN.md` moves the Lean pointer out of `Source:` onto a
  separate `Evidence:` line, outside gate 5's citation grammar.
- **F-11** — `docs/statement-reviews/` added to 01-07's `files_modified` and to its task 2 file
  list; the conditional `.planning/REQUIREMENTS.md` and `.planning/ROADMAP.md` writes declared
  in both 01-06 and 01-07.

## 3. What I deliberately did NOT do

Everything below is a **user ruling** or needs re-planning rather than a bounded edit. This is
why the phase is **not** cleared for execution.

- **F-1 (STRUCT-02) — user ruling, then re-plan 01-07.** The row as drafted is factually wrong,
  not merely imprecise: the code discards `Ct1Ack`'s Boolean and accepts trailing data, so
  "differ only by non-minimal varint padding" is not the equivalence relation. Fixing it means
  deciding what STRUCT-02 asserts (a precise non-injectivity witness, or a full characterisation
  over a stated domain), which is a catalog statement change. It also implies qualifying
  **PROP-35**'s existing unrestricted roundtrip at `docs/spqr-properties.md:243` in the same PR —
  and 01-07 currently forbids touching existing statements. I will not rewrite a catalog
  statement or authorise a PROP-35 edit on my own.
- **F-2 (STRUCT-04) — user ruling, then re-plan 01-07.** Same shape: the honest statement needs
  a validity invariant (`pts_needed` representability, the variant-specific size checks at
  `src/v1/chunked/send_ct/serialize.rs:18`), and PROP-37's universal roundtrip needs the same
  qualification. Which invariant is in scope for v1 is yours.
- **F-4 (PROV-01 grammar) — user ruling.** I moved 01-07's stray citation, but the underlying
  conflict stands: `REQUIREMENTS.md:21` says a row cites "exactly one of" the three forms while
  `01-03-PLAN.md:80` permits several with all required to resolve. Changing PROV-01's wording is
  a requirements edit, which is contract-level.
- **F-6 (eligibility semantics) — user ruling, then re-plan 01-06.** Making `C1 = partial`
  eligible for its named open obligation is a change to what the target list *means*, and it
  interacts with the "22 targets" figure (`REQUIREMENTS.md:172` already counts work units, not
  rows — three axiom-removal obligations, PROP-47 spanning two requirements). A support-lemma
  review route has to be defined too. Both are scope decisions.
- **F-7 (statement packet) — re-plan 01-06 and 01-07.** The fix is a real interface: a named
  statement-record location holding a complete Lean declaration, a hashing rule over it, and a
  defined C1 evidence channel. That is planning work, not an edit to a verify line.
- **Codex's non-binding alternatives** — not adopted: F-1's "precise non-injectivity witness"
  and F-2's reformulation are exactly the options the user should choose between in F-1/F-2.
- **The `origin/main` SHA in F-10** — not propagated. Codex's `995436c` is wrong for this
  checkout (`e8f6689`); I recorded the re-measure instruction instead of either SHA, since both
  rot.
- **Wave-count references elsewhere** — none to fix. Neither `ROADMAP.md` nor `STATE.md` states a
  wave count, so the 5→8 wave change needed no downstream edit. The commit message on `92ea6b6`
  says "5 waves" and is now historical.
