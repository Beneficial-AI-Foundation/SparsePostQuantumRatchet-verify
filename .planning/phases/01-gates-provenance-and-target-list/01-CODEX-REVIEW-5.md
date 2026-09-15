<!--
Provenance
  reviewer:   Codex CLI (OpenRouter), cross-engine (not the planning engine)
  effort:     model_reasoning_effort = high
  sandbox:    read-only (bwrap, kernel-enforced)
  rubric:     docs/rubrics/spqr-plan-review.md (appended verbatim to the prompt)
  prompt:     /tmp/phase01-review-assignment-5.md
  raw output: /tmp/phase01-codex-review-5.md
  log:        /tmp/phase01-codex-review-5-log.txt
  date:       2026-09-15
  phase:      01-gates-provenance-and-target-list (plans 01-01 .. 01-09)
  branch:     la/spec-catalog @ d7cf202, working-tree revisions reviewed
  round:      5 (r1 REJECT, r2 APPROVE-WITH-EDITS, r3 REJECT, r4 REJECT)
  context:    reviewed after the user's 2026-09-15 ruling deferring PROP-37's
              restatement to Phase 7, and after round 4's other eight findings
              were applied.
  caveat:     ROADMAP Phase 1 criteria 3 and 4 were conformed to the earlier
              rulings while this review was running, so a finding citing their
              pre-edit wording may already be addressed. No finding below does.
  note:       The Codex review below is verbatim and never edited. Planning-seat
              triage is appended after the --- separator.
-->

# SPQR Plan Review

- Phase: 01 — Gates, Provenance and the Reviewed Target List
- Plans reviewed: `01-01-PLAN.md` through `01-09-PLAN.md`, as one set, in `.planning/phases/01-gates-provenance-and-target-list/`
- Date: 2026-09-15
- Branch/base verified: `la/spec-catalog`; HEAD `d7cf202a02c69ddc7d33f4c870293199b3f36cd6`; `origin/main` `e8f66895d61acd0238abb8b2c656c423b381bd8a`; source pin `d47083cd3abf2906229efa38ae2bfb1121498af0`. Working-tree plans reviewed. The working-tree `src/` and `SrcTranslated/` match the pin.
- VERDICT: APPROVE-WITH-EDITS

## Findings

The required changes are bounded consistency, evidence-packet and workflow edits. None requires designing PROP-37’s deferred invariant, attempting a proof, or changing immutable code.

### F-1 — MAJOR
**Claim:** PROP-37’s deferral is contradicted by the human checkpoint and completion language that still require the rejected representability-only domain correction.

**Evidence:**

The correct instruction is explicit at `.planning/phases/01-gates-provenance-and-target-list/01-07-PLAN.md:214`: annotate PROP-37, leave its conclusion and `Open` status unchanged, and add **no** `Domain:` line. The final verification repeats that correctly at `.planning/phases/01-gates-provenance-and-target-list/01-07-PLAN.md:498`.

However, the same plan’s blocking checkpoint says:

- Task 1 added `Domain:` lines to **both** PROP-35 and PROP-37.
- The user must confirm `pts_needed.val ≤ U32.max` for PROP-37.
- Variant-specific validity was ruled out as Phase 4/5 work.

These instructions remain at `.planning/phases/01-gates-provenance-and-target-list/01-07-PLAN.md:447`. They describe precisely the ruling superseded on September 15, 2026.

Additional residuals:

- `.planning/phases/01-gates-provenance-and-target-list/01-07-PLAN.md:278` describes the permitted diff as two domain corrections.
- `.planning/phases/01-gates-provenance-and-target-list/01-07-PLAN.md:282` declares both false domains corrected.
- `.planning/phases/01-gates-provenance-and-target-list/01-07-PLAN.md:473` requires a ruling on both `Domain:` corrections.
- `.planning/phases/01-gates-provenance-and-target-list/01-VALIDATION.md:183` still validates “the two `Domain:` corrections.”

This is a residual of **round 4 F-1**, not a new objection to the human’s deferral.

The underlying counterexample still holds:

| Step | State/value | Result |
|---|---|---|
| Input | `Ct1SentEkReceived`, fixed epoch/authenticator, `es = []`, `ek = []`, `ct1 = []` | These vector fields are admitted by the extracted type |
| `into_pb` | Copies the three vectors; wraps the authenticator in `Some` | Successful protobuf value |
| `from_pb` | First length check asks whether `es.len() == 2080` | False |
| Return | `Error::StateDecode` | Not the original state |

The field types are at `SrcTranslated/Types.lean:1077`; copying is at `src/v1/unchunked/send_ct/serialize.rs:74` and `SrcTranslated/Funs.lean:10639`; rejection is at `src/v1/unchunked/send_ct/serialize.rs:85` and `SrcTranslated/Funs.lean:12265`. There is no decoder representability field in this counterexample.

There is also a metadata consequence: `docs/spqr-properties.md:24` defines `Open` as “Statement fixed, no theorem yet.” Leaving PROP-37 `Open` is the explicit ruling, but its legend needs an exception for an annotated statement awaiting restatement.

**Minimal suggested edit:** Replace all remaining “two domain corrections” instructions with “PROP-35 domain qualification and PROP-37 finding/Phase 7 deferral.” Make task 4 inspect those actual deliverables rather than re-request the superseded invariant ruling. Update the corresponding diff/completion checks and validation row. Preserve PROP-37’s conclusion and status; clarify the status legend’s treatment of `Finding:`-annotated deferred statements.

### F-2 — MAJOR
**Claim:** The isolated statement-review packets omit the implementation that establishes the new statements’ varint and tag claims.

**Evidence:**

Both new rows are prescribed the source range `src/v1/chunked/states/serialize.rs:221-280` at `.planning/phases/01-gates-provenance-and-target-list/01-07-PLAN.md:156` and `.planning/phases/01-gates-provenance-and-target-list/01-07-PLAN.md:166`.

That range contains calls to helpers, not their relevant definitions:

| Required evidence | Actual location | In prescribed source extract? |
|---|---|---|
| Tag discriminants and decoding | `src/v1/chunked/states/serialize.rs:95` | No |
| Both `Ct1Ack` Boolean values map to the same tag | `src/v1/chunked/states/serialize.rs:123` | No |
| Encoder emits minimal varints | `src/v1/chunked/states/serialize.rs:139` | No |
| Decoder accepts nonminimal varints and truncating ten-byte blocks | `src/v1/chunked/states/serialize.rs:152` | No |
| Chunk index decoding and size checks | `src/v1/chunked/states/serialize.rs:184` | No |

The skill must supply the **actual cited lines** and exclude other material: `.planning/phases/01-gates-provenance-and-target-list/01-06-PLAN.md:366`. Its C1 channel supplies names and signatures, not implementation bodies. The Lean pointer on `Evidence:` is deliberately separate from `Source:` and is not specified as part of the assembled evidence packet.

Consequently, a reviewer obeying the isolation rule cannot independently verify the nonminimal-varint witness or the canonical encoder language from the prescribed packet. Following the helpers outside the extract would require relaxing the stated evidence boundary.

This recurs from the **source-range component of round 3 F-1**: the range now includes payload reconstruction and suffix acceptance, but still excludes the encoding primitives needed for the revised obligations.

ML-KEM Braid §2.3 specifies message fields rather than this concrete byte encoding, so the spec cannot fill this evidentiary gap. citeturn1view0

**Minimal suggested edit:** Expand the two rows’ code citations to include the tag mappings and encoding/decoding helpers, for example the relevant portions of lines 95–202 as well as 221–280. Ensure the resulting extracts, including any specifically required extracted type declarations, are explicitly permitted and included by the packet builder. Keep this a finite cited-source expansion, not permission to browse neighboring catalog arguments.

### F-3 — MAJOR
**Claim:** The per-obligation selection model still lacks an unambiguous identity contract for the review command, statement files and catalog-source lookup.

**Evidence:**

`.planning/phases/01-gates-provenance-and-target-list/01-06-PLAN.md:148` correctly requires multiple obligation lines for a partially proved catalog row. Its worked example gives PROP-35:

- proved component specifications, `C1 = fail`, outside the goal;
- open composed roundtrip, `C1 = pass`, `Target? = yes`.

But the prescribed table has `ID | Obligation | ...` without defining a distinct obligation key or a parent catalog ID: `.planning/phases/01-gates-provenance-and-target-list/01-06-PLAN.md:146`.

The downstream interface then:

1. accepts “obligation IDs”;
2. looks that ID up in the target table;
3. reads **its** catalog `Source:`;
4. opens `docs/statements/<ID>.md`.

See `.planning/phases/01-gates-provenance-and-target-list/01-06-PLAN.md:340` and `.planning/phases/01-gates-provenance-and-target-list/01-06-PLAN.md:362`.

Neither possible interpretation is completed:

| Interpretation | Unspecified operation |
|---|---|
| `ID` remains the catalog ID, e.g. `PROP-35` | Which obligation’s C1/eligibility and statement record does `/spqr-statement-review PROP-35` select? |
| Each obligation receives a new unique ID | How does that ID resolve back to the catalog row whose text and `Source:` must be supplied? |

This matters beyond the worked example. The plan explicitly acknowledges that PROP-47 spans two refinement requirements and that MERGE-04/05/06 are non-row work units at `.planning/phases/01-gates-provenance-and-target-list/01-06-PLAN.md:180`. Those units must also have an executable review route.

The residual “one row per registry entry” final check at `.planning/phases/01-gates-provenance-and-target-list/01-06-PLAN.md:472`, repeated in `.planning/phases/01-gates-provenance-and-target-list/01-VALIDATION.md:114`, does not distinguish catalog-ID coverage from obligation-row cardinality.

This is a remaining interface consequence of the **round 3 F-6 obligation split**. The support eligibility branch itself has been fixed; identity and lookup are the remaining issue.

**Minimal suggested edit:** Define a stable unique obligation key and an explicit catalog-parent/source mapping. Use the obligation key consistently for CLI arguments, statement records, artifact names and log entries. Specify representation of non-row work units. Check catalog coverage by the set of parent IDs, independently of the number of obligation rows. Include a worked lookup with two obligations belonging to one catalog row.

### F-4 — MAJOR
**Claim:** The validation schedule still consumes the wave-7 deviation table before its producer runs.

**Evidence:**

The sampling rule at `.planning/phases/01-gates-provenance-and-target-list/01-VALIDATION.md:46` requires the §11 parse check after **every task commit** that changes `docs/spqr-properties.md`.

That parse check requires:

- five `Provisional` decision rows, at `.planning/phases/01-gates-provenance-and-target-list/01-VALIDATION.md:98`;
- ten total deviation-table rows, at `.planning/phases/01-gates-provenance-and-target-list/01-VALIDATION.md:104`.

But the second table is created only by plan 01-08, wave 7: `.planning/phases/01-gates-provenance-and-target-list/01-08-PLAN.md:5` and `.planning/phases/01-gates-provenance-and-target-list/01-08-PLAN.md:105`. Plan 01-03 necessarily edits the catalog in wave 2, and plan 01-07 edits it in wave 6.

Running the prescribed checks on the current pre-decision shape produced:

```text
Provisional decision rows: 0
D1 7
D2 7
D3 7
D4 7
D5 7
```

Plan 01-03 adds a source column, not the missing decision rows. Therefore its correct output still cannot satisfy the sampling assertions.

Two related scheduling residuals remain:

- `.planning/phases/01-gates-provenance-and-target-list/01-VALIDATION.md:140` requires both builds “before any gate task can be validated,” contradicting its corrected waves-1–2 static/gate-5 policy.
- `.planning/phases/01-gates-provenance-and-target-list/01-VALIDATION.md:88` still assigns the caller contract to nonexistent `01-08 T3`, wave 6; its producer is task 2, wave 7.

This recurs from **round 4 F-6**. The full-run sampling paragraph was fixed, but the subordinate checks were not completely staged.

**Minimal suggested edit:** Before 01-08 task 1, validate only the existing wide table and registry/source structure. Enable the five-decision/ten-row assertions after that producer. Restrict the build prerequisite to build-dependent gates, and correct the remaining task/wave entry.

### F-5 — MAJOR
**Claim:** Rejecting the first new statement leaves the workflow at a checkpoint that requires a second review it has not run.

**Evidence:**

The prescribed order is STRUCT-02a, then STRUCT-02b: `.planning/phases/01-gates-provenance-and-target-list/01-07-PLAN.md:367`.

For each statement, a REJECT or HUMAN_RULING must “stop and take it to task 4”: `.planning/phases/01-gates-provenance-and-target-list/01-07-PLAN.md:383`. The skill also stops for the user on these verdicts at `.planning/phases/01-gates-provenance-and-target-list/01-06-PLAN.md:385`.

Nevertheless:

- task 3’s check requires artifacts for **both** statements and no remaining empty `Review:` reference: `.planning/phases/01-gates-provenance-and-target-list/01-07-PLAN.md:408`;
- task 4 starts by requiring both artifacts: `.planning/phases/01-gates-provenance-and-target-list/01-07-PLAN.md:430`;
- its action and acceptance require both verdicts and both source extracts: `.planning/phases/01-gates-provenance-and-target-list/01-07-PLAN.md:460`.

The allowed execution is therefore:

| Event | STRUCT-02a | STRUCT-02b |
|---|---|---|
| Records written | Present | Present |
| First review returns REJECT | Artifact and log persisted; `Review:` filled | Not reviewed |
| Mandatory stop to task 4 | Available for ruling | No verdict, artifact or source extract from a run |
| Task 3/task 4 completion assertions | First half satisfied | Required second half unavailable |

Filling the first row’s `Review:` for every verdict fixes **round 4 F-9**, but does not fix this remaining early-stop path. This is consequential because the plan explicitly anticipates objections to STRUCT-02a; rejection must be a supported result of the demonstration, not an execution dead end.

**Minimal suggested edit:** Specify an interim ruling-and-resume path: persist the first review, obtain the required ruling without demanding the pending second artifact, then resume task 3 at STRUCT-02b. Run the final two-artifact checkpoint only after both reviews have completed. Preserve the prohibition on silently rewriting a rejected statement to obtain acceptance.

### F-6 — MINOR
**Claim:** The accepted project’s active-goal list still promises the retired standalone protobuf-injectivity row.

**Evidence:**

`.planning/PROJECT.md:70` still lists both “the new wire-format canonicity row” and “the new `States` protobuf injectivity row” as active whole-structure targets.

The same document’s updated context at `.planning/PROJECT.md:98`, `.planning/REQUIREMENTS.md:45`, and `.planning/phases/01-gates-provenance-and-target-list/01-07-PLAN.md:178` say STRUCT-04 is retired into STRUCT-03 and **no such catalog row is to be created**. The actual wire-format work is now two rows.

The more specific instructions allow execution to proceed correctly, so this is not a proof-content blocker. It does leave an operative active-goal list that the planned endpoint cannot satisfy literally. It is another residual of the retirement following **round 3 F-2**, reaffirmed in round 4.

**Minimal suggested edit:** Synchronize `.planning/PROJECT.md`’s active whole-structure list with STRUCT-02a/02b and the absorbed STRUCT-04 obligations. Do not restore a separate protobuf-injectivity target or change the target count.

## Cleared surfaces

### 1. Catalog fidelity

The substantive PROP-37 deferral is appropriate. Its `Finding:` can honestly record a false assertion without making gate 5 fail: gate 5 checks citation resolution, not theorem truth. That is not a vacuous pass unless its result is misreported as statement validation. Plan 01-09’s handoff correctly distinguishes Phase 7’s remaining **design** work at `.planning/phases/01-gates-provenance-and-target-list/01-09-PLAN.md:109`.

PROP-38 does not exhibit the empty-vector failure above. Its Rust chain conversion reconstructs the enum, preserves link order and fields, and introduces the `Some` fields consumed by the inverse: `src/chain.rs:298`, `src/chain.rs:306`, `src/chain.rs:415`, and `src/chain.rs:434`. Extraction/prost conditionality remains a separate issue, correctly deferred rather than dismissed.

LEAN-ENC-1’s fixed-size, big-endian point conversion survives the domain check. Its four-byte input and two `U16` coordinates do not require an arbitrary-vector validity invariant: `Spqr/Specs/Encoding/Polynomial/Pt/Serialize.lean:88` and `Spqr/Specs/Encoding/Polynomial/Pt/Deserialize.lean:144`.

### 2. Internal consistency and ordering

The main dependency chain is now coherent:

| Wave | Producer/work |
|---|---|
| 1 | 01-01 documentation; 01-02 checker/runner |
| 2 | 01-03 reference lists and source retrofit |
| 3 | 01-04 builds and negative controls |
| 4 | 01-05 PR A boundary and PR B branch decision |
| 5 | 01-06 selection and review machinery |
| 6 | 01-07 registration, records and reviews |
| 7 | 01-08 deviation decisions |
| 8 | 01-09 boundary report |

The two new rows are registered as candidates **before** their review. The `--support` branch now precedes target-only rejection. PR B’s head and base are separately produced and correctly consumed. The remaining ordering defects are F-4 and F-5, not the old checker/retrofit race.

No new Lean module is planned, so no new `Spqr.lean` re-export is required by this phase.

### 3. Statement-level soundness

The corrected extracted signatures are accurate:

```text
Message.serialize :
  Message → U32 → Result (alloc.vec.Vec U8)

Message.deserialize :
  alloc.vec.Vec U8 →
  Result (core.result.Result (Message × U32 × Usize) Error)
```

See `SrcTranslated/Funs.lean:11460` and `SrcTranslated/Funs.lean:14163`. Encoder-image membership must use `serialize message index = ok bytes`; decoder success must distinguish the outer `ok` from inner `.Ok`.

**PROP-35 does not need a fourth independent input hypothesis revealed by these declarations.** The nonzero epoch and true `Ct1Ack` Boolean are genuine restrictions. The decoder’s `hlen` is a real theorem premise, but on serializer output it is a derived bound, not evidence of a further semantic validity invariant:

- epoch is `U64`;
- message index is `U32`;
- chunk index is `U16`;
- chunk data is an array of exactly 32 bytes.

These are fixed by `SrcTranslated/Types.lean:904`, `SrcTranslated/Types.lean:1189`, and the serializer signature. A serialized chunk-carrying message has at most `1 + 10 + 5 + 1 + 3 + 32 = 52` bytes. Thus the required output-length-plus-32 bound is at most 84. The general varint length lemma exists at `Spqr/Specs/V1/Chunked/States/Serialize/EncodeVarint.lean:51`.

The derivation must distinguish input restrictions from obligations discharged by the encoder layout. It must **not** turn decoder success or the desired roundtrip into a new hypothesis. The existing decoder theorem is one-way on success; its error branch does not establish a positive decoding theorem. The plans correctly leave the missing agreement/composition work to Phase 3 rather than attempting it here.

The concrete non-injectivity witnesses are not vacuous:

| Input | Successful result |
|---|---|
| Serialize epoch 1, index 0, `Ct1Ack false` | `ok [01, 01, 00, 04]` |
| Serialize epoch 1, index 0, `Ct1Ack true` | `ok [01, 01, 00, 04]` |
| Deserialize `[01, 01, 00, 00]` | `ok (.Ok (Message(1, None), 0, 4))` |
| Deserialize `[01, 81, 00, 00, 00]` | `ok (.Ok (Message(1, None), 0, 5))` |

The second pair witnesses non-injectivity of the successful `(message, index)` projection, **not equality of the complete results**. Task 2 now says this correctly.

STRUCT-02b can be stated non-circularly using encoder-image membership, explicit varint conditions and successful decoding. Membership in an encoder’s image does not itself assume injectivity of the decoder. However, “successful image” must not be confused with the entire image: epoch-zero messages serialize and then fail decoding. No concrete predicate exists yet to certify; checking its coverage and avoiding an assumed re-encoding equality remain legitimate duties of the planned statement review.

### 4. Semantic closure

The D1–D5 code-authoritative posture matches the inspected paths. In particular, the D5 contract accurately distinguishes local computation from the caller’s retained serialized state.

| Trace point | Local state/output | Caller-visible consequence |
|---|---|---|
| Completing `Ct2` reaches `recv_ct2` | Decapsulation and KDF produce a candidate secret | No return yet |
| Before MAC verification | Local authenticator updated | Caller input remains immutable |
| `verify_ct` fails | Error propagated; no successor/key pair constructed | `MacVerifyFailed`; no returned replacement state or key |
| `verify_ct` succeeds, epoch nonoverflowing | Successor epoch is `e + 1`; emitted key epoch is `e` | Successful state/key processing continues |

The extracted ordering is explicit at `SrcTranslated/Funs.lean:13241`, `SrcTranslated/Funs.lean:13248`, and `SrcTranslated/Funs.lean:13255`. The public error conversion and API return boundary are at `src/lib.rs:145`, `src/lib.rs:356`, and `src/lib.rs:425`. Dropping the failed local computation is not zeroization.

The exceptional Greater arm is also preserved: `Ct2Sampled(e)` receiving epoch `e + 1` transitions to `KeysUnsampled(e + 1)`; a larger epoch errors. See `src/v1/chunked/states.rs:513`. D3’s `Ct1Ack(true)` emission and acceptance, and D4’s extra `Ek` acceptance, match `src/v1/chunked/states.rs:175`, `src/v1/chunked/states.rs:458`, and `src/v1/chunked/states.rs:479`.

### 5. Precedent and interface realism

The cited message serializer/deserializer, authenticator update and decoder serialization specifications exist with `@[step]` and the relevant hypotheses. The update memory-size premise is present at `Spqr/Specs/Authenticator/Authenticator/Update.lean:49`.

The C1 baseline correction survives review. `origin/main` really contains `Spqr/Specs/Chain/Chain/EpochIdx.lean`, absent from this branch. Classification against the working tree would miss that precedent. The explicit SHA and revision-qualified search in 01-06 fix this.

The missing `varintBytes`/`varintBlockAt` bridge was not found by the targeted repository search. It remains future work, not an available lemma.

The local papers identify ML-KEM Braid Revision 1, updated September 26, 2025, and SCKA Def. 3.1/Fig. 1/Fig. 2. No proof of their security games is scheduled. ML-KEM Braid §2.4’s session-restart guidance is stronger than the library’s error return, so retaining D5 as a provisional deviation is appropriate. citeturn1view0

### 6. Trusted-base discipline

No new axiom, opaque declaration, proof or committed Lean file is authorized. The conditional `sorryAx` control is a gate test, not permission to introduce a trusted theorem.

The namespace and multiline-declaration traps are real: `SrcTranslated/FunsExternal.lean:16` opens rather than enters `spqr`; the long fixup axiom starts on the line after `axiom` at `SrcTranslated/FunsExternal.lean:3687`; the handwritten HKDF specification is inside `spqr.kdf` at `Spqr/Specs/Kdf/HkdfToSlice.lean:18`.

STRUCT-04’s retirement is logically sound **conditionally on the eventual successful left-inverse law**. Equal successful protobuf encodings can be fed to the same decoder to obtain equal states. This argument does not need Phase 1 to select the validity domain. It does not establish unrestricted injectivity off that domain, and the plans now make that distinction.

### 7. Gates

The gate design now addresses missing reports, misspelled theorem names, wrapped axiom lists and malformed report termination. The empirical controls are required, rather than declared completed.

Registry enumeration independently produced:

```text
headings: 28 section10: 9 deviations: 5
registry: 42 index rows: 38
symmetric difference: []
```

The proposed parser explicitly covers `### STRUCT-` headings and joins both §11 tables by deviation ID. Adding two new properties gives 44 registry entries and 40 index rows. `Evidence:`, `Domain:` and `Finding:` are metadata, not extra registry entries or additional `Source:` citations. They must not be accidentally consumed as a continuation of a source list.

The scoped phantom-token search currently finds exactly the three operative files that 01-01 edits. The named-marker checks and stash-baseline comparisons are repaired at both task and final-verification levels.

No build, elaboration or negative-control execution was attempted in this review. Runtime gate correctness remains an execution obligation, not a claimed review result.

### 8. Boundedness and safety

The committed phase scope remains documentation and tooling. Broken Lean controls are confined to throwaway worktrees by 01-04’s explicit exception; no such control was run here.

The final source/extraction comparison returned exit 0. Five pre-existing stashes remain. No repository file was modified, created, staged, formatted or committed.

The branch boundary uses separate head/base references and full committed ranges rather than a bare working-tree diff. Unmet criteria must still be reported honestly; completing a plan is not itself evidence of a green gate.

### 9. Roadmap and catalog coherence

**ROADMAP Phase 1 criterion 5 remains satisfiable.** It concerns D1–D5 and PROP-42/30/47/50/43, not PROP-37. The deferral does not remove a prerequisite for those decisions or restatements.

Likewise, criterion 4 demonstrates that the review machinery ran; it does not require every reviewed statement to receive ACCEPT. F-5 must be fixed so that this remains executable when the first review rejects.

The Phase 7 contract and 01-09 handoff correctly reserve invariant design, catalog restatement and the inherited injectivity corollary for Phase 7. The stale checkpoint and active-goal list are the exceptions identified in F-1 and F-6.

## Probe log

All shell commands below were read-only. Large initial reads sometimes returned truncated output; subsequent narrower reads supplied the cited evidence. No `lake` command was executed.

### Checkout and initial plan reads

```bash
pwd; for dir in / /home /home/lacra /home/lacra/git_repos /home/lacra/git_repos/baif /home/lacra/git_repos/baif/SparsePostQuantumRatchet-verify; do if [ -f "$dir/AGENTS.md" ]; then printf '\n--- %s ---\n' "$dir/AGENTS.md"; cat "$dir/AGENTS.md"; fi; done; git status --short; git branch --show-current; git rev-parse HEAD origin/main d47083c; git diff --name-only d47083c..HEAD -- src; git stash list; rg --files -g AGENTS.md -g '*PLAN.md' -g '*REVIEW*.md' -g '*VALIDATION.md' -g '*RESEARCH.md' .planning .github scripts docs Spqr SrcTranslated .claude
```

Result: confirmed branch, three SHAs, working-tree planning changes, unchanged pinned Rust range and five stashes; no applicable `AGENTS.md` content was returned.

```bash
for file in .planning/phases/01-gates-provenance-and-target-list/01-{06,07,09}-PLAN.md .planning/ROADMAP.md .planning/REQUIREMENTS.md; do printf '\n--- %s ---\n' "$file"; nl -ba "$file"; done
```

Result: initial combined read; output truncated.

```bash
wc -l .planning/phases/01-gates-provenance-and-target-list/* .planning/{ROADMAP,REQUIREMENTS,PROJECT,STATE}.md docs/spqr-properties.md; nl -ba .planning/phases/01-gates-provenance-and-target-list/01-06-PLAN.md | sed -n '90,280p'
```

Result: measured document sizes and read selection/review design; output partly truncated.

```bash
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-06-PLAN.md | sed -n '148,218p;280,380p'
```

Result: obligation split, target classification and support routing.

```bash
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-06-PLAN.md | sed -n '197,327p'
```

Result: table acceptance, record format, C1 baseline and support rubric.

```bash
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-06-PLAN.md | sed -n '380,486p'
```

Result: persistence, triage, human checkpoint and final verification.

```bash
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-07-PLAN.md | sed -n '1,140p'
```

Result: phase scope, new statement objectives and evidence list.

```bash
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-07-PLAN.md | sed -n '140,244p'
```

Result: witnesses, canonical-domain requirement, retirement and corrected PROP-37 deferral.

```bash
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-07-PLAN.md | sed -n '242,360p'
```

Result: registration, residual domain-completion language and corrected extracted signatures.

```bash
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-07-PLAN.md | sed -n '358,518p'
```

Result: review/rejection flow, human checkpoint and final checks.

```bash
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-07-PLAN.md | sed -n '420,477p'; nl -ba .planning/phases/01-gates-provenance-and-target-list/01-09-PLAN.md
```

Result: confirmed stale task-4 invariant ruling; read boundary/handoff, with part of the combined output truncated.

```bash
nl -ba .planning/ROADMAP.md | sed -n '1,112p;185,219p'; nl -ba .planning/REQUIREMENTS.md | sed -n '1,96p'
```

Result: phase criteria and requirement context; output truncated.

```bash
nl -ba .planning/ROADMAP.md | sed -n '65,98p;176,207p'; nl -ba .planning/REQUIREMENTS.md | sed -n '1,54p'
```

Result: Phase 1 criteria and revised STRUCT requirements.

### Serializer declarations and semantics

```bash
nl -ba Spqr/Specs/V1/Chunked/States/Serialize/Message/Deserialize.lean | sed -n '1,115p'; nl -ba Spqr/Specs/V1/Chunked/States/Serialize/Message/Serialize.lean | sed -n '1,90p'
```

Result: verified `hlen`, success conjuncts, unconditional serializer specification and layout model.

```bash
nl -ba SrcTranslated/Funs.lean | sed -n '11455,11503p;14158,14242p'; rg -n 'structure .*Chunk|structure .*Message|inductive .*MessagePayload|Ct1SentEkReceived|def .*decode_chunk' SrcTranslated/{Types,Funs}.lean; nl -ba Spqr/Specs/V1/Chunked/States/Serialize/DecodeChunk.lean | sed -n '20,76p'
```

Result: verified serializer `Result`, nested decoder result and chunk predicate; output partly truncated.

```bash
rg -n '^structure encoding.Chunk|^structure v1.chunked.states.Message|^inductive v1.chunked.states.MessagePayload' SrcTranslated/Types.lean; nl -ba src/v1/chunked/states/serialize.rs | sed -n '170,202p;220,280p'; nl -ba Spqr/Specs/V1/Chunked/States/Serialize/DecodeVarint.lean | sed -n '30,60p'
```

Result: located fixed chunk types and verified Boolean normalization, trailing-byte acceptance and `% 2 ^ 64` varint relation.

### Remaining plans

```bash
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-01-PLAN.md | sed -n '1,115p'
```

Result: documentation scope and planned checklist.

```bash
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-01-PLAN.md | sed -n '116,217p'; nl -ba .planning/phases/01-gates-provenance-and-target-list/01-02-PLAN.md | sed -n '1,90p'
```

Result: support-review checklist and runner scope; output partly truncated.

```bash
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-02-PLAN.md | sed -n '91,200p'
```

Result: gates 1–3, baseline cache, compatibility shim and allowlist design.

```bash
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-02-PLAN.md | sed -n '197,286p'
```

Result: wrapped-list handling, multiline source validation and normalized registry design.

```bash
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-02-PLAN.md | sed -n '287,358p'; nl -ba .planning/phases/01-gates-provenance-and-target-list/01-03-PLAN.md | sed -n '1,75p'
```

Result: fail-closed provenance, expected-red initial run and retrofit scope.

```bash
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-03-PLAN.md | sed -n '74,178p'
```

Result: citation grammar, PDF prerequisites and source-column retrofit.

```bash
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-03-PLAN.md | sed -n '179,271p'; nl -ba .planning/phases/01-gates-provenance-and-target-list/01-04-PLAN.md | sed -n '1,82p'
```

Result: Unsourced handling and build/control scope; output partly truncated.

```bash
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-04-PLAN.md | sed -n '83,187p'
```

Result: empirical axiom probes and same-SHA CI comparison.

```bash
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-04-PLAN.md | sed -n '188,275p'
```

Result: baseline verification and all nine controls, including stash preservation.

```bash
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-04-PLAN.md | sed -n '275,325p'; nl -ba .planning/phases/01-gates-provenance-and-target-list/01-05-PLAN.md | sed -n '1,120p'
```

Result: control completion and PR A boundary; output partly truncated.

```bash
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-05-PLAN.md | sed -n '116,188p'; nl -ba .planning/phases/01-gates-provenance-and-target-list/01-08-PLAN.md | sed -n '1,98p'
```

Result: separate head/base fields and provisional deviation posture.

```bash
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-08-PLAN.md | sed -n '95,184p'
```

Result: second-table producer, 44-entry expectation and statement-restatement scope.

```bash
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-08-PLAN.md | sed -n '183,249p'; nl -ba .planning/phases/01-gates-provenance-and-target-list/01-09-PLAN.md | sed -n '1,104p'
```

Result: D5 contract and final boundary reporting; output partly truncated.

### Validation, history and catalog

```bash
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-VALIDATION.md | sed -n '1,110p'
```

Result: corrected full-run staging, but premature §11 checks and stale task mapping.

```bash
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-VALIDATION.md | sed -n '111,200p'; nl -ba .planning/phases/01-gates-provenance-and-target-list/01-CODEX-REVIEW-4.md | sed -n '570,725p'
```

Result: remaining validation requirements and round-4 triage; output truncated.

```bash
rg -n '^### F-|^\*\*Claim|^## [0-9]|^### Planning-seat|^\| F-|^\| PS-' .planning/phases/01-gates-provenance-and-target-list/01-CODEX-REVIEW-{3,4}.md; nl -ba .planning/phases/01-gates-provenance-and-target-list/01-VALIDATION.md | sed -n '158,200p'; nl -ba .planning/PROJECT.md | sed -n '22,80p'
```

Result: prior finding identities, validation residuals and active target-selection rules.

```bash
nl -ba docs/spqr-properties.md | sed -n '1,74p;162,196p;205,236p'
```

Result: status legend, trusted-base description, point roundtrip and authenticator claims.

```bash
nl -ba docs/spqr-properties.md | sed -n '235,296p;315,403p'
```

Result: PROP-35, MAC failure, transition refinement and liveness statements.

```bash
nl -ba docs/spqr-properties.md | sed -n '405,451p'; nl -ba .planning/PROJECT.md | sed -n '90,149p'; nl -ba .planning/STATE.md | sed -n '40,90p'; rg -n '^## |^### ' .planning/phases/01-gates-provenance-and-target-list/01-RESEARCH.md
```

Result: table row shapes, serialization claims, deviation list and planning context; output truncated.

```bash
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-CODEX-REVIEW-4.md | sed -n '647,672p'; nl -ba .planning/phases/01-gates-provenance-and-target-list/01-CODEX-REVIEW-3.md | sed -n '17,70p'; nl -ba .planning/STATE.md | sed -n '51,76p'; nl -ba .planning/REQUIREMENTS.md | sed -n '8,23p'
```

Result: verified round-4 triage and the earlier citation/domain findings; read PROV-01/REV-01.

### Gate implementation precedents and source checks

```bash
nl -ba scripts/check-lint.sh; nl -ba .github/workflows/lean.yml | sed -n '38,90p'; nl -ba .github/workflows/sorry-delta-comment.yml | sed -n '30,54p'; nl -ba scripts/sorry-diff.py | sed -n '1,60p'; rg -n 'SORRY_|write|output|return|sys.exit' scripts/sorry-diff.py; nl -ba scripts/Audit.lean | sed -n '1,100p'
```

Result: verified CI command/filter shapes, sorry-delta invocation and Audit import visibility.

```bash
git grep -nE 'check[_]no[_]sorry' -- ':!.planning'; git diff --name-only origin/main..HEAD -- '*.lean' lakefile.toml lean-toolchain lake-manifest.json; git show origin/main:Spqr/Specs/Chain/Chain/EpochIdx.lean | sed -n '25,65p'; nl -ba SrcTranslated/Types.lean | sed -n '900,923p;1100,1120p;1177,1195p'; nl -ba src/v1/unchunked/send_ct/serialize.rs | sed -n '70,101p'; nl -ba SrcTranslated/Funs.lean | sed -n '12260,12280p'
```

Result: three operative phantom-token hits; confirmed upstream-only Lean differences, C1 precedent, fixed chunk types and empty-vector rejection.

```bash
nl -ba src/v1/chunked/states/serialize.rs | sed -n '126,182p'; nl -ba Spqr/Specs/V1/Chunked/States/Serialize/EncodeVarint.lean | sed -n '28,84p'; nl -ba Spqr/Specs/Encoding/Polynomial/Pt/{Serialize,Deserialize}.lean | sed -n '1,120p'; nl -ba src/chain.rs | sed -n '414,452p'
```

Result: inspected varint encoder/decoder, length lemmas, point specs and chain conversion.

```bash
nl -ba src/authenticator.rs | sed -n '8,18p;43,55p'; nl -ba src/lib.rs | sed -n '135,151p;350,361p;412,447p'; nl -ba src/v1/unchunked/send_ek.rs | sed -n '142,171p'; nl -ba src/v1/unchunked/send_ct.rs | sed -n '99,116p'; nl -ba Spqr/Specs/Authenticator/Authenticator/Update.lean | sed -n '43, sixty p'
```

Result: source reads succeeded through the header-verification path. The last `sed` expression was mistyped and exited 1; corrected in the next command.

```bash
nl -ba Spqr/Specs/Authenticator/Authenticator/Update.lean | sed -n '39,65p'; nl -ba src/v1/chunked/states.rs | sed -n '173,190p;274,292p;456,498p;510,535p'; nl -ba .planning/ROADMAP.md | sed -n '153,176p'; nl -ba Spqr/Specs/Encoding/Polynomial/Pt/Deserialize.lean | sed -n '35,73p'
```

Result: verified update premise, D2–D4 branches, Phase 7 invariant contract and point decoding.

```bash
rg -n -C 2 'obligation|duplicate|statement record|support' .planning/phases/01-gates-provenance-and-target-list/01-CODEX-REVIEW-3.md | head -n 95; nl -ba .planning/REQUIREMENTS.md | sed -n '30,39p;63,69p'; nl -ba .planning/phases/01-gates-provenance-and-target-list/01-06-PLAN.md | sed -n '254,270p'; nl -ba .planning/PROJECT.md | sed -n '94,132p'
```

Result: checked prior obligation-split finding, non-row requirements, record identity wording and retirement context.

### Narrow reads and structural probes

```bash
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-01-PLAN.md | sed -n '182,209p'; nl -ba .planning/phases/01-gates-provenance-and-target-list/01-03-PLAN.md | sed -n '245,253p'; nl -ba .planning/phases/01-gates-provenance-and-target-list/01-05-PLAN.md | sed -n '17,37p;178,188p'; nl -ba .planning/phases/01-gates-provenance-and-target-list/01-08-PLAN.md | sed -n '1,8p;235,249p'; nl -ba .planning/phases/01-gates-provenance-and-target-list/01-09-PLAN.md | sed -n '1,24p'
```

Result: checked final marker/registry/head-base rules, wave 7 and boundary frontmatter.

```bash
nl -ba src/v1/chunked/states/serialize.rs | sed -n '1,78p'; nl -ba .planning/phases/01-gates-provenance-and-target-list/01-RESEARCH.md | sed -n '542,620p'; nl -ba .planning/phases/01-gates-provenance-and-target-list/01-VALIDATION.md | sed -n '155,200p'
```

Result: state-variant serialization dispatch, allowlist recipe and residual manual domain-review requirement.

```bash
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-RESEARCH.md | sed -n '563,599p'; nl -ba SrcTranslated/FunsExternal.lean | sed -n '9,23p;3680,3698p'; nl -ba Spqr/Specs/Kdf/HkdfToSlice.lean | sed -n '15,35p'; nl -ba src/v1/chunked/states/serialize.rs | sed -n '92,135p'; rg -n 'varintBytes.*varintBlockAt|varintBlockAt.*varintBytes' Spqr/Specs; test -d .lake/build; printf 'build-directory status: %s\n' "$?"
```

Result: confirmed namespace/multiline traps and tag mappings; bridge search returned no match; build-directory status was 1.

```bash
python3 -B - <<'PY'
from pathlib import Path
import re
text = Path('docs/spqr-properties.md').read_text()
heading_ids = re.findall(r'^### ((?:PROP|LEAN|STRUCT)-\S+)', text, re.M)
section10 = text.split('## 10.')[1].split('## 11.')[0]
section11 = text.split('## 11.')[1].split('## 12.')[0]
section12 = text.split('## 12.')[1]
table10 = re.findall(r'^\| ((?:PROP|LEAN|STRUCT)-\S+) \|', section10, re.M)
deviations = re.findall(r'^\| (D[1-5]) \|', section11, re.M)
index_ids = re.findall(r'^\| ((?:PROP|LEAN|STRUCT)-\S+|D1[–-]D5) \|', section12, re.M)
registry = set(heading_ids + table10 + deviations)
expanded_index = set(index_ids) - {'D1–D5', 'D1-D5'} | set(deviations)
print('headings:', len(heading_ids), 'section10:', len(table10), 'deviations:', len(deviations))
print('registry:', len(registry), 'index rows:', len(index_ids))
print('symmetric difference:', sorted(registry ^ expanded_index))
PY
awk '/^## 11\./{f=1} /^## 12\./{f=0} f && /^\| D[1-5] \| .* \| Provisional /' docs/spqr-properties.md | wc -l
awk '/^## 11\./{f=1} /^## 12\./{f=0} f && /^\| D[1-5] \|/{n=split($0,c,"|"); print $2, n}' docs/spqr-properties.md
rg -n 'two.*[Dd]omain|both.*Domain|domain corrections|corrected.*domains|before any gate|01-08 T3|one row per registry' .planning/phases/01-gates-provenance-and-target-list/01-{06,07,09}-PLAN.md .planning/phases/01-gates-provenance-and-target-list/01-VALIDATION.md
```

Result: 42 registry entries, 38 index rows, empty symmetric difference; zero decision rows; located the residual instructions cited in F-1, F-3 and F-4.

```bash
rg -n 'theorem decode_varint_spec|theorem decode_chunk_spec|\| .Err|\| .Ok' Spqr/Specs/V1/Chunked/States/Serialize/DecodeVarint.lean Spqr/Specs/V1/Chunked/States/Serialize/DecodeChunk.lean; nl -ba Spqr/Specs/V1/Chunked/States/Serialize/DecodeChunk.lean | sed -n '74,96p'; nl -ba .planning/REQUIREMENTS.md | sed -n '30,43p'; nl -ba Spqr/Specs/Encoding/Polynomial/Pt/Deserialize.lean | sed -n '83,102p'; nl -ba src/chain.rs | sed -n '263,289p'
```

Result: verified one-way decoder success specifications and requirement work units.

```bash
rg -n 'fn (into_pb|from_pb)|fn (encode|decode)' src/chain.rs src/serialize.rs; nl -ba src/chain.rs | sed -n '305,350p'; nl -ba src/serialize.rs | sed -n '1,95p'; nl -ba src/encoding/polynomial.rs | sed -n '776,835p'; nl -ba SrcTranslated/Funs.lean | sed -n '10720,10735p'; nl -ba Spqr/Specs/Encoding/Polynomial/PolyDecoder/IntoPb.lean | sed -n '280,297p'
```

Result: checked chain field preservation, narrowing cast, monadic `States.into_pb` and decoder-serialization premises.

### Paper reads and final source confirmation

```bash
rg -n '(pdftotext|mlkembraid.*pdf|2025-2267.*pdf)' .planning/phases/01-gates-provenance-and-target-list/01-CODEX-REVIEW-{3,4}.md | tail -n 18; nl -ba .planning/phases/01-gates-provenance-and-target-list/01-06-PLAN.md | sed -n '80,98p'; nl -ba src/chain.rs | sed -n '296,312p'; git status --porcelain -- src SrcTranslated '*.lean'
```

Result: located previously used local PDFs; checked branch precondition and chain-direction conversion; source/Lean status empty.

```bash
pdftotext -f 1 -l 2 /tmp/props-review/mlkembraid.pdf - | head -n 45; pdftotext -layout /tmp/props-review/mlkembraid.pdf - | rg -n -A8 -B2 '2.3 Messages|salt equal|should not proceed|fresh messages'; pdftotext -layout /tmp/props-review/2025-2267.pdf - | rg -n -A12 -B2 'Definition 3.1.|Fig. 1:|Fig. 2:|Fig. 16:' | head -n 85
```

Result: verified braid revision/date, message section, MAC-failure guidance, liveness wording and SCKA definition.

```bash
nl -ba SrcTranslated/Types.lean | sed -n '1029,1089p'; nl -ba src/v1/chunked/send_ct/serialize.rs | sed -n '1,32p;92,163p'; rg -n '^theorem deserialize_spec|^def encoding.polynomial.Pt.(serialize|deserialize)|^def v1.unchunked.send_ct.serialize.Ct1SentEkReceived.into_pb' Spqr/Specs/Encoding/Polynomial/Pt/Deserialize.lean SrcTranslated/Funs.lean; nl -ba .planning/phases/01-gates-provenance-and-target-list/01-RESEARCH.md | sed -n '1426,1439p'
```

Result: confirmed unconstrained vector fields, enclosing state conversion and variant-specific decoder checks.

```bash
rg -n '^def (v1.unchunked.send_ek.EkSentCt1Received.recv_ct2|v1.chunked.states.States.recv|v1.chunked.states.States.send|recv$)' SrcTranslated/Funs.lean; nl -ba SrcTranslated/Funs.lean | sed -n '10635,10653p'; pdftotext -layout /tmp/props-review/2025-2267.pdf - | rg -n -m 8 'Definition 3.1|Figure 1|Figure 2|Figure 16'; nl -ba Spqr/Specs/V1/Chunked/States/Serialize/DecodeVarint.lean | sed -n '296,312p'; nl -ba Spqr/Specs/Encoding/Polynomial/Pt/Deserialize.lean | sed -n '137,154p'
```

Result: located extracted transition functions; verified successful vector copying, SCKA figure captions, decoder specification and point theorem signature.

```bash
nl -ba SrcTranslated/Funs.lean | sed -n '13216,13291p;13641,13662p'; nl -ba src/v1/chunked/states.rs | sed -n '510,535p'; git diff --quiet d47083c -- src SrcTranslated; printf 'pinned-source/extraction diff exit: %s\n' "$?"; git stash list | wc -l; git status --porcelain -- src SrcTranslated '*.lean'
```

Result: verified extracted MAC-check ordering and Greater rejection; pinned source/extraction diff exit 0; five stashes; source/Lean status empty.

Web probes supplemented the local paper reads:

```text
search_query: {"q":"site.signal.org/docs/specifications mlkembraid pdf"}
open: {"ref_id":"https://signal.org/docs/specifications/mlkembraid/mlkembraid.pdf"}
find: {"ref_id":"turn1view0","pattern":"2.3 Messages"}
find: {"ref_id":"turn1view0","pattern":"verification failure"}
```

Result: official Signal specification located and checked for the cited message and authentication sections.

## Resolution map

| Finding | Suggested edit | Destination plan/section |
|---|---|---|
| F-1 | Replace superseded two-domain checkpoint/completion language with PROP-35 qualification plus PROP-37 annotation/deferral; clarify the `Open` legend exception | 01-07 objective, tasks 1/4 and acceptance; 01-VALIDATION manual checks; planned catalog legend |
| F-2 | Include tag mappings and encoding/decoding helpers in the finite cited-source packets | 01-07 task 1 `Source:` fields; 01-06 packet assembly and permitted evidence |
| F-3 | Define unique obligation keys, catalog-parent mapping and non-row work-unit representation; separate coverage from row count | 01-06 tasks 1–3, record/log format and final verification; 01-VALIDATION target-table check |
| F-4 | Stage §11 assertions after their wave-7 producer; scope build prerequisites and correct the stale task/wave row | 01-VALIDATION sampling, §11 checks, Wave 0 requirements and verification map |
| F-5 | Add an explicit interim ruling/resume path when the first review rejects; defer two-artifact completion checks until both run | 01-07 tasks 3/4; 01-06 skill triage contract |
| F-6 | Synchronize active whole-structure goals with the two wire-format rows and absorbed protobuf-injectivity obligations | `.planning/PROJECT.md` active requirements; corresponding bounded documentation edit scope |
---

## 1. Codex's review

**VERDICT: APPROVE-WITH-EDITS** — 5 MAJOR, 1 MINOR, no BLOCKER. All six confirmed, all six
applied. This is the first round since round 2 without a REJECT, and the reason is visible in
the findings: none of them disputes what the phase asserts any more. They are consistency,
evidence-packet and workflow defects — the residue of three rounds of rulings landing in a
nine-plan set.

| # | Sev | Claim | My verification |
|---|-----|-------|-----------------|
| F-1 | MAJOR | PROP-37's deferral is contradicted by leftover "two domain corrections" language | **Confirmed at five locations** — `01-07:278, 282, 447, 473` and `01-VALIDATION:183`. Task 4's checkpoint still asked the user to confirm `pts_needed.val ≤ U32.max` for PROP-37, the exact ruling that was superseded. Its extra catch is the good one: `docs/spqr-properties.md:24` defines `Open` as "Statement fixed, no theorem yet", which is false of an annotated row awaiting restatement |
| F-2 | MAJOR | The cited source range omits the implementation the new statements are about | **Confirmed.** `src/v1/chunked/states/serialize.rs:221-280` contains *calls*; the definitions are outside it — `MessageType` at `:97`, `try_from` at `:109`, `from_payload` (where both `Ct1Ack` Booleans collapse to one tag) at `:124`, `encode_varint` at `:139`, `decode_varint` at `:152`, `encode_chunk`/`decode_chunk` at `:184`/`:190`. A reviewer held to the isolation rule could not have checked either witness |
| F-3 | MAJOR | The per-obligation model has no identity contract | **Confirmed.** The table was `ID \| Obligation \| …` with no unique key and no parent pointer, while the skill takes "obligation IDs", looks them up, reads *their* catalog `Source:` and opens `docs/statements/<ID>.md`. With PROP-35 split in two, neither reading resolves — and MERGE-04/05/06 are work units with no catalog row at all |
| F-4 | MAJOR | The §11 decision-table assertions run before their wave-7 producer | **Confirmed.** Sampling required the §11 parse check after every catalog-touching commit; the five `Provisional` rows only exist after 01-08 in wave 7, so 01-03 (wave 2) and 01-07 (wave 6) would both "fail" while being correct. Codex's probe reproduced it: `Provisional decision rows: 0`. Two related residuals also confirmed — the build prerequisite was unscoped, and a task entry still read `01-08 T3`, wave 6 |
| F-5 | MAJOR | A first-statement REJECT is an execution dead end | **Confirmed.** Task 3 stopped for the user on a non-ACCEPT, while task 3's own check and task 4's entry both require artifacts for *both* statements. Since the plan explicitly anticipates objections to STRUCT-02a, the anticipated outcome was unreachable |
| F-6 | MINOR | `PROJECT.md`'s active-goal list still promises the retired standalone injectivity row | **Confirmed** at `PROJECT.md:70` |

Its **Cleared surfaces** section is worth keeping: it independently checked PROP-38 and
LEAN-ENC-1 for the empty-vector defect and cleared both — PROP-38's chain conversion
reconstructs the enum and preserves link order (`src/chain.rs:298, 306, 415, 434`), and
LEAN-ENC-1's fixed-size four-byte point conversion needs no vector invariant
(`Pt/Serialize.lean:88`, `Pt/Deserialize.lean:144`). It also confirmed the PROP-37 deferral is
coherent with gate 5, since gate 5 checks citation resolution and not theorem truth.

## 2. What I did in response

- **F-1** — purged the superseded language everywhere: the permitted-diff criterion, the
  done-line, `01-VALIDATION`'s REV-01 row. Task 4's checkpoint item 3 now inspects the two
  **actual** deliverables (PROP-35's derived `Domain:` line, PROP-37's `Finding:` with no
  `Domain:` line) plus any other row the executor annotated, instead of re-requesting the
  superseded invariant ruling. Added a task to fix the status legend: an `Open` row carrying a
  `Finding:` annotation means "no theorem *and* no settled statement", with no new status value
  introduced.
- **F-2** — both new rows now cite
  `serialize.rs:95-202; serialize.rs:221-280`, with the reason written into the plan so a later
  editor does not trim it back: the review sees only the cited source, and the tag collapse and
  varint primitives live in the first range.
- **F-3** — defined the identity contract: a `Key` column of the form `<parent>/<slug>`
  (`PROP-35/roundtrip`, `PROP-35/components`, `PROP-47/transitions-1-5`) used uniformly for the
  CLI argument, the statement record filename, the artifact name and the log row, plus a
  `Parent` column holding the catalog ID or the literal `none` for a non-row work unit, which
  then carries its own `Source:`. A bare parent ID is rejected as ambiguous with the candidate
  keys listed. Catalog coverage is now checked by the **set of `Parent` values**, so the
  obligation-row count may exceed the registry size. The two-obligation `PROP-35` lookup is a
  required worked example in the SUMMARY.
- **F-4** — the §11 decision-table assertions now apply only from 01-08 task 1 onward, with the
  pre-01-08 zero count named as the expected reading; per-commit checking is reduced to the
  structural catalog check; the build prerequisite is scoped to the build-dependent gates
  (1, 2, 3a, 3b, 4) with gate 5 and the static checks explicitly exempt; the `01-08 T3` entry
  corrected to `01-08 T2`, wave 7.
- **F-5** — task 3 now specifies the interim ruling-and-resume path: persist, fill `Review:`,
  present, take the ruling, record it verbatim, then continue to the next statement. A deferral
  of STRUCT-02a does not cancel STRUCT-02b's review, and "the first one was rejected" is named
  as an insufficient reason for a missing second artifact.
- **F-6** — `PROJECT.md`'s whole-structure goal list now reads STRUCT-02a/02b plus PROP-37
  against Phase 7's invariant with injectivity as its corollary, and records the retirement.
  The target count is untouched.

## 3. What I deliberately did NOT do

- **Nothing was escalated this round.** Every finding was a bounded edit within the rulings
  already made, which is what APPROVE-WITH-EDITS means, and all of them are applied.
- **The status-legend wording** is specified as a task for the executor rather than written by
  me into `docs/spqr-properties.md`: the catalog is edited by the plans, in the PR, not by the
  planning seat mid-review.
- **PROP-38 and LEAN-ENC-1** are left as 01-07 already has them — the executor checks both and
  annotates or clears each. Codex cleared both on its own reading, but a cleared-by-review claim
  is not a substitute for the executor's recorded check, and 01-07 requires the SUMMARY to say
  so either way.
- **No re-review is required by the rubric** for an APPROVE-WITH-EDITS whose edits are all
  triaged and applied. Given that rounds 3 and 4 each found real defects introduced by the
  previous round's own patching, a sixth round scoped to 01-06 and 01-07 is available on request
  and is the conservative call — but it is not a gate on dispatch.
