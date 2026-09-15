<!--
Provenance
  reviewer:   Codex CLI (OpenRouter), cross-engine (not the planning engine)
  effort:     model_reasoning_effort = high
  sandbox:    read-only (bwrap, kernel-enforced)
  rubric:     docs/rubrics/spqr-plan-review.md (appended verbatim to the prompt)
  prompt:     /tmp/phase01-review-assignment-4.md
  raw output: /tmp/phase01-codex-review-4.md
  log:        /tmp/phase01-codex-review-4-log.txt
  date:       2026-09-15
  phase:      01-gates-provenance-and-target-list (plans 01-01 .. 01-09)
  branch:     la/spec-catalog @ d7cf202, working-tree revisions reviewed
  round:      4 (r1 REJECT, r2 APPROVE-WITH-EDITS, r3 REJECT)
  context:    reviewed after the user's 2026-09-15 rulings on round 3's four
              escalated questions, which amended REQUIREMENTS.md, ROADMAP.md,
              PROJECT.md and CLAUDE.md and caused 01-06 and 01-07 to be rewritten.
  note:       The Codex review below is verbatim and never edited. Planning-seat
              triage is appended after the --- separator.
-->

# SPQR Plan Review

- Phase: `.planning/phases/01-gates-provenance-and-target-list/`
- Plans reviewed: `01-01-PLAN.md` through `01-09-PLAN.md`, as one working-tree set, with amended contracts and `01-VALIDATION.md`
- Date: 2026-09-15
- Branch/base verified: `la/spec-catalog`, HEAD `d7cf202`, `origin/main` `e8f6689`; no `src/` difference against `d47083c`; `.lake/build` absent
- VERDICT: REJECT

## Findings

### F-1 — MAJOR

**Claim:** PROP-37’s proposed representability domain still admits states that fail the roundtrip, so the phase cannot honestly describe this catalog correction as complete.

**Evidence:**

The proposed correction adds only `pts_needed.val ≤ U32.max` for embedded decoders and says this makes the roundtrip true: `.planning/phases/01-gates-provenance-and-target-list/01-07-PLAN.md:188` and `.planning/phases/01-gates-provenance-and-target-list/01-07-PLAN.md:225`. The amended requirement makes the same assertion for all eleven variants: `.planning/REQUIREMENTS.md:44`.

That bound is necessary for preserving the narrowing cast, but it is not sufficient for deserialization:

- `Spqr/Specs/Encoding/Polynomial/PolyDecoder/IntoPb.lean:287` specifies **serialization**, not a decoder left-inverse. Its signature also includes `h_inner_overflow` at line 290.
- `src/v1/chunked/send_ct/serialize.rs:18` checks a variant-specific decoder size. The extracted check is explicit at `SrcTranslated/Funs.lean:12762`.
- Independently of decoder sizes, unchunked state deserializers validate stored byte-vector lengths. For example, `src/v1/unchunked/send_ct/serialize.rs:84` requires lengths `2080`, `960`, and `1152`; the corresponding extracted branches are at `SrcTranslated/Funs.lean:12265`.

A concrete counterexample avoids decoder fields and opaque cryptographic calls altogether:

| Step | State/value | Result |
|---|---|---|
| Construct `uc` | `Ct1SentEkReceived`: epoch `1`; authenticator keys empty; `es = []`, `ek = []`, `ct1 = []` | Well-typed: these fields are ordinary vectors, not length-indexed arrays (`SrcTranslated/Types.lean:1077`) |
| Construct encoder | `idx = 0`; `EncoderState.Points` containing sixteen empty `Point.value` vectors | Well-typed (`SrcTranslated/Types.lean:865`, `SrcTranslated/Types.lean:871`) |
| Construct state | `States.EkReceivedCt1Sampled { uc, sending_ct1 := encoder }` | Contains **no PolyDecoder**, so the proposed domain holds vacuously (`SrcTranslated/Types.lean:1087`) |
| Serialize | Inner serializer copies `es`, `ek`, and `ct1`; encoder serializes sixteen empty point vectors | Successful protobuf value; `pb.uc.es.length = 0` (`SrcTranslated/Funs.lean:10639`, `SrcTranslated/Funs.lean:8449`) |
| Deserialize inner state | Test `pb.es.length = 2080` | False; returns `ok (.Err Error.StateDecode)` (`SrcTranslated/Funs.lean:12265`, `SrcTranslated/Funs.lean:12294`) |
| Propagate through wrappers | Chunked wrapper, then `States.from_pb` | Same error, not `ok (.Ok originalState)` (`SrcTranslated/Funs.lean:12329`, `SrcTranslated/Funs.lean:12895`) |

This is a recurrence of round 3 F-2’s missing-validity-domain problem, not merely the already-corrected cast counterexample.

The retirement argument itself is mathematically sound **given a successful left-inverse law on an adequate domain**. In this extraction that law must use monadic composition because `States.into_pb` returns `Result V1State` (`SrcTranslated/Funs.lean:10723`). The proposed roundtrip does not establish the required premise on its stated domain.

This requires renewed planning rather than just a wording cleanup: `.planning/phases/01-gates-provenance-and-target-list/01-07-PLAN.md:392` expressly treats stronger variant-specific conditions as work ruled out on September 15, 2026.

**Minimal suggested edit:** Reopen the domain ruling with this counterexample. Specify the necessary state-validity conditions—including relevant byte-vector lengths and decoder-size checks—and account for component-spec preconditions, then amend STRUCT-03, ROADMAP Phase 7, and the planned catalog correction together. Alternatively, explicitly defer the roundtrip correction rather than certify the cast bound as sufficient.

### F-2 — MAJOR

**Claim:** The statement-record instructions incorrectly tell the executor that extracted `Message.serialize` returns a vector rather than a `Result`.

**Evidence:**

`.planning/phases/01-gates-provenance-and-target-list/01-07-PLAN.md:270` says:

> `Message.serialize` is total and returns the byte vector

It then expressly says the witness equality is “not a `Result` equality.”

The extracted declaration is:

```lean
def v1.chunked.states.serialize.Message.serialize
  (self : v1.chunked.states.Message) (index : Std.U32) :
  Result (alloc.vec.Vec Std.U8)
```

Source: `SrcTranslated/Funs.lean:11460`.

`Message.serialize_spec` proves unconditional success through WP notation; it does not change that return type (`Spqr/Specs/V1/Chunked/States/Serialize/Message/Serialize.lean:75`). Consequently, an equality between two extracted `serialize` applications **is** an equality of `Result` values. Membership in the successful encoder image likewise needs `serialize message index = ok bytes`, not a vector-valued application.

The proposed witnesses otherwise survive direct inspection:

| Input | Successful output |
|---|---|
| Epoch `1`, `Ct1Ack false`, index `0` | `ok [01 01 00 04]` |
| Epoch `1`, `Ct1Ack true`, index `0` | `ok [01 01 00 04]` |
| Bytes `01 01 00 00` | `ok (.Ok (Message(1, None), 0, 4))` |
| Bytes `01 81 00 00 00` | `ok (.Ok (Message(1, None), 0, 5))` |

The Boolean is discarded at `SrcTranslated/Funs.lean:11483`. The decoder’s nested result and triple are declared at `SrcTranslated/Funs.lean:14163`; its `None` return is at line 14222.

Thus the second pair witnesses non-injectivity of the **successful `(message, index)` projection**, not equality of the complete decoder results. Task 1 already acknowledges the differing cursors; the statement record must preserve that distinction.

This is a new incorrect signature assertion in the area addressed by round 3 F-7.

**Minimal suggested edit:** Correct the return-type instruction. Require successful encoder-image membership and witness equations using the actual `Result` constructors, and explicitly name the decoder projection whose non-injectivity STRUCT-02a witnesses.

### F-3 — MAJOR

**Claim:** The corrected registry algorithm is still contradicted by mandatory downstream count checks.

**Evidence:**

Independent enumeration produced:

```text
headings: 28 section 10: 9 section 11: 5
registry: 42 index rows: 38 symmetric difference: []
```

The new algorithm correctly explains this at `.planning/phases/01-gates-provenance-and-target-list/01-02-PLAN.md:255`, including `STRUCT-` headings and joining duplicate deviation IDs.

However, the following requirements remain:

| Location | Remaining requirement | Why it cannot validate the intended result |
|---|---|---|
| `01-02-PLAN.md:306` | Explain differences from **39** as catalog gains/losses | The unchanged starting catalog already has 42 entries |
| `01-03-PLAN.md:251` | Registry count equals index length | Correct values are 42 and 38 |
| `01-03-PLAN.md:256` | At least 39 literal `Source:` occurrences | Task 2 puts table citations in a `Source` **column**, not literal `Source:` fields |
| `01-03-PLAN.md:257` | Again require count equality | Contradicts that plan’s corrected acceptance criteria at line 190 |
| `01-08-PLAN.md:112` | Checker must “still” report 42 entries | Its dependency, 01-07, has added two entries and explicitly requires 42 → 44 |
| `01-VALIDATION.md:106` | Count equals index length, at least 39 | Reintroduces the same impossible contract |

All paths in this table are under `.planning/phases/01-gates-provenance-and-target-list/`.

This recurs from round 3 F-3. An implementation following the revised parser design still cannot satisfy the complete plan set.

**Minimal suggested edit:** Replace every residual count-equality/token-count assertion with normalized ID-set agreement and checker-reported citation coverage. Use 42 registry entries/38 index rows before 01-07 and 44/40 afterward; distinguish registry coverage from the potentially larger per-obligation target table.

### F-4 — MAJOR

**Claim:** The new `--support` mode remains unreachable for the support obligations it is intended to review.

**Evidence:**

- Excluded-band obligations receive `C3 = fail`, hence `Target? = no`: `.planning/phases/01-gates-provenance-and-target-list/01-06-PLAN.md:163`.
- The skill’s resolution step unconditionally stops on `Target? = no`: `.planning/phases/01-gates-provenance-and-target-list/01-06-PLAN.md:328`.
- The reduced rubric is selected only later, during assignment assembly at line 343.
- The proposed PR checklist additionally requires the property to be a target: `.planning/phases/01-gates-provenance-and-target-list/01-01-PLAN.md:119`.

The contradiction is visible as a short control-flow trace:

| Stage | Support obligation |
|---|---|
| Classification | Excluded band; named target dependency; `Target? = no` |
| Invocation | `/spqr-statement-review <obligation> --support` |
| Resolution | Stops because the entry is `no` |
| Reduced C2/vacuity review | Never reached |
| Recorded support ACCEPT | Cannot be produced |

This directly defeats the permission in `.planning/PROJECT.md:47` to prove support lemmas when a target needs them. It recurs from round 3 F-6.

**Minimal suggested edit:** Branch eligibility on `--support` **before** target-only rejection. Permit documented support obligations with named target dependencies and appropriate source evidence, while retaining target-only eligibility for ordinary mode. Give the checklist a corresponding support-work route without promoting support lemmas into the target count.

### F-5 — MAJOR

**Claim:** The C1 evidence channel does not specify a `main` snapshot, so its prescribed search can certify novelty against the wrong tree.

**Evidence:**

C1 means “no theorem on `main`,” both in `.planning/PROJECT.md:26` and `.planning/phases/01-gates-provenance-and-target-list/01-06-PLAN.md:156`.

The packet is nevertheless specified as a name-and-signature search over `Spqr/Specs/**`, without a ref, source SHA, or baseline checkout procedure:

- `.planning/phases/01-gates-provenance-and-target-list/01-06-PLAN.md:261`
- `.planning/phases/01-gates-provenance-and-target-list/01-06-PLAN.md:339`

Calling its output “pinned” does not define what revision it represents.

This checkout demonstrates the distinction:

```text
rg -n 'epoch_idx_spec|theorem .*epoch_idx|def .*epoch_idx' Spqr/Specs
→ no matches
```

But:

```text
git show origin/main:Spqr/Specs/Chain/Chain/EpochIdx.lean
→ @[step]
  theorem epoch_idx_spec (self : chain.Chain) (epoch : U64) ...
```

The theorem is at `Spqr/Specs/Chain/Chain/EpochIdx.lean:24` **in `origin/main` at `e8f6689`**, a file absent from the working tree. Its signature describes `Chain.epoch_idx`; the current catalog still calls PROP-29 open at `docs/spqr-properties.md:415`.

This is the remaining C1-evidence defect from round 3 F-7. A statement hash does not authenticate the revision used for its novelty decision.

**Minimal suggested edit:** Define C1’s baseline as an explicitly resolved `main` SHA; search that revision, include the SHA and search scope with the signature extract, and use the same baseline for target classification and review. Keep working-tree extraction/type evidence separately identified.

### F-6 — MAJOR

**Claim:** The validation schedule still requires nonexistent tooling and full runs before their prerequisites are produced.

**Evidence:**

`.planning/phases/01-gates-provenance-and-target-list/01-VALIDATION.md:48` mandates a full, baseline-backed gate run **after every plan wave**. It additionally requires “the issue-script dry-run over all IDs” at line 54.

That contradicts both the revised schedule and the same document:

| Requirement | Actual producer/contract |
|---|---|
| Full run after wave 1 | 01-02 explicitly writes but does not run the runner; building/running belongs to 01-04 (`01-02-PLAN.md:70`) |
| Gate 5 reference lists and citation retrofit | Produced by 01-03 in **wave 2** (`01-03-PLAN.md:5`) |
| Built tree and measured baseline | Produced by 01-04 in **wave 3** (`01-04-PLAN.md:5`, `01-04-PLAN.md:111`) |
| Issue-script dry-run | The script is expressly not a deliverable and must not appear in a validation path (`01-VALIDATION.md:39`) |

The per-task map is also not synchronized: it still assigns 01-03 to wave 1, 01-04 to wave 2, and 01-07 reviews to task 2/wave 5 (`01-VALIDATION.md:75`, `01-VALIDATION.md:105`, `01-VALIDATION.md:109`). Current 01-07 task 2 writes records; task 3 runs reviews.

All paths in the table are under the phase directory.

This recurs from round 3 F-9 and leaves a prerequisite-ordering residue related to F-5 of that round. The plan-frontmatter DAG is repaired; the mandatory validation consumer is not.

**Minimal suggested edit:** Remove the issue-script path, update the task/wave map, and stage validation: static and expected-red checks before prerequisites exist; full five-gate runs after 01-04 and at PR boundaries. Do not describe intentionally unavailable prerequisites as failed implementation evidence.

### F-7 — MAJOR

**Claim:** Final preservation checks still demand modification of preserved state or an impossible result despite the corrected task-level checks.

**Evidence:**

Two previous findings remain verbatim in terminal verification sections:

| Surface | Corrected task-level rule | Residual terminal rule | Measured state |
|---|---|---|---|
| `CLAUDE.md` markers | Check all seven named pairs (`01-01-PLAN.md:190`) | `grep -c 'GSD:' CLAUDE.md` → **8** (`01-01-PLAN.md:203`) | **14** |
| User stashes | Compare against baseline; never drop/pop/clear pre-existing stashes (`01-04-PLAN.md:285`) | `git stash list` empty (`01-04-PLAN.md:316`) | **5** entries |

All plan paths are under `.planning/phases/01-gates-provenance-and-target-list/`.

Additionally, `01-VALIDATION.md:142` still permits a “stashed change” for negative controls, contrary to `01-04-PLAN.md:213`, which requires a throwaway worktree and forbids parking breakage in a stash.

These recur from round 3 F-8 and planning-seat PS-1. The stash baseline correction is substantive and good, but the plan’s final checks still cannot pass while preserving the user’s existing state.

**Minimal suggested edit:** Apply the named-pair and baseline-stash rules to the terminal verification sections too; remove the stashed-change alternative from validation. Preserve all existing stashes and marker pairs.

### F-8 — MINOR

**Claim:** Two consumers still request the retired `PR B branch:` field after the producer was changed to separate head and base fields.

**Evidence:**

The corrected producer requires `PR B head:` and `PR B base:` at `.planning/phases/01-gates-provenance-and-target-list/01-05-PLAN.md:154`, and 01-09’s range commands correctly consume the base at `.planning/phases/01-gates-provenance-and-target-list/01-09-PLAN.md:87`.

Nevertheless:

- `01-05-PLAN.md:180` verifies that `PR B branch:` exists.
- `01-09-PLAN.md:112` tells the user to open the PR based on the branch named in that obsolete field.

This is a bounded residual recurrence of round 3 F-10; the principal head/base separation is now present.

**Minimal suggested edit:** Verify both new fields in 01-05’s final section; use `PR B base:` for the PR-opening instruction and `PR B head:` for the source branch.

### F-9 — MINOR

**Claim:** The review workflow does not fill catalog review references on its legitimate non-ACCEPT path, although completion forbids empty references.

**Evidence:**

Only the ACCEPT branch explicitly fills `Review:` at `.planning/phases/01-gates-provenance-and-target-list/01-07-PLAN.md:326`. REJECT and HUMAN_RULING route to task 4 instead.

Task 4 expressly permits deferring either row (`01-07-PLAN.md:386`) and requires corresponding planning updates, but does not specify filling the catalog reference to the already-persisted negative review. Meanwhile task 3 and final verification require no empty `Review:` placeholder (`01-07-PLAN.md:352`, `01-07-PLAN.md:441`).

The existing artifacts and checkpoint make recovery straightforward, but the written negative-result route is incomplete.

**Minimal suggested edit:** Record the artifact reference for every validated review verdict; separately restrict promotion to `Target? = yes` to ACCEPT. Specify the final catalog/target-table state when a row is deferred.

## Cleared surfaces

1. **Catalog fidelity.** PROP-35’s two semantic restrictions are justified: the decoder rejects epoch zero and reconstructs `Ct1Ack true` (`src/v1/chunked/states/serialize.rs:254`, `src/v1/chunked/states/serialize.rs:267`). No further message-field domain defect was found: epoch/index/chunk-index widths and the fixed 32-byte chunk data bound serialized messages to at most 52 bytes, so the merged decoder’s buffer-overflow premise does not require an additional restriction on messages (`SrcTranslated/Types.lean:904`, `Spqr/Specs/V1/Chunked/States/Serialize/Message/Deserialize.lean:61`). PROP-37 is not cleared, for F-1.

2. **Internal consistency.** The frontmatter ordering is now coherent: 01-01/02 wave 1; 03 wave 2; 04 wave 3; 05 wave 4; 06 wave 5; 07 wave 6; 08 wave 7; 09 wave 8. Candidate registration precedes the new-row reviews (`01-07-PLAN.md:204`). Conditional requirements/roadmap writes are declared in 01-06 and 01-07. Remaining contradictory consumers are identified in F-3, F-6, F-7, and F-8.

3. **Statement-level soundness.** Concrete STRUCT-02a witnesses are genuinely informative, not vacuous merely because they are concrete. The short varint pair has different cursors; the ten-byte pair has equal length and equal truncated value (`Spqr/Specs/V1/Chunked/States/Serialize/DecodeVarint.lean:44`). STRUCT-02b can be stated non-circularly using an independently quantified successful encoder preimage plus explicit block/cursor conditions; membership in an encoder image does not itself assume decoder injectivity. No completed predicate exists yet to certify, and F-2 must be corrected before writing it.

4. **Semantic closure.** The D5 distinction is correct: ciphertext verification follows a local authenticator update, whereas header verification precedes construction of the next unchunked state. The extracted public conversion is `Error.MacVerifyFailed` (`SrcTranslated/Funs.lean:10339`).

   | Path, with preceding operations successful | Local state | Return/caller effect |
   |---|---|---|
   | Completing Ct2, MAC succeeds, epoch `e < U64.max` | Authenticator updated | Next unchunked state has epoch `e+1`; emitted key has epoch `e` (`SrcTranslated/Funs.lean:13243`, `SrcTranslated/Funs.lean:13255`) |
   | Completing Ct2, MAC fails | Updated authenticator exists only locally | Error propagates; no next state/key payload (`SrcTranslated/Funs.lean:13248`, `SrcTranslated/Funs.lean:13257`) |
   | Header MAC fails | Next `HeaderReceived` not constructed | Same public MAC error (`SrcTranslated/Funs.lean:13585`) |
   | Public `recv` receives that error | Input serialized state is immutable | Returns before construction of successful serialized state (`src/lib.rs:356`, `src/lib.rs:425`, `src/lib.rs:438`) |

   D2’s exceptional Ct2Sampled next-epoch arm, D3’s acknowledgment behavior, and D4’s extra accepted `Ek` chunks match the inspected Rust branches (`src/v1/chunked/states.rs:182`, `src/v1/chunked/states.rs:464`, `src/v1/chunked/states.rs:489`, `src/v1/chunked/states.rs:513`). No zeroization or session-teardown guarantee follows, and 01-08 correctly disclaims them.

5. **Precedent and interface realism.** The cited `serialize_spec`, `deserialize_spec`, decoder `into_pb_spec`, and authenticator `update_spec` exist and are tagged `@[step]`. The decoder and authenticator hypotheses were checked from declarations, not inferred from descriptions. No new proof-module import/re-export is required by this infrastructure phase. F-2 and F-5 identify the remaining interface/baseline defects.

6. **Trusted-base discipline.** The intended allowlist’s sixteen external names exist, including the multiline declaration at `SrcTranslated/FunsExternal.lean:3687`; adding the HKDF axiom and three builtins gives twenty. The HKDF namespace and root-level external names are correct. No new delivered axiom, proof, or trusted `sorry` is authorized. Scratch negative controls are explicitly segregated from the committed patch.

7. **Gates.** The design retains a wrap-aware axiom parser, rejection of absent reports and misspelled targets, regenerated head manifests, SHA-keyed baselines, and mandatory negative controls. `scripts/Audit.lean:23` imports `Spqr`, and its manifest is generated from imported declarations at line 246, supporting the documented re-export blind spot. CI’s sorry delta is advisory while local policy is stricter (`.github/workflows/sorry-delta-comment.yml:43`). Runtime behavior was not tested in this unbuilt, read-only checkout. F-3, F-6, and F-7 concern the written validation contract.

8. **Boundedness and safety.** All delivered changes are documentation/tooling; no plan authorizes editing the extraction or production Rust. The source pin is unchanged. PR creation remains a user action. The stash-protection instructions are present, although conflicting residual checks must be removed. Missing future deliverables and locally unavailable PDFs were not treated as findings; 01-03 explicitly stops if the required PDFs cannot be located.

9. **Roadmap and catalog coherence.** The split into STRUCT-02a/02b and retirement of STRUCT-04 preserve the stated target-count construction; no additional target is proposed here. The retirement retains both the injectivity corollary and off-domain counterexample obligation (`.planning/REQUIREMENTS.md:45`). Its logical justification depends on repairing F-1. PROP-38’s inspected Rust conversion preserves fields and wraps required option fields; no analogous decoder-size/cast-domain defect was found (`src/chain.rs:298`, `src/chain.rs:414`). LEAN-ENC-1 uses two `U16` coordinates and fixed four-byte encoding, with unconditional component specs; no analogous domain restriction was found. The instruction to report any further roundtrip defect rather than silently edit it is appropriate (`01-07-PLAN.md:195`).

## Probe log

All shell probes were read-only. No build, elaboration, proof attempt, repository write, stash mutation, or network-side mutation was performed. Several large reads were truncated by the tool; narrower follow-up reads are included below. Commands are recorded verbatim.

### Checkout and initial plan reads

```bash
pwd; git status --short; git rev-parse --abbrev-ref HEAD; git rev-parse --short HEAD origin/main; git diff --name-only d47083c..HEAD -- src; rg --files -g AGENTS.md -g '01-*-PLAN.md' -g '01-*REVIEW*.md' -g '01-RESEARCH.md' -g '01-VALIDATION.md' .planning docs scripts .claude; ls -d .lake/build 2>/dev/null
```

Result: working-tree planning/contract changes confirmed; source diff empty; build directory absent. The combined `rev-parse --short` invocation rejected multiple revisions; corrected below.

```bash
for directory in / /home /home/lacra /home/lacra/git_repos /home/lacra/git_repos/baif /home/lacra/git_repos/baif/SparsePostQuantumRatchet-verify; do if test -f "$directory/AGENTS.md"; then printf '\n--- %s ---\n' "$directory/AGENTS.md"; cat "$directory/AGENTS.md"; fi; done; rg --files --hidden -g AGENTS.md -g '!\.git' .; git rev-parse --short HEAD; git rev-parse --short origin/main; git diff --name-only d47083c -- src; for file in .planning/phases/01-gates-provenance-and-target-list/01-0{6,7}-PLAN.md; do printf '\n--- %s ---\n' "$file"; nl -ba "$file"; done
```

Result: `d7cf202`, `e8f6689`; no source difference or AGENTS output; plan output truncated.

```bash
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-06-PLAN.md | sed -n '95,310p'; nl -ba .planning/phases/01-gates-provenance-and-target-list/01-07-PLAN.md | sed -n '1,285p'
```

Result: target/review and statement tasks inspected; output truncated.

```bash
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-06-PLAN.md | sed -n '170,355p'
```

Result: target-count, record, and skill requirements inspected; output truncated.

```bash
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-06-PLAN.md | sed -n '223,292p'; nl -ba .planning/phases/01-gates-provenance-and-target-list/01-06-PLAN.md | sed -n '350,460p'
```

Result: C1 evidence, support mode, hashing, checkpoint, and terminal checks inspected.

```bash
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-07-PLAN.md | sed -n '1,125p'
```

Result: scope, outputs, and source claims inspected.

```bash
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-07-PLAN.md | sed -n '126,219p'; nl -ba .planning/phases/01-gates-provenance-and-target-list/01-06-PLAN.md | sed -n '280,290p'; nl -ba .planning/phases/01-gates-provenance-and-target-list/01-06-PLAN.md | sed -n '350,387p'
```

Result: witnesses, canonical-domain prescription, retirement, domain corrections, log shape, and skill acceptance inspected.

```bash
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-07-PLAN.md | sed -n '188,240p'; nl -ba .planning/phases/01-gates-provenance-and-target-list/01-07-PLAN.md | sed -n '284,375p'
```

Result: correction boundaries, candidate registration, and review verdict branches inspected.

### Contracts and extracted message interfaces

```bash
wc -l .planning/phases/01-gates-provenance-and-target-list/{01-0*-PLAN.md,01-VALIDATION.md,01-RESEARCH.md,01-CODEX-REVIEW*.md} .planning/{PROJECT,REQUIREMENTS,ROADMAP,STATE}.md; rg -n 'PROV-01|STRUCT-0[1234]|22|C1|Source:|Evidence:|Domain:|2026-09-15|REV-01' .planning/{PROJECT,REQUIREMENTS,ROADMAP,STATE}.md CLAUDE.md
```

Result: amendment locations and document sizes identified.

```bash
nl -ba .planning/REQUIREMENTS.md | sed -n '1,95p'; nl -ba .planning/PROJECT.md | sed -n '12,42p'; nl -ba .planning/PROJECT.md | sed -n '96,112p'
```

Result: provenance/review constraints and amended targets inspected.

```bash
nl -ba .planning/REQUIREMENTS.md | sed -n '39,54p'; nl -ba .planning/PROJECT.md | sed -n '21,35p'; nl -ba .planning/ROADMAP.md | sed -n '65,82p'; nl -ba .planning/ROADMAP.md | sed -n '160,176p'; nl -ba .planning/phases/01-gates-provenance-and-target-list/01-07-PLAN.md | sed -n '288,310p'
```

Result: STRUCT-03/04 contract, Phase 1/7 criteria, and record acceptance requirements confirmed.

```bash
rg -n '^def .*Message\.(serialize|deserialize)|^def .*States\.(into_pb|from_pb)|^structure .*Message|^inductive .*MessagePayload|^def .*PolyDecoder\.(into_pb|from_pb)' SrcTranslated/{Funs,Types}.lean; nl -ba SrcTranslated/Funs.lean | sed -n '14095,14245p'
```

Result: decoder nested-result/triple signature and successful `None` branch confirmed.

```bash
nl -ba SrcTranslated/Funs.lean | sed -n '11455,11545p'; nl -ba Spqr/Specs/V1/Chunked/States/Serialize/Message/Deserialize.lean | sed -n '1,84p'
```

Result: serializer returns `Result`; decoder spec’s buffer premise and successful-output restrictions confirmed.

```bash
nl -ba Spqr/Specs/V1/Chunked/States/Serialize/Message/Serialize.lean | sed -n '32,80p'; nl -ba SrcTranslated/Types.lean | sed -n '1100,1196p'; nl -ba Spqr/Specs/Encoding/Polynomial/PolyDecoder/IntoPb.lean | sed -n '276,298p'
```

Result: serializer model/success spec, message/state types, and both decoder serialization hypotheses inspected.

### Remaining plan set

```bash
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-01-PLAN.md | sed -n '1,110p'
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-01-PLAN.md | sed -n '111,213p'
```

Result: checklist requirements inspected; residual eight-marker assertion found.

```bash
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-02-PLAN.md | sed -n '1,115p'
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-02-PLAN.md | sed -n '116,213p'
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-02-PLAN.md | sed -n '214,296p'
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-02-PLAN.md | sed -n '296,355p'; nl -ba .planning/phases/01-gates-provenance-and-target-list/01-03-PLAN.md | sed -n '1,75p'
```

Result: runner, baseline, allowlist, parser, and registry design inspected; residual 39-entry checks found.

```bash
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-03-PLAN.md | sed -n '74,172p'
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-03-PLAN.md | sed -n '173,268p'; nl -ba .planning/phases/01-gates-provenance-and-target-list/01-04-PLAN.md | sed -n '1,65p'
```

Result: PDF stop condition and Source-column design confirmed; contradictory terminal enumeration checks found.

```bash
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-04-PLAN.md | sed -n '66,167p'
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-04-PLAN.md | sed -n '166,261p'
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-04-PLAN.md | sed -n '262,325p'; nl -ba .planning/phases/01-gates-provenance-and-target-list/01-05-PLAN.md | sed -n '1,102p'
```

Result: empirical probes, CI comparison, negative controls, and cleanup inspected; residual empty-stash requirement found.

```bash
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-05-PLAN.md | sed -n '1,18p;103,188p'; nl -ba .planning/phases/01-gates-provenance-and-target-list/01-06-PLAN.md | sed -n '80,96p'
```

Result: corrected head/base producer and precondition confirmed; old-field terminal consumer found.

```bash
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-08-PLAN.md | sed -n '1,115p'
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-08-PLAN.md | sed -n '115,212p'
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-08-PLAN.md | sed -n '212,248p'; nl -ba .planning/phases/01-gates-provenance-and-target-list/01-09-PLAN.md | sed -n '1,105p'
```

Result: deviation decisions and PR B checks inspected; obsolete post-01-07 registry count found.

```bash
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-09-PLAN.md | sed -n '106,166p'; nl -ba .planning/phases/01-gates-provenance-and-target-list/01-VALIDATION.md | sed -n '1,90p'
```

Result: old PR B field and premature/nonexistent validation consumers found.

```bash
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-VALIDATION.md | sed -n '23,40p;90,152p'
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-VALIDATION.md | sed -n '153,190p'; rg -n '^### F-|^\*\*Claim|^### PS-|^## |^### .*F-' .planning/phases/01-gates-provenance-and-target-list/01-CODEX-REVIEW-3.md
```

Result: validation controls and stale task/wave mappings inspected; prior finding locations identified.

```bash
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-CODEX-REVIEW-3.md | sed -n '673,776p'; rg -n '^### F-|^\*\*Claim|^## .*triage|^## [0-9]' .planning/phases/01-gates-provenance-and-target-list/01-CODEX-REVIEW{,-2}.md
```

Result: prior claims and triage inspected as review data; recurrence labels checked.

### Serialization and catalog evidence

```bash
nl -ba SrcTranslated/Types.lean | sed -n '910,960p;1025,1100p'; nl -ba src/v1/chunked/send_ct/serialize.rs | sed -n '1,130p'
```

Result: unconstrained decoder/state fields and variant-specific decoder-size checks identified.

```bash
nl -ba src/encoding/polynomial.rs | sed -n '780,850p'; rg -n 'NoHeaderReceived\.(into_pb|from_pb)' SrcTranslated/Funs.lean; nl -ba src/v1/unchunked/send_ct/serialize.rs | sed -n '1,103p'
```

Result: narrowing cast, decoder conversion, and state byte-vector length checks inspected.

```bash
nl -ba SrcTranslated/Funs.lean | sed -n '10700,10730p;12715,12778p;12860,12881p'; nl -ba src/incremental_mlkem768.rs | sed -n '8,21p'; nl -ba docs/spqr-properties.md | sed -n '259,278p;395,429p'
```

Result: extracted size-check path and PROP-37/38 statements inspected.

```bash
nl -ba docs/spqr-properties.md | sed -n '1,75p'; nl -ba docs/spqr-properties.md | sed -n '205,256p'; nl -ba SrcTranslated/Funs.lean | sed -n '12762,12773p'; rg -n 'def incremental_mlkem768.HEADER_SIZE|def libcrux_ml_kem.*pk1_len|def authenticator.Authenticator.MACSIZE' SrcTranslated/Funs.lean
```

Result: catalog source/status conventions, PROP-35/36, and extracted size comparison inspected.

```bash
nl -ba src/v1/chunked/states/serialize.rs | sed -n '140,185p;220,280p'; nl -ba Spqr/Specs/V1/Chunked/States/Serialize/DecodeVarint.lean | sed -n '29,60p'; rg -n 'LEAN-ENC-1|into_pb_spec|from_pb_spec' docs/spqr-properties.md Spqr/Specs/Encoding/Polynomial/PolyDecoder/FromPb.lean Spqr/Specs/Chain/Chain/{IntoPb,FromPb}.lean
```

Result: wire traces and truncation semantics confirmed. The two requested `Chain/Chain` spec paths do not exist; no claim relied on them.

### Gate and main-baseline evidence

```bash
nl -ba scripts/check-lint.sh; nl -ba scripts/sorry-diff.py | sed -n '1,120p'; nl -ba .github/workflows/lean.yml | sed -n '38,86p'; nl -ba .github/workflows/sorry-delta-comment.yml | sed -n '30,52p'
```

Result: current commands, manifest handling, and local-versus-CI policy inspected.

```bash
git diff --name-only origin/main..HEAD -- '*.lean' lakefile.toml lean-toolchain lake-manifest.json; git show origin/main:Spqr/Specs/Chain/Chain/EpochIdx.lean | nl -ba | sed -n '1,95p'; rg -n 'epoch_idx_spec|theorem .*epoch_idx|def .*epoch_idx' Spqr/Specs; rg -n '^(axiom|opaque)|^(namespace|open spqr)' Spqr/Specs/Kdf/HkdfToSlice.lean Spqr/Crypto/Hkdf.lean; nl -ba .planning/phases/01-gates-provenance-and-target-list/01-RESEARCH.md | sed -n '540,591p'
```

Result: four upstream Lean differences; `epoch_idx_spec` present on `origin/main` but absent locally; HKDF names and allowlist recipe inspected.

```bash
nl -ba docs/spqr-properties.md | sed -n '75,150p'; nl -ba docs/spqr-properties.md | sed -n '151,204p'
nl -ba docs/spqr-properties.md | sed -n '278,354p'; nl -ba docs/spqr-properties.md | sed -n '355,395p;430,491p'
```

Result: catalog obligations, deviation statements, and index inspected.

```bash
python3 - <<'PY'
from pathlib import Path
import re
text = Path('docs/spqr-properties.md').read_text()
headings = re.findall(r'^### ((?:PROP|LEAN|STRUCT)-\S+)', text, re.M)
sections = {number: re.search(rf'^## {number}\.\s.*?(?=^## |\Z)', text, re.M | re.S).group() for number in (10, 11, 12)}
rows = {number: re.findall(r'^\| ((?:PROP|LEAN)-\S+|D\S*) \|', section, re.M) for number, section in sections.items()}
registry = set(headings + rows[10] + rows[11])
index = set(rows[12])
expanded_index = (index - {'D1–D5'}) | {f'D{number}' for number in range(1,6)}
print('headings:', len(headings), 'section 10:', len(rows[10]), 'section 11:', len(rows[11]))
print('registry:', len(registry), 'index rows:', len(index), 'symmetric difference:', sorted(registry ^ expanded_index))
print('standalone Source tokens:', len(re.findall(r'^Source:', text, re.M)))
PY
printf 'GSD lines: '; grep -c 'GSD:' CLAUDE.md; printf 'Stashes: '; git stash list | wc -l; rg -n '^(import Spqr|def .*classify|def .*Manifest|#eval)|sorry-manifest|isSpecsModule|sorryAx|collectAxioms' scripts/Audit.lean; rg -n 'LEAN_ABORT_ON_PANIC' .github/workflows/lean.yml; rg --files Spqr/Specs | rg '(Pt/|Serialize/(IntoPb|FromPb)|Chain.*Pb|PolyEncoder/FromPb)'
```

Result: registry/index `42/38`, empty normalized symmetric difference, zero existing standalone Source fields, fourteen marker lines, five stashes; audit and spec inventory confirmed.

```bash
nl -ba .planning/REQUIREMENTS.md | sed -n '107,135p'; nl -ba .planning/PROJECT.md | sed -n '22,55p'; nl -ba .planning/phases/01-gates-provenance-and-target-list/01-CODEX-REVIEW-3.md | sed -n '696,776p'
```

Result: support permission, prior stash finding, and claimed fixes checked.

### Further domain and semantic checks

```bash
nl -ba Spqr/Specs/Encoding/Polynomial/Pt/Serialize.lean | sed -n '15,60p'; nl -ba Spqr/Specs/Encoding/Polynomial/Pt/Deserialize.lean | sed -n '15,70p'; nl -ba src/chain.rs | sed -n '414,456p'; rg -n 'fn into_pb|fn from_pb' src/chain.rs; nl -ba Spqr/Specs/Encoding/Polynomial/PolyDecoder/FromPb.lean | sed -n '571,625p'
```

Result: point/chain conversion semantics and decoder deserialization preconditions inspected.

```bash
nl -ba src/chain.rs | sed -n '290,321p'; nl -ba Spqr/Specs/Encoding/Polynomial/Pt/Serialize.lean | sed -n '60,83p'; rg -n '^theorem deserialize_spec|^theorem.*round|^def .*Pt\.(serialize|deserialize)|^structure encoding.polynomial.Pt' Spqr/Specs/Encoding/Polynomial/Pt/Deserialize.lean SrcTranslated/{Funs,Types}.lean; nl -ba .planning/REQUIREMENTS.md | sed -n '168,183p'; nl -ba scripts/Audit.lean | sed -n '21,33p;70,95p;246,257p'
```

Result: chain field preservation, point declarations, obligation-count explanation, and audit traversal inspected.

```bash
nl -ba src/encoding/polynomial.rs | sed -n '430,501p'; nl -ba SrcTranslated/Funs.lean | sed -n '9340,9363p'; nl -ba Spqr/Specs/Encoding/Polynomial/Pt/Deserialize.lean | sed -n '137,152p'; nl -ba Spqr/Specs/Encoding/Polynomial/Pt/Serialize.lean | sed -n '85,101p'; nl -ba SrcTranslated/Types.lean | sed -n '705,735p'; nl -ba SrcTranslated/FunsExternal.lean | sed -n '1832,1854p'
```

Result: extracted decoder cast, unconditional point specs, vector-valued authenticator fields, and constant stubs inspected.

```bash
rg -n 'def cast|def wrap_cast|def tryMk|def castCore' .lake/packages/aeneas/backends/lean/Aeneas/Std/Scalar* .lake/packages/aeneas/backends/lean/Aeneas/Std --glob '*.lean' | head -50; rg --files .lake/packages/aeneas | rg '/Scalar|Sorted'; rg -n 'PolyEncoder|pub\(crate\) fn into_pb|pub\(crate\) fn from_pb' src/encoding/polynomial.rs | tail -16; rg -n 'HEADER_SIZE_spec|pk1_len_spec|pk2_len_spec' Spqr/Specs SrcTranslated/FunsExternal.lean
```

Result: cast-definition location identified; no matching constant specs from the final search.

```bash
nl -ba .lake/packages/aeneas/backends/lean/Aeneas/Std/Scalar/Casts.lean | sed -n '1,97p'; nl -ba src/encoding/polynomial.rs | sed -n '527,608p'; nl -ba SrcTranslated/Funs.lean | sed -n '10042,10053p'; rg -n 'namespace|def lift|abbrev lift' .lake/packages/aeneas/backends/lean/Aeneas/Std/Result* | head -22
```

Result: unsigned cast truncates/zero-extends; encoder conversion inspected. The final Result-path glob did not exist.

```bash
nl -ba src/authenticator.rs | sed -n '10,18p;32,55p'; nl -ba src/lib.rs | sed -n '137,150p;350,368p;405,447p'; nl -ba src/v1/unchunked/send_ek.rs | sed -n '136,168p'; nl -ba src/v1/unchunked/send_ct.rs | sed -n '102,118p'; nl -ba Spqr/Specs/Authenticator/Authenticator/Update.lean | sed -n '44,65p'
```

Result: D1 implementation/spec agreement and D5 public-error/ordering/caller-state behavior confirmed.

```bash
rg -n '^def v1\.(un)?chunked\.(send_ct|send_ek)\.serialize\.(HeaderReceived|Ct1SentEkReceived|EkReceivedCt1Sampled)\.(into_pb|from_pb)|^def encoding.polynomial.PolyEncoder.into_pb|^inductive encoding.polynomial.EncoderState|^structure encoding.polynomial.(Point|PolyEncoder)' SrcTranslated/{Funs,Types}.lean; nl -ba SrcTranslated/Funs.lean | sed -n '12235,12306p'; nl -ba src/v1/chunked/states.rs | sed -n '176,193p;200,224p;459,494p;506,530p'
```

Result: hardcoded state-length rejection and D2–D4 branches confirmed.

```bash
rg --files /home/lacra -g '*2267*.pdf' -g 'mlkembraid*.pdf' 2>/dev/null; nl -ba SrcTranslated/Funs.lean | sed -n '10635,10678p;12318,12352p'; nl -ba SrcTranslated/Types.lean | sed -n '863,887p'; nl -ba SrcTranslated/Funs.lean | sed -n '8447,8475p'
```

Result: no matching PDFs reported by this search; counterexample serializer/wrapper and encoder types inspected.

```bash
nl -ba .planning/phases/01-gates-provenance-and-target-list/01-07-PLAN.md | sed -n '370,399p'; nl -ba .claude/skills/spqr-plan-review/SKILL.md | sed -n '1,100p'; nl -ba docs/ISSUE_TEMPLATE.md | sed -n '90,127p'
```

Result: explicit domain ruling, review-skill pattern, and existing checklist inspected as data.

```bash
rg -n '^structure encoding.Chunk|^structure encoding.gf.GF16|^def v1.chunked.states.serialize.encode_varint|^def v1.chunked.states.serialize.encode_chunk' SrcTranslated/{Types,Funs}.lean; nl -ba SrcTranslated/Funs.lean | sed -n '12873,12892p;12288,12297p'; nl -ba SrcTranslated/Funs.lean | sed -n '14318,14337p'; nl -ba .planning/phases/01-gates-provenance-and-target-list/01-RESEARCH.md | sed -n '1400,1428p'; rg -n 'allow-sorry|baseline|skips|SKIP|no targets|new axiom' .planning/phases/01-gates-provenance-and-target-list/01-RESEARCH.md | head -25
```

Result: type/declaration locations, error propagation, and research assumptions located.

```bash
python3 - <<'PY'
from pathlib import Path
import re
text = Path('SrcTranslated/FunsExternal.lean').read_text()
names = re.findall(r'^axiom\s+(\S+)', text, re.M)
required = ['libcrux_ml_kem.mlkem768.incremental.validate_pk_bytes', 'libcrux_ml_kem.mlkem768.incremental.encapsulate1', 'libcrux_ml_kem.mlkem768.incremental.encapsulate2', 'libcrux_ml_kem.mlkem768.incremental.decapsulate_compressed_key', 'libcrux_ml_kem.mlkem768.incremental.pk1_len', 'libcrux_ml_kem.mlkem768.incremental.pk2_len', 'libcrux_ml_kem.mlkem768.incremental.encaps_state_len', 'libcrux_ml_kem.mlkem768.incremental.KeyPairCompressedBytes.from_seed_spec', 'libcrux_ml_kem.constants.SHARED_SECRET_SIZE', 'libcrux_ml_kem.ind_cca.incremental.types.Ciphertext1.len', 'libcrux_ml_kem.ind_cca.incremental.types.Ciphertext2.len', 'libcrux_hmac.hmac', 'libcrux_hmac.hmac_sha256_tag32_spec', 'encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.decoded_message', 'incremental_mlkem768.potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275', 'encoding.gf.mul2_u16']
for name in required:
    match = re.search(r'^axiom\s+' + re.escape(name) + r'(?=\s|:)', text, re.M)
    print(name, 'line', text.count('\n', 0, match.start()) + 1 if match else 'MISSING')
print('external stubs:', sum(name in names for name in required), '+ HKDF 1 + builtins 3 = 20')
PY
nl -ba SrcTranslated/Types.lean | sed -n '898,908p'; rg -n '^def v1\.chunked\.states\.States\.(recv|send)|^def v1.unchunked.send_ek.EkSentCt1Received.recv_ct2|^def v1.unchunked.send_ct.NoHeaderReceived.recv_header|^def Error.Insts.CoreConvertFromAuthenticatorError' SrcTranslated/Funs.lean; nl -ba .planning/phases/01-gates-provenance-and-target-list/01-RESEARCH.md | sed -n '1426,1447p'; git status --porcelain -- src SrcTranslated '*.lean'
```

Result: all sixteen external allowlist names found; chunk layout confirmed; protected source status empty.

```bash
nl -ba SrcTranslated/Funs.lean | sed -n '13216,13296p;13577,13607p;10334,10345p'; nl -ba .planning/phases/01-gates-provenance-and-target-list/01-04-PLAN.md | sed -n '320,325p'; nl -ba .planning/phases/01-gates-provenance-and-target-list/01-06-PLAN.md | sed -n '131,169p'; git diff --name-only d47083c -- src; git diff --quiet -- SrcTranslated; printf 'SrcTranslated worktree diff exit: %s\n' "$?"
```

Result: extracted MAC success/error traces confirmed; source diff empty; extraction worktree-diff exit `0`.

```bash
nl -ba SrcTranslated/Funs.lean | sed -n '10773,10793p;12894,12909p'; nl -ba src/v1/chunked/send_ct/serialize.rs | sed -n '9,35p;91,107p'; nl -ba .planning/phases/01-gates-provenance-and-target-list/01-03-PLAN.md | sed -n '240,261p'; nl -ba .planning/phases/01-gates-provenance-and-target-list/01-06-PLAN.md | sed -n '261,274p;321,343p'; git rev-parse --short HEAD; git rev-parse --short origin/main
```

Result: complete counterexample propagation and residual registry/support defects confirmed; final refs remain `d7cf202`/`e8f6689`.

## Resolution map

| Finding | Suggested edit | Destination plan/section |
|---|---|---|
| F-1 | Reopen the validity-domain ruling; qualify or defer the roundtrip and its corollary coherently | 01-07 tasks 1/4; REQUIREMENTS STRUCT-03/04; ROADMAP Phase 7; planned PROP-37 correction |
| F-2 | Respect serializer `Result` type and explicit successful-output projection | 01-07 task 2; STRUCT-02 statement-record instructions |
| F-3 | Remove count-equality/token-count checks; use normalized coverage and stage-correct counts | 01-02 task 3; 01-03 verification/threat model; 01-08 task 1; validation map |
| F-4 | Route support eligibility before target-only rejection | 01-06 task 3 step 1; 01-01 checklist |
| F-5 | Pin and identify the `main` revision used for C1 evidence | 01-06 tasks 1–3; packet/provenance format |
| F-6 | Remove issue dry-run; update waves/tasks; defer full runs until prerequisites exist | 01-VALIDATION sampling and per-task map |
| F-7 | Apply marker/stash preservation rules consistently; forbid stashed controls | 01-01 final verification; 01-04 final verification; 01-VALIDATION negative controls |
| F-8 | Replace obsolete branch-field consumers with explicit head/base fields | 01-05 final verification; 01-09 user action |
| F-9 | Persist catalog review references for all verdicts, independently of target promotion | 01-07 tasks 3/4 and final verification |
---

## 1. Codex's review

**VERDICT: REJECT** — 7 MAJOR, 2 MINOR, no BLOCKER. All nine confirmed. Five of them
(F-3, F-4, F-6, F-7, F-8) are **residuals of my own round-3 patching**: I corrected the
task-level `<verify>` and `<acceptance_criteria>` blocks and left the same assertion standing
in the plan-level `<verification>` sections, the threat-model tables and `01-VALIDATION.md`.
That is a real process lesson — a contradiction fixed in one of four places is not fixed.

| # | Sev | Claim | My verification |
|---|-----|-------|-----------------|
| F-1 | MAJOR | PROP-37's representability domain still admits states that fail the roundtrip | **Confirmed, and it invalidates my own ruling.** `src/v1/unchunked/send_ct/serialize.rs:84` gates `from_pb` on `pb.es.len() == 2080 && pb.ct1.len() == 960 && pb.ek.len() == 1152`, while `into_pb` copies the vectors verbatim (`:75-81`). A `Ct1SentEkReceived` with empty `es`/`ek`/`ct1` serializes fine and fails to deserialize, with no `PolyDecoder` and no prost `sorry` involved. `pts_needed.val ≤ U32.max` is necessary but **not sufficient**, so the correction I recommended would have replaced a false statement with another false statement |
| F-2 | MAJOR | 01-07 tells the executor `Message.serialize` returns a bare vector | **Confirmed.** `SrcTranslated/Funs.lean:11460` declares `Result (alloc.vec.Vec Std.U8)`. `serialize_spec` proves unconditional success in WP style, which is not a change of return type. My instruction would have produced an ill-typed statement record |
| F-3 | MAJOR | Residual count-equality and token-count assertions contradict the fixed registry design | **Confirmed at all six locations** — `01-02:306`, `01-03:251/256/257` (threat table + `<verification>`), `01-08:112`, `01-VALIDATION:106`. Codex's independent enumeration reproduced my figures exactly (42 registry / 38 index / empty symmetric difference). Its extra catch is real: `01-08` said "still reports 42" but runs **after** 01-07 adds two rows, so 44 |
| F-4 | MAJOR | `--support` is unreachable: step 1 rejects `Target? = no` before the mode branch | **Confirmed.** Excluded band → `C3 = fail` → `Target? = no` → the skill stops, and the reduced rubric was only selected later during assembly. My own edit created this |
| F-5 | MAJOR | The C1 evidence channel names no `main` snapshot | **Confirmed, and the example is exact.** `origin/main` (`e8f6689`) carries `Spqr/Specs/Chain/Chain/EpochIdx.lean` with a proved `epoch_idx_spec`; that file is **absent from this working tree**, and the catalog still calls PROP-29 open. A working-tree search would have certified a proved property as novel |
| F-6 | MAJOR | The validation schedule demands full gate runs before their prerequisites exist, and still invokes the dropped issue script | **Confirmed.** `01-VALIDATION:48` required a full baseline-backed run after *every* wave, impossible in waves 1-2 (01-02 writes the runner without running it; 01-04 builds the tree in wave 3); line 54 still had the issue-script dry-run I missed when I cleaned lines 37-38; and the task/wave map was never resynced after the renumbering |
| F-7 | MAJOR | Terminal verification still demands 8 `GSD:` lines and an empty stash list | **Confirmed.** `01-01:203` and `01-04:316` — the same two defects as round-3 F-8 and PS-1, fixed at task level and left in the plan-level sections. `01-VALIDATION:142` also still offered "a stashed change" as a negative-control route, contradicting the worktree-only rule |
| F-8 | MINOR | Two consumers still read the retired `PR B branch:` field | **Confirmed** at `01-05:180` and `01-09:112` |
| F-9 | MINOR | `Review:` is filled only on the ACCEPT path, yet completion forbids an empty placeholder | **Confirmed.** A REJECT produces a real artifact and must still be referenced |

### Planning-seat finding

| # | Sev | Claim |
|---|-----|-------|
| PS-2 | MAJOR | PROP-35's `Domain:` correction is **also** incomplete, the same class of defect as F-1. `Message.deserialize_spec` carries `hlen : from1.length + 32 ≤ Std.Usize.max` (`Deserialize.lean:61`) and `Message.serialize_spec` has no precondition, so the composed roundtrip needs a length/no-overflow hypothesis on `serialize`'s output that 01-07 task 1 does not name |

## 2. What I did in response

- **F-2** — `01-07` task 2: corrected to `Result (alloc.vec.Vec Std.U8)` with the `Funs.lean:11460`
  citation, spelled out that encoder-image membership is `serialize m i = ok bytes`, and added
  that STRUCT-02a's second witness pair is non-injectivity of the **successful
  `(message, index)` projection** — the cursors differ (`4` vs `5`), so an unqualified claim
  about the whole decoder result would be false.
- **F-3** — replaced every residual count assertion with ID-set agreement: `01-02` acceptance
  criteria, `01-03`'s threat row T-1-08 and `<verification>` items 1-2, `01-VALIDATION`'s
  requirement table, and `01-08`'s post-01-07 figure corrected 42 → 44.
- **F-4** — `01-06` step 1 now branches on `--support` **before** any target-only rule, with
  support eligibility defined as "exists, marked `support`, names at least one target"; an
  orphan stops for the user. `01-01`'s checklist gained the matching support route so a support
  lemma is not required to hold a target ACCEPT.
- **F-5** — the C1 baseline is now an explicitly resolved `git rev-parse origin/main`, searched
  with `git grep <pattern> $BASE -- Spqr/Specs`, with the SHA and patterns recorded in both the
  packet and the artifact header; working-tree evidence must be labelled separately. The same
  baseline is recorded at the top of `docs/proof-targets.md` and governs its C1 column. The
  `epoch_idx_spec` example is written into the plan as the reason.
- **F-6** — `01-VALIDATION` sampling is now staged: static-only plus a `--gates 5` run in waves
  1-2, with the expected-red gate-5 run named as a *required observation* rather than a failure;
  full runs from wave 3 and at PR boundaries. The issue-script path is gone from line 54 as
  well, and the task/wave map is resynced (01-03→2, 01-04→3, 01-06→5, 01-07 reviews→task 3 wave 6,
  01-08→7).
- **F-7** — the named-marker-pair check and the `STASH_BASELINE` comparison now also appear in
  `01-01`'s and `01-04`'s `<verification>` sections, and `01-VALIDATION`'s negative-control
  preamble is worktree-only with an explicit prohibition on touching the five pre-existing
  stashes.
- **F-8** — `01-05`'s verification checks all three fields and that no `PR B branch:` remains;
  `01-09` opens from `PR B head:` targeting `PR B base:`.
- **F-9** — `Review:` is filled with the artifact path on **every** validated verdict including
  REJECT and HUMAN_RULING; only promotion to `Target? = yes` is ACCEPT-only, and a
  reviewed-and-deferred row's end state is written out.

## 3. What I deliberately did NOT do

- **F-1 — escalated, and it reverses part of my own recommendation.** I recommended the
  representability hypothesis alone and explicitly ruled the variant-specific invariant out as
  Phase 4/5 work. The counterexample shows that was wrong: the byte-length checks in the
  unchunked deserializers are not polish, they are load-bearing for the statement's truth. I
  will not pick the replacement domain unilaterally, because the honest options differ in scope
  by a lot. `01-07` task 1's PROP-37 instruction is marked **blocked** pending the ruling so no
  executor acts on the insufficient version.
- **PS-2 — partially applied, and the residue escalated with F-1.** I added the length
  hypothesis to `01-07`'s PROP-35 instruction and, more importantly, changed the instruction to
  **derive** the domain from `deserialize_spec`'s hypotheses and success conjuncts rather than
  from a hand-written list — the list is what was incomplete twice. Whether PROP-35's corrected
  domain is now complete is a claim I would rather have the next review attack than assert.
- **The STRUCT-04 retirement** stands: Codex agrees the argument is sound given a successful
  left-inverse law on an adequate domain, and notes the composition must be monadic because
  `into_pb` returns `Result`. That is a wording tightening, applied to `REQUIREMENTS.md`, not a
  reversal. The retirement's correctness now depends on F-1's domain being settled, since the
  corollary inherits whatever domain PROP-37 ends up with.
