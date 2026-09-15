<!--
Provenance
  reviewer:   Codex CLI (OpenRouter), GPT-class model, cross-engine
  effort:     model_reasoning_effort = high
  sandbox:    read-only (bwrap, kernel-enforced)
  rubric:     docs/rubrics/spqr-plan-review.md
  prompt:     /tmp/phase01-review-assignment.md
  log:        /tmp/phase01-codex-review-2-log.txt
  date:       2026-09-14
  round:      2 (round 1 = 01-CODEX-REVIEW.md, verdict REJECT)
  note:       Codex review below is verbatim and never edited. Planning-seat
              triage is appended after the --- separator.
-->

# SPQR Plan Review

- Phase: 01 — Gates, Issues and Deviation Decisions
- Plans reviewed: 01-01 through 01-09, as one set, under `.planning/phases/01-gates-issues-and-deviation-decisions/`
- Date: 2026-09-14
- Branch/base verified: `la/spec-catalog`, HEAD `d7cf202a02c69ddc7d33f4c870293199b3f36cd6`; pinned source commit `d47083cd3abf2906229efa38ae2bfb1121498af0`. Working-tree revisions were reviewed. `src/` and `SrcTranslated/` have no diff against the pin.
- VERDICT: APPROVE-WITH-EDITS

## Findings

Phase-document references below are relative to `.planning/phases/01-gates-issues-and-deviation-decisions/`. The edits below are required before dispatch. No remaining theorem-statement or trusted-base BLOCKER was established; the remaining changes can be bounded without replacing the nine-plan decomposition.

### F-1 — MAJOR

**Claim:** The revised plans still permit PR B work to accumulate on PR A’s head without an enforced branch boundary.

**Evidence:** This remains open from round-1 F-4.

- `.planning/config.json:10` sets `branching_strategy` to `none`.
- `01-07-PLAN.md:305` explicitly acknowledges that execution has been committing directly to `la/spec-catalog`.
- The added branch questions at `01-07-PLAN.md:303` are useful, but the operative resume signal at `01-07-PLAN.md:335` still permits an unqualified `"skip"` to continue.
- `01-08-PLAN.md:6` depends only on completion of 01-07. Its first edit, at `01-08-PLAN.md:135`, has no precondition asserting the user-selected PR B branch or separating it from PR A’s head.
- PR A’s range check was repaired at `01-07-PLAN.md:280`; PR B’s corresponding instruction still uses bare `git diff --stat` at `01-09-PLAN.md:300`. After task commits, that does not report the PR’s committed changes.

The following execution remains permitted:

| Step | Branch | Consequence |
|---|---|---|
| Execute 01-01 through 01-07 | `la/spec-catalog` | PR A commits accumulate there |
| Answer `"skip"` | Unchanged | No branch transition is required |
| Execute 01-08 | Same branch | PR B catalog edits extend PR A’s head |
| Run PR B’s bare diff command after commits | Same branch | Committed PR B changes are absent from the reported diff |

The branch facts also still contradict the old quotation retained at `01-07-PLAN.md:321`:

```text
git rev-list --left-right --count origin/la/spec-catalog...HEAD
0	9
```

The branch is ahead, not diverged. The new instruction to re-measure does not justify presenting the contradictory old statement as the question’s factual premise.

**Minimal suggested edit:** Require user-selected head/base branches before PR A execution and a verified transition before 01-08. Skipping PR creation must not waive branch selection. Distinguish the recorded implementation tip from the subsequent tracked SUMMARY commit. Use complete base-to-head ranges for both PR reports, including `.planning/` and committed frozen-path checks; remove the stale divergence premise.

### F-2 — MAJOR

**Claim:** Plan 01-04’s revised duplicate-detection instructions and acceptance predicates are mutually unsatisfiable.

**Evidence:** The new full-enumeration algorithm at `01-04-PLAN.md:230` replaces search-based detection, but the earlier binding guidance at `01-04-PLAN.md:83` still prescribes `--search` and an exact `--jq` match. The old search-based mitigation also remains at `01-04-PLAN.md:406`.

More decisively, the same acceptance command has opposite required outcomes:

| Location | Command | Required result |
|---|---|---|
| `01-04-PLAN.md:285` | `grep -q 'in:title' scripts/create-property-issues.sh` | Exit 1 |
| `01-04-PLAN.md:289` | `grep -q 'in:title' scripts/create-property-issues.sh` | Exit 0 |

The revised action permits a real `jq --arg` at `01-04-PLAN.md:243`, while `01-04-PLAN.md:286` rejects the substring `jq --arg`, inadvertently rejecting that valid implementation option too.

The read probe was:

```bash
sed -n '284,290p' .planning/phases/01-gates-issues-and-deviation-decisions/01-04-PLAN.md
```

Its output contains both opposite `in:title` assertions. No implementation can satisfy both. This leaves round-1 F-6 only partially resolved and risks restoring the search algorithm that round-1 F-2 identified.

**Minimal suggested edit:** Make full enumeration the sole authoritative algorithm throughout the plan and its binding examples. Delete the old positive `in:title` assertion and search-based mitigation. Restrict the invalid-interface check to `gh`’s unsupported argument shape rather than rejecting valid standalone `jq --arg`.

### F-3 — MAJOR

**Claim:** Full enumeration fixes the search-index problem but still does not enforce the required one-issue-per-ID identity.

**Evidence:** `01-04-PLAN.md:242` fetches only `number,title`; `01-04-PLAN.md:249` explicitly acknowledges that an edited title defeats detection. Nevertheless, the requirement being written at `01-02-PLAN.md:125` and the process constraint at `CLAUDE.md:22` remain one issue per property, not one issue per unchanged title.

The existing template already provides an identity-bearing body field at `docs/ISSUE_TEMPLATE.md:8`: `## Property: {PROP-ID}`.

A hand-executed counterexample to the prescribed algorithm is:

| Step | GitHub state / observation | Prescribed result |
|---|---|---|
| Earlier successful filing | Issue `N` has body identifying `INFRA-01` | One issue for the ID |
| Title edited later | Body still identifies `INFRA-01`; title differs from TSV | Identity has not changed |
| Enumeration | Returns `N` and its edited title | No exact TSV-title match |
| Filing | Creates issue `N+1` for `INFRA-01` | Two issues for one ID |
| Immediate repeat | Finds `N+1` by its unchanged title | Prints `SKIP`; repeat test passes |

The batch count checks at `01-07-PLAN.md:187` and `01-09-PLAN.md:228` do not catch this: the first batch can increase the count by exactly five/four, and its repeat can create nothing, while an older same-ID issue remains.

This is the remaining identity portion of round-1 F-2, not a renewed claim that non-search enumeration has the same demonstrated indexing defect.

**Minimal suggested edit:** Match a stable ID marker, such as the existing exact property heading in the body, using complete enumeration. Fail closed on multiple matching issues or an incompatible closed match. Retain the full-enumeration and lookup-failure protections; do not silently narrow the requirement to unchanged titles.

### F-4 — MAJOR

**Claim:** The revised allowlist source-validation procedure still rejects one of its mandatory legitimate entries.

**Evidence:** `01-03-PLAN.md:388` repairs comment stripping and namespace handling, but its prescribed declaration match at `01-03-PLAN.md:395` still requires the declaration keyword and name on the same line.

The actual selected stub is split across lines:

```text
SrcTranslated/FunsExternal.lean:3687  axiom
SrcTranslated/FunsExternal.lean:3688    incremental_mlkem768.potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275
```

The concrete check returned:

```bash
grep -qE '^axiom +incremental_mlkem768\.potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275\b' SrcTranslated/FunsExternal.lean
printf 'check_exit=%s\n' "$?"
```

```text
check_exit=1
```

This is not an incorrect allowlist name. It is a valid required declaration that the mandatory validation cannot recognize. The same source-layout issue explains why a scan requiring a space after `axiom` sees only 54 axioms, while a declaration-keyword scan correctly counts 173.

Round-1 F-10’s original comment/FQN, scratch-cleanup and escaped-awk defects were repaired, but this replacement predicate remains broken.

**Minimal suggested edit:** Recognize declaration names across intervening whitespace/newlines while retaining namespace-aware, comment-stripping validation. Validate the multiline libcrux-fix stub explicitly. Do not delete or rename the entry to satisfy the broken predicate.

### F-5 — MAJOR

**Claim:** A newly required README edit is absent from 01-04’s file map and overlaps 01-06 in the actual execution wave.

**Evidence:**

- `01-04-PLAN.md:208` now requires documentation in `scripts/README.md`.
- Neither its frontmatter at `01-04-PLAN.md:7` nor task file lists at `01-04-PLAN.md:118` and `01-04-PLAN.md:303` declare that write.
- `01-06-PLAN.md:10` owns the same README; `01-06-PLAN.md:260` edits its measurements and gate-output documentation.

The installed scheduler was checked rather than inferred from the plan prose. Its actual wave index is:

```text
1: 01-01, 01-02, 01-03
2: 01-04, 01-06
3: 01-05
4: 01-07
5: 01-08
6: 01-09
```

The scheduler’s overlap protection uses `files_modified`, at `/home/lacra/.claude/get-shit-done/workflows/execute-phase.md:438`. It cannot see 01-04’s omitted README write. Thus the two executions can concurrently edit the same tracked deliverable without triggering that protection.

The dependency repair for retirement **does work**: `/home/lacra/.claude/get-shit-done/bin/lib/phase.cjs:524` uses computed topological waves. It puts 01-05 after 01-04 despite their declared wave numbers. The original deletion-before-consumption finding is therefore not repeated here.

However, four declared wave numbers and the ROADMAP/validation listing remain stale. The scheduler reports:

```text
Plan 01-05: declared wave: 2 but depends_on DAG places it in wave 3
Plan 01-07: declared wave: 3 but depends_on DAG places it in wave 4
Plan 01-08: declared wave: 4 but depends_on DAG places it in wave 5
Plan 01-09: declared wave: 5 but depends_on DAG places it in wave 6
```

**Minimal suggested edit:** Assign the new README note to one owner, or declare the shared write and serialize the plans. Synchronize frontmatter, ROADMAP and validation waves with the resulting DAG. Do not remove 01-05’s dependency on 01-04.

### F-6 — MAJOR

**Claim:** The revised validation still permits the required wrapped-axiom negative control to remain unexecuted while recording completion.

**Evidence:** The parser specification itself is materially improved: `01-03-PLAN.md:354` requires complete bracket-delimited reports, including continuation lines.

But:

- `01-06-PLAN.md:336` permits reporting A1 as partially verified if no wrapped report is produced.
- `01-06-PLAN.md:358` explicitly accepts that report as an alternative to observing the required failure.
- `01-06-PLAN.md:366` then permits the validation completion flags to be declared ready.
- `01-VALIDATION.md:142` instead says all seven controls are mandatory.
- `01-06-PLAN.md:411` likewise requires the wrapped-list control to establish that the matcher is not line-oriented.

The output shape is a real source-established case, not speculative proof difficulty:

```text
.../Lean/Elab/Print.lean:244
  logInfo m!"'{constName}' depends on axioms: {axioms.qsort Name.lt |>.map MessageData.ofConstName |>.toList}"

.../Lean/Message.lean:417
  | xs => sbracket <| joinSep xs (ofFormat "," ++ Format.line)
```

An honest “not verified” report is appropriate, but it cannot simultaneously satisfy this mandatory control. This is the remaining validation portion of round-1 F-8.

**Minimal suggested edit:** Make inability to exercise the wrapped case a stop/incomplete condition. Specify a deterministic way to obtain a wrapped report or test the parser with a faithful wrapped fixture, and require rejection naming the unexpected continuation-line axiom before completion is recorded.

### F-7 — MINOR

**Claim:** The Signal-note task requires two candidate resolutions for D5 but supplies only one.

**Evidence:** `01-09-PLAN.md:125` requires the five-part structure for every deviation. Its fifth part at `01-09-PLAN.md:132` explicitly requires two candidate resolutions, but the D5 instruction at `01-09-PLAN.md:135` supplies only writing down the caller contract.

This accurately reflects the limitation of its cited source: `docs/spqr-properties.md:444` also names only the written caller contract, not a pair. The two-candidate obligation nevertheless remains in `01-CONTEXT.md:87`, `01-09-PLAN.md:175` and `01-09-PLAN.md:380`.

ML-KEM Braid Rev. 1 §2.4 provides the relevant contrast: participants should discontinue the session after verification failure, whereas the proposed contract leaves that decision to the caller.

**Minimal suggested edit:** Explicitly formulate the alternative D5 question—confirmation of caller-managed session termination versus requiring enforcement of the spec’s termination behavior—or obtain an explicit exception to the two-candidate format. Do not imply that the existing catalog paragraph already provides two choices.

## Cleared surfaces

### 1. Catalog fidelity

The corrected D5 public-error statement survives independent source inspection. `src/authenticator.rs:13` and `src/authenticator.rs:15` define the internal causes; `src/lib.rs:145` converts both to public `Error::MacVerifyFailed`. The extraction independently agrees at `SrcTranslated/Types.lean:719`, `SrcTranslated/Types.lean:795` and `SrcTranslated/Funs.lean:10339`. Round-1 F-1 is resolved.

The D1 code statement also matches the existing theorem:

- `src/authenticator.rs:44` concatenates the prior root key with the update key.
- `src/authenticator.rs:51` uses a 32-byte zero salt.
- `Spqr/Specs/Authenticator/Authenticator/Update.lean:48` states the corresponding HKDF value, under the explicit memory-size hypothesis at line 49.

D2–D4 agree with the inspected dispatch and message paths at `src/v1/chunked/states.rs:282`, `src/v1/chunked/states.rs:182`, `src/v1/chunked/states.rs:464`, `src/v1/chunked/states.rs:489` and `src/v1/chunked/states.rs:513`.

Existing local copies of both specification PDFs were read directly, with `pdftotext` writing only to stdout. The Braid document identifies itself as Revision 1, last updated September 26, 2025. Its §2.2, §2.4 and §2.5 support the stated spec/code contrasts; §2.6 supplies the shared-secret initialization and progress context. SCKA Def. 3.1 and Figs. 1–2 were checked for the optional epoch/key interface and compiler layering. No new cryptographic-security conclusion is inferred from these functional checks.

### 2. Internal consistency

The retirement dependency is effective under the installed topological scheduler. There is no longer a supported basis for claiming that 01-05 can legally delete the legacy input before 01-04 consumes it under that scheduler. F-5 identifies the separate new README conflict and stale wave metadata.

No new committed Lean module is proposed, so no new `Spqr.lean` re-export is required. The already cited modules are imported at `Spqr.lean:52`, `Spqr.lean:71`, `Spqr.lean:146`, `Spqr.lean:196` and `Spqr.lean:200`.

The intended sequential edits by 01-03/01-06 and 01-03/01-05 are otherwise coherent. F-1 covers the unresolved PR-range and branch ownership contract.

### 3. Statement-level soundness

The relevant extraction returns a nested result:

```text
SrcTranslated/Funs.lean:13219
Result (core.result.Result (v1.unchunked.send_ct.NoHeaderReceived × EpochSecret) Error)
```

Thus an ordinary protocol MAC error is not an outer Aeneas execution failure. No claim of vacuous WP success was used in this review.

The revised caller contract is sound when scoped to the caller’s serialized input: `src/lib.rs:356` takes an immutable reference, and the successful updated serialization is constructed at `src/lib.rs:438`. Internal local computation and authenticator updates must remain distinguished from mutation of that caller-owned state.

The nonoverflow qualification already recorded at `docs/spqr-properties.md:422` remains relevant. No full liveness theorem, axiom closure or elaboration result was certified from source reading alone.

### 4. Semantic closure

The following failure trace is conditioned on successful decoding, decapsulation and KDF computation, with valid buffer shapes:

| Step | Local state at epoch 7 | Caller’s serialized state | Result |
|---|---|---|---|
| Decode input | Local copy contains authenticator `A` | Original bytes `S` | Continue |
| Derive epoch secret | Secret derived | Still `S` | Continue |
| Update authenticator | Local authenticator becomes `A′` | Still `S`, encoding `A` | Continue |
| Verify ciphertext MAC | Check rejects | Still `S` | Internal `InvalidCtMac` |
| Propagate error | Updated local state is not returned | Still `S` | Public `MacVerifyFailed`; no returned state/key |

The ordering is explicit at `src/v1/unchunked/send_ek.rs:150`, `src/v1/unchunked/send_ek.rs:158`, `src/v1/unchunked/send_ek.rs:160` and `SrcTranslated/Funs.lean:13241`. Header verification instead precedes construction of `HeaderReceived`, at `src/v1/unchunked/send_ct.rs:107` and `SrcTranslated/Funs.lean:13585`. Dropping local values is not evidence of secure zeroization.

The successful terminal transition also preserves the necessary D2 exception:

| Step | A | B | Key/message consequence |
|---|---|---|---|
| Assumed completing pair | `EkSentCt1Received(7)` | `Ct2Sampled(7)` | Valid completing Ct2 is available |
| A receives Ct2 | `NoHeaderReceived(8)` | `Ct2Sampled(7)` | A returns an epoch-7 secret |
| A sends | Unchanged | Unchanged | Sends epoch 8, payload `None`, no new key |
| B receives that message | `NoHeaderReceived(8)` | `KeysUnsampled(8)` | Exceptional Greater arm succeeds; no key |

Sources: `SrcTranslated/Funs.lean:13251`, `SrcTranslated/Funs.lean:11289` and `SrcTranslated/Funs.lean:13971`. Separately, `HeaderReceived.send` emits its key while remaining at the current epoch and entering `Ct1Sampled`, at `SrcTranslated/Funs.lean:11297`. These traces do not establish equality of the parties’ secrets or universal liveness.

### 5. Precedent and interface realism

`update_spec` exists with its cited behavior and `@[step]` tag at `Spqr/Specs/Authenticator/Authenticator/Update.lean:47`. The handwritten HKDF axiom is correctly named `spqr.kdf.hkdf_to_slice_spec`, inside the namespace at `Spqr/Specs/Kdf/HkdfToSlice.lean:18`, with its `@[step]` tag at line 24.

The two handwritten sorry sites remain at `Spqr/Specs/Aeneas/MapCollectBridge.lean:70` and `Spqr/Specs/Lib/DecodeState.lean:54`.

The #272 diagnosis is historical: `Spqr/Specs/Encoding/Polynomial/LagrangePolysForCompletePoints.lean:47` has a preservation/frame statement, not the old unconditional `y = GF16.ONE` conclusion. The revised instruction to treat the legacy README as history is justified.

### 6. Trusted-base discipline

The explicit source inventory is:

| Surface | Inventory |
|---|---|
| `SrcTranslated/FunsExternal.lean` | 173 `axiom` declarations; one `opaque` |
| `SrcTranslated/TypesExternal.lean` | Three type axioms |
| `SrcTranslated/Funs.lean` | 57 explicit `sorry` occurrences |
| Handwritten `Spqr/` | One explicit axiom, one opaque, two proof `sorry` sites |
| Existing `sorry-manifest.txt` | 134 lines, including 36 `Spqr.Specs.*` lines; not a fresh audit |

The 20-name figure is correct for the **selected policy allowlist**, not for the entire extraction inventory. Independently expanding the selected names gives:

| Accepted name | Declaration source |
|---|---|
| `propext` | Builtin; recognized by `scripts/Audit.lean:27` |
| `Classical.choice` | Builtin; recognized by `scripts/Audit.lean:27` |
| `Quot.sound` | Builtin; recognized by `scripts/Audit.lean:27` |
| `spqr.kdf.hkdf_to_slice_spec` | `Spqr/Specs/Kdf/HkdfToSlice.lean:25` |
| `libcrux_ml_kem.mlkem768.incremental.validate_pk_bytes` | `SrcTranslated/FunsExternal.lean:1985` |
| `libcrux_ml_kem.mlkem768.incremental.encapsulate1` | `SrcTranslated/FunsExternal.lean:1994` |
| `libcrux_ml_kem.mlkem768.incremental.encapsulate2` | `SrcTranslated/FunsExternal.lean:1856` |
| `libcrux_ml_kem.mlkem768.incremental.decapsulate_compressed_key` | `SrcTranslated/FunsExternal.lean:2006` |
| `libcrux_ml_kem.mlkem768.incremental.pk1_len` | `SrcTranslated/FunsExternal.lean:1838` |
| `libcrux_ml_kem.mlkem768.incremental.pk2_len` | `SrcTranslated/FunsExternal.lean:1844` |
| `libcrux_ml_kem.mlkem768.incremental.encaps_state_len` | `SrcTranslated/FunsExternal.lean:1850` |
| `libcrux_ml_kem.mlkem768.incremental.KeyPairCompressedBytes.from_seed_spec` | `SrcTranslated/FunsExternal.lean:1873` |
| `libcrux_ml_kem.constants.SHARED_SECRET_SIZE` | `SrcTranslated/FunsExternal.lean:1806` |
| `libcrux_ml_kem.ind_cca.incremental.types.Ciphertext1.len` | `SrcTranslated/FunsExternal.lean:1823` |
| `libcrux_ml_kem.ind_cca.incremental.types.Ciphertext2.len` | `SrcTranslated/FunsExternal.lean:1831` |
| `libcrux_hmac.hmac` | `SrcTranslated/FunsExternal.lean:1748` |
| `libcrux_hmac.hmac_sha256_tag32_spec` | `SrcTranslated/FunsExternal.lean:1795` |
| `encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.decoded_message` | `SrcTranslated/FunsExternal.lean:3682` |
| `incremental_mlkem768.potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275` | `SrcTranslated/FunsExternal.lean:3687` |
| `encoding.gf.mul2_u16` | `SrcTranslated/FunsExternal.lean:3676` |

The research table supplies enough information to reconstruct this selection, but F-4 means the executor is **not yet given a reliable mechanical validation procedure**.

`crypto.HMAC_SHA256` is the correct opaque name, at `Spqr/Crypto/Hkdf.lean:30`; the other opaque is `spqr.kdf.hkdf_to_slice`, at `SrcTranslated/FunsExternal.lean:3669`. The pinned collector distinguishes `axiomInfo` from `opaqueInfo` at `/home/lacra/.elan/toolchains/leanprover--lean4---v4.31.0/src/lean/Lean/Util/CollectAxioms.lean:57`: it traverses an opaque’s dependencies rather than automatically inserting its own name as an axiom.

The excluded bare `initial_state`, `send` and `recv` stubs remain correctly excluded. No permanent new axiom, sorry or native-decision trust was authorized by the reviewed tasks.

### 7. Gates

The gate-1 and gate-2 command/grep claim survives inspection:

```bash
lake build --no-ansi 2>&1 | tee /tmp/lake-build.log
lake exe runLinter Spqr 2>&1 | tee /tmp/lake-lint.log || true
```

These match `.github/workflows/lean.yml:47` and `.github/workflows/lean.yml:57`. The warning filter and `error:` filter match too. CI has no working-directory override for these steps; its `LEAN_ABORT_ON_PANIC: 1` at `.github/workflows/lean.yml:23` is explicitly added locally by `01-03-PLAN.md:165`.

The revised plan now handles build/audit subprocess failures, requires a fresh head manifest, and distinguishes partial runs from a full pass. Those are substantive repairs to round-1 F-7.

The local/CI comparison is also substantially repaired: `01-06-PLAN.md:219` specifies script-versus-CWD provenance, line 235 requires matching source SHAs, and line 245 distinguishes the stricter local delta policy. CI restores the actual PR-base manifest at `.github/workflows/lean.yml:68`; its delta reporter does not set `SORRY_FAIL_ON_NEW=true`, at `.github/workflows/sorry-delta-comment.yml:43`. Gate 4 has no CI counterpart.

The wrapped-report grammar is now specified correctly, subject to F-6’s completion defect. No `lake build`, elaboration probe, gate execution or live GitHub mutation was run during this review.

### 8. Boundedness and safety

The source/extraction freeze is explicit throughout the plan set, and the current source trees match the pin. Negative controls are confined to disposable worktrees by `01-06-PLAN.md:302`; they are not authorization to alter the committed trusted base.

The legacy directory is indeed ignored and untracked. The user checkpoint precedes its irreversible deletion, and the effective dependency now preserves its lifetime through 01-04.

The new PR B authorization checkpoint at `01-09-PLAN.md:178` precedes live DEV filing. The labels-only exception is explicitly defined at `01-04-PLAN.md:175`. The new `--show-body` interface and complete placeholder guard materially resolve round-1 F-11. Agent pushes and PR creation remain prohibited.

### 9. Roadmap and catalog coherence

The criterion-1 repair is legitimate and explicit: it scopes the check to tracked operative documents while retaining the planning history, as recorded in research Q-1. It should not be described as mathematically stronger than an unscoped grep; it is an authorized scope correction.

The criterion-3/INFRA-02 repair is also supported by the recorded human choice: `01-DISCUSSION-LOG.md:156` explicitly selects just-in-time filing with INFRA-02 reworded. It is not an undisclosed removal of the original bulk-filing obligation. F-3 concerns the separate identity guarantee that remains in the repaired requirement.

Provisional decisions are expressly authorized by D-10 at `01-CONTEXT.md:81`; they are not Signal rulings. The two-table layout is recorded as a user decision at `01-RESEARCH.md:1479`. Preserving proof statuses and updating the D1–D5 index entry are appropriate for this decision-only phase.

The remaining branch guards, identity checks, file ownership and mandatory-validation repairs are bounded edits. They must be applied before the plan set is dispatched unchanged.

### Round-1 disposition

| Prior finding | Independent round-2 result |
|---|---|
| F-1 — public MAC error | Resolved: Rust and extraction agree with revised public `MacVerifyFailed` wording |
| F-2 — duplicate filing | Search-index defect addressed; obsolete instructions and stable-ID gap remain as F-2/F-3 |
| F-3 — PR B authorization | Resolved by the new blocking checkpoint before DEV writes |
| F-4 — PR separation/ranges | Partially repaired; still open as F-1 |
| F-5 — legacy-input deletion race | Resolved by the dependency under the actual topological scheduler; wave metadata remains stale |
| F-6 — invalid `gh` interface | Argument-shape and labels-only repairs are substantive; contradictory acceptance predicates remain as F-2 |
| F-7 — incomplete/full gate evidence | Resolved at specification level; execution evidence remains unavailable in this read-only review |
| F-8 — multiline axiom parser | Parser specification repaired; mandatory test can still be waived, F-6 |
| F-9 — baseline deployment/CI comparison | Resolved at specification level by explicit directory provenance, SHA matching and semantic separation |
| F-10 — impossible predicates | Original examples repaired; multiline declaration validation remains broken, F-4 |
| F-11 — inaccessible bodies/placeholders | Resolved by `--show-body`, truthful non-property values and the widened placeholder guard |

The prior MINOR inventory/name correction was also independently checked: 173 extraction axioms and `crypto.HMAC_SHA256` are the correct facts.

## Probe log

All commands were read-only. Repeated identical commands are listed once; numbered-source reads produced source excerpts, not build or test evidence. Some large batched outputs were truncated, and critical sections were subsequently read in smaller ranges.

### Repository, history and instruction probes

Result: correct branch and pin; reviewed working-tree plan revisions; source/extraction unchanged; `.planning/` tracked; prior review artifact currently untracked; legacy `issues/` ignored and untracked. No applicable `AGENTS.md` was found by these searches.

```bash
pwd
git status --short
git branch --show-current
git rev-parse HEAD
git rev-parse d47083c
git diff --name-only
git diff d47083c -- src/
rg --files -g AGENTS.md -g '*Braid*' -g '*2267*' -g '*manifest*' -g '*pdf' -g '*SKILL.md' . .planning
wc -l .planning/phases/01-gates-issues-and-deviation-decisions/*.md
for dir in / /home /home/lacra /home/lacra/git_repos /home/lacra/git_repos/baif /home/lacra/git_repos/baif/SparsePostQuantumRatchet-verify; do if test -f "$dir/AGENTS.md"; then printf '\n--- %s/AGENTS.md ---\n' "$dir"; cat "$dir/AGENTS.md"; fi; done
find .planning docs scripts .github src SrcTranslated Spqr issues -name AGENTS.md -print
git diff --stat
git diff --numstat
git diff --name-only origin/main..HEAD -- '*.lean' lakefile.toml lean-toolchain lake-manifest.json
git diff --stat d47083c -- src/ SrcTranslated/
git rev-list --left-right --count origin/la/spec-catalog...HEAD
git diff --stat origin/main..HEAD | tail -n 1
git ls-files .planning | wc -l
git ls-files issues/
git check-ignore -v issues/create_issues.sh
git ls-files .planning/phases/01-gates-issues-and-deviation-decisions/01-CODEX-REVIEW.md
git status --short -- src SrcTranslated Spqr scripts docs/ISSUE_TEMPLATE.md docs/spqr-properties.md .github
git status --porcelain -- src SrcTranslated Spqr scripts .github
git diff --numstat -- .planning/phases/01-gates-issues-and-deviation-decisions
```

### Contract, prior-review and revision reads

Result: recovered the prior critical findings, accepted issue-timing/provisional-decision records, unchanged phase criteria, and the revised actions rather than relying on triage assertions.

```bash
nl -ba CLAUDE.md
nl -ba .planning/ROADMAP.md
nl -ba .planning/PROJECT.md
nl -ba .planning/REQUIREMENTS.md
nl -ba .planning/STATE.md
nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-CODEX-REVIEW.md | sed -n '1,490p'
nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-CODEX-REVIEW.md | sed -n '68,325p'
nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-CODEX-REVIEW.md | sed -n '120,271p'
nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-CODEX-REVIEW.md | sed -n '622,762p'
nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-CODEX-REVIEW.md | sed -n '180,285p'
nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-CODEX-REVIEW.md | sed -n '217,270p'
nl -ba .planning/ROADMAP.md | sed -n '1,105p'
nl -ba .planning/ROADMAP.md | sed -n '1,83p'
nl -ba .planning/ROADMAP.md | sed -n '1,92p'
nl -ba .planning/ROADMAP.md | sed -n '20,80p'
nl -ba .planning/PROJECT.md | sed -n '1,115p'
nl -ba .planning/PROJECT.md | sed -n '54,72p'
nl -ba .planning/REQUIREMENTS.md | sed -n '1,120p'
nl -ba .planning/REQUIREMENTS.md | sed -n '1,30p'
nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-CONTEXT.md | sed -n '1,165p'
nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-CONTEXT.md | sed -n '1,100p'
nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-CONTEXT.md | sed -n '20,104p'
nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-DISCUSSION-LOG.md
git diff -- .planning/phases/01-gates-issues-and-deviation-decisions/01-RESEARCH.md
git diff -- .planning/phases/01-gates-issues-and-deviation-decisions/01-03-PLAN.md | sed -n '1,118p'
git diff -- .planning/phases/01-gates-issues-and-deviation-decisions/01-04-PLAN.md | sed -n '1,107p'
git diff -- .planning/phases/01-gates-issues-and-deviation-decisions/01-05-PLAN.md .planning/phases/01-gates-issues-and-deviation-decisions/01-07-PLAN.md .planning/phases/01-gates-issues-and-deviation-decisions/01-08-PLAN.md .planning/phases/01-gates-issues-and-deviation-decisions/01-09-PLAN.md | head -n 95
```

### Plan-set reads

Result: inspected frontmatter, dependencies, task actions, acceptance predicates, scope restrictions and boundary reports across all nine plans.

```bash
nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-01-PLAN.md | sed -n '1,140p'
nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-01-PLAN.md | sed -n '95,205p'
nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-01-PLAN.md | sed -n '206,264p'
nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-02-PLAN.md | sed -n '1,105p'
nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-02-PLAN.md | sed -n '104,190p'
nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-02-PLAN.md | sed -n '188,247p'
nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-02-PLAN.md | sed -n '117,130p'
nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-03-PLAN.md | sed -n '1,112p'
nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-03-PLAN.md | sed -n '113,228p'
nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-03-PLAN.md | sed -n '227,350p'
nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-03-PLAN.md | sed -n '350,447p'
nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-03-PLAN.md | sed -n '447,535p'
nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-04-PLAN.md | sed -n '1,55p'
nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-04-PLAN.md | sed -n '55,169p'
nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-04-PLAN.md | sed -n '170,274p'
nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-04-PLAN.md | sed -n '275,374p'
nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-04-PLAN.md | sed -n '375,434p'
nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-05-PLAN.md | sed -n '1,82p'
nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-05-PLAN.md | sed -n '81,196p'
nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-05-PLAN.md | sed -n '194,270p'
nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-06-PLAN.md | sed -n '1,78p'
nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-06-PLAN.md | sed -n '79,182p'
nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-06-PLAN.md | sed -n '182,280p'
nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-06-PLAN.md | sed -n '280,379p'
nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-06-PLAN.md | sed -n '379,424p'
nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-07-PLAN.md | sed -n '1,109p'
nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-07-PLAN.md | sed -n '110,219p'
nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-07-PLAN.md | sed -n '219,323p'
nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-07-PLAN.md | sed -n '319,411p'
nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-08-PLAN.md | sed -n '1,63p'
nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-08-PLAN.md | sed -n '63,174p'
nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-08-PLAN.md | sed -n '174,279p'
nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-08-PLAN.md | sed -n '279,379p'
nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-08-PLAN.md | sed -n '379,412p'
nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-09-PLAN.md | sed -n '1,102p'
nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-09-PLAN.md | sed -n '102,211p'
nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-09-PLAN.md | sed -n '211,312p'
nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-09-PLAN.md | sed -n '312,398p'
nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-VALIDATION.md | sed -n '1,60p'
nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-VALIDATION.md | sed -n '61,167p'
nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-VALIDATION.md | sed -n '104,167p'
nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-RESEARCH.md | sed -n '517,560p'
nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-RESEARCH.md | sed -n '560,598p'
nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-RESEARCH.md | sed -n '1416,1493p'
rg -n 'KDF_AUTH|Native|native_decide|STATE_INVARIANT|A1|A2|A4' .planning/phases/01-gates-issues-and-deviation-decisions/01-RESEARCH.md | tail -n 18
rg -n 'immutable_statements|pinned_statements|STATE_INVARIANT_PROOFS' .planning/phases/01-gates-issues-and-deviation-decisions/*-PLAN.md .planning/phases/01-gates-issues-and-deviation-decisions/01-RESEARCH.md
rg -n '^(plan:|wave:|depends_on:|files_modified:|  - scripts/README.md)' .planning/phases/01-gates-issues-and-deviation-decisions/*-PLAN.md
sed -n '284,290p' .planning/phases/01-gates-issues-and-deviation-decisions/01-04-PLAN.md
```

### Catalog, scripts, CI and legacy-tool reads

Result: confirmed current catalog wording, template placeholders/15 labels, actual CI command/environment semantics, audit side effects, comparator behavior and legacy-tool provenance.

```bash
nl -ba docs/spqr-properties.md | sed -n '1,77p'
nl -ba docs/spqr-properties.md | sed -n '199,220p'
nl -ba docs/spqr-properties.md | sed -n '267,320p'
nl -ba docs/spqr-properties.md | sed -n '321,364p'
nl -ba docs/spqr-properties.md | sed -n '415,510p'
nl -ba docs/spqr-properties.md | sed -n '431,448p'
nl -ba docs/ISSUE_TEMPLATE.md | sed -n '1,127p'
nl -ba docs/rubrics/spqr-plan-review.md | sed -n '91,126p'
nl -ba docs/STATE_INVARIANT_PROOFS.md | sed -n '1,82p'
nl -ba .github/workflows/lean.yml | sed -n '1,111p'
nl -ba .github/workflows/sorry-delta-comment.yml | sed -n '24,60p'
nl -ba scripts/check-lint.sh
nl -ba scripts/README.md
nl -ba scripts/sorry-diff.py | sed -n '1,142p'
nl -ba scripts/Audit.lean | sed -n '1,48p'
rg -n 'import |writeFile|Spqr.Specs|sorryAx|builtinAxioms|collectAxioms' scripts/Audit.lean
nl -ba .gitignore | sed -n '20,39p'
nl -ba issues/create_issues.sh | sed -n '1,70p'
ls -la issues/272
rg -n 'sorry|frame|postcondition|fix/272' issues/272/README.md
rg -n 'mlkembraid|2025.2267' README.md docs .planning/phases/01-gates-issues-and-deviation-decisions/01-RESEARCH.md | head -n 18
```

### Rust and extracted-semantics reads

Result: established public/internal error distinction, update-before-verification ordering, successful serialization boundary, D2 exception and D3/D4 dispatch. These were source reads and hand traces, not executed protocol tests.

```bash
nl -ba src/lib.rs | sed -n '95,154p'
nl -ba src/lib.rs | sed -n '351,453p'
nl -ba src/authenticator.rs | sed -n '1,90p'
nl -ba src/v1/unchunked/send_ct.rs | sed -n '90,172p'
nl -ba src/v1/unchunked/send_ek.rs | sed -n '138,175p'
nl -ba src/v1/chunked/states.rs | sed -n '174,213p'
nl -ba src/v1/chunked/states.rs | sed -n '452,531p'
nl -ba src/v1/chunked/states.rs | sed -n '267,318p'
nl -ba src/v1/chunked/states.rs | sed -n '346,420p'
rg -n '^def (v1\.chunked\.states\.States\.(send|recv)|v1\.unchunked\.(send_ct|send_ek)\.|recv |send |chain\.Chain\.add_epoch)|MacVerifyFailed|recv_next_epoch' SrcTranslated/Funs.lean | tail -n 38
nl -ba SrcTranslated/Funs.lean | sed -n '13223,13265p'
nl -ba SrcTranslated/Funs.lean | sed -n '13958,13998p'
nl -ba SrcTranslated/Funs.lean | sed -n '11163,11201p'
nl -ba SrcTranslated/Funs.lean | sed -n '11280,11320p'
nl -ba SrcTranslated/Funs.lean | sed -n '13574,13604p'
nl -ba SrcTranslated/Funs.lean | sed -n '13971,13996p'
nl -ba SrcTranslated/Funs.lean | sed -n '10335,10343p'
nl -ba SrcTranslated/Funs.lean | sed -n '13199,13223p'
nl -ba SrcTranslated/Types.lean | sed -n '712,728p'
nl -ba SrcTranslated/Types.lean | sed -n '790,812p'
nl -ba SrcTranslated/Types.lean | sed -n '719,728p'
nl -ba SrcTranslated/Types.lean | sed -n '795,803p'
```

### Lean inventory and declaration probes

Result: 173 extraction axioms, the selected 20-name policy, the two handwritten sorry sites and the multiline declaration-check failure. Searches requiring a trailing space after `axiom` undercounted multiline declarations; the subsequent keyword-boundary scan corrected that. The attempted Aeneas source-path lookup returned exit 2 because those paths were unavailable.

```bash
rg -c '^(axiom|opaque) ' SrcTranslated/*.lean
rg -n '^(axiom|opaque) |\bsorry\b|native_decide' Spqr --glob '*.lean'
rg -n '\bsorry\b' SrcTranslated/Funs.lean
wc -l sorry-manifest.txt
head -n 6 sorry-manifest.txt
rg '^Spqr\.Specs\.' sorry-manifest.txt | wc -l
rg -c '^\s*axiom ' SrcTranslated/*.lean
rg -c '^\s*opaque ' SrcTranslated/*.lean
rg -c '\bsorry\b' SrcTranslated/*.lean
rg -n '^\s*(axiom|opaque) ' SrcTranslated/FunsExternal.lean | sed -n '1,100p'
rg -c '\baxiom\b' SrcTranslated/FunsExternal.lean
rg -n '\baxiom\b' SrcTranslated/FunsExternal.lean | tail -n 32
rg -n '^axiom([[:space:]]|$)' SrcTranslated/FunsExternal.lean | wc -l
grep -cE '^axiom([[:space:]]|$)' SrcTranslated/FunsExternal.lean
grep -qE '^axiom +incremental_mlkem768\.potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275\b' SrcTranslated/FunsExternal.lean
printf 'same_line_check_exit=%s\n' "$?"
printf 'check_exit=%s\n' "$?"
awk '/^axiom([[:space:]]|$)/ {if (NF > 1) print NR, $2; else {declaration_line=NR; getline; print declaration_line, $1}}' SrcTranslated/FunsExternal.lean | tail -n 12
rg -c 'sorry --' SrcTranslated/Funs.lean
rg -n '^axiom' SrcTranslated/TypesExternal.lean
rg -n '^\s*(sorry|axiom|opaque)\b|native_decide' SrcTranslated/Funs.lean SrcTranslated/FunsExternal.lean Spqr/Crypto/Hkdf.lean Spqr/Specs/Kdf/HkdfToSlice.lean | tail -n 12
nl -ba SrcTranslated/TypesExternal.lean | sed -n '1,75p'
nl -ba SrcTranslated/FunsExternal.lean | sed -n '1744,1808p'
nl -ba SrcTranslated/FunsExternal.lean | sed -n '1819,1879p'
nl -ba SrcTranslated/FunsExternal.lean | sed -n '3660,3714p'
nl -ba SrcTranslated/FunsExternal.lean | sed -n '1981,2016p'
nl -ba Spqr/Specs/Kdf/HkdfToSlice.lean | sed -n '1,50p'
nl -ba Spqr/Crypto/Hkdf.lean | sed -n '20,65p'
nl -ba Spqr/Specs/Authenticator/Authenticator/Update.lean | sed -n '15,87p'
nl -ba Spqr/Specs/Lib/DecodeState.lean | sed -n '20,62p'
nl -ba Spqr/Specs/Aeneas/MapCollectBridge.lean | sed -n '32,75p'
nl -ba Spqr/Specs/Encoding/Polynomial/LagrangePolysForCompletePoints.lean | sed -n '36,72p'
rg -n 'DecodeState|MapCollectBridge|HkdfToSlice|LagrangePolysForCompletePoints|Authenticator.Authenticator.Update' Spqr.lean
nl -ba /home/lacra/.elan/toolchains/leanprover--lean4---v4.31.0/src/lean/Lean/Elab/Print.lean | sed -n '234,248p'
nl -ba /home/lacra/.elan/toolchains/leanprover--lean4---v4.31.0/src/lean/Lean/Message.lean | sed -n '411,420p'
rg -n -A48 -B4 'partial def collect|opaqueInfo|axiomInfo' /home/lacra/.elan/toolchains/leanprover--lean4---v4.31.0/src/lean/Lean/Util/CollectAxioms.lean
rg -n 'def (spec|theta)|\|.*fail.*False|\|.*div.*False' .lake/packages/aeneas/Aeneas/Std/Result.lean .lake/packages/aeneas/Aeneas/Std/Progress.lean 2>/dev/null
```

### Scheduler probes

Result: actual topological scheduling prevents the old deletion race, produces six effective waves, and exposes the hidden README overlap between 01-04 and 01-06.

```bash
nl -ba .planning/config.json
command -v gsd-sdk
rg -n 'wave|depends_on|parallel' /home/lacra/.claude/get-shit-done/workflows/execute-phase.md | head -n 48
rg -n 'phasePlanIndex|phase-plan-index|waves\[|depends_on' /home/lacra/.claude/get-shit-done/bin/lib/phase.cjs | head -n 35
nl -ba /home/lacra/.claude/get-shit-done/workflows/execute-phase.md | sed -n '413,478p'
rg -n -A45 -B5 'function cmdPhasePlanIndex|waves\[' /home/lacra/.claude/get-shit-done/bin/lib/phase.cjs
nl -ba /home/lacra/.claude/get-shit-done/bin/lib/phase.cjs | sed -n '392,451p'
nl -ba /home/lacra/.claude/get-shit-done/bin/lib/phase.cjs | sed -n '452,563p'
node /home/lacra/.claude/get-shit-done/bin/gsd-tools.cjs phase-plan-index 1 | node -e 'let input=""; process.stdin.on("data", chunk => input += chunk); process.stdin.on("end", () => { const data=JSON.parse(input); console.log(JSON.stringify({waves:data.waves,warnings:data.warnings},null,2)); });'
```

### Specification probes

Result: located existing local specification copies; checked Braid revision/date, relevant KDF/authentication/transition/initialization sections, and SCKA Def. 3.1/Figs. 1–2. No PDF or extracted-text file was created.

```bash
find /home/lacra /tmp -type f \( -name 'mlkembraid.pdf' -o -name 'mlkembraid.txt' -o -name '2025-2267.pdf' -o -name '2025-2267.txt' \) -print 2>/dev/null
pdfinfo /tmp/props-review/mlkembraid.pdf | head -n 17
pdfinfo /tmp/props-review/2025-2267.pdf | head -n 17
pdftotext /tmp/props-review/mlkembraid.pdf - | head -n 27
pdftotext /tmp/props-review/2025-2267.pdf - | head -n 25
rg -n '2\.2|2\.4|2\.5|2\.6|KDF_AUTH|negotiate|Ct1Ack|Ct1Acknowledged|EkSentCt1Received|fresh messages' /tmp/props-review/mlkembraid.txt | head -n 52
pdftotext -f 6 -l 9 -layout /tmp/props-review/mlkembraid.pdf - | sed -n '30,164p'
pdftotext -layout /tmp/props-review/2025-2267.pdf - | rg -n 'Definition 3\.1|Figure 1:|Figure 2:|Correctness|correctness game' | head -n 20
pdftotext -f 9 -l 9 -layout /tmp/props-review/mlkembraid.pdf - | tail -n 19
pdftotext -f 15 -l 15 -layout /tmp/props-review/mlkembraid.pdf - | head -n 48
pdftotext -f 20 -l 23 -layout /tmp/props-review/mlkembraid.pdf - | rg -n -A16 -B4 'def EkReceivedCt1Sampled.Receive|def Ct1Acknowledged.Receive|2.6 Initialization|always be able|Figure 2'
pdftotext -layout /tmp/props-review/2025-2267.pdf - | sed -n '367,407p'
pdftotext -layout /tmp/props-review/2025-2267.pdf - | sed -n '530,579p'
pdftotext -layout /tmp/props-review/2025-2267.pdf - | sed -n '367,404p'
pdftotext -layout /tmp/props-review/2025-2267.pdf - | sed -n '474,497p'
```

## Resolution map

| Finding | Suggested edit | Destination plan/section |
|---|---|---|
| F-1 | Enforce user-owned head/base choices and PR B transition; repair both complete-range reports and stale branch facts | 01-01 execution precondition; 01-07 boundary; 01-08 entry guard; 01-09 boundary |
| F-2 | Remove obsolete search instructions and contradictory greps; permit valid standalone `jq --arg` | 01-04 guidance, Task 1 acceptance, threat register; binding research examples |
| F-3 | Detect stable property identity, not mutable title; fail closed on conflicting matches | 01-04 filing algorithm; 01-07/01-09 idempotency verification |
| F-4 | Support multiline declarations in namespace-aware allowlist validation | 01-03 Task 2 |
| F-5 | Give the README note one declared owner or serialize its writers; synchronize effective waves | 01-04/01-06 file maps and tasks; plan frontmatter; ROADMAP; VALIDATION |
| F-6 | Require successful execution of the wrapped-list negative control before completion | 01-06 Task 3 acceptance and completion; 01-VALIDATION |
| F-7 | Supply D5’s second candidate resolution or explicitly authorize a format exception | 01-09 Task 1, D5 question |
---

# Planning-seat triage (round 2)

Date: 2026-09-14. Every finding below was re-verified independently before acting: the
cited `path:line`s were read, the decisive greps were re-run against the real tree, and the
scheduling claims were checked against the installed GSD scheduler rather than the plan
prose. All seven findings were **confirmed**. No finding was accepted on Codex's word.

## 1. Codex's review

**VERDICT: APPROVE-WITH-EDITS** — 6 MAJOR, 1 MINOR, no BLOCKER.

| ID | Sev | Claim | Independently confirmed? |
|---|---|---|---|
| F-1 | MAJOR | PR B work can still accumulate on PR A's head: `"skip"` waives branch selection, 01-08 has no branch precondition, 01-09 uses a bare `git diff --stat`, and the "diverged" premise is false | **Yes.** `git rev-list --left-right --count origin/la/spec-catalog...HEAD` → `0	9` (ahead, not diverged). `01-09-PLAN.md:300` was a bare `git diff --stat`. `01-08` went straight to editing. |
| F-2 | MAJOR | 01-04's acceptance predicates are mutually unsatisfiable: `grep -q 'in:title'` required to exit 1 *and* 0; `jq --arg` grep-rejected though the action prescribes it | **Yes.** Both assertions present at `01-04-PLAN.md:285` and `:289`. Stale search-based guidance also still at `:83` and in threat `T-1-16`. |
| F-3 | MAJOR | Title-based duplicate detection does not deliver INFRA-02's "one issue per property"; an edited title yields a second issue for the same ID | **Yes.** The plan admits the gap itself (`01-04:249`). `docs/ISSUE_TEMPLATE.md:8` carries `## Property: {PROP-ID}`, and `gh issue list --json` accepts `body` (checked). |
| F-4 | MAJOR | The prescribed allowlist source-validation predicate rejects a mandatory entry | **Yes.** `grep -qE '^axiom +incremental_mlkem768\.potentially_fix…_1275\b' SrcTranslated/FunsExternal.lean` → **exit 1**; the keyword is alone on `:3687` with the name on `:3688`. 119 axioms in that file have this shape. |
| F-5 | MAJOR | 01-04 now writes `scripts/README.md` without declaring it, and 01-06 owns the same file in the same computed wave | **Yes.** `01-04:208` requires the write; it was absent from `files_modified` and both `<files>` lists. `phase.cjs:524` buckets by computed topological level and `execute-phase.md:438` detects overlap from `files_modified` only — so the write was invisible to the guard. The four stale declared waves reproduce as scheduler warnings. |
| F-6 | MAJOR | The mandatory wrapped-axiom-list negative control can be waived while completion is recorded | **Yes.** `01-06:336`/`:358` permitted "partially verified", `:366` then allowed the flags to flip, against `01-VALIDATION.md:142` ("all seven rows are mandatory"). The plan's own `<done>` also said "six negative controls" for seven. |
| F-7 | MINOR | 01-09 requires two candidate resolutions per deviation but supplies one for D5 | **Yes.** `01-09:132` mandates the pair; `:135` gives one option; `docs/spqr-properties.md:443` likewise names only "the caller's contract written down". |

Codex's "cleared surfaces" were spot-checked, not re-derived: the gate-1/gate-2 byte-for-byte
claim against `.github/workflows/lean.yml:47,57` holds, `spqr.kdf.hkdf_to_slice_spec` is
correctly namespaced (`Spqr/Specs/Kdf/HkdfToSlice.lean:18,25`), and the 20-name allowlist
figure is right for the selected policy list (3 builtins + 17 stubs), distinct from the
173-axiom extraction inventory.

## 2. What I did in response

**F-1 — branch boundary (01-07, 01-08, 01-09).**
- `01-07`: `"skip"` now defers the *pull request*, not the branch decision. The action must
  re-ask for the PR B branch and must not hand control to 01-08 until the user names it;
  the answer is recorded as a literal `PR B branch:` line in `01-07-SUMMARY.md`. A
  "same branch, I'll split it later" answer is recorded verbatim as an explicit ruling.
- `01-07`: added a new `must_haves` truth and a second artifact entry asserting that
  `PR B branch:` line, so the plan cannot complete without it.
- `01-07`: replaced the false "has diverged from its remote" premise with the measured
  `0	9` (ahead by nine, zero behind) and noted that `.planning/STATE.md:76`'s
  `--force-with-lease` advice is stale. Removed the stale "2229 lines" figure that
  contradicted the corrected 25-file/7058-insertion measurement three paragraphs above.
- `01-07`: the recorded SHA is now explicitly the *implementation tip*, with a note that
  the tracked SUMMARY commit lands after it and the PR A range must include both.
- `01-08`: added a `<pr_b_branch_precondition>` block — read `01-07-SUMMARY.md`'s
  `PR B branch:` line, compare with `git branch --show-current`, STOP on mismatch, STOP if
  the line is absent, never switch branches unilaterally — and wired it into task 1's
  `<read_first>` so it is checked before the first catalog edit.
- `01-09`: the bare `git diff --stat` became `git diff --stat <PR B base>...HEAD` with the
  same "a bare diff reports nothing after commits" reasoning 01-07 already carried, plus a
  committed-range code-freeze check
  (`git diff --name-only <base>...HEAD -- src SrcTranslated '*.lean'` must be empty).

**F-2 — contradictory predicates (01-04).** Full enumeration is now the single authoritative
algorithm. The positive `in:title` assertion is gone; the negative one is joined by
`--search` and by a narrowed `--jq[[:space:]]+--arg` rejection that targets only `gh`'s
unsupported argument shape, so a standalone `jq --arg` (the prescribed implementation)
passes. The stale search guidance in `<do_not_hand_roll>` and in threat `T-1-16` was
rewritten to match, as were the five places that called exact-title matching "the
idempotency key".

**F-3 — stable-ID identity (01-04).** Duplicate detection now enumerates with
`--json number,title,body` and matches the body's whole-line `## Property: <ID>` marker
(exact, so `INFRA-01` cannot match `INFRA-01-EXTRA`). Three fail-closed paths are spelled
out and grep-asserted: a 500-row (possibly truncated) enumeration, a failed lookup, and
**more than one** matching issue or a closed-only match — each an error naming the numbers,
never a filing. Titles stay unique for human legibility; the TSV now also asserts unique
IDs, which is what the new key requires. The honest residual moved from "a hand-edited
title defeats this" to "a hand-deleted `## Property:` line defeats this".

**F-4 — multiline declarations (01-03).** The validation predicate must now match the
declaration keyword and the name **across intervening whitespace including a newline**
(`grep -Pzo`/`perl -0777`/`python3`, or `grep -A1` on a bare `^axiom$`), with the failing
command and its exit 1 quoted in the plan as verified fact. Added an acceptance criterion
naming the libcrux-1275 entry specifically, and an explicit prohibition on deleting,
shortening or renaming an allowlist entry to satisfy the tooling.

**F-5 — README ownership and waves.** `scripts/README.md` is now declared in 01-04's
`files_modified` and in task 1's `<files>`, and `01-06` depends on `01-04` so the shared
file is never written concurrently. Declared waves were conformed to the DAG
(01-05→3, 01-06→3, 01-07→4, 01-08→5, 01-09→6); `phase-plan-index 1` now emits **zero**
declared-wave warnings, and a pairwise check confirms no intra-wave `files_modified`
overlap remains. `.planning/ROADMAP.md`'s wave listing and `**Plans**:` line and
`01-VALIDATION.md`'s per-task Wave column were resynced; `01-02`'s ROADMAP task was
updated so it does not re-apply the old line or renumber the headings.

**F-6 — non-waivable wrapped-list control (01-06).** The waiver is gone. Control 7 now
prescribes a deterministic way to force the wrap — `set_option format.width 20` in the
scratch file; `format.width` is a registered builtin option in this toolchain
(`Lean/Data/Format.lean:23`, verified) — with "find a theorem that wraps at the default
width" as the fallback and **STOP and report** if neither works, because an unwrapped log is
not evidence about a wrapped list. The acceptance criterion, the validation-flag criterion
and the `<done>` line were all tightened, and the "six negative controls" miscount fixed to
seven.

**F-7 — D5's second option (01-09).** D5 is now marked as the explicit exception: the plan
states that the catalog supplies only one option and writes the pair out — (a) confirm
caller-managed handling, with the PROP-43 contract as the spec's text, or (b) the spec
requires the implementation to enforce session discontinuation. The plan instructs the
executor to let the question follow from the spec text quoted in part 2 rather than
asserting from memory what §2.4 requires. The three downstream restatements were reworded
so none implies the catalog already offers a pair.

## 3. What I deliberately did NOT do

- **Did not change `docs/spqr-properties.md` §11's closing paragraph** to add D5's second
  option. That is a catalog statement change and belongs to the user / Signal; the note now
  supplies the alternative as a *question*, which is the note's job. If the user wants the
  catalog to name a pair for D5, that is a one-line edit to add to plan 01-08's task list.
- **Did not fix `.planning/STATE.md:76`** ("Local `la/spec-catalog` has diverged from
  `origin/la/spec-catalog`; pushing needs `--force-with-lease`"). It is false as of today —
  the branch is ahead by nine, zero behind — but STATE.md is not in any plan's
  `files_modified` and it carries a push instruction the user acts on. Flagged here;
  `01-07` now tells the reader the line is stale and to re-measure.
- **Did not change `branching_strategy: none`** in `.planning/config.json`, and did not
  create, switch or split any branch. F-1's real fix is a workflow setting or a manual
  branch split, both of which are the user's call; the plans now *stop* rather than silently
  landing PR B on PR A's head, which is the reviewable part.
- **Did not weaken ROADMAP criterion 2 or 3, or any success criterion.** Codex explicitly
  cleared the criterion-1 and criterion-3 rewordings as authorized scope corrections
  recorded in `01-DISCUSSION-LOG.md:156` and research Q-1; nothing there was touched.
- **Did not adopt Codex's suggestion to "distinguish the recorded implementation tip from
  the subsequent tracked SUMMARY commit" by changing how GSD commits.** Recorded it as a
  reporting obligation in 01-07 instead; changing GSD's commit ordering is out of scope for
  a plan review.
- **Did not verify `set_option format.width` actually wraps the `#print axioms` message.**
  That needs a `lake env lean` probe on a built tree, which this phase's plan 01-06 is the
  place for. The plan therefore prescribes it as the *first* route with a named fallback and
  a STOP, rather than as an established fact.
- **Did not re-derive Codex's specification (PDF) readings.** Its §2.4 termination contrast
  is plausible and is cited only as motivation for D5's question (b); the plan is written so
  the executor quotes the spec text rather than relying on it.

---

# Supersession note — 2026-09-15

This review, and round 1 before it, reviewed the **original** Phase 1 plan set: close every
Open catalog row, with one GitHub issue per property. On 2026-09-15 the user re-scoped the
goal to *prove as many non-trivial specs as possible*, added two cross-cutting requirements
(PROV-01 provenance, REV-01 statement review), and dropped automated issue creation. The nine
plans reviewed here were archived to `.planning/archive/01-superseded-2026-09-15/` before
execution and replaced by a new nine-plan set in this directory.

The review is retained because its findings were carried forward, not discarded. Mapping:

| This review's finding | Carried into |
|---|---|
| F-1 — PR separation, `"skip"` waiving branch selection, bare `git diff --stat` | New 01-05 (`PR B branch:` line, `"skip"` defers only the PR), new 01-06 (`<pr_b_branch_precondition>` STOP block), new 01-09 (`<base>...HEAD` range plus a committed-range freeze check) |
| F-2, F-3 — contradictory duplicate-detection predicates, title-vs-ID identity | **Moot.** The issue script they were about is out of scope |
| F-4 — the allowlist validation predicate rejects the multiline libcrux-1275 declaration | New 01-02 task 2, with the failing `grep` and its exit 1 quoted as verified fact and an acceptance criterion naming the entry |
| F-5 — undeclared `scripts/README.md` write; stale declared waves | New plan set: README declared in 01-02 and 01-04 only, in different waves; declared waves match the DAG (`phase-plan-index 1` emits no warning) |
| F-6 — the wrapped-axiom-list control could be waived | New 01-04 task 3 control 8 and `01-VALIDATION.md`: non-waivable, with `set_option format.width 20` as the deterministic route and a STOP if no route works |
| F-7 — D5 given one candidate resolution where two were required | **Moot in this form.** The Signal note is deferred to v2 (DEV-05); D5's caller contract is still written out in new 01-08 task 2 |

Two findings from the review's *cleared surfaces* also carried forward as facts the new plans
rely on: gates 1 and 2 are byte-for-byte `lean.yml:47,57`, and the 20-name allowlist is correct
for the selected policy list as distinct from the 173-axiom extraction inventory.
