<!--
  Provenance
  ----------
  Reviewer engine : Codex CLI (`codex exec`), OpenRouter-backed
  Reasoning effort: high (`model_reasoning_effort="high"`)
  Sandbox mode    : read-only (kernel-enforced, bwrap)
  Rubric          : docs/rubrics/spqr-plan-review.md (appended verbatim to the prompt)
  Prompt          : /tmp/phase01-review-assignment.md
  Raw output      : /tmp/phase01-codex-review.md (reproduced verbatim below, unedited)
  Run log         : /tmp/phase01-codex-review-log.txt
  Date            : 2026-09-14
  Phase           : 01-gates-issues-and-deviation-decisions (plans 01-01 .. 01-09)
  Branch          : la/spec-catalog @ d7cf202
  Triage          : appended after the `---` separator by the planning seat (Claude Opus 5)
-->

# SPQR Plan Review

- Phase: 01 — Gates, Issues and Deviation Decisions
- Plans reviewed: 01-01 through 01-09, as one set, under `.planning/phases/01-gates-issues-and-deviation-decisions/`
- Date: 2026-09-14
- Branch/base verified: `la/spec-catalog`, HEAD `d7cf202a02c69ddc7d33f4c870293199b3f36cd6`; `main`, `origin/main`, and pin `d47083c` resolve to `d47083cd3abf2906229efa38ae2bfb1121498af0`. No source/extraction diff against that pin.
- VERDICT: REJECT

## Findings

References to `01-*-PLAN.md`, `01-RESEARCH.md`, and other phase documents below are relative to `.planning/phases/01-gates-issues-and-deviation-decisions/`.

### F-1 — BLOCKER

**Claim:** Plan 01-08 commits the catalog to MAC-error constructors that the public API does not return, supplying an incorrect statement for the later AUTH-01 theorem.

**Evidence:** `01-08-PLAN.md:293` requires the caller contract to say that `spqr::recv` returns `Err(InvalidHdrMac)` or `Err(InvalidCtMac)`. Those are **internal authenticator errors**, not public `spqr::Error` variants:

- `src/authenticator.rs:59` returns internal `InvalidCtMac`; the header verifier likewise returns internal `InvalidHdrMac`.
- `src/lib.rs:145` converts **every** `authenticator::Error` to `Error::MacVerifyFailed`.
- `src/v1/unchunked/send_ek.rs:143` returns the crate-level error type; its `?` at `src/v1/unchunked/send_ek.rs:160` performs that conversion.
- `src/lib.rs:356` declares the public return type, and `src/lib.rs:425` propagates the converted error.
- The extraction independently confirms the distinction: `SrcTranslated/Types.lean:719` defines `authenticator.Error`; `SrcTranslated/Types.lean:795` defines `spqr.Error`, with `MacVerifyFailed` at line 799.
- `SrcTranslated/Funs.lean:10339` implements the conversion as `ok Error.MacVerifyFailed`; the failure branch at `SrcTranslated/Funs.lean:13257` invokes it.

The relevant read probe returned:

```text
145 impl From<authenticator::Error> for Error {
146     fn from(_v: authenticator::Error) -> Self {
147         Error::MacVerifyFailed
```

The already-updated-authenticator assertion, by contrast, survives inspection. A concrete failure trace, conditioned on successful decoding, decapsulation, and KDF evaluation, is:

| Step | Local execution at epoch 7 | Caller’s serialized state | Result |
|---|---|---|---|
| 1 | `recv` decodes an owned local state containing authenticator `A` | Original bytes `S` | Continues |
| 2 | `recv_ct2` derives the epoch secret | Still `S` | Continues |
| 3 | `auth.update` produces local authenticator `A′` | Still `S`, encoding `A` | Continues |
| 4 | `verify_ct` rejects the MAC | Still `S` | Internal `InvalidCtMac` |
| 5 | `?` converts and propagates the error; the success-state construction is not reached | Still `S` | Public `MacVerifyFailed`; no returned state or key |

The ordering is explicit at `src/v1/unchunked/send_ek.rs:150`, `:156`, `:158`, and `:160`, and at `SrcTranslated/Funs.lean:13241`. A header failure occurs before the new `HeaderReceived` construction at `src/v1/unchunked/send_ct.rs:107`.

Thus the caller retains the pre-update state; this does **not** establish secure zeroization of the discarded local values. In the extracted interface the protocol error is an inner Rust-result error inside the outer Aeneas `Result`, not an Aeneas execution failure.

This is a statement-level blocker now: `01-08-PLAN.md:311` explicitly makes this paragraph the source for AUTH-01, while lines 313–315 direct the executor to record contradictory evidence rather than correct the mandated claim.

**Minimal suggested edit:** State public `Err(MacVerifyFailed)`, distinguish the two internal causes, and preserve the correctly scoped caller-state rollback claim. Replace “record the discrepancy rather than adjusting the claim” with a stop-and-correct requirement before publishing the contract. Carry the correction into the research’s D5 explanation and the downstream note/issue bodies.

### F-2 — MAJOR

**Claim:** The live repeated-execution tests can create duplicate issues before detecting that the claimed idempotency failed.

**Evidence:** `01-04-PLAN.md:200` specifies exact-title duplicate detection using a search limited to 200 results. `01-07-PLAN.md:179` and `01-09-PLAN.md:201` then require an immediate second live `--execute` invocation.

The plans’ own research identifies the counterexample: `01-RESEARCH.md:1395`, assumption A4, says a second run within seconds can re-file because title search may not yet index the first issue. Its “minutes to days apart” justification does not apply to the mandated tests.

| Invocation | Search observation permitted by A4 | Action prescribed by the plan | Live state |
|---|---|---|---|
| First | No exact-title result | Create issue `N` | One issue |
| Immediate repeat | Newly created issue still absent from search results | Create issue `N+1` | Two issues for the same ID |
| Count verification | Count increased too far | Report failure | Duplicate already exists |

Exact-title identity also fails to recognize an issue whose title was edited, despite the stronger “one issue per property ID” claim. Neither a truncated search nor a count check establishes absence. Lookup failure or an uncertain create response must not be treated as permission to create again.

**Minimal suggested edit:** Remove live mutation as the mechanism for testing stale-search/retry behavior. Specify a serialized, fail-closed lookup/create procedure using stable property identity, complete non-search enumeration, and reconciliation after uncertain outcomes. Exercise repeated calls and stale results with a nonmutating fake `gh` before the approved live filing. Do not claim atomic concurrent idempotency without a mechanism providing it.

### F-3 — MAJOR

**Claim:** Plan 01-09 does not establish that the user has authorized its four live DEV-issue writes.

**Evidence:** D-01 requires review before filing at `01-CONTEXT.md:26`. Plan 01-07 shows all nine listing rows, but explicitly scopes the next filing action to **five PR A IDs** at `01-07-PLAN.md:125`; its blocking approval and stop are at lines 131–135.

Plan 01-09’s task beginning at `01-09-PLAN.md:178` is automatic. It checks the newly rendered DEV bodies and immediately executes four issue creations at lines 195–204. The next blocking human checkpoint begins only at line 231, **after** those writes. Reviewing a nine-row listing while approving a stated five-ID operation is not an unambiguous authorization for the later four-ID operation.

The label operation also uses `--force` at `01-04-PLAN.md:178`. The assertion that none of the labels exists “today” at `01-07-PLAN.md:128` must not substitute for checking the actual label changes at execution time.

**Minimal suggested edit:** Before the PR B mutation, require a blocking approval naming the four final DEV IDs, titles, labels, and repository. Alternatively, make the initial checkpoint explicitly authorize both later batches and define what changes invalidate that approval. Refresh and disclose any existing labels that `--force` would modify.

### F-4 — MAJOR

**Claim:** The plans do not establish branch ownership or PR-range checks sufficient to keep PR A and PR B separate.

**Evidence:**

- `.planning/config.json:10` sets `branching_strategy` to `none`; execution starts on `la/spec-catalog`.
- `01-07-PLAN.md:269` postpones the base-branch decision until PR A’s work is complete, suggesting PR A target `la/spec-catalog`.
- No corresponding precondition ensures the work was committed on a distinct PR A branch, or requires a transition to a distinct PR B branch before 01-08.
- `01-09-PLAN.md:185` permits running from the PR A branch while lines 195–199 require the post-01-08 catalog. The plan does not separate the script checkout from the catalog/data checkout.
- `01-07-PLAN.md:264` and `01-09-PLAN.md:271` call plain `git diff --stat` the whole PR change set. After task commits, that command omits the committed changes entirely.
- `01-07-PLAN.md:358` requires zero repository changes while line 362 requires a new `.planning/.../01-07-SUMMARY.md`. Planning artifacts are tracked and therefore are real PR scope, not invisible runtime state.

The factual basis for the boundary report is also stale:

```text
git rev-list --left-right --count origin/la/spec-catalog...HEAD
0    9
```

The branch is ahead, not diverged. The actual `git diff --stat origin/main..HEAD` reports **25 files and 7058 insertions**, not the prescribed 14 files and 2229 insertions at `01-07-PLAN.md:272`.

No plan commands an agent push or PR creation; that absolute prohibition survives. The defect is that stopping alone does not establish coherent branch boundaries.

**Minimal suggested edit:** Establish the user-owned branch/base choices before execution, record PR A’s final tip, and require an explicit branch transition before PR B edits. Verify each complete PR range, including tracked planning outputs and committed frozen-path changes. Refresh branch facts instead of prescribing stale output. Preserve the prohibitions on agent pushes and PR creation.

### F-5 — MAJOR

**Claim:** A legal wave-2 execution order deletes an untracked input before plan 01-04 reads it.

**Evidence:** Plan 01-04 and plan 01-05 are both wave 2. The former depends on 01-01; the latter depends on 01-03. Neither orders them relative to each other.

`01-04-PLAN.md:136` requires reading `issues/create_issues.sh`; lines 147–148 require reusing its label colors. `01-05-PLAN.md:174` deletes the entire directory.

The probes confirm that recovery from Git is unavailable:

```text
git ls-files issues/
# no output

git check-ignore -v issues/create_issues.sh
.gitignore:25:issues/    issues/create_issues.sh
```

With parallelization enabled at `.planning/config.json:4`, an allowed schedule is:

| Order | Plan | Effect |
|---|---|---|
| 1 | 01-05, after its human checkpoint | Deletes ignored `issues/` |
| 2 | 01-04 | Required color-source file no longer exists |

The human deletion checkpoint protects against unauthorized deletion, but it does not repair this missing dependency.

**Minimal suggested edit:** Order retirement after 01-04 has consumed and verified the legacy inputs, adjusting waves and dependencies accordingly; alternatively, require an approved immutable capture before either task can delete the originals.

### F-6 — MAJOR

**Claim:** The specified issue-script interface contains a rejected `gh` invocation and contradictory execution-argument requirements.

**Evidence:** `01-04-PLAN.md:201` prescribes:

```bash
gh issue list --repo "$REPO" --state all --limit 200 --search "\"$title\" in:title" --json number,title --jq --arg t "$title" 'map(select(.title == $t)) | .[0].number // empty'
```

`gh --jq` accepts an expression; it does not expose standalone `jq`’s `--arg` interface. The exact command shape was tested read-only with installed `gh` 2.100.0:

```text
unknown arguments ["t" "INFRA-01: issue template names the four real gates" "map(select(.title == $t)) | .[0].number // empty"]
gh_exit=1
```

Separately, `01-04-PLAN.md:163` requires every `--execute` invocation without IDs to fail. Yet `01-07-PLAN.md:170` requires this to succeed:

```bash
./scripts/create-property-issues.sh --labels-only --execute
```

No explicit labels-only exception resolves the conflict.

**Minimal suggested edit:** Specify a valid JSON-filtering interface with safe argument binding, and explicitly define the labels-only exception—or supply the required arguments consistently. Add nonmutating interface checks before any label or issue operation.

### F-7 — MAJOR

**Claim:** The gate runner’s completion and baseline rules permit incomplete or unverified evidence to be treated as a successful full check.

**Evidence:**

1. `01-03-PLAN.md:185` says a cache miss starts the baseline build; lines 193–195 instead say no baseline without `--refresh-baseline` produces `SKIPPED` without setting failure. These prescribe different cold-start behavior.
2. Gate 4 is skipped without theorem arguments at `01-03-PLAN.md:291`, but `01-VALIDATION.md:40` calls the bare runner the “full” after-wave/boundary check. The full-suite row at line 31 uses targets, so the validation document also disagrees with itself.
3. Gate 3a’s `test -f sorry-manifest.txt` at `01-03-PLAN.md:176` does not establish that this invocation produced the file. The existing root manifest is indeed stale:

   ```text
   sorry-manifest.txt 2026-08-07 17:12:57.593789885 +0200 14139 bytes
   134 sorry-manifest.txt
   ```

4. Reusing an existing worktree with `checkout --detach` at `01-03-PLAN.md:188` does not establish that its audited contents are clean. Local changes can survive checkout. Naming the resulting cache file after `BASE_SHA` therefore does not prove that its contents came from that SHA.
5. Merely replacing `exit 1` with `fail=1` does not make the inherited `set -euo pipefail` build pipeline continue after a nonzero build. This contradicts the promised all-gates report at `01-03-PLAN.md:162`.

The unchanged `sorry-diff.py` cannot compensate: `scripts/sorry-diff.py:105` deliberately treats a missing baseline as no comparison, not failure.

**Minimal suggested edit:** Define one strict full-run contract: explicit targets, a successfully generated head manifest, and a baseline verified against a clean dedicated checkout. Build the missing baseline or fail the full check; reserve skipping for an explicitly partial mode that cannot discharge completion. Handle subprocess failures deliberately so required later reports are not silently bypassed.

### F-8 — MAJOR

**Claim:** Gate 4’s prescribed line-based parser does not cover Lean’s multiline axiom-list output.

**Evidence:** `01-03-PLAN.md:298` counts report-header lines and lines 302–303 require splitting the bracketed list on each `depends on axioms` line.

The installed pinned Lean source establishes a broader output grammar without requiring elaboration:

- `/home/lacra/.elan/toolchains/leanprover--lean4---v4.31.0/src/lean/Lean/Elab/Print.lean:244` formats the axiom collection as a `MessageData` list.
- `/home/lacra/.elan/toolchains/leanprover--lean4---v4.31.0/src/lean/Lean/Message.lean:414` documents newline-separated list formatting; line 417 joins items with `Format.line`.

Consequently, one matching report header does not establish that the entire axiom list was consumed. Depending on the executor’s implementation, a continuation-line axiom can be missed or a legitimate wrapped report can be rejected. The required probes do not specifically require a long closure containing an unexpected non-`sorryAx` axiom on a continuation line.

**Minimal suggested edit:** Parse complete reports through their closing bracket, normalize permitted whitespace, and reject incomplete or malformed reports. Add a negative control placing an unexpected axiom on a continuation line. Do not mark A1 verified before that output shape has been checked.

### F-9 — MAJOR

**Claim:** The local-versus-CI validation lacks an executable baseline deployment and conflates checks with different comparison semantics.

**Evidence:** `01-06-PLAN.md:210` requires running the new script inside the `origin/main` worktree. That revision contains neither the new runner nor its allowlist:

```text
git ls-tree origin/main scripts/check-gates.sh scripts/check-lint.sh
100755 blob 5560b2f8d1e0c5c0ae9ff860f28e4299428a02e1 scripts/check-lint.sh
```

No overlay or invocation arrangement specifies how the reviewed script and allowlist will be used while auditing the baseline tree rather than their own checkout.

The comparison also has distinct semantics:

- `.github/workflows/lean.yml:68` restores the manifest for the **actual PR base ref and SHA**, not unconditionally `origin/main`.
- `.github/workflows/sorry-delta-comment.yml:43` invokes the comparator without `SORRY_FAIL_ON_NEW=true`; it reports a delta rather than making that delta a failing Lean gate.
- `01-06-PLAN.md:212` selects the latest `main` CI run but does not require its `headSha` to equal the locally audited SHA.
- Gate 4 has no CI counterpart, correctly acknowledged at `01-06-PLAN.md:217`.

Gates 1 and 2’s build/linter commands and greps **do** literally match the workflow. The finding is not command drift in those gates.

**Minimal suggested edit:** Specify how the exact reviewed runner and allowlist operate against a pinned baseline working directory. Require matching local/CI source SHAs. Compare genuinely shared checks separately from the stricter local delta policy, and retain the explicit “no CI counterpart” result for gate 4.

### F-10 — MAJOR

**Claim:** Several mandatory acceptance predicates cannot pass an implementation that follows the plans.

**Evidence:**

| Predicate | Contradiction or read-only result |
|---|---|
| Allowlist source-existence loop, `01-03-PLAN.md:329` | It greps the entire non-comment line, although line 277 requires trailing source comments. Those annotated lines do not occur in the declaration files. |
| Same loop, even after stripping comments | The valid FQN `spqr.kdf.hkdf_to_slice_spec` is expressed by `namespace spqr.kdf` plus a bare declaration at `Spqr/Specs/Kdf/HkdfToSlice.lean:18` and `:25`. Literal full-name search returned exit 1. |
| Zero `rm -rf`, `01-03-PLAN.md:235` and `:426` | Task 2 explicitly mandates `trap 'rm -rf "$SCRATCH_DIR"' EXIT` at line 293. |
| Section-11 parser, `01-08-PLAN.md:164` | The quoted awk program contains literal `f \&\&`. The prescribed probe returned `awk: 1: unexpected character '\'`, then `0`; the outer expected-five assertion cannot pass. |

The awk pipeline itself returned zero because `wc` succeeded, illustrating why checking only its pipeline status is insufficient.

**Minimal suggested edit:** Make source validation namespace-aware and strip annotations, reconcile scratch cleanup with the destructive-operation policy, and correct the awk expression with error propagation. Validate these checks independently of the future file contents.

### F-11 — MAJOR

**Claim:** The dry-run contract does not expose the rendered bodies required by the plans’ own review checkpoints.

**Evidence:** `01-04-PLAN.md:160` says dry-run prints a body **path**. Lines 188–190 put that body under a temporary directory removed on exit. Once the command returns, the advertised body path is gone.

Nevertheless, `01-04-PLAN.md:321` requires examining a rendered body, and `01-07-PLAN.md:120` requires showing the full INFRA-01 body to the user before authorization. No show-body mode or retained-output option is specified.

Rendering is also underspecified: the eleven TSV columns at `01-04-PLAN.md:261` supply neither `LEAN_STATEMENT` nor `APPROACH`, although both substitutions are required at line 186. The placeholder guard at line 197 does not match `{PROP-ID}`, because its character class excludes the hyphen.

**Minimal suggested edit:** Provide a nonmutating way to print the complete rendered body before temporary cleanup, define truthful values for fields absent from the TSV, and check the complete placeholder set. Use that interface in both the pre-write review and body-verification steps.

### F-12 — MINOR

**Claim:** Several research claims labeled verified or used as exact citations are stale or inaccurate, although the intended 20-entry allowlist count is defensible.

**Evidence:**

- `01-RESEARCH.md:1480` claims 55 `axiom`/`opaque` declarations in `FunsExternal.lean`. The declaration scan counted **173 axioms and one opaque** there.
- `01-03-PLAN.md:283`, `01-06-PLAN.md:141`, and research A2 name `Spqr.Crypto.Hkdf.HMAC_SHA256`. The actual namespace and declaration at `Spqr/Crypto/Hkdf.lean:27` produce **`crypto.HMAC_SHA256`**.
- `01-03-PLAN.md:267` places `opaque hkdf_to_slice` beside the handwritten spec. It is actually at `SrcTranslated/FunsExternal.lean:3669`.
- `01-04-PLAN.md:258` cites research lines 1483–1490 as Q-5; those lines are the source inventory. Q-5 begins at `01-RESEARCH.md:1460`.
- Research Q-3 at `01-RESEARCH.md:1444` describes the historical #272 postcondition and a `sorry` as though present at the cited current lines. The current `Spqr/Specs/Encoding/Polynomial/LagrangePolysForCompletePoints.lean:47` theorem preserves the previous `y` field at line 58; line 57 is not a `sorry`.

These errors do not justify broadening the allowlist. They do undermine claims that the cited inventory and historical defect were verified against this tree.

**Minimal suggested edit:** Refresh the exact names, declaration inventory, and research pointers. Label the #272 analysis historical if it is shown or posted. Preserve the distinction between the full extraction inventory and the deliberately restricted allowlist.

## Cleared surfaces

### 1. Catalog fidelity

The source pin is consistent. Although `076a85d` is the last commit touching `src/`, both it and `d47083c` identify the same source tree:

```text
040000 tree fba290e6025c144806a3b0c9b420baf25a85e430 src
```

`git diff --stat d47083c -- src/ SrcTranslated/` is empty. There is no pinned-source discrepancy to report.

The D1 code target is accurate: `src/authenticator.rs:44` concatenates the previous root key with the update key and uses a 32-byte zero salt. The proposed D2–D4 restatements match the inspected strict Greater dispatch, acknowledgment emission, and additional accepted Ek-chunk path at `src/v1/chunked/states.rs:282`, `:464`, `:484`, and `:513`. F-1 isolates the incorrect D5 public-error claim.

The external ML-KEM Braid Rev. 1 PDF and SCKA paper were not independently obtained in this review. Accordingly, the catalog’s external citations—particularly Braid §2.2/§2.4/§2.6 and SCKA Def. 3.1/Figs. 1–2—are not certified here. The findings above are independently established by repository evidence.

### 2. Internal consistency

No new committed Lean module is proposed, so no new `Spqr.lean` re-export is required. The sequential edits to `scripts/check-gates.sh` and `scripts/README.md` in 01-03 followed by 01-06 are intentional. Likewise, 01-05 depends on 01-03 for their shared `.gitignore` edits. The missing dependency is specifically the legacy-input lifetime identified in F-5.

The template contains the claimed 15 labels: nine type labels, four status labels, and two special labels. Plan 01-08 preserves property proof statuses and explicitly updates the §12 D1–D5 index entry at `01-08-PLAN.md:158`.

### 3. Statement-level soundness

The relevant error types and nested result structure were checked against the extraction, not inferred from Rust notation. No theorem proof or guessed provability was used.

The existing global nonoverflow assumption remains explicit at `docs/spqr-properties.md:422`; plan 01-08 retains the existing PROP-50 context rather than deleting its fairness qualification. No separate epoch-overflow or vacuity finding is warranted on those grounds. The substantive statement defect is F-1.

### 4. Semantic closure

Besides the failing-MAC trace in F-1, a successful terminal transition was checked. Assume valid completing chunks/MACs and successful prerequisite computations:

| Step | Party A | Party B | Message/key consequence |
|---|---|---|---|
| Initial | `EkSentCt1Received(7)` | `Ct2Sampled(7)` | B can supply the completing Ct2 |
| A receives valid completing Ct2 | `NoHeaderReceived(8)` | `Ct2Sampled(7)` | A returns the epoch-7 secret |
| A sends | `NoHeaderReceived(8)` | `Ct2Sampled(7)` | Sends epoch 8 with payload `None`; no new key |
| B receives that epoch-8 message | `NoHeaderReceived(8)` | `KeysUnsampled(8)` | Exceptional `Ct2Sampled` Greater arm succeeds; no key |

The extracted success return is at `SrcTranslated/Funs.lean:13251`; `NoHeaderReceived.send` is at `SrcTranslated/Funs.lean:11289`; the exceptional next-epoch receive is at `SrcTranslated/Funs.lean:13971`. This confirms that the D2 exception is necessary and that advancing state does not imply every step returns a key.

### 5. Precedent and interface realism

`update_spec` exists on `main`, is tagged `@[step]`, and has the expected memory-bound hypothesis and zero-salt/concatenated-IKM postcondition at `Spqr/Specs/Authenticator/Authenticator/Update.lean:47`. Its import is present at `Spqr.lean:71`.

The branch-only `States/Send.lean`, `States/Recv.lean`, and liveness-axiom `External.lean` were not mistaken for merged prerequisites. This phase does not import them.

No operative caller of `scripts/check-lint.sh` was found in the searched workflows, scripts, documentation, `lakefile.toml`, or configured hooks. Thus no concrete caller-specific breakage from the proposed shim was established; the new runner’s own contract defects are reported separately.

### 6. Trusted-base discipline

The checked tree contains:

| Scope | Axioms | Opaques |
|---|---:|---:|
| `SrcTranslated/FunsExternal.lean` | 173 | 1 |
| `SrcTranslated/TypesExternal.lean` | 3 | 0 |
| `Spqr/Specs/Kdf/HkdfToSlice.lean` | 1 | 0 |
| `Spqr/Crypto/Hkdf.lean` | 0 | 1 |
| **Total in these repository source trees** | **177** | **2** |

The proposed allowlist is a restricted policy, not this complete inventory. Its **three builtins plus seventeen selected declarations** can be grounded in the tree. The seventeen exact names are:

```text
spqr.kdf.hkdf_to_slice_spec
libcrux_ml_kem.mlkem768.incremental.validate_pk_bytes
libcrux_ml_kem.mlkem768.incremental.encapsulate1
libcrux_ml_kem.mlkem768.incremental.encapsulate2
libcrux_ml_kem.mlkem768.incremental.decapsulate_compressed_key
libcrux_ml_kem.mlkem768.incremental.pk1_len
libcrux_ml_kem.mlkem768.incremental.pk2_len
libcrux_ml_kem.mlkem768.incremental.encaps_state_len
libcrux_ml_kem.mlkem768.incremental.KeyPairCompressedBytes.from_seed_spec
libcrux_ml_kem.constants.SHARED_SECRET_SIZE
libcrux_ml_kem.ind_cca.incremental.types.Ciphertext1.len
libcrux_ml_kem.ind_cca.incremental.types.Ciphertext2.len
libcrux_hmac.hmac
libcrux_hmac.hmac_sha256_tag32_spec
encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.decoded_message
incremental_mlkem768.potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275
encoding.gf.mul2_u16
```

The builtins are `propext`, `Classical.choice`, and `Quot.sound`, matching `scripts/Audit.lean:27`. The HKDF spec’s fully qualified name is correct despite the failing literal-source grep.

The pinned Lean collector at `Lean/Util/CollectAxioms.lean:57` adds axiom declarations and recursively inspects opaque bodies/types at line 62. An opaque declaration’s own name is not itself an axiom-list entry; this does not imply its dependencies are invisible.

No new committed axiom, opaque, `sorry`, or `native_decide` is authorized. The negative controls are segregated from the deliverable tree. No quiet trusted-base expansion was established.

### 7. Gates

The existing build and linter command lines and warning/error greps literally match `.github/workflows/lean.yml:47` and `:57`.

The proposed `sorry-diff.py` argument order and `SORRY_FAIL_ON_NEW=true` spelling match its real interface at `scripts/sorry-diff.py:5`. It exits nonzero for a missing head manifest, does not fail merely because the baseline is absent, and writes `.sorry-delta-comment.md` when new specification sorries exist. It can also append to paths supplied through `GITHUB_OUTPUT` and `GITHUB_STEP_SUMMARY`; leaving those unset is appropriate.

`Audit.lean` imports `Spqr` and scans the imported project environment, including `Spqr` and `SrcTranslated` modules; it does not discover unimported specification files merely because they exist on disk. Its findings are not themselves a failing exit code. The planned import-blindspot negative control is therefore relevant.

The phantom gate is present at the cited template/rubric/CLAUDE locations. Removing it is legitimate work, not a finding against an output that does not exist yet.

### 8. Boundedness and safety

Every plan declares zero committed Lean changes and `allowed_sorries: 0`. No task was found that directs modification of `src/` or `SrcTranslated/`, an agent push, or agent PR creation. The retirement task has a genuine human checkpoint before deleting ignored data.

The unresolved safety defects concern ordering, live issue mutations, branch boundaries, and gate evidence—not an invented source-freeze violation. No repository files, GitHub issues, or labels were modified during this review. Existing user changes were preserved.

### 9. Roadmap and catalog coherence

Plan 01-02’s two success-criterion changes are **authorized contract maintenance**, not a plan rewriting its own acceptance criteria without authority:

- `01-CONTEXT.md:65` explicitly orders the just-in-time issue-filing change and replacement of the all-properties issue count.
- `01-RESEARCH.md:1408` records the human ruling of September 14, 2026 to scope the phantom-token grep and leave planning history intact.

Likewise, the two-table §11 layout is explicitly authorized at `01-RESEARCH.md:1456`. Preserving proof statuses while recording provisional decisions is appropriate for this documentation phase. Those clearances do not cure the incorrect D5 statement or the incomplete execution/PR boundaries.

## Probe log

All successful terminal probes were read-only and ran from the repository root. No build, elaboration, source mutation, issue creation, label creation, push, or PR operation ran. The `gh issue list` interface probe failed during local argument parsing.

The inherited handoff retained results and selected commands, but not a complete verbatim transcript of every earlier file read. That limitation is disclosed rather than replacing missing commands with an invented transcript. The re-verification command payloads are recorded verbatim below; repeated evidence is intentional. Some broad read outputs were truncated by the tool, and relevant portions were subsequently read in narrower probes.

<details>
<summary>1. Repository identity, differences, and instruction-file discovery</summary>

```bash
pwd; git status --short --branch; git rev-parse HEAD main origin/main d47083c; git log -1 --format='%h %s' -- src/; git ls-tree d47083c src; git ls-tree 076a85d src; git diff --stat d47083c -- src/ SrcTranslated/; git rev-list --left-right --count origin/la/spec-catalog...HEAD; git diff --stat origin/main..HEAD; rg --files -g AGENTS.md -g '!SrcTranslated/**' -g '!src/**' .planning docs scripts .github issues 2>/dev/null; for path in /AGENTS.md /home/AGENTS.md /home/lacra/AGENTS.md /home/lacra/git_repos/AGENTS.md /home/lacra/git_repos/baif/AGENTS.md AGENTS.md; do if [ -f "$path" ]; then printf '\n--- %s ---\n' "$path"; cat "$path"; fi; done
```

Result: verified HEAD/base/pin, identical source trees, no frozen-path diff, branch ahead by nine, and 25-file committed diff. Existing `.planning/config.json` modification and unrelated untracked files remain.

</details>

<details>
<summary>2. Plan-set frontmatter and gate-plan reads</summary>

```bash
for file in .planning/phases/01-gates-issues-and-deviation-decisions/01-0{1,2,3,4,5,6,7,8,9}-PLAN.md; do printf '\n--- %s ---\n' "$file"; nl -ba "$file" | sed -n '1,100p'; done; printf '\n--- gate plan body ---\n'; nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-03-PLAN.md | sed -n '125,350p'; printf '\n--- gate validation plan ---\n'; nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-06-PLAN.md | sed -n '100,250p'
```

Result: inspected scope, waves, dependencies, deliverables, and gate validation; broad output truncated.

```bash
nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-03-PLAN.md | sed -n '145,340p'; nl -ba scripts/check-lint.sh; nl -ba scripts/sorry-diff.py | sed -n '1,225p'; nl -ba scripts/Audit.lean | sed -n '1,175p'
```

Result: verified runner requirements and actual script behavior; broad output truncated.

```bash
nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-03-PLAN.md | sed -n '264,340p'; nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-04-PLAN.md | sed -n '128,208p'; nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-05-PLAN.md | sed -n '160,181p'
```

Result: confirmed allowlist/parser rules, issue CLI, and destructive input-lifetime conflict.

</details>

<details>
<summary>3. Issue authorization and caller-contract reads</summary>

```bash
nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-07-PLAN.md | sed -n '108,206p'; nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-09-PLAN.md | sed -n '166,237p'; nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-08-PLAN.md | sed -n '277,323p'
```

Result: confirmed approval scope, repeated live execution, and the mandated incorrect public error constructors.

```bash
nl -ba src/lib.rs | sed -n '116,150p;350,366p;414,454p'; nl -ba src/v1/unchunked/send_ek.rs | sed -n '137,177p'; nl -ba src/v1/unchunked/send_ct.rs | sed -n '97,119p'; nl -ba SrcTranslated/Types.lean | sed -n '714,726p;792,810p'; nl -ba SrcTranslated/Funs.lean | sed -n '10333,10350p;13236,13266p;11282,11310p'
```

Result: confirmed public error conversion, update-before-verification ordering, nested result types, and `NoHeaderReceived.send`.

```bash
nl -ba docs/spqr-properties.md | sed -n '1,80p;251,279p;322,351p;420,472p'; nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-09-PLAN.md | sed -n '176,207p'; nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-04-PLAN.md | sed -n '135,168p'; nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-03-PLAN.md | sed -n '324,334p'
```

Result: checked catalog context, DEV execution, CLI selection rules, and impossible literal-source acceptance checks.

</details>

<details>
<summary>4. Declaration inventory, callers, and ignored files</summary>

```bash
printf '%s\n' '--- declarations ---'; rg -n '^[[:space:]]*(axiom|opaque)\b' SrcTranslated Spqr -g '*.lean'; printf '%s\n' '--- builtin and namespace evidence ---'; nl -ba Spqr/Specs/Kdf/HkdfToSlice.lean | sed -n '15,33p'; nl -ba Spqr/Crypto/Hkdf.lean | sed -n '24,33p'; nl -ba scripts/Audit.lean | sed -n '21,33p;62,83p'; printf '%s\n' '--- phantom token and callers ---'; rg -n --hidden --glob '!.git/**' --glob '!.planning/**' --glob '!.verilib/**' 'check[_]no[_]sorry|check-lint\.sh' CLAUDE.md docs scripts .github lakefile.toml .gitignore; git config --get core.hooksPath; rg -n 'check-lint|check-gates' /home/lacra/.git-hooks; printf '%s\n' '--- ignored inputs ---'; git ls-files issues/; git check-ignore -v issues/create_issues.sh issues/SPQR_ISSUES_PREVIEW.md issues/272/README.md; rg --files --hidden --no-ignore issues; stat -c '%n %y %s bytes' sorry-manifest.txt; wc -l sorry-manifest.txt; nl -ba .gitignore
```

Result: enumerated declarations, verified namespaces and phantom-token locations, found no operative shim caller in the searched surfaces, confirmed three ignored legacy files and the August 7 manifest timestamp. Inventory display was truncated; counts were checked separately.

</details>

<details>
<summary>5. Pinned Lean output grammar and CI commands</summary>

```bash
nl -ba /home/lacra/.elan/toolchains/leanprover--lean4---v4.31.0/src/lean/Lean/Elab/Print.lean | sed -n '228,247p'; nl -ba /home/lacra/.elan/toolchains/leanprover--lean4---v4.31.0/src/lean/Lean/Message.lean | sed -n '409,422p'; nl -ba /home/lacra/.elan/toolchains/leanprover--lean4---v4.31.0/src/lean/Lean/Util/CollectAxioms.lean | sed -n '47,68p'; nl -ba .github/workflows/lean.yml | sed -n '40,90p'; nl -ba .github/workflows/sorry-delta-comment.yml | sed -n '25,58p'; nl -ba scripts/check-lint.sh
```

Result: confirmed report prefixes, multiline list formatting, opaque traversal, literal gate-1/2 parity, and CI’s distinct baseline/delta policy.

</details>

<details>
<summary>6. Roadmap authority, validation, and PR boundaries</summary>

```bash
nl -ba .planning/ROADMAP.md | sed -n '16,57p;90,126p'; nl -ba .planning/REQUIREMENTS.md | sed -n '8,48p'; nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-VALIDATION.md | sed -n '12,54p'; nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-CONTEXT.md | sed -n '20,38p;63,82p'; nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-RESEARCH.md | sed -n '1386,1430p;1443,1490p'; nl -ba .planning/STATE.md | sed -n '35,69p'
```

Result: checked requirements, assumptions, human rulings, and stale research claims; broad output truncated.

```bash
nl -ba .planning/ROADMAP.md | sed -n '57,76p'; nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-VALIDATION.md | sed -n '25,45p'; nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-07-PLAN.md | sed -n '259,300p;349,367p'; nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-09-PLAN.md | sed -n '250,279p'; nl -ba .planning/config.json | sed -n '1,44p'
```

Result: confirmed bare “full” invocation, late branch decision, non-PR-range diff commands, tracked-summary contradiction, and disabled automatic branching.

</details>

<details>
<summary>7. Executed negative interface probes and exact counts</summary>

```bash
gh --version; gh issue list --repo Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify --state all --limit 200 --search '"INFRA-01: issue template names the four real gates" in:title' --json number,title --jq --arg t 'INFRA-01: issue template names the four real gates' 'map(select(.title == $t)) | .[0].number // empty'; printf 'gh_exit=%s\n' "$?"; rg -nF 'spqr.kdf.hkdf_to_slice_spec' SrcTranslated/FunsExternal.lean Spqr/Specs/Kdf/HkdfToSlice.lean; printf 'qualified_name_grep_exit=%s\n' "$?"; bash -c "awk '/^## 11\./{f=1} /^## 12\./{f=0} f \&\& /^\| D[1-5] \| .* \| Provisional /' docs/spqr-properties.md | wc -l"; printf 'awk_pipeline_exit=%s\n' "$?"; for file in SrcTranslated/FunsExternal.lean SrcTranslated/TypesExternal.lean Spqr/Specs/Kdf/HkdfToSlice.lean Spqr/Crypto/Hkdf.lean; do printf '%s: ' "$file"; awk '/^[[:space:]]*(axiom|opaque)([[:space:]]|$)/ {counts[$1]++} END {for (kind in counts) printf "%s=%s ", kind, counts[kind]; print ""}' "$file"; done; git ls-tree origin/main scripts/check-gates.sh scripts/check-lint.sh; git worktree list; nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-08-PLAN.md | sed -n '158,169p'; nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-03-PLAN.md | sed -n '228,238p;423,430p'
```

Result: `gh_exit=1`; qualified-name literal search exit 1; awk syntax error followed by count 0 and pipeline exit 0; declaration counts 173+3+1 axioms and two opaques; only the old lint runner exists on `origin/main`; unrelated existing worktree recorded.

</details>

<details>
<summary>8. Restatements and concrete transition evidence</summary>

```bash
nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-08-PLAN.md | sed -n '180,247p'; nl -ba docs/spqr-properties.md | sed -n '280,297p;320,350p;390,449p'; nl -ba src/v1/chunked/states.rs | sed -n '275,296p;457,529p'; nl -ba SrcTranslated/Funs.lean | sed -n '13965,13987p'; nl -ba src/authenticator.rs | sed -n '39,60p'; git show main:Spqr/Specs/Authenticator/Authenticator/Update.lean | sed -n '40,55p'
```

Result: checked D1–D4 restatement targets, next-epoch exception, authenticator update, and the actual merged `update_spec` signature.

</details>

<details>
<summary>9. Authorization records, historical #272 claim, and branch-only axioms</summary>

```bash
nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-CONTEXT.md | sed -n '24,32p;65,79p'; nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-RESEARCH.md | sed -n '1386,1426p'; nl -ba scripts/sorry-diff.py | sed -n '118,195p'; nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-04-PLAN.md | sed -n '258,266p;316,325p'; nl -ba Spqr/Specs/Encoding/Polynomial/LagrangePolysForCompletePoints.lean | sed -n '43,62p'; git ls-tree -r --name-only la/lean-v1-protocol-proofs Spqr/Specs | rg '/(Send|Recv|External)\.lean$'; git show la/lean-v1-protocol-proofs:Spqr/Specs/External.lean | sed -n '1,110p'
```

Result: confirmed D-01/D-09/Q-1, explicit search-lag assumption, missing rendering columns, corrected current frame condition, and branch-only liveness axioms.

</details>

<details>
<summary>10. Final interface, template, imports, and requirement-edit checks</summary>

```bash
nl -ba scripts/sorry-diff.py; nl -ba docs/ISSUE_TEMPLATE.md | sed -n '108,127p'; nl -ba .planning/PROJECT.md | sed -n '36,54p;85,103p'; nl -ba Spqr.lean | sed -n '48,55p;68,73p;192,202p'; nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-04-PLAN.md | sed -n '258,266p'; nl -ba .planning/phases/01-gates-issues-and-deviation-decisions/01-02-PLAN.md | sed -n '103,135p'
```

Result: rechecked comparator behavior, label inventory, project context, existing imports, TSV schema, and bounded requirement edits.

</details>

<details>
<summary>Additional exact probes retained in the inherited handoff</summary>

```bash
git ls-files .planning issues
git rev-parse origin/main origin/la/spec-catalog
git diff --name-only origin/main..HEAD -- '*.lean' src SrcTranslated lean-toolchain lakefile.toml
git ls-tree origin/main scripts/check-gates.sh scripts/check-lint.sh docs/spqr-properties.md .gitignore
awk '/^[[:space:]]*(axiom|opaque)([[:space:]]|$)/ {counts[$1]++} END {for (kind in counts) print kind,counts[kind]}' SrcTranslated/FunsExternal.lean
rg -n '^\s*(axiom|opaque)\b' Spqr/Specs -g '*.lean'
command -v gsd-sdk gsd-tools
```

Retained results: planning files tracked; no Lean/source/toolchain differences from base; new phase outputs absent from `main` as expected; declaration counts agree with the re-verification. The SDK executable lookup did not establish an available command.

</details>

## Resolution map

| Finding | Suggested edit | Destination plan/section |
|---|---|---|
| F-1 | Correct public error constructor, distinguish internal errors, and stop rather than publish contradictory claims | 01-08 task 3; research D5; 01-09 note and issue bodies |
| F-2 | Replace search-dependent live retry tests with fail-closed identity lookup and nonmutating retry controls | 01-04 filing algorithm; 01-07 task 2; 01-09 task 2 |
| F-3 | Establish explicit approval for the four DEV writes and actual label changes | 01-07 approval scope; 01-09 before task-2 mutations |
| F-4 | Establish branch/base/tip transitions and verify full PR ranges including planning artifacts | Phase execution preconditions; 01-07/01-09 boundaries; 01-08 entry conditions |
| F-5 | Ensure legacy inputs are consumed before deletion | 01-04/01-05 dependencies and waves |
| F-6 | Correct the `gh` filter invocation and labels-only argument contract | 01-04 task 1; 01-07 task 2 |
| F-7 | Define strict full-run semantics and require fresh, cleanly sourced manifest evidence | 01-03 tasks 1–2; 01-06 baseline checks; 01-VALIDATION |
| F-8 | Parse complete multiline axiom reports and test continuation-line rejection | 01-03 gate 4; 01-06 negative controls |
| F-9 | Specify baseline runner deployment and compare matching SHAs and equivalent checks | 01-06 task 2; scripts README requirements |
| F-10 | Repair namespace-aware validation, contradictory cleanup predicates, and awk syntax | 01-03 acceptance criteria/threat table; 01-08 task-1 verification |
| F-11 | Expose full dry-run bodies and define all substitutions and placeholder checks | 01-04 rendering/interface; 01-07 human review; 01-09 body checks |
| F-12 | Refresh declaration counts, actual names, research pointers, and historical-defect labeling | 01-RESEARCH; 01-03/01-04/01-06 citations; 01-05 legacy-analysis handling |

---

# Planning-seat triage

Every finding was re-verified independently before any edit: cited `path:line`s were read in
the tree at `la/spec-catalog@d7cf202`, the concrete commands (`gh`, `awk`, `grep`) were
re-executed, and the Lean-output claim was checked against the **pinned toolchain source**
(`~/.elan/toolchains/leanprover--lean4---v4.31.0/src/lean/`). Lean elaboration probes were
*not* available to either engine — `.lake/build` does not exist, the tree is unbuilt (that is
what plan 01-06 exists to change) — so the `#print axioms` findings are grounded in the
formatter source, not in observed output. That limit is recorded in the plans themselves.

**All 12 findings were confirmed.** None was rejected as unverifiable.

## 1. Codex's review

**VERDICT: REJECT** — 1 BLOCKER, 10 MAJOR, 1 MINOR.

| # | Sev | Claim | My verification |
|---|-----|-------|-----------------|
| F-1 | BLOCKER | 01-08 commits the catalog to MAC errors the public API never returns | **CONFIRMED.** `spqr::Error` (`src/lib.rs:98-128`) has no `InvalidHdrMac`/`InvalidCtMac`; those are `authenticator::Error` variants (`src/authenticator.rs:13,15`), and `impl From<authenticator::Error> for Error` (`src/lib.rs:145-149`) collapses **every** one to `Error::MacVerifyFailed`. Codex's separate finding that the *asymmetry* claim (point 5) is sound also holds: I confirmed `auth.update` at `send_ek.rs:158` precedes `verify_ct` at `:160`, and `verify_hdr` at `send_ct.rs:107` precedes any state construction. All three D5 `path:line` citations are exact. |
| F-2 | MAJOR | The mandated back-to-back `--execute` test can itself create duplicates | **CONFIRMED.** RESEARCH A4 (`01-RESEARCH.md:1395`) says in as many words that a second run within seconds may re-file, and excuses it on a "minutes to days apart" cadence — which is precisely not the immediate re-run that 01-07 and 01-09 mandate. |
| F-3 | MAJOR | 01-09's four live DEV issue writes are never authorized | **CONFIRMED.** 01-07's only pre-filing checkpoint scopes approval to five PR A IDs (task 1 step 5); 01-09's task 2 was `type="auto"` and its first blocking checkpoint sat at line 231, *after* the writes. |
| F-4 | MAJOR | No branch-ownership or PR-range discipline keeps PR A and PR B separate | **CONFIRMED, partly a user ruling.** `branching_strategy: none`; a bare `git diff --stat` after commits reports nothing; the tracked `01-07-SUMMARY.md` contradicts "no repository file changes". Stale figure confirmed: 25 files / 7058 insertions, not 14 / 2229. The base-branch *decision* is the user's (see §3). |
| F-5 | MAJOR | A legal wave-2 order deletes 01-04's input before it is read | **CONFIRMED.** 01-04 reads `issues/create_issues.sh` for label colours; 01-05 deletes it; both wave 2, no mutual dependency, `parallelization: true`, and the file is gitignored+untracked so there is no recovery. |
| F-6 | MAJOR | A rejected `gh` invocation plus a contradictory `--execute` rule | **CONFIRMED, both halves.** I ran the prescribed command on `gh` 2.100.0: `unknown arguments ["t" …]` — `gh --jq` does not accept `jq`'s `--arg`. And 01-04 required `--execute` without IDs to fail while 01-07 required `--labels-only --execute` to succeed. |
| F-7 | MAJOR | Gate completion and baseline rules admit unverified evidence as a pass | **CONFIRMED (4 sub-claims).** Sharpest is the fifth: under inherited `set -euo pipefail`, a non-zero `lake build` kills the script before any `fail=1`, so gates 2–4 never run. Also: the cold-start rule contradicts itself on a cache miss; `test -f sorry-manifest.txt` is vacuous against the stale root manifest (2026-08-07, 14139 bytes, verified); `checkout --detach` does not make a reused worktree clean. |
| F-8 | MAJOR | Gate 4's line-based parser misses wrapped axiom lists | **CONFIRMED from pinned toolchain source.** `#print axioms` formats via `MessageData.ofList` (`Lean/Elab/Print.lean:244`), which joins with `"," ++ Format.line` (`Lean/Message.lean:414-417`). `Format.line` is a **soft** break — a newline past the print width. Long closures wrap; a line-oriented matcher then silently drops axioms. This is a false green in the one gate with no CI counterpart. |
| F-9 | MAJOR | The local-vs-CI check has no executable baseline deployment | **CONFIRMED.** `git ls-tree origin/main scripts/check-gates.sh` is empty — the script is new in this PR, so "run the script inside the baseline worktree" is infeasible as written. The semantic conflation is also real: `lean.yml:64-70` keys on the PR's actual base, and `sorry-delta-comment.yml` runs `sorry-diff.py` *without* `SORRY_FAIL_ON_NEW`, so CI reports a delta where the local gate fails on one. |
| F-10 | MAJOR | Four mandatory acceptance predicates cannot pass | **CONFIRMED, all four.** The `awk` in 01-08's `<verify>` carries markdown-escaped `\&\&` into `bash -c` → `awk: 1: unexpected character '\''`; `rm -rf` was asserted absent and mandated in the same plan; the allowlist loop's literal `grep -F 'spqr.kdf.hkdf_to_slice_spec'` exits **1** against the tree (namespace + bare declaration). |
| F-11 | MAJOR | The dry-run cannot show the bodies the plans' own checkpoints require | **CONFIRMED.** Bodies live under a trap-removed `mktemp -d`, so the advertised path is dead on return; `{PROP-ID}` escapes the `\{[A-Z_]+\}` guard (the `-` is outside the class — re-tested); `{LEAN_STATEMENT}` and `{APPROACH}` have no column in the eleven-column TSV. |
| F-12 | MINOR | Stale/inaccurate research citations | **CONFIRMED.** `FunsExternal.lean` holds **173 `axiom` + 1 `opaque`**, not 55. The declaration is `crypto.HMAC_SHA256` (`Spqr/Crypto/Hkdf.lean:27,30`), not `Spqr.Crypto.Hkdf.HMAC_SHA256` (a module path). The Q-5 pointer was off. And the #272 analysis is **historical**: `LagrangePolysForCompletePoints.lean:57` is `(ones1[i]!).y = (ones[i]!).y`, a preserved frame — the file has no `sorry`. Codex's judgement that none of this widens the allowlist is right; the 20-name count (3 builtins + 17 stubs) checks out exactly, and `spqr.kdf.hkdf_to_slice_spec` is the correct FQN. |

## 2. What I did in response

All twelve accepted. Edits are confined to the phase's own plan files, `01-RESEARCH.md` and
`01-VALIDATION.md`; no `src/`, no `SrcTranslated/`, no `*.lean`, no catalog, no ROADMAP.

**F-1 (BLOCKER) — `01-08-PLAN.md`, `01-RESEARCH.md`**
Rewrote caller-contract item 1 to state `Err(Error::MacVerifyFailed)` as the only public MAC
error, present `InvalidHdrMac`/`InvalidCtMac` as the two internal causes `src/lib.rs:145-149`
collapses into it, and require the catalog to say the two are **indistinguishable to a
caller** — the trap a Phase 5 AUTH-01 statement would otherwise fall into. Replaced the
"record the discrepancy rather than adjusting the claim" instruction with a **stop-and-correct**
rule that distinguishes citation drift (re-cite) from a wrong claim (rewrite), while keeping
the original rule's purpose of stopping an executor from silently *weakening* a statement.
Corrected the same error at its source in `01-RESEARCH.md:958`, with a dated correction note;
left the internal error names intact in the rows above it and at `docs/spqr-properties.md:282`,
where PROP-15 speaks at the authenticator level and they are correct. Updated 01-08's
acceptance criterion to assert `MacVerifyFailed` and the indistinguishability wording.

**F-2 + F-6 — `01-04-PLAN.md`, `01-07-PLAN.md`, `01-09-PLAN.md`**
One fix closes both: duplicate detection now **enumerates** `gh issue list --state all
--limit 500 --json number,title` once per run and matches titles client-side, instead of
querying the `in:title` index through an invalid `--jq --arg` command. That removes the broken
invocation *and* the index-lag window, which makes the mandated back-to-back idempotency test
sound rather than hazardous. Added fail-closed behaviour on a truncated enumeration (500 rows)
and on any lookup error — an unknown answer is never permission to create — and required the
residual limit (a hand-edited title is not recognised) to be stated in `--help`. Both re-run
steps now carry a `grep -q 'in:title' … exits 1` pre-check so the test cannot run against a
regressed script. Carved out the `--labels-only --execute` exception explicitly and required
the ID check to sit after that branch.

**F-3 — `01-09-PLAN.md`**
Inserted `Task 2a`, a `checkpoint:human-verify gate="blocking"` before the four live writes:
show the four IDs/titles/labels, show `--show-body DEV-01` in full so the user can see the
post-01-08 catalog text actually came through, state the repo slug and open-issue count, and
list which labels already exist and would therefore be *modified* by `--force` (01-07 has
created them by then, so its "none exists today" note is stale at this point). Filing is now
`Task 2b`.

**F-4 — `01-07-PLAN.md`**
Replaced the bare `git diff --stat` with `git diff --stat <base>...HEAD` and explained why the
bare form reports nothing after commits. Replaced the stale 14/2229 figure with a
re-measure-and-date instruction plus today's 25/7058, and kept the substantive B-4 finding
(no `docs/spqr-properties.md`, no `.planning/` on `origin/main`; zero Lean/toolchain diff —
I re-verified all three). Corrected "No repository file changes" to acknowledge that the
tracked `01-07-SUMMARY.md` is real PR scope under `commit_docs: true`. Added the two branch
questions to the user-action block and required PR A's tip SHA to be recorded.

**F-5 — `01-05-PLAN.md`**
`depends_on: ["01-03", "01-04"]`, plus an `<ordering_constraint>` block explaining that the
input is gitignored and untracked so there is no recovery, and requiring
`scripts/property-issue-labels.tsv` to exist before the deletion.

**F-7 — `01-03-PLAN.md`, `01-VALIDATION.md`**
Required each gate's pipeline to be run so its failure is captured rather than fatal
(`if ! <pipeline>`, or `PIPESTATUS`), with the exit status in the verdict line and without
dropping `set -e` wholesale. Gate 3a now marks the manifest's mtime before `lake env lean`
and asserts freshness, rather than `test -f` against the stale artifact. Resolved the
cold-start contradiction in favour of *building* on a cache miss, and confined `SKIPPED` to
two named cases. Added an `ALL GATES PASSED` vs `PASSED WITH SKIPS: …` distinction, and made
`01-VALIDATION.md`'s boundary check the targeted full run rather than the bare runner, which
skips gate 4 by design. Required a reused worktree to be clean and at `$BASE_SHA`.

**F-8 — `01-03-PLAN.md`, `01-06-PLAN.md`, `01-VALIDATION.md`**
Gate 4 must now parse each report as a region from `depends on axioms: [` through its matching
`]`, accumulate continuation lines, normalise whitespace, and **fail** on a malformed report —
with the `Format.line` soft-break mechanism cited so the constraint survives a rewrite. A1 may
no longer be marked verified on a single-line report. Added negative control **row 7** to both
01-06 and `01-VALIDATION.md`: produce a genuinely wrapped list, confirm from the raw log that
it wrapped, drop a **continuation-line** axiom from the allowlist, and require a FAIL — with
an explicit "record A1 as partially verified" escape if no wrapping target exists. Updated the
six-row counts to seven throughout.

**F-9 — `01-06-PLAN.md`, `01-VALIDATION.md`**
Specified the arrangement: invoke the working tree's script by absolute path with the baseline
worktree as CWD, resolve the allowlist from `$(dirname "$0")` (not CWD, not
`--show-toplevel`), record the directory provenance of script/allowlist/lakefile/sources, and
**stop and report** rather than copying the script into the baseline — an overlay would
invalidate the comparison. Required the CI run's `headSha` to equal the locally audited SHA.
Split the comparison table's semantics: gates 1–2 directly comparable, gate 3b labelled
`local policy, stricter than CI`, gate 4 `n/a (no CI step)`; `agree: yes` is forbidden for a
check CI does not perform.

**F-10 — `01-03-PLAN.md`, `01-08-PLAN.md`**
Rewrote the awk predicate as `test "$(awk … | wc -l)" -eq 5` without the escaped `&&`, so it
parses and no longer hides awk's failure behind a pipeline exit (re-tested: parses, returns 0
now, will return 5 after 01-08 runs). Reconciled `rm -rf`: the single permitted occurrence is
the `mktemp -d` scratch trap, asserted never to reference a worktree, cache or repo path.
Replaced the allowlist source-existence loop with a namespace-aware, comment-stripping check,
spelled out for both the root-scope `FunsExternal.lean` entries and the `spqr.kdf.`-prefixed
one.

**F-11 — `01-04-PLAN.md`, `01-07-PLAN.md`, `01-VALIDATION.md`**
Added a non-mutating `--show-body <ID>…` mode printing to stdout, and removed the promise to
print a trap-removed body path. Routed 01-07's pre-authorization review, 01-09's new
checkpoint and the validation-table row through it. Widened the placeholder guard to
`\{[A-Z_][A-Z0-9_-]*\}` and added a positive check that derives the template's placeholder set
so a newly added placeholder cannot slip through. Defined truthful fixed values for
`{LEAN_STATEMENT}` and `{APPROACH}` (these are infrastructure/decision rows, not Lean
properties) with a note to add real columns when a property issue is first filed.

**F-12 — `01-RESEARCH.md`, `01-03-PLAN.md`, `01-04-PLAN.md`, `01-05-PLAN.md`, `01-06-PLAN.md`**
Corrected the declaration inventory to 173 `axiom` + 1 `opaque`, with a note that the
allowlist is deliberately much smaller (17 stubs, so a prost or `core.*` axiom fails gate 4 by
design). Corrected `crypto.HMAC_SHA256` in all three places, including the conditional
allowlist addition in 01-06 that would otherwise have added a dead entry. Fixed the
`opaque hkdf_to_slice` location (`FunsExternal.lean:3669`, not the specs file) and the Q-5
line pointer. Added a dated correction to research Q-3 and to 01-05's `read_first` and
`<context>` recording that the #272 analysis is **historical** — which reframes that blocking
decision from "preserve live analysis" to "archive a record of a defect since addressed".

## 3. What I deliberately did NOT do

- **The base-branch and branch-ownership decisions (F-4).** `origin/main` carries no
  `docs/spqr-properties.md` and no `.planning/` at all, so PR A's base, whether PR A gets its
  own branch, and where PR B branches from are contract-level calls that are yours. I made the
  plan *ask* them concretely and pin PR A's tip SHA; I did not choose. Nothing in the plans
  pushes a branch or runs `gh pr` — I re-checked, and that prohibition survives intact.
- **Codex's heavier remedy for F-2** (a non-mutating fake `gh` harness, full reconciliation
  after uncertain outcomes, explicit disclaimers about concurrent atomicity). Full enumeration
  plus fail-closed lookup removes the actual defect; a fake-`gh` test harness is a
  disproportionate build for a nine-row script that files thirteen issues once. Non-binding
  and recorded here if you want it.
- **Re-planning the phase.** Every finding turned out to be a bounded edit to a plan's text.
  The phase decomposition survived review: nine plans, five waves, two PR boundaries, and
  decisions D-01..D-17 are all in Codex's cleared surfaces, as is the 20-name allowlist and
  the `spqr.kdf.hkdf_to_slice_spec` FQN. Routing back to `/gsd-plan-phase 1` would discard
  work that the review found sound.
- **Changing `docs/spqr-properties.md`.** The catalog is PR B's deliverable (plan 01-08); the
  F-1 correction lands as corrected *plan* text that 01-08 will write, not as a pre-emptive
  catalog edit. `docs/spqr-properties.md:282` (PROP-15) was checked and is correct as it
  stands — the internal MAC error names belong at the authenticator level.
- **Marking A1/A2 settled.** Neither engine could elaborate Lean: the tree is unbuilt. The
  `#print axioms` findings rest on the pinned formatter source. Plan 01-06's empirical probe
  remains the only thing that can close them, and it now has to produce a wrapped list to do so.
- **`scripts/sorry-diff.py` and `scripts/Audit.lean`.** Codex correctly notes
  `sorry-diff.py:105` treats a missing baseline as "no comparison" rather than failure. That
  is CI's contract and D-08 forbids touching either file; the fix belongs in the caller, which
  is where I put it.

## 4. Route

**REJECT stands for this revision of the plan set.** Per the skill's routing rule, a REJECT
requires a fresh review of the revised plans rather than direct dispatch to execution: the
next artifact is `01-CODEX-REVIEW-2.md`, from `/spqr-plan-review 1` re-run on the edited set.
The BLOCKER and all ten MAJORs have bounded fixes applied above; what the second pass needs to
confirm is that the fixes are right and that none introduced a new inconsistency — in
particular the gate-4 bracket parser (F-8), the enumeration-based duplicate detection
(F-2/F-6) and the 01-05 wave-2 reordering (F-5), none of which existed in the reviewed text.

The two base-branch questions in §3 are yours and do not block a re-review.
