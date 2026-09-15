---
phase: 01-gates-provenance-and-target-list
plan: 03
subsystem: docs
tags: [provenance, catalog, prov-01, gate-5, citations, mlkem-braid, scka]

requires:
  - phase: 01-02
    provides: scripts/check-provenance.py (gate 5) and scripts/check-gates.sh, which define the Source: grammar this plan writes against
provides:
  - docs/spec-sections.txt - all 23 ML-KEM Braid Rev. 1 section numbers, transcribed from the PDF table of contents; gate 5's membership set for `Spec §x.y`
  - docs/scka-refs.txt - SCKA Def. 2.1/2.2/2.3/3.1/3.3 and Fig. 1-23; gate 5's membership set for `SCKA Def./Fig. n`
  - docs/spqr-properties.md - a resolving `Source:` citation on all 42 registry rows, plus a PROV-01 paragraph in section 1
affects: [01-04 (gate 5 is now green and stays green in the five-gate run), 01-05 (criterion 2 met, no known-red gate to report from this plan), 01-06 (every row's C2 verdict now has a citation to adjudicate), 01-07 (new rows must carry a Source: or the gate turns red), 01-08 (D1-D5 rows now cite both grounds)]

tech-stack:
  added: []
  patterns:
    - "Provenance lives in a machine-checkable field, not in a section heading: every row's ground is a `Source:` line or table column that gate 5 resolves"
    - "Reference lists are transcribed, never remembered: each `.txt` header records the document, its revision, the `pdftotext` command and the transcription date"
    - "The gate's membership set is the checkable proxy for a gitignored PDF"
    - "Braid-spec figures have no citation form; a figure is cited through its enclosing section"

key-files:
  created:
    - docs/spec-sections.txt
    - docs/scka-refs.txt
  modified:
    - docs/spqr-properties.md

key-decisions:
  - "Zero rows ended `Unsourced`. Every one of the 42 registry rows resolved to a spec section, an SCKA definition, verified `src/` lines, or a combination. Gate 5 went from 42 citation failures to PASS, so criterion 2 has no residue for plan 01-05 to report as known-red."
  - "PROP-50's `Fig. 2` is the ML-KEM Braid document's Figure 2 (the reachable state-pair graph inside §2.6), NOT SCKA Fig. 2 (an SM protocol from an SCKA). Citing `SCKA Fig. 2` here would have been a fabricated citation that passed the gate. PROP-50 cites `Spec §2.6` instead, and the new §1 paragraph records the general rule: a braid-spec figure is cited through the section that contains it."
  - "§10's rows keep code-only citations, per the section's own preamble (\"properties here are grounded in the code\"). §11's deviation rows cite both grounds, because a deviation *is* a spec-versus-code claim and needs the spec side to be resolvable."
  - "§10's `Code` column was renamed to `Source` and its cells rewritten to full `src/`-rooted paths; §11 gained a new trailing `Source` column. Neither table's Statement/Where/Spec/Code/Impact/Status cells changed - verified cell-by-cell against `git show HEAD:docs/spqr-properties.md`."
  - "PROP-25 is spec-grounded, not code-only: §2.5's `Ct1Sampled.Receive` pseudocode contains `if SHA3-256(state.ek_seed || ek_vector) != state.hek: raise Error(\"EK integrity check failed\")`. Read out of the PDF before citing."
  - "Where a row's own prose already gave line numbers, the `Source:` field mirrors them exactly rather than 'improving' them, so the citation and the statement cannot drift apart."
  - "Lean paths (`Spqr/Specs/**`) went on `Evidence:` lines for the four rows that carried them inline (LEAN-ENC-1, LEAN-ENC-2, LEAN-GF, PROP-35, PROP-42). The checker records but does not gate them."

metrics:
  duration: ~35 min
  tasks_completed: 3 of 3 (task 3's blocking human-verify checkpoint closed by the user's "no unsourced rows, proceed", 2026-09-15)
  completed: 2026-09-15
  files_created: 2
  files_modified: 1
  rows_cited: 42
  unsourced_rows: 0
---

# Phase 01 Plan 03: Catalog provenance retrofit Summary

All 42 registry rows of `docs/spqr-properties.md` now carry a `Source:` citation that
gate 5 resolves, backed by two reference lists transcribed from the ML-KEM Braid PDF and
the SCKA paper; gate 5 went from 42 citation failures to PASS with no `Unsourced` row and
no statement text touched.

## Worktree base

HEAD was spawned on `main` and was repointed, before any other action, to
`19c3ad2672dd3a6be443658f5fbaf2e8da7c847f` (`docs(phase-01): update tracking after wave 1`)
with `git checkout -B worktree-agent-a3a8cb1fc733ba241 19c3ad2`. Confirmed: both commits of
this plan are based on `19c3ad2`, which already contains wave 1 (01-01's honest
ISSUE_TEMPLATE/rubric/CLAUDE.md edits and 01-02's five-gate runner).

## Task 1: the two reference lists

`docs/spec-sections.txt` and `docs/scka-refs.txt`. Both PDFs were read from
`/tmp/props-review/` — paths **outside** the repository — and no PDF was added to the tree
(`docs/*.pdf` is gitignored and absent from the worktree). `git status --porcelain` after
the commit is clean apart from the intended files.

### Commands, paths and page ranges used

| Purpose | Command | PDF path | Pages |
|---------|---------|----------|-------|
| ML-KEM Braid table of contents | `pdftotext -f 1 -l 3 /tmp/props-review/mlkembraid.pdf -` | `/tmp/props-review/mlkembraid.pdf` | 1-3 (Contents spans printed pages 1-2) |
| ML-KEM Braid cross-check against body headings | `pdftotext /tmp/props-review/mlkembraid.pdf - \| grep -nE '^[0-9]+(\.[0-9]+)*\.?[[:space:]]+[A-Z]'` | same | all |
| SCKA numbered environments | `pdftotext /tmp/props-review/2025-2267.pdf - > /tmp/scka.txt` then `grep -noE '(Definition\|Theorem\|Lemma\|Corollary\|Figure\|Construction\|Proposition\|Remark\|Claim\|Table\|Protocol\|Game)[[:space:]]+[0-9]+(\.[0-9]+)*' /tmp/scka.txt \| sed 's/^[0-9]*://' \| sort -u -V` | `/tmp/props-review/2025-2267.pdf` | all |

`pdftotext` is `/usr/bin/pdftotext`. Both commands wrote to stdout or to `/tmp`, never into
the repository. `acd19.pdf` was not opened.

Identification read off the documents themselves:

- `mlkembraid.pdf` title page: "The ML-KEM Braid Protocol / Rolfe Schmidt / Revision 1 ,
  2025-02-21 / Last updated: 2025-09-26" — matches the catalog's References block.
- `2025-2267.pdf` title page: "How to Compare Bandwidth Constrained Two-Party Secure
  Messaging Protocols: A Quest for A More Efficient and Secure Post-Quantum Protocol",
  Auerbach (PQShield), Dodis (NYU), Jost (Blanqet), Katsumata (PQShield/AIST), Schmidt
  (Signal Messenger) — matches.

### What was transcribed

`docs/spec-sections.txt` — 23 entries, the complete numbered structure: 1, 1.1, 1.2, 1.2.1,
1.3, 2, 2.1, 2.2, 2.3, 2.4, 2.5, 2.6, 3, 3.1-3.8, 4, 5. The table of contents and the body
headings agree exactly: no numbered heading appears in one and not the other. The named
subheadings under §2.4 ("Ratcheted Authenticator state variables/functions") and the eleven
state names under §2.5 carry no number, so they have no entry.

`docs/scka-refs.txt` — 28 entries: `Def. 2.1`, `Def. 2.2`, `Def. 2.3`, `Def. 3.1`,
`Def. 3.3`, and `Fig. 1` through `Fig. 23`. The enumeration also found Theorem 3.4 and
Remarks 3.2 and 3.5; PROV-01 has no citation form for either, so they are recorded in the
file's header comment rather than listed as entries. The paper numbers no lemma, corollary,
proposition, claim or table.

Both acceptance greps pass: the catalog's already-cited sections (1.1, 1.2, 2.2, 2.3, 2.4,
2.5, 2.6, 3.6, 3.8) are all present, `Def. 3.1`, `Fig. 1`, `Fig. 2` and `Fig. 16` are all
present, and `grep -vcE '^#|^$|^[0-9.]+$' docs/spec-sections.txt` returns 0.

## Task 2: a resolving Source: on every row

### Gate 5, before and after

Measured with `bash scripts/check-gates.sh --gates 5` (gate 5 needs no `lake`).

| | Registry entries | §12 index rows | Structural failures | Citation failures | Verdict |
|---|---|---|---|---|---|
| **Before** (at `19c3ad2`) | 42 (37 non-deviation, 5 deviation) | 38 (37 individual, 1 aggregate) | 0 | 42 — every row "no `Source:` field" | `GATE 5 FAIL`, exit 1 |
| **After** | 42 (37 non-deviation, 5 deviation) | 38 (37 individual, 1 aggregate) | 0 | 0 | `GATE 5 PASS: every one of 42 row(s) has a resolving Source: citation.`, exit 0 |

ID-set agreement with the §12 index held before and after (0 structural failures); the two
counts are 42 and 38 and are not expected to be equal, because §12 collapses D1-D5 into one
aggregate row.

Gates 1-4 were not run: they need a real `lake` build, which is plan 01-04's job in wave 3.
This plan touched zero `*.lean`, zero `src/` and zero `SrcTranslated/` files, so it cannot
have moved them.

### Per-row verdict, from the checker

`python3 scripts/check-provenance.py --verbose` — all 42 rows `PASS`. The citation read back
for each row:

| ID | Source (as the checker parsed it) |
|----|-----------------------------------|
| PROP-1 | `Spec §1.1; SCKA Def. 3.1` |
| PROP-21 | `Spec §1.1; src/v1/chunked/states.rs:203-220; src/v1/chunked/states.rs:361-368` |
| PROP-22 | `Spec §1.1; src/lib.rs:300; src/lib.rs:427` |
| PROP-23 | `Spec §1.1; src/lib.rs:298; src/lib.rs:430` |
| PROP-3 | `Spec §1.2; src/incremental_mlkem768.rs:34-156` |
| PROP-3b | `Spec §1.2.1; src/incremental_mlkem768.rs:28-30` |
| LEAN-ENC-1 | `src/encoding/polynomial.rs:26-44` |
| LEAN-ENC-2 | `Spec §3.6; src/encoding/polynomial.rs:905-911` |
| LEAN-GF | `Spec §2.2; src/encoding/gf.rs:16-196` |
| PROP-45 | `Spec §2.2; src/incremental_mlkem768.rs:8-15` |
| PROP-24 | `Spec §2.2; src/v1/unchunked/send_ct.rs:129-135; src/v1/unchunked/send_ek.rs:150-158` |
| PROP-42 | `Spec §2.2; src/authenticator.rs:43-54` |
| PROP-18 | `Spec §2.2; src/authenticator.rs:51; src/v1/unchunked/send_ct.rs:135; src/v1/unchunked/send_ek.rs:156; src/chain.rs:232; src/chain.rs:331; src/chain.rs:357` |
| PROP-41 | `Spec §2.2; src/authenticator.rs:47; src/authenticator.rs:68; src/authenticator.rs:93; src/v1/unchunked/send_ct.rs:131; src/v1/unchunked/send_ek.rs:152` |
| PROP-35 | `Spec §2.3; src/v1/chunked/states/serialize.rs:221; src/v1/chunked/states/serialize.rs:248` |
| PROP-36 | `src/v1/chunked/states/serialize.rs:254-256; src/lib.rs:427` |
| PROP-31 | `Spec §2.4; src/authenticator.rs:34-41` |
| PROP-40 | `Spec §2.4; src/authenticator.rs:66-105; src/v1/unchunked/send_ct.rs:192-193; src/v1/unchunked/send_ek.rs:160` |
| PROP-15 | `Spec §2.4; src/authenticator.rs:57; src/authenticator.rs:82; src/util.rs:25-33` |
| PROP-43 | `Spec §2.4; src/v1/unchunked/send_ct.rs:107; src/v1/unchunked/send_ek.rs:160; src/lib.rs:356-425` |
| PROP-30 | `Spec §2.5; src/v1/chunked/states.rs:275-532` |
| PROP-47 | `Spec §2.5; src/v1/chunked/states.rs:115-532` |
| PROP-50 | `Spec §2.6; src/v1/chunked/states.rs:115-532` |
| PROP-25 | `Spec §2.5; src/v1/unchunked/send_ct.rs:160-169` |
| PROP-48 | `Spec §2.2; src/v1/chunked/send_ct.rs:72-73; src/v1/chunked/send_ct.rs:96; src/v1/chunked/send_ek.rs:86; src/v1/chunked/send_ek.rs:170-171; src/v1/chunked/send_ek.rs:208-209` |
| PROP-49 | `Spec §2.5; src/v1/unchunked/send_ek.rs:163-166` |
| PROP-27 | `Spec §2.6; src/lib.rs:198-209; src/v1/unchunked/send_ek.rs:78-79; src/v1/unchunked/send_ct.rs:94-95` |
| PROP-16 | `src/lib.rs:373-389` |
| PROP-9 | `src/chain.rs:350-368` |
| PROP-14 | `src/chain.rs:384-387` |
| PROP-17 | `src/chain.rs:247-260` |
| PROP-29 | `src/chain.rs:372-382` |
| PROP-10 | `src/chain.rs:389-399; src/chain.rs:314; src/chain.rs:145-168; src/chain.rs:200` |
| PROP-12a | `src/chain.rs:130-210` |
| PROP-12b | `src/chain.rs:184-210` |
| PROP-37 | `src/v1/chunked/states/serialize.rs:12-49; src/v1/chunked/send_ek/serialize.rs:10-112; src/v1/chunked/send_ct/serialize.rs:11-151` |
| PROP-38 | `src/chain.rs:414-452` |
| D1 | `Spec §2.2; src/authenticator.rs:43-54` |
| D2 | `Spec §2.5; src/v1/chunked/states.rs:275-532` |
| D3 | `Spec §2.3; Spec §2.5; src/v1/chunked/states.rs:182; src/v1/chunked/states.rs:464-467` |
| D4 | `Spec §2.5; src/v1/chunked/states.rs:484-492` |
| D5 | `Spec §2.4; src/v1/unchunked/send_ct.rs:107; src/v1/unchunked/send_ek.rs:160` |

Breakdown: 29 rows cite a spec section **and** code, 12 cite code only (all of §10, plus
PROP-36, PROP-16, LEAN-ENC-1), and 1 (PROP-1) cites the spec and SCKA with no code — it is
a cross-party statement with no single implementing site.

`Evidence:` lines (recorded, not gated) were added for the five rows that carried a Lean
path inline: LEAN-ENC-1, LEAN-ENC-2, LEAN-GF, PROP-35, PROP-42.

### Every src/ citation resolves

The checker resolves 107 citations in total across the 42 rows: 75 `src/`, 31 `Spec §` and
1 `SCKA`. All 75 `src/` citations were checked, and each was also **read** to confirm it points at the
construct the row names — not merely that the line number is in range. No citation failed
to resolve and none needed correcting. Spot record:

| Citation | What is actually there |
|----------|------------------------|
| `src/v1/chunked/states.rs:203-220` | the `HeaderReceived` send arm, `send_ct1_chunk`, `key: Some(epoch_secret)` (transition 7) |
| `src/v1/chunked/states.rs:361-368` | `EkSentCt1Received` `recv_ct2_chunk` Done arm, `key = Some(sec)` (transition 5) |
| `src/v1/chunked/states.rs:115` / `:275` | `fn send` / `fn recv`; `send` spans 115-273, `recv` spans 275-532 |
| `src/authenticator.rs:47/51` | the `:Authenticator Update` label; `hkdf_to_vec(..., 64)` |
| `src/authenticator.rs:57` / `:82` | `verify_ct` / `verify_hdr` |
| `src/authenticator.rs:68` / `:93` | the `:ciphertext` / `:ekheader` labels |
| `src/v1/unchunked/send_ct.rs:131/135` | the `:SCKA Key` label; `hkdf_to_vec(..., 32)` |
| `src/v1/unchunked/send_ek.rs:152/156/160` | the `:SCKA Key` label; `hkdf_to_vec(..., 32)`; `auth.verify_ct(...)?` |
| `src/v1/unchunked/send_ek.rs:163-166` | `NoHeaderReceived { epoch: epoch + 1, auth }` (PROP-49's pre-increment claim) |
| `src/v1/chunked/states/serialize.rs:221/248/254-256` | `fn serialize`; `fn deserialize`; `if epoch == 0 { return Err(Error::MsgDecode); }` |
| `src/lib.rs:373-389` | exactly the version-negotiation block (`VersionMismatch`, `MinimumVersion`) |
| `src/chain.rs:130/247/350/372/384` | `KEY_SIZE = 4 + 32`; `fn key`; `fn add_epoch`; `fn epoch_idx`; `fn send_key` |
| `src/v1/chunked/states.rs:182` / `:464-467` / `:484-492` | `MessagePayload::Ct1Ack(true)` (D3 send); the `Ct1Ack(true) \| EkCt1Ack(_)` match (D3 recv); the out-of-order `Ek` acceptance and its comment (D4) |

`src/` itself was not touched: `git status --porcelain -- src SrcTranslated '*.lean'` is
empty, so the `d47083c` line numbers still hold.

### No statement was edited

`git diff docs/spqr-properties.md` on the working tree before commit: **104 insertions, 18
deletions**. Every one of the 18 deletions is a table line, accounted for individually:

| Deleted lines | What they are |
|---------------|---------------|
| 2 | §10's header + separator (`Code` → `Source`) |
| 9 | §10's nine data rows, re-added with only the `Code`/`Source` cell rewritten |
| 2 | §11's header + separator (a `Source` column appended) |
| 5 | §11's five data rows, re-added with only a trailing `Source` cell appended |

No prose line was deleted, so no statement sentence was deleted. This was also checked
mechanically, not just by eye: a cell-by-cell comparison of every pipe-table row against
`git show HEAD:docs/spqr-properties.md` (49 rows: 9 in §10, 5 in §11, 35 in §12) reported
**0** changes to any non-`Source` cell, and the §12 index is byte-identical with the same 38
rows.

The 104 insertions account exactly: a 24-line PROV-01 block in §1 (21 non-blank), 28
`Source:` lines and 5 `Evidence:` lines in the prose sections §2-§9, the 18 re-added table
lines, and 32 blank separator lines. 21 + 28 + 5 + 18 + 32 = 104.

## Task 3: checkpoint — closed

`checkpoint:human-verify`, `gate="blocking"`. Presented to the user with the two tables and
the `git diff --stat` below; the user ruled **"no unsourced rows, proceed"** on 2026-09-15.
Verbatim record and what it covers are in subsection 3.

### 1. Unsourced rows

**None.** All 42 registry rows resolved. Gate 5 is green, so plan 01-05 has no known-red
gate to report from this plan and ROADMAP criterion 2 is met with no residue.

One row came close and is worth the user's eye even though it is not `Unsourced`:

- **PROP-1** is the only row with no code citation. It is a cross-party statement ("if both
  parties output `(t, K)` and `(t, K')` then `K = K'`") with no single implementing site, so
  it cites `Spec §1.1; SCKA Def. 3.1`. A reviewer who wants a code ground here would have to
  pick the two KDF_OK sites, which are PROP-24's, not PROP-1's.

### 2. Rows cited to both a spec section and code — suggested spot-checks

29 rows carry both grounds. Three suggested for the sample, each read out of the PDF during
execution:

| Row | Source | What the spec section says, verified against the PDF |
|-----|--------|------------------------------------------------------|
| PROP-25 | `Spec §2.5; src/v1/unchunked/send_ct.rs:160-169` | §2.5's `Ct1Sampled.Receive` pseudocode contains `# Verify ek_vector integrity` / `if SHA3-256(state.ek_seed \|\| ek_vector) != state.hek: raise Error("EK integrity check failed")` before `KEM.Encaps2`. The code checks `ek_matches_header(&ek, &self.hdr)` and returns `Err(Error::ErroneousDataReceived)` otherwise. The row's "checked before `ek` is used" is the spec's order. |
| PROP-24 | `Spec §2.2; src/v1/unchunked/send_ct.rs:129-135; src/v1/unchunked/send_ek.rs:150-158` | §2.2 defines `KDF_OK(shared_secret, epoch)` = 32 bytes of HKDF with IKM = shared_secret, salt = a zero-filled sequence of hash-output length, info = `PROTOCOL_INFO \|\| ":SCKA Key" \|\| ToBytes(epoch)`, length 32. Both code sites call `hkdf_to_vec(&[0u8; 32], &ss, &info, 32)` with the `Signal_PQCKA_V1_MLKEM768:SCKA Key` label and big-endian epoch. |
| D1 | `Spec §2.2; src/authenticator.rs:43-54` | §2.2 defines `KDF_AUTH(root_key, update_key, epoch)` with **HKDF salt = root_key, IKM = update_key**. The code at `:45-51` computes `ikm = root_key ‖ k` and passes `salt = [0u8; 32]`. The deviation the row records is exactly the difference, and the spec side of it is resolvable. |

### 3. The user's ruling — checkpoint closed

Ruling, verbatim, 2026-09-15:

> no unsourced rows, proceed

It covers both halves of what task 3 asked:

1. **The `Unsourced` table.** There was nothing to adjudicate — zero rows ended `Unsourced`,
   so no row needs a C2 verdict carried into plan 01-06 on this account.
2. **The citation spot-check and the no-statement-text-changed check.** Both accepted.

Independently verified by the orchestrator in this worktree before the ruling was presented,
and recorded here as confirmed:

- Gate 5 re-run: `GATE 5 PASS: every one of 42 row(s) has a resolving Source: citation.`,
  exit 0.
- All 18 catalog deletions read line by line: exactly four table header/separator lines
  (§10's `Code` → `Source`, §11 gaining a `Source` column) plus nine §10 and five §11 data
  rows, each replaced by the same row re-columned. PROP-9's and PROP-37's statement cells are
  byte-identical; the only changes in those cells' row are the `src/` prefix PROV-01 requires
  and PROP-37's `chunked/{send_ek,send_ct}/serialize.rs` glob resolving to three real line
  ranges.
- The PROP-50 finding (threat T-1-06: `SCKA Fig. 2` would have resolved against the wrong
  document; the reachable-state-pair graph is the braid document's Figure 2 inside §2.6) was
  accepted as-is, including the new §1 rule that a braid-spec figure is cited through its
  enclosing section.

### 4. `git diff --stat` for the plan

```
 docs/scka-refs.txt      |  56 ++++++++++++
 docs/spec-sections.txt  |  50 +++++++++++
 docs/spqr-properties.md | 122 ++++++++++++++++++++++++-------
 3 files changed, 210 insertions(+), 18 deletions(-)
```

## Deviations from Plan

### Auto-fixed issues

**1. [Rule 1 - Bug] PROP-50's "Fig. 2" is not SCKA Fig. 2**

- **Found during:** Task 2, while choosing PROP-50's citation
- **Issue:** PROP-50's statement cites "§2.6: ... ; Fig. 2 gives the reachable pairs". Read
  as an SCKA reference — the only figure form PROV-01 has — this would have become
  `SCKA Fig. 2`, which resolves against `docs/scka-refs.txt` and would have made gate 5
  green on a citation pointing at the wrong document. SCKA Fig. 2 is "An SM protocol based
  on an SCKA protocol with slack ∆Slack"; the reachable-state-pair graph is the **ML-KEM
  Braid** document's Figure 2, captioned "The graph of all possible state transitions for
  Alice and Bob", inside §2.6.
- **Fix:** PROP-50 cites `Spec §2.6`. The new §1 PROV-01 paragraph states the general rule:
  braid-spec figures have no citation form of their own and are cited through the section
  containing them. This is threat T-1-06 firing in practice.
- **Files modified:** `docs/spqr-properties.md`, `docs/scka-refs.txt` (header note)
- **Commit:** `c78cf8b`

**2. [Rule 2 - Missing critical functionality] `Evidence:` lines for the five Lean-cited rows**

- **Found during:** Task 2
- **Issue:** LEAN-ENC-1, LEAN-ENC-2, LEAN-GF, PROP-35 and PROP-42 name `Spqr/Specs/**` paths
  in their prose. A `Spqr/Specs` path in a `Source:` field is an unparseable citation and a
  gate failure, and the next editor's natural move is to put it there.
- **Fix:** added `Evidence:` lines carrying those paths, which the checker records and does
  not gate — the mechanism PROV-01 provides for exactly this.
- **Files modified:** `docs/spqr-properties.md`
- **Commit:** `c78cf8b`

**3. [Rule 2 - Missing critical functionality] PROP-36 given a second code citation**

- **Found during:** Task 2
- **Issue:** PROP-36's point is that rejecting wire epoch 0 is what keeps `msg.epoch - 1` in
  `lib.rs` from underflowing. Citing only the rejection site leaves the consequence
  ungrounded.
- **Fix:** cites `src/v1/chunked/states/serialize.rs:254-256; src/lib.rs:427`. No spec
  citation: §2.3 says the epoch field is the "current epoch being negotiated" and says
  nothing about rejecting 0, so this row is genuinely code-grounded.
- **Files modified:** `docs/spqr-properties.md`
- **Commit:** `c78cf8b`

### Notes, not deviations

- `docs/spec-sections.txt` and `docs/scka-refs.txt` are 50 and 56 lines against the plan's
  `min_lines: 20` / `5`, because each carries a header recording the document, the command
  and the transcription date. Entry counts are 23 and 28.
- The plan's `min_lines: 20` for `spec-sections.txt` is satisfied by entries alone (23).

## Authentication gates

None.

## Known Stubs

None. This plan created no code and no stub; it added two data files and citations.

## Threat Flags

None. No network endpoint, auth path, file-access pattern or schema at a trust boundary was
introduced: the plan added two `.txt` reference lists and edited one Markdown document.

The threat register's three entries for this plan all have `mitigate` dispositions and are
discharged as follows.

| Threat ID | How it is discharged |
|-----------|----------------------|
| T-1-06 (a fabricated citation that makes gate 5 green) | Every Spec/SCKA citation is a member of a list transcribed from its PDF with the command recorded in the file header; every `src/` citation was resolved *and* read. The threat fired once for real — PROP-50's Fig. 2 — and was caught (deviation 1). |
| T-1-07 (a statement edited while "adding a citation") | All 18 diff deletions are table lines, itemised above, and a cell-by-cell comparison against `HEAD` shows 0 changes to any non-`Source` cell across all 49 pipe-table rows. |
| T-1-08 (gate 5 enumerating only part of the catalog) | The checker reports 42 registry entries (37 non-deviation, at its floor of 37) against 38 index rows with 0 structural failures, i.e. empty symmetric difference with D1-D5 aggregated. Unchanged before and after. |

## Verification

| Check | Result |
|-------|--------|
| `python3 scripts/check-provenance.py --verbose` reports a citation for every registry entry | PASS — 42/42 rows `PASS`, read from the checker, not from `grep -c` |
| ID-set agreement with the §12 index (42 registry, 38 index, empty symmetric difference) | PASS — 0 structural failures |
| Gate 5 green, or red only on named `Unsourced` rows | PASS — green, zero `Unsourced` rows |
| No statement-sentence deletion in `git diff docs/spqr-properties.md` | PASS — all 18 deletions are table lines; 0 non-`Source` cell changes |
| `git status --porcelain -- src SrcTranslated '*.lean'` empty | PASS — empty |
| `grep -q 'spec-sections.txt'` and `grep -q 'scka-refs.txt'` in the catalog | PASS — both named in the §1 PROV-01 paragraph |
| Both reference lists start with a `#` provenance comment naming document, revision, date | PASS |
| `grep -vcE '^#\|^$\|^[0-9.]+$' docs/spec-sections.txt` returns 0 | PASS |
| No PDF added to the repository | PASS — `git status --porcelain` shows only the intended files |

## Commits

| Task | Commit | What |
|------|--------|------|
| 1 | `f3ff32d` | `docs(01-03): transcribe the two provenance reference lists` |
| 2 | `c78cf8b` | `docs(01-03): give every catalog row a resolving Source: citation` |
| — | `97003eb` | `docs(01-03): summarise the provenance retrofit` |
| 3 | (this file) | `docs(01-03): record the closed task-3 checkpoint ruling` — no code or catalog change; task 3 is a review checkpoint, and the approving ruling asks for nothing to be edited |

## Status

**Plan complete: all 3 tasks done.** Tasks 1 and 2 executed and committed; task 3's blocking
`checkpoint:human-verify` was presented and closed by the user's ruling "no unsourced rows,
proceed" (2026-09-15). ROADMAP criterion 2 is met with no residue, and the C2 criterion is
enforceable from here on: a new catalog row without a resolving citation cannot reach a green
gate 5.

STATE.md and ROADMAP.md were deliberately not touched: the orchestrator owns those writes
after the wave completes.

## Self-Check: PASSED

- `docs/spec-sections.txt` — FOUND
- `docs/scka-refs.txt` — FOUND
- `docs/spqr-properties.md` — FOUND
- `.planning/phases/01-gates-provenance-and-target-list/01-03-SUMMARY.md` — FOUND
- commit `f3ff32d` — FOUND in `git log`
- commit `c78cf8b` — FOUND in `git log`
- HEAD based on `19c3ad2` — confirmed (`git log --oneline -3` shows `19c3ad2` as the parent
  of `f3ff32d`)
