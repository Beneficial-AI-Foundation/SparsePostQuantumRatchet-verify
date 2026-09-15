---
created: 2026-09-15
source: phase 01 execution (/gsd-execute-phase 1)
status: pending
blocked_until: PR A and PR B are both merged
---

# Post-PR cleanup after Phase 1

Deliberately **not** tied to `resolves_phase`: this cannot run while the Phase 1
PRs are open, because some of the artifacts below are what a reviewer reads. Do
it after PR A and PR B are merged.

## 1. Merged executor branches

`git branch -D` is permission-denied for the GSD orchestrator, so every wave
leaves its `worktree-agent-*` branch behind after the merge. As of 2026-09-15
these are merged into `la/spec-catalog` and safe to delete:

```
worktree-agent-ae34408ff42616711   # 01-01
worktree-agent-a230c949b0ea345ef   # 01-02
worktree-agent-a3a8cb1fc733ba241   # 01-03
worktree-agent-a34fde24bf66ad3c7   # 01-04
```

Waves 5-8 will add one each. Enumerate with `git branch --list 'worktree-agent-*'`
and confirm each is merged (`git branch --merged la/spec-catalog`) before deleting.

## 2. Agent worktrees and their build caches

Each executor worktree that runs a Lean build carries its own **~8.4 GB**
`.lake` (mathlib oleans from `lake exe cache get`, plus the project's own).
`git worktree remove <path> --force` works, but only as a single bare command —
a compound shell loop around it is permission-denied.

```bash
git worktree list                     # find .claude/worktrees/agent-* entries
git worktree remove <path> --force    # one call per worktree, not in a loop
git worktree prune
```

Also check for plan 01-04's own scratch worktrees if it did not remove them:
`/home/lacra/git_repos/baif/spqr-gate-baseline` (CI verdict comparison) and
`/home/lacra/git_repos/baif/spqr-negctl` (gate negative controls).
`spqr-pr340` predates this phase — leave it alone.

## 3. Local-only source PDFs — decide, do not silently drop

The orchestrator copied the two provenance sources into `docs/` on 2026-09-15
because they were absent and plan 01-03 would otherwise have halted by design:

```
docs/mlkembraid.pdf    <- /tmp/props-review/mlkembraid.pdf
docs/2025-2267.pdf     <- /tmp/props-review/2025-2267.pdf
```

`docs/*.pdf` is gitignored, so these are **not** in either PR and will not
reach a reviewer or CI. Gate 5 does not need them (it resolves citations against
`docs/spec-sections.txt` and `docs/scka-refs.txt`), but every later phase that
adds or revises a `Source:` citation does. The originals live in `/tmp`, which
does not survive a reboot.

Decide one of: keep the `docs/` copies as the documented local convention and
say so in `scripts/README.md`; move them somewhere durable outside the repo; or
un-ignore them and commit them if their licensing allows. Do not leave the only
copies in `/tmp`.

## 4. Stray untracked files at the repo root

Pre-existing, unrelated to Phase 1, and `.planning/PROJECT.md:100` records the
`docs/` ones as working notes rather than project inputs. Confirm with the user
before removing anything:

```
acd19.pdf
summary.md
.verilib/
docs/audit-prf-prng-acd19-4.3.md
docs/probe-lean-sorry-unsoundness.md
docs/props-draft-review.md
docs/report-consistency-check.md
```
