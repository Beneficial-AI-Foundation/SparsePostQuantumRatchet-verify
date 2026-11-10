# PR 677 review: Fix Lean build caching in CI

Branch `pr-677-review` (base `c0b7543f` = origin/main HEAD). Only `.github/workflows/lean.yml` changes (+15).
Closes #676.

## Verdict: mergeable

Does what the issue asks. Verified against the PR's own runs: first run saved a 2.6 GB `.lake`
entry (`spqr-lake-v1-Linux-X64-<hash>-<sha>`), rerun restored it and rebuilt nothing.
`actions/cache` post step is `post-if: success()`, so a failed build never poisons the cache.
`use-github-cache` is a real `lean-action@v1` input. `test "${PIPESTATUS[0]}" -eq 0` is correct
under the default `bash -e` shell (no pipefail), and fixes a pre-existing bug: before this PR a
failed `lake build` was swallowed by `tee` and only caught indirectly by the lint step.

## Non-blocking

- `lean.yml:38-47`: entries are ~2.6 GB and the repo cache limit is 10 GB (currently 12.1 GB,
  already evicting). Every PR push saves a new entry keyed by its own sha, so main's entry gets
  evicted after ~3 PR pushes and the next fresh PR does a full 10 min rebuild. Not a regression
  (old `lean-action` cache had the same key scheme at 2.35 GB), but two cheap improvements:
  - split into `actions/cache/restore` + `actions/cache/save` with
    `if: github.event_name == 'push'`, so only main populates the cache; or
  - exclude mathlib oleans from the cached path (`!.lake/packages/mathlib/.lake`); `lake exe
    cache get` refetches them in ~1 min and entries shrink to a few hundred MB.
- `lean.yml:38`: cache saves only when the whole job succeeds, so a PR failing lint/audit never
  caches its build. Acceptable; the restore/save split above would also let the save run right
  after the build step.
- `lean.yml:41-47`: the `>-` folded scalar keeps newlines inside `${{ ... }}` (more-indented
  line). GitHub tolerates it and actionlint passes, but a single-line key is less surprising.
- `lean.yml:61`: lint step uses `set -o pipefail`; build step uses `PIPESTATUS`. Equivalent;
  pick one for consistency.
