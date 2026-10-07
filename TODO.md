# TODO: Aeneas update PR (#635)

Branch `update-to-nightly-2026.10.05-557eff8`, now pinned to Aeneas `nightly-2026.10.07-aa66752`.
`main` is merged and pushed. Status as of 2026-10-07.

## Before marking the PR ready

1. **Title.** The branch and PR title still say `nightly-2026.10.05-557eff8`, but the pin is now
   `nightly-2026.10.07-aa66752`. Retitle the PR; renaming the branch would force a new PR.
2. **Description.** It still says "TODO: CI is currently failing due to warnings produced by
   Aeneas". Cover instead:
   - **Statement changes**, all forced by the new types:
     - `mac_ct_spec`/`mac_hdr_spec` (`.deref`);
     - `verify_ct_spec`/`verify_hdr_spec` (`{ slice := … }`);
     - `ChainEpochDirection.new_spec` (`.deref`);
     - `decode_varint_loop_spec` (argument order);
     - the 8 `PolyDecoder/FromPb` specs (`.match`);
     - `Pt` `try_from_spec` (`_h_clone`).

     Full table: `doc/TODO-aeneas-update-statement-changes.md`.
   - **The two-step update:** `nightly-2026.10.05`, then `nightly-2026.10.07` with the
     `spec_imp_exists` removal (aeneas#1384).
   - **The compatibility shim** `Spqr/Auxiliary/Aeneas/SpecImpExists.lean`, with its plan for
     removal.
   - **Module-system opt-out:** `use_lean_modules: false`, #632.
   - **charon#1504 workaround:** `#[derive(Copy, Clone)]` on `PolyConst`.
   - **Dropped tweaks:** the `ok_or` annotation (aeneas#1018), and the linter-switch-off tweak,
     replaced by `leanOptions = { weak.linter.style.headerAlt = false }` on the `SrcTranslated`
     lib.
   - **`sorry` status:** no new `sorry`. Remaining: `DecodeState` (#102), `MapCollectBridge`
     (aeneas#1043), and two that came with `main` (`Chain/FromPb.lean`, `Chain/IntoPb.lean`).
3. **CI.** `scripts/check-lint.sh` passed locally on the 10-07 pin before the merge; the full
   build and `lake exe runLinter Spqr` pass after it. Confirm CI is green on the pushed head.

## Optional, small (could go in this PR)

4. **Statement choices to revisit:**
   - `ChainEpochDirection.new_spec`: `result.next.deref = k`, or the equivalent
     `result.next.val = k.val` that `CedForDirection` already uses.
   - `Pt` `try_from_spec`: drop the now-unused `_h_clone` hypothesis.
5. **`scripts/check-lint.sh`:** its `runLinter` step greps for `error:` instead of trusting the
   exit code, as CI does (`.github/workflows/lean.yml`). One-line fix.
6. **Step-generated hypothesis names still referenced:**
   - `ce_post`/`r_post`/`r1_post` in `Chain/Chain/SendKey`, `RecvKey`, `RecvKey32`;
   - `PolyEncoder.point_at_spec` (`g1_post`, `p_post`, …);
   - `V1/Chunked/States/Serialize/Message/Deserialize`;
   - `h_bytes` in `PolyEncoder/FromPb`.

   They compile; this is style cleanup and could be a separate PR.
7. **`Spqr/Auxiliary/Aeneas/Vec.lean`:** staged for upstreaming (#305). Check whether the new
   Aeneas already provides `alloc.vec.Vec.deref_val`/`deref_length`.

## Follow-up PRs (not this one)

8. **Group C refactor.** Remove the `= ok` statements so that the shim and
   `Spqr/Auxiliary/Aeneas/SpecRefl.lean` can be deleted.
   - Waiting on decisions (a)–(f) in `doc/TODO-group-c-proposal.md`.
   - Groups A/B are already done: 39 of 49 uses removed, no statement changes.
9. **`extend-coverage` branch** (`da26445`, notes in `doc/extend-coverage-progress.md` on that
   branch). Still on the 10-05 pin. Rebasing onto this branch needs:
   - the 10-07 fixes again (`spec_imp_exists` shim, `WP.spec_ok` on `ok …` goals,
     `extend_from_slice` via `List.clone`);
   - fixes for the spec files that branch rewrote.
10. **Upstream reports** (drafts in `/home/oliver/Projects/aeneas-mwe`, uncommitted, not filed):
    - `issue_28`: aeneas#1043, `-filter-trait-methods` plus a `Std` `Map` model draft.
    - `issue_30`: `Vec<&T>` internal error, with a patch.
    - `issue_31`: negative literal patterns, with a patch.
    - `issue_32`: "Could not match the contexts" in prost-style `encoded_len`.
    - `issue_33`: nested-borrow sanity check with closures capturing borrows.

## Housekeeping

11. **Untracked docs:** `doc/TODO-aeneas-update-statement-changes.md`,
    `doc/TODO-group-c-proposal.md`.
12. **Stale git worktrees** (`git worktree list`):
    - the Claude scratchpad one (detached HEAD, throwaway commits);
    - an older locked agent worktree under
      `/home/oliver/Projects/Verify/SparsePostQuantumRatchet-verify/.claude/worktrees/`.

    Remove with `git worktree remove --force <path>` and `git worktree prune`.
