# Generated Lean function memory, 2026-11-13

The earlier 404-module scan used `lake env lean` without Lake's setup JSON. That
omitted the `SrcTranslated` linter options, so its RSS and time rankings are not
comparable to this run. Profiling the unsplit `Funs.lean` under those old options
showed 864 header-linter calls taking 512 seconds in total. The benchmark now uses
each module's Lake setup JSON.

The remaining generated `SrcTranslated.Funs` module was split at the declaration
for `COMPLETE_POINTS_POLYS_36`. `scripts/split-translated-funs.py` applies this
split after each Aeneas extraction. The source definitions are unchanged and keep
their original order; `Funs.lean` publicly imports the new `FunsCore.lean`.

| Module | Before peak RSS median | After peak RSS median | Before time median | After time median |
| --- | ---: | ---: | ---: | ---: |
| `SrcTranslated.FunsCore` | — | 1713.74 MiB | — | 8.14 s |
| `SrcTranslated.Funs` | 1902.77 MiB | 1631.69 MiB | 14.12 s | 8.30 s |
| `Spqr.Specs.Encoding.Polynomial.PolyDecoder.AddChunk` | 1559.00 MiB | 1559.45 MiB | 9.55 s | 9.48 s |

The peak of the generated-function compilation steps fell 9.93%. Their summed
median check time rose 16.43% because the second module loads the first one. This
exceeds the workflow's default 10% time threshold; the split is retained for its
peak-memory reduction. The measured downstream module stayed flat. These are
single-process RSS measurements, not a whole-build peak.

Results: [`data/memory/2026-11-13-baseline.jsonl`](../data/memory/2026-11-13-baseline.jsonl)
and [`data/memory/2026-11-13-split.jsonl`](../data/memory/2026-11-13-split.jsonl).
Raw logs remain in `/tmp/spqr-memory-cause-20261113/`. `lake build`,
`lake exe runLinter Spqr`, `lake env lean scripts/Audit.lean`, and
`git diff --check` passed. The split output was also checked byte for byte
against the original generated source.
