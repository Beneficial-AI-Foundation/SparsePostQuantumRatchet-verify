# Progress: generating Lean definitions with a Python Codex agent

## Goal and current status

The goal is to propose new, general Lean definitions from selected source files, then evaluate whether those definitions make specifications clearer and proofs in other files shorter or faster. `scripts/generate-lean-definitions.py` invokes the Codex CLI and writes structured proposals. `scripts/apply-generated-definitions.py` applies proposals to generation files and compiles the full generation set. Neither script evaluates proof improvements.

The framework has passed Python syntax checking and an end-to-end invocation with a stubbed Codex CLI response. **No real Codex generation run has been performed with this framework yet**, and no generated definition has been compiled or adopted through it. The chain decoder definitions described in `doc/CHAIN_DECODER_DEFINITIONS_AND_PROOFS.md` were created manually in earlier work; they are not output from this Python agent.

## Input: the file split

`scripts/split-probe-lean.py` produced a dependency-aware, whole-file split from the probe-lean extract. The current manifest reports 119 generation files containing 477 eligible `def` declarations, and 239 test files containing 923. There are no generation-to-test dependency edges. The generator accepts any explicit repository `.lean` files; it does not infer or enforce which side of the split a file belongs to. To keep the experiment separated, supply files from `data/probe-lean-split/generation-files.txt` only.

## Python workflow

1. The command accepts positional `.lean` paths or `--files-from` with one path per line. It removes duplicate paths and checks that each file exists inside the repository.
2. For each file, Python launches a separate `codex exec` process with `subprocess.run`. Codex receives a prompt naming the file and can inspect its imports and neighboring definitions. The invocation uses `--sandbox read-only` and `--ephemeral`.
3. The prompt asks for small, reusable `def` or `abbrev` declarations that express existing specification meaning. It asks Codex to avoid duplicate, one-use, or semantics-changing proposals and to return an empty list when no good candidate exists. It excludes theorems, lemmas, axioms, proofs, and `sorry`.
4. `--output-schema` constrains Codex's final response. Python reads that response from a temporary file supplied through `--output-last-message`, checks the required fields, and checks that each code string begins with `def` or `abbrev`.
5. After all files succeed, Python writes one JSON result containing each source path and its proposals. The source files remain untouched until the apply step.

Each proposal has four fields: `name`, `code` (the exact proposed Lean declaration), `purpose` (the specification meaning), and `reuse` (likely reuse sites or uncertainty). The output has this shape:

```json
{
  "schema": "lean-definition-proposals/v1",
  "files": [
    {
      "source_file": "Spqr/Specs/Example.lean",
      "definitions": [
        {
          "name": "Example.ValidInput",
          "code": "def Example.ValidInput (x : Nat) : Prop := x > 0",
          "purpose": "Names the positive-input condition.",
          "reuse": "Potentially reusable by callers that check input validity."
        }
      ]
    }
  ]
}
```

This JSON is a format example, **not an actual generated proposal**.

## Running it

For a small trial with explicit files:

```bash
npm run generate-lean-definitions -- Spqr/Specs/Chain/ChainEpochDirection/FunctionalModels.lean
```

For the full generation partition:

```bash
npm run generate-lean-definitions -- --files-from data/probe-lean-split/generation-files.txt
```

The default result path is `data/generated-definitions.json`. Use `-o path.json` to choose another path, `--model MODEL` to select a model, and `--timeout SECONDS` to change the per-file limit (600 seconds by default). The full partition currently means up to 119 sequential Codex calls, so a small trial is the practical first run.

After reviewing the JSON proposals, apply and compile them with:

```bash
npm run apply-generated-definitions
```

The apply command accepts `--proposals path.json` for another result file. It appends declarations in a public section at the end of each source file, after its final namespace, so proposed names and references must be fully qualified. It only accepts files listed in `generation-files.txt`, builds every module in that list with Lake, and restores the original source bytes if the build fails. A successful run leaves the definitions in the generation files. The command refuses to append a second generated block to the same file.

## Verification and remaining work

Completed verification: Python syntax checks for both scripts; command-line help; an invocation using a stub Codex executable that returned a valid definition; a temporary valid proposal applied to a generation file and compiled with `lake build` across all 119 generation modules (2,546 Lake jobs); a deliberately invalid Lean proposal that failed the build and restored the source byte for byte; rejection of a held-out test file; and `git diff --check`. The temporary definition was removed afterward. These checks do not verify model quality or the value of any real AI proposal.

The framework does not prove semantic equivalence, detect all duplicates, rewrite proofs, or measure proof length or runtime. Compiling catches Lean errors in applied definitions and the generation set, but a human must still judge whether each proposed definition is useful and states the intended meaning. A failed generation file stops the proposal run before the aggregate JSON is written, so there is no checkpoint or resume mechanism yet.

The next experimental step is to run the agent on a small set of generation files, review and apply useful proposals, and record concrete reuse sites. Then test whether the new definitions improve proofs in untouched test files. Proof-line and proof-time improvements need measurements from those later changes; the framework itself has achieved neither yet.
