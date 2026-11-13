#!/usr/bin/env python3
"""Ask Codex for reusable Lean definitions from selected source files.

The source files are read by a read-only Codex session. The only output is a
JSON proposal file; applying definitions to the project is a separate step.
"""

from __future__ import annotations

import argparse
import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
SCHEMA = {
    "type": "object",
    "properties": {
        "definitions": {
            "type": "array",
            "items": {
                "type": "object",
                "properties": {
                    "name": {"type": "string"},
                    "code": {"type": "string"},
                    "purpose": {"type": "string"},
                    "reuse": {"type": "string"},
                },
                "required": ["name", "code", "purpose", "reuse"],
                "additionalProperties": False,
            },
        },
    },
    "required": ["definitions"],
    "additionalProperties": False,
}


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("files", nargs="*", type=Path, help="Lean source files to analyze")
    parser.add_argument(
        "--files-from", type=Path,
        help="text file with one Lean source path per line, e.g. generation-files.txt",
    )
    parser.add_argument(
        "-o", "--output", type=Path, default=Path("data/generated-definitions.json"),
        help="JSON proposal file (default: %(default)s)",
    )
    parser.add_argument("--codex-bin", default="codex", help="Codex CLI executable")
    parser.add_argument("--model", help="optional Codex model")
    parser.add_argument(
        "--timeout", type=int, default=600,
        help="seconds allowed per file (default: %(default)s)",
    )
    args = parser.parse_args()
    if args.timeout <= 0:
        parser.error("--timeout must be positive")
    if not args.files and args.files_from is None:
        parser.error("supply Lean files or --files-from")
    return args


def source_path(path: Path) -> Path:
    resolved = path.resolve(strict=True)
    if not resolved.is_file() or resolved.suffix != ".lean":
        raise ValueError(f"expected a Lean source file: {path}")
    if not resolved.is_relative_to(ROOT):
        raise ValueError(f"Lean source file must be inside {ROOT}: {path}")
    return resolved


def prompt_for(path: Path) -> str:
    relative = path.relative_to(ROOT).as_posix()
    return f"""Analyze the Lean source file `{relative}` in this repository.

Propose new reusable definitions that express the meaning of specifications in
this file more precisely and can plausibly be reused by other files. Inspect
relevant imports and neighboring definitions when needed. Return only genuinely
useful proposals; an empty array is valid. Keep the semantics of existing
specifications, avoid duplicates of existing definitions, and prefer small,
general predicates or functions over one-use wrappers.

Return JSON matching the supplied schema. Each `code` must be one complete,
exact Lean `def` or `abbrev` declaration. Use a fully qualified declaration
name and fully qualified references so the code typechecks when appended after
the source file's final namespace. Do not rely on local `open` declarations.
Do not propose theorems, lemmas, axioms, proofs, `sorry`, or
changes to existing definitions. In `purpose`, state the specification meaning.
In `reuse`, identify concrete likely reuse sites, or say when reuse is uncertain.
Do not edit any repository files.
"""


def generate_one(
    path: Path, codex_bin: str, model: str | None, timeout: int, schema: Path,
    message: Path,
) -> list[dict[str, str]]:
    command = [
        codex_bin, "exec", "--ephemeral", "--sandbox", "read-only",
        "--cd", str(ROOT), "--output-schema", str(schema),
        "--output-last-message", str(message), "-",
    ]
    if model:
        command[2:2] = ["--model", model]
    try:
        result = subprocess.run(
            command, input=prompt_for(path), text=True, capture_output=True,
            cwd=ROOT, timeout=timeout, check=False,
        )
    except subprocess.TimeoutExpired as exc:
        raise RuntimeError(f"Codex timed out on {path} after {timeout}s") from exc
    if result.returncode:
        detail = (result.stderr or result.stdout).strip()
        raise RuntimeError(f"Codex failed on {path} (exit {result.returncode}): {detail}")
    try:
        payload = json.loads(message.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise RuntimeError(f"Codex returned no valid JSON for {path}") from exc
    if not isinstance(payload, dict) or not isinstance(payload.get("definitions"), list):
        raise RuntimeError(f"Codex returned an invalid response for {path}")
    for definition in payload["definitions"]:
        if not isinstance(definition, dict) or any(
            not isinstance(definition.get(key), str) or not definition[key].strip()
            for key in ("name", "code", "purpose", "reuse")
        ):
            raise RuntimeError(f"Codex returned an incomplete definition for {path}")
        if not definition["code"].lstrip().startswith(("def ", "abbrev ")):
            raise RuntimeError(f"Codex returned a non-definition for {path}: {definition['name']}")
    return payload["definitions"]


def main() -> int:
    args = parse_args()
    if shutil.which(args.codex_bin) is None:
        raise ValueError(f"Codex executable not found: {args.codex_bin}")
    input_paths = list(args.files)
    if args.files_from is not None:
        input_paths.extend(
            Path(line.strip()) for line in args.files_from.read_text(encoding="utf-8").splitlines()
            if line.strip() and not line.lstrip().startswith("#")
        )
    files = list(dict.fromkeys(source_path(path) for path in input_paths))
    if not files:
        raise ValueError("no Lean files were supplied")
    output = args.output.resolve()
    if output in files:
        raise ValueError("output cannot overwrite an input file")

    proposals = []
    with tempfile.TemporaryDirectory(prefix="lean-definitions-") as temporary:
        schema = Path(temporary) / "schema.json"
        message = Path(temporary) / "response.json"
        schema.write_text(json.dumps(SCHEMA), encoding="utf-8")
        for index, path in enumerate(files, start=1):
            print(f"[{index}/{len(files)}] Analyzing {path.relative_to(ROOT)}", file=sys.stderr)
            definitions = generate_one(
                path, args.codex_bin, args.model, args.timeout, schema, message,
            )
            proposals.append({"source_file": path.relative_to(ROOT).as_posix(),
                              "definitions": definitions})
            message.unlink(missing_ok=True)

    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps({"schema": "lean-definition-proposals/v1",
                                  "files": proposals}, indent=2) + "\n", encoding="utf-8")
    count = sum(len(item["definitions"]) for item in proposals)
    print(f"Wrote {count} proposed definitions from {len(files)} files to {output}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, ValueError, RuntimeError) as exc:
        raise SystemExit(f"error: {exc}") from exc
