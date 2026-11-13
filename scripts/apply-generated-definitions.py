#!/usr/bin/env python3
"""Apply proposed definitions to generation files and compile the generation set.

All source edits are rolled back if the Lake build fails. Existing source text is
preserved byte for byte before the generated block.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
GENERATION_FILES = ROOT / "data/probe-lean-split/generation-files.txt"
START = "-- BEGIN GENERATED DEFINITIONS (lean-definition-proposals/v1)"
END = "-- END GENERATED DEFINITIONS"


def arguments() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--proposals", type=Path, default=Path("data/generated-definitions.json"))
    parser.add_argument("--lake-bin", default="lake", help="Lake executable")
    return parser.parse_args()


def relative_source(value: str) -> Path:
    path = Path(value)
    if path.is_absolute() or path.suffix != ".lean" or ".." in path.parts:
        raise ValueError(f"invalid source path: {value}")
    resolved = (ROOT / path).resolve(strict=True)
    if not resolved.is_file() or not resolved.is_relative_to(ROOT):
        raise ValueError(f"source file is outside the repository: {value}")
    return resolved


def load_inputs(args: argparse.Namespace) -> tuple[list[Path], dict[Path, list[str]]]:
    generation = [
        relative_source(line.strip())
        for line in GENERATION_FILES.read_text(encoding="utf-8").splitlines()
        if line.strip() and not line.lstrip().startswith("#")
    ]
    if not generation or len(generation) != len(set(generation)):
        raise ValueError("generation file list is empty or has duplicate paths")
    allowed = set(generation)
    payload = json.loads(args.proposals.read_text(encoding="utf-8"))
    if not isinstance(payload, dict) or payload.get("schema") != "lean-definition-proposals/v1" or not isinstance(payload.get("files"), list):
        raise ValueError("expected lean-definition-proposals/v1 JSON")
    proposed: dict[Path, list[str]] = {}
    for item in payload["files"]:
        if not isinstance(item, dict) or not isinstance(item.get("source_file"), str):
            raise ValueError("proposal entry is missing source_file")
        source = relative_source(item["source_file"])
        if source not in allowed:
            raise ValueError(f"proposal targets a file outside the generation set: {item['source_file']}")
        if source in proposed or not isinstance(item.get("definitions"), list):
            raise ValueError(f"duplicate source or invalid definitions: {item['source_file']}")
        codes = []
        for definition in item["definitions"]:
            if not isinstance(definition, dict) or any(
                not isinstance(definition.get(key), str) or not definition[key].strip()
                for key in ("name", "code", "purpose", "reuse")
            ):
                raise ValueError(f"incomplete definition in {item['source_file']}")
            code = definition["code"].strip()
            if not re.match(r"^(def|abbrev)\s+", code):
                raise ValueError(f"expected def or abbrev: {definition['name']}")
            codes.append(code)
        proposed[source] = codes
    return generation, proposed


def module_name(path: Path) -> str:
    return ".".join(path.relative_to(ROOT).with_suffix("").parts)


def main() -> None:
    args = arguments()
    generation, proposed = load_inputs(args)
    changes: dict[Path, bytes] = {}
    for path, codes in proposed.items():
        if not codes:
            continue
        original = path.read_bytes()
        if START.encode() in original or END.encode() in original:
            raise ValueError(f"generated definition block already exists: {path.relative_to(ROOT)}")
        changes[path] = original
    if not changes:
        raise ValueError("proposal file has no definitions to apply")

    success = False
    try:
        for path, original in changes.items():
            block = (
                "\n" + START + "\n@[expose] public section\n\n"
                + "\n\n".join(proposed[path]) + "\n" + END + "\n"
            ).encode("utf-8")
            path.write_bytes(original + (b"" if original.endswith(b"\n") else b"\n") + block)
        targets = [module_name(path) for path in generation]
        print(f"Compiling {len(targets)} generation modules with {sum(map(len, proposed.values()))} proposals", flush=True)
        subprocess.run([args.lake_bin, "build", *targets], cwd=ROOT, check=True)
        success = True
    finally:
        if not success:
            for path, original in changes.items():
                path.write_bytes(original)
            print("Build failed; restored all edited source files", flush=True)
    print(f"Applied definitions to {len(changes)} files; generation set compiled")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, subprocess.CalledProcessError) as exc:
        raise SystemExit(f"error: {exc}") from exc
