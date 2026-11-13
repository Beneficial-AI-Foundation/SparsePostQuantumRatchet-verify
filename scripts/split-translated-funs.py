#!/usr/bin/env python3
"""Split Aeneas's generated Funs module at a stable declaration boundary."""

from pathlib import Path
import sys


MARKER = "/-- [spqr::encoding::polynomial::COMPLETE_POINTS_POLYS_36]"
HEADER_END = "namespace spqr\n"
IMPORT = "public import SrcTranslated.FunsExternal\n"


def split(source: str) -> tuple[str, str]:
    if source.count(MARKER) != 1 or source.count(HEADER_END) != 1:
        raise ValueError("unexpected Aeneas Funs layout; update the split point")
    if not source.endswith("end spqr\n"):
        raise ValueError("expected the generated Funs module to end with `end spqr`")
    header_end = source.index(HEADER_END) + len(HEADER_END)
    marker_start = source.index(MARKER)
    if marker_start <= header_end:
        raise ValueError("split point precedes the module body")
    header = source[:header_end]
    prefix = header + source[header_end:marker_start] + "end spqr\n"
    # The upstream generated text has a few trailing spaces. The first half
    # becomes a new file, so trim them to keep `git diff --check` clean.
    prefix = "\n".join(line.rstrip() for line in prefix.split("\n"))
    suffix = (header.replace(IMPORT, IMPORT + "public import SrcTranslated.FunsCore\n")
              + "\n" + source[marker_start:])
    return prefix, suffix


def main() -> None:
    repo = Path(__file__).resolve().parent.parent
    funs = repo / "SrcTranslated/Funs.lean"
    core = repo / "SrcTranslated/FunsCore.lean"
    prefix, suffix = split(funs.read_text())
    core.write_text(prefix)
    funs.write_text(suffix)


if __name__ == "__main__":
    try:
        main()
    except ValueError as error:
        print(error, file=sys.stderr)
        raise SystemExit(1) from error
