#!/usr/bin/env python3
"""Gate 5: PROV-01 provenance check over `docs/spqr-properties.md`.

Every property row of the catalog must carry a `Source:` field, and **every**
citation in that field must resolve.  PROV-01 (as ruled 2026-09-15) says "at
least one of" the three source classes, semicolon-separated when a row has both
a spec ground and the code implementing it - so one good citation does not
rescue a bad one in the same list.

The three citation forms and how each is resolved:

    Spec §x.y            membership in `docs/spec-sections.txt`
    SCKA Def. n          membership in `docs/scka-refs.txt`
    SCKA Fig. n          membership in `docs/scka-refs.txt`
    src/path.rs:a-b      the file exists and a..b is within its length
    src/path.rs:a        the file exists and line a is within its length

The two `.txt` lists are the checkable proxy for the PDFs, which are gitignored
and not parsed.  A row's `Evidence:` line is deliberately **not** parsed and
**not** gated: it carries pointers outside the three source classes (a
`Spqr/Specs/**` lemma, a planning doc), so it has no citation grammar.  That is
why a Lean path belongs on `Evidence:` and never in `Source:`.

The checker fails closed.  An unparseable citation form, a missing `Source:`
field, an `Unsourced - …` marker and a missing reference list are all failures,
never skips - otherwise a typo buys a pass.

Usage:
    python3 scripts/check-provenance.py [--verbose] [--row ID] [--catalog PATH]

Exit status:
    0  every row has a `Source:` whose every citation resolves
    1  at least one row failed, or the registry disagrees with the §12 index
    2  usage error / the catalog could not be read
"""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
CATALOG = REPO_ROOT / "docs" / "spqr-properties.md"
SPEC_SECTIONS = REPO_ROOT / "docs" / "spec-sections.txt"
SCKA_REFS = REPO_ROOT / "docs" / "scka-refs.txt"

# The §12 index collapses the five §11 deviation rows into one aggregate entry
# (`| D1–D5 | 11 | Deviations |`).  Registry IDs matching this are mapped onto
# that aggregate before the ID sets are compared.
DEVIATION_ID = re.compile(r"^D\d+$")
INDEX_AGGREGATE = re.compile(r"^D\d+\s*[–—-]\s*D\d+$")

# Enumerating half the catalog is the failure mode to prevent; the bare count
# floor is the backstop for it.  42 registry entries / 37 non-deviation on the
# 2026-09-15 catalog.
MIN_NON_DEVIATION_ENTRIES = 37

ID_HEADING = re.compile(r"^###\s+((?:PROP|LEAN|STRUCT)-[A-Za-z0-9-]+)\b")
SECTION_HEADING = re.compile(r"^##\s+(\d+)\.\s")
ROW_ID = re.compile(r"^(?:\*\*|`)*((?:PROP|LEAN|STRUCT)-[A-Za-z0-9-]+|D\d+(?:\s*[–—-]\s*D\d+)?)(?:\*\*|`)*$")

CITE_SPEC = re.compile(r"^Spec\s+§\s*([0-9]+(?:\.[0-9]+)*)$")
CITE_SCKA = re.compile(r"^SCKA\s+((?:Def|Fig)\.\s*[0-9]+(?:\.[0-9]+)*)$")
CITE_SRC = re.compile(r"^(src/[A-Za-z0-9_./-]+\.rs):([0-9]+)(?:\s*-\s*([0-9]+))?$")
UNSOURCED = re.compile(r"^Unsourced\b")


class Row:
    """One catalog property, joined by ID across every place it appears."""

    def __init__(self, ident: str, where: str):
        self.id = ident
        self.where = where            # first location, for the report
        self.sources: list[str] = []  # raw `Source:` field texts, in order seen
        self.evidence: list[str] = []  # recorded but never gated

    def __repr__(self) -> str:  # pragma: no cover - debugging aid
        return f"Row({self.id!r}, {self.where!r}, sources={self.sources!r})"


def split_table_row(line: str) -> list[str] | None:
    s = line.strip()
    if not s.startswith("|"):
        return None
    cells = [c.strip() for c in s.strip("|").split("|")]
    if all(re.fullmatch(r":?-{2,}:?", c) for c in cells if c):
        return None  # the |---|---| separator
    return cells


def normalise_id(cell: str) -> str | None:
    m = ROW_ID.match(cell.strip())
    if not m:
        return None
    return re.sub(r"\s+", "", m.group(1))


def build_registry(text: str, verbose: bool) -> tuple[dict[str, Row], set[str]]:
    """Return (registry keyed by normalised ID, §12 index ID set).

    Prose rows (§2-§9) are `### PROP-…` / `### LEAN-…` / `### STRUCT-…`
    headings with a `Source:` line in the body beneath.  §10 and §11 are pipe
    tables whose citation lives in a `Source` *column*.  A deviation ID that
    appears in both §11 tables - the existing five-column table and the
    Decision/Status table - is **one** registry entry, joined by ID.
    """
    registry: dict[str, Row] = {}
    index_ids: set[str] = set()

    section = None
    current: Row | None = None
    table_header: list[str] | None = None

    def get(ident: str, where: str) -> Row:
        if ident not in registry:
            registry[ident] = Row(ident, where)
        return registry[ident]

    for lineno, line in enumerate(text.splitlines(), start=1):
        sec = SECTION_HEADING.match(line)
        if sec:
            section = sec.group(1)
            current = None
            table_header = None
            continue

        head = ID_HEADING.match(line)
        if head:
            ident = re.sub(r"\s+", "", head.group(1))
            current = get(ident, f"§{section} heading (line {lineno})")
            table_header = None
            continue

        cells = split_table_row(line)
        if cells is not None:
            lowered = [c.lower() for c in cells]
            if "id" in lowered and ("status" in lowered or "source" in lowered
                                    or "statement" in lowered or "where" in lowered
                                    or "spec" in lowered or "decision" in lowered
                                    or "section" in lowered):
                table_header = lowered
                continue
            ident = normalise_id(cells[0]) if cells else None
            if ident is None:
                continue
            if section == "12":
                index_ids.add(ident)
                continue
            if section in ("10", "11"):
                row = get(ident, f"§{section} table (line {lineno})")
                if table_header and "source" in table_header:
                    col = table_header.index("source")
                    if col < len(cells) and cells[col]:
                        row.sources.append(cells[col])
                if table_header and "evidence" in table_header:
                    col = table_header.index("evidence")
                    if col < len(cells) and cells[col]:
                        row.evidence.append(cells[col])
            continue

        if current is not None:
            m = re.match(r"^\s*(?:\*\*)?Source(?:\*\*)?\s*:\s*(.+?)\s*$", line)
            if m:
                current.sources.append(m.group(1))
                continue
            m = re.match(r"^\s*(?:\*\*)?Evidence(?:\*\*)?\s*:\s*(.+?)\s*$", line)
            if m:
                current.evidence.append(m.group(1))

    if verbose:
        for ident, row in registry.items():
            print(f"  registry {ident:<14} {row.where}")

    return registry, index_ids


def load_reference_list(path: Path) -> set[str] | None:
    if not path.exists():
        return None
    out = set()
    for raw in path.read_text().splitlines():
        line = raw.split("#", 1)[0].strip()
        if line:
            out.add(line)
    return out


def check_citation(cite: str, spec_sections: set[str] | None,
                   scka_refs: set[str] | None) -> str | None:
    """Return None if the citation resolves, else a failure reason."""
    cite = cite.strip().strip("`").rstrip(".,").strip()
    if not cite:
        return "empty citation"

    if UNSOURCED.match(cite):
        return f"marked Unsourced ({cite})"

    m = CITE_SPEC.match(cite)
    if m:
        if spec_sections is None:
            return (f"cannot resolve '{cite}': {SPEC_SECTIONS.relative_to(REPO_ROOT)} "
                    "does not exist (plan 01-03 transcribes it)")
        if m.group(1) not in spec_sections:
            return (f"unknown ML-KEM Braid section '§{m.group(1)}' "
                    f"(not in {SPEC_SECTIONS.relative_to(REPO_ROOT)})")
        return None

    m = CITE_SCKA.match(cite)
    if m:
        ref = re.sub(r"\s+", " ", m.group(1))
        if scka_refs is None:
            return (f"cannot resolve '{cite}': {SCKA_REFS.relative_to(REPO_ROOT)} "
                    "does not exist (plan 01-03 transcribes it)")
        if ref not in scka_refs:
            return f"unknown SCKA reference '{ref}' (not in {SCKA_REFS.relative_to(REPO_ROOT)})"
        return None

    m = CITE_SRC.match(cite)
    if m:
        rel, start, end = m.group(1), int(m.group(2)), m.group(3)
        path = REPO_ROOT / rel
        if not path.is_file():
            return f"no such file '{rel}'"
        total = len(path.read_text(errors="replace").splitlines())
        last = int(end) if end else start
        if start < 1 or last < start:
            return f"'{rel}:{m.group(2)}{'-' + end if end else ''}' is not a line range"
        if last > total:
            return f"'{rel}' has {total} lines; citation reaches line {last}"
        return None

    return (f"unparseable citation '{cite}' - expected 'Spec §x.y', "
            "'SCKA Def./Fig. n' or 'src/path.rs:a[-b]' "
            "(a Spqr/Specs path belongs on an Evidence: line)")


def main() -> int:
    ap = argparse.ArgumentParser(
        prog="check-provenance.py",
        description="Gate 5: resolve every Source: citation in the SPQR property catalog.")
    ap.add_argument("--verbose", action="store_true",
                    help="print every row and its citations, not just the failures")
    ap.add_argument("--row", metavar="ID",
                    help="check a single property, e.g. --row PROP-35")
    ap.add_argument("--catalog", metavar="PATH", default=str(CATALOG),
                    help="catalog path (default: docs/spqr-properties.md)")
    args = ap.parse_args()

    catalog = Path(args.catalog)
    if not catalog.is_file():
        print(f"check-provenance.py: no catalog at {catalog}", file=sys.stderr)
        return 2

    text = catalog.read_text(errors="replace")
    registry, index_ids = build_registry(text, args.verbose)

    deviations = {i for i in registry if DEVIATION_ID.match(i)}
    non_deviation = set(registry) - deviations
    index_non_aggregate = {i for i in index_ids if not INDEX_AGGREGATE.match(i)}
    index_aggregate = {i for i in index_ids if INDEX_AGGREGATE.match(i)}

    print(f"Registry entries: {len(registry)} "
          f"({len(non_deviation)} non-deviation, {len(deviations)} deviation)")
    print(f"§12 index rows:   {len(index_ids)} "
          f"({len(index_non_aggregate)} individual, {len(index_aggregate)} aggregate)")
    print("The two numbers are not expected to be equal: §12 collapses D1-D5 "
          "into one aggregate entry.  ID-set agreement is what is checked.")

    structural: list[str] = []

    if len(non_deviation) < MIN_NON_DEVIATION_ENTRIES:
        structural.append(
            f"registry holds only {len(non_deviation)} non-deviation entries, "
            f"below the floor of {MIN_NON_DEVIATION_ENTRIES} - enumeration is incomplete")

    missing_from_index = sorted(non_deviation - index_non_aggregate)
    missing_from_registry = sorted(index_non_aggregate - non_deviation)
    for i in missing_from_index:
        structural.append(f"{i} is a catalog row but is absent from the §12 index")
    for i in missing_from_registry:
        structural.append(f"{i} is in the §12 index but no catalog row was enumerated for it")
    if deviations and not index_aggregate:
        structural.append("the §11 deviations have no aggregate entry (D1-D5) in the §12 index")
    if index_aggregate and not deviations:
        structural.append("the §12 index has a D1-D5 aggregate entry but no §11 deviation row "
                          "was enumerated")

    if args.row:
        want = re.sub(r"\s+", "", args.row)
        if want not in registry:
            print(f"check-provenance.py: no catalog row with ID {args.row!r}", file=sys.stderr)
            return 2
        rows = {want: registry[want]}
        structural = []   # a single-row query does not adjudicate the whole index
    else:
        rows = registry

    spec_sections = load_reference_list(SPEC_SECTIONS)
    scka_refs = load_reference_list(SCKA_REFS)
    if spec_sections is None:
        print(f"note: {SPEC_SECTIONS.relative_to(REPO_ROOT)} does not exist; every "
              "`Spec §x.y` citation will fail (plan 01-03 transcribes it)")
    if scka_refs is None:
        print(f"note: {SCKA_REFS.relative_to(REPO_ROOT)} does not exist; every "
              "`SCKA Def./Fig. n` citation will fail (plan 01-03 transcribes it)")

    failures: list[tuple[str, str, str]] = []   # (id, where, reason)
    for ident in sorted(rows):
        row = rows[ident]
        if not row.sources:
            failures.append((ident, row.where, "no `Source:` field"))
            continue
        cites = [c for s in row.sources for c in s.split(";") if c.strip()]
        if not cites:
            failures.append((ident, row.where, "`Source:` field is empty"))
            continue
        row_failed = False
        for cite in cites:
            reason = check_citation(cite, spec_sections, scka_refs)
            if reason:
                failures.append((ident, row.where, reason))
                row_failed = True
            elif args.verbose:
                print(f"  ok      {ident:<14} {cite.strip()}")
        if args.verbose and not row_failed:
            print(f"  PASS    {ident:<14} {'; '.join(c.strip() for c in cites)}")
        if args.verbose and row.evidence:
            print(f"  (evidence, not gated) {ident}: {'; '.join(row.evidence)}")

    if structural:
        print(f"\nStructural failures ({len(structural)}):")
        for s in structural:
            print(f"  - {s}")

    if failures:
        width = max(len(i) for i, _, _ in failures)
        print(f"\nCitation failures ({len(failures)}) in "
              f"{len({i for i, _, _ in failures})} row(s):")
        print(f"  {'ID'.ljust(width)}  WHERE                        REASON")
        for ident, where, reason in failures:
            print(f"  {ident.ljust(width)}  {where:<28} {reason}")

    if structural or failures:
        print(f"\nGATE 5 FAIL: {len(structural)} structural, {len(failures)} citation failure(s).")
        return 1

    print(f"\nGATE 5 PASS: every one of {len(rows)} row(s) has a resolving Source: citation.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
