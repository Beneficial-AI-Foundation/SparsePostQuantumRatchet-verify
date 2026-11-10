#!/usr/bin/env python3
"""Create a reproducible, dependency-safe generation/test file split."""

from __future__ import annotations

import argparse
import hashlib
import heapq
import json
import random
import sys
from pathlib import Path
from typing import Any


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Split Lean source files using a probe-lean dependency graph and "
            "emit only definitions. The generation file partition is "
            "dependency-closed, so it cannot depend on a held-out test file."
        )
    )
    parser.add_argument(
        "--input",
        type=Path,
        default=Path(".verilib/probes/lean_extract.json"),
        help="probe-lean extract JSON (default: %(default)s)",
    )
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=Path("data/probe-lean-split"),
        help="directory for definition records, file lists, and manifest.json",
    )
    parser.add_argument(
        "--generation-ratio",
        type=float,
        default=0.5,
        help="target fraction of definitions assigned to generation (default: %(default)s)",
    )
    parser.add_argument(
        "--seed",
        type=int,
        default=20261110,
        help="random seed (default: %(default)s)",
    )
    return parser.parse_args()


def strongly_connected_components(
    nodes: list[str], dependencies: dict[str, list[str]]
) -> tuple[list[list[str]], dict[str, int]]:
    """Tarjan SCC decomposition of declaration -> dependency edges."""
    sys.setrecursionlimit(max(10_000, len(nodes) * 2))
    next_index = 0
    indexes: dict[str, int] = {}
    lowlinks: dict[str, int] = {}
    stack: list[str] = []
    on_stack: set[str] = set()
    components: list[list[str]] = []

    def visit(node: str) -> None:
        nonlocal next_index
        indexes[node] = next_index
        lowlinks[node] = next_index
        next_index += 1
        stack.append(node)
        on_stack.add(node)

        for dependency in dependencies[node]:
            if dependency not in indexes:
                visit(dependency)
                lowlinks[node] = min(lowlinks[node], lowlinks[dependency])
            elif dependency in on_stack:
                lowlinks[node] = min(lowlinks[node], indexes[dependency])

        if lowlinks[node] != indexes[node]:
            return
        component: list[str] = []
        while True:
            member = stack.pop()
            on_stack.remove(member)
            component.append(member)
            if member == node:
                break
        components.append(sorted(component))

    for node in nodes:
        if node not in indexes:
            visit(node)

    component_of = {
        node: component_id
        for component_id, component in enumerate(components)
        for node in component
    }
    return components, component_of


def randomized_dependency_order(
    components: list[list[str]],
    component_of: dict[str, int],
    dependencies: dict[str, list[str]],
    seed: int,
) -> list[int]:
    """Return SCCs in a seeded random topological order, dependencies first."""
    users: list[set[int]] = [set() for _ in components]
    unmet_dependencies = [0] * len(components)
    for node, node_dependencies in dependencies.items():
        user_component = component_of[node]
        for dependency in node_dependencies:
            dependency_component = component_of[dependency]
            if dependency_component == user_component:
                continue
            if user_component not in users[dependency_component]:
                users[dependency_component].add(user_component)
                unmet_dependencies[user_component] += 1

    rng = random.Random(seed)
    priorities = [rng.random() for _ in components]
    ready = [
        (priorities[component_id], component_id)
        for component_id, count in enumerate(unmet_dependencies)
        if count == 0
    ]
    heapq.heapify(ready)
    order: list[int] = []
    while ready:
        _, component_id = heapq.heappop(ready)
        order.append(component_id)
        for user in users[component_id]:
            unmet_dependencies[user] -= 1
            if unmet_dependencies[user] == 0:
                heapq.heappush(ready, (priorities[user], user))

    if len(order) != len(components):
        raise RuntimeError("internal error: condensed dependency graph is cyclic")
    return order


def record(atom_id: str, atom: dict[str, Any], partition: str) -> dict[str, Any]:
    return {
        "id": atom_id,
        "partition": partition,
        "display_name": atom.get("display-name"),
        "kind": atom.get("kind"),
        "module": atom.get("code-module"),
        "path": atom.get("code-path"),
        "lines": atom.get("code-text"),
        "dependencies": atom.get("dependencies", []),
    }


def write_jsonl(path: Path, rows: list[dict[str, Any]]) -> None:
    with path.open("w", encoding="utf-8") as output:
        for row in rows:
            output.write(json.dumps(row, sort_keys=True, separators=(",", ":")) + "\n")


def write_lines(path: Path, lines: list[str]) -> None:
    path.write_text("".join(f"{line}\n" for line in lines), encoding="utf-8")


def main() -> None:
    args = parse_args()
    if not 0.0 < args.generation_ratio < 1.0:
        raise SystemExit("--generation-ratio must be strictly between 0 and 1")

    input_bytes = args.input.read_bytes()
    extraction = json.loads(input_bytes)
    if extraction.get("schema") != "probe-lean/extract":
        raise SystemExit(f"{args.input} is not a probe-lean extract")

    all_atoms: dict[str, dict[str, Any]] = extraction["data"]

    # Hidden declarations (for example projections) still contribute edges to
    # the file graph. They are not emitted as definition-generation examples.
    graph_atoms = {
        atom_id: atom
        for atom_id, atom in all_atoms.items()
        if atom.get("is-in-package") is True
        and atom.get("is-relevant") is True
        and atom.get("is-ignored") is False
        and atom.get("code-path") is not None
    }
    definitions = {
        atom_id: atom
        for atom_id, atom in graph_atoms.items()
        if atom.get("kind") == "def" and atom.get("is-hidden") is False
    }
    atom_to_file = {
        atom_id: atom["code-path"] for atom_id, atom in graph_atoms.items()
    }
    nodes = sorted(set(atom_to_file.values()))
    node_set = set(nodes)
    dependencies: dict[str, list[str]] = {path: [] for path in nodes}
    for atom_id, atom in graph_atoms.items():
        source_file = atom_to_file[atom_id]
        for dependency in atom.get("dependencies", []):
            dependency_file = atom_to_file.get(dependency)
            if dependency_file is not None and dependency_file != source_file:
                dependencies[source_file].append(dependency_file)
    dependencies = {
        path: sorted(set(path_dependencies) & node_set)
        for path, path_dependencies in dependencies.items()
    }

    components, component_of = strongly_connected_components(nodes, dependencies)
    component_order = randomized_dependency_order(
        components, component_of, dependencies, args.seed
    )

    # Every prefix of this SCC order is dependency-closed. Choose the legal cut
    # nearest the requested definition count while keeping files and SCCs whole.
    target = len(definitions) * args.generation_ratio
    cumulative = 0
    cuts: list[tuple[float, int, int]] = []
    for position, component_id in enumerate(component_order[:-1], start=1):
        cumulative += sum(
            1
            for atom in definitions.values()
            if atom["code-path"] in components[component_id]
        )
        cuts.append((abs(cumulative - target), position, cumulative))
    if not cuts:
        raise SystemExit("at least two dependency components are required for a split")
    _, cut_position, generation_definition_count = min(cuts)

    generation_components = set(component_order[:cut_position])
    generation_files = {
        path
        for path, component_id in component_of.items()
        if component_id in generation_components
    }
    test_files = node_set - generation_files
    ordered_files = [
        path for component_id in component_order for path in components[component_id]
    ]
    file_position = {path: position for position, path in enumerate(ordered_files)}
    generation_ids = sorted(
        (
            atom_id
            for atom_id, atom in definitions.items()
            if atom["code-path"] in generation_files
        ),
        key=lambda atom_id: (file_position[definitions[atom_id]["code-path"]], atom_id),
    )
    test_ids = sorted(
        (
            atom_id
            for atom_id, atom in definitions.items()
            if atom["code-path"] in test_files
        ),
        key=lambda atom_id: (file_position[definitions[atom_id]["code-path"]], atom_id),
    )

    generation_to_test_edges = sum(
        dependency in test_files
        for path in generation_files
        for dependency in dependencies[path]
    )
    if generation_to_test_edges:
        raise RuntimeError("generation file partition is not dependency-closed")
    test_to_generation_edges = sum(
        dependency in generation_files
        for path in test_files
        for dependency in dependencies[path]
    )

    args.output_dir.mkdir(parents=True, exist_ok=True)
    write_jsonl(
        args.output_dir / "generation.jsonl",
        [record(atom_id, definitions[atom_id], "generation") for atom_id in generation_ids],
    )
    write_jsonl(
        args.output_dir / "test.jsonl",
        [record(atom_id, definitions[atom_id], "test") for atom_id in test_ids],
    )
    write_lines(
        args.output_dir / "generation-files.txt",
        [path for path in ordered_files if path in generation_files],
    )
    write_lines(
        args.output_dir / "test-files.txt",
        [path for path in ordered_files if path in test_files],
    )
    manifest = {
        "schema": "probe-lean/dependency-split",
        "schema_version": "1.0",
        "source": str(args.input),
        "source_sha256": hashlib.sha256(input_bytes).hexdigest(),
        "seed": args.seed,
        "requested_generation_ratio": args.generation_ratio,
        "actual_generation_file_ratio": len(generation_files) / len(nodes),
        "actual_generation_definition_ratio": generation_definition_count
        / len(definitions),
        "filters": {
            "is_in_package": True,
            "is_relevant": True,
            "is_hidden": False,
            "is_ignored": False,
            "requires_code_path": True,
            "kind": "def",
        },
        "counts": {
            "eligible_definitions": len(definitions),
            "generation_definitions": len(generation_ids),
            "test_definitions": len(test_ids),
            "eligible_files": len(nodes),
            "generation_files": len(generation_files),
            "test_files": len(test_files),
            "strongly_connected_components": len(components),
            "cyclic_components": sum(len(component) > 1 for component in components),
        },
        "dependency_edges": {
            "generation_to_test": generation_to_test_edges,
            "test_to_generation": test_to_generation_edges,
        },
        "ordering": "seeded random topological order of file-dependency SCCs",
    }
    (args.output_dir / "manifest.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(
        f"Wrote {len(generation_ids)} generation definitions from "
        f"{len(generation_files)} files and {len(test_ids)} test definitions "
        f"from {len(test_files)} files to {args.output_dir}"
    )


if __name__ == "__main__":
    main()
