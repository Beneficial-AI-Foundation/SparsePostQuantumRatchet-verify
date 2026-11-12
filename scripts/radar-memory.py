#!/usr/bin/env python3
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import statistics
import subprocess

# Project library roots in lakefile.toml; includes tests and executable modules.
ROOTS = ("Spqr", "SrcTranslated", "HeaderLinter", "Utils", "Tests")


def discover_modules(repo):
    files = set()
    for root in ROOTS:
        entry = repo / f"{root}.lean"
        if entry.is_file():
            files.add(entry)
        files.update((repo / root).rglob("*.lean"))
    return sorted(".".join(f.relative_to(repo).with_suffix("").parts) for f in files)


def input_files(repo):
    """All project sources and build configuration that affect a Lean check."""
    sources = [repo / (module.replace(".", "/") + ".lean")
               for module in discover_modules(repo)]
    return sources + [repo / name for name in
                      ("lakefile.toml", "lake-manifest.json", "lean-toolchain")]


def snapshot_inputs(repo, logs, files):
    hashes = {}
    for path in files:
        relative = path.relative_to(repo)
        content = path.read_bytes()
        hashes[str(relative)] = hashlib.sha256(content).hexdigest()
        snapshot = logs / "inputs" / relative
        snapshot.parent.mkdir(parents=True, exist_ok=True)
        snapshot.write_bytes(content)
    (logs / "input-hashes.json").write_text(json.dumps(hashes, indent=2) + "\n")
    return hashes


def check_inputs(repo, hashes):
    current = {}
    for path in input_files(repo):
        relative = str(path.relative_to(repo))
        current[relative] = hashlib.sha256(path.read_bytes()).hexdigest()
    if current != hashes:
        changed = sorted(set(current) ^ set(hashes) |
                         {name for name in current.keys() & hashes.keys()
                          if current[name] != hashes[name]})
        raise SystemExit("project inputs changed during benchmark: " + ", ".join(changed))


def main():
    parser = argparse.ArgumentParser(description="Radar-compatible per-module Lean RSS benchmark")
    parser.add_argument("repo", type=Path)
    parser.add_argument("output", type=Path, nargs="?")
    parser.add_argument("--modules-file", type=Path, help="one module per line; default: all project libraries")
    parser.add_argument("--trials", type=int, choices=(1, 3), default=3)
    parser.add_argument("--list-modules", action="store_true")
    args = parser.parse_args()
    repo = args.repo.resolve()
    available = discover_modules(repo)
    modules = available if args.modules_file is None else [
        line.strip() for line in args.modules_file.read_text().splitlines() if line.strip()
    ]
    if not modules or len(modules) != len(set(modules)) or set(modules) - set(available):
        parser.error("module list must be nonempty, unique, and contain only project modules")
    if args.list_modules:
        print("\n".join(modules))
        return
    if args.output is None:
        parser.error("output is required unless --list-modules is used")
    output = args.output.resolve()
    if output.exists():
        raise SystemExit("output must not already exist; use a fresh path")
    logs = output.with_suffix(".logs")
    logs.mkdir(parents=True, exist_ok=False)
    (logs / "modules.txt").write_text("\n".join(modules) + "\n")
    (logs / "config.json").write_text(json.dumps({"trials": args.trials, "threads": 1,
                                                "warmups": 1, "roots": ROOTS}))
    print(f"raw logs: {logs}", flush=True)
    env = dict(os.environ, LC_ALL="C")

    def run(command, label):
        with (logs / f"{label}.log").open("w") as log:
            subprocess.run(command, cwd=repo, env=env, stdout=log,
                           stderr=subprocess.STDOUT, check=True)

    run(["git", "rev-parse", "HEAD"], "commit")
    run(["git", "status", "--short"], "status")
    run(["git", "diff", "--binary", "HEAD"], "working-tree")
    shutil.copy2(__file__, logs / "benchmark.py")
    run(["lake", "env", "lean", "--version"], "lean-version")
    run(["uname", "-a"], "machine")
    input_hashes = snapshot_inputs(repo, logs, input_files(repo))
    rows = []
    for module in modules:
        source = module.replace(".", "/") + ".lean"
        run(["lake", "build", module], f"{module}-build")
        lean = ["lake", "env", "lean", "-j1", source]
        run(lean, f"{module}-warmup")
        rss, elapsed = [], []
        for trial in range(1, args.trials + 1):
            label = f"{module}-{trial}"
            metrics = logs / f"{label}.metrics"
            run(["/usr/bin/time", "-f", "%M %e", "-o", str(metrics),
                 *lean], label)
            kib, seconds = metrics.read_text().split()
            rss.append(int(kib) * 1024)
            elapsed.append(float(seconds))
            print(f"{label}: rss_B={rss[-1]} elapsed_s={elapsed[-1]}", flush=True)
        for metric, value, unit in [
            ("peak-rss-median", statistics.median(rss), "B"),
            ("peak-rss-max", max(rss), "B"),
            ("elapsed-median", statistics.median(elapsed), "s"),
        ]:
            prefix = "memory-j1" if args.trials == 3 else "memory-scan-j1"
            rows.append({"metric": f"{prefix}/module/{module}//{metric}",
                         "value": value, "unit": unit})
    check_inputs(repo, input_hashes)
    # Only emit measurements after every module has succeeded.
    with output.open("x") as stream:
        for row in rows:
            stream.write(json.dumps(row) + "\n")


if __name__ == "__main__":
    main()
