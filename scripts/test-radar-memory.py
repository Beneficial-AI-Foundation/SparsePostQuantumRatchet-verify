#!/usr/bin/env python3
"""Smoke checks for a complete run and for a source change during a run."""

import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest


SCRIPT = Path(__file__).with_name("radar-memory.py")


class RadarMemoryTest(unittest.TestCase):
    def run_benchmark(self, mutate):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            repo = root / "repo"
            repo.mkdir()
            (repo / "Spqr.lean").write_text("def example := 1\n")
            (repo / "lakefile.toml").write_text('name = "Spqr"\n')
            (repo / "lake-manifest.json").write_text("{}\n")
            (repo / "lean-toolchain").write_text("leanprover/lean4:test\n")
            subprocess.run(["git", "init", "-q", str(repo)], check=True)
            subprocess.run(["git", "-C", str(repo), "-c", "user.name=Test",
                            "-c", "user.email=test@example.com", "commit", "-q",
                            "--allow-empty", "-m", "fixture"], check=True)
            bin_dir = root / "bin"
            bin_dir.mkdir()
            lake = bin_dir / "lake"
            lake.write_text("#!/bin/sh\n"
                            "if [ \"$1\" = lean ] && "
                            "[ \"$MUTATE_SOURCE\" = 1 ]; then\n"
                            "  printf 'def changed := 2\\n' >> Spqr.lean\n"
                            "fi\n")
            lake.chmod(0o755)
            output = root / "result.jsonl"
            env = dict(os.environ, PATH=f"{bin_dir}:{os.environ['PATH']}",
                       MUTATE_SOURCE="1" if mutate else "0")
            result = subprocess.run(["python3", str(SCRIPT), str(repo), str(output),
                                     "--trials", "1"], env=env, text=True,
                                    capture_output=True)
            if mutate:
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("inputs changed", result.stderr)
                self.assertFalse(output.exists())
            else:
                self.assertEqual(result.returncode, 0, result.stderr)
                rows = [json.loads(line) for line in output.read_text().splitlines()]
                self.assertEqual(len(rows), 3)
                self.assertTrue((root / "result.logs" / "inputs" / "Spqr.lean").exists())

    def test_complete_run(self):
        self.run_benchmark(False)

    def test_mutated_source_rejected(self):
        self.run_benchmark(True)


if __name__ == "__main__":
    unittest.main()
