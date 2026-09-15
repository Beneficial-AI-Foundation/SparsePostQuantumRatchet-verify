#!/usr/bin/env bash
# Local runner for the five repository verification gates (INFRA-03).
#
#   1  lake build          - no warning other than `declaration uses 'sorry'`
#   2  lake exe runLinter  - no `error:` in the hand-written `Spqr` library
#   3  Audit.lean          - axiom audit runs (3a) and the sorry delta is empty (3b)
#   4  #print axioms       - every audited theorem's axiom closure is on the allowlist
#   5  provenance          - every `Source:` citation in the catalog resolves
#
# Every selected gate runs; each prints `GATE n: PASS|FAIL|SKIP`.  A gate that
# could not run prints SKIP with a reason and **counts as a failure** - the
# script never reports an unrun gate as a pass (threat T-1-01).
#
# Gates 1 and 2 issue byte-for-byte the commands `.github/workflows/lean.yml`
# uses (lines 47 and 57) so that a green local run means a green CI run.
#
# See `scripts/README.md` for flags, env vars and the `.gate-cache/` layout.

set -euo pipefail

export LEAN_ABORT_ON_PANIC=1

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

# ─── Defaults, overridable by env then by flag ────────────────────────────────

GATES="1,2,3,4,5"
BASELINE_REF="${SPQR_BASELINE_REF:-origin/main}"
BASELINE_DIR="${SPQR_BASELINE_WORKTREE:-$(cd "$REPO_ROOT/.." && pwd)/spqr-gate-baseline}"
CACHE_DIR="${SPQR_GATE_CACHE:-$REPO_ROOT/.gate-cache}"
SKIP_BASELINE=false
REFRESH_BASELINE=false
ALLOW_SORRY=()
AXIOM_TARGETS=()
ALLOWLIST="${SPQR_AXIOM_ALLOWLIST:-$REPO_ROOT/scripts/axiom-allowlist.txt}"

usage() {
  cat <<'USAGE'
Usage: scripts/check-gates.sh [options]

Runs the five repository verification gates and prints a per-gate verdict.
Exits non-zero if any selected gate is FAIL or SKIP.

Gates:
  1  build          `lake build --no-ansi`, no warning other than sorry
  2  lint           `lake exe runLinter Spqr`, no `error:`
  3  audit+delta    3a `lake env lean scripts/Audit.lean`
                    3b sorry delta vs an origin/main baseline (no new specs sorries)
  4  axioms         `#print axioms` closure vs scripts/axiom-allowlist.txt
  5  provenance     scripts/check-provenance.py over docs/spqr-properties.md

Options:
  --gates LIST          Comma-separated subset, e.g. --gates 1,2 (default: 1,2,3,4,5)
  --allow-sorry THM     Permit `sorryAx` in THM's closure in gate 4 (repeatable)
  --axiom-target THM    Check THM in gate 4 (repeatable).  With no --axiom-target,
                        gate 4 checks every theorem/axiom declared under
                        Spqr/Specs/**; if that yields nothing it reports SKIP
  --allowlist FILE      Gate-4 allowlist (default: scripts/axiom-allowlist.txt)
  --baseline-ref REF    Git ref for the gate-3b baseline (default: origin/main)
  --baseline-dir DIR    Worktree path for the baseline build
                        (default: ../spqr-gate-baseline)
  --skip-baseline       Do not build a baseline; gate 3b reports SKIP (a failure)
  --no-delta            Alias for --skip-baseline
  --refresh-baseline    Rebuild the cached baseline manifest even if present
  -h, --help            This message

Environment:
  SPQR_BASELINE_REF        same as --baseline-ref
  SPQR_BASELINE_WORKTREE   same as --baseline-dir
  SPQR_GATE_CACHE          cache directory (default: .gate-cache)

Gate 5 needs no build: `--gates 5` never invokes lake.
USAGE
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --gates)           GATES="${2:?--gates needs a value}"; shift 2 ;;
    --gates=*)         GATES="${1#*=}"; shift ;;
    --allow-sorry)     ALLOW_SORRY+=("${2:?--allow-sorry needs a theorem name}"); shift 2 ;;
    --allow-sorry=*)   ALLOW_SORRY+=("${1#*=}"); shift ;;
    --axiom-target)    AXIOM_TARGETS+=("${2:?--axiom-target needs a theorem name}"); shift 2 ;;
    --axiom-target=*)  AXIOM_TARGETS+=("${1#*=}"); shift ;;
    --allowlist)       ALLOWLIST="${2:?--allowlist needs a path}"; shift 2 ;;
    --allowlist=*)     ALLOWLIST="${1#*=}"; shift ;;
    --baseline-ref)    BASELINE_REF="${2:?--baseline-ref needs a value}"; shift 2 ;;
    --baseline-ref=*)  BASELINE_REF="${1#*=}"; shift ;;
    --baseline-dir)    BASELINE_DIR="${2:?--baseline-dir needs a value}"; shift 2 ;;
    --baseline-dir=*)  BASELINE_DIR="${1#*=}"; shift ;;
    --skip-baseline|--no-delta) SKIP_BASELINE=true; shift ;;
    --refresh-baseline) REFRESH_BASELINE=true; shift ;;
    -h|--help)         usage; exit 0 ;;
    *) echo "check-gates.sh: unknown option '$1'" >&2; usage >&2; exit 2 ;;
  esac
done

# Reject an unknown or empty gate list rather than running nothing and
# reporting success - a vacuous "all gates PASS" is threat T-1-01.
IFS=',' read -r -a _requested_gates <<< "$GATES"
if [[ "${#_requested_gates[@]}" -eq 0 ]]; then
  echo "check-gates.sh: --gates selected no gate" >&2
  exit 2
fi
for _g in "${_requested_gates[@]}"; do
  case "$_g" in
    1|2|3|4|5) ;;
    *) echo "check-gates.sh: --gates: unknown gate '$_g' (valid: 1 2 3 4 5)" >&2; exit 2 ;;
  esac
done

# ─── Verdict accumulator ──────────────────────────────────────────────────────
#
# GATE_STATUS[n] is PASS, FAIL or SKIP.  Only PASS counts as success.

declare -A GATE_STATUS=()
declare -A GATE_REASON=()

selected() {
  case ",$GATES," in
    *",$1,"*) return 0 ;;
    *) return 1 ;;
  esac
}

pass() { GATE_STATUS["$1"]="PASS"; GATE_REASON["$1"]="${2:-}"; }
fail() { GATE_STATUS["$1"]="FAIL"; GATE_REASON["$1"]="${2:-}"; }
skip() { GATE_STATUS["$1"]="SKIP"; GATE_REASON["$1"]="${2:-}"; }

have_lake() { command -v lake >/dev/null 2>&1; }

banner() { printf '\n=== %s ===\n' "$1"; }

# ─── Gate 1: build warnings ───────────────────────────────────────────────────

gate_1() {
  banner "GATE 1: build warnings (lean.yml:47-52)"
  if ! have_lake; then
    skip 1 "lake not on PATH"
    return
  fi

  # errexit off so that a failing `lake build` does not abort the gate before
  # the warning filter runs; pipefail stays on so that build_rc is lake's
  # status and not tee's.  CI masks lake's status here (no pipefail in a
  # GitHub `run:` block); locally a non-zero lake is a FAIL.
  local build_rc=0
  set +e
  lake build --no-ansi 2>&1 | tee /tmp/lake-build.log
  build_rc=$?
  set -e

  local warned=false
  if grep 'warning:' /tmp/lake-build.log | grep -qv 'declaration uses .sorry'; then
    warned=true
    echo "FAIL: non-sorry warnings found:"
    grep 'warning:' /tmp/lake-build.log | grep -v 'declaration uses .sorry'
  fi

  if [[ "$build_rc" -ne 0 && "$warned" == true ]]; then
    fail 1 "lake build exited $build_rc and produced non-sorry warnings"
  elif [[ "$build_rc" -ne 0 ]]; then
    fail 1 "lake build exited $build_rc"
  elif [[ "$warned" == true ]]; then
    fail 1 "non-sorry build warnings"
  else
    pass 1
  fi
}

# ─── Gate 2: lint ─────────────────────────────────────────────────────────────

gate_2() {
  banner "GATE 2: lint hand-written Spqr (lean.yml:57-62)"
  if ! have_lake; then
    skip 2 "lake not on PATH"
    return
  fi

  # Lint ONLY the hand-written `Spqr` library.  `|| true` is CI's: runLinter
  # exits non-zero when it reports lints, and the `error:` grep is the verdict.
  set +e
  lake exe runLinter Spqr 2>&1 | tee /tmp/lake-lint.log || true
  set -e

  if grep -q 'error:' /tmp/lake-lint.log; then
    echo "FAIL: lint errors in hand-written code:"
    grep 'error:' /tmp/lake-lint.log
    fail 2 "runLinter reported error:"
  else
    pass 2
  fi
}

# ─── Gate 3a: axiom audit runs ────────────────────────────────────────────────

gate_3a() {
  banner "GATE 3a: axiom audit (lake env lean scripts/Audit.lean)"
  if ! have_lake; then
    skip 3a "lake not on PATH"
    return 1
  fi
  local rc=0
  set +e
  lake env lean scripts/Audit.lean 2>&1 | tee /tmp/lake-audit.log
  rc=$?
  set -e
  if [[ "$rc" -ne 0 ]]; then
    fail 3a "Audit.lean exited $rc"
    return 1
  fi
  if [[ ! -f "$REPO_ROOT/sorry-manifest.txt" ]]; then
    fail 3a "Audit.lean did not write sorry-manifest.txt"
    return 1
  fi
  pass 3a
  return 0
}

# ─── Gate 3b: sorry delta against a SHA-keyed origin/main baseline ────────────
#
# The repo-root `sorry-manifest.txt` is gitignored, generated and stale; it is
# never used as the *baseline* (threat T-1-05).  The two manifest paths here are
#   - "$CACHE_DIR/sorry-manifest-<base-sha>.txt"  the baseline, keyed by SHA so
#     it self-invalidates when the ref moves (CI keys its cache the same way,
#     lean.yml:80-84), and
#   - the head manifest, regenerated by gate 3a in this very run.
#
# Local policy is stricter than CI's: CI reports the delta without failing
# (sorry-delta-comment.yml:43 does not set SORRY_FAIL_ON_NEW); here
# SORRY_FAIL_ON_NEW=true makes a new specs sorry a FAIL.

build_baseline_manifest() {
  local base_sha="$1" out="$2"
  echo "Cold baseline build for $BASELINE_REF ($base_sha) - this takes a while."
  if [[ ! -d "$BASELINE_DIR" ]]; then
    git -C "$REPO_ROOT" worktree add --detach "$BASELINE_DIR" "$base_sha" || return 1
  else
    git -C "$BASELINE_DIR" checkout --detach "$base_sha" || return 1
  fi
  (
    cd "$BASELINE_DIR" || exit 1
    lake exe cache get || true     # mathlib oleans; without this mathlib builds from source
    lake build --no-ansi || exit 1
    lake env lean scripts/Audit.lean || exit 1
  ) || return 1
  mkdir -p "$(dirname "$out")"
  cp "$BASELINE_DIR/sorry-manifest.txt" "$out"
}

gate_3b() {
  banner "GATE 3b: sorry delta vs $BASELINE_REF"
  if [[ "$SKIP_BASELINE" == true ]]; then
    skip 3b "--skip-baseline given; no delta computed"
    return
  fi
  if ! have_lake; then
    skip 3b "lake not on PATH"
    return
  fi
  local head_manifest="$REPO_ROOT/sorry-manifest.txt"
  if [[ ! -f "$head_manifest" ]]; then
    skip 3b "no head manifest; gate 3a must run first"
    return
  fi

  local base_sha
  git -C "$REPO_ROOT" fetch --quiet origin main 2>/dev/null || true
  if ! base_sha="$(git -C "$REPO_ROOT" rev-parse --verify --quiet "$BASELINE_REF^{commit}")"; then
    skip 3b "cannot resolve $BASELINE_REF"
    return
  fi

  local base_manifest="$CACHE_DIR/sorry-manifest-$base_sha.txt"
  if [[ "$REFRESH_BASELINE" == true ]]; then
    rm -f "$base_manifest"
  fi
  if [[ ! -f "$base_manifest" ]]; then
    if ! build_baseline_manifest "$base_sha" "$base_manifest"; then
      skip 3b "baseline build for $base_sha failed"
      return
    fi
  else
    echo "Using cached baseline manifest: $base_manifest"
  fi

  local rc=0
  set +e
  SORRY_FAIL_ON_NEW=true python3 "$REPO_ROOT/scripts/sorry-diff.py" \
    "$base_manifest" "$head_manifest"
  rc=$?
  set -e
  if [[ "$rc" -ne 0 ]]; then
    fail 3b "new sorry-tainted declarations in Spqr.Specs.*"
  else
    pass 3b
  fi
}

# ─── Gate 4: #print axioms against scripts/axiom-allowlist.txt ────────────────
#
# Two halves, both of which must hold:
#
#   4A  the allowlist itself still resolves against the tree - every non-builtin
#       entry is an `axiom` or `opaque` declaration that exists.  Aeneas wraps a
#       long name onto the line *after* the keyword (FunsExternal.lean:3687-3688,
#       and 119 axioms in that file have the shape), so a `^axiom +NAME` matcher
#       returns 1 on a correct entry.  The matcher below is whitespace- and
#       newline-insensitive.  If an entry fails here, fix the matcher or the
#       tree - never delete, shorten or rename the entry: the allowlist is the
#       trusted base, the predicate is only tooling.
#
#   4B  every target's `#print axioms` closure is a subset of the allowlist.
#       A scratch file under `mktemp -d` (mode 0700, removed by a trap, threat
#       T-1-14) holds `import Spqr` plus one `#print axioms <name>` per target.
#
# 4B fails, and never passes, on each of:
#   - `unknown identifier` / `unknown constant` - a typo'd target
#   - a target that produced no report line at all (asserted per target by name)
#   - a `depends on axioms: [` whose `]` never arrives ("malformed" report)
#   - `sorryAx` in a target not named by `--allow-sorry`
# A wrapped axiom list is *not* a failure: Lean soft-breaks the list with
# `"," ++ Format.line` (Lean/Message.lean:417), so the parser accumulates
# continuation lines up to the closing `]` before splitting on `,`.

validate_allowlist() {
  python3 - "$ALLOWLIST" "$REPO_ROOT" <<'PYVALIDATE'
import re, sys, pathlib

allowlist_path, repo_root = pathlib.Path(sys.argv[1]), pathlib.Path(sys.argv[2])
BUILTINS = {"propext", "Classical.choice", "Quot.sound"}

if not allowlist_path.exists():
    print(f"FAIL: allowlist not found at {allowlist_path}")
    sys.exit(1)

entries = []
for raw in allowlist_path.read_text().splitlines():
    line = raw.split("#", 1)[0].strip()       # entries carry a trailing `# file:line`
    if line:
        entries.append(line)

sources = sorted(repo_root.glob("SrcTranslated/*.lean")) + \
          sorted(repo_root.rglob("Spqr/**/*.lean"))
texts = {p: p.read_text(errors="replace") for p in sources}

def locate(name):
    """Find `axiom|opaque NAME`, tolerating a newline between keyword and name
    and tolerating NAME being declared inside `namespace <stripped prefix>`."""
    parts = name.split(".")
    for drop in range(len(parts)):
        prefix, suffix = ".".join(parts[:drop]), ".".join(parts[drop:])
        pat = re.compile(r"(?m)^(?:axiom|opaque)\s+" + re.escape(suffix) + r"(?![\w.])")
        for path, text in texts.items():
            m = pat.search(text)
            if not m:
                continue
            if prefix and not re.search(r"(?m)^namespace\s+" + re.escape(prefix) + r"\s*$", text):
                continue
            kw_line = text[:m.start()].count("\n") + 1
            name_line = text[:m.end()].count("\n") + 1
            span = str(kw_line) if kw_line == name_line else f"{kw_line}-{name_line}"
            rel = path.relative_to(repo_root)
            return f"{rel}:{span}"
    return None

print(f"Allowlist entries: {len(entries)} ({len(BUILTINS & set(entries))} builtins)")
bad = []
for name in entries:
    if name in BUILTINS:
        print(f"  accept {name}  (Lean builtin, no tree declaration)")
        continue
    where = locate(name)
    if where is None:
        bad.append(name)
        print(f"  REJECT {name}  (no `axiom`/`opaque` declaration found in the tree)")
    else:
        print(f"  accept {name}  ({where})")

if bad:
    print(f"FAIL: {len(bad)} allowlist entry/entries do not resolve against the tree:")
    for name in bad:
        print(f"  - {name}")
    sys.exit(1)
print("Allowlist resolves against the tree.")
PYVALIDATE
}

collect_axiom_targets() {
  python3 - "$REPO_ROOT" <<'PYTARGETS'
import re, sys, pathlib

repo_root = pathlib.Path(sys.argv[1])
DECL = re.compile(
    r"(?m)^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|nonrec\s+)*"
    r"(?:theorem|lemma|axiom)\s+([A-Za-z_À-￿][^\s:({\[⦃]*)"
)
out = []
for path in sorted(repo_root.glob("Spqr/Specs/**/*.lean")):
    text = path.read_text(errors="replace")
    stack = []
    for line in text.splitlines():
        ns = re.match(r"^namespace\s+(\S+)\s*$", line)
        if ns:
            stack.append(ns.group(1))
            continue
        if re.match(r"^end\s+\S+\s*$", line) and stack:
            stack.pop()
            continue
        m = DECL.match(line)
        if m:
            name = m.group(1).strip()
            if name:
                out.append(".".join(stack + [name]) if stack else name)
for name in sorted(set(out)):
    print(name)
PYTARGETS
}

parse_axiom_report() {
  python3 - "$ALLOWLIST" "$1" "$2" "$3" <<'PYPARSE'
import re, sys, pathlib

allowlist_path = pathlib.Path(sys.argv[1])
log_path = pathlib.Path(sys.argv[2])
targets = [t for t in pathlib.Path(sys.argv[3]).read_text().split() if t]
allow_sorry = set(t for t in pathlib.Path(sys.argv[4]).read_text().split() if t)

allowed = set()
for raw in allowlist_path.read_text().splitlines():
    line = raw.split("#", 1)[0].strip()
    if line:
        allowed.add(line)

log = log_path.read_text(errors="replace").splitlines()

HEADER = re.compile(r"'([^']+)'\s+(depends on axioms:\s*\[|does not depend on any axioms)")
failures, reports = [], {}

# A typo'd target must fail loudly rather than pass vacuously.
for line in log:
    if "unknown identifier" in line or "unknown constant" in line:
        failures.append(f"unresolved target name: {line.strip()}")

i = 0
while i < len(log):
    m = HEADER.search(log[i])
    if not m:
        i += 1
        continue
    name, kind = m.group(1), m.group(2)
    if kind.startswith("does not depend"):
        reports[name] = set()
        i += 1
        continue
    # Accumulate the axiom list across Lean's soft line breaks up to the `]`.
    chunk = log[i][m.end():]
    closed = "]" in chunk
    chunk = chunk.split("]", 1)[0]
    j = i + 1
    while not closed and j < len(log):
        if HEADER.search(log[j]):
            break                      # next report started: bracket never closed
        if "]" in log[j]:
            chunk += " " + log[j].split("]", 1)[0]
            closed = True
            j += 1
            break
        chunk += " " + log[j]
        j += 1
    if not closed:
        failures.append(f"malformed #print axioms report for '{name}': "
                        "no closing ']' before the next report or EOF")
        reports[name] = None
    else:
        reports[name] = {a.strip() for a in re.sub(r"\s+", " ", chunk).split(",") if a.strip()}
    i = j if j > i else i + 1

# Every target must have produced a report, by name.
for t in targets:
    if t not in reports:
        failures.append(f"no #print axioms report for target '{t}' "
                        "(target missing, renamed or the elaboration aborted)")

for name, axioms in sorted(reports.items()):
    if axioms is None:
        continue
    if "sorryAx" in axioms and name not in allow_sorry:
        failures.append(f"'{name}' depends on sorryAx (not permitted; pass "
                        f"--allow-sorry {name} to accept it deliberately)")
    extra = sorted(a for a in axioms if a != "sorryAx" and a not in allowed)
    if extra:
        failures.append(f"'{name}' depends on non-allowlisted axiom(s): {', '.join(extra)}")

print(f"Targets checked: {len(targets)}; reports parsed: {len(reports)}")
if failures:
    print(f"FAIL: {len(failures)} axiom violation(s):")
    for f in failures:
        print(f"  - {f}")
    sys.exit(1)
print("Every target's axiom closure is within the allowlist.")
PYPARSE
}

gate_4() {
  banner "GATE 4: #print axioms vs $(basename "$ALLOWLIST")"

  echo "--- 4A: allowlist resolves against the tree ---"
  local rc_a=0
  set +e
  validate_allowlist
  rc_a=$?
  set -e
  if [[ "$rc_a" -ne 0 ]]; then
    fail 4 "allowlist entries do not resolve against the tree"
    return
  fi

  echo "--- 4B: axiom closure of each target ---"
  if ! have_lake; then
    skip 4 "lake not on PATH; 4A passed but the axiom closure was not checked"
    return
  fi

  local scratch_dir
  scratch_dir="$(mktemp -d)"            # mode 0700
  trap 'rm -rf "$scratch_dir"' RETURN

  local targets_file="$scratch_dir/targets.txt"
  if [[ "${#AXIOM_TARGETS[@]}" -gt 0 ]]; then
    printf '%s\n' "${AXIOM_TARGETS[@]}" > "$targets_file"
  else
    collect_axiom_targets > "$targets_file" || true
  fi
  if [[ ! -s "$targets_file" ]]; then
    skip 4 "no #print axioms targets found under Spqr/Specs; pass --axiom-target"
    return
  fi
  echo "Targets: $(grep -c '' "$targets_file")"

  local allow_file="$scratch_dir/allow-sorry.txt"
  : > "$allow_file"
  if [[ "${#ALLOW_SORRY[@]}" -gt 0 ]]; then
    printf '%s\n' "${ALLOW_SORRY[@]}" > "$allow_file"
  fi

  local scratch="$scratch_dir/PrintAxioms.lean"
  {
    echo 'import Spqr'
    while IFS= read -r thm; do
      [[ -n "$thm" ]] && echo "#print axioms $thm"
    done < "$targets_file"
  } > "$scratch"

  set +e
  lake env lean "$scratch" > "$scratch_dir/axioms.log" 2>&1
  local lean_rc=$?
  set -e
  cp "$scratch_dir/axioms.log" /tmp/lake-axioms.log 2>/dev/null || true

  local rc_b=0
  set +e
  parse_axiom_report "$scratch_dir/axioms.log" "$targets_file" "$allow_file"
  rc_b=$?
  set -e

  if [[ "$rc_b" -ne 0 ]]; then
    fail 4 "axiom closure violates the allowlist (see /tmp/lake-axioms.log)"
  elif [[ "$lean_rc" -ne 0 ]]; then
    # Every report parsed cleanly but lean still errored: something else in the
    # scratch elaboration failed.  Do not call that a pass.
    fail 4 "lake env lean exited $lean_rc on the scratch file"
  else
    pass 4
  fi
}

# ─── Gate 5: provenance (PROV-01) ─────────────────────────────────────────────
#
# Needs no build: `--gates 5` never invokes lake.  The checker enumerates every
# catalog row, requires a `Source:` field and resolves every citation in it.

gate_5() {
  banner "GATE 5: provenance (scripts/check-provenance.py)"
  if ! command -v python3 >/dev/null 2>&1; then
    skip 5 "python3 not on PATH"
    return
  fi
  if [[ ! -f "$REPO_ROOT/scripts/check-provenance.py" ]]; then
    skip 5 "scripts/check-provenance.py not found"
    return
  fi
  local rc=0
  set +e
  python3 "$REPO_ROOT/scripts/check-provenance.py"
  rc=$?
  set -e
  case "$rc" in
    0) pass 5 ;;
    1) fail 5 "unresolved Source: citations or §12 index disagreement" ;;
    *) skip 5 "check-provenance.py exited $rc (could not run)" ;;
  esac
}

# ─── Run the selected gates ───────────────────────────────────────────────────

if selected 1; then gate_1; fi
if selected 2; then gate_2; fi
if selected 3; then
  if gate_3a; then gate_3b; else skip 3b "gate 3a did not produce a manifest"; fi
fi
if selected 4; then gate_4; fi
if selected 5; then gate_5; fi

# ─── Report ───────────────────────────────────────────────────────────────────

banner "SUMMARY"
FAILED=0
REPORTED=0
for g in 1 2 3a 3b 4 5; do
  [[ -n "${GATE_STATUS[$g]:-}" ]] || continue
  REPORTED=$((REPORTED + 1))
  status="${GATE_STATUS[$g]}"
  reason="${GATE_REASON[$g]:-}"
  if [[ -n "$reason" ]]; then
    printf 'GATE %s: %s (%s)\n' "$g" "$status" "$reason"
  else
    printf 'GATE %s: %s\n' "$g" "$status"
  fi
  [[ "$status" == "PASS" ]] || FAILED=$((FAILED + 1))
done

if [[ "$REPORTED" -eq 0 ]]; then
  echo "check-gates.sh: no gate produced a verdict - refusing to report success." >&2
  exit 1
fi

if [[ "$FAILED" -gt 0 ]]; then
  printf '\n%s gate(s) not PASS (SKIP counts as a failure).\n' "$FAILED"
  exit 1
fi
printf '\nAll selected gates PASS.\n'
