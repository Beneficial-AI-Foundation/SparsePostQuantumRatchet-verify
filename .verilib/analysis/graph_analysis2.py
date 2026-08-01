#!/usr/bin/env python3
"""Round 2: layering violations, theorem reuse via source grep, dup instances,
def reuse across Specs files."""
import json, re
from collections import defaultdict
from pathlib import Path

ROOT = Path('/home/zhang-liao/spqr2/SparsePostQuantumRatchet-verify')
data = json.load(open(ROOT / '.verilib/probes/lean_Spqr_0.1.0.json'))['data']

def strip_comments(s):
    s = re.sub(r'/-.*?-/', '', s, flags=re.S)
    s = re.sub(r'--.*', '', s)
    return s

# ---------- 1. layering: Math/Auxiliary depending on Specs or SrcTranslated ----------
print('=' * 70)
print('1. LAYERING: Spqr/Math or Spqr/Auxiliary atoms depending on Specs/SrcTranslated')
for n, a in data.items():
    if not a['code-path'].startswith(('Spqr/Math', 'Spqr/Auxiliary')):
        continue
    bad = [d for d in a.get('dependencies', [])
           if d in data and data[d]['code-path'].startswith(('Spqr/Specs', 'SrcTranslated'))]
    if bad:
        print(f'   {n.replace("probe:","")} ({a["code-path"]})')
        for b in bad:
            print(f'      -> {b.replace("probe:","")} ({data[b]["code-path"]})')

# ---------- 2. Specs atoms depended on by SrcTranslated? (should never happen) --
# skip: SrcTranslated is generated, cannot import Specs.

# ---------- 3. def reuse across *files* within Spqr/Specs ----------
print('=' * 70)
print('2. SPECS DEFS USED FROM OTHER SPECS FILES (shared-def candidates)')
rev = defaultdict(set)
for n, a in data.items():
    for dep in a.get('dependencies', []):
        if dep in data and dep != n:
            rev[dep].add(n)
for n, a in sorted(data.items()):
    if not a['code-path'].startswith('Spqr/Specs/'):
        continue
    if a['kind'] not in ('def', 'structure', 'abbrev', 'inductive', 'instance'):
        continue
    other = sorted({data[d]['code-path'] for d in rev[n]
                    if data[d]['code-path'] != a['code-path']
                    and data[d]['code-path'].startswith('Spqr/')})
    if other:
        print(f'   [{a["kind"]:9s}] {n.replace("probe:","")}  @ {a["code-path"]}')
        for f in other:
            print(f'       used by {f}')

# ---------- 4. duplicate Inhabited-style instances ----------
print('=' * 70)
print('3. INSTANCE NAME SUFFIX COLLISIONS across files (dup instance candidates)')
suff = defaultdict(list)
for n, a in data.items():
    if a['kind'] != 'instance' or not a['code-path'].startswith('Spqr/'):
        continue
    last = n.split('.')[-1]
    suff[last].append((n, a['code-path']))
for s, lst in sorted(suff.items()):
    if len(lst) > 1:
        print(f'   {s}:')
        for n, p in lst:
            print(f'      {n.replace("probe:","")}  @ {p}')

# ---------- 5. theorem reuse recovered from source text ----------
print('=' * 70)
print('4. THEOREM USAGE BY SOURCE GREP (graph-invisible)')
# collect hand-written theorems
thms = {n: a for n, a in data.items()
        if a['kind'] == 'theorem' and a['code-path'].startswith('Spqr/')}
# unique reference token: use the full last component; count word-boundary hits
# across all hand-written lean files, excluding the defining span.
files = {}
for p in set(a['code-path'] for a in data.values() if a['code-path'].startswith('Spqr/')):
    fp = ROOT / p
    if fp.exists():
        files[p] = strip_comments(fp.read_text())

use_count = defaultdict(set)          # theorem -> set of files referencing it
name_of = {}
for n, a in thms.items():
    tok = n.split('.')[-1]
    name_of.setdefault(tok, []).append(n)

# tokens that are too generic (defined by many theorems) still counted per-file,
# but flag ambiguity
for p, text in files.items():
    words = set(re.findall(r'[A-Za-z_][A-Za-z0-9_!\'?]*', text))
    for tok, ns in name_of.items():
        if tok in words:
            for n in ns:
                if data[n]['code-path'] != p:
                    use_count[n].add(p)

dead = []
for n, a in sorted(thms.items()):
    tok = n.split('.')[-1]
    ambiguous = len(name_of[tok]) > 1
    if not use_count[n]:
        # check own file: referenced elsewhere in same file?
        own = files.get(a['code-path'], '')
        # count occurrences of token; >1 means used besides its own decl
        occ = len(re.findall(r'(?<![A-Za-z0-9_])' + re.escape(tok) + r'(?![A-Za-z0-9_!\'?])', own))
        if occ <= 1:
            dead.append((n, a, ambiguous))
print(f'   hand-written theorems: {len(thms)}')
print(f'   theorems with NO textual reference anywhere (dead-lemma candidates): {len(dead)}')
mathdead = [x for x in dead if x[1]['code-path'].startswith('Spqr/Math')]
print(f'   ... of which in Spqr/Math: {len(mathdead)}')
for n, a, amb in mathdead:
    print(f'      {n.replace("probe:","")}  @ {a["code-path"]}{"  [ambig-token]" if amb else ""}')

print()
print('   MOST-REUSED Math theorems (by #files referencing):')
rows = sorted(((len(fs), n) for n, fs in use_count.items()
               if data[n]['code-path'].startswith('Spqr/Math')), reverse=True)[:25]
for c, n in rows:
    print(f'      {c:3d} files  {n.replace("probe:","")}  @ {data[n]["code-path"]}')
