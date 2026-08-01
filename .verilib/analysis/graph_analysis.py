#!/usr/bin/env python3
"""Graph analysis over probe-lean extract for SPQR-verify.

Analyses:
  A. counts by top-dir / kind / status
  B. fan-in (reverse deps) for Spqr/** atoms -- most-reused concepts
  C. cross-subtree deps inside Spqr/Specs -- lift-to-Math candidates
  D. Spqr/Math + Auxiliary atoms with zero graph dependents (defs only;
     theorem usage recovered separately by source grep)
  E. file-size / one-atom-file stats -- organization signals
  F. duplicate display-names across files -- possible duplicated concepts
"""
import json, re, sys
from collections import Counter, defaultdict
from pathlib import Path

ROOT = Path('/home/zhang-liao/spqr2/SparsePostQuantumRatchet-verify')
data = json.load(open(ROOT / '.verilib/probes/lean_Spqr_0.1.0.json'))['data']

def topdir(p):
    parts = p.split('/')
    if parts[0] == 'Spqr' and len(parts) > 1:
        return 'Spqr/' + parts[1]
    return parts[0]

# ---------- A. overview ----------
print('=' * 70)
print('A. OVERVIEW')
cnt_dir = Counter(); cnt_kind = Counter(); cnt_status = Counter()
for name, a in data.items():
    cnt_dir[topdir(a['code-path'])] += 1
    cnt_kind[a['kind']] += 1
    cnt_status[a['verification-status']] += 1
for c, title in [(cnt_dir, 'by dir'), (cnt_kind, 'by kind'), (cnt_status, 'by status')]:
    print(f'-- {title}:')
    for k, v in c.most_common():
        print(f'   {v:5d}  {k}')

# ---------- reverse graph ----------
rev = defaultdict(set)   # target -> set of dependents
for name, a in data.items():
    for dep in a.get('dependencies', []):
        if dep in data and dep != name:
            rev[dep].add(name)

# ---------- B. fan-in for hand-written (Spqr/, Utils/) atoms ----------
print('=' * 70)
print('B. TOP FAN-IN, hand-written atoms (Spqr/** and Utils/**)')
hand = {n: a for n, a in data.items()
        if a['code-path'].startswith(('Spqr/', 'Utils/'))}
rows = sorted(((len(rev[n]), n) for n in hand), reverse=True)[:30]
for c, n in rows:
    a = data[n]
    print(f'   {c:4d}  [{a["kind"]:9s}] {n.replace("probe:","")}  ({a["code-path"]})')

# ---------- C. cross-subtree deps inside Spqr/Specs ----------
print('=' * 70)
print('C. CROSS-SUBTREE REUSE inside Spqr/Specs (lift candidates)')
def spec_subtree(p):
    # Spqr/Specs/<area>/... -> area
    parts = p.split('/')
    if len(parts) >= 3 and parts[0] == 'Spqr' and parts[1] == 'Specs':
        return parts[2]
    return None
lift = []
for n, dependents in rev.items():
    if n not in data:
        continue
    a = data[n]
    st = spec_subtree(a['code-path'])
    if st is None:
        continue
    ext = {d for d in dependents
           if spec_subtree(data[d]['code-path']) not in (st, None)
           or (data[d]['code-path'].startswith('Spqr/') and spec_subtree(data[d]['code-path']) is None)}
    if ext:
        lift.append((len(ext), n, a, sorted({topdir(data[d]['code-path']) + '/' + (spec_subtree(data[d]['code-path']) or '') for d in ext})))
for c, n, a, users in sorted(lift, reverse=True)[:25]:
    print(f'   {c:3d} ext-users  [{a["kind"]:9s}] {n.replace("probe:","")}')
    print(f'        at {a["code-path"]}  used from: {", ".join(users)}')

# ---------- D. zero-dependent defs in Math/Auxiliary/Utils ----------
print('=' * 70)
print('D. ZERO-GRAPH-DEPENDENT defs/structures in Spqr/Math, Spqr/Auxiliary, Utils')
print('   (theorem-edge blindness: usage from theorem *proofs* IS visible for defs;')
print('    only theorem->theorem is invisible. Zero here = no def/type/proof uses it.)')
for n, a in sorted(data.items()):
    if a['kind'] == 'theorem':
        continue
    p = a['code-path']
    if p.startswith(('Spqr/Math', 'Spqr/Auxiliary', 'Utils/')) and not rev[n]:
        print(f'   [{a["kind"]:9s}] {n.replace("probe:",""):60s} {p}')

# ---------- E. file stats ----------
print('=' * 70)
print('E. FILE ORGANIZATION SIGNALS')
by_file = defaultdict(list)
for n, a in data.items():
    by_file[a['code-path']].append(n)
spec_files = {f: ns for f, ns in by_file.items() if f.startswith('Spqr/Specs/')}
one_atom = [f for f, ns in spec_files.items() if len(ns) == 1]
print(f'   Spqr/Specs files in extract: {len(spec_files)}, single-atom files: {len(one_atom)}')
depth = Counter(len(f.split('/')) for f in spec_files)
print('   file path depth histogram (Spqr/Specs):', dict(sorted(depth.items())))
big = sorted(((len(ns), f) for f, ns in by_file.items()), reverse=True)[:10]
print('   biggest files by atom count:')
for c, f in big:
    print(f'      {c:5d}  {f}')

# ---------- F. duplicate display names in hand-written code ----------
print('=' * 70)
print('F. SAME display-name DEFINED IN MULTIPLE hand-written FILES (dup-concept candidates)')
byname = defaultdict(set)
for n, a in hand.items():
    if a['kind'] in ('def', 'structure', 'abbrev', 'inductive'):
        byname[a['display-name']].add(a['code-path'])
for dn, files in sorted(byname.items()):
    if len(files) > 1:
        print(f'   {dn}: {sorted(files)}')
