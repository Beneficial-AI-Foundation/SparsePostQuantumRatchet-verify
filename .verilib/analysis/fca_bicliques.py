#!/usr/bin/env python3
"""FCA / maximal-biclique mining over the (theorem x cited-lemma) bipartite graph.

Objects   = hand-written theorems/lemmas under Spqr/ (parsed from source, since
            probe-lean dependency edges never target theorems and JSON line
            ranges may be stale).
Attributes = lemma names cited inside tactic bracket lists of the proof body
            (simp/simp_all/simp_rw/fsimp/rw/rewrite/grind ... [ ... ]) plus
            `unfold` argument lists.  Names are normalised to their last dotted
            component so that `GF16.toGF216` and `toGF216` coincide.

A formal concept = maximal biclique = (extent, intent) with
   extent = set of theorems, intent = set of lemma names,
   every theorem in extent cites every lemma in intent, both maximal.
Intents are computed as the closure of proof-rows under pairwise intersection.
Ranked by area = |extent| * |intent|.
"""
import re
from collections import defaultdict
from pathlib import Path

ROOT = Path('/home/zhang-liao/spqr2/SparsePostQuantumRatchet-verify')

def strip_comments(s):
    s = re.sub(r'/-.*?-/', '', s, flags=re.S)
    s = re.sub(r'--.*', '', s)
    return s

DECL_RE = re.compile(
    r'^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|scoped\s+)*'
    r'(theorem|lemma|def|abbrev|instance|structure|inductive|example|opaque)\b'
    r'\s*([A-Za-z_][\w.!?\']*)?',
    re.M)

TACTIC_LIST_RE = re.compile(
    r'\b(?:simp_all|simp_rw|simp|fsimp|rw|rewrite|grind|norm_num|field_simp|step)'
    r'\s*(?:only)?\s*\[([^\[\]]*)\]')
UNFOLD_RE = re.compile(r'\bunfold((?:[ \t]+[A-Za-z_][\w.!?\']*)+)')

# tactic keywords / structuring tokens that are not lemma citations
STOP = {'simp', 'only', 'simp_all', 'simp_rw', 'rw', 'rewrite', 'unfold',
        'obtain', 'apply', 'exact', 'intro', 'intros', 'rcases', 'cases',
        'by_cases', 'constructor', 'refine', 'have', 'show', 'at', 'with',
        'this', 'fun', 'step', 'grind', 'omega', 'decide', 'trivial', 'and'}
HYP_RE = re.compile(r"^(h|ih)([_A-Z0-9].*)?$")   # local-hypothesis names: h, h1, hLt, h_opt_eq, ih...

def norm(name):
    name = name.strip().lstrip('←').lstrip('<-').strip()
    if not name or ' ' in name or name in ('*',) or name.startswith(('(', '"')):
        return None
    name = name.rstrip(',')
    last = name.split('.')[-1]
    if not re.fullmatch(r"[A-Za-z_][\w!?\']*", last):
        return None
    if last in STOP or HYP_RE.match(last):
        return None
    return last

# ---------- 1. parse theorem blocks & extract vocabulary rows ----------
rows = {}          # (file, thmname) -> frozenset of lemma tokens
for fp in sorted(ROOT.glob('Spqr/**/*.lean')):
    text = strip_comments(fp.read_text())
    decls = list(DECL_RE.finditer(text))
    for i, m in enumerate(decls):
        if m.group(1) not in ('theorem', 'lemma'):
            continue
        name = m.group(2) or f'<anon@{m.start()}>'
        end = decls[i + 1].start() if i + 1 < len(decls) else len(text)
        block = text[m.start():end]
        vocab = set()
        for lst in TACTIC_LIST_RE.findall(block):
            for item in lst.split(','):
                t = norm(item)
                if t:
                    vocab.add(t)
        for lst in UNFOLD_RE.findall(block):
            for item in lst.split():
                t = norm(item)
                if t:
                    vocab.add(t)
        # drop the theorem's own name if self-cited
        vocab.discard(name.split('.')[-1])
        if vocab:
            rows[(str(fp.relative_to(ROOT)), name)] = frozenset(vocab)

print(f'theorems parsed with non-empty tactic vocabulary: {len(rows)}')
all_attrs = set().union(*rows.values())
print(f'distinct cited lemma tokens: {len(all_attrs)}')

# ---------- 2. closure under pairwise intersection => all intents ----------
MIN_INTENT = 2
base = {r for r in rows.values() if len(r) >= MIN_INTENT}
intents = set(base)
frontier = set(base)
CAP = 60000
while frontier and len(intents) < CAP:
    new = set()
    for a in frontier:
        for b in base:
            c = a & b
            if len(c) >= MIN_INTENT and c not in intents:
                new.add(c)
    intents |= new
    frontier = new
print(f'closed intents (|intent| >= {MIN_INTENT}): {len(intents)}')

# ---------- 3. extents, filtering, ranking ----------
MIN_EXTENT = 3
concepts = []
for intent in intents:
    extent = [k for k, r in rows.items() if intent <= r]
    if len(extent) >= MIN_EXTENT:
        concepts.append((len(extent) * len(intent), len(extent), intent, extent))
concepts.sort(key=lambda x: (-x[0], -x[1]))

# keep only concepts whose intent is not a subset of a higher-ranked intent
# with the SAME extent (those are non-maximal duplicates already excluded by
# closure; but also drop near-noise: intents made only of ubiquitous tokens)
print()
print('TOP CONCEPTS (maximal bicliques), by area = |theorems| x |lemmas|')
print('=' * 72)
shown = 0
for area, ext_n, intent, extent in concepts:
    if shown >= 30:
        break
    shown += 1
    print(f'[area {area:4d}] {ext_n:3d} theorems x {len(intent)} lemmas')
    print(f'   intent: {", ".join(sorted(intent))}')
    byfile = defaultdict(list)
    for f, t in extent:
        byfile[f].append(t)
    ex = sorted(byfile.items())
    for f, ts in ex[:4]:
        print(f'      {f}: {", ".join(sorted(ts)[:4])}')
    if len(ex) > 4:
        print(f'      ... and {len(ex) - 4} more files')
    print()
