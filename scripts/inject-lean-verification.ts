#!/usr/bin/env tsx
/*
 * Post-processes rustdoc HTML (target/docs-build/doc/spqr/) to inject a "Lean
 * specification" panel under each function/method/constant that has a spec
 * theorem recorded in functions.json (produced by `lake exe docsjson`).
 *
 * Panel grades (see Utils/Lib/Analysis.lean `specStatus`):
 *   ✓✓  proven       — spec theorem, axiom closure within the trusted base
 *   △   axiomatized  — the spec itself is a trusted axiom
 *   ◑   incomplete   — proof contains `sorry` or an unrecognized axiom
 *
 * Every spec'd record MUST inject successfully: any unmapped file/anchor or
 * ambiguous trait-impl match is a hard error (nonzero exit) so CI never
 * publishes docs with silently missing panels. Ambiguities can be resolved
 * via scripts/injection-overrides.json:
 *   { "<rust_name>": { "file": "...", "anchor": "..." } | { "skip": "reason" } }
 *
 * Output: modified HTML files in-place; lean-verification.css written at the
 * rustdoc root and linked from each modified page; a root index.html redirect
 * with a provenance footer.
 *
 * Usage:
 *   tsx scripts/inject-lean-verification.ts \
 *     --rustdoc-root target/docs-build/doc \
 *     --functions   target/docs-build/functions.json \
 *     [--rust-version "$(rustc --version)"]
 *
 * Adapted from curve25519-dalek-lean-verify's injector; the target-mapping
 * logic is rewritten because spqr derives module paths from `rust_name`
 * (inline modules like `gf::reduce` make source-file paths unreliable) and
 * needs impl-scoped anchors (GF16 has two impls per arithmetic trait).
 */

import fs from 'node:fs'
import path from 'node:path'

// ---------- Types ----------

const CRATE = 'spqr'
const REPO_URL = 'https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify'

interface FunctionRecord {
  rust_name: string
  lean_name: string
  source: string
  line_start: number
  line_end: number
  is_opaque: boolean
  has_spec: boolean
  spec_name?: string
  spec_file?: string
  spec_docstring?: string | null
  spec_statement?: string
  spec_kind?: 'theorem' | 'axiom'
  status?: 'proven' | 'axiomatized' | 'incomplete'
  axioms?: string[]
}

interface Config {
  rustdocRoot: string
  functionsJson: string
  rustVersion: string | null
}

type Override = { file: string; anchor: string } | { skip: string }

// ---------- CLI ----------

function parseArgs(): Config {
  const args = new Map<string, string>()
  for (let i = 2; i < process.argv.length; i += 2) {
    const k = process.argv[i].replace(/^--/, '')
    const v = process.argv[i + 1]
    if (!v) throw new Error(`Missing value for --${k}`)
    args.set(k, v)
  }
  return {
    rustdocRoot: args.get('rustdoc-root') ?? 'target/docs-build/doc',
    functionsJson: args.get('functions') ?? 'target/docs-build/functions.json',
    rustVersion: args.get('rust-version') ?? null,
  }
}

// ---------- rust_name → rustdoc target ----------

interface RustdocTarget {
  /** Candidate paths under rustdoc-root; the first that exists wins
   *  (struct vs enum vs union is not knowable from the rust_name). */
  fileCandidates: string[]
  /** 'method.X', 'associatedconstant.X', or '' (own page: fn/constant). */
  anchor: string
  /** For trait impls: the impl signature to scope the anchor search to,
   *  e.g. 'AddAssign<&GF16> for GF16'. null → page-global anchor. */
  implSig: ImplSig | null
}

interface ImplSig {
  trait: string       // short trait name, e.g. 'AddAssign'
  args: string[]      // normalized generic args, e.g. ['&GF16'] (charon may append extras)
  receiver: string    // short receiver type name, e.g. 'GF16'
}

function isConstName(name: string): boolean {
  return /^[A-Z][A-Z0-9_]*$/.test(name) && !/[a-z]/.test(name)
}

function lastSegment(rustName: string): string {
  const segs = rustName.split('::')
  return segs[segs.length - 1]
}

/** Shorten every fully-qualified path to its last segment and drop lifetimes:
 *  `core::ops::arith::AddAssign<&'_0 spqr::encoding::gf::GF16>` → `AddAssign<&GF16>`. */
function shortenTypePath(s: string): string {
  return s
    .replace(/&'\w+\s*/g, '&')            // &'_0 GF16 → &GF16
    .replace(/'\w+\s*,?\s*/g, '')         // stray lifetime params
    .replace(/\b[A-Za-z_][A-Za-z0-9_]*::/g, '')  // path prefixes
    .replace(/\s+/g, ' ')
    .trim()
}

/** Split `Trait<A, B<C, D>>`-style generic args at top-level commas. */
function splitTopLevel(s: string): string[] {
  const out: string[] = []
  let depth = 0
  let cur = ''
  for (const ch of s) {
    if (ch === '<' || ch === '(' || ch === '[') depth++
    if (ch === '>' || ch === ')' || ch === ']') depth--
    if (ch === ',' && depth === 0) {
      out.push(cur.trim())
      cur = ''
    } else {
      cur += ch
    }
  }
  if (cur.trim()) out.push(cur.trim())
  return out
}

/** Parse `Name<a, b>` into base name + normalized args. */
function parseTypeApp(s: string): { name: string; args: string[] } {
  const lt = s.indexOf('<')
  if (lt === -1) return { name: s.trim(), args: [] }
  const name = s.slice(0, lt).trim()
  const inner = s.slice(lt + 1, s.lastIndexOf('>'))
  return { name, args: splitTopLevel(inner).map(a => a.replace(/\s+/g, '')) }
}

/** Receiver path from a brace form's inner text (already RHS of ` for ` when trait). */
function parseReceiver(recv: string): { type: string; modulePath: string } | null {
  let inner = recv.trim()
  inner = inner.replace(/^&\d+\s*\(/, '').replace(/\)\s*$/, '').replace(/^&'?\w*\s*/, '').trim()
  inner = inner.replace(/<[^<>]*(?:<[^<>]*>[^<>]*)*>\s*$/, '') // strip trailing generics (1 nesting level)
  const parts = inner.split('::').map(s => s.trim()).filter(s => s.length > 0)
  if (parts.length === 0) return null
  const type = parts[parts.length - 1]
  const modulePath = parts.length > 1 ? parts.slice(0, -1).join('/') : CRATE
  return { type, modulePath }
}

/** Candidate page filenames for a type (rustdoc names the page after the item kind). */
function typePageCandidates(modulePath: string, type: string): string[] {
  return ['struct', 'enum', 'union'].map(kind => `${modulePath}/${kind}.${type}.html`)
}

/**
 * Decide where in rustdoc the item lives, from `rust_name` alone. Module paths
 * are NOT derived from the source file path: inline modules (`mod reduce` in
 * gf.rs) live in child module dirs that the file path cannot reveal.
 */
function rustNameToRustdoc(rustName: string): RustdocTarget | null {
  const braceMatch = rustName.match(/\{[\s\S]*\}/)
  if (braceMatch) {
    // Brace form: `mod::{impl Trait for Recv}::item` or `mod::{Recv}::item`.
    let inner = braceMatch[0].slice(1, -1).trim()
    const item = lastSegment(rustName)
    const anchor = isConstName(item) ? `associatedconstant.${item}` : `method.${item}`
    const forIdx = inner.lastIndexOf(' for ')
    if (forIdx >= 0) {
      // Trait impl: scope the anchor to the matching impl section.
      const traitPart = inner.slice(0, forIdx).replace(/^impl\s+/, '').trim()
      const recvPart = inner.slice(forIdx + 5).trim()
      const receiver = parseReceiver(recvPart)
      if (!receiver) return null
      const t = parseTypeApp(shortenTypePath(traitPart))
      return {
        fileCandidates: typePageCandidates(receiver.modulePath, receiver.type),
        anchor,
        implSig: { trait: t.name, args: t.args, receiver: receiver.type },
      }
    }
    // Inherent impl: page-global anchor (inherent items precede trait impls,
    // so they own the unsuffixed id).
    const receiver = parseReceiver(inner)
    if (!receiver) return null
    return {
      fileCandidates: typePageCandidates(receiver.modulePath, receiver.type),
      anchor,
      implSig: null,
    }
  }

  // Plain path: module::…::item
  const segs = rustName.split('::')
  const name = segs[segs.length - 1]
  const parent = segs[segs.length - 2] ?? ''
  if (isConstName(name)) {
    const modulePath = segs.slice(0, -1).join('/')
    return { fileCandidates: [`${modulePath}/constant.${name}.html`], anchor: '', implSig: null }
  }
  if (parent && /^[A-Z]/.test(parent)) {
    const modulePath = segs.slice(0, -2).join('/')
    return {
      fileCandidates: typePageCandidates(modulePath, parent),
      anchor: `method.${name}`,
      implSig: null,
    }
  }
  const modulePath = segs.slice(0, -1).join('/')
  return { fileCandidates: [`${modulePath}/fn.${name}.html`], anchor: '', implSig: null }
}

// ---------- impl-section matching ----------

interface PageImpl {
  idx: number       // index of the `<section id="impl-…"` in the HTML
  endIdx: number    // start of the NEXT impl section (or html.length)
  trait: string | null
  args: string[]
  receiver: string
}

/**
 * Enumerate `<section id="impl-…">` blocks and parse their ids.
 * Rustdoc ids look like `impl-AddAssign%3C%26GF16%3E-for-GF16` (URL-encoded,
 * `+` for spaces, default generic args like `Rhs = Self` omitted) or
 * `impl-GF16` for inherent impls.
 */
function pageImplSections(html: string): PageImpl[] {
  const out: PageImpl[] = []
  const re = /<section id="(impl-[^"]*)"[^>]*>/g
  let m: RegExpExecArray | null
  while ((m = re.exec(html)) !== null) {
    let id: string
    try {
      id = decodeURIComponent(m[1]).replace(/\+/g, ' ')
    } catch {
      id = m[1]
    }
    let sig = id.replace(/^impl-/, '').replace(/-\d+$/, '')
    // Strip generic parameter intro `impl<'a, T> Trait for …` remnants if present.
    const forSplit = sig.split('-for-')
    let trait: string | null = null
    let args: string[] = []
    let receiver: string
    if (forSplit.length >= 2) {
      const t = parseTypeApp(shortenTypePath(forSplit.slice(0, -1).join('-for-')))
      trait = t.name
      args = t.args
      receiver = parseTypeApp(shortenTypePath(forSplit[forSplit.length - 1])).name
    } else {
      receiver = parseTypeApp(shortenTypePath(sig)).name
    }
    out.push({ idx: m.index, endIdx: html.length, trait, args, receiver })
  }
  for (let i = 0; i + 1 < out.length; i++) out[i].endIdx = out[i + 1].idx
  return out
}

/**
 * Find the [start, end) region of the impl section matching `sig`, or an
 * Error describing why (no match / ambiguous).
 *
 * Charon writes explicit generic args that rustdoc's id omits when they are
 * defaults (`AddAssign<GF16> for GF16` → `impl-AddAssign-for-GF16`) or
 * appends associated-output types (`Add<&GF16, GF16>` → id `Add<&GF16>`), so:
 *   1. filter by trait + receiver name;
 *   2. if several remain, prefer the impl whose args are a prefix of the
 *      record's args; among those prefer the longest match (an empty-args id
 *      matches everything, so it only wins when nothing longer does).
 */
function findImplRegion(html: string, sig: ImplSig): { start: number; end: number } | Error {
  const impls = pageImplSections(html)
  const byName = impls.filter(s => s.trait === sig.trait && s.receiver === sig.receiver)
  if (byName.length === 0) {
    return new Error(`no impl section for '${sig.trait}<${sig.args.join(',')}> for ${sig.receiver}'`)
  }
  // The generic check applies even to a sole candidate: if the borrowed impl
  // disappears from the docs while a stale record still references it, the
  // record must fail rather than silently land on the remaining impl.
  const isPrefix = (s: PageImpl) =>
    s.args.length <= sig.args.length && s.args.every((a, i) => a === sig.args[i])
  const prefixed = byName.filter(isPrefix)
  if (prefixed.length === 0) {
    return new Error(
      `no impl section with matching generics for '${sig.trait}<${sig.args.join(',')}> for ${sig.receiver}'`)
  }
  const maxLen = Math.max(...prefixed.map(s => s.args.length))
  const best = prefixed.filter(s => s.args.length === maxLen)
  if (best.length > 1) {
    return new Error(
      `ambiguous impl sections for '${sig.trait}<${sig.args.join(',')}> for ${sig.receiver}'`)
  }
  return { start: best[0].idx, end: best[0].endIdx }
}

// ---------- Panel rendering ----------

function htmlEscape(s: string): string {
  return s
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;')
}

/**
 * Lightweight regex-based Lean syntax highlighter (derived from the curve25519
 * injector). Every produced `<span>` is stashed behind a `\x00N\x00` placeholder
 * so later passes can never match markup emitted by earlier ones (e.g. the
 * keyword `class` matching a `class="hl-comment"` attribute).
 */
function highlightLean(code: string): string {
  const stash: string[] = []
  // Placeholder indexes are letter-encoded (0 → 'a', 1 → 'b', …): a digit-based
  // placeholder would itself be matched by the numeric-literal pass below.
  const enc = (n: number) => {
    let s = ''
    do { s = String.fromCharCode(97 + (n % 26)) + s; n = Math.floor(n / 26) } while (n > 0)
    return s
  }
  const put = (cls: string) => (m: string) => {
    stash.push(`<span class="${cls}">${m}</span>`)
    return `\x00${enc(stash.length - 1)}\x00`
  }
  let h = htmlEscape(code)
  h = h.replace(/\/-[\s\S]*?-\//g, put('hl-comment'))
  h = h.replace(/--[^\n]*/g, put('hl-comment'))
  h = h.replace(/&quot;(?:[^&]|&(?!quot;))*?&quot;/g, put('hl-string'))
  h = h.replace(/\b(?:theorem|lemma|def|abbrev|axiom|instance|structure|inductive|class|mutual|end|namespace|section|open|variable|universe|noncomputable|protected|public|private)\b/g,
    put('hl-keyword'))
  h = h.replace(/\b(?:by|fun|let|do|if|then|else|match|with|return|pure|try|catch|simp|rw|rewrite|exact|intro|intros|have|show|suffices|induction|cases|constructor|refine|calc|ring|omega|norm_num|linarith|aesop|trivial|contradiction|exfalso|congr|ext|funext|sorry|decide|native_decide|apply|subst|change|where)\b/g,
    put('hl-keyword'))
  h = h.replace(/\b(?:true|false|none|some|True|False|None|Some|Nat|Int|Bool|String|Type|Prop|Sort)\b/g,
    put('hl-const'))
  h = h.replace(/\b\d+\b/g, put('hl-lit'))
  const dec = (s: string) => [...s].reduce((n, c) => n * 26 + (c.charCodeAt(0) - 97), 0)
  return h.replace(/\x00([a-z]+)\x00/g, (_, i) => stash[dec(i)])
}

/** Strip the "… := by ..." truncation tail so the display ends at the proposition. */
function trimSpecTail(spec: string): string {
  return spec.replace(/\s*:=\s*by\s*\.{2,}\s*$/, '')
             .replace(/\s*:=\s*\.{2,}\s*$/, '')
}

const GRADE = {
  proven: { tick: '✓✓', cls: 'lean-tick-proven', label: 'Lean specification — proof complete' },
  axiomatized: { tick: '△', cls: 'lean-tick-axiom', label: 'Lean specification — trusted assumption (axiomatized)' },
  incomplete: { tick: '◑', cls: 'lean-tick-incomplete', label: 'Lean specification — proof incomplete' },
} as const

function renderPanel(fn: FunctionRecord): string {
  const grade = GRADE[fn.status ?? 'incomplete']
  const parts: string[] = []
  parts.push(`<div class="lean-verification lean-${fn.status ?? 'incomplete'}">`)
  parts.push(`  <div class="lean-header"><span class="lean-tick ${grade.cls}">${grade.tick}</span> ${grade.label}</div>`)
  parts.push(`  <pre class="lean-code"><code>${highlightLean(trimSpecTail(fn.spec_statement!))}</code></pre>`)
  parts.push(`</div>`)
  return parts.join('\n')
}

// ---------- CSS ----------

const PANEL_CSS = `
/* Lean verification panel — injected by scripts/inject-lean-verification.ts */
.lean-verification {
  margin: 0.75rem 0 1rem 0;
  padding: 0.75rem 1rem;
  border: 1px solid var(--border-color, #d2d2d2);
  border-radius: 6px;
  background: var(--code-block-background-color, #f5f5f5);
  font-size: 0.95em;
}
.lean-header {
  font-weight: 500;
  font-size: 0.95em;
  margin-bottom: 0.5rem;
  color: var(--main-color, #333);
}
.lean-tick { font-weight: 700; margin-right: 0.15rem; }
.lean-tick-proven     { color: #1a7f37; }
.lean-tick-axiom      { color: #9a6700; }
.lean-tick-incomplete { color: #bc4c00; }
@media (prefers-color-scheme: dark) {
  .lean-tick-proven     { color: #5fb874; }
  .lean-tick-axiom      { color: #d4a72c; }
  .lean-tick-incomplete { color: #e8824a; }
}
html[data-theme="dark"] .lean-tick-proven,
html[data-theme="ayu"]  .lean-tick-proven     { color: #5fb874; }
html[data-theme="dark"] .lean-tick-axiom,
html[data-theme="ayu"]  .lean-tick-axiom      { color: #d4a72c; }
html[data-theme="dark"] .lean-tick-incomplete,
html[data-theme="ayu"]  .lean-tick-incomplete { color: #e8824a; }
/* Lean syntax-highlighting tokens (github-light theme) */
.lean-code .hl-keyword { color: #D73A49; }
.lean-code .hl-const   { color: #6F42C1; }
.lean-code .hl-lit     { color: #005CC5; }
.lean-code .hl-string  { color: #032F62; }
.lean-code .hl-comment { color: #6A737D; font-style: italic; }
@media (prefers-color-scheme: dark) {
  .lean-code .hl-keyword { color: #ff7b72; }
  .lean-code .hl-const   { color: #d2a8ff; }
  .lean-code .hl-lit     { color: #79c0ff; }
  .lean-code .hl-string  { color: #a5d6ff; }
  .lean-code .hl-comment { color: #8b949e; }
}
html[data-theme="dark"] .lean-code .hl-keyword,
html[data-theme="ayu"]  .lean-code .hl-keyword { color: #ff7b72; }
html[data-theme="dark"] .lean-code .hl-const,
html[data-theme="ayu"]  .lean-code .hl-const   { color: #d2a8ff; }
html[data-theme="dark"] .lean-code .hl-lit,
html[data-theme="ayu"]  .lean-code .hl-lit     { color: #79c0ff; }
html[data-theme="dark"] .lean-code .hl-string,
html[data-theme="ayu"]  .lean-code .hl-string  { color: #a5d6ff; }
html[data-theme="dark"] .lean-code .hl-comment,
html[data-theme="ayu"]  .lean-code .hl-comment { color: #8b949e; }
.lean-code {
  margin: 0.4rem 0;
  padding: 0.6rem 0.8rem;
  background: var(--code-block-background-color, #fafafa);
  border: 1px solid var(--border-color, #ddd);
  border-radius: 4px;
  overflow-x: auto;
  font-family: monospace;
  font-size: 0.88em;
  line-height: 1.5;
  white-space: pre;
}`

// ---------- HTML injection ----------

/** Walk forward from `from` to the end of a `<div class="docblock">` block. */
function findDocblockEnd(html: string, from: number, lookahead = 600): number | null {
  const docOpenRe = /<div class=['"]docblock['"][^>]*>/g
  docOpenRe.lastIndex = from
  const m = docOpenRe.exec(html)
  if (!m || m.index - from > lookahead) return null
  let pos = m.index + m[0].length
  let depth = 1
  while (pos < html.length && depth > 0) {
    const nextOpen = html.indexOf('<div', pos)
    const nextClose = html.indexOf('</div>', pos)
    if (nextClose === -1) return null
    if (nextOpen !== -1 && nextOpen < nextClose) {
      depth++
      const openEnd = html.indexOf('>', nextOpen)
      if (openEnd === -1) return null
      pos = openEnd + 1
    } else {
      depth--
      pos = nextClose + '</div>'.length
    }
  }
  return depth === 0 ? pos : null
}

/**
 * Inject `panelHtml` into a rustdoc page.
 *  - anchor '' → after the first </h1> (fn./constant. own pages).
 *  - anchored → after the `<section id="anchor(-N)?">`'s docblock (falls back
 *    to right after the section). With `implSig` the search is confined to the
 *    matching impl section's region.
 */
function injectPanel(
  html: string, anchor: string, implSig: ImplSig | null, panelHtml: string,
): { html: string; matchedId: string } | Error {
  if (anchor === '') {
    // Own-page items (fn./constant.): insert after the signature block
    // (<pre class="rust item-decl">) and, when present, after the top-level
    // description docblock — so the page reads signature → description →
    // Lean panel, matching the anchored (method) cases.
    const dm = /<pre class="rust item-decl"[^>]*>[\s\S]*?<\/pre>/.exec(html)
    if (dm) {
      const declEnd = dm.index + dm[0].length
      const docEnd = findDocblockEnd(html, declEnd, 800)
      const insertAt = docEnd ?? declEnd
      return {
        html: html.slice(0, insertAt) + '\n' + panelHtml + '\n' + html.slice(insertAt),
        matchedId: '',
      }
    }
    // Fallback for unexpected page shapes: after the first </h1>.
    const m = /(<h1[^>]*>[\s\S]*?<\/h1>)/.exec(html)
    if (!m) return new Error('no <h1> or item-decl found')
    const idx = m.index + m[0].length
    return { html: html.slice(0, idx) + '\n' + panelHtml + '\n' + html.slice(idx), matchedId: '' }
  }

  let searchStart = 0
  let searchEnd = html.length
  if (implSig) {
    const region = findImplRegion(html, implSig)
    if (region instanceof Error) return region
    searchStart = region.start
    searchEnd = region.end
  }

  const escAnchor = anchor.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')
  // Within an impl region rustdoc may suffix duplicate ids (`method.add-1`).
  const suffix = implSig ? '(?:-\\d+)?' : ''
  const sectionRe = new RegExp(`<section\\s+id="(${escAnchor}${suffix})"[^>]*>[\\s\\S]*?<\\/section>`, 'g')
  sectionRe.lastIndex = searchStart
  const m = sectionRe.exec(html)
  if (!m || m.index >= searchEnd) return new Error(`anchor '${anchor}' not found${implSig ? ' in impl region' : ''}`)
  const sectionEnd = m.index + m[0].length
  const docEnd = findDocblockEnd(html, sectionEnd)
  const insertAt = docEnd ?? sectionEnd
  return {
    html: html.slice(0, insertAt) + '\n' + panelHtml + '\n' + html.slice(insertAt),
    matchedId: m[1],
  }
}

/** Inject a <link> for the panel stylesheet into <head> if not already present. */
function injectStylesheetLink(html: string, relCssPath: string): string {
  if (html.includes(`href="${relCssPath}"`)) return html
  return html.replace(/(<\/head>)/, `  <link rel="stylesheet" href="${relCssPath}">\n$1`)
}

/** Strip previously injected panels (balanced <div> counting) → idempotent runs. */
function stripExistingPanels(html: string): string {
  let out = html
  const openRe = /<div\s+class="lean-verification[^"]*"[^>]*>/g
  while (true) {
    openRe.lastIndex = 0
    const m = openRe.exec(out)
    if (!m) break
    const start = m.index
    let pos = m.index + m[0].length
    let depth = 1
    while (pos < out.length && depth > 0) {
      const nextOpen = out.indexOf('<div', pos)
      const nextClose = out.indexOf('</div>', pos)
      if (nextClose === -1) break
      if (nextOpen !== -1 && nextOpen < nextClose) {
        depth++
        const openEnd = out.indexOf('>', nextOpen)
        if (openEnd === -1) break
        pos = openEnd + 1
      } else {
        depth--
        pos = nextClose + '</div>'.length
      }
    }
    if (depth !== 0) break
    let cleanStart = start
    let cleanEnd = pos
    if (out[cleanStart - 1] === '\n') cleanStart--
    if (out[cleanEnd] === '\n') cleanEnd++
    out = out.slice(0, cleanStart) + out.slice(cleanEnd)
  }
  return out
}

function relCssPathFor(htmlFile: string): string {
  const depth = htmlFile.split('/').length - 1
  return depth > 0 ? '../'.repeat(depth) + 'lean-verification.css' : 'lean-verification.css'
}

// ---------- Root index + provenance ----------

function writeRootIndex(cfg: Config, commit: string | null) {
  const commitLine = commit
    ? `commit <a href="${REPO_URL}/tree/${commit}"><code>${commit.slice(0, 12)}</code></a>`
    : 'commit unknown'
  const rustLine = cfg.rustVersion ? `, ${htmlEscape(cfg.rustVersion)}` : ''
  const html = `<!DOCTYPE html>
<html lang="en"><head><meta charset="utf-8">
<meta http-equiv="refresh" content="0; url=${CRATE}/index.html">
<title>spqr — Rust docs with Lean verification</title></head>
<body>
<p>Redirecting to <a href="${CRATE}/index.html">${CRATE} documentation</a>…</p>
<footer style="font-size:0.85em;color:#666">
  <p>Generated from ${commitLine}${rustLine}.
  Documented configuration: <code>--features extraction</code> with private items —
  the code configuration Aeneas translated to Lean. In this configuration the verified
  functions never dispatch to the arch-accelerated GF(2¹⁶) helpers (e.g.
  <code>mul2_u16</code> uses only the unaccelerated implementation); accelerated helper
  modules may still appear in these docs but carry no verification panels and are outside
  the verified scope. Lean specification panels are injected per function from
  <code>functions.json</code> (<code>lake exe docsjson</code>).</p>
</footer>
</body></html>
`
  fs.writeFileSync(path.join(cfg.rustdocRoot, 'index.html'), html, 'utf-8')
}

// ---------- Main ----------

function main() {
  const cfg = parseArgs()

  const fnsData = JSON.parse(fs.readFileSync(cfg.functionsJson, 'utf-8')) as {
    commit: string | null
    functions: FunctionRecord[]
  }
  const commit = fnsData.commit ?? null

  const overridesPath = path.join(path.dirname(new URL(import.meta.url).pathname), 'injection-overrides.json')
  const overrides: Record<string, Override> = fs.existsSync(overridesPath)
    ? JSON.parse(fs.readFileSync(overridesPath, 'utf-8'))
    : {}

  // Only spec'd records get panels; docsjson guarantees spec_statement for them.
  const specd = fnsData.functions.filter(f => f.has_spec)
  const failures: string[] = []
  for (const f of specd) {
    if (!f.spec_statement) failures.push(`${f.rust_name}: has_spec but no spec_statement (malformed functions.json)`)
  }

  // Stale overrides are themselves an error: an entry that no longer matches
  // any spec'd record means the mapping it patched has changed under it.
  // (Config errors are tracked apart from per-record failures so the final
  // accounting equation over spec'd records stays exact.)
  const configErrors: string[] = []
  const specdNames = new Set(specd.map(f => f.rust_name))
  for (const name of Object.keys(overrides)) {
    if (!specdNames.has(name)) configErrors.push(`override for '${name}' matches no spec'd record (stale?)`)
  }

  // Resolve targets. Skips are audited, not silent: they require a reason and
  // are reported in the summary.
  interface Job { fn: FunctionRecord; file: string; anchor: string; implSig: ImplSig | null }
  const jobs: Job[] = []
  const skipped: string[] = []
  for (const fn of specd) {
    const ov = overrides[fn.rust_name]
    if (ov && 'skip' in ov) {
      if (!ov.skip.trim()) failures.push(`override for '${fn.rust_name}' has an empty skip reason`)
      else skipped.push(`${fn.rust_name}: ${ov.skip}`)
      continue
    }
    if (ov) {
      jobs.push({ fn, file: ov.file, anchor: ov.anchor, implSig: null })
      continue
    }
    const target = rustNameToRustdoc(fn.rust_name)
    if (!target) {
      failures.push(`${fn.rust_name}: cannot derive rustdoc target`)
      continue
    }
    const file = target.fileCandidates.find(c => fs.existsSync(path.join(cfg.rustdocRoot, c)))
    if (!file) {
      failures.push(`${fn.rust_name}: no HTML file among [${target.fileCandidates.join(', ')}]`)
      continue
    }
    jobs.push({ fn, file, anchor: target.anchor, implSig: target.implSig })
  }

  // Group jobs by file and inject.
  const byFile = new Map<string, Job[]>()
  for (const j of jobs) {
    const arr = byFile.get(j.file) ?? []
    arr.push(j)
    byFile.set(j.file, arr)
  }

  fs.writeFileSync(path.join(cfg.rustdocRoot, 'lean-verification.css'), PANEL_CSS, 'utf-8')

  let panelsInjected = 0
  let filesModified = 0
  for (const [file, entries] of byFile) {
    const abs = path.join(cfg.rustdocRoot, file)
    const originalHtml = fs.readFileSync(abs, 'utf-8')
    let html = stripExistingPanels(originalHtml)

    // Duplicate-target guard keyed on the RESOLVED section id: two records
    // resolving to the same HTML section (e.g. stale generics both matching
    // one remaining impl) is an error even when their requested targets differ.
    const claimedIds = new Map<string, string>()
    for (const e of entries) {
      const panel = renderPanel(e.fn)
      const next = injectPanel(html, e.anchor, e.implSig, panel)
      if (next instanceof Error) {
        failures.push(`${e.fn.rust_name} → ${file}#${e.anchor}: ${next.message}`)
      } else {
        const idKey = next.matchedId || '<page-top>'
        const prev = claimedIds.get(idKey)
        if (prev) {
          failures.push(`${e.fn.rust_name} → ${file}#${idKey}: section already claimed by ${prev}`)
          continue
        }
        claimedIds.set(idKey, e.fn.rust_name)
        html = next.html
        panelsInjected++
      }
    }

    if (html !== originalHtml) {
      html = injectStylesheetLink(html, relCssPathFor(file))
      fs.writeFileSync(abs, html, 'utf-8')
      filesModified++
    }
  }

  writeRootIndex(cfg, commit)

  console.log('[inject-lean-verification] done')
  console.log(`  Spec'd records:  ${specd.length}`)
  console.log(`  Panels injected: ${panelsInjected}`)
  console.log(`  Files modified:  ${filesModified}`)
  if (skipped.length > 0) {
    console.log(`  Skipped via injection-overrides.json (${skipped.length}):`)
    for (const s of skipped) console.log(`    ⊘ ${s}`)
  }
  // Belt-and-suspenders: every spec'd record is accounted for as injected,
  // audited-skip, or per-record failure.
  if (panelsInjected + skipped.length + failures.length !== specd.length) {
    configErrors.push(`accounting mismatch: ${panelsInjected} injected + ${skipped.length} skipped + ` +
      `${failures.length} failed ≠ ${specd.length} spec'd records`)
  }
  const errors = [...failures, ...configErrors]
  if (errors.length > 0) {
    console.error(`\n[inject-lean-verification] FAILED — ${errors.length} error(s):`)
    for (const e of errors) console.error(`  ✗ ${e}`)
    process.exit(1)
  }
}

main()
