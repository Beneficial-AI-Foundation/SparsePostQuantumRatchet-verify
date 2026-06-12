/**
 * Distill the (large, machine-specific) charon `.llbc` into a small,
 * path-normalized `llbc-summary.json` for the verification-status utility.
 */
import fs from "node:fs";

interface FunSummary {
  def_id: number;
  rust_name: string;
  source: string;
  line_start: number;
  line_end: number;
  is_public: boolean;
  is_local: boolean;
  opacity: string;
  is_global_initializer: boolean;
  is_unsafe: boolean;
}

/** Rewrite an absolute source path into a stable, machine-independent form. */
function normalizePath(p: string, repoRoot: string): string {
  // rustc sysroot std sources: .../rustc/<optional-hash>/library/... -> rustc/library/...
  p = p.replace(/^.*\/rustc\/(?:[0-9a-f]{6,}\/)?/, "rustc/");
  // cargo registry: .../cargo/registry/src/index.crates.io-<hash>/<crate>-<ver>/... -> cargo/registry/<crate>-<ver>/...
  p = p.replace(/^.*\/cargo\/registry\/src\/[^/]*\//, "cargo/registry/");
  // build-script (prost) output: .../target/<triple>/<profile>/build/<pkg>-<hash>/out/... -> target/out/...
  p = p.replace(/^.*\/target\/.*\/out\//, "target/out/");
  // anything still rooted at the repo dir -> crate-relative
  if (p.startsWith(repoRoot + "/")) p = p.slice(repoRoot.length + 1);
  return p;
}

/** An LLBC name is a list of path components; keep the `Ident`s, joined by `::`. */
function rustName(nameArr: unknown[]): string {
  return nameArr
    .map((c) =>
      c && typeof c === "object" && "Ident" in c
        ? ((c as { Ident: [string, number] }).Ident[0])
        : null,
    )
    .filter((s): s is string => typeof s === "string")
    .join("::");
}

/** Read `llbcPath`, project + normalize, and write `outPath`. */
export function writeLlbcSummary(llbcPath: string, outPath: string, repoRoot: string): number {
  const llbc = JSON.parse(fs.readFileSync(llbcPath, "utf-8"));
  const t = llbc.translated;

  const files = new Map<number, string>();
  for (const f of t.files ?? []) {
    const nm = f.name ?? {};
    const raw = typeof nm.Local === "string" ? nm.Local : typeof nm.Virtual === "string" ? nm.Virtual : "";
    files.set(f.id, normalizePath(raw, repoRoot));
  }

  const functions: FunSummary[] = [];
  for (const fd of t.fun_decls ?? []) {
    if (fd == null || fd.def_id == null) continue; // skip sparse-vector null holes
    const im = fd.item_meta ?? {};
    const span = im.span?.data ?? {};
    functions.push({
      def_id: fd.def_id,
      rust_name: rustName(im.name ?? []),
      source: files.get(span.file_id) ?? "",
      line_start: span.beg?.line ?? 0,
      line_end: span.end?.line ?? 0,
      is_public: im.attr_info?.public ?? false,
      is_local: im.is_local ?? false,
      opacity: typeof im.opacity === "string" ? im.opacity : "",
      is_global_initializer: fd.is_global_initializer ?? false,
      is_unsafe: fd.signature?.is_unsafe ?? false,
    });
  }
  // Sort by def_id for byte-stable output.
  functions.sort((a, b) => a.def_id - b.def_id);

  const out = { crate: t.crate_name, charon_version: llbc.charon_version, functions };
  fs.writeFileSync(outPath, JSON.stringify(out, null, 2) + "\n");
  return functions.length;
}
