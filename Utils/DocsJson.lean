/-
  docsjson: per-function verification records for the rustdoc Lean-spec panels.

  Reads `translation.json` (Aeneas `emit-json`) and the compiled Lean environment, and writes
  `functions.json`: one record per crate-local extracted function (loop artifacts excluded;
  trait impls and opaque functions INCLUDED — unlike `status.json`), carrying the spec theorem's
  source text and a soundness grade for `scripts/inject-lean-verification.ts`.

  Any function that has a spec theorem but whose statement cannot be extracted from source is a
  hard error: the exe exits nonzero so CI never publishes docs with silently missing panels.

  Run with:  lake exe docsjson [output.json]
-/
import Lean
import Utils.Config
import Utils.Lib.Analysis
import Utils.Lib.Translation

open Lean
open Utils.Lib.Analysis Utils.Lib.Translation

/-- Import the spqr environment (hand-written specs + extracted code). -/
def loadEnvironment : IO Environment := do
  Lean.initSearchPath (← Lean.findSysroot)
  importModules #[{ module := Utils.Config.mainModule }] {}

/-- Resolve a `translation.json` `lean_name` against the environment. Aeneas's `emit-json`
prefixes every crate-local function with the crate name, but hand-written externals in
`SrcTranslated/FunsExternal.lean` are declared at the root (e.g. `kdf.hkdf_to_slice`, with only
an `open spqr` in scope) — so for local-but-opaque functions the claimed name may not exist and
the crate-prefix-stripped name is the real declaration. -/
def resolveLeanName (env : Environment) (leanName : String) : Name :=
  let name := leanName.toName
  if env.find? name |>.isSome then name
  else
    let crateDot := Utils.Config.crateName ++ "."
    if leanName.startsWith crateDot then
      let stripped := (leanName.drop crateDot.length).toString.toName
      if env.find? stripped |>.isSome then stripped else name
    else name

/-- JSON record for one extracted function; `IO.userError` when spec extraction fails.
`allSpecs` is the set of all panel-rendered spec theorem names (see `specStatus`). -/
def functionJson (env : Environment) (allSpecs : Std.HashSet Name) (f : TransFun) :
    IO Json := do
  let name := resolveLeanName env f.leanName
  let hasSpec := hasSpecTheorem env name
  let base : List (String × Json) := [
    ("rust_name", Json.str f.rustName),
    ("lean_name", Json.str f.leanName),
    ("source", Json.str f.source),
    ("line_start", toJson f.lineStart),
    ("line_end", toJson f.lineEnd),
    ("is_opaque", Json.bool f.isOpaque),
    ("has_spec", Json.bool hasSpec)
  ]
  if !hasSpec then return Json.mkObj base
  let specName := getSpecName name
  let parts ← getSpecParts env name
  let some statement := parts.statement
    | throw <| IO.userError s!"docsjson: failed to extract statement of {specName} from source"
  let some specFile := getSpecFilePath env name
    | throw <| IO.userError s!"docsjson: cannot resolve defining module of {specName}"
  let status := specStatus env allSpecs name
  let axioms := (specNonCoreAxioms env name).qsort (fun a b => a.toString < b.toString)
  return Json.mkObj (base ++ [
    ("spec_name", Json.str specName.toString),
    ("spec_file", Json.str specFile),
    ("spec_docstring", match parts.docstring with
      | some d => Json.str d
      | none => Json.null),
    ("spec_statement", Json.str statement),
    ("spec_kind", Json.str (match env.find? specName with
      | some (.axiomInfo _) => "axiom"
      | _ => "theorem")),
    ("status", Json.str status.toString),
    ("axioms", Json.arr (axioms.map (fun a => Json.str a.toString)))
  ])

/-- Best-effort current commit hash (for the provenance header). -/
def gitCommit : IO (Option String) := do
  try
    let out ← IO.Process.output { cmd := "git", args := #["rev-parse", "HEAD"] }
    if out.exitCode == 0 then return some out.stdout.trimAscii.toString else return none
  catch _ => return none

def main (args : List String) : IO UInt32 := do
  let outPath := args[0]?.getD Utils.Config.docsJsonOutPath
  if let some parent := (System.FilePath.mk outPath).parent then
    IO.FS.createDirAll parent
  IO.eprintln "Loading spqr environment..."
  let env ← loadEnvironment
  IO.eprintln "Reading translation.json..."
  let allFuns ← readTranslationWithGlobals
  IO.eprintln s!"  {allFuns.size} function + global entries"
  -- Crate-local functions only; loop wrappers/bodies share their parent's `rust_name`, so they
  -- must not produce records (they'd collide with the parent's rustdoc anchor).
  let funs := allFuns.filter fun f => f.isLocal && !f.isLoopArtifact
  if funs.isEmpty then
    throw <| IO.userError "docsjson: no crate-local functions parsed from translation.json \
      (schema change?)"
  -- The per-field JSON accessors are lenient (missing string → ""); a renamed field would
  -- silently blank every record, so require the fields the injector depends on.
  for f in funs do
    if f.leanName.isEmpty || f.rustName.isEmpty || f.source.isEmpty then
      throw <| IO.userError s!"docsjson: crate-local record with empty lean_name/rust_name/\
        source (def_id {f.defId}) — translation.json schema change?"
  IO.eprintln s!"  {funs.size} crate-local entries (trait impls and opaques included)"

  -- The set of panel-rendered spec theorems, used both for grading (nearest-visible-spec
  -- blame in `specStatus`) and for the reverse-coverage gate below.
  let claimed : Std.HashSet Name := funs.foldl (init := {}) fun acc f =>
    let n := resolveLeanName env f.leanName
    if hasSpecTheorem env n then acc.insert (getSpecName n) else acc

  let records ← funs.mapM (functionJson env claimed)

  -- Reverse-coverage gate: every hand-written spec theorem (`Spqr.Specs.*`) whose subject is
  -- a crate declaration must be claimed by some emitted record. Catches records lost to
  -- translation.json drift (e.g. constants vanishing from the `globals` array) that the
  -- forward direction cannot see. Loop-artifact sub-lemmas (`*_loop*`) have no rustdoc
  -- anchor of their own and are exempt.
  let specsPrefix : Name := `Spqr.Specs
  let isOrphan (declName : Name) : Bool :=
    match declName with
    | .str base last =>
      last.endsWith "_spec" && !last.startsWith "_"
        && (match declModule? env declName with
            | some m => specsPrefix.isPrefixOf m
            | none => false)
        && (let subject := Name.str base ((last.dropEnd 5).toString)
            let subjectStr := subject.toString
            (subjectStr.splitOn "_loop").length == 1     -- not a loop-artifact sub-lemma
              && subjectStr.startsWith (Utils.Config.crateName ++ ".")
              && (env.find? subject).isSome
              && !claimed.contains declName)
    | _ => false
  let orphans := env.constants.fold (init := #[]) fun acc n _ =>
    if isOrphan n then acc.push n else acc
  unless orphans.isEmpty do
    throw <| IO.userError s!"docsjson: {orphans.size} spec theorem(s) have no emitted record \
      (translation.json drift?): {orphans.toList}"

  let mut proven := 0
  let mut axiomatized := 0
  let mut incomplete := 0
  for f in funs do
    let name := resolveLeanName env f.leanName
    if hasSpecTheorem env name then
      match specStatus env claimed name with
      | .proven => proven := proven + 1
      | .axiomatized => axiomatized := axiomatized + 1
      | .incomplete => incomplete := incomplete + 1

  let header : List (String × Json) := [
    ("generated_by", Json.str "lake exe docsjson"),
    ("commit", match (← gitCommit) with
      | some c => Json.str c
      | none => Json.null),
    ("functions", Json.arr records)
  ]
  IO.FS.writeFile outPath ((Json.mkObj header).pretty ++ "\n")
  IO.println s!"Wrote {outPath}: {funs.size} functions — \
    {proven} proven, {axiomatized} axiomatized, {incomplete} incomplete."
  return 0
