/-
  status: verification-status report for the spqr crate.

  Joins `translation.json` (Aeneas: Lean decl ↔ Rust `def_id`) with `spqr.llbc`
  (charon: Rust name / source / visibility), then queries the Lean environment
  for each extracted function: does a `_spec` theorem exist, which axioms it
  uses, and its verification status. Writes `status.json`.

  Run with:  lake exe status [output.json]
-/
import Lean
import Utils.Config
import Utils.Lib.Analysis
import Utils.Lib.Join

open Lean
open Utils.Lib.Analysis Utils.Lib.Join

/-- Import the spqr environment (hand-written specs + extracted code). -/
def loadEnvironment : IO Environment := do
  Lean.initSearchPath (← Lean.findSysroot)
  importModules #[{ module := Utils.Config.mainModule }] {}

/-- JSON record for one extracted function. -/
def functionJson (env : Environment) (known : Std.HashSet Name)
    (f : TransFun) (fm : FunMeta) : Json :=
  let name := f.leanId.toName
  let exists_ := env.find? name |>.isSome
  let hasSpec := hasSpecTheorem env name
  let deps := (filterToKnownFunctions known (getDirectDeps env name)).qsort
    (fun a b => a.toString < b.toString)
  let base : List (String × Json) := [
    ("lean_id", Json.str f.leanId),
    ("def_id", toJson f.defId),
    ("rust_name", Json.str fm.rustName),
    ("source", Json.str fm.source),
    ("line_start", toJson fm.lineStart),
    ("line_end", toJson fm.lineEnd),
    ("is_public", Json.bool fm.isPublic),
    ("is_local", Json.bool fm.isLocal),
    ("opacity", Json.str fm.opacity),
    ("is_opaque", Json.bool f.isOpaque),
    ("is_global_initializer", Json.bool fm.isGlobalInit),
    ("is_unsafe", Json.bool fm.isUnsafe),
    ("is_extraction_artifact", Json.bool f.isLoopArtifact),
    ("can_fail", Json.bool f.canFail),
    ("exists", Json.bool exists_),
    ("has_spec", Json.bool hasSpec),
    ("dependencies", Json.arr (deps.map (fun d => Json.str d.toString)))
  ]
  -- Only meaningful when a spec theorem exists.
  let specFields : List (String × Json) :=
    if hasSpec then
      [ ("spec_name", Json.str (getSpecName name).toString),
        ("verified_modulo_specs", Json.bool (isVerified env name)),
        ("axioms", Json.arr (((specAxioms env name).qsort
          (fun a b => a.toString < b.toString)).map (fun a => Json.str a.toString))) ]
    else []
  Json.mkObj (base ++ specFields)

def main (args : List String) : IO UInt32 := do
  let outPath := args[0]?.getD Utils.Config.statusOutPath
  IO.eprintln "Loading spqr environment..."
  let env ← loadEnvironment
  IO.eprintln "Reading translation.json + spqr.llbc..."
  let (allFuns, metaMap) ← readArtifacts
  IO.eprintln s!"  {allFuns.size} function entries, {metaMap.size} LLBC fun_decls"
  -- Restrict the report to functions defined in the crate under study.
  let funs := allFuns.filter fun f => (metaMap.getD f.defId default).isLocal
  IO.eprintln s!"  {funs.size} crate-local entries (filtered from {allFuns.size})"
  -- Known function set (for dependency filtering): resolvable, crate-local lean ids.
  let known : Std.HashSet Name := funs.foldl (init := {}) fun acc f =>
    let n := f.leanId.toName
    if env.find? n |>.isSome then acc.insert n else acc

  let records := funs.map fun f =>
    functionJson env known f (metaMap.getD f.defId default)

  -- Output is a bare array of per-function records; consumers derive any
  -- summary/filtered views from the metadata themselves.
  IO.FS.writeFile outPath ((Json.arr records).pretty ++ "\n")
  let specifiedN := (funs.filter (fun f => hasSpecTheorem env f.leanId.toName)).size
  IO.println s!"Wrote {outPath}: {funs.size} functions, {specifiedN} specified."
  return 0
