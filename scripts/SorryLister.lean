/-
Generate a machine-readable sorry manifest for CI delta reporting.

Usage:
  lake env lean scripts/SorryLister.lean

Scans all `Spqr.*` modules reachable via `import Spqr` (i.e. those
already part of the build), then for each theorem/def/opaque/axiom that
transitively depends on `sorryAx`, classifies it as `direct` (body
itself references `sorryAx`) or `transitive` (calls something that
eventually reaches `sorryAx`).

Any `Spqr.*` module not imported by the root `Spqr` module will not be
scanned.  Ensure new modules are re-exported from `Spqr.lean`.

Writes sorted output to `sorry-manifest.txt`, one line per declaration:
  <module> <declaration> <direct|transitive>
-/
import Spqr

open Lean Elab Command

run_cmd liftTermElabM do
  let env ← getEnv
  let moduleNames := env.header.moduleNames

  let mut projectModuleIdxs : Std.HashSet Nat := {}
  for h : i in [:moduleNames.size] do
    let m := moduleNames[i]
    if m == `Spqr || m.getRoot == `Spqr then
      projectModuleIdxs := projectModuleIdxs.insert i

  let (moduleLookup, allProjectDecls) :=
    env.constants.fold
      (init := (({} : Std.HashMap Name Name), (#[] : Array Name)))
    fun acc nm ci =>
      let (ml, pa) := acc
      match env.getModuleIdxFor? nm with
      | some idx =>
        if !projectModuleIdxs.contains idx.toNat then acc
        else
          match ci with
          | .thmInfo _ | .defnInfo _ | .opaqueInfo _ | .axiomInfo _ =>
            (ml.insert nm (moduleNames[idx.toNat]?.getD `unknown), pa.push nm)
          | _ => acc
      | none => acc

  let mut axiomCache : Std.HashMap Name (Array Name) := {}
  for h : i in [:allProjectDecls.size] do
    let nm := allProjectDecls[i]
    let usedAxioms ← Lean.collectAxioms nm
    axiomCache := axiomCache.insert nm usedAxioms

  let getBodyRefs (nm : Name) : Array Name :=
    match env.find? nm with
    | some (.thmInfo   ci) => ci.value.getUsedConstants
    | some (.defnInfo  ci) => ci.value.getUsedConstants
    | some (.opaqueInfo ci) => ci.value.getUsedConstants
    | _ => #[]

  let mut directSorrySet : Std.HashSet Name := {}
  for h : i in [:allProjectDecls.size] do
    let nm := allProjectDecls[i]
    if (getBodyRefs nm).any (· == ``sorryAx) then
      directSorrySet := directSorrySet.insert nm

  let mut lines : Array String := #[]
  for h : i in [:allProjectDecls.size] do
    let nm := allProjectDecls[i]
    let usedAxioms := axiomCache[nm]?.getD #[]
    if usedAxioms.any (· == ``sorryAx) then
      let modName := moduleLookup[nm]?.map toString |>.getD "(unknown)"
      let kind := if directSorrySet.contains nm then "direct" else "transitive"
      lines := lines.push s!"{modName} {nm} {kind}"

  let sorted := lines.qsort (· < ·)
  let content := String.join (sorted.toList.map (· ++ "\n"))
  IO.FS.writeFile "sorry-manifest.txt" content
  logInfo m!"sorry-manifest.txt written ({sorted.size} sorry-tainted declarations)"
