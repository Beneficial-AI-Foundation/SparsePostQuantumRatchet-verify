import Lean
import Utils.Config
/-! Analysis: spec-existence, verification status, dependency and axiom analysis.

* `isVerified`: the spec's own proof has no `sorry` (i.e. verified *assuming* every spec theorem it
calls is proven);
* `isFullyVerified`: proof depends only on the standard permitted axioms. -/

open Lean

namespace Utils.Lib.Analysis

/-- Spec theorem name for a function: `foo` ↦ `foo_spec`. -/
def getSpecName (name : Name) : Name := name.appendAfter Utils.Config.specSuffix

/-- Direct dependencies of a constant, from its value expression. -/
def getDirectDeps (env : Environment) (name : Name) : Array Name :=
  match env.find? name with
  | some ci =>
    match ci.value? (allowOpaque := true) with
    | some value => value.getUsedConstants
    | none => #[]
  | none => #[]

/-- Keep only dependencies that are in the given set of known functions. -/
def filterToKnownFunctions (knownNames : Std.HashSet Name) (deps : Array Name) : Array Name :=
  deps.filter (fun n => knownNames.contains n)

/-- Does a spec theorem exist for this function? -/
def hasSpecTheorem (env : Environment) (name : Name) : Bool :=
  env.find? (getSpecName name) |>.isSome

/-- Does a declaration's own proof term directly use `sorry`? -/
def proofContainsSorry (env : Environment) (name : Name) : Bool :=
  match env.find? name with
  | some ci =>
    match ci.value? (allowOpaque := true) with
    | some value => value.getUsedConstants.any (· == ``sorryAx)
    | none => true
  | none => true

/-- Verified *modulo specs*: the spec exists and its own proof has no `sorry`
    (calls to other, possibly-unproven, spec theorems are assumed). -/
def isVerified (env : Environment) (name : Name) : Bool :=
  match env.find? (getSpecName name) with
  | some _ => !proofContainsSorry env (getSpecName name)
  | none => false

/-- Transitive function dependencies within `knownNames`. -/
partial def getTransitiveDeps (env : Environment) (knownNames : Std.HashSet Name)
    (name : Name) (visited : Std.HashSet Name := {}) : Std.HashSet Name :=
  if visited.contains name then visited
  else
    let visited := visited.insert name
    let deps := filterToKnownFunctions knownNames (getDirectDeps env name)
    deps.foldl (fun acc dep => getTransitiveDeps env knownNames dep acc) visited

/-- Fully verified: this function's spec is proven and every transitively-called
    function's spec is also proven. -/
def isFullyVerified (env : Environment) (knownNames : Std.HashSet Name) (name : Name) : Bool :=
  if !isVerified env name then false
  else
    let transitive := (getTransitiveDeps env knownNames name).erase name
    transitive.toList.all (isVerified env)

/-! ## Axiom analysis (new) -/

inductive AxiomKind where
  | sorryAx   -- the Lean `sorry`
  | builtin   -- propext / Classical.choice / Quot.sound
  | external  -- a trusted external model (axiom declared under `SrcTranslated.*`)
  | other     -- any other axiom
  deriving DecidableEq, Repr

def AxiomKind.toString : AxiomKind → String
  | .sorryAx => "sorry"
  | .builtin => "builtin"
  | .external => "external"
  | .other => "other"

private def isBuiltinAxiom (n : Name) : Bool :=
  n == ``propext || n == ``Classical.choice || n == ``Quot.sound

/-- Classify an axiom by where it comes from. -/
def classifyAxiom (env : Environment) (n : Name) : AxiomKind :=
  if n == ``sorryAx then .sorryAx
  else if isBuiltinAxiom n then .builtin
  else
    match env.getModuleIdxFor? n with
    | some idx =>
      let m := env.allImportedModuleNames[idx.toNat]!
      if m.getRoot == Utils.Config.extractedRoot then .external else .other
    | none => .other

/-- Transitive axiom closure of a declaration's proof: BFS over the constants
    used in proof/value terms, collecting those that are themselves axioms.
    (Same closure as `Lean.collectAxioms`, restricted to what we need.) -/
partial def collectAxioms (env : Environment) (root : Name) : Array Name := Id.run do
  let mut visited : Std.HashSet Name := {}
  let mut axioms : Std.HashSet Name := {}
  let mut queue : Array Name := #[root]
  let mut i := 0
  while h : i < queue.size do
    let nm := queue[i]
    i := i + 1
    if visited.contains nm then continue
    visited := visited.insert nm
    match env.find? nm with
    | some (.axiomInfo _) => axioms := axioms.insert nm
    | some ci =>
      match ci.value? (allowOpaque := true) with
      | some v => for r in v.getUsedConstants do
          if !visited.contains r then queue := queue.push r
      | none => pure ()
    | none => pure ()
  return axioms.toArray

/-- The classified axioms used by a function's spec theorem (including the
    builtin `propext` / `Classical.choice` / `Quot.sound`). -/
def specAxioms (env : Environment) (name : Name) : Array (Name × AxiomKind) :=
  let specName := getSpecName name
  if env.find? specName |>.isNone then #[]
  else
    (collectAxioms env specName).map (fun a => (a, classifyAxiom env a))

end Utils.Lib.Analysis
