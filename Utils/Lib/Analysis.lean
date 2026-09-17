import Lean
import Utils.Config
/-! Analysis: spec-existence, verification status, dependency and axiom analysis.

* `isVerified`: the spec's own proof has no `sorry`;
* `specAxioms`: the spec's full transitive axiom closure. -/

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

/-- Verified *modulo specs*: the spec exists and its own proof has no `sorry`. -/
def isVerified (env : Environment) (name : Name) : Bool :=
  match env.find? (getSpecName name) with
  | some _ => !proofContainsSorry env (getSpecName name)
  | none => false

/-! Axiom analysis: There is no separate "fully verified" predicate: a spec is fully proven iff its
axoms contains no `sorryAx`. Consumers read that directly off the emitted `axioms` list. -/

abbrev EnvM := ReaderT Environment Id
instance : MonadEnv EnvM where
  getEnv := read
  modifyEnv _ := pure ()

/-- The axioms in a spec theorem's transitive closure, via `Lean.collectAxioms`. -/
def specAxioms (env : Environment) (name : Name) : Array Name :=
  let specName := getSpecName name
  if env.find? specName |>.isNone then #[]
  else Id.run <| (Lean.collectAxioms (m := EnvM) specName).run env

/-! ## Spec grading (for `lake exe docsjson`)

Grades a spec'd function for the rustdoc verification panels:
* `proven` — the spec is a theorem and no `sorry` (or untrusted axiom) is reachable through
  its own proof chain, where other panel-rendered spec theorems are treated as opaque
  ("blame the nearest visible spec": using an incomplete spec does not re-taint the user,
  since that spec reports its own status on its own panel);
* `axiomatized` — the `_spec` declaration is itself an axiom (a trusted assumption, used for
  functions kept opaque during extraction, e.g. `hkdf_to_slice`);
* `incomplete` — `sorryAx`, `Lean.trustCompiler`, or an unrecognized axiom in the spec's own
  proof chain.

Trusted axioms: Lean core, `Utils.Config.trustedAxiomModules`/`ModulePrefixes`, and
origin-authenticated native decision certificates. -/

/-- The Lean core axioms every classical proof may use. -/
def coreAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The module a declaration comes from, if it was imported (not in the current file). -/
def declModule? (env : Environment) (name : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? name
  env.allImportedModuleNames[idx.toNat]?

/-- Is this axiom part of the trusted base (an exact trusted module, or under a trusted
module prefix)? -/
def axiomIsTrusted (env : Environment) (ax : Name) : Bool :=
  match declModule? env ax with
  | none => false
  | some m =>
    Utils.Config.trustedAxiomModules.contains m
      || Utils.Config.trustedAxiomModulePrefixes.any (·.isPrefixOf m)

/-- `bv_decide`/`native_decide` discharge goals via an external checker and record the
kernel-checked certificate as a per-proof scoped axiom `<decl>._native.<tactic>.ax_*` — the
same trust tier as `Lean.ofReduceBool` (native-code evaluation of the certificate checker).
These are part of the standard Lean tactic toolbox, so they count as trusted; they still
appear in the panel's axiom list so the trust base stays visible.

Origin is authenticated, not just name-matched: the name's prefix before `_native` must be an
existing declaration living in the SAME module as the certificate axiom (auto-generated
certificates are always emitted alongside their parent declaration). -/
def isNativeCertAxiom (env : Environment) (n : Name) : Bool :=
  let cs := n.components
  match cs.idxOf? (Name.mkSimple "_native") with
  | none => false
  | some i =>
    let tail := cs.drop (i + 1)
    let isDecideCert := tail.contains (Name.mkSimple "bv_decide")
      || tail.contains (Name.mkSimple "decide")
    let parent := (cs.take i).foldl (· ++ ·) Name.anonymous
    isDecideCert
      && (env.find? parent).isSome
      && declModule? env n == declModule? env parent

inductive SpecStatus where
  | proven | axiomatized | incomplete
  deriving Repr, BEq

def SpecStatus.toString : SpecStatus → String
  | .proven => "proven"
  | .axiomatized => "axiomatized"
  | .incomplete => "incomplete"

/-- Is `sorryAx` (or an untrusted axiom) reachable from the proof of `root`, treating every
OTHER declaration in `stops` (the panel-rendered spec theorems) as opaque?

This implements *blame-the-nearest-visible-spec* grading: a spec whose own proof chain is
`sorry`-free counts as proven even when a spec theorem it merely *applies* is incomplete —
that incompleteness is already reported on the applied spec's own panel. Helper lemmas
without panels (e.g. loop-body sub-lemmas) ARE expanded, so their `sorry` taints the
nearest rendered spec. -/
partial def proofTaintedExcluding (env : Environment) (stops : Std.HashSet Name)
    (root : Name) : Bool := Id.run do
  let mut visited : Std.HashSet Name := {}
  let mut work : Array Name := #[root]
  while h : work.size > 0 do
    let n := work[work.size - 1]'(by omega)
    work := work.pop
    if visited.contains n then continue
    visited := visited.insert n
    if n == ``sorryAx then return true
    if n != root && stops.contains n then continue
    match env.find? n with
    | none => continue
    | some (.axiomInfo _) =>
      if !(coreAxioms.contains n || axiomIsTrusted env n || isNativeCertAxiom env n) then
        return true
    | some ci =>
      match ci.value? (allowOpaque := true) with
      | some v => work := work ++ v.getUsedConstants
      | none => continue
  return false

/-- Grade the spec theorem of `name` (assumes `hasSpecTheorem env name`).
`allSpecs` is the set of panel-rendered spec theorem names (for nearest-visible-spec
blame; the spec's own name is always expanded). -/
def specStatus (env : Environment) (allSpecs : Std.HashSet Name) (name : Name) : SpecStatus :=
  let specName := getSpecName name
  match env.find? specName with
  -- A spec declared as an axiom is graded `axiomatized` wherever it lives: the △ glyph
  -- makes the assumption visible, and `incomplete` is reserved for spec *theorems* whose
  -- own proof chain still contains `sorry` (or an untrusted axiom).
  | some (.axiomInfo _) => .axiomatized
  | some _ =>
    if proofTaintedExcluding env allSpecs specName then .incomplete else .proven
  | none => .incomplete

/-- The spec's axiom dependencies minus the Lean core axioms (the panel-visible trust base). -/
def specNonCoreAxioms (env : Environment) (name : Name) : Array Name :=
  (specAxioms env name).filter (fun a => !coreAxioms.contains a)

/-! ## Spec source extraction

Reads the spec theorem's docstring and statement verbatim from its source file (preserving the
hand-written formatting and notation), truncating the statement at `:= by`. Ported from the
curve25519-dalek-lean-verify status tooling, extended to tolerate `lemma`, visibility modifiers,
and attributes on the same line as the declaration. -/

/-- File path (relative to the project root) of the module defining the spec theorem,
e.g. `Spqr/Specs/Encoding/Gf/GF16/Mul.lean`. -/
def getSpecFilePath (env : Environment) (name : Name) : Option String := do
  let m ← declModule? env (getSpecName name)
  return m.toString.replace "." "/" ++ ".lean"

/-- Result of extracting spec theorem parts from source. -/
structure SpecParts where
  docstring : Option String := none
  statement : Option String := none
  deriving Repr, Inhabited

/-- Drop a leading `@[...]` attribute group from a (trimmed) declaration line. -/
def stripLeadingAttrs (s : String) : String :=
  let t := s.trimAsciiStart.toString
  if t.startsWith "@[" then
    match (t.splitOn "]").tail with
    | [] => t
    | rest => (String.intercalate "]" rest).trimAsciiStart.toString
  else t

/-- Does this line start the theorem statement (after attributes/modifiers)? -/
def isDeclLine (line : String) : Bool :=
  let t := stripLeadingAttrs line
  let t := if t.startsWith "private " then (t.drop 8).trimAsciiStart.toString
           else if t.startsWith "protected " then (t.drop 10).trimAsciiStart.toString
           else t
  t.startsWith "theorem " || t.startsWith "lemma " || t.startsWith "axiom "

/-- A processed statement line and whether it ends the statement. -/
structure StatementLineResult where
  line : String
  isEnd : Bool

/-- Truncate a statement line at `:= by` (or a trailing `:=`), marking the statement's end. -/
def processStatementLine (line : String) : StatementLineResult :=
  let parts := line.splitOn ":= by"
  if parts.length > 1 then
    { line := parts[0]!.trimAsciiEnd.toString ++ " := by ...", isEnd := true }
  else if line.trimAsciiEnd.toString.endsWith ":=" then
    { line := line.trimAsciiEnd.toString ++ " ...", isEnd := true }
  else
    { line := line, isEnd := false }

/-- Parse the declaration's source lines into docstring and statement components. -/
def parseSpecSource (relevantLines : Array String) : SpecParts := Id.run do
  let mut docstringLines : Array String := #[]
  let mut statementLines : Array String := #[]
  let mut inDocstring := false
  for line in relevantLines do
    if statementLines.isEmpty then
      if inDocstring then
        docstringLines := docstringLines.push line
        if (line.splitOn "-/").length > 1 then
          inDocstring := false
      else if line.trimAsciiStart.toString.startsWith "/-" then
        inDocstring := true
        docstringLines := docstringLines.push line
        if (line.splitOn "-/").length > 1 then
          inDocstring := false
      else if isDeclLine line then
        let result := processStatementLine (stripLeadingAttrs line)
        statementLines := statementLines.push result.line
        if result.isEnd then
          break
      else
        -- attribute-only or blank lines before the declaration
        continue
    else
      let result := processStatementLine line
      statementLines := statementLines.push result.line
      if result.isEnd then
        break
  let docstring := if docstringLines.isEmpty then none
    else some (String.intercalate "\n" docstringLines.toList)
  let statement := if statementLines.isEmpty then none
    else some (String.intercalate "\n" statementLines.toList)
  return { docstring, statement }

/-- Get the spec theorem's docstring and statement from its source file.
The statement excludes the proof (truncated at `:= by`). -/
def getSpecParts (env : Environment) (name : Name) : IO SpecParts := do
  let specName := getSpecName name
  if env.find? specName |>.isNone then return {}
  let rangesOpt : Option DeclarationRanges := (findDeclarationRangesCore? specName : EnvM _).run env
  let some ranges := rangesOpt | return {}
  let some filePath := getSpecFilePath env name | return {}
  let filePath : System.FilePath := filePath
  if !(← filePath.pathExists) then return {}
  let contents ← IO.FS.readFile filePath
  let lines := contents.splitOn "\n"
  let range := ranges.range
  let startLine := range.pos.line
  let endLine := range.endPos.line
  if startLine == 0 || endLine == 0 then return {}
  -- The declaration range starts at the docstring when one is attached.
  let relevantLines := lines.toArray.extract (startLine - 1) endLine
  return parseSpecSource relevantLines

end Utils.Lib.Analysis
