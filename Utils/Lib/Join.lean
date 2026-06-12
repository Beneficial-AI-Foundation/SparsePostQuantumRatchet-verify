import Lean
import Utils.Config
/-! Join: parse `translation.json` (Aeneas) and `llbc-summary.json` (charon) and join them on the
shared `def_id` to link each extracted Lean function to its Rust source. -/

open Lean

namespace Utils.Lib.Join

/-! ## Small `Lean.Json` accessors (lenient: defaults instead of errors) -/

def jVal? (j : Json) (k : String) : Option Json := (j.getObjVal? k).toOption
def jStr (j : Json) (k : String) : String := ((j.getObjVal? k).bind Json.getStr?).toOption.getD ""
def jNat (j : Json) (k : String) : Nat := ((j.getObjVal? k).bind Json.getNat?).toOption.getD 0
def jBool (j : Json) (k : String) : Bool := ((j.getObjVal? k).bind Json.getBool?).toOption.getD false
def jArr (j : Json) (k : String) : Array Json := ((j.getObjVal? k).bind Json.getArr?).toOption.getD #[]

/-! ## translation.json -/

/-- One Aeneas-emitted function entry from `translation.json`. -/
structure TransFun where
  defId : Nat
  leanId : String
  leanFile : String
  isOpaque : Bool
  canFail : Bool
  /-- `true` for loop wrapper/body entries (Aeneas extraction artifacts). -/
  isLoopArtifact : Bool
  deriving Repr, Inhabited

def parseTransFun (j : Json) : TransFun :=
  { defId := jNat j "def_id"
    leanId := jStr j "lean_id"
    leanFile := jStr j "lean_file"
    isOpaque := jBool j "is_opaque"
    canFail := jBool j "can_fail"
    -- The emitter writes `"loop": null` for non-loop entries (it does not omit
    -- the field), so a present-but-null `loop` is NOT a loop artifact.
    isLoopArtifact := match jVal? j "loop" with
      | some Json.null => false
      | some _ => true
      | none => false }

/-- Parse the `functions` array of `translation.json`. -/
def parseTranslation (j : Json) : Array TransFun :=
  (jArr j "functions").map parseTransFun

/-! ## llbc-summary.json -/

/-- Rust-side metadata for one `def_id`, read from `llbc-summary.json`. -/
structure FunMeta where
  rustName : String
  source : String
  lineStart : Nat
  lineEnd : Nat
  isPublic : Bool
  /-- Defined in the crate (vs a dependency / std). -/
  isLocal : Bool
  /-- charon-level opacity: `Transparent` / `Opaque` / `Foreign`. -/
  opacity : String
  /-- A global's synthetic initializer function. -/
  isGlobalInit : Bool
  isUnsafe : Bool
  deriving Repr, Inhabited

/-- Build `def_id → FunMeta` from the `functions` array of `llbc-summary.json`. -/
def parseSummary (root : Json) : Std.HashMap Nat FunMeta := Id.run do
  let mut m : Std.HashMap Nat FunMeta := {}
  for fd in jArr root "functions" do
    m := m.insert (jNat fd "def_id")
      { rustName := jStr fd "rust_name"
        source := jStr fd "source"
        lineStart := jNat fd "line_start"
        lineEnd := jNat fd "line_end"
        isPublic := jBool fd "is_public"
        isLocal := jBool fd "is_local"
        opacity := jStr fd "opacity"
        isGlobalInit := jBool fd "is_global_initializer"
        isUnsafe := jBool fd "is_unsafe" }
  return m

/-! ## Combined read -/

/-- Read and parse both artifacts. -/
def readArtifacts : IO (Array TransFun × Std.HashMap Nat FunMeta) := do
  let transStr ← IO.FS.readFile Utils.Config.translationJsonPath
  let summaryStr ← IO.FS.readFile Utils.Config.llbcSummaryPath
  let transJson ← IO.ofExcept (Json.parse transStr)
  let summaryJson ← IO.ofExcept (Json.parse summaryStr)
  return (parseTranslation transJson, parseSummary summaryJson)

end Utils.Lib.Join
