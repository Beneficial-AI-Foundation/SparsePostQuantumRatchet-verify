import Lean
import Utils.Config
/-! Join: parse `translation.json` (Aeneas) and `spqr.llbc` (charon) and join them on the shared
`def_id` to link each extracted Lean function to its Rust source. -/

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

/-! ## spqr.llbc -/

/-- Rust-side metadata for one `def_id`, read from the LLBC `fun_decls`. -/
structure FunMeta where
  rustName : String
  source : String
  lineStart : Nat
  lineEnd : Nat
  isPublic : Bool
  deriving Repr, Inhabited

/-- A LLBC name is a list of path components; keep the `Ident` ones, joined by `::`. -/
private def nameComponent (j : Json) : Option String :=
  match (j.getObjVal? "Ident").toOption with
  | some ident => ((ident.getArr?).toOption.bind (·[0]?)).bind (Json.getStr? · |>.toOption)
  | none => none

private def rustNameOf (nameArr : Array Json) : String :=
  String.intercalate "::" (nameArr.filterMap nameComponent).toList

/-- file_id → source path, from `translated.files`. -/
private def fileMap (translated : Json) : Std.HashMap Nat String := Id.run do
  let mut m : Std.HashMap Nat String := {}
  for f in jArr translated "files" do
    let id := jNat f "id"
    let nameObj := (jVal? f "name").getD Json.null
    -- name is { "Local": path } or { "Virtual": path }
    let path :=
      match (nameObj.getObjVal? "Local").bind Json.getStr? |>.toOption with
      | some p => p
      | none => ((nameObj.getObjVal? "Virtual").bind Json.getStr?).toOption.getD ""
    m := m.insert id path
  return m

/-- Build `def_id → FunMeta` from the LLBC `fun_decls`. -/
def parseLlbc (root : Json) : Std.HashMap Nat FunMeta := Id.run do
  let translated := (jVal? root "translated").getD Json.null
  let files := fileMap translated
  let mut m : Std.HashMap Nat FunMeta := {}
  for fd in jArr translated "fun_decls" do
    -- `fun_decls` is a sparse, index-keyed vector: skip the `null` holes
    -- (filtered/untranslated FunDeclIds) so they don't collapse onto def_id 0.
    if (fd.getObjVal? "def_id").toOption |>.isNone then continue
    let defId := jNat fd "def_id"
    let im := (jVal? fd "item_meta").getD Json.null
    let rustName := rustNameOf (jArr im "name")
    let span := (jVal? im "span").getD Json.null
    let data := (jVal? span "data").getD Json.null
    let lineStart := jNat ((jVal? data "beg").getD Json.null) "line"
    let lineEnd := jNat ((jVal? data "end").getD Json.null) "line"
    let fileId := jNat data "file_id"
    let isPublic := jBool ((jVal? im "attr_info").getD Json.null) "public"
    m := m.insert defId
      { rustName, source := files.getD fileId "", lineStart, lineEnd, isPublic }
  return m

/-! ## Combined read -/

/-- Read and parse both artifacts. Returns the Aeneas function entries and the
    `def_id → Rust metadata` map. -/
def readArtifacts : IO (Array TransFun × Std.HashMap Nat FunMeta) := do
  let transStr ← IO.FS.readFile Utils.Config.translationJsonPath
  let llbcStr ← IO.FS.readFile Utils.Config.llbcPath
  let transJson ← IO.ofExcept (Json.parse transStr)
  let llbcJson ← IO.ofExcept (Json.parse llbcStr)
  return (parseTranslation transJson, parseLlbc llbcJson)

end Utils.Lib.Join
