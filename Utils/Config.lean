import Lean
/-! Config: project-specific settings for the verification status tracking utility. -/

open Lean

namespace Utils.Config

/-- The module to import to obtain the full environment (hand-written specs + the extracted
`SrcTranslated.*` declarations, which `Spqr` imports). -/
def mainModule : Name := `Spqr

/-- The crate name (matches the LLBC `crate_name`). -/
def crateName : String := "spqr"

/-- Suffix forming a spec theorem name: function `foo` ↦ theorem `foo_spec`. -/
def specSuffix : String := "_spec"

/-- Inputs produced by `npm run aeneas-extract` (paths relative to repo root). -/
def translationJsonPath : String := "translation.json"
def llbcPath : String := "spqr.llbc"

/-- Default output path for the status report. -/
def statusOutPath : String := "status.json"

/-- Module-name root of the Aeneas-extracted code. An `axiom` declared in a module under this root
is a *trusted external model* (an opaque Rust item), as opposed to `sorry` or builtin axiom. -/
def extractedRoot : Name := `SrcTranslated

end Utils.Config
