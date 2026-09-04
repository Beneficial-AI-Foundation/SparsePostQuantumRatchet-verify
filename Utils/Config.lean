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

/-- Location of translation.json produced by Aeneas. -/
def translationJsonPath : String := "translation.json"

/-- Default output path for the status report. -/
def statusOutPath : String := "status.json"

/-- Default output path for the rustdoc-injection report (`lake exe docsjson`).
Deliberately under `target/` (gitignored as a whole): the report is regenerated on every
docs build and must never be committed, and keeping the repo root clear avoids clashing
with any future checked-in `functions.json`. -/
def docsJsonOutPath : String := "target/docs-build/functions.json"

/-- Exact modules whose axioms are part of the trusted base: the hand-written external
models. Deliberately NOT a `SrcTranslated` prefix — the generated `SrcTranslated.Funs`
must never be a source of trusted axioms. -/
def trustedAxiomModules : List Name :=
  [`SrcTranslated.FunsExternal, `SrcTranslated.TypesExternal]

/-- Module prefixes whose axioms are part of the trusted base: the Aeneas standard
library's models of Rust built-ins (same trust tier as the translation itself).
A spec theorem counts as *proven* only when every axiom in its transitive closure is a
Lean core axiom, comes from `trustedAxiomModules`/these prefixes, or is an
origin-authenticated native decision certificate — anything else (`sorryAx`,
`Lean.trustCompiler`, stray project axioms) demotes it. -/
def trustedAxiomModulePrefixes : List Name := [`Aeneas]

end Utils.Config
