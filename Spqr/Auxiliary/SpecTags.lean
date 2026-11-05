/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Lacramioara Astefanoaei
-/
module

public import Mathlib.Tactic.Linter.Style
public import Lean

/-! # Tags for specs that are not about a single Rust function

Function specs are found through `@[step]`. A spec that ranges over runs of the state machine,
or over both parties, has no function application for `@[step]` to index, so it carries these
tags instead:

* `@[correctness_spec]`: the theorem proves a correctness property of SPQR. The name and meaning
  match the tag `probe-lean` registers in `ProbeLean.Attrs`, which it reads from the attribute
  header; it is registered here so that SPQR does not depend on `probe-lean`. Importing
  `ProbeLean.Attrs` as well would register the name twice.
* `@[braid_spec "§x.y"]`: the section of the ML-KEM Braid spec (Rev. 1) the property comes from.
  The argument must not contain `,` or `]`.
* `@[braid_deviation D₁ … Dₙ]`: the places where the code differs from ML-KEM Braid §2.5 that the
  declaration states or follows. Each argument names a constructor of `Braid.Deviation`
  (`Spqr/Specs/Braid/Deviations.lean`), and Lean checks that it does.
-/

@[expose] public section

open Lean

namespace Spqr

/-- `@[correctness_spec]` marks a theorem that proves a correctness property of SPQR. -/
initialize correctnessSpecAttr : TagAttribute ←
  registerTagAttribute `correctness_spec "Marks a declaration as a correctness property."

/-- `@[braid_spec "§x.y"]` records the section of the ML-KEM Braid spec a theorem proves. Lean
takes an attribute's name from the last component of its syntax kind, hence the underscore. -/
@[nolint defsWithUnderscore]
syntax (name := braid_spec) "braid_spec " str : attr

/-- The ML-KEM Braid spec section of each `@[braid_spec]` theorem. -/
initialize braidSpecAttr : ParametricAttribute String ←
  registerParametricAttribute {
    name := `braid_spec
    descr := "The section of the ML-KEM Braid spec a theorem proves."
    getParam := fun _ stx => do
      let some s := stx[1].isStrLit? | throwError "expected a section, e.g. \"§1.1\""
      return s }

/-- `@[braid_deviation D₁ … Dₙ]` records the deviations from ML-KEM Braid §2.5 that a declaration
states or follows. Each `Dᵢ` must name a constructor of `Braid.Deviation`. -/
@[nolint defsWithUnderscore]
syntax (name := braid_deviation) "braid_deviation" (ppSpace ident)+ : attr

/-- The deviations of each `@[braid_deviation]` declaration, as constructor names of
`Braid.Deviation`. -/
initialize braidDeviationAttr : ParametricAttribute (Array Name) ←
  registerParametricAttribute {
    name := `braid_deviation
    descr := "The deviations from ML-KEM Braid §2.5 that a declaration states or follows."
    getParam := fun _ stx => stx[1].getArgs.mapM fun id => do
      let n ← Elab.realizeGlobalConstNoOverloadWithInfo id
      let some (.ctorInfo c) := (← getEnv).find? n
        | throwErrorAt id "`{n}` is not a constructor of `Braid.Deviation`"
      unless c.induct == `Braid.Deviation do
        throwErrorAt id "`{n}` is not a constructor of `Braid.Deviation`"
      return n }

end Spqr
