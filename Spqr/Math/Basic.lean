/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.GaloisField

/-! # Common Definitions

Common definitions used across spec theorems: field constants, conversion functions,
field element bridge (FieldElement51), and field utility functions (sqrt, is_negative).
-/

open Aeneas.Std Result

/-! ## Constants -/

abbrev GF216 := GaloisField 2 16
