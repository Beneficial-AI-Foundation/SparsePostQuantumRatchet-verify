/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Spqr.Code.Funs
import Spqr.Math.Gf16.Field
import Mathlib.RingTheory.Polynomial.Basic

open Polynomial

abbrev GF216Poly := GF216[X]

namespace spqr.encoding.polynomial

instance : Inhabited spqr.encoding.polynomial.Pt where default := ⟨⟨0#u16⟩, ⟨0#u16⟩⟩

noncomputable def listToGF216Poly (cs : List spqr.encoding.gf.GF16) : GF216Poly :=
  ∑ i : Fin cs.length, C ((cs.get i).toGF216) * X ^ i.val

noncomputable def Poly.toGF216Poly (p : Poly) : GF216Poly :=
  listToGF216Poly p.coefficients.val

end spqr.encoding.polynomial
