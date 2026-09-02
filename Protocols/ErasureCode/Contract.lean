/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Alessandro D'Angelo
-/
import Protocols.ErasureCode.Correctness.Maps
import SrcTranslated.FunsExternal
import Spqr.Specs.Encoding.Polynomial.PolyDecoder.NewWithPolyCount

/-! # Contract for the opaque polynomial decoder -/

open Aeneas Aeneas.Std Result Polynomial
open spqr encoding.polynomial
open spqr.encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder

namespace Protocols.ErasureCode

/-- Points the decoder needs in store `j`. -/
def neededPoints (pd : PolyDecoder) (j : Nat) : Nat :=
  pd.pts_needed.val / 16 + if j < pd.pts_needed.val % 16 then 1 else 0

/-- Strictly sorted by x, hence sorted and duplicate-free. -/
def SortedStore (l : List Pt) : Prop :=
  l.Pairwise (fun p q => p.x.value.val < q.x.value.val)

/-- Every stored point lies on `P`. -/
def StoreOn (l : List Pt) (P : Polynomial GF216) : Prop :=
  ∀ p ∈ l, P.eval p.x.toGF216 = p.y.toGF216

/-- Assumption about the shipped Rust `decoded_message` implementation: a short point store
forces decoding to return `none`. The function is opaque to extraction and this assumption can
become a theorem if that Rust function is refactored for extraction. -/
@[step]
axiom decoded_message_spec_short
    (pd : PolyDecoder)
    (h_short : ∃ j, j < 16 ∧ ((pd.pts[j]!).val).length < neededPoints pd j) :
    spqr.encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.decoded_message pd
      ⦃ (r : Option (alloc.vec.Vec U8)) => r = none ⦄

/-- Assumption about the shipped Rust `decoded_message` implementation: complete sorted point
stores on low-degree polynomials serialize their evaluations. The function is opaque to
extraction and this assumption can become a theorem if that Rust function is refactored for
extraction. -/
@[step]
axiom decoded_message_spec_complete
    (pd : PolyDecoder) (P : Nat → Polynomial GF216)
    (h_flag : pd.is_complete = false)
    (h_sorted : ∀ j, j < 16 → SortedStore (pd.pts[j]!).val)
    (h_on : ∀ j, j < 16 → StoreOn (pd.pts[j]!).val (P j))
    (h_deg : ∀ j, j < 16 → (P j).degree < (neededPoints pd j : WithBot ℕ))
    (h_len : ∀ j, j < 16 → neededPoints pd j ≤ ((pd.pts[j]!).val).length) :
    spqr.encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.decoded_message pd
      ⦃ (r : Option (alloc.vec.Vec U8)) =>
      ∃ out, r = some out ∧ out.length = 2 * pd.pts_needed.val ∧
        ∀ i, i < pd.pts_needed.val →
          Nat.toGF216 (256 * (out.val[2 * i]!).val + (out.val[2 * i + 1]!).val)
            = (P (i % 16)).eval ((i / 16 : ℕ).toGF216) ⦄

end Protocols.ErasureCode
