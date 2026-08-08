/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Encoding.Polynomial.PolyEncoder.NextChunk

/-!
# Spec theorems for `spqr::encoding::{Encoder for Option<T>}::next_chunk`

The `Option<T>` encoder's `next_chunk` unwraps `self`, delegates to `T::next_chunk`, and re-wraps
the result in `Some`. It is a pure structural lift adding no mathematical content.

This file proves:
  • `next_chunk_spec_lift` — lifts any postcondition of the inner `next_chunk` through `Option<T>`.
  • `next_chunk_spec_poly_encoder` — the `T = PolyEncoder` specialisation.

**Source**: spqr/src/encoding.rs (lines 63:4-71:5)
-/

open Aeneas Aeneas.Std Result spqr encoding.polynomial encoding.gf Polynomial

namespace spqr.core.option.Option.Insts.SpqrEncodingEncoder

/-- **Predicate-lifting spec for `Option<T>::next_chunk`**:

If `self.isSome` and the inner `EncoderInst.next_chunk` satisfies predicate `P`, then
`next_chunk EncoderInst self` satisfies `P` lifted through `Some`.

**Source**: spqr/src/encoding.rs (lines 63:4-71:5)
-/
@[step]
theorem next_chunk_spec_lift
    {T : Type} (EncoderInst : encoding.Encoder T) (self : Option T)
    (h_some : self.isSome)
    (P : encoding.Chunk → T → Prop)
    (h_inner : ∀ tmp, self = some tmp →
        EncoderInst.next_chunk tmp ⦃ ((chunk, tmp') : encoding.Chunk × T) =>
          P chunk tmp' ⦄) :
    next_chunk EncoderInst self ⦃ ((chunk, result) : encoding.Chunk × (Option T)) =>
      ∃ tmp', result = some tmp' ∧ P chunk tmp' ⦄ := by
  unfold next_chunk
  simp only [Aeneas.Std.core.option.Option.take]
  step with Aeneas.Std.core.option.Option.unwrap.spec
  rename_i tmp h_eq
  have h_post := h_inner tmp h_eq
  step with h_post
  grind

/-- **`next_chunk` spec for `Option<PolyEncoder>`**:

Lifts `PolyEncoder.Insts.SpqrEncodingEncoder.next_chunk_spec` through the `Option` wrapper via
`next_chunk_spec_lift`. The result stays `Some` and the inner postcondition (chunk index, 32-byte
data, wrapping index increment, polynomial evaluation / Lagrange interpolation) holds verbatim.

**Source**: spqr/src/encoding.rs (lines 63:4-71:5)
-/
@[step]
theorem next_chunk_spec_poly_encoder
    (pe0 : PolyEncoder)
    (h_idx_fits : pe0.idx.val ≤ U16.max)
    (h_admissible : ∀ pts, pe0.s = .Points pts →
        ∀ (j : Nat), j < 16 →
          let len := (pts[j]!).value.length
          len = 0 ∨ len = 1 ∨ len = 3 ∨ len = 5 ∨
          len = 30 ∨ len = 34 ∨ len = 36)
    (h_coeff_bound : ∀ (polys : Array encoding.polynomial.Poly 16#usize),
        pe0.s = .Polys polys →
        ∀ (j : Nat), j < 16 →
          (polys[j]!).coefficients.length + 1 ≤ Usize.max) :
    next_chunk PolyEncoder.Insts.SpqrEncodingEncoder (some pe0) ⦃
        ((chunk, result) : encoding.Chunk × (Option PolyEncoder)) =>
      match result with
      | some pe =>
        chunk.index.val = pe0.idx.val ∧
        chunk.data.val.length = 32 ∧
        pe.idx.val = (pe0.idx.val + 1) % U32.size ∧
        match pe0.s with
        | .Polys polys =>
            pe.s = pe0.s ∧
            ∀ (j : Nat), j < 16 →
              Nat.toGF216 (256 * chunk.data.val[2 * j]! + chunk.data.val[2 * j + 1]!) =
                (polys[j]!).toGF216Poly.eval (pe0.idx.val.toGF216)
        | .Points pts =>
            ∀ polys', pe.s = .Polys polys' →
              ∀ (j : Nat), j < 16 →
                polys'[j]!.toGF216Poly =
                  ∑ k ∈ Finset.range (pts[j]!).value.length,
                    C (((pts[j]!).value[k]!).toGF216) *
                      scaledLagrangeBasis (alloc.vec.Vec.len ((pts[j]!).value)) k
      | none => False ⦄ := by
  unfold next_chunk
  simp only [Aeneas.Std.core.option.Option.take]
  step with Aeneas.Std.core.option.Option.unwrap.spec
  rename_i tmp h_eq
  have h_tmp_eq : tmp = pe0 := by injection h_eq with h; exact h.symm
  simp only [h_tmp_eq]
  have h_inner := PolyEncoder.Insts.SpqrEncodingEncoder.next_chunk_spec pe0
    h_idx_fits h_admissible h_coeff_bound
  step with h_inner
  grind

end spqr.core.option.Option.Insts.SpqrEncodingEncoder
