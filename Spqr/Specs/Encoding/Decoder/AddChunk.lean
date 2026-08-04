/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Funs
import Spqr.Specs.Encoding.Polynomial.PolyDecoder.AddChunk

/-!
# Spec theorems for `spqr::encoding::{Decoder for Option<T>}::add_chunk`

Whenever `T : Decoder`, the `Decoder` trait also applies to `Option<T>`. In Rust the method
`add_chunk` on `Option<T>` operates on a `&mut Option<T>` and is only legitimate when the option is
`Some` (the `#[hax_lib::requires(self.is_some())]` annotation); under that precondition it
transparently delegates to `T::add_chunk` on the inner value and leaves the option in the `Some`
state, having folded the fresh `chunk` into the inner decoder.

To enable formal verification with hax — which disallows mutable references that escape a function
body via APIs such as `Option::take` — the extracted Lean version reifies the borrow as a pair of
ordinary functional steps:

  1. `core.option.Option.take self` — pure decomposition `self ↦ (self, none)`, returning the
     "extracted" inner option together with a `none` placeholder.
  2. `core.option.Option.unwrap o` — partial projection out of `Option T`, succeeding iff
     `o.isSome` (i.e. `self.isSome`).
  3. `DecoderInst.add_chunk tmp chunk` — delegation to the underlying `Decoder T` instance on the
     unwrapped state, absorbing `chunk`.
  4. `ok (some tmp1)` — re-injection of the updated inner state back into the `Some` branch.

The composition is a *pure structural lift*: the outer `add_chunk` carries no extra mathematical
content beyond that of `DecoderInst.add_chunk`; the `Option` layer merely repackages inputs and
outputs. This mirrors, on the decoding side, the `Option<T>` lifting already established for the
encoder's `next_chunk`, and for the decoder's own `new`.

This file proves two theorems built on that observation:

  • `add_chunk_spec_lift` — transports an arbitrary postcondition of the inner decoder's
    `add_chunk` through the `Option<T>` wrapper, under the `self.isSome` precondition.
  • `add_chunk_spec_poly_decoder` — the `T = PolyDecoder` instance, obtained from the lift plus the
    point-insertion postcondition of
    `PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk_spec`.

**Source**: spqr/src/encoding.rs (lines 84:4-91:5)
-/

open Aeneas Aeneas.Std Result spqr encoding.polynomial

namespace spqr.core.option.Option.Insts.SpqrEncodingDecoder

/-- **Predicate-lifting spec for `Option<T>::add_chunk`**:

Given a `Decoder T` instance `DecoderInst`, an option `self` with `self.isSome`, a `chunk`, and a
predicate `P` on the inner result, the hypothesis `h_inner` states that whenever `self = some tmp`
the inner call `DecoderInst.add_chunk tmp chunk` satisfies `P`. The theorem concludes that
`add_chunk DecoderInst self chunk` satisfies the postcondition obtained by pushing `P` through the
`Some` constructor:

  `result ↦ ∃ tmp', result = some tmp' ∧ P tmp'`.

The proof composes the four functional steps of the extraction:

  1. `core.option.Option.take` — pure decomposition `(o, _) := (self, none)`.
  2. `core.option.Option.unwrap.spec` — succeeds because `self.isSome`, producing `tmp` with
     `self = some tmp`.
  3. `DecoderInst.add_chunk tmp chunk` — the opaque inner call, discharged by `h_inner`.
  4. `ok (some tmp1)` — repackaging into the `Some` branch.

Since the `Option` layer only re-injects along `Some`, whatever `P` holds for the inner decoder
holds — retagged with `Some` — for the wrapped one. This is the reusable building block behind
`add_chunk_spec_poly_decoder`.

**Source**: spqr/src/encoding.rs (lines 84:4-91:5)
-/
@[step]
theorem add_chunk_spec_lift
    {T : Type} (DecoderInst : encoding.Decoder T) (self : Option T)
    (chunk : encoding.Chunk)
    (h_some : self.isSome)
    (P : T → Prop)
    (h_inner : ∀ tmp, self = some tmp →
        DecoderInst.add_chunk tmp chunk ⦃ (r : T) => P r ⦄) :
    add_chunk DecoderInst self chunk ⦃ (result : Option T) =>
      ∃ tmp', result = some tmp' ∧ P tmp' ⦄ := by
  unfold add_chunk
  simp only [Aeneas.Std.core.option.Option.take]
  step with Aeneas.Std.core.option.Option.unwrap.spec as ⟨tmp, h_eq⟩
  have h_post := h_inner tmp h_eq
  step with h_post
  grind

/-- **`add_chunk` spec for `Option<PolyDecoder>`**:

`add_chunk PolyDecoder.Insts.SpqrEncodingDecoder (some pd0) chunk` inherits, through the `Option<T>`
wrapper, the point-insertion behaviour of the underlying `PolyDecoder`: the call succeeds in the
`Ok (some pd)` shape — the option stays `Some` — and the inner state `pd` satisfies exactly the
postcondition of `PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk`:

  • `pts_needed` and `is_complete` are preserved.
  • There is a chain `selfs 0 = pd0, …, selfs 16 = pd` of intermediate decoders, where each of the
    16 two-byte pairs of `chunk` is routed to polynomial `poly = (chunk.index * 16 + j) % 16` at
    x-coordinate `poly_idx = chunk.index`, building a point `p` (y being the big-endian pair
    `256 * b_hi + b_lo`) that is conditionally inserted into `pts[poly]` following the sorted
    set's append / replace / `sortedInsert` cases.

The postcondition is **conditional**: when `poly_idx < np ∨ pts[poly].len() < np` (where
`np = necessary_points(poly)`), the point is inserted; otherwise the state is unchanged.

The hypotheses `h_overflow` (no `usize` overflow of the base index) and `h_push_cap` (each bucket
has room for the 16 potential pushes plus the length prefix) are forwarded verbatim to the inner
spec.

Proved by feeding `PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk_spec` (the inner `PolyDecoder`
postcondition) into `add_chunk_spec_lift`, whose `Some`-lifted conclusion matches the target shape.

**Source**: spqr/src/encoding.rs (lines 84:4-91:5)
-/
@[step]
theorem add_chunk_spec_poly_decoder
    (pd0 : PolyDecoder) (chunk : encoding.Chunk)
    (h_overflow : chunk.index * 16 + 16 ≤ Usize.max)
    (h_push_cap : ∀ (k : Nat), k < 16 → (pd0.pts[k]!).length + 17 ≤ Usize.max) :
    add_chunk PolyDecoder.Insts.SpqrEncodingDecoder (some pd0) chunk ⦃
        (result : Option PolyDecoder) =>
      ∃ pd, result = some pd ∧
        pd.pts_needed = pd0.pts_needed ∧
        pd.is_complete = pd0.is_complete ∧
        ∃ (selfs : Nat → PolyDecoder),
          selfs 0 = pd0 ∧
          selfs 16 = pd ∧
          ∀ (j : Nat), j < 16 →
            let total_idx := chunk.index.val * 16 + j
            let poly := total_idx % 16
            let poly_idx := total_idx / 16
            let np := pd0.pts_needed.val / 16 +
              (if poly < pd0.pts_needed.val % 16 then 1 else 0)
            (selfs (j + 1)).pts_needed = pd0.pts_needed ∧
            (selfs (j + 1)).is_complete = pd0.is_complete ∧
            poly < 16 ∧
            poly_idx = chunk.index.val ∧
            ∃ (p : Pt),
              p.x.value.val = poly_idx ∧
              p.y.value.val = (chunk.data[j * 2]!) * 256 + (chunk.data[j * 2 + 1]!) ∧
              (if poly_idx < np ∨ ((selfs j).pts.val[poly]!).val.length < np
               then
                 (∀ (k : Nat), k ≠ poly → (selfs (j + 1)).pts[k]! = (selfs j).pts.val[k]!) ∧
                 match ((selfs j).pts.val[poly]!).val.getLast? with
                 | none =>
                     ((selfs (j + 1)).pts.val[poly]!).val = ((selfs j).pts.val[poly]!).val ++ [p]
                 | some last =>
                   match Pt.Insts.CoreCmpOrd.cmp p last with
                   | ok Ordering.gt =>
                       ((selfs (j + 1)).pts.val[poly]!).val = ((selfs j).pts.val[poly]!).val ++ [p]
                   | ok Ordering.eq =>
                       ((selfs (j + 1)).pts.val[poly]!).val =
                       ((selfs j).pts.val[poly]!).val.dropLast ++ [p]
                   | ok Ordering.lt =>
                       ∃ (m : Nat),
                         m ≤ ((selfs j).pts.val[poly]!).val.length ∧
                         (((selfs (j + 1)).pts.val[poly]!).val =
                             ((selfs j).pts.val[poly]!).val.take m ++ [p] ++
                             ((selfs j).pts.val[poly]!).val.drop m ∨
                          (m < ((selfs j).pts.val[poly]!).val.length ∧
                           ((selfs (j + 1)).pts.val[poly]!).val =
                             ((selfs j).pts.val[poly]!).val.take m ++ [p] ++
                             ((selfs j).pts.val[poly]!).val.drop (m + 1)))
                   | _ => False
               else
                 selfs (j + 1) = selfs j) ⦄ := by
  apply add_chunk_spec_lift PolyDecoder.Insts.SpqrEncodingDecoder (some pd0) chunk (by simp)
  intro tmp h_eq
  simp only [Option.some.injEq] at h_eq
  rw [h_eq] at h_push_cap
  rw [h_eq]
  exact PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk_spec tmp chunk h_overflow h_push_cap

end spqr.core.option.Option.Insts.SpqrEncodingDecoder
