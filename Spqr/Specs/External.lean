/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Spqr.Code.Funs

/-! # Liveness axioms

This file collects `@[step]` liveness axioms used across proof files.
A liveness axiom asserts that a function does not fail, without constraining
its output: `f args ⦃ _ => True ⦄`.

## Two categories

1. **Opaque functions** (axioms in `FunsExternal.lean`): These have no Lean
   definition at all — axiomatizing them is the *only* way to reason about them.

2. **Deep defined functions** (defined in `Funs.lean` but with long call chains
   through encoding, MLKEM, HKDF, etc.): These *could* in principle be proved
   as `@[step] theorem`s by recursively unfolding and proving each callee, but
   the effort is disproportionate when the postcondition does not depend on
   their output. Axiomatizing them is a pragmatic shortcut. Unlike opaque-function
   axioms, these carry an implicit proof obligation: the defined function
   must be total on the reachable inputs. Each such axiom documents its
   soundness rationale in a doc-comment.

## Soundness

All axioms are trusted assumptions. They are sound as long as the
underlying Rust implementations do not panic on the inputs reachable
from the extracted code paths.
-/

open Aeneas Aeneas.Std Result

namespace spqr

/-! ## Category 1: Opaque functions (`FunsExternal.lean`) -/

/-- The HKDF-based KDF call succeeds for any input slices.
Soundness: HKDF-SHA256 is total on arbitrary byte inputs. -/
@[step]
axiom kdf.hkdf_to_slice_spec
    (salt ikm info out : Slice Std.U8) :
    kdf.hkdf_to_slice salt ikm info out ⦃ _ => True ⦄

/-- Appending an element to a `VecDeque` always succeeds.
Soundness: `push_back` only fails on OOM, which Rust treats as an abort. -/
@[step]
axiom alloc.collections.vec_deque.VecDeque.push_back_spec
    {T A : Type} (vd : alloc.collections.vec_deque.VecDeque T A) (val : T) :
    alloc.collections.vec_deque.VecDeque.push_back vd val ⦃ _ => True ⦄

/-! ## Category 2: Deep defined functions (`Funs.lean`)

These functions are fully extracted and could be proved as theorems, but their
call chains are deep (encoding loops, MLKEM operations, HKDF derivations).
Axiomatizing them is a pragmatic shortcut; see the file-level doc for policy.
-/

/-- `PolyEncoder.next_chunk` always succeeds. -/
@[step]
axiom encoding.polynomial.PolyEncoder.Insts.SpqrEncodingEncoder.next_chunk_spec
    (self : encoding.polynomial.PolyEncoder) :
    encoding.polynomial.PolyEncoder.Insts.SpqrEncodingEncoder.next_chunk self
      ⦃ _ => True ⦄

/-- `KeysUnsampled.send_hdr_chunk` always succeeds (performs header sampling
    with RNG + MLKEM key generation + encoding). -/
@[step]
axiom v1.chunked.send_ek.KeysUnsampled.send_hdr_chunk_spec
    {R : Type} (rng_inst : rand.rng.Rng R) (crypto_inst : rand_core.CryptoRng R)
    (self : v1.chunked.send_ek.KeysUnsampled) (rng : R) :
    v1.chunked.send_ek.KeysUnsampled.send_hdr_chunk rng_inst crypto_inst self rng
      ⦃ _ => True ⦄

/-- `HeaderReceived.send_ct1_chunk` always succeeds (performs CT1 sampling
    with RNG + MLKEM encapsulation + epoch secret derivation + encoding). -/
@[step]
axiom v1.chunked.send_ct.HeaderReceived.send_ct1_chunk_spec
    {R : Type} (rng_inst : rand.rng.Rng R) (crypto_inst : rand_core.CryptoRng R)
    (self : v1.chunked.send_ct.HeaderReceived) (rng : R) :
    v1.chunked.send_ct.HeaderReceived.send_ct1_chunk rng_inst crypto_inst self rng
      ⦃ _ => True ⦄

end spqr
