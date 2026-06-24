/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Liao Zhang
-/
import SrcTranslated.Funs
import SrcTranslated.FunsExternal

/-! # Spec theorem for `incremental_mlkem768::generate`

`generate` draws fresh randomness, derives a compressed ML-KEM key pair via libcrux, and
returns the three serialized buffers `(hdr, ek, dk)`.  The Rust contract is purely about the
sizes of those buffers:

```
#[hax_lib::ensures(|result|
  result.hdr.len() == HEADER_SIZE && result.ek.len() == ENCAPSULATION_KEY_SIZE
  && result.dk.len() == 2400)]
```

with `HEADER_SIZE = 64` and `ENCAPSULATION_KEY_SIZE = 1152`.  These three sizes are not bare
literals in the model: they are the buffer lengths *derived* from the ML-KEM-768 parameter set
in `SrcTranslated/TypesExternal.lean` (`headerBytes = 64`,
`mlkem768Params.encapsulationKeyBytes = 1152`, `mlkem768Params.decapsulationKeyBytes = 2400`).

The libcrux routines `KeyPairCompressedBytes::{from_seed, pk1, pk2, sk}` are externals whose
return *types* already pin the array sizes (`[u8; 64]`, `[u8; 1152]`, `[u8; 2400]`).  They are
modelled in `SrcTranslated/FunsExternal.lean` as honest `def`s over a concrete
`KeyPairCompressedBytes` struct — whose field lengths are exactly those derived sizes — each
with a proved `@[step]` spec stating only that the call does not panic (the cryptographic
content is not modelled).
`RngCore::fill_bytes` is a trait method on an arbitrary `R`, so its
non-panicking behaviour is taken as a hypothesis on the instance.  The output buffer lengths are
then independent of the randomness: `from_slice` reconstructs a `[u8; 64]` regardless, so the
sizes follow from the `pk1`/`pk2`/`sk` return types through `to_slice`/`to_vec`.

**Source**: spqr/src/incremental_mlkem768.rs (lines 34:0-43:1) -/

open Aeneas Aeneas.Std Result

namespace spqr.incremental_mlkem768

open libcrux_ml_kem.mlkem768.incremental
open Spqr.Mlkem
/-- **Spec theorem for `incremental_mlkem768.generate`**:

Assuming the RNG's `fill_bytes` does not panic, `generate` returns a `Keys` that is the
*serialization of a single compressed ML-KEM key pair* — not merely three independent buffers
of the right size.  Concretely, there is one key pair `kp` (the one libcrux derives from the
freshly sampled 64-byte randomness) such that the three returned buffers are exactly its
`pk1`/`pk2`/`sk` projections, byte-for-byte:

  * `hdr` is the header `kp.pk1Bytes`,
  * `ek`  is the encapsulation key `kp.pk2Bytes`,
  * `dk`  is the decapsulation key `kp.skBytes`.

This `(hdr, ek, dk)` ↦ `(pk1, pk2, sk)` correspondence is the relationship that ties the three
outputs together; the contractual sizes (`64`, `1152`, `2400`) then follow because `kp`'s fields
are fixed-size arrays.  The *cryptographic* content of `kp` is opaque in this model (libcrux's
`from_seed` is an external whose key-derivation is not modelled), so this is the strongest
relationship the model supports — it pins the structure and provenance of the output, not the
algebraic key-generation itself. -/
theorem generate_spec {R : Type} (rngInst : rand.rng.Rng R)
    (cryptoInst : rand_core.CryptoRng R) (rng : R)
    (h_fill : ∀ (r : R) (s : Slice Std.U8),
      rngInst.rand_coreRngCoreInst.fill_bytes r s ⦃ fun _ => True ⦄) :
    generate rngInst cryptoInst rng ⦃ (result : Keys × R) =>
      ∃ kp : libcrux_ml_kem.mlkem768.incremental.KeyPairCompressedBytes,
        -- the three output buffers are the `pk1`/`pk2`/`sk` projections of *one and the
        -- same* compressed key pair `kp`, byte-for-byte (not merely buffers of the right size)
        result.1.hdr.val = kp.pk1Bytes.val ∧
        result.1.ek.val  = kp.pk2Bytes.val ∧
        result.1.dk.val  = kp.skBytes.val ∧
        -- the sizes mandated by the Rust contract follow, since `kp`'s fields are fixed-size
        result.1.hdr.length = 64 ∧
        result.1.ek.length = 1152 ∧
        result.1.dk.length = 2400 ⦄ := by
  unfold generate
  step*
  -- All three buffers are the `pk1`/`pk2`/`sk` projections of the *same* key pair `k`
  -- (the one derived from the freshly sampled randomness); `to_slice`/`to_vec` only copy
  -- the underlying bytes, so both the contents and the sizes are preserved.
  refine ⟨k, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [← v_post, ← v1_post, ← v2_post, s2_post, s3_post, s4_post,
      a_post, a1_post, a2_post, Array.val_to_slice, Array.length_to_slice] <;>
    rfl

end spqr.incremental_mlkem768
