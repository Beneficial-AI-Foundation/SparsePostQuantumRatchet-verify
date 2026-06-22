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

with `HEADER_SIZE = 64` and `ENCAPSULATION_KEY_SIZE = 1152`.

The libcrux routines `KeyPairCompressedBytes::{from_seed, pk1, pk2, sk}` are externals whose
return *types* already pin the array sizes (`[u8; 64]`, `[u8; 1152]`, `[u8; 2400]`).  They are
modelled in `SrcTranslated/FunsExternal.lean` as honest `def`s over a concrete
`KeyPairCompressedBytes` struct, each with a proved `@[step]` spec stating only that the call
does not panic (the cryptographic content is not modelled).
`RngCore::fill_bytes` is a trait method on an arbitrary `R`, so its
non-panicking behaviour is taken as a hypothesis on the instance.  The output buffer lengths are
then independent of the randomness: `from_slice` reconstructs a `[u8; 64]` regardless, so the
sizes follow from the `pk1`/`pk2`/`sk` return types through `to_slice`/`to_vec`.

**Source**: spqr/src/incremental_mlkem768.rs (lines 34:0-43:1) -/

open Aeneas Aeneas.Std Result

namespace spqr.incremental_mlkem768

open libcrux_ml_kem.mlkem768.incremental

/-- **Spec theorem for `incremental_mlkem768.generate`**:

- Assuming the RNG's `fill_bytes` does not panic
- `generate` returns a `Keys` whose three buffers have the sizes mandated by the Rust contract
  * `hdr` is 64 bytes
  * `ek` is 1152 bytes
  * and `dk` is 2400 bytes. -/
theorem generate_spec {R : Type} (rngInst : rand.rng.Rng R)
    (cryptoInst : rand_core.CryptoRng R) (rng : R)
    (h_fill : ∀ (r : R) (s : Slice Std.U8),
      rngInst.rand_coreRngCoreInst.fill_bytes r s ⦃ fun _ => True ⦄) :
    generate rngInst cryptoInst rng ⦃ (result : Keys × R) =>
      result.1.hdr.length = 64 ∧
      result.1.ek.length = 1152 ∧
      result.1.dk.length = 2400 ⦄ := by
  unfold generate
  step*

end spqr.incremental_mlkem768
