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

The libcrux routines `KeyPairCompressedBytes::{from_seed, pk1, pk2, sk}` are opaque externals
whose return *types* already pin the array sizes (`[u8; 64]`, `[u8; 1152]`, `[u8; 2400]`); we
only postulate that they do not panic (return `ok`), mirroring the admitted libcrux interface
used by the hax extraction.  `RngCore::fill_bytes` is a trait method on an arbitrary `R`, so its
non-panicking behaviour is taken as a hypothesis on the instance.  The output buffer lengths are
then independent of the randomness: `from_slice` reconstructs a `[u8; 64]` regardless, so the
sizes follow from the `pk1`/`pk2`/`sk` return types through `to_slice`/`to_vec`.

**Source**: spqr/src/incremental_mlkem768.rs (lines 34:0-43:1) -/

open Aeneas Aeneas.Std Result

namespace spqr.incremental_mlkem768

open libcrux_ml_kem.mlkem768.incremental

/-- Trusted interface spec: `KeyPairCompressedBytes::from_seed` does not panic.  The result type
`KeyPairCompressedBytes` carries no size obligation, so the postcondition is trivial. -/
@[step]
axiom from_seed_spec (x : Array Std.U8 64#usize) :
    KeyPairCompressedBytes.from_seed x ⦃ fun _ => True ⦄

/-- Trusted interface spec: `KeyPairCompressedBytes::pk1` does not panic.  Its return type
`[u8; 64]` pins the header size. -/
@[step]
axiom pk1_spec (k : KeyPairCompressedBytes) :
    KeyPairCompressedBytes.pk1 k ⦃ fun (_ : Array Std.U8 64#usize) => True ⦄

/-- Trusted interface spec: `KeyPairCompressedBytes::pk2` does not panic.  Its return type
`[u8; 1152]` pins the encapsulation-key size. -/
@[step]
axiom pk2_spec (k : KeyPairCompressedBytes) :
    KeyPairCompressedBytes.pk2 k ⦃ fun (_ : Array Std.U8 1152#usize) => True ⦄

/-- Trusted interface spec: `KeyPairCompressedBytes::sk` does not panic.  Its return type
`[u8; 2400]` pins the decapsulation-key size. -/
@[step]
axiom sk_spec (k : KeyPairCompressedBytes) :
    KeyPairCompressedBytes.sk k ⦃ fun (_ : Array Std.U8 2400#usize) => True ⦄

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
