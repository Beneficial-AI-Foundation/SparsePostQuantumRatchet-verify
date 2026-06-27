/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Liao Zhang
-/
import SrcTranslated.Funs
import SrcTranslated.FunsExternal

/-! # Spec theorem for `incremental_mlkem768::generate`

`generate` is ML-KEM-768 key generation packaged for the SPQR ratchet: it samples a fresh
64-byte seed from a cryptographically secure RNG, derives a compressed ML-KEM-768 key pair via
libcrux, and returns the three serialized buffers `(hdr, ek, dk)` that the protocol transmits
and stores.

The extracted body in `SrcTranslated/Funs.lean` proceeds in four steps:
* allocate a 64-byte zero buffer and overwrite it via `RngCore::fill_bytes` — the fresh seed;
* `KeyPairCompressedBytes::from_seed seed` — libcrux's ML-KEM-768 keygen, returning one
  compressed key pair `k`;
* read the three projections `k.pk1 ()`, `k.pk2 ()`, `k.sk ()` — the 64-byte header, the
  1152-byte encapsulation key (the serialized `t̂` vector), and the 2400-byte decapsulation key;
* copy each into an owned `Vec` (`to_slice` then `to_vec`) and assemble `Keys { hdr, ek, dk }`.

Cryptographically the three buffers are *not* independent: ML-KEM's decapsulation key embeds the
public key.  In the serialized layout `dk` is the whole key pair, `ek` is the sub-range
`dk[enc .. 2·enc]`, and `hdr` is the sub-range `dk[2·enc .. 2·enc + 64]`, where
`enc = encapsulationKeyBytes = 1152`.  These containments — not just the lengths — are exactly
what the spec theorem proves.

`KeyPairCompressedBytes::{from_seed, pk1, pk2, sk}` are externals modelled in
`SrcTranslated/FunsExternal.lean` over a concrete `KeyPairCompressedBytes` that faithfully
mirrors the Rust struct: a *single* serialized buffer `value` of length
`mlkem768Params.decapsulationKeyBytes = 2400`.  Over it `sk` returns the whole buffer, `pk2` the
slice `value[enc .. 2·enc]`, and `pk1` the slice `value[2·enc .. 2·enc + 64]`, where
`enc = mlkem768Params.encapsulationKeyBytes = 1152`.  The three contractual sizes are therefore
not bare literals but the buffer lengths *derived* from the ML-KEM-768 parameter set in
`SrcTranslated/TypesExternal.lean` (`headerBytes = 64`, `encapsulationKeyBytes = 1152`,
`decapsulationKeyBytes = 2400`).  `pk1`/`pk2`/`sk` carry proved `@[step]` specs recording both
their length and their slice provenance; `from_seed` carries an `@[step]` spec fixing only the
length of its buffer (its key derivation is not modelled).

**Source**: `src/incremental_mlkem768.rs`, lines 34:0-43:1 -/

open Aeneas Aeneas.Std Result

namespace spqr.incremental_mlkem768

open libcrux_ml_kem.mlkem768.incremental
open Spqr.Mlkem

/-- **Spec theorem for `incremental_mlkem768.generate`**:

Assuming the RNG's `fill_bytes` does not panic, `generate` returns a `Keys` that is the
*serialization of a single compressed ML-KEM key pair* — not merely three independent buffers
of the right size.  Concretely, there is one key pair `kp` (the one libcrux derives from the
freshly sampled 64-byte randomness) whose single serialized buffer `kp.value` is the source of
all three outputs, byte-for-byte:

  * `dk`  is the *whole* decapsulation-key buffer `kp.value`;
  * `ek`  is the encapsulation-key (`t̂`) sub-range `kp.value[enc .. 2·enc]`;
  * `hdr` is the header sub-range `kp.value[2·enc .. 2·enc + 64]`,

with `enc = encapsulationKeyBytes = 1152`.  Because the model stores one shared buffer rather
than three independent fields, the fact that `hdr`/`ek` are *sub-ranges of* `dk` is exact (a
`List.slice` equality), mirroring the Rust accessors that slice the same `value`.  The
contractual sizes (`64`, `1152`, `2400`) then follow because `kp.value` is a fixed-size array.
The *cryptographic* content of `kp.value` is left for furture work.

TODO:
- Functional correctness (round-trip). For (ek, dk) from generate, any shared secret encapsulated to
  ek is recovered by decapsulating with dk:
  decaps(dk, encaps(ek)) = ss, up to ML-KEM's negligible (~2⁻¹³⁸) failure probability. This is the minimal
  crypto-functional property, and it's the one the current model cannot state because from_seed/encaps/decaps are
  opaque size-only externals.

  2. Distributional faithfulness. (ek, dk) is identically distributed to ML-KEM-768 KeyGen on a uniform seed. This
  is the bridge to all security: IND-CCA2 only transfers to these keys if their distribution is correct.

  3. Security (inherited, game-based). Given (2): the KEM built on (ek, dk) is IND-CCA2; ek/hdr are pseudorandom
  (safe to transmit — MLWE hides t̂); and the secret portion of dk (i.e. dk \ (ek‖hdr) — dk_pke, z) is one-way /
  computationally hidden given the transmitted (hdr, ek). The subtlety from the layout above: secrecy is not that
  ek/hdr bytes are disjoint from dk — they aren't — it's that the complement slices stay hidden.

-/
theorem generate_spec {R : Type} (rngInst : rand.rng.Rng R)
    (cryptoInst : rand_core.CryptoRng R) (rng : R)
    (h_fill : ∀ (r : R) (s : Slice Std.U8),
      rngInst.rand_coreRngCoreInst.fill_bytes r s ⦃ fun _ => True ⦄) :
    generate rngInst cryptoInst rng ⦃ (result : Keys × R) =>
        result.1.ek.val  = result.1.dk.val.slice mlkem768Params.encapsulationKeyBytes
        (2 * mlkem768Params.encapsulationKeyBytes) ∧
        result.1.hdr.val = result.1.dk.val.slice (2 * mlkem768Params.encapsulationKeyBytes)
        (2 * mlkem768Params.encapsulationKeyBytes + headerBytes) ∧
        result.1.hdr.length = 64 ∧
        result.1.ek.length = 1152 ∧
        result.1.dk.length = 2400 ⦄ := by
  unfold generate
  step*
  refine ⟨?_, ?_, ?_⟩ <;>
  simp only [← v_post, ← v1_post, ← v2_post, s2_post, s3_post, s4_post,
    a_post2, a1_post2, a2_post2, Array.val_to_slice, Array.length_to_slice] ; grind

end spqr.incremental_mlkem768
