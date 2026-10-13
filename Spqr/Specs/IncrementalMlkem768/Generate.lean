/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Liao Zhang, Hoang Le Truong
-/
import SrcTranslated.Funs
import SrcTranslated.FunsExternal
import Spqr.Crypto.Fips203.Bridge.LibcruxKeygen

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

**Source**: `src/incremental_mlkem768.rs`, lines 34:0-43:1 -/

open Aeneas Aeneas.Std Result

namespace spqr.incremental_mlkem768

open libcrux_ml_kem.mlkem768.incremental
open Spqr.Mlkem

/-- **Spec theorem for `incremental_mlkem768.generate`**:

Assuming `fill_bytes` is panic-free, `generate` returns a `Keys` that is the serialization of a
single compressed ML-KEM key pair `kp` — not three independent buffers of the right size.  All
three outputs come, byte-for-byte, from `kp`'s one serialized buffer `kp.value`
(`enc = encapsulationKeyBytes = 1152`):
* `dk`  = the whole buffer `kp.value`                 (length `2400`);
* `ek`  = the sub-range `kp.value[enc .. 2·enc]`    (length `1152`);
* `hdr` = the header sub-range `kp.value[2·enc .. 2·enc + 64]` (length `64`).

**FIPS 203 value semantics** (Phase 7.1 of `doc/plan.md`): beyond the layout facts, there is a
64-byte seed (the one `fill_bytes` wrote) such that the three buffers are exactly the FIPS 203
(Algorithm 16) values of `ML-KEM.KeyGen_internal(seed[0:32], seed[32:64])`:
* `dk`  = `Fips203.Bridge.keyPairList seed` — the serialised decapsulation key
  `ByteEncode₁₂(ŝ) ‖ ByteEncode₁₂(t̂) ‖ ρ ‖ H(ek) ‖ z`;
* `ek`  = `Fips203.Bridge.pk2Bytes seed` — `ByteEncode₁₂(t̂)`, the serialised NTT public vector;
* `hdr` = `Fips203.Bridge.pk1Bytes seed` — `ρ ‖ H(ek)`, the matrix seed and key hash.

Remaining future work (not expressible at this layer): distributional faithfulness of the seed
(uniformity of `fill_bytes`) and game-based IND-CCA2 security. -/
theorem generate_spec {R : Type} (rngInst : rand.rng.Rng R)
    (cryptoInst : rand_core.CryptoRng R) (rng : R)
    (h_fill : ∀ (r : R) (s : Slice Std.U8),
      rngInst.rand_coreRngCoreInst.fill_bytes r s ⦃ fun _ => True ⦄) :
    generate rngInst cryptoInst rng ⦃ (result : Keys × R) =>
        (∃ seed : Fin 64 → UInt8,
          result.1.dk.val  = Fips203.Bridge.keyPairList seed ∧
          result.1.ek.val  = Fips203.Bridge.toU8List (Fips203.Bridge.pk2Bytes seed) ∧
          result.1.hdr.val = Fips203.Bridge.toU8List (Fips203.Bridge.pk1Bytes seed)) ∧
        result.1.ek.val  = result.1.dk.val.slice mlkem768Params.encapsulationKeyBytes
        (2 * mlkem768Params.encapsulationKeyBytes) ∧
        result.1.hdr.val = result.1.dk.val.slice (2 * mlkem768Params.encapsulationKeyBytes)
        (2 * mlkem768Params.encapsulationKeyBytes + headerBytes) ∧
        result.1.hdr.length = headerBytes ∧
        result.1.ek.length = mlkem768Params.encapsulationKeyBytes ∧
        result.1.dk.length = mlkem768Params.decapsulationKeyBytes ⦄ := by
  unfold generate
  step*
  have henc : mlkem768Params.encapsulationKeyBytes = 1152 := by decide
  have hhdr : headerBytes = 64 := by decide
  refine ⟨⟨Fips203.Bridge.seedOfArray (to_slice_mut_back s1), ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simp only [← v2_post, s4_post, Array.val_to_slice, a2_post2, k_post2]
  · simp only [← v1_post, s3_post, Array.val_to_slice, a1_post2, k_post2, henc,
      Nat.reduceMul]
    exact Fips203.Bridge.keyPairList_slice_pk2 _
  · simp only [← v_post, s2_post, Array.val_to_slice, a_post2, k_post2, henc, hhdr,
      Nat.reduceMul, Nat.reduceAdd]
    exact Fips203.Bridge.keyPairList_slice_pk1 _
  all_goals
    simp only [← v_post, ← v1_post, ← v2_post, s2_post, s3_post, s4_post,
      a_post2, a1_post2, a2_post2, Array.val_to_slice, Array.length_to_slice]
  all_goals grind

end spqr.incremental_mlkem768
