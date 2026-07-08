/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Zhang Liao
-/
import SrcTranslated.Funs
import SrcTranslated.FunsExternal
import Spqr.Specs.LibcruxMlKem.Incremental.DecapsulateCompressedKey
import Spqr.Specs.LibcruxMlKem.Incremental.Encapsulate1
import Spqr.Specs.LibcruxMlKem.Incremental.Encapsulate2

/-! # Round-trip (KEM correctness) property for `spqr::incremental_mlkem768`

This file states and proves the round-trip property of the SPQR incremental
ML-KEM-768 wrapper layer, mirroring the Rust test
`incremental_mlkem768_round_trip` (src/incremental_mlkem768.rs, lines 178-185):

```rust
let keys = generate(&mut rng);
let (ct1, es, ss1) = encaps1(&keys.hdr, &mut rng);
let ct2 = encaps2(&keys.ek, &es);
let ss2 = decaps(&keys.dk, &ct1, &ct2);
assert_eq!(ss1, ss2);
```

That is: for a key triple `(hdr, ek, dk)` produced by `generate`, encapsulating
against the header (`encaps1`) and then against the full encapsulation key
(`encaps2`) yields ciphertexts `(ct1, ct2)` such that `decaps` recovers exactly
the shared secret produced by `encaps1`.

The four SPQR functions are thin wrappers around the *incremental* ML-KEM API of
libcrux (`KeyPairCompressedBytes::from_seed` / `encapsulate1` / `encapsulate2` /
`decapsulate_compressed_key`), which is opaque in the Lean extraction: each of
these functions is an axiom with no defining equations, and the RNG's
`fill_bytes` is an abstract trait field.

The behaviour of the opaque libcrux functions is assumed via specification
axioms.  Small panic-freedom and size facts (`from_seed_ok`, `pk1_ok`,
`pk2_ok`, `sk_ok`, `encaps_state_len_eq_2080`, `SHARED_SECRET_SIZE_eq_32`)
live in `SrcTranslated/FunsExternal.lean` next to the bare declarations, in
the style of `libcrux_hmac.hmac_sha256_tag32_length_eq_32` (#243).  The
per-function specifications of the incremental primitives have their own
spec files, like the proved specifications in this repository:

* `Spqr/Specs/LibcruxMlKem/Incremental/Encapsulate1.lean` (`encapsulate1_ok`);
* `Spqr/Specs/LibcruxMlKem/Incremental/Encapsulate2.lean` (`encapsulate2_ok`);
* `Spqr/Specs/LibcruxMlKem/Incremental/DecapsulateCompressedKey.lean`
  (`decapsulate_compressed_key_roundtrip`) — **the KEM correctness of the
  incremental libcrux API itself**: decapsulation with the matching secret key
  recovers the shared secret produced by the `encapsulate1`/`encapsulate2`
  chain.  This is the "roundtrip property for decaps" proper, stated over the
  extracted axioms and independent of any external formalisation.

The theorem keeps two explicit hypotheses that cannot (or should not) be
global axioms:

* `h_fill` — the RNG's `fill_bytes` is panic-free and preserves the buffer
  length.  `fill_bytes` is a trait field of the caller-supplied instance on an
  arbitrary type `R`, so a global axiom about it would be false for a
  trivially-failing instance — it must remain a hypothesis;
* `h_fix` — the endianness repair function
  `potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275` is the
  identity (returns `None`) on the states considered here: the repair path
  (libcrux issue #1275) only concerns states persisted with a broken encoding,
  not states freshly produced by `encapsulate1` in the same run.

What this file *proves* is the linking theorem: the SPQR wrapper layer (slicing,
`try_into` conversions, buffer allocation, the endianness-fix dispatch, and all
`Vec`/`Array`/`Slice` plumbing) faithfully forwards to the primitives, so the
wrapper-level composition inherits the primitive-level roundtrip.

**Source**: src/incremental_mlkem768.rs (test at lines 178-185)
-/

open Aeneas Aeneas.Std Result

namespace spqr.incremental_mlkem768

open libcrux_ml_kem.mlkem768.incremental
open libcrux_ml_kem.ind_cca.incremental.types (Ciphertext1 Ciphertext2)

/-- The composed round-trip program, mirroring the Rust test
`incremental_mlkem768_round_trip`: generate a key triple, encapsulate against
the header, complete encapsulation against the encapsulation key, then
decapsulate.  Returns the pair of the sender's and the receiver's shared
secrets. -/
noncomputable def round_trip {R : Type} (rngInst : rand.rng.Rng R)
    (cryptoRngInst : rand_core.CryptoRng R) (rng : R) :
    Result ((alloc.vec.Vec Std.U8) × (alloc.vec.Vec Std.U8)) := do
  let (keys, rng1) ← generate rngInst cryptoRngInst rng
  let (t, _rng2) ← encaps1 rngInst cryptoRngInst keys.hdr rng1
  let (ct1, es, ss1) := t
  let ct2 ← encaps2 keys.ek es
  let ss2 ← decaps keys.dk ct1 ct2
  ok (ss1, ss2)

/-- **Round-trip property for the SPQR incremental ML-KEM-768 wrappers**:

Under the specification axioms for the opaque libcrux incremental API (see the
module docstring; `decapsulate_compressed_key_roundtrip` is the correctness of
the underlying incremental KEM) and the two modelling hypotheses `h_fill` and
`h_fix`, the composition `generate → encaps1 → encaps2 → decaps` succeeds and
the decapsulated shared secret equals the encapsulated one. -/
theorem round_trip_spec {R : Type} (rngInst : rand.rng.Rng R)
    (cryptoRngInst : rand_core.CryptoRng R) (rng : R)
    -- The RNG's `fill_bytes` is panic-free and preserves the buffer length.
    (h_fill : ∀ (r : R) (s : Slice Std.U8), ∃ r' s',
      rngInst.rand_coreRngCoreInst.fill_bytes r s = ok (r', s') ∧
      s'.length = s.length)
    -- Freshly produced encapsulation states are correctly encoded, so the
    -- endianness repair (libcrux issue #1275) is the identity.
    (h_fix : ∀ es,
      _root_.incremental_mlkem768.potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275
        es = ok none) :
    round_trip rngInst cryptoRngInst rng ⦃ ss1 ss2 => ss1 = ss2 ⦄ := by
  unfold round_trip generate encaps1 encaps2 decaps
  -- ### `generate`: seed buffer, RNG fill, `from_seed`, and the three accessors.
  step as ⟨seedP, h_seedS, h_seedBack⟩
  obtain ⟨seedS, seedBack⟩ := seedP
  simp only at h_seedS h_seedBack
  obtain ⟨rng1, s1, h_fb1, h_s1len⟩ := h_fill rng seedS
  step*
  rw [h_fb1]
  simp only [step_simps]
  obtain ⟨k, h_k⟩ := KeyPairCompressedBytes.from_seed_ok (seedBack s1)
  rw [h_k]
  simp only [step_simps]
  obtain ⟨hdrA, h_hdrA⟩ := KeyPairCompressedBytes.pk1_ok k
  rw [h_hdrA]
  simp only [step_simps]
  step as ⟨hdrSl, h_hdrSl⟩
  step as ⟨hdrV, h_hdrV⟩
  obtain ⟨ekA, h_ekA⟩ := KeyPairCompressedBytes.pk2_ok k
  rw [h_ekA]
  simp only [step_simps]
  step as ⟨ekSl0, h_ekSl0⟩
  step as ⟨ekV, h_ekV⟩
  obtain ⟨dkA, h_dkA⟩ := KeyPairCompressedBytes.sk_ok k
  rw [h_dkA]
  simp only [step_simps]
  step as ⟨dkSl0, h_dkSl0⟩
  step as ⟨dkV, h_dkV⟩
  -- ### `encaps1`: randomness buffer, RNG fill, state/secret buffers, `encapsulate1`.
  step as ⟨randP, h_randS, h_randBack⟩
  obtain ⟨randS, randBack⟩ := randP
  simp only at h_randS h_randBack
  obtain ⟨rng2, s2, h_fb2, h_s2len⟩ := h_fill rng1 randS
  step*
  rw [h_fb2]
  simp only [step_simps]
  rw [encaps_state_len_eq_2080]
  simp only [step_simps]
  step as ⟨stateV, h_stateV1, h_stateV2⟩
  rw [libcrux_ml_kem.constants.SHARED_SECRET_SIZE_eq_32]
  simp only [step_simps]
  step as ⟨ssV, h_ssV1, h_ssV2⟩
  step as ⟨hdrS2, h_hdrS2⟩
  simp only [step_simps, lift, alloc.vec.Vec.deref_mut]
  -- The header slice seen by `encapsulate1` carries the bytes of `pk1 k`.
  have h_hdrS2_val : hdrS2.val = hdrA.val := by
    rw [h_hdrS2, ← h_hdrV, h_hdrSl]; rfl
  -- `encapsulate1` on the header bytes, the sampled randomness, and the two buffers.
  obtain ⟨⟨re1, st', ss'⟩, h_e1, h_post1⟩ :=
    WP.spec_imp_exists
      (encapsulate1_ok hdrS2 (randBack s2) ⟨↑stateV, by scalar_tac⟩ ⟨↑ssV, by scalar_tac⟩
        (by simp only [Slice.length, h_hdrS2_val]; scalar_tac)
        (by simp only [Slice.length]; scalar_tac)
        (by simp only [Slice.length]; scalar_tac))
  simp only [WP.uncurry'_pair] at h_post1
  obtain ⟨⟨c1, rfl⟩, h_st'len, h_ss'len⟩ := h_post1
  rw [h_e1]
  simp only [step_simps]
  simp only [core.result.Result.expect]
  step as ⟨ct1V, h_ct1V⟩
  -- ### `encaps2`: the endianness fix is the identity, then `encapsulate2`.
  rw [h_fix]
  simp only [step_simps, core.option.Option.as_ref, core.option.Option.unwrap_or]
  step as ⟨esSl, h_esSl⟩
  have h_esSl_len : esSl.len = 2080#usize := by
    have := Slice.len_val esSl
    scalar_tac
  simp only [core.array.TryFromSharedArraySlice.try_from, h_esSl_len, dif_pos]
  simp only [step_simps]
  step as ⟨ekSl2, h_ekSl2⟩
  have h_ekSl2_len : ekSl2.len = 1152#usize := by
    have := Slice.len_val ekSl2
    scalar_tac
  simp only [h_ekSl2_len, dif_pos]
  simp only [step_simps]
  have h_ekArr : (⟨↑ekSl2, by scalar_tac⟩ : Array Std.U8 1152#usize) = ekA := by
    have h_val : ekSl2.val = ekA.val := by
      rw [h_ekSl2, ← h_ekV, h_ekSl0]; rfl
    exact Subtype.ext h_val
  rw [h_ekArr]
  obtain ⟨c2, h_e2, -⟩ := WP.spec_imp_exists (encapsulate2_ok ⟨↑esSl, by scalar_tac⟩ ekA)
  rw [h_e2]
  simp only [step_simps]
  step as ⟨ct2V, h_ct2V⟩
  -- ### `decaps`: rebuild the fixed-size arrays and decapsulate.
  step as ⟨dc1Sl, h_dc1Sl⟩
  step as ⟨r1, h_r1⟩
  have h_dc1Sl_len : dc1Sl.length = 960 := by
    simp only [Slice.length, h_dc1Sl, ← h_ct1V]
    scalar_tac
  rcases r1 with c1a | e1
  swap
  · simp only [h_dc1Sl_len, ne_eq, not_true_eq_false] at h_r1
  simp only at h_r1
  obtain ⟨h_c1a_val, h_c1a_len⟩ := h_r1
  simp only [step_simps]
  step as ⟨dc2Sl, h_dc2Sl⟩
  step as ⟨r2, h_r2⟩
  have h_dc2Sl_len : dc2Sl.length = 128 := by
    simp only [Slice.length, h_dc2Sl, ← h_ct2V]
    scalar_tac
  rcases r2 with c2a | e2
  swap
  · simp only [h_dc2Sl_len, ne_eq, not_true_eq_false] at h_r2
  simp only at h_r2
  obtain ⟨h_c2a_val, h_c2a_len⟩ := h_r2
  simp only [step_simps]
  step as ⟨dkSl2, h_dkSl2⟩
  have h_dkSl2_val : dkSl2.val = dkA.val := by
    rw [h_dkSl2, ← h_dkV, h_dkSl0]; rfl
  have h_dkSl2_len : dkSl2.len = 2400#usize := by
    have := Slice.len_val dkSl2
    simp only [Slice.length, h_dkSl2_val] at this
    scalar_tac
  simp only [h_dkSl2_len, dif_pos]
  simp only [step_simps]
  -- The rebuilt arrays are exactly the objects produced upstream.
  have h_dkArr : (⟨↑dkSl2, by scalar_tac⟩ : Array Std.U8 2400#usize) = dkA := by
    apply Subtype.ext
    exact h_dkSl2_val
  rw [h_dkArr]
  have h_c1Ct : ({ value := c1a } : Ciphertext1 960#usize) = c1 := by
    have h : c1a = c1.value := by
      apply Subtype.ext
      rw [h_c1a_val, h_dc1Sl, ← h_ct1V]; rfl
    rw [h]
  rw [h_c1Ct]
  have h_c2Ct : ({ value := c2a } : Ciphertext2 128#usize) = c2 := by
    have h : c2a = c2.value := by
      apply Subtype.ext
      rw [h_c2a_val, h_dc2Sl, ← h_ct2V]; rfl
    rw [h]
  rw [h_c2Ct]
  -- Decapsulation recovers the shared secret of `encapsulate1`
  -- (`decapsulate_compressed_key_roundtrip`).
  obtain ⟨ssA, h_dec, h_ssA⟩ :=
    WP.spec_imp_exists
      (decapsulate_compressed_key_roundtrip (seedBack s1) k hdrA ekA dkA hdrS2 (randBack s2)
        ⟨↑stateV, by scalar_tac⟩ ⟨↑ssV, by scalar_tac⟩ c1 st' ss'
        ⟨↑esSl, by scalar_tac⟩ c2
        h_k h_hdrA h_ekA h_dkA h_hdrS2_val h_e1 h_esSl h_e2)
  rw [h_dec]
  simp only [step_simps]
  step as ⟨ss2V, h_ss2V⟩
  -- Both shared secrets carry the bytes of `ss'`.
  have h_val : ss'.val = ss2V.val := by
    rw [← h_ss2V, ← h_ssA]; rfl
  exact Subtype.ext h_val

end spqr.incremental_mlkem768
