/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Zhang Liao
-/
import SrcTranslated.Funs
import SrcTranslated.FunsExternal

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
`fill_bytes` is an abstract trait field.  Consequently the theorem is stated
under explicit hypotheses that model the essential behaviour of those opaque
functions:

* `h_fill` — the RNG's `fill_bytes` is panic-free and preserves the buffer length;
* `h_state_len`, `h_ss_size` — the values of the two opaque size constants
  (`encaps_state_len = 2080`, `SHARED_SECRET_SIZE = 32`);
* `h_seed`, `h_pk1`, `h_pk2`, `h_sk` — key generation from a 64-byte seed and
  the key-pair accessors are panic-free;
* `h_enc1` — `encapsulate1` on well-sized inputs succeeds with an `Ok`
  ciphertext and preserves the lengths of the state and shared-secret buffers;
* `h_fix` — the endianness repair function
  `potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275` is the
  identity (returns `None`) on the states considered here: the repair path
  (libcrux issue #1275) only concerns states persisted with a broken encoding,
  not states freshly produced by `encapsulate1` in the same run;
* `h_enc2` — `encapsulate2` is panic-free;
* `h_kem` — **the KEM correctness of the incremental libcrux API itself**: if a
  key pair `k` stems from `from_seed`, `encapsulate1` was run against (the bytes
  of) `pk1 k` producing ciphertext `ct1`, state `st'` and shared secret `ss'`,
  and `encapsulate2` was run on (the bytes of) that state against `pk2 k`
  producing `ct2`, then `decapsulate_compressed_key` on `sk k`, `ct1`, `ct2`
  succeeds and returns exactly `ss'`.

`h_kem` is the "roundtrip property for decaps" proper — the correctness
statement of the incremental Encaps1/Encaps2/Decaps triple, stated here over
the extracted axioms and independent of any external formalisation.  What this
file *proves* is the linking theorem: the SPQR wrapper layer (slicing,
`try_into` conversions, buffer allocation, the endianness-fix dispatch, and all
`Vec`/`Array`/`Slice` plumbing) faithfully forwards to the primitives, so the
wrapper-level composition inherits the primitive-level roundtrip.

None of the hypotheses is added as a global axiom: the trust base of the
project is unchanged.  Promoting (some of) them to documented axioms in
`FunsExternal.lean` — in the style of `libcrux_hmac.hmac_sha256_tag32_length_eq_32`
(#243) — is a separate, deliberate decision.

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

Under the modelling hypotheses on the opaque libcrux incremental API (see the
module docstring; `h_kem` is the correctness of the underlying incremental
KEM), the composition `generate → encaps1 → encaps2 → decaps` succeeds and the
decapsulated shared secret equals the encapsulated one. -/
theorem round_trip_spec {R : Type} (rngInst : rand.rng.Rng R)
    (cryptoRngInst : rand_core.CryptoRng R) (rng : R)
    -- The RNG's `fill_bytes` is panic-free and preserves the buffer length.
    (h_fill : ∀ (r : R) (s : Slice Std.U8), ∃ r' s',
      rngInst.rand_coreRngCoreInst.fill_bytes r s = ok (r', s') ∧
      s'.length = s.length)
    -- Values of the opaque size constants.
    (h_state_len : encaps_state_len = ok 2080#usize)
    (h_ss_size : libcrux_ml_kem.constants.SHARED_SECRET_SIZE = ok 32#usize)
    -- Key generation and the key-pair accessors are panic-free.
    (h_seed : ∀ (seed : Array Std.U8 64#usize), ∃ k,
      KeyPairCompressedBytes.from_seed seed = ok k)
    (h_pk1 : ∀ k, ∃ a, KeyPairCompressedBytes.pk1 k = ok a)
    (h_pk2 : ∀ k, ∃ a, KeyPairCompressedBytes.pk2 k = ok a)
    (h_sk : ∀ k, ∃ a, KeyPairCompressedBytes.sk k = ok a)
    -- `encapsulate1` succeeds on well-sized inputs and preserves buffer lengths.
    (h_enc1 : ∀ (hdr : Slice Std.U8) (rand : Array Std.U8 32#usize)
        (st ss : Slice Std.U8),
      hdr.length = 64 → st.length = 2080 → ss.length = 32 →
      ∃ ct1 st' ss', encapsulate1 hdr rand st ss = ok (.Ok ct1, st', ss') ∧
        st'.length = 2080 ∧ ss'.length = 32)
    -- Freshly produced encapsulation states are correctly encoded, so the
    -- endianness repair (libcrux issue #1275) is the identity.
    (h_fix : ∀ es,
      _root_.incremental_mlkem768.potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275
        es = ok none)
    -- `encapsulate2` is panic-free.
    (h_enc2 : ∀ (st : Array Std.U8 2080#usize) (ek : Array Std.U8 1152#usize),
      ∃ ct2, encapsulate2 st ek = ok ct2)
    -- KEM correctness of the underlying incremental API: decapsulation with the
    -- matching secret key recovers the shared secret produced by encapsulation.
    (h_kem : ∀ (seed : Array Std.U8 64#usize) k
        (hdrA : Array Std.U8 64#usize) (ekA : Array Std.U8 1152#usize)
        (dkA : Array Std.U8 2400#usize) (hdrS : Slice Std.U8)
        (rand : Array Std.U8 32#usize) (st ss : Slice Std.U8)
        (ct1 : Ciphertext1 960#usize) (st' ss' : Slice Std.U8)
        (stA : Array Std.U8 2080#usize) (ct2 : Ciphertext2 128#usize),
      KeyPairCompressedBytes.from_seed seed = ok k →
      KeyPairCompressedBytes.pk1 k = ok hdrA →
      KeyPairCompressedBytes.pk2 k = ok ekA →
      KeyPairCompressedBytes.sk k = ok dkA →
      hdrS.val = hdrA.val →
      encapsulate1 hdrS rand st ss = ok (.Ok ct1, st', ss') →
      stA.val = st'.val →
      encapsulate2 stA ekA = ok ct2 →
      ∃ ssA, decapsulate_compressed_key dkA ct1 ct2 = ok ssA ∧
        ssA.val = ss'.val) :
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
  obtain ⟨k, h_k⟩ := h_seed (seedBack s1)
  rw [h_k]
  simp only [step_simps]
  obtain ⟨hdrA, h_hdrA⟩ := h_pk1 k
  rw [h_hdrA]
  simp only [step_simps]
  step as ⟨hdrSl, h_hdrSl⟩
  step as ⟨hdrV, h_hdrV⟩
  obtain ⟨ekA, h_ekA⟩ := h_pk2 k
  rw [h_ekA]
  simp only [step_simps]
  step as ⟨ekSl0, h_ekSl0⟩
  step as ⟨ekV, h_ekV⟩
  obtain ⟨dkA, h_dkA⟩ := h_sk k
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
  rw [h_state_len]
  simp only [step_simps]
  step as ⟨stateV, h_stateV1, h_stateV2⟩
  rw [h_ss_size]
  simp only [step_simps]
  step as ⟨ssV, h_ssV1, h_ssV2⟩
  step as ⟨hdrS2, h_hdrS2⟩
  simp only [step_simps, lift, alloc.vec.Vec.deref_mut]
  -- The header slice seen by `encapsulate1` carries the bytes of `pk1 k`.
  have h_hdrS2_val : hdrS2.val = hdrA.val := by
    rw [h_hdrS2, ← h_hdrV, h_hdrSl]; rfl
  -- `encapsulate1` on the header bytes, the sampled randomness, and the two buffers.
  obtain ⟨c1, st', ss', h_e1, h_st'len, h_ss'len⟩ :=
    h_enc1 hdrS2 (randBack s2) ⟨↑stateV, by scalar_tac⟩ ⟨↑ssV, by scalar_tac⟩
      (by simp only [Slice.length, h_hdrS2_val]; scalar_tac)
      (by simp only [Slice.length]; scalar_tac)
      (by simp only [Slice.length]; scalar_tac)
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
  obtain ⟨c2, h_e2⟩ := h_enc2 ⟨↑esSl, by scalar_tac⟩ ekA
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
  -- Decapsulation recovers the shared secret of `encapsulate1` (`h_kem`).
  obtain ⟨ssA, h_dec, h_ssA⟩ :=
    h_kem (seedBack s1) k hdrA ekA dkA hdrS2 (randBack s2)
      ⟨↑stateV, by scalar_tac⟩ ⟨↑ssV, by scalar_tac⟩ c1 st' ss'
      ⟨↑esSl, by scalar_tac⟩ c2
      h_k h_hdrA h_ekA h_dkA h_hdrS2_val h_e1 h_esSl h_e2
  rw [h_dec]
  simp only [step_simps]
  step as ⟨ss2V, h_ss2V⟩
  -- Both shared secrets carry the bytes of `ss'`.
  have h_val : ss'.val = ss2V.val := by
    rw [← h_ss2V, ← h_ssA]; rfl
  exact Subtype.ext h_val

end spqr.incremental_mlkem768
