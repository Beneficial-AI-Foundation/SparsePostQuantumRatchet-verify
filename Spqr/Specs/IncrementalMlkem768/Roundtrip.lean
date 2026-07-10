/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Zhang Liao
-/
import SrcTranslated.Funs
import SrcTranslated.FunsExternal
import Spqr.Specs.IncrementalMlkem768.Decaps
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
axioms.  Key generation and the key-pair accessors have pure companions
(`from_seed!`, `pk1!`, `pk2!`, `sk!`) with bridging axioms (`from_seed_eq`,
`pk1_eq`, `pk2_eq`, `sk_eq`) stating that each call succeeds and returns its
companion's value, and the two size constants have value axioms
(`encaps_state_len_eq_2080`, `SHARED_SECRET_SIZE_eq_32`); these live in
`SrcTranslated/FunsExternal.lean` next to the bare declarations, in
the style of `libcrux_hmac.hmac_sha256_tag32_length_eq_32` (#243).  The
per-function specifications of the incremental primitives have their own
spec files, like the proved specifications in this repository:

* `Spqr/Specs/LibcruxMlKem/Incremental/Encapsulate1.lean` — functional spec:
  pure companions `encapsulate1_ct1!` / `encapsulate1_st!` / `encapsulate1_ss!`
  with the bridging axiom `encapsulate1_eq` and the buffer-length axioms
  `encapsulate1_st_length` / `encapsulate1_ss_length`, all conditional on the
  input-length preconditions (`encapsulate1` genuinely fails on mis-sized
  slices, so an unconditional bridging axiom would be unfaithful);
* `Spqr/Specs/LibcruxMlKem/Incremental/Encapsulate2.lean` (`encapsulate2_ok`);
* `Spqr/Specs/LibcruxMlKem/Incremental/DecapsulateCompressedKey.lean`
  (`decapsulate_compressed_key_roundtrip`) — **the KEM correctness of the
  incremental libcrux API itself**: decapsulation with the matching secret key
  recovers the shared secret produced by the `encapsulate1`/`encapsulate2`
  chain.  This is the "roundtrip property for decaps" proper, stated over the
  extracted axioms and independent of any external formalisation.

The SPQR `decaps` wrapper itself has a *proved* functional specification,
`decaps_spec` (`Spqr/Specs/IncrementalMlkem768/Decaps.lean`): given the
fixed-size images of its three vector inputs and the behaviour of
`decapsulate_compressed_key` on them, `decaps` succeeds and returns exactly
that shared secret.  The proof below applies `decaps_spec` at the `decaps`
call site (discharging its hypothesis with
`decapsulate_compressed_key_roundtrip`) instead of unfolding the wrapper.

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
  unfold round_trip generate encaps1 encaps2
  -- ### `generate`: seed buffer, RNG fill, `from_seed`, and the three accessors.
  step as ⟨seedP, h_seedS, h_seedBack⟩
  obtain ⟨seedS, seedBack⟩ := seedP
  simp only at h_seedS h_seedBack
  obtain ⟨rng1, s1, h_fb1, h_s1len⟩ := h_fill rng seedS
  step*
  rw [h_fb1]
  simp only [step_simps]
  rw [KeyPairCompressedBytes.from_seed_eq]
  simp only [step_simps]
  rw [KeyPairCompressedBytes.pk1_eq]
  simp only [step_simps]
  step as ⟨hdrSl, h_hdrSl⟩
  step as ⟨hdrV, h_hdrV⟩
  rw [KeyPairCompressedBytes.pk2_eq]
  simp only [step_simps]
  step as ⟨ekSl0, h_ekSl0⟩
  step as ⟨ekV, h_ekV⟩
  rw [KeyPairCompressedBytes.sk_eq]
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
  -- The header slice seen by `encapsulate1` carries the bytes of `pk1!` of the
  -- generated key pair.
  have h_hdrS2_val : hdrS2.val =
      (KeyPairCompressedBytes.pk1! (KeyPairCompressedBytes.from_seed! (seedBack s1))).val := by
    rw [h_hdrS2, ← h_hdrV, h_hdrSl]; rfl
  -- `encapsulate1` on the header bytes, the sampled randomness, and the two
  -- buffers: it succeeds and returns its pure companions' values
  -- (`encapsulate1_eq`), preserving the buffer lengths.
  have h_hdrS2_len : hdrS2.length = 64 := by
    simp only [Slice.length, h_hdrS2_val]; scalar_tac
  have h_stS_len : Slice.length (⟨↑stateV, by scalar_tac⟩ : Slice Std.U8) = 2080 := by
    simp only [Slice.length]; scalar_tac
  have h_ssS_len : Slice.length (⟨↑ssV, by scalar_tac⟩ : Slice Std.U8) = 32 := by
    simp only [Slice.length]; scalar_tac
  have h_e1 :=
    encapsulate1_eq hdrS2 (randBack s2) _ _ h_hdrS2_len h_stS_len h_ssS_len
  have h_st'len :=
    encapsulate1_st_length hdrS2 (randBack s2) _ _ h_hdrS2_len h_stS_len h_ssS_len
  have h_ss'len :=
    encapsulate1_ss_length hdrS2 (randBack s2) _ _ h_hdrS2_len h_stS_len h_ssS_len
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
  have h_ekArr : (⟨↑ekSl2, by scalar_tac⟩ : Array Std.U8 1152#usize) =
      KeyPairCompressedBytes.pk2! (KeyPairCompressedBytes.from_seed! (seedBack s1)) := by
    have h_val : ekSl2.val =
        (KeyPairCompressedBytes.pk2! (KeyPairCompressedBytes.from_seed! (seedBack s1))).val := by
      rw [h_ekSl2, ← h_ekV, h_ekSl0]; rfl
    exact Subtype.ext h_val
  rw [h_ekArr]
  obtain ⟨c2, h_e2, -⟩ :=
    WP.spec_imp_exists (encapsulate2_ok ⟨↑esSl, by scalar_tac⟩
      (KeyPairCompressedBytes.pk2! (KeyPairCompressedBytes.from_seed! (seedBack s1))))
  rw [h_e2]
  simp only [step_simps]
  step as ⟨ct2V, h_ct2V⟩
  -- ### `decaps`: apply the functional spec `decaps_spec`
  -- (`Spqr/Specs/IncrementalMlkem768/Decaps.lean`) at the call site.
  -- The vectors fed to `decaps` carry the bytes of the objects produced upstream.
  have h_dkVal : (KeyPairCompressedBytes.sk!
      (KeyPairCompressedBytes.from_seed! (seedBack s1))).val = dkV.val := by
    rw [← h_dkV, h_dkSl0]; rfl
  have h_ct1Val : (encapsulate1_ct1! hdrS2 (randBack s2) ⟨↑stateV, by scalar_tac⟩
      ⟨↑ssV, by scalar_tac⟩).value.val = ct1V.val := by
    rw [← h_ct1V]; rfl
  have h_ct2Val : c2.value.val = ct2V.val := by
    rw [← h_ct2V]; rfl
  -- Decapsulation recovers the shared secret of `encapsulate1`
  -- (`decapsulate_compressed_key_roundtrip`); this discharges the hypothesis of
  -- `decaps_spec`.
  obtain ⟨ssA, h_dec, h_ssA⟩ :=
    WP.spec_imp_exists
      (decapsulate_compressed_key_roundtrip (seedBack s1) hdrS2 (randBack s2)
        _ _ ⟨↑esSl, by scalar_tac⟩ c2
        h_hdrS2_val h_stS_len h_ssS_len h_esSl h_e2)
  obtain ⟨ss2V, h_deq, h_ss2Val, -⟩ :=
    WP.spec_imp_exists (decaps_spec dkV ct1V ct2V _ _ c2 ssA h_dkVal h_ct1Val h_ct2Val h_dec)
  rw [h_deq]
  simp only [step_simps]
  -- Both shared secrets carry the bytes of `encapsulate1_ss!`.
  have h_val : (encapsulate1_ss! hdrS2 (randBack s2) ⟨↑stateV, by scalar_tac⟩
      ⟨↑ssV, by scalar_tac⟩).val = ss2V.val := by
    rw [h_ss2Val, h_ssA]
  exact Subtype.ext h_val

end spqr.incremental_mlkem768
