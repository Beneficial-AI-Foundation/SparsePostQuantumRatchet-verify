/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Alessandro D'Angelo
-/
import SrcTranslated.Funs
import SrcTranslated.FunsExternal

/-!
# Spec theorem for `encaps1`

`encaps1` performs the first incremental ML-KEM-768 encapsulation phase. It returns the ciphertext,
serialized encapsulation state and shared secret as byte vectors, together with the updated RNG.

The specification assumes contracts for RNG filling, the two size queries and libcrux encapsulation.
These require successful calls with the stated buffer lengths, for every RNG state and every
64-byte header. The fill contract concerns the `Rng` dictionary used by `encaps1`. Neither the
`CryptoRng` marker nor the Rust `hax_lib::assume!` annotations establish these contracts.

The theorem relates the returned bytes and RNG state to the component calls. Cryptographic
correctness of libcrux and the distribution of random bytes are outside this specification.

Source: "src/incremental_mlkem768.rs", lines 46–66.

## Randomness

The postcondition retains the bytes supplied by `fill_bytes` and the successor RNG state, without
assigning a distribution to either. A separate probabilistic model may use fresh uniform coins.
Relating a concrete generator to that model is a further proof obligation.

Formosa separates `enc_derand`, which takes explicit coins, in its [EasyCrypt specification][spec]
from coin sampling in its [security model][security]. The relevant procedures are in
`ml-kem/MLKEM768.ec` and `proof/spec/MLKEMSecurity768.ec`, respectively. Apple's
[corecrypto verification][corecrypto], using Galois's SAW and Cryptol, similarly assumes a stateful
RNG contract. Its `corecrypto_verify/rng.cry` models the returned bytes and successor state with an
uninterpreted function; `corecrypto_verify/technical_overview/soundness.md` leaves entropy quality
outside the proof.

[spec]:
  https://github.com/formosa-crypto/crypto-specs/tree/fb050598ed356c5c6604d92a1e198b2dd4543777
[security]:
  https://github.com/formosa-crypto/formosa-mlkem/tree/475b87434506280fdfa1a1ba5da0af3787e00579
[corecrypto]:
  https://github.com/apple/corecrypto/tree/9612a959abb6eac0aac3ee6a7245c46365c9d81b
-/

open Aeneas Aeneas.Std Result

namespace spqr.incremental_mlkem768

open alloc.vec
open Aeneas.Std.alloc
open Aeneas.Std.core
open libcrux_ml_kem.constants (SHARED_SECRET_SIZE)
open libcrux_ml_kem.mlkem768.incremental (encaps_state_len encapsulate1)
open libcrux_ml_kem.ind_cca.incremental.types (Ciphertext1)

/-- Under `fill_service`, filling a 32-byte buffer returns the slice of a 32-byte array. -/
theorem fill_bytes32_spec {R : Type} (randrngRngInst : rand.rng.Rng R)
    (fill_service : ∀ (r : R) (s : Slice U8), s.length = 32 →
      randrngRngInst.rand_coreRngCoreInst.fill_bytes r s ⦃
        (_r' : R) (s' : Slice U8) => s'.length = 32 ⦄)
    (rng : R) (buffer : Slice U8) (h_buffer : buffer.length = 32) :
    randrngRngInst.rand_coreRngCoreInst.fill_bytes rng buffer ⦃
      (_rng1 : R) (filled : Slice U8) =>
      ∃ coins : Array U8 32#usize, filled = coins.to_slice ⦄ := by
  apply WP.spec_mono (fill_service rng buffer h_buffer)
  rintro ⟨rng1, filled⟩ h_length
  simp only [WP.uncurry'_pair] at h_length ⊢
  refine ⟨⟨filled.val, h_length⟩, ?_⟩
  apply Subtype.ext
  rfl

/-- `encaps1` preserves component outputs and the successor RNG when dependency calls succeed. -/
private theorem encaps1_plumbing_spec {R : Type} (randrngRngInst : rand.rng.Rng R)
    (rand_coreCryptoRngInst : rand_core.CryptoRng R) (hdr : Vec U8) (rng : R)
    (randomness : Array U8 32#usize) (rng1 : R)
    (ciphertext : Ciphertext1 960#usize) (state secret : Slice U8)
    (h_fill : randrngRngInst.rand_coreRngCoreInst.fill_bytes rng
      (Array.to_slice (Array.repeat 32#usize 0#u8)) = ok (rng1, randomness.to_slice))
    (h_state_size : encaps_state_len = ok 2080#usize)
    (h_secret_size : SHARED_SECRET_SIZE = ok 32#usize)
    (h_encapsulate : encapsulate1 (Vec.deref hdr) randomness
      (Array.to_slice (Array.repeat 2080#usize 0#u8))
      (Array.to_slice (Array.repeat 32#usize 0#u8)) = ok (.Ok ciphertext, state, secret))
    (h_state_len : state.length = 2080)
    (h_secret_len : secret.length = 32) :
    encaps1 randrngRngInst rand_coreCryptoRngInst hdr rng ⦃
      ((ct1 : Vec U8), (es : Vec U8), (ss : Vec U8)) (rng' : R) =>
      ct1.val = ciphertext.value.val ∧
      es.val = state.val ∧
      ss.val = secret.val ∧
      rng' = rng1 ∧
      ct1.length = 960 ∧
      es.length = 2080 ∧
      ss.length = 32 ⦄ := by
  have h_alloc (n : Usize) :
      vec.from_elem clone.CloneU8 0#u8 n =
        ok (show Vec U8 from (Array.repeat n 0#u8).to_slice) := by
    obtain ⟨v, hv, h_val, _⟩ :=
      WP.spec_imp_exists (vec.from_elem_spec clone.CloneU8 0#u8 n rfl)
    apply hv.trans
    apply congrArg ok
    apply Subtype.ext
    exact h_val
  have h_back :
      Array.from_slice (Array.repeat 32#usize 0#u8) randomness.to_slice = randomness := by
    apply Subtype.ext
    exact Array.from_slice_val _ _ randomness.property
  have h_hdr : Vec.as_slice Global hdr = ok (Vec.deref hdr) := rfl
  have h_mut (n : Usize) :
      Vec.deref_mut (show Vec U8 from (Array.repeat n 0#u8).to_slice) =
        ((Array.repeat n 0#u8).to_slice, fun s : Slice U8 => (show Vec U8 from s)) := rfl
  have h_copy :
      slice.Slice.to_vec clone.CloneU8 ciphertext.value.to_slice =
        ok (show Vec U8 from ciphertext.value.to_slice) := by
    obtain ⟨v, hv, h_val⟩ := WP.spec_imp_exists
      (slice.Slice.to_vec_spec clone.CloneU8 ciphertext.value.to_slice (by
        intro x _
        rfl))
    exact hv.trans (congrArg ok h_val.symm)
  unfold encaps1
  simp only [Array.to_slice_mut, lift, bind_tc_ok, Aeneas.Std.uncurry_apply_pair, h_fill,
    h_state_size, h_secret_size, h_alloc, h_hdr, h_mut, h_back, h_encapsulate,
    result.Result.expect, h_copy, WP.spec_ok, WP.uncurry'_pair]
  exact ⟨rfl, True.intro, True.intro, True.intro, ciphertext.value.property,
    h_state_len, h_secret_len⟩

/-- **Spec theorem for `spqr::incremental_mlkem768::encaps1`**

Given the component contracts and a 64-byte header, `encaps1` returns ciphertext, state and secret
vectors of lengths 960, 2080 and 32. Their bytes equal the corresponding libcrux outputs, using the
bytes supplied by `fill_bytes`. The returned RNG is the successor state of that same fill call. -/
@[step]
theorem encaps1_spec {R : Type} (randrngRngInst : rand.rng.Rng R)
    (rand_coreCryptoRngInst : rand_core.CryptoRng R)
    (fill_service : ∀ (r : R) (s : Slice U8), s.length = 32 →
      randrngRngInst.rand_coreRngCoreInst.fill_bytes r s ⦃
        (_r' : R) (s' : Slice U8) => s'.length = 32 ⦄)
    (state_size_service : encaps_state_len ⦃ (n : Usize) => n = 2080#usize ⦄)
    (secret_size_service : SHARED_SECRET_SIZE ⦃ (n : Usize) => n = 32#usize ⦄)
    (phase1_service : ∀ (h : Slice U8) (coins : Array U8 32#usize)
        (es ss : Slice U8),
      h.length = 64 → es.length = 2080 → ss.length = 32 →
      encapsulate1 h coins es ss ⦃ inner (es' : Slice U8) (ss' : Slice U8) =>
        (∃ ct : Ciphertext1 960#usize, inner = .Ok ct) ∧
        es'.length = 2080 ∧ ss'.length = 32 ⦄)
    (hdr : Vec U8) (rng : R) (h_hdr_len : hdr.length = 64) :
    encaps1 randrngRngInst rand_coreCryptoRngInst hdr rng ⦃
      ((ct1 : Vec U8), (es : Vec U8), (ss : Vec U8)) (rng' : R) =>
      ct1.length = 960 ∧
      es.length = 2080 ∧
      ss.length = 32 ∧
      ∃ (coins : Array U8 32#usize) (ct : Ciphertext1 960#usize)
        (state secret : Slice U8),
        randrngRngInst.rand_coreRngCoreInst.fill_bytes rng
          (Array.to_slice (Array.repeat 32#usize 0#u8)) = ok (rng', coins.to_slice) ∧
        encapsulate1 (Vec.deref hdr) coins
          (Array.to_slice (Array.repeat 2080#usize 0#u8))
          (Array.to_slice (Array.repeat 32#usize 0#u8)) = ok (.Ok ct, state, secret) ∧
        ct1.val = ct.value.val ∧
        es.val = state.val ∧
        ss.val = secret.val ∧
        state.length = 2080 ∧
        secret.length = 32 ⦄ := by
  have h_buffer : (Array.repeat 32#usize 0#u8).to_slice.length = 32 :=
    Array.length_to_slice _
  obtain ⟨⟨rng1, filled⟩, h_fill, h_coins⟩ :=
    WP.spec_imp_exists (fill_bytes32_spec randrngRngInst fill_service rng
      (Array.repeat 32#usize 0#u8).to_slice h_buffer)
  simp only [WP.uncurry'_pair] at h_coins
  obtain ⟨coins, h_coins⟩ := h_coins
  rw [h_coins] at h_fill
  obtain ⟨state_size, h_state_size, h_state_value⟩ := WP.spec_imp_exists state_size_service
  rw [h_state_value] at h_state_size
  obtain ⟨secret_size, h_secret_size, h_secret_value⟩ := WP.spec_imp_exists secret_size_service
  rw [h_secret_value] at h_secret_size
  have h_header : (Vec.deref hdr).length = 64 := h_hdr_len
  have h_state_buffer : (Array.repeat 2080#usize 0#u8).to_slice.length = 2080 :=
    Array.length_to_slice _
  have h_secret_buffer : (Array.repeat 32#usize 0#u8).to_slice.length = 32 :=
    Array.length_to_slice _
  obtain ⟨⟨inner, state, secret⟩, h_encapsulate, h_phase⟩ :=
    WP.spec_imp_exists (phase1_service (Vec.deref hdr) coins
      (Array.repeat 2080#usize 0#u8).to_slice (Array.repeat 32#usize 0#u8).to_slice
      h_header h_state_buffer h_secret_buffer)
  simp only [WP.uncurry'_pair] at h_phase
  obtain ⟨⟨ct, h_ct⟩, h_state_len, h_secret_len⟩ := h_phase
  rw [h_ct] at h_encapsulate
  have h_wrapper := encaps1_plumbing_spec randrngRngInst rand_coreCryptoRngInst hdr rng
    coins rng1 ct state secret h_fill h_state_size h_secret_size h_encapsulate
    h_state_len h_secret_len
  apply WP.spec_mono h_wrapper
  rintro ⟨⟨ct1, es, ss⟩, rng'⟩ h_outputs
  simp only [WP.uncurry'_pair] at h_outputs ⊢
  obtain ⟨h_ct1, h_es, h_ss, h_rng, h_ct1_len, h_es_len, h_ss_len⟩ := h_outputs
  refine ⟨h_ct1_len, h_es_len, h_ss_len, coins, ct, state, secret, ?_, h_encapsulate,
    h_ct1, h_es, h_ss, h_state_len, h_secret_len⟩
  rw [h_rng]
  exact h_fill

end spqr.incremental_mlkem768
