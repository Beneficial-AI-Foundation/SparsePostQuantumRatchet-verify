/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Alessandro D'Angelo
-/
import SrcTranslated.Funs
import SrcTranslated.FunsExternal

/-!
# Spec theorem for `encaps1`

Performs the first incremental ML-KEM-768 encapsulation phase and packages its ciphertext, state,
and shared secret as byte vectors, returning the RNG state produced by the randomness fill.

This is a conditional wrapper contract, not a cryptographic specification of libcrux. The RNG
transition, opaque size queries, successful outer and inner encapsulation results, and output slice
lengths are explicit hypotheses. The 64-byte header condition alone establishes none of these facts.
The Rust Hax assumptions are not treated as proved dependency contracts. No randomness distribution,
security, header validity, or agreement with later decapsulation is asserted.

Source: "src/incremental_mlkem768.rs", lines 46–66.
-/

open Aeneas Aeneas.Std Result

namespace spqr.incremental_mlkem768

open alloc.vec
open libcrux_ml_kem.constants (SHARED_SECRET_SIZE)
open libcrux_ml_kem.mlkem768.incremental (encaps_state_len encapsulate1)
open libcrux_ml_kem.ind_cca.incremental.types (Ciphertext1)

/-- **Spec theorem for `spqr::incremental_mlkem768::encaps1`**

Given a 64-byte header, assume that filling the initial 32-byte zero slice yields `randomness` and
`rng1`, that the size queries return 2080 and 32, and that phase one on this header and randomness
with zero-filled output buffers succeeds with `ciphertext`, `state`, and `secret`. Assume also that
the returned state and secret slices retain the required lengths. Then the wrapper succeeds,
preserves all three dependency outputs byte-for-byte, and returns exactly `rng1`. The ciphertext
length 960 comes from its fixed array type; state and secret lengths depend on the hypotheses. -/
@[step]
theorem encaps1_spec {R : Type} (randrngRngInst : rand.rng.Rng R)
    (rand_coreCryptoRngInst : rand_core.CryptoRng R) (hdr : Vec U8) (rng : R)
    (randomness : Array U8 32#usize) (rng1 : R)
    (ciphertext : Ciphertext1 960#usize) (state secret : Slice U8)
    (h_hdr_len : hdr.length = 64) -- Mirrors Rust requires; unnecessary for this postcondition.
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
  sorry

end spqr.incremental_mlkem768
