/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Zhang Liao
-/
import SrcTranslated.FunsExternal
import Spqr.Specs.LibcruxMlKem.Incremental.Encapsulate1

/-! # Specification axiom for `libcrux_ml_kem::mlkem768::incremental::decapsulate_compressed_key`

`decapsulate_compressed_key` is an opaque external function (declared as a bare
axiom in `SrcTranslated/FunsExternal.lean`), so its behaviour cannot be proved
and is instead assumed here as a specification axiom, stating the conditions
needed by the round-trip spec (`Spqr/Specs/IncrementalMlkem768/Roundtrip.lean`).

Correctness of decapsulation is only expressible relative to the encapsulation
that produced the ciphertexts, so the axiom mentions the whole incremental
chain: decapsulation inverts encapsulation.  The key-pair components are
written with the pure companions `KeyPairCompressedBytes.from_seed!` / `pk1!` /
`pk2!` / `sk!` (see `SrcTranslated/FunsExternal.lean`) and the `encapsulate1`
outputs with the pure companions `encapsulate1_ct1!` / `encapsulate1_st!` /
`encapsulate1_ss!` (see
`Spqr/Specs/LibcruxMlKem/Incremental/Encapsulate1.lean`), which avoids having
to carry the `ok`-equations of key generation, the accessors, and
`encapsulate1` as hypotheses.  Since the `encapsulate1` companions are only
meaningful on well-sized buffers, the axiom keeps the corresponding length
preconditions (the header length follows from `h_hdr`, as `pk1!` is a 64-byte
array).

Faithfulness note: stated universally over all seeds and randomness, this is
marginally stronger than the real ML-KEM-768 guarantee, which admits a
negligible (2^-164) decryption-failure probability (FIPS 203, Table 1).
-/

open Aeneas Aeneas.Std Result

open spqr.libcrux_ml_kem.ind_cca.incremental.types (Ciphertext2)

namespace libcrux_ml_kem.mlkem768.incremental

/-- KEM correctness of the incremental API: for the key pair derived from
`seed` (`from_seed!`), if `encapsulate1` was run against (the bytes of) its
public header `pk1!` — producing the ciphertext `encapsulate1_ct1!`, the state
`encapsulate1_st!` and the shared secret `encapsulate1_ss!` — and
`encapsulate2` was run on (the bytes of) that state against its encapsulation
key `pk2!`, producing `ct2`, then `decapsulate_compressed_key` with its
decapsulation key `sk!` on those ciphertexts succeeds and returns exactly the
shared secret of `encapsulate1`. -/
axiom decapsulate_compressed_key_roundtrip
    (seed : Array Std.U8 64#usize) (hdrS : Slice Std.U8)
    (rand : Array Std.U8 32#usize) (st ss : Slice Std.U8)
    (stA : Array Std.U8 2080#usize) (ct2 : Ciphertext2 128#usize)
    (h_hdr : hdrS.val =
      (KeyPairCompressedBytes.pk1! (KeyPairCompressedBytes.from_seed! seed)).val)
    (h_st : st.length = 2080) (h_ss : ss.length = 32)
    (h_stA : stA.val = (encapsulate1_st! hdrS rand st ss).val)
    (h_enc2 : encapsulate2 stA
      (KeyPairCompressedBytes.pk2! (KeyPairCompressedBytes.from_seed! seed)) =
      ok ct2) :
    decapsulate_compressed_key
      (KeyPairCompressedBytes.sk! (KeyPairCompressedBytes.from_seed! seed))
      (encapsulate1_ct1! hdrS rand st ss) ct2
      ⦃ ssA => ssA.val = (encapsulate1_ss! hdrS rand st ss).val ⦄

end libcrux_ml_kem.mlkem768.incremental
