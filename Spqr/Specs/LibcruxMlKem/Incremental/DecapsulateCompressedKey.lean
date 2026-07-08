/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Zhang Liao
-/
import SrcTranslated.FunsExternal

/-! # Specification axiom for `libcrux_ml_kem::mlkem768::incremental::decapsulate_compressed_key`

`decapsulate_compressed_key` is an opaque external function (declared as a bare
axiom in `SrcTranslated/FunsExternal.lean`), so its behaviour cannot be proved
and is instead assumed here as a specification axiom, stating the conditions
needed by the round-trip spec (`Spqr/Specs/IncrementalMlkem768/Roundtrip.lean`).

Correctness of decapsulation is only expressible relative to the encapsulation
that produced the ciphertexts, so the axiom mentions the whole incremental
chain (`KeyPairCompressedBytes.from_seed` / `pk1` / `pk2` / `sk`,
`encapsulate1`, `encapsulate2`): decapsulation inverts encapsulation.

Faithfulness note: stated universally over all seeds and randomness, this is
marginally stronger than the real ML-KEM-768 guarantee, which admits a
negligible (2^-164) decryption-failure probability (FIPS 203, Table 1).
-/

open Aeneas Aeneas.Std Result

open spqr.libcrux_ml_kem.ind_cca.incremental.types (Ciphertext1 Ciphertext2)

namespace libcrux_ml_kem.mlkem768.incremental

/-- KEM correctness of the incremental API: if a key pair `k` stems from
`from_seed`, `encapsulate1` was run against (the bytes of) `pk1 k` producing
ciphertext `ct1`, state `st'` and shared secret `ss'`, and `encapsulate2` was
run on (the bytes of) that state against `pk2 k` producing `ct2`, then
`decapsulate_compressed_key` on `sk k`, `ct1`, `ct2` succeeds and returns
exactly `ss'`. -/
axiom decapsulate_compressed_key_roundtrip
    (seed : Array Std.U8 64#usize) (k : KeyPairCompressedBytes)
    (hdrA : Array Std.U8 64#usize) (ekA : Array Std.U8 1152#usize)
    (dkA : Array Std.U8 2400#usize) (hdrS : Slice Std.U8)
    (rand : Array Std.U8 32#usize) (st ss : Slice Std.U8)
    (ct1 : Ciphertext1 960#usize) (st' ss' : Slice Std.U8)
    (stA : Array Std.U8 2080#usize) (ct2 : Ciphertext2 128#usize)
    (h_seed : KeyPairCompressedBytes.from_seed seed = ok k)
    (h_pk1 : KeyPairCompressedBytes.pk1 k = ok hdrA)
    (h_pk2 : KeyPairCompressedBytes.pk2 k = ok ekA)
    (h_sk : KeyPairCompressedBytes.sk k = ok dkA)
    (h_hdr : hdrS.val = hdrA.val)
    (h_enc1 : encapsulate1 hdrS rand st ss = ok (.Ok ct1, st', ss'))
    (h_st : stA.val = st'.val)
    (h_enc2 : encapsulate2 stA ekA = ok ct2) :
    decapsulate_compressed_key dkA ct1 ct2 ⦃ ssA => ssA.val = ss'.val ⦄

end libcrux_ml_kem.mlkem768.incremental
