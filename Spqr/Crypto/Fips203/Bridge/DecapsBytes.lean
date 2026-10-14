/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module
public import Aeneas
public import Spqr.Auxiliary.Aeneas.Scalar
public import Spqr.Crypto.Fips203.KEM.Decaps
public import Spqr.Crypto.Fips203.Bridge.EncapsBytes
/-!
# FIPS 203 model of libcrux's incremental `decapsulate_compressed_key`

libcrux-ml-kem 0.0.7 (`src/mlkem.rs`, `mlkem768::incremental::decapsulate_compressed_key`) takes
the 2400-byte compressed key-pair buffer (the FIPS 203 decapsulation key
`dk = dkPKE ‖ ek ‖ H(ek) ‖ z`, see `Bridge/KeyPairBytes.lean`), the 960-byte first ciphertext
half `c₁` and the 128-byte second half `c₂` — all as fixed-size arrays, so there are no error
cases — reassembles the 1088-byte ciphertext `c = c₁ ‖ c₂` and runs `ML-KEM.Decaps_internal`
(FIPS 203 Algorithm 18, `Fips203.mlkemDecaps`): decrypt, re-derive `(K', r') = G(m' ‖ h)`,
re-encrypt, and return `K'` or the implicit-rejection key `J(z ‖ c)`.

This file states that model over Aeneas byte arrays, so that `SrcTranslated/FunsExternal.lean`
can use it as the definition of the external `decapsulate_compressed_key`.  It deliberately does
**not** import `SrcTranslated` (it is imported *by* it).

**Sources**: NIST FIPS 203, § 6.3 (Algorithm 18); libcrux-ml-kem 0.0.7, `src/mlkem.rs` lines
439–443 and `src/ind_cca/incremental.rs` (`decapsulate_compressed_key`).
-/

@[expose] public section

noncomputable section

open Aeneas Aeneas.Std

namespace Fips203.Bridge

/-! ## Reading the fixed-size inputs -/

/-- Read the 2400-byte Aeneas key-pair buffer as a `Fin dkSize → UInt8` decapsulation key. -/
def dkOfArray (dk : Array U8 2400#usize) : Fin mlkem768.dkSize → UInt8 :=
  fun i => (dk.val[i.val]'(by
    rw [Aeneas.Std.Array.length_eq]
    have := i.isLt
    simp only [ParamSet.dkSize, mlkem768_k] at this
    change i.val < 2400
    omega)).toUInt8

/-- On a generated key pair, reading the buffer back gives the FIPS 203 decapsulation key. -/
theorem dkOfArray_keyPairArray (seed : Fin 64 → UInt8) :
    dkOfArray (keyPairArray seed) = keyPairBytes seed := by
  funext i
  simp only [dkOfArray, keyPairArray, Aeneas.Std.Array.make_val, keyPairList]
  rw [toU8List_getElem, U8.toUInt8_ofUInt8]

/-- Reassemble the 1088-byte ciphertext `c = c₁ ‖ c₂` from the two fixed-size halves. -/
def ctOfParts (ct1 : Array U8 960#usize) (ct2 : Array U8 128#usize) :
    Fin mlkem768.ctSizeEnc → UInt8 :=
  fun i =>
    if h : i.val < ct1Size then
      (ct1.val[i.val]'(by
        rw [Aeneas.Std.Array.length_eq]
        simp only [ct1Size] at h
        change i.val < 960
        exact h)).toUInt8
    else
      (ct2.val[i.val - ct1Size]'(by
        rw [Aeneas.Std.Array.length_eq]
        have hi := i.isLt
        simp only [ParamSet.ctSizeEnc, mlkem768CompressionU, mlkem768CompressionV, mlkem768_k] at hi
        simp only [ct1Size] at h
        change i.val - 960 < 128
        omega)).toUInt8

/-! ## The FIPS 203 model of `decapsulate_compressed_key` (ML-KEM-768) -/

/-- The 32-byte shared secret: `ML-KEM.Decaps_internal(dk, c₁ ‖ c₂)` (Algorithm 18). -/
def ssBytes (dk : Array U8 2400#usize) (ct1 : Array U8 960#usize) (ct2 : Array U8 128#usize) :
    Fin 32 → UInt8 :=
  mlkemDecaps mlkem768 (dkOfArray dk) (ctOfParts ct1 ct2)

/-- The shared secret as an Aeneas list. -/
def ssList (dk : Array U8 2400#usize) (ct1 : Array U8 960#usize) (ct2 : Array U8 128#usize) :
    List U8 :=
  toU8List (ssBytes dk ct1 ct2)

theorem ssList_length (dk : Array U8 2400#usize) (ct1 : Array U8 960#usize)
    (ct2 : Array U8 128#usize) : (ssList dk ct1 ct2).length = 32 := by
  simp only [ssList, toU8List_length]

/-- The shared secret as an Aeneas `Array U8 32`. -/
def ssArray (dk : Array U8 2400#usize) (ct1 : Array U8 960#usize) (ct2 : Array U8 128#usize) :
    Array U8 32#usize :=
  Aeneas.Std.Array.make 32#usize (ssList dk ct1 ct2) (ssList_length dk ct1 ct2)

end Fips203.Bridge
