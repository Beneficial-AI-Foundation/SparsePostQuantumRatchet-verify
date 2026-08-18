/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Oliver Butterley
-/
module

public section

/-! # RFC 5869: HMAC-based Extract-and-Expand Key Derivation Function (HKDF)

The construction here is faithful to the RFC and independent of any particular implementation.
Section numbers below refer to the RFC, and the names `salt`, `IKM`, `PRK`, `info`, `L`, `N`, `T`,
`OKM` and `HashLen` are used verbatim.

Reference: <https://datatracker.ietf.org/doc/html/rfc5869> -/

namespace HKDF

/-- The hash function for use with HMAC. -/
structure HashFunction where
  /-- The length of the hash function output in octets. -/
  HashLen : Nat
  /-- A hash function has non-empty output. -/
  HashLen_pos : 0 < HashLen
  /-- `HMAC-Hash(key, data)`. -/
  HMAC : List UInt8 → List UInt8 → List UInt8
  /-- HMAC-Hash emits exactly `HashLen` octets. -/
  HMAC_length : ∀ key data, (HMAC key data).length = HashLen

variable (H : HashFunction)

/-! ## §2.2 Step 1: Extract -/

/-- `HKDF-Extract(salt, IKM) -> PRK`, where `PRK = HMAC-Hash(salt, IKM)`.

* `salt` is an optional salt value (non-secret random value); defaults to a string of zeros.
* `IKM` is the input keying material.
* `PRK` is a pseudorandom key of `HashLen` octets. -/
def Extract (salt : Option (List UInt8)) (IKM : List UInt8) : List UInt8 :=
  H.HMAC (salt.getD (List.replicate H.HashLen 0)) IKM

/-- `PRK` has length `HashLen` octets. -/
theorem Extract_length (salt : Option (List UInt8)) (IKM : List UInt8) :
    (Extract H salt IKM).length = H.HashLen := H.HMAC_length _ _

/-! ## §2.3 Step 2: Expand -/

/-- The blocks of the output stream:
`T(0) = empty string (zero length)` and `T(i) = HMAC-Hash(PRK, T(i-1) | info | i)`, where the
constant concatenated to the end of each block is a single octet. -/
def T (PRK info : List UInt8) : Nat → List UInt8
  | 0     => []
  | i + 1 => H.HMAC PRK (T PRK info i ++ info ++ [UInt8.ofNat (i + 1)])

/-- Every block after `T(0)` is one hash output long. -/
theorem T_length (PRK info : List UInt8) (i : Nat) :
    (T H PRK info (i + 1)).length = H.HashLen := by simp [T, H.HMAC_length]

/-- `N = ceil(L/HashLen)`, the number of blocks needed to cover `L` octets. -/
def N (L : Nat) : Nat := (L + H.HashLen - 1) / H.HashLen

/-- `HKDF-Expand(PRK, info, L) -> OKM`, where `T = T(1) | T(2) | ... | T(N)` and `OKM` is the first
`L` octets of `T`.

* `PRK` is a pseudorandom key of at least `HashLen` octets.
* `info` is optional context and application specific information (can be zero-length).
* `L` is the length of the output keying material in octets, and must satisfy
  `L ≤ 255 * HashLen`. -/
def Expand (PRK info : List UInt8) (L : Nat) : List UInt8 :=
  ((List.range (N H L)).flatMap fun i => T H PRK info (i + 1)).take L

/-- `T(1) | ... | T(n)` is `n` hash outputs long. -/
theorem blocks_length (PRK info : List UInt8) (n : Nat) :
    ((List.range n).flatMap fun i => T H PRK info (i + 1)).length = H.HashLen * n := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, ih, T_length, Nat.mul_succ]

/-- `OKM` is `L` octets long. -/
theorem Expand_length (PRK info : List UInt8) (L : Nat) : (Expand H PRK info L).length = L := by
  have hpos := H.HashLen_pos
  have := Nat.div_add_mod (L + H.HashLen - 1) H.HashLen
  have := Nat.mod_lt (L + H.HashLen - 1) hpos
  simp only [Expand, List.length_take, blocks_length, N]
  grind

/-! ## §2 The composite construction -/

/-- HKDF: extract a pseudorandom key from `salt` and `IKM`, then expand it under `info` to `L`
octets of output keying material. -/
def ExtractAndExpand (salt : Option (List UInt8)) (IKM info : List UInt8) (L : Nat) : List UInt8 :=
  Expand H (Extract H salt IKM) info L

/-- `OKM` is `L` octets long. -/
theorem ExtractAndExpand_length (salt : Option (List UInt8)) (IKM info : List UInt8) (L : Nat) :
    (ExtractAndExpand H salt IKM info L).length = L := Expand_length ..

end HKDF
