/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Oliver Butterley
-/
import SrcTranslated.Funs
import Spqr.Auxiliary.Aeneas.Scalar
import Spqr.Crypto.RFC5869

/-!
# HKDF-SHA256

Definitions, not spec theorems: `RFC5869` formalises HKDF over `UInt8`, and this file instantiates
it at SHA-256 and re-expresses it over Aeneas bytes, so that specs can refer to `hkdf` directly.

- `HMAC_SHA256` is the one assumed primitive: an opaque 32-octet tag.
- `SHA256` packages it as an RFC 5869 hash parameter.
- `hkdf` is RFC 5869 §2 at SHA-256, over Aeneas byte lists.
-/

-- TODO: this should be specific for this use case or upstreamed.
private instance List.instInhabitedSubtypeEqNatLength (ty : Type) [Inhabited ty] (n : ℕ) :
    Inhabited { l : List ty // l.length = n } :=
  ⟨List.replicate n (default : ty), List.length_replicate⟩

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace crypto

/-- HMAC-SHA256: a 32-octet authentication tag. -/
opaque HMAC_SHA256 (key data : List UInt8) : { l : List UInt8 // l.length = 32 }

/-- SHA-256 as an RFC 5869 hash parameter: `HashLen = 32`. -/
def SHA256 : HKDF.HashFunction where
  HashLen := 32
  HashLen_pos := by omega
  HMAC key data := (HMAC_SHA256 key data).val
  HMAC_length key data := (HMAC_SHA256 key data).property

/-- HKDF-SHA256 with an explicit salt: `L` octets of output keying material derived from `salt`,
`IKM` and `info`. -/
def hkdf (salt IKM info : List U8) (L : Nat) : List U8 :=
  (HKDF.ExtractAndExpand SHA256 (some (salt.map U8.toUInt8)) (IKM.map U8.toUInt8)
    (info.map U8.toUInt8) L).map U8.ofUInt8

/-- HKDF emits exactly `L` octets. -/
@[simp, scalar_tac_simps, grind =]
theorem hkdf_length (salt IKM info : List U8) (L : Nat) : (hkdf salt IKM info L).length = L := by
  simp [hkdf, HKDF.ExtractAndExpand_length]

end crypto
