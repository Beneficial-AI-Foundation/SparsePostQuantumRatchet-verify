/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import SrcTranslated.Funs
public import Spqr.Specs.IncrementalMlkem768.Encaps1
public import Spqr.Specs.Authenticator.Authenticator.Update
public import Spqr.Crypto.Hkdf
import Spqr.Specs.Kdf.HkdfToVec
import Spqr.Specs.Aeneas.SliceConcat
import Spqr.Specs.Aeneas.VecClone
import Spqr.Auxiliary.Aeneas.Vec
/-!
# Spec theorem for `spqr::v1::unchunked::send_ct::{HeaderReceived}::send_ct1`

`send_ct1` is the sender-side step of the SPQR ratchet in which, having received the peer's
64-byte ML-KEM-768 header `hdr = ρ ‖ H(ek)`, the sender produces the first ciphertext half and
derives the epoch secret.  Consuming the `HeaderReceived` state `{epoch, auth, hdr}` it:

  1. runs round 1 of incremental ML-KEM-768 encapsulation, `encaps1(hdr, rng)`, obtaining the
     960-byte first ciphertext half `ct1`, the 2080-byte serialised encapsulation state `es`
     (consumed later by `encaps2`) and the 32-byte raw shared secret `K`;
  2. builds the domain-separation string
       `info = b"Signal_PQCKA_V1_MLKEM768:SCKA Key" ‖ epoch.to_be_bytes()`
     and derives the 32-byte epoch secret
       `secret = HKDF-SHA256(salt = 0³², ikm = K, info, L = 32)`;
  3. ratchets the authenticator with `auth.update(epoch, &secret)`;
  4. returns the successor state `Ct1Sent {epoch, auth, hdr, es, ct1}`, a copy of `ct1` to be
     transmitted, and `EpochSecret {secret, epoch}`.

The hax contract on the Rust function is `requires(self.hdr.len() == 64)` and
`ensures(|(_, ct1, _)| ct1.len() == 960)`.  The spec below strengthens the postcondition to the
full FIPS 203 / HKDF value semantics inherited from `encaps1_spec`, `hkdf_to_vec_spec` and
`update_spec`.

**Source**: spqr/src/v1/unchunked/send_ct.rs (lines 120:4-148:5)
-/

@[expose] public section

open Aeneas Aeneas.Std Result spqr crypto

/- Helper definitions live in a CamelCase namespace (mirroring `Spqr.IncrementalMlkem768` in
`Encaps2.lean`) so that their full names satisfy the `defsWithUnderscore` linter; the spec
theorem itself stays in the Rust-mirroring `spqr.v1.unchunked.send_ct.HeaderReceived` namespace. -/
namespace Spqr.V1.Unchunked.SendCt

/-- The 33-byte domain-separation label `b"Signal_PQCKA_V1_MLKEM768:SCKA Key"` used as the HKDF
info prefix when deriving the epoch secret in `send_ct1` (and, symmetrically, in `recv_ct1`). -/
def sckaKeyLabel : List U8 :=
  [83#u8, 105#u8, 103#u8, 110#u8, 97#u8, 108#u8, 95#u8, 80#u8, 81#u8,
   67#u8, 75#u8, 65#u8, 95#u8, 86#u8, 49#u8, 95#u8, 77#u8, 76#u8, 75#u8,
   69#u8, 77#u8, 55#u8, 54#u8, 56#u8, 58#u8, 83#u8, 67#u8, 75#u8, 65#u8,
   32#u8, 75#u8, 101#u8, 121#u8]

@[simp, grind =]
theorem sckaKeyLabel_length : sckaKeyLabel.length = 33 := by rfl

end Spqr.V1.Unchunked.SendCt

namespace spqr.v1.unchunked.send_ct.HeaderReceived

open Spqr.V1.Unchunked.SendCt

open List core.num.U64 in
/-- **Spec theorem for `spqr.v1.unchunked.send_ct.HeaderReceived.send_ct1`**:

• Takes the `HeaderReceived` state `self = {epoch, auth, hdr}` and a CSPRNG `rng`; the Rust
  `&mut R` is threaded through the result after Aeneas extraction.
• Requires the hax precondition `self.hdr.len() == 64`, that `fill_bytes` of the RNG is
  panic-free, and that `self.auth.root_key ‖ secret` (32 more bytes) fits in memory.

The function always succeeds and returns `((st, ct1, es), rng')` where:

• **Successor state `st : Ct1Sent`** — `epoch` and `hdr` are carried over unchanged and
  `st.ct1 = ct1` (the clone of a byte vector is the vector itself).
• **Ciphertext `ct1`** — has length `960` (the hax `ensures`).  Together with `st.es` and the
  epoch secret it is pinned to FIPS 203 Algorithm 17 round 1: there is a 32-byte message `m`
  such that, with `(K, c₁, (ŷ, e₂, m)) = mlkemEncapsPhase1 (ρ, h) m`
  for `(ρ, h) = (hdr[0:32], hdr[32:64])`,
    `ct1.val   = ct1List hdr m`                       (serialised `c₁`),
    `st.es.val = toU8List (stateOut hdr m)`           (serialised `ŷ ‖ e₂ ‖ m`, 2080 bytes),
    `es.secret.val =
       hkdf 0³² (toU8List (ssOut hdr m)) (sckaKeyLabel ++ to_be_bytes epoch) 32`.
• **Epoch secret `es`** — `es.epoch = self.epoch` and `es.secret` has length `32`.
• **Authenticator** — ratcheted exactly as `update_spec` describes: both keys are 32 bytes and
    `st.auth.root_key ‖ st.auth.mac_key =
       hkdf 0³² (self.auth.root_key ‖ es.secret) (updateLabel ++ to_be_bytes epoch) 64`.

The proof unfolds `send_ct1`, applies `encaps1_spec` by hand (it is not `@[step]`-registered
because of its `h_fill` hypothesis) and discharges the remaining chain of calls with `step*`.

**Source**: spqr/src/v1/unchunked/send_ct.rs (lines 120:4-148:5)
-/
@[step]
theorem send_ct1_spec {R : Type} (rngInst : rand_1.rng.Rng R)
    (cryptoInst : rand_core_1.CryptoRng R) (self : HeaderReceived) (rng : R)
    (h_hdr : self.hdr.length = 64)
    (h_fill : ∀ (r : R) (s : Slice U8),
      rngInst.rand_core_1RngCoreInst.fill_bytes r s ⦃ fun _ => True ⦄)
    (h_root : self.auth.root_key.length + 32 ≤ Usize.max) :
    send_ct1 rngInst cryptoInst self rng ⦃
      (result : (Ct1Sent × (alloc.vec.Vec U8) × EpochSecret) × R) =>
      let st := result.1.1
      let ct1 := result.1.2.1
      let es := result.1.2.2
      st.epoch = self.epoch ∧ st.hdr = self.hdr ∧ st.ct1 = ct1 ∧
      ct1.length = 960 ∧ st.es.length = Fips203.Refinement.encapsStateSize ∧
      es.epoch = self.epoch ∧ es.secret.length = 32 ∧
      (∃ m : Fin 32 → UInt8,
        ct1.val = Fips203.Refinement.ct1List self.hdr.val (by scalar_tac) m ∧
        st.es.val = Fips203.Refinement.toU8List (Fips203.Refinement.stateOut self.hdr.val
          (by scalar_tac) m) ∧
        es.secret.val = hkdf (replicate 32 0#u8)
          (Fips203.Refinement.toU8List (Fips203.Refinement.ssOut self.hdr.val (by scalar_tac) m))
          (sckaKeyLabel ++ to_be_bytes self.epoch) 32) ∧
      st.auth.root_key.length = 32 ∧ st.auth.mac_key.length = 32 ∧
      st.auth.root_key.val ++ st.auth.mac_key.val
        = hkdf (replicate 32 0#u8) (self.auth.root_key.val ++ es.secret.val)
          (authenticator.Authenticator.updateLabel ++ to_be_bytes self.epoch) 64 ⦄ := by
  unfold send_ct1
  have h_hdr' : 64 ≤ self.hdr.val.length := by scalar_tac
  step with incremental_mlkem768.encaps1_spec rngInst cryptoInst self.hdr rng h_hdr' h_fill
    as ⟨ct1, es, secret, rng1, m, h_ct1, h_es, h_ss, h_ct1_len, h_es_len, h_ss_len⟩
  step*
  · simp only [Array.val_to_slice, Array.make_val, map_cons, map_nil, flatten_cons, flatten_nil,
      append_nil, cons_append, nil_append, length_cons, Array.property, UScalar.ofNatCore_val_eq,
      Nat.reduceAdd]
    scalar_tac
  · refine ⟨v_post, h_ct1_len, h_es_len, secret1_post1, ⟨m, h_ct1, h_es, ?_⟩, auth_post,
      auth_post1, ?_⟩
    · rw [secret1_post, ← h_ss, alloc.vec.Vec.deref_val, alloc.vec.Vec.deref_val, info_post]
      simp [sckaKeyLabel]
    · simpa [alloc.vec.Vec.val] using auth_post2

end spqr.v1.unchunked.send_ct.HeaderReceived
