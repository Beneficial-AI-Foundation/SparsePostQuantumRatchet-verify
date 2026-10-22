/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
module

public import SrcTranslated.Funs
public import Spqr.Specs.IncrementalMlkem768.Decaps
public import Spqr.Specs.Authenticator.Authenticator.Update
public import Spqr.Specs.Authenticator.Authenticator.VerifyCt
public import Spqr.Specs.V1.Unchunked.SendCt.HeaderReceived.SendCt1
public import Spqr.Crypto.Hkdf
import Spqr.Specs.Authenticator.Authenticator.MACSIZE
import Spqr.Specs.Kdf.HkdfToVec
import Spqr.Specs.Aeneas.SliceConcat
import Spqr.Specs.Aeneas.VecExtendFromSlice
import Spqr.Auxiliary.Aeneas.Vec
/-!
# Spec theorem for `spqr::v1::unchunked::send_ek::{EkSentCt1Received}::recv_ct2`

`EkSentCt1Received::recv_ct2` is the last step on the key-sending side of the unchunked V1
ratchet: having sent `ek` and received `ct1` (960 bytes), it receives the second half `ct2`
(128 bytes) and the 32-byte tag `mac` over `c₁ ‖ c₂`.  From the state `{epoch, auth, dk, ct1}`
it:

  1. decapsulates, `K = decaps(dk, ct1, ct2)` (FIPS 203 Alg. 18, implicit rejection included);
  2. derives `secret = HKDF-SHA256(0³², K, b"Signal_PQCKA_V1_MLKEM768:SCKA Key" ‖ epoch, 32)`,
     matching `HeaderReceived::send_ct1` on the peer side;
  3. ratchets `auth.update(epoch, &secret)` *before* checking the tag;
  4. extends `ct1` with `ct2` to the full 1088-byte ciphertext;
  5. runs `auth.verify_ct(epoch, &ct1, &mac)?`, i.e. compares `mac` in constant time with
     `HMAC-SHA256(auth.mac_key, MAC_CT_LABEL ‖ epoch ‖ c₁ ‖ c₂)[0..32]`;
  6. on success returns `send_ct::NoHeaderReceived {epoch + 1, auth}` (roles swap) and
     `EpochSecret {secret, epoch}`; on failure `?` yields `Err(Error::MacVerifyFailed)`.

The hax contract is `requires(ct2.len() == CIPHERTEXT2_SIZE && mac.len() == MACSIZE)` plus
`assume!(epoch < u64::MAX)`; the lengths of `dk` (2400) and `ct1` (960) are the struct's
`#[hax_lib::refine]` invariants.  The spec assumes exactly these, plus the memory-boundedness
hypothesis of `update`, and inherits the value semantics of `decaps_spec`, `hkdf_to_vec_spec`,
`update_spec`, `extend_from_slice_U8_spec` and `verify_ct_spec`, characterising `Ok`/`Err`
exactly.

**Source**: spqr/src/v1/unchunked/send_ek.rs (lines 139:4-172:5)
-/

@[expose] public section

open Aeneas Aeneas.Std Result spqr crypto

/- Helper definitions live in a CamelCase namespace (mirroring `Spqr.V1.Unchunked.SendCt` in
`SendCt1.lean`) so that their full names satisfy the `defsWithUnderscore` linter; the spec
theorems themselves stay in the Rust-mirroring `spqr.v1.unchunked.send_ek.EkSentCt1Received`
namespace. -/
namespace Spqr.V1.Unchunked.SendEk.EkSentCt1Received

open spqr spqr.v1.unchunked spqr.v1.unchunked.send_ek

open List core.num.U64 in
/-- The 32-byte epoch secret `hkdf 0³² ss (sckaKeyLabel ++ epoch.to_be_bytes()) 32` derived by
`recv_ct2` from the raw shared secret `ss`; same derivation as `HeaderReceived::send_ct1`. -/
def epochSecretOf (epoch : U64) (ss : List U8) : List U8 :=
  hkdf (replicate 32 0#u8) ss (Spqr.V1.Unchunked.SendCt.sckaKeyLabel ++ to_be_bytes epoch) 32

@[simp, grind =]
theorem epochSecretOf_length (epoch : U64) (ss : List U8) :
    (epochSecretOf epoch ss).length = 32 := by
  simp [epochSecretOf]

/-- `recv_ct2` accepts the complete ciphertext `ct` (= `c₁ ‖ c₂`) with tag `mac` under the
*ratcheted* authenticator `auth` iff `mac_ct auth epoch ct` equals `mac`, i.e. iff
`verify_ct auth epoch ct mac` returns `Ok ()` (see `verify_ct_spec`). -/
def ctAccepted (auth : authenticator.Authenticator) (epoch : U64)
    (ct : List U8) (mac : alloc.vec.Vec U8) : Prop :=
  ∃ s : Slice U8, s.val = ct ∧ authenticator.Authenticator.mac_ct auth epoch s = ok mac

open List core.num.U64 in
/-- Outcome of `EkSentCt1Received::recv_ct2`, given the ratcheted authenticator `auth'` and the
epoch `secret`:

  - **`Ok (st, es)`** iff `ctAccepted auth' self.epoch (self.ct1 ++ ct2) mac`, with
    `st.epoch = self.epoch + 1`, `st.auth = auth'`, `es.epoch = self.epoch`, `es.secret = secret`;
  - **`Err e`** iff `¬ ctAccepted ...`, and then `e = MacVerifyFailed`. -/
def recvCt2Outcome (self : EkSentCt1Received) (ct2 mac : alloc.vec.Vec U8)
    (auth' : authenticator.Authenticator) (secret : List U8)
    (result : core.result.Result (send_ct.NoHeaderReceived × EpochSecret) spqr.Error) : Prop :=
  match result with
  | core.result.Result.Ok (st, es) =>
      ctAccepted auth' self.epoch (self.ct1.val ++ ct2.val) mac ∧
      st.epoch.val = self.epoch.val + 1 ∧ st.auth = auth' ∧
      es.epoch = self.epoch ∧ es.secret.val = secret
  | core.result.Result.Err e =>
      ¬ ctAccepted auth' self.epoch (self.ct1.val ++ ct2.val) mac ∧ e = spqr.Error.MacVerifyFailed

open List core.num.U64 in
/-- Postcondition of `EkSentCt1Received::recv_ct2`: there are fixed-size arrays `dk'`, `ct1'`,
`ct2'` holding the input bytes (as in `decaps_spec`) and a ratcheted authenticator `auth'` with
keys from `hkdf 0³² (self.auth.root_key ‖ secret) (updateLabel ‖ epoch) 64` (as in
`update_spec`), where `secret = epochSecretOf self.epoch (ssList dk' ct1' ct2')`, such that
`recvCt2Outcome` holds. -/
def recvCt2Post (self : EkSentCt1Received) (ct2 mac : alloc.vec.Vec U8)
    (result : core.result.Result (send_ct.NoHeaderReceived × EpochSecret) spqr.Error) : Prop :=
  ∃ (dk' : Array U8 2400#usize) (ct1' : Array U8 960#usize) (ct2' : Array U8 128#usize)
    (auth' : authenticator.Authenticator),
    dk'.val = self.dk.val ∧ ct1'.val = self.ct1.val ∧ ct2'.val = ct2.val ∧
    auth'.root_key.length = 32 ∧ auth'.mac_key.length = 32 ∧
    auth'.root_key.val ++ auth'.mac_key.val
      = hkdf (replicate 32 0#u8)
          (self.auth.root_key.val ++
            epochSecretOf self.epoch (Fips203.Refinement.ssList dk' ct1' ct2'))
          (authenticator.Authenticator.updateLabel ++ to_be_bytes self.epoch) 64 ∧
    recvCt2Outcome self ct2 mac auth'
      (epochSecretOf self.epoch (Fips203.Refinement.ssList dk' ct1' ct2')) result

end Spqr.V1.Unchunked.SendEk.EkSentCt1Received

namespace spqr.v1.unchunked.send_ek.EkSentCt1Received

open Spqr.V1.Unchunked.SendEk.EkSentCt1Received

open List core.num.U64 in
/-- **Spec theorem for `spqr.v1.unchunked.send_ek.EkSentCt1Received.recv_ct2`**:

• `decaps self.dk self.ct1 ct2` gives `ss.val = ssList dk' ct1' ct2'` (`decaps_spec`).
• `Slice.concat` of the label with `epoch.to_be_bytes()` and `hkdf_to_vec` give
  `ss1.val = epochSecretOf self.epoch ss.val` (`hkdf_to_vec_spec`).
• `auth ← update self.auth self.epoch ss1` (`update_spec`).
• `extend_from_slice` builds `self.ct1 ++ ct2`, then `verify_ct auth self.epoch ct1 mac`
  returns `r` with `r = Ok () ↔ mac_ct auth self.epoch ct1 = ok mac` (`verify_ct_spec`).
• If `r = Ok ()`: returns `Ok ({ epoch := self.epoch + 1, auth }, { epoch := self.epoch,
  secret })`; otherwise `Err Error.MacVerifyFailed`.

• Requires `ct2.length = 128 ∧ mac.length = MACSIZE` (hax precondition), `self.dk.length = 2400
  ∧ self.ct1.length = 960` (struct refinements), `self.epoch < u64::MAX` (hax `assume!`) and
  that `self.auth.root_key ‖ secret` fits in memory.  Under these the call never panics and the
  branch is decided by `ctAccepted auth' self.epoch (self.ct1 ++ ct2) mac`.

The result satisfies `recvCt2Post self ct2 mac result`: for some `dk'`, `ct1'`, `ct2'`, `auth'`
and `secret = epochSecretOf self.epoch (ssList dk' ct1' ct2')`,

  `result = Ok (st, es) →  ctAccepted auth' self.epoch (self.ct1 ++ ct2) mac ∧
                            st.epoch = self.epoch + 1 ∧ st.auth = auth' ∧
                            es.epoch = self.epoch ∧ es.secret = secret`
  `result = Err e       →  ¬ ctAccepted auth' self.epoch (self.ct1 ++ ct2) mac ∧
                            e = Error.MacVerifyFailed`

Proof: unfold, apply `decaps_spec` by hand, let `step*` discharge the remaining calls, then
close the two `?` arms by cases on `r` using the `↔` forwards (`Ok`) and contrapositively
(`Err`).

**Source**: spqr/src/v1/unchunked/send_ek.rs (lines 139:4-172:5)
-/
@[step]
theorem recv_ct2_spec (self : EkSentCt1Received) (ct2 mac : alloc.vec.Vec U8)
    (h_dk : self.dk.length = 2400)
    (h_ct1 : self.ct1.length = 960)
    (h_ct2 : ct2.length = 128)
    (h_mac : mac.length = authenticator.Authenticator.MACSIZE.val)
    (h_epoch : self.epoch < U64.max)
    (h_root : self.auth.root_key.length + 32 ≤ Usize.max) :
    recv_ct2 self ct2 mac ⦃
      (result : core.result.Result (send_ct.NoHeaderReceived × EpochSecret) Error) =>
      recvCt2Post self ct2 mac result ⦄ := by
  unfold recv_ct2
  step with incremental_mlkem768.decaps_spec self.dk self.ct1 ct2 h_dk h_ct1 h_ct2
    as ⟨ss, dk', ct1', ct2', h_dk', h_ct1', h_ct2', h_ss, h_ss_len⟩
  have h_mac_vec : ({ slice := mac.deref } : alloc.vec.Vec U8) = mac :=
    alloc.vec.Vec.ext _ _ (alloc.vec.Vec.deref_val mac)
  step*
  · -- `Slice.concat`: the 41-byte `info` fits in memory.
    simp only [Array.val_to_slice, Array.make_val, map_cons, map_nil, flatten_cons, flatten_nil,
      append_nil, cons_append, nil_append, length_cons, Array.property, UScalar.ofNatCore_val_eq,
      Nat.reduceAdd]
    scalar_tac
  · -- `verify_ct`: the 1088-byte complete ciphertext plus the 43-byte HMAC header fits in `u32`.
    simp only [Slice.length, alloc.vec.Vec.deref_val, ct1_post, List.length_append]
    scalar_tac
  -- In both arms, the derived `ss1` is the epoch secret `epochSecretOf self.epoch ss`.
  all_goals
    have h_secret :
        ss1.val = epochSecretOf self.epoch (Fips203.Refinement.ssList dk' ct1' ct2') := by
      rw [ss1_post, alloc.vec.Vec.deref_val, alloc.vec.Vec.deref_val, h_ss, info_post]
      simp [epochSecretOf, Spqr.V1.Unchunked.SendCt.sckaKeyLabel]
  · -- `Ok` arm of `?`: `verify_ct` accepted.
    refine ⟨dk', ct1', ct2', auth, h_dk', h_ct1', h_ct2', auth_post, auth_post1, ?_, ?_⟩
    · simpa [alloc.vec.Vec.deref_val, h_secret] using auth_post2
    · refine ⟨⟨ct1.deref, by simp [ct1_post], ?_⟩, i_post, rfl, rfl, ?_⟩
      · rcases r with _ | e
        · simpa [h_mac_vec] using r_post.mp rfl
        · simp at cf_post; simp [cf_post] at *
      · rw [← h_secret, alloc.vec.Vec.val, ← v_post, alloc.vec.Vec.deref_val]
  · -- `Err` arm of `?`: `verify_ct` rejected, the error is mapped to `MacVerifyFailed`.
    subst result_post1
    simp only [Error.Insts.CoreConvertFromError.from, ok.injEq] at result_post
    subst result_post
    refine ⟨dk', ct1', ct2', auth, h_dk', h_ct1', h_ct2', auth_post, auth_post1, ?_, ?_⟩
    · simpa [alloc.vec.Vec.deref_val, h_secret] using auth_post2
    · refine ⟨fun h => ?_, rfl⟩
      obtain ⟨s, h_s, h_mac_ct⟩ := h
      have h_s' : s = ct1.deref := Slice.ext _ _ (by simp [h_s, ct1_post])
      rcases r with _ | e'
      · simp at cf_post; simp [cf_post] at *
      · have := r_post.mpr (by rw [← h_s', h_mac_ct, h_mac_vec])
        simp at this

/-- **Spec theorem for `spqr.v1.unchunked.send_ek.EkSentCt1Received.recv_ct2`** (shape of the
result):

Either `Err Error.MacVerifyFailed`, or `Ok (st, es)` with `st.epoch = self.epoch + 1`,
`es.epoch = self.epoch` and a 32-byte `es.secret`.  Projection of `recv_ct2_spec`.

**Source**: spqr/src/v1/unchunked/send_ek.rs (lines 139:4-172:5)
-/
theorem recv_ct2_spec_shape (self : EkSentCt1Received) (ct2 mac : alloc.vec.Vec U8)
    (h_dk : self.dk.length = 2400)
    (h_ct1 : self.ct1.length = 960)
    (h_ct2 : ct2.length = 128)
    (h_mac : mac.length = authenticator.Authenticator.MACSIZE.val)
    (h_epoch : self.epoch < U64.max)
    (h_root : self.auth.root_key.length + 32 ≤ Usize.max) :
    recv_ct2 self ct2 mac ⦃
      (result : core.result.Result (send_ct.NoHeaderReceived × EpochSecret) Error) =>
      result = core.result.Result.Err Error.MacVerifyFailed ∨
      ∃ st es, result = core.result.Result.Ok (st, es) ∧
        st.epoch.val = self.epoch.val + 1 ∧ es.epoch = self.epoch ∧
        es.secret.length = 32 ⦄ := by
  apply WP.spec_mono (recv_ct2_spec self ct2 mac h_dk h_ct1 h_ct2 h_mac h_epoch h_root)
  intro result h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, h_out⟩ := h
  cases result with
  | Ok p =>
    obtain ⟨st, es⟩ := p
    obtain ⟨_, h1, _, h2, h3⟩ := h_out
    exact Or.inr ⟨st, es, rfl, h1, h2, by simp [alloc.vec.Vec.length, h3]⟩
  | Err e => exact Or.inl (by rw [h_out.2])

end spqr.v1.unchunked.send_ek.EkSentCt1Received
