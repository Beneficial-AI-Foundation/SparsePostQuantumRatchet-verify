/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Lacramioara Astefanoaei
-/
module

public import SrcTranslated.Funs
public meta import Spqr.Auxiliary.SpecTags
public import SrcTranslated.FunsExternal
public import Spqr.Crypto.Hkdf
public import Spqr.Specs.Authenticator.Authenticator.Update
public import Spqr.Specs.V1.Unchunked.SendCt.HeaderReceived.SendCt1
public import Spqr.Specs.Braid.StateMachine.Model
public import Spqr.Specs.Braid.StateMachine.Relation
public import Spqr.Specs.Braid.StateMachine.Run
import Spqr.Specs.Aeneas.SliceConcat
import Spqr.Auxiliary.Aeneas.SpecImpExists
import Spqr.Auxiliary.Aeneas.Result
import Spqr.Specs.Kdf.HkdfToVec
public import Spqr.Specs.Braid.StateMachine.EpochDispatch
import Spqr.Specs.Aeneas.VecClone
import Spqr.Specs.Aeneas.VecExtendFromSlice
import Spqr.Specs.Aeneas.VecAppend
import Spqr.Specs.Aeneas.VecAsSlice
import Spqr.Specs.Aeneas.SliceListToVec
import Spqr.Specs.Aeneas.SliceConcatListAux
import Spqr.Specs.Aeneas.ResultExpect
import Spqr.Auxiliary.Aeneas.Slice
import Spqr.Auxiliary.Aeneas.Scalar
import Spqr.Specs.Authenticator.Authenticator.New
import Spqr.Specs.Encoding.Polynomial.PolyDecoder.New
import Spqr.Specs.Encoding.Polynomial.PolyDecoder.AddChunk
import Spqr.Specs.Encoding.Polynomial.PolyDecoder.DecodedMessage.Length
import Spqr.Specs.IncrementalMlkem768.HEADER_SIZE
import Spqr.Specs.IncrementalMlkem768.CIPHERTEXT1_SIZE
import Spqr.Specs.IncrementalMlkem768.CIPHERTEXT2_SIZE
import Spqr.Specs.Authenticator.Authenticator.MACSIZE
import Spqr.Specs.Authenticator.Authenticator.VerifyHdr
import Spqr.Specs.Authenticator.Authenticator.VerifyCt
import Spqr.Specs.Authenticator.Authenticator.MacHdr
import Spqr.Specs.Authenticator.Authenticator.MacCt
import Spqr.Auxiliary.Aeneas.Vec

/-! # The chunked `States` machine refines the abstract ML-KEM Braid machine

Every successful `States::send` or `States::recv` of the code is a step of `Braid`, the machine
of [ML-KEM Braid] §2.5 and §2.6 in `Model.lean`, with the same message and the same key.

## What to read

The proofs are checked by Lean. A reviewer reads only what the theorems are stated with:

1. `Model.lean`: the machine. It must match §2.5 and §2.6, and the deviations in
   `Deviations.lean`.
2. `Relation.lean`: `CodeAgrees`, `absMsg`, `absKey` and `Refines`, which relate the code to
   the machine.
3. `Run.lean`: `Step` and `Run`, the successful calls and runs of the code.
4. The statements of `init_refines` and `run_refines` below. Together they say that every run
   of the code from `init_a` or `init_b` is a run of the machine from `InitAlice` or `InitBob`
   with the same keys.

`send_refines` and `recv_refines` are the one-step results that `run_refines` uses. Every other
declaration of this module is a proof step.

## Results

Assume `CodeAgrees P`. Then:

* `init_refines`: the states that `init_a` and `init_b` return refine `InitAlice` and `InitBob`;
* `send_refines`: if `Refines s σ` and `States::send` succeeds on `s`, then for some randomness
  the machine's `Send()` on `σ` returns a related state, the same message and the same key;
* `recv_refines`: if `Refines s σ` and `States::recv` succeeds on `s`, then the machine's
  `Receive()` on `σ` succeeds with a related state and the same key;
* `run_refines`: if `Refines s σ`, then every run of the code from `s` is a run of the machine
  from `σ` with a related end state and the same keys.

`codeAgrees_exists` states that some `P` satisfies `CodeAgrees P`. It does not show that a
related state with a successful call exists. Its `KeyGen` and `Encaps1` do not satisfy a KEM
correctness law.

`recv_refines` uses the ciphertext sizes 960 and 128 (`CIPHERTEXT1_SIZE_eq`,
`CIPHERTEXT2_SIZE_eq`). They hold because `Ciphertext1::len` and `Ciphertext2::len` are
definitions in `SrcTranslated/FunsExternal.lean`, written by hand from libcrux-ml-kem 0.0.10
`src/ind_cca/incremental/types.rs:161,174`.

The results cover successful code steps only. They say nothing about calls that the code
rejects, about progress, or about agreement between the two parties. The machine uses the code's
`KDF_AUTH` (salt `[0u8; 32]`, key `root_key ‖ update_key`) and the code's `PROTOCOL_INFO`
(`Signal_PQCKA_V1_MLKEM768`, with no MAC component), not the choices of §2.2. It also uses the
code's `ek` check, which hashes `ek_vector ‖ ek_seed` and checks lengths and the encoding, not
the check `SHA3-256(ek_seed || ek_vector) = hek` of §2.5.

**Source**: ML-KEM Braid Rev. 1, §1.2, §2.2–§2.6; spqr/src/v1/chunked/states.rs:56-533 -/

@[expose] public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP spqr

namespace spqr.v1.chunked.states

open core.result.Result.Insts.CoreOpsTry (continue_of_ok)
open core.result.Result (eq_Ok_of_expect_eq_ok)
open spqr.encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder
  (add_chunk_pts_needed new_pts_needed decoded_message_length)
open Braid

/-- Assume `CodeAgrees P`. If `Authenticator::new v ep` returns `a`, then `absAuth a` is the
model's `Authenticator.Init` on `ep` and `v`. -/
theorem absAuth_new (P : CodePrims) (hP : CodeAgrees P) (v : alloc.vec.Vec Std.U8)
    (ep : Std.U64) (a : authenticator.Authenticator)
    (h : authenticator.Authenticator.new v ep = ok a) :
    absAuth a = Auth.init P ep.val v.val := by
  simp only [authenticator.Authenticator.new, Result.bind_eq_ok] at h
  obtain ⟨z, hz, hu⟩ := h
  have hb := authenticator.Authenticator.length_le_of_update_ok hu
  obtain ⟨hr, -, hrm⟩ := post_of_ok (authenticator.Authenticator.update_spec _ _ _ hb) hu
  have hz' : z.val = List.replicate 32 0#u8 := by
    exact (post_of_ok (alloc.vec.from_elem_spec _ _ _ rfl) hz).1
  simp only [absAuth, Auth.init, Auth.update, hP.kdfAuth]
  simp only [alloc.vec.Vec.deref, hz', Slice.from_val] at hrm
  rw [← hrm]
  have hr' : (a.root_key.val).length = 32 := hr
  simp only [List.take_left' hr', List.drop_left' hr']

/-- Assume `CodeAgrees P`. Then the states that `init_a` and `init_b` return refine `InitAlice`
and `InitBob` of §2.6. -/
@[correctness_spec, braid_spec "§2.6"]
theorem init_refines (P : CodePrims) (hP : CodeAgrees P) (key : Slice Std.U8) :
    (∀ s, States.init_a key = ok s → Refines s (initAlice P key.val)) ∧
    (∀ s, States.init_b key = ok s → Refines s (initBob P key.val)) := by
  constructor
  · intro s h
    simp only [States.init_a, v1.chunked.send_ek.KeysUnsampled.new,
      v1.unchunked.send_ek.KeysUnsampled.new, Result.bind_eq_ok, Result.ok.injEq] at h
    obtain ⟨_, ⟨_, ⟨v, hv, a, ha, rfl⟩, rfl⟩, rfl⟩ := h
    refine ⟨rfl, ?_⟩
    rw [absAuth_new P hP v _ a ha, Slice.to_vec_U8_ok_val hv]; rfl
  · intro s h
    simp only [States.init_b, v1.chunked.send_ct.NoHeaderReceived.new,
      v1.unchunked.send_ct.NoHeaderReceived.new, Result.bind_eq_ok, Result.ok.injEq] at h
    obtain ⟨_, ⟨n, hn, i, hi, dr, hdr, _, ⟨v, hv, a, ha, rfl⟩, d, hd, rfl⟩, rfl⟩ := h
    have hdr' := eq_Ok_of_expect_eq_ok hd
    subst hdr'
    refine ⟨rfl, ?_, ?_⟩
    · rw [absAuth_new P hP v _ a ha, Slice.to_vec_U8_ok_val hv]; rfl
    · have hn' := post_of_ok incremental_mlkem768.HEADER_SIZE_spec hn
      have hhb : Spqr.Mlkem.headerBytes = 64 := by decide
      have hi' := UScalar.val_of_add_eq_ok hi
      rw [authenticator.Authenticator.MACSIZE_spec, hn', hhb] at hi'
      refine ⟨?_, ?_⟩
      · rw [hP.headerSize n hn, hP.macSize, ← UScalar.val_of_add_eq_ok hi, hP.decoderNew i d hdr]
      · refine ⟨authenticator.Authenticator.mac_key_length_of_new_ok ha, ?_⟩
        rw [new_pts_needed (by omega) hdr, hi']

/-- `pick p` is the value that satisfies `p` when there is one. -/
private noncomputable def pick {β : Type} [Nonempty β] (p : β → Prop) : β :=
  open Classical in if h : ∃ b, p b then Classical.choose h else Classical.choice inferInstance

/-- If `b` is the only value that satisfies `p`, then `pick p = b`. -/
private theorem pick_eq {β : Type} [Nonempty β] {p : β → Prop} {b : β} (hb : p b)
    (hu : ∀ b', p b' → b' = b) : pick p = b := by
  have h : ∃ b, p b := ⟨b, hb⟩
  simp only [pick, h, _root_.dite_true]
  exact hu _ (Classical.choose_spec h)

/-- A computation returns at most one value. -/
private theorem ok_unique {α : Type} {m : Result α} {a b : α} (ha : m = ok a) (hb : m = ok b) :
    b = a := by
  rw [ha, Result.ok.injEq] at hb; exact hb.symm

private instance : Nonempty encoding.polynomial.PolyEncoder :=
  ⟨⟨0#u32, .Polys (Array.repeat 16#usize
    ⟨alloc.vec.Vec.from [] (by simp only [List.length_nil, zero_le])⟩)⟩⟩

private instance : Nonempty encoding.polynomial.PolyDecoder :=
  ⟨⟨0#usize, Array.repeat 16#usize ⟨Slice.from [] (by simp only [List.length_nil, zero_le])⟩,
    false⟩⟩

private instance : Nonempty encoding.Chunk := ⟨⟨0#u16, Array.repeat 32#usize 0#u8⟩⟩

/-- Some `P` agrees with the code. -/
theorem codeAgrees_exists : ∃ P : CodePrims, CodeAgrees P := by
  have : Countable Std.U8 :=
    Function.Injective.countable (f := fun x : Std.U8 => x.val)
      (fun _ _ h => UScalar.eq_of_val_eq h)
  obtain ⟨f, hf⟩ := exists_surjective_nat (Bytes × Bytes × Bytes)
  have hsurj : ∀ t, ∃ r : Bytes, f r.length = t := fun t =>
    let ⟨n, hn⟩ := hf t; ⟨List.replicate n 0#u8, by simpa only [List.length_replicate] using hn⟩
  let P : CodePrims :=
    { encode := fun msg => pick fun e => ∃ s : Slice Std.U8, s.val = msg ∧
        encoding.polynomial.PolyEncoder.Insts.SpqrEncodingEncoder.encode_bytes s = ok (.Ok e)
      nextChunk := fun e => pick fun ce =>
        encoding.polynomial.PolyEncoder.Insts.SpqrEncodingEncoder.next_chunk e = ok ce
      decoderNew := fun n => pick fun d => ∃ u : Std.Usize, u.val = n ∧
        encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.new u = ok (.Ok d)
      addChunk := fun d c => pick fun d' =>
        encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk d c = ok d'
      message := fun d => pick fun o => ∃ m,
        encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.decoded_message d = ok m ∧
          o = m.map (·.val)
      keyGen := fun r => f r.length
      encaps1 := fun _ r => f r.length
      encaps2 := fun es _ ek => pick fun ct2 => ∃ ekv esv ct2v : alloc.vec.Vec Std.U8,
        ekv.val = ek ∧ esv.val = es ∧ incremental_mlkem768.encaps2 ekv esv = ok ct2v ∧
          ct2 = ct2v.val
      decaps := fun dk ct1 ct2 => pick fun ss => ∃ dkv ct1v ct2v ssv : alloc.vec.Vec Std.U8,
        dkv.val = dk ∧ ct1v.val = ct1 ∧ ct2v.val = ct2 ∧
          incremental_mlkem768.decaps dkv ct1v ct2v = ok ssv ∧ ss = ssv.val
      ekMatches := fun hdr ek => pick fun b => ∃ ekv hdrv : alloc.vec.Vec Std.U8,
        ekv.val = ek ∧ hdrv.val = hdr ∧ incremental_mlkem768.ek_matches_header ekv hdrv = ok b
      headerSize := pick fun m => ∃ n, incremental_mlkem768.HEADER_SIZE = ok n ∧ m = n.val
      ekSize := pick fun m => ∃ n, incremental_mlkem768.ENCAPSULATION_KEY_SIZE = ok n ∧ m = n.val
      ct1Size := pick fun m => ∃ n, incremental_mlkem768.CIPHERTEXT1_SIZE = ok n ∧ m = n.val
      ct2Size := pick fun m => ∃ n, incremental_mlkem768.CIPHERTEXT2_SIZE = ok n ∧ m = n.val
      macSize := authenticator.Authenticator.MACSIZE.val
      mac := fun k d => pick fun t => ∃ (ks ds : Slice Std.U8) (tv : alloc.vec.Vec Std.U8),
        ks.val = k ∧ ds.val = d ∧ libcrux_hmac.hmac .Sha256 ks ds (some 32#usize) = ok tv ∧
          t = tv.val
      protocolInfo := ascii "Signal_PQCKA_V1_MLKEM768"
      toBytes := fun n => pick fun l => ∃ ep : Std.U64, ep.val = n ∧
        l = (core.num.U64.to_be_bytes ep).val
      kdfAuth := fun rk k n => pick fun out => ∃ ep : Std.U64, ep.val = n ∧
        out = crypto.hkdf (List.replicate 32 0#u8) (rk ++ k)
          (authenticator.Authenticator.updateLabel ++ (core.num.U64.to_be_bytes ep).val) 64
      kdfOk := fun ss n => pick fun out => ∃ ep : Std.U64, ep.val = n ∧
        out = crypto.hkdf (List.replicate 32 0#u8) ss
          (Spqr.V1.Unchunked.SendCt.sckaKeyLabel ++ (core.num.U64.to_be_bytes ep).val) 32 }
  have hU64 : ∀ a b : Std.U64, a.val = b.val → a = b := fun _ _ h => UScalar.eq_of_val_eq h
  have hUs : ∀ a b : Std.Usize, a.val = b.val → a = b := fun _ _ h => UScalar.eq_of_val_eq h
  have hV : ∀ a b : alloc.vec.Vec Std.U8, a.val = b.val → a = b :=
    fun a b h => (alloc.vec.Vec.eq_iff a b).mpr h
  have hS : ∀ a b : Slice Std.U8, a.val = b.val → a = b := fun a b h => (Slice.eq_iff a b).mpr h
  refine ⟨P, ?_⟩
  constructor
  · intro msg e h
    refine pick_eq ⟨msg, rfl, h⟩ ?_
    rintro e' ⟨s', hs', h'⟩
    rw [hS s' msg hs'] at h'
    simpa only [core.result.Result.Ok.injEq] using ok_unique h h'
  · intro e e' c h
    exact pick_eq h fun _ h' => ok_unique h h'
  · intro n d h
    refine pick_eq ⟨n, rfl, h⟩ ?_
    rintro d' ⟨u, hu, h'⟩
    rw [hUs u n hu] at h'
    simpa only [core.result.Result.Ok.injEq] using ok_unique h h'
  · intro d d' c h
    exact pick_eq h fun _ h' => ok_unique h h'
  · intro d m h
    refine pick_eq ⟨m, h, rfl⟩ ?_
    rintro o ⟨m', h', rfl⟩
    rw [ok_unique h h']
  · intro R i₁ i₂ rng rng' k _
    exact hsurj _
  · intro R i₁ i₂ rng rng' hdr ct1 es ss _
    exact hsurj _
  · intro ek es ct2 hdr h
    refine pick_eq ⟨ek, es, ct2, rfl, rfl, h, rfl⟩ ?_
    rintro _ ⟨ekv, esv, ct2v, h1, h2, h', rfl⟩
    rw [hV ekv ek h1, hV esv es h2] at h'
    rw [ok_unique h h']
  · intro dk ct1 ct2 ss h
    refine pick_eq ⟨dk, ct1, ct2, ss, rfl, rfl, rfl, h, rfl⟩ ?_
    rintro _ ⟨dkv, ct1v, ct2v, ssv, h1, h2, h3, h', rfl⟩
    rw [hV dkv dk h1, hV ct1v ct1 h2, hV ct2v ct2 h3] at h'
    rw [ok_unique h h']
  · intro ek hdr b h
    refine pick_eq ⟨ek, hdr, rfl, rfl, h⟩ ?_
    rintro _ ⟨ekv, hdrv, h1, h2, h'⟩
    rw [hV ekv ek h1, hV hdrv hdr h2] at h'
    exact ok_unique h h'
  · intro n h
    exact pick_eq ⟨n, h, rfl⟩ fun _ ⟨n', h', e⟩ => by rw [e, ok_unique h h']
  · intro n h
    exact pick_eq ⟨n, h, rfl⟩ fun _ ⟨n', h', e⟩ => by rw [e, ok_unique h h']
  · intro n h
    exact pick_eq ⟨n, h, rfl⟩ fun _ ⟨n', h', e⟩ => by rw [e, ok_unique h h']
  · intro n h
    exact pick_eq ⟨n, h, rfl⟩ fun _ ⟨n', h', e⟩ => by rw [e, ok_unique h h']
  · rfl
  · intro key data t h
    refine pick_eq ⟨key, data, t, rfl, rfl, h, rfl⟩ ?_
    rintro _ ⟨ks, ds, tv, h1, h2, h', rfl⟩
    rw [hS ks key h1, hS ds data h2] at h'
    rw [ok_unique h h']
  · rfl
  · intro ep
    exact pick_eq ⟨ep, rfl, rfl⟩ fun _ ⟨ep', h1, e⟩ => by rw [e, hU64 ep' ep h1]
  · intro rk k ep
    exact pick_eq ⟨ep, rfl, rfl⟩ fun _ ⟨ep', h1, e⟩ => by rw [e, hU64 ep' ep h1]
  · intro ss ep
    exact pick_eq ⟨ep, rfl, rfl⟩ fun _ ⟨ep', h1, e⟩ => by rw [e, hU64 ep' ep h1]

/-- Assume `CodeAgrees P`. If `Authenticator::update a ep k` returns `a'`, then `absAuth a'` is
the model's `Authenticator.Update` of `absAuth a` on `ep` and `k`. -/
theorem absAuth_update (P : CodePrims) (hP : CodeAgrees P) (a a' : authenticator.Authenticator)
    (ep : Std.U64) (k : Slice Std.U8) (h : authenticator.Authenticator.update a ep k = ok a') :
    absAuth a' = Auth.update P (absAuth a) ep.val k.val := by
  have hb := authenticator.Authenticator.length_le_of_update_ok h
  obtain ⟨hr, -, hrm⟩ := post_of_ok (authenticator.Authenticator.update_spec _ _ _ hb) h
  simp only [absAuth, Auth.update, hP.kdfAuth, ← hrm]
  have hr' : (a'.root_key.val).length = 32 := hr
  simp only [List.take_left' hr', List.drop_left' hr']

/-- Assume `CodeAgrees P`. If `data` is `Signal_PQCKA_V1_MLKEM768 ‖ label ‖ ToBytes(ep) ‖ x` and
the code's HMAC-SHA256 of `data` under `key` returns `t`, then `t` is the model's `MAC` under
`key` of `PROTOCOL_INFO ‖ label ‖ ToBytes(ep) ‖ x`. -/
theorem hmac_ok (P : CodePrims) (hP : CodeAgrees P) (label : String) (key data : Slice Std.U8)
    (ep : Std.U64) (x : Bytes) (t : alloc.vec.Vec Std.U8)
    (hd : data.val = ascii "Signal_PQCKA_V1_MLKEM768" ++ ascii label ++
      (core.num.U64.to_be_bytes ep).val ++ x)
    (h : libcrux_hmac.hmac .Sha256 key data (some 32#usize) = ok t) :
    t.val = P.mac key.val (P.protocolInfo ++ ascii label ++ P.toBytes ep.val ++ x) := by
  rw [← hP.mac _ _ _ h, hd, hP.protocolInfo, hP.toBytes]

/-- Assume `CodeAgrees P`. If `mac_hdr a ep hdr` returns `m`, then `m` is the model's `MacHdr`
of `hdr` under `absAuth a` at epoch `ep`. -/
theorem mac_hdr_ok (P : CodePrims) (hP : CodeAgrees P) (a : authenticator.Authenticator)
    (ep : Std.U64) (hdr : Slice Std.U8) (m : alloc.vec.Vec Std.U8)
    (h : authenticator.Authenticator.mac_hdr a ep hdr = ok m) :
    m.val = Auth.macHdr P (absAuth a) ep.val hdr.val := by
  simp only [authenticator.Authenticator.mac_hdr, authenticator.Authenticator.MACSIZE,
    Result.bind_eq_ok] at h
  obtain ⟨_, h1, _, h2, _, h3, _, h4, d, hd, hm⟩ := h
  simp only [lift, Result.ok.injEq] at h1 h2 h3 h4
  subst h1 h2 h3 h4
  have hl : ascii "Signal_PQCKA_V1_MLKEM768" ++ ascii ":ekheader" =
      authenticator.Authenticator.MAC_HDR_LABEL := by decide
  rw [hmac_ok P hP ":ekheader" _ _ ep hdr.val m ?_ hm]
  · simp only [Auth.macHdr, absAuth, alloc.vec.Vec.deref_val]
  · rw [alloc.vec.Vec.deref_val, alloc.slice.Slice.concat_shared_id_ok_val _ (fun _ => rfl) hd, hl]
    simp only [Array.to_slice, Array.make, Array.from_val, Slice.from_val, List.map_cons,
        List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append,
        List.nil_append, authenticator.Authenticator.MAC_HDR_LABEL]

/-- Assume `CodeAgrees P`. If `mac_ct a ep ct` returns `m`, then `m` is the model's `MacCt` of
`ct` under `absAuth a` at epoch `ep`. -/
theorem mac_ct_ok (P : CodePrims) (hP : CodeAgrees P) (a : authenticator.Authenticator)
    (ep : Std.U64) (ct : Slice Std.U8) (m : alloc.vec.Vec Std.U8)
    (h : authenticator.Authenticator.mac_ct a ep ct = ok m) :
    m.val = Auth.macCt P (absAuth a) ep.val ct.val := by
  simp only [authenticator.Authenticator.mac_ct, authenticator.Authenticator.MACSIZE,
    Result.bind_eq_ok] at h
  obtain ⟨_, h1, _, h2, _, h3, _, h4, d, hd, hm⟩ := h
  simp only [lift, Result.ok.injEq] at h1 h2 h3 h4
  subst h1 h2 h3 h4
  have hl : ascii "Signal_PQCKA_V1_MLKEM768" ++ ascii ":ciphertext" =
      authenticator.Authenticator.MAC_CT_LABEL := by decide
  rw [hmac_ok P hP ":ciphertext" _ _ ep ct.val m ?_ hm]
  · simp only [Auth.macCt, absAuth, alloc.vec.Vec.deref_val]
  · rw [alloc.vec.Vec.deref_val, alloc.slice.Slice.concat_shared_id_ok_val _ (fun _ => rfl) hd, hl]
    simp only [Array.to_slice, Array.make, Array.from_val, Slice.from_val, List.map_cons,
        List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append,
        List.nil_append, authenticator.Authenticator.MAC_CT_LABEL]

/-- Assume `CodeAgrees P`. If `Ct1SentEkReceived::send_ct2 uc` returns `(u2, ct2, mac)` and
`send_ct2_encoder ct2 mac` returns `pe`, then `u2` has the epoch and the authenticator of `uc`,
and for every header `hdr`, `pe` is the model's `ct2Encoder` for `uc` and `hdr`. -/
theorem ct2_encoder_ok (P : CodePrims) (hP : CodeAgrees P)
    (uc : v1.unchunked.send_ct.Ct1SentEkReceived) (u2 : v1.unchunked.send_ct.Ct2Sent)
    (ct2 mac : alloc.vec.Vec Std.U8) (pe : encoding.polynomial.PolyEncoder) (hdr : Bytes)
    (h1 : v1.unchunked.send_ct.Ct1SentEkReceived.send_ct2 uc = ok (u2, ct2, mac))
    (h2 : send_ct.send_ct2_encoder ct2.deref mac.deref = ok pe) :
    u2 = ⟨uc.epoch, uc.auth⟩ ∧
      pe = ct2Encoder P uc.epoch.val (absAuth uc.auth) uc.es.val uc.ct1.val hdr uc.ek.val := by
  simp only [v1.unchunked.send_ct.Ct1SentEkReceived.send_ct2, Result.bind_eq_ok] at h1
  obtain ⟨c2, hc2, ct1', hct1, m, hm, h1⟩ := h1
  simp only [Result.ok.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl, rfl⟩ := h1
  refine ⟨rfl, ?_⟩
  simp only [send_ct.send_ct2_encoder, Result.bind_eq_ok] at h2
  obtain ⟨v, hv, v', hv', r, hr, h2⟩ := h2
  obtain rfl := eq_Ok_of_expect_eq_ok h2
  have he2 := hP.encaps2 _ _ _ hdr hc2
  have hmac := mac_ct_ok P hP _ _ _ _ hm
  have hct := alloc.vec.Vec.extend_from_slice_U8_ok_val hct1
  have hvv' := alloc.vec.Vec.extend_from_slice_U8_ok_val hv'
  have hen := hP.encode _ _ hr
  simp only [alloc.vec.Vec.deref, Slice.from_val] at hmac hct hvv' hen
  rw [hct] at hmac
  simp only [ct2Encoder, he2, ← hmac, ← hen, hvv']
  congr 1
  rw [Slice.to_vec_U8_ok_val hv]; simp only [alloc.vec.Vec.deref, Slice.from_val]

/-- Assume `CodeAgrees P`. If `EkReceivedCt1Sampled::recv_ct1_ack st ep` returns `st'`, then for
every header `hdr`, `st'` refines the model's `Ct2Sampled` state at the epoch and with the
authenticator of `st`, whose encoder is `ct2Encoder` for `st` and `hdr`. -/
theorem recv_ct1_ack_ok (P : CodePrims) (hP : CodeAgrees P) (st : send_ct.EkReceivedCt1Sampled)
    (ep : Std.U64) (st' : send_ct.Ct2Sampled) (hdr : Bytes)
    (h : send_ct.EkReceivedCt1Sampled.recv_ct1_ack st ep = ok st') :
    Refines (.Ct2Sampled st') (.ct2Sampled st.uc.epoch.val (absAuth st.uc.auth)
      (ct2Encoder P st.uc.epoch.val (absAuth st.uc.auth) st.uc.es.val st.uc.ct1.val hdr
        st.uc.ek.val)) := by
  simp only [send_ct.EkReceivedCt1Sampled.recv_ct1_ack, massert, Result.bind_eq_ok] at h
  obtain ⟨_, -, ⟨u2, ct2, mac⟩, h1, h⟩ := h
  simp only [uncurry_apply_pair, Result.bind_eq_ok] at h
  obtain ⟨pe, h2, h⟩ := h
  simp only [Result.ok.injEq] at h
  subst h
  obtain ⟨rfl, rfl⟩ := ct2_encoder_ok P hP _ _ _ _ _ hdr h1 h2
  simp only [Refines, and_self]

/-- Assume `CodeAgrees P` and `Refines s σ`. If `States::send` succeeds on `s`, then for some
randomness the model's `Send()` on `σ` gives a related state, the code's message and the code's
key. -/
@[correctness_spec, braid_spec "§2.5", braid_deviation Deviation.ct1AckAccepted]
theorem send_refines (P : CodePrims) (hP : CodeAgrees P) {R : Type} (i₁ : rand_1.rng.Rng R)
    (i₂ : rand_core_1.CryptoRng R) (s : States) (σ : State _ _) (h : Refines s σ) (rng rng' : R)
    (out : Send) (hs : States.send i₁ i₂ s rng = ok (.Ok out, rng')) :
    ∃ r, Refines out.state (Braid.send P σ r).1 ∧ absMsg out.msg = (Braid.send P σ r).2.1 ∧
      out.key.map absKey = (Braid.send P σ r).2.2 := by
  cases s <;> cases σ <;> simp only [Refines] at h <;> simp only [States.send,
    Result.bind_eq_ok, Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hs
  case KeysSampled.keysSampled s e a dk hdr ek enc =>
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
    obtain ⟨ep, hep, ⟨s1, c⟩, hc, hout⟩ := hs
    simp only [send_ek.KeysSampled.epoch, Result.ok.injEq] at hep; subst hep
    simp only [send_ek.KeysSampled.send_hdr_chunk, Result.bind_eq_ok] at hc
    obtain ⟨⟨c', e'⟩, hn, hc⟩ := hc
    simp only [uncurry_apply_pair, ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hc hout
    obtain ⟨rfl, rfl⟩ := hc
    obtain ⟨rfl, -⟩ := hout
    refine ⟨[], ?_⟩
    simp only [Refines, Braid.send, hP.nextChunk _ _ _ hn, and_self, absMsg, Option.map_none]
  case HeaderSent.headerSent s e a dk d enc =>
    obtain ⟨rfl, rfl, rfl, rfl, rfl, hp⟩ := h
    obtain ⟨ep, hep, ⟨s1, c⟩, hc, hout⟩ := hs
    simp only [send_ek.HeaderSent.epoch, Result.ok.injEq] at hep; subst hep
    simp only [send_ek.HeaderSent.send_ek_chunk, Result.bind_eq_ok] at hc
    obtain ⟨⟨c', e'⟩, hn, hc⟩ := hc
    simp only [uncurry_apply_pair, ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hc hout
    obtain ⟨rfl, rfl⟩ := hc
    obtain ⟨rfl, -⟩ := hout
    have hnc := hP.nextChunk _ _ _ hn
    refine ⟨[], ?_⟩
    simp only [Refines, Braid.send, hnc, hp, and_self, absMsg, Option.map_none]
  case Ct1Received.ct1Received s e a dk ct1 enc =>
    obtain ⟨rfl, rfl, rfl, rfl, rfl, hp⟩ := h
    obtain ⟨ep, hep, ⟨s1, c⟩, hc, hout⟩ := hs
    simp only [send_ek.Ct1Received.epoch, Result.ok.injEq] at hep; subst hep
    simp only [send_ek.Ct1Received.send_ek_chunk, Result.bind_eq_ok] at hc
    obtain ⟨⟨c', e'⟩, hn, hc⟩ := hc
    simp only [uncurry_apply_pair, ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hc hout
    obtain ⟨rfl, rfl⟩ := hc
    obtain ⟨rfl, -⟩ := hout
    have hnc := hP.nextChunk _ _ _ hn
    refine ⟨[], ?_⟩
    simp only [Refines, Braid.send, hnc, alloc.vec.Vec.length, hp, and_self, absMsg,
        Option.map_none]
  case Ct1Sampled.ct1Sampled s e a hdr es ct1 enc d =>
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
    obtain ⟨ep, hep, ⟨s1, c⟩, hc, hout⟩ := hs
    simp only [send_ct.Ct1Sampled.epoch, Result.ok.injEq] at hep; subst hep
    simp only [send_ct.Ct1Sampled.send_ct1_chunk, Result.bind_eq_ok] at hc
    obtain ⟨⟨c', e'⟩, hn, hc⟩ := hc
    simp only [uncurry_apply_pair, ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hc hout
    obtain ⟨rfl, rfl⟩ := hc
    obtain ⟨rfl, -⟩ := hout
    have hnc := hP.nextChunk _ _ _ hn
    refine ⟨[], ?_⟩
    simp only [Refines, Braid.send, hnc, and_self, absMsg, Option.map_none]
  case EkReceivedCt1Sampled.ekReceivedCt1Sampled s e a es ct1 hdr ek enc =>
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
    obtain ⟨ep, hep, ⟨s1, c⟩, hc, hout⟩ := hs
    simp only [send_ct.EkReceivedCt1Sampled.epoch, Result.ok.injEq] at hep; subst hep
    simp only [send_ct.EkReceivedCt1Sampled.send_ct1_chunk, Result.bind_eq_ok] at hc
    obtain ⟨⟨c', e'⟩, hn, hc⟩ := hc
    simp only [uncurry_apply_pair, ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hc hout
    obtain ⟨rfl, rfl⟩ := hc
    obtain ⟨rfl, -⟩ := hout
    have hnc := hP.nextChunk _ _ _ hn
    refine ⟨[], ?_⟩
    simp only [Refines, Braid.send, hnc, and_self, absMsg, Option.map_none]
  case Ct2Sampled.ct2Sampled s e a enc =>
    obtain ⟨rfl, rfl, rfl⟩ := h
    obtain ⟨ep, hep, ⟨s1, c⟩, hc, hout⟩ := hs
    simp only [send_ct.Ct2Sampled.epoch, Result.ok.injEq] at hep; subst hep
    simp only [send_ct.Ct2Sampled.send_ct2_chunk, Result.bind_eq_ok] at hc
    obtain ⟨⟨c', e'⟩, hn, hc⟩ := hc
    simp only [uncurry_apply_pair, ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hc hout
    obtain ⟨rfl, rfl⟩ := hc
    obtain ⟨rfl, -⟩ := hout
    have hnc := hP.nextChunk _ _ _ hn
    refine ⟨[], ?_⟩
    simp only [Refines, Braid.send, hnc, and_self, absMsg, Option.map_none]
  case EkSentCt1Received.ekSentCt1Received s e a dk ct1 d =>
    obtain ⟨rfl, rfl, rfl, rfl, rfl, hp⟩ := h
    obtain ⟨ep, hep, hout⟩ := hs
    simp only [send_ek.EkSentCt1Received.epoch, Result.ok.injEq] at hep; subst hep
    obtain ⟨rfl, -⟩ := hout
    refine ⟨[], ?_⟩
    simp only [Refines, Braid.send, alloc.vec.Vec.length, hp, and_self, absMsg, Option.map_none]
  case NoHeaderReceived.noHeaderReceived s e a d =>
    obtain ⟨rfl, rfl, rfl, hp⟩ := h
    obtain ⟨ep, hep, hout⟩ := hs
    simp only [send_ct.NoHeaderReceived.epoch, Result.ok.injEq] at hep; subst hep
    obtain ⟨rfl, -⟩ := hout
    refine ⟨[], ?_⟩
    simp only [Refines, Braid.send, alloc.vec.Vec.length, hp, and_self, absMsg, Option.map_none]
  case Ct1Acknowledged.ct1Acknowledged s e a hdr es ct1 d =>
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
    obtain ⟨ep, hep, hout⟩ := hs
    simp only [send_ct.Ct1Acknowledged.epoch, Result.ok.injEq] at hep; subst hep
    obtain ⟨rfl, -⟩ := hout
    refine ⟨[], ?_⟩
    simp only [Refines, Braid.send, and_self, absMsg, Option.map_none]
  case KeysUnsampled.keysUnsampled s e a =>
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨ep, hep, ⟨⟨s1, c⟩, rng1⟩, hc, hout⟩ := hs
    simp only [send_ek.KeysUnsampled.epoch, Result.ok.injEq] at hep; subst hep
    simp only [uncurry_apply_pair, ok.injEq, Prod.mk.injEq,
        core.result.Result.Ok.injEq] at hout; obtain ⟨rfl, -⟩ := hout
    simp only [send_ek.KeysUnsampled.send_hdr_chunk,
      v1.unchunked.send_ek.KeysUnsampled.send_header, Result.bind_eq_ok] at hc
    obtain ⟨⟨⟨uc, ts, mac⟩, r1⟩, ⟨⟨keys, rk⟩, hg, hk⟩, hrest⟩ := hc
    simp only [uncurry_apply_pair] at hk hrest
    simp only [Result.bind_eq_ok] at hk hrest
    obtain ⟨m, hm, hk⟩ := hk
    simp only [Result.ok.injEq, Prod.mk.injEq] at hk
    obtain ⟨⟨h1, h2, h3⟩, h4⟩ := hk
    subst h2 h3 h4
    obtain ⟨⟨ts1, z⟩, hap, hrest⟩ := hrest
    simp only [uncurry_apply_pair] at hrest
    simp only [Result.bind_eq_ok] at hrest
    obtain ⟨enc0, henc, sh, hsh, ⟨c', e'⟩, hn, hfin⟩ := hrest
    simp only [uncurry_apply_pair, ok.injEq, Prod.mk.injEq, and_assoc] at hfin
    obtain ⟨rfl, rfl, -⟩ := hfin
    have hsh' := eq_Ok_of_expect_eq_ok hsh; subst hsh'
    obtain ⟨r, hr⟩ := hP.keyGen i₁ i₂ rng rk keys hg
    have hmac := mac_hdr_ok P hP _ _ _ _ hm
    have hts := alloc.vec.Vec.append_ok_val hap
    have he := hP.encode _ _ henc
    have hnc := hP.nextChunk _ _ _ hn
    simp only [alloc.vec.Vec.deref, Slice.from_val] at hmac he
    rw [hts, hmac] at he
    refine ⟨r, ?_⟩
    subst h1
    simp only [Braid.send, hr, he, hnc]
    simp only [Refines, and_self, absMsg, Option.map_none]
  case HeaderReceived.headerReceived s e a hdr d =>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    obtain ⟨ep, hep, ⟨⟨s1, c, k⟩, rng1⟩, hc, hout⟩ := hs
    simp only [send_ct.HeaderReceived.epoch, Result.ok.injEq] at hep; subst hep
    simp only [uncurry_apply_pair, ok.injEq, Prod.mk.injEq,
        core.result.Result.Ok.injEq] at hout; obtain ⟨rfl, -⟩ := hout
    simp only [send_ct.HeaderReceived.send_ct1_chunk, Result.bind_eq_ok] at hc
    obtain ⟨⟨⟨uc, ct1, k'⟩, r1⟩, hsc, hrest⟩ := hc
    simp only [uncurry_apply_pair] at hrest
    simp only [Result.bind_eq_ok] at hrest
    obtain ⟨enc0, henc, sh, hsh, ⟨c', e'⟩, hn, hfin⟩ := hrest
    simp only [uncurry_apply_pair, ok.injEq, Prod.mk.injEq, and_assoc] at hfin
    obtain ⟨rfl, rfl, rfl, -⟩ := hfin
    have hsh' := eq_Ok_of_expect_eq_ok hsh; subst hsh'
    simp only [unchunked.send_ct.HeaderReceived.send_ct1, Result.bind_eq_ok] at hsc
    obtain ⟨⟨⟨ct1₀, es, ss₀⟩, rk⟩, he1, hsc⟩ := hsc
    simp only [alloc.slice.Slice.concat_eq, Slice.Insts.AllocSliceConcatTVec.concat_eq,
        Std.bind_assoc, uncurry_apply_pair] at hsc
    simp only [Result.bind_eq_ok] at hsc
    obtain ⟨_, h1, _, h2, _, h3, _, h4, l, hl, info, hinfo, _, h5, sec, hk, a', hu, v, hv, hsc⟩ :=
      hsc
    simp only [lift, Result.ok.injEq] at h1 h2 h3 h4 h5
    subst h1 h2 h3 h4 h5
    rw [Slice.concatListAux_shared_id_spec _ (fun _ => rfl), Result.ok.injEq] at hl
    subst hl
    have hiv := Slice.listToVec_ok_val hinfo
    have hiv' : info.val = Spqr.V1.Unchunked.SendCt.sckaKeyLabel ++
        (core.num.U64.to_be_bytes s.uc.epoch).val := by
      rw [hiv]; simp only [Array.to_slice, Array.make, Array.from_val, Slice.from_val,
          List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil,
          List.cons_append, List.nil_append, Spqr.V1.Unchunked.SendCt.sckaKeyLabel]
    have hsec := (post_of_ok (kdf.hkdf_to_vec_spec _ _ _ _ (by simp only [UScalar.ofNatCore_val_eq,
        Nat.reduceMul, Nat.reduceLeDiff])) hk).1
    simp only [alloc.vec.Vec.deref, Slice.from_val, hiv'] at hsec
    have hz : (Array.repeat 32#usize 0#u8).to_slice.val = List.replicate 32 0#u8 := by
      simp only [Array.to_slice, Array.repeat, UScalar.ofNatCore_val_eq, List.reduceReplicate,
          Array.from_val, Slice.from_val]
    rw [hz, show (32#usize : Std.Usize).val = 32 by simp only [UScalar.ofNatCore_val_eq],
      ← hP.kdfOk] at hsec
    have hau := absAuth_update P hP _ _ _ _ hu
    simp only [alloc.vec.Vec.deref, Slice.from_val, hsec] at hau
    have hv' := post_of_ok (alloc.vec.CloneVec.clone_U8_spec _) hv
    subst hv'
    simp only [Result.ok.injEq, Prod.mk.injEq] at hsc
    obtain ⟨⟨h6, rfl, rfl⟩, -⟩ := hsc
    subst h6
    obtain ⟨r, hr⟩ := hP.encaps1 i₁ i₂ rng rk _ _ _ _ he1
    have he := hP.encode _ _ henc
    have hnc := hP.nextChunk _ _ _ hn
    simp only [alloc.vec.Vec.deref, Slice.from_val] at he
    refine ⟨r, ?_⟩
    simp only [Braid.send, hr, he, hnc]
    simp only [Refines, hau, and_self, absMsg, Option.map_some, absKey, hsec]

/-- Related states have the same epoch. -/
theorem Refines.epoch {s : States} {σ : State _ _} (h : Refines s σ) :
    σ.epoch = s.epochOf.val := by
  cases s <;> cases σ <;> simp only [Refines] at h <;>
    simp only [State.epoch, States.epochOf, h.1]

/-- If `Refines s σ` and `s` does not expect the payload of `msg` (`States.Expects`), then the
model's `receiveEq` on `σ` and that payload returns `σ` and no key. -/
theorem receiveEq_of_not_expects (P : CodePrims) {s : States} {σ : State _ _} (h : Refines s σ)
    {msg : Message} (hp : ¬ s.Expects msg.payload) :
    Braid.receiveEq P σ (absMsg msg).payload = some (σ, none) := by
  obtain ⟨_, p⟩ := msg
  cases s <;> cases σ <;> simp only [Refines] at h <;>
    rcases p with _ | _ | _ | _ | (_ | _) | _ | _ <;>
    simp only [States.Expects, not_true_eq_false] at hp <;>
    simp only [receiveEq, absMsg]

/-- If `m` has the epoch of `σ`, then the model's `Receive()` of `m` on `σ` is `receiveEq` on the
payload of `m`. -/
theorem receive_of_eq (P : CodePrims) {σ : State _ _} {m : Msg encoding.Chunk}
    (h : m.epoch = σ.epoch) : Braid.receive P σ m = Braid.receiveEq P σ m.payload := by
  cases σ <;> simp only [State.epoch] at h <;>
    simp only [receive, h, State.epoch, gt_iff_lt, lt_self_iff_false, ↓reduceIte,
      Nat.left_eq_add, one_ne_zero]
  all_goals simp only [receiveEq]

/-- The model's `ek` branch of `Ct1Acknowledged` (transition (11)) and of `Ct1Sampled` with an
acknowledgement (transitions (8), (9)), with `onNone` the state when `ek` is still incomplete. -/
def ekStep (P : CodePrims) (e : Nat) (a : Auth) (hdr es ct1 : Bytes)
    (d : encoding.polynomial.PolyDecoder) (onNone : encoding.polynomial.PolyDecoder →
      State encoding.polynomial.PolyEncoder encoding.polynomial.PolyDecoder) :
    Option (State encoding.polynomial.PolyEncoder encoding.polynomial.PolyDecoder × Option Key) :=
  match P.message d with
  | none => some (onNone d, none)
  | some ek =>
    if P.ekMatches hdr ek then some (.ct2Sampled e a (ct2Encoder P e a es ct1 hdr ek), none)
    else none

/-- Assume `CodeAgrees P`. If `Ct1Sent::recv_ek uc ep ek` returns `Ok v`, then `v` has the
epoch, authenticator, `es` and `ct1` of `uc` and stores `ek` in place of the header, and the
model's `ek` check of `ek` against the header of `uc` passes. -/
theorem recv_ek_ok (P : CodePrims) (hP : CodeAgrees P) (uc : v1.unchunked.send_ct.Ct1Sent)
    (ep : Std.U64) (ek : alloc.vec.Vec Std.U8) (v : v1.unchunked.send_ct.Ct1SentEkReceived)
    (h : v1.unchunked.send_ct.Ct1Sent.recv_ek uc ep ek = ok (.Ok v)) :
    v = { epoch := uc.epoch, auth := uc.auth, es := uc.es, ek, ct1 := uc.ct1 } ∧
      P.ekMatches uc.hdr.val ek.val = true := by
  simp only [v1.unchunked.send_ct.Ct1Sent.recv_ek, massert, Result.bind_eq_ok] at h
  obtain ⟨_, -, b, hb, h⟩ := h
  cases b with
  | false => simp only [Bool.false_eq_true, ↓reduceIte, ok.injEq, reduceCtorEq] at h
  | true =>
    simp only [↓reduceIte, Result.ok.injEq, core.result.Result.Ok.injEq] at h
    exact ⟨h.symm, hP.ekMatches _ _ _ hb⟩

/-- Assume `CodeAgrees P`. If `Ct1Acknowledged::recv_ek_chunk` on `st` at its epoch and a chunk
`c` returns `Ok v`, then the model's `ekStep` on the decoder with `c` added returns a state `σ'`
and no key, and the state of `v` refines `σ'`. -/
theorem ct1Acknowledged_chunk_ok (P : CodePrims) (hP : CodeAgrees P)
    (st : send_ct.Ct1Acknowledged) (c : encoding.Chunk) (v : send_ct.Ct1AcknowledgedRecvChunk)
    (h : send_ct.Ct1Acknowledged.recv_ek_chunk st st.uc.epoch c = ok (.Ok v)) :
    ∃ σ', ekStep P st.uc.epoch.val (absAuth st.uc.auth) st.uc.hdr.val st.uc.es.val
        st.uc.ct1.val (P.addChunk st.receiving_ek c)
        (.ct1Acknowledged st.uc.epoch.val (absAuth st.uc.auth) st.uc.hdr.val st.uc.es.val
          st.uc.ct1.val) = some (σ', none) ∧
      Refines (match v with
        | .StillReceiving s => .Ct1Acknowledged s
        | .Done s => .Ct2Sampled s) σ' := by
  simp only [send_ct.Ct1Acknowledged.recv_ek_chunk, Result.bind_eq_ok] at h
  obtain ⟨d', hadd, o, ho, h⟩ := h
  have h3 := hP.addChunk _ _ _ hadd
  have h4 := hP.message _ _ ho
  rw [h3]
  cases o with
  | none =>
    simp only [Result.ok.injEq, core.result.Result.Ok.injEq] at h; subst h
    exact ⟨.ct1Acknowledged st.uc.epoch.val (absAuth st.uc.auth) st.uc.hdr.val st.uc.es.val
      st.uc.ct1.val d', by simp only [ekStep, h4,
          Option.map_none], by simp only [Refines, and_self]⟩
  | some m =>
    simp only [Result.bind_eq_ok] at h
    obtain ⟨r, hr, h⟩ := h
    replace h := continue_of_ok h fun _ => rfl
    obtain ⟨val, rfl, h⟩ := h
    obtain ⟨rfl, hm⟩ := recv_ek_ok P hP _ _ _ _ hr
    simp only [Result.bind_eq_ok] at h
    obtain ⟨⟨u2, ct2, mac⟩, h1, h⟩ := h
    simp only [uncurry_apply_pair, Result.bind_eq_ok] at h
    obtain ⟨pe, h2, h⟩ := h
    simp only [Result.ok.injEq, core.result.Result.Ok.injEq] at h; subst h
    obtain ⟨rfl, rfl⟩ := ct2_encoder_ok P hP _ _ _ _ _ st.uc.hdr.val h1 h2
    exact ⟨.ct2Sampled st.uc.epoch.val (absAuth st.uc.auth) (ct2Encoder P st.uc.epoch.val
      (absAuth st.uc.auth) st.uc.es.val st.uc.ct1.val st.uc.hdr.val m.val),
      by simp only [ekStep, h4, Option.map_some, hm,
          ↓reduceIte], by simp only [Refines, and_self]⟩

/-- Assume `CodeAgrees P`. If `Ct1Sampled::recv_ek_chunk` on `st` at its epoch and an `EkCt1Ack`
chunk `c` returns `Ok v`, then the model's `ekStep` on the decoder with `c` added returns a state
`σ'` and no key, and the state of `v` refines `σ'`. -/
theorem ct1Sampled_chunk_ack_ok (P : CodePrims) (hP : CodeAgrees P)
    (st : send_ct.Ct1Sampled) (c : encoding.Chunk) (v : send_ct.Ct1SampledRecvChunk)
    (h : send_ct.Ct1Sampled.recv_ek_chunk st st.uc.epoch c true = ok (.Ok v)) :
    ∃ σ', ekStep P st.uc.epoch.val (absAuth st.uc.auth) st.uc.hdr.val st.uc.es.val
        st.uc.ct1.val (P.addChunk st.receiving_ek c)
        (.ct1Acknowledged st.uc.epoch.val (absAuth st.uc.auth) st.uc.hdr.val st.uc.es.val
          st.uc.ct1.val) = some (σ', none) ∧
      Refines (match v with
        | .StillReceivingStillSending s => .Ct1Sampled s
        | .StillReceiving s => .Ct1Acknowledged s
        | .StillSending s => .EkReceivedCt1Sampled s
        | .Done s => .Ct2Sampled s) σ' := by
  simp only [send_ct.Ct1Sampled.recv_ek_chunk, Result.bind_eq_ok] at h
  obtain ⟨d', hadd, o, ho, h⟩ := h
  have h3 := hP.addChunk _ _ _ hadd
  have h4 := hP.message _ _ ho
  rw [h3]
  cases o with
  | none =>
    simp only [↓reduceIte, Result.ok.injEq, core.result.Result.Ok.injEq] at h; subst h
    exact ⟨.ct1Acknowledged st.uc.epoch.val (absAuth st.uc.auth) st.uc.hdr.val st.uc.es.val
      st.uc.ct1.val d', by simp only [ekStep, h4,
          Option.map_none], by simp only [Refines, and_self]⟩
  | some m =>
    simp only [Result.bind_eq_ok] at h
    obtain ⟨r, hr, h⟩ := h
    replace h := continue_of_ok h fun _ => rfl
    obtain ⟨val, rfl, h⟩ := h
    obtain ⟨rfl, hm⟩ := recv_ek_ok P hP _ _ _ _ hr
    simp only [↓reduceIte, Result.bind_eq_ok] at h
    obtain ⟨⟨u2, ct2, mac⟩, h1, h⟩ := h
    simp only [uncurry_apply_pair, Result.bind_eq_ok] at h
    obtain ⟨pe, h2, h⟩ := h
    simp only [Result.ok.injEq, core.result.Result.Ok.injEq] at h; subst h
    obtain ⟨rfl, rfl⟩ := ct2_encoder_ok P hP _ _ _ _ _ st.uc.hdr.val h1 h2
    exact ⟨.ct2Sampled st.uc.epoch.val (absAuth st.uc.auth) (ct2Encoder P st.uc.epoch.val
      (absAuth st.uc.auth) st.uc.es.val st.uc.ct1.val st.uc.hdr.val m.val),
      by simp only [ekStep, h4, Option.map_some, hm,
          ↓reduceIte], by simp only [Refines, and_self]⟩

/-- Assume `CodeAgrees P`. If `Ct1Sampled::recv_ek_chunk` on `st` at its epoch and an `Ek` chunk
`c` returns `Ok v`, then the model's `Ek` branch of `Ct1Sampled` on the decoder with `c` added
returns a state `σ'` and no key, and the state of `v` refines `σ'`. The branch stays in
`Ct1Sampled` while `ek` is incomplete and takes transition (10) when it completes. -/
theorem ct1Sampled_chunk_noack_ok (P : CodePrims) (hP : CodeAgrees P)
    (st : send_ct.Ct1Sampled) (c : encoding.Chunk) (v : send_ct.Ct1SampledRecvChunk)
    (h : send_ct.Ct1Sampled.recv_ek_chunk st st.uc.epoch c false = ok (.Ok v)) :
    ∃ σ', (match P.message (P.addChunk st.receiving_ek c) with
        | none => some (State.ct1Sampled st.uc.epoch.val (absAuth st.uc.auth) st.uc.hdr.val
            st.uc.es.val st.uc.ct1.val st.sending_ct1 (P.addChunk st.receiving_ek c), none)
        | some ek =>
          if P.ekMatches st.uc.hdr.val ek then
            some (State.ekReceivedCt1Sampled st.uc.epoch.val (absAuth st.uc.auth) st.uc.es.val
              st.uc.ct1.val st.uc.hdr.val ek st.sending_ct1, none)
          else none : Option (State encoding.polynomial.PolyEncoder
            encoding.polynomial.PolyDecoder × Option Key)) = some (σ', none) ∧
      Refines (match v with
        | .StillReceivingStillSending s => .Ct1Sampled s
        | .StillReceiving s => .Ct1Acknowledged s
        | .StillSending s => .EkReceivedCt1Sampled s
        | .Done s => .Ct2Sampled s) σ' := by
  simp only [send_ct.Ct1Sampled.recv_ek_chunk, Result.bind_eq_ok] at h
  obtain ⟨d', hadd, o, ho, h⟩ := h
  have h3 := hP.addChunk _ _ _ hadd
  have h4 := hP.message _ _ ho
  rw [h3]
  cases o with
  | none =>
    simp only [Bool.false_eq_true, ↓reduceIte, Result.ok.injEq,
      core.result.Result.Ok.injEq] at h
    subst h
    exact ⟨.ct1Sampled st.uc.epoch.val (absAuth st.uc.auth) st.uc.hdr.val st.uc.es.val
      st.uc.ct1.val st.sending_ct1 d', by simp only [h4,
          Option.map_none], by simp only [Refines, and_self]⟩
  | some m =>
    simp only [Result.bind_eq_ok] at h
    obtain ⟨r, hr, h⟩ := h
    replace h := continue_of_ok h fun _ => rfl
    obtain ⟨val, rfl, h⟩ := h
    obtain ⟨rfl, hm⟩ := recv_ek_ok P hP _ _ _ _ hr
    simp only [Bool.false_eq_true, ↓reduceIte, Result.ok.injEq,
      core.result.Result.Ok.injEq] at h
    subst h
    exact ⟨.ekReceivedCt1Sampled st.uc.epoch.val (absAuth st.uc.auth) st.uc.es.val
      st.uc.ct1.val st.uc.hdr.val m.val st.sending_ct1, by simp only [h4, Option.map_some, hm,
          ↓reduceIte], by simp only [Refines, and_self]⟩

/-- Assume `CodeAgrees P`. If `uc` has a 960-byte `ct1`, `ct2` has 128 bytes, `mac` has 32 bytes,
and `EkSentCt1Received::recv_ct2 uc ct2 mac` returns `Ok (nh, sec)`, then, with `e` the epoch of
`uc`:

* `sec` is at epoch `e`, and its secret is `KDF_OK` at `e` of `Decaps(uc.dk, uc.ct1, ct2)`;
* `nh` is at epoch `e + 1`, its authenticator is that of `uc` updated at `e` with the secret of
  `sec`, and its MAC key has 32 bytes;
* `mac` is the model's `MacCt` at `e` of `uc.ct1 ‖ ct2` under the authenticator of `nh`. -/
theorem recv_ct2_ok (P : CodePrims) (hP : CodeAgrees P) (uc : unchunked.send_ek.EkSentCt1Received)
    (ct2 mac : alloc.vec.Vec Std.U8) (nh : unchunked.send_ct.NoHeaderReceived) (sec : EpochSecret)
    (hct1 : uc.ct1.length = 960) (hct2 : ct2.length = 128) (hmac : mac.length = 32)
    (h : unchunked.send_ek.EkSentCt1Received.recv_ct2 uc ct2 mac = ok (.Ok (nh, sec))) :
    sec.epoch = uc.epoch ∧ sec.secret.val = P.kdfOk (P.decaps uc.dk.val uc.ct1.val ct2.val)
      uc.epoch.val ∧ nh.epoch.val = uc.epoch.val + 1 ∧
      absAuth nh.auth = Auth.update P (absAuth uc.auth) uc.epoch.val sec.secret.val ∧
      nh.auth.mac_key.length = 32 ∧
      mac.val = Auth.macCt P (absAuth nh.auth) uc.epoch.val (uc.ct1.val ++ ct2.val) := by
  simp only [unchunked.send_ek.EkSentCt1Received.recv_ct2, Result.bind_eq_ok] at h
  obtain ⟨ss, hss, _, h1, _, h2, _, h3, _, h4, info, hinfo, _, h5, ss1, hk, a', hu, ct1', hct,
    r, hr, h⟩ := h
  simp only [lift, Result.ok.injEq] at h1 h2 h3 h4 h5
  subst h1 h2 h3 h4 h5
  replace h := continue_of_ok h fun _ => rfl
  obtain ⟨u, rfl, h⟩ := h
  simp only [Result.bind_eq_ok] at h
  obtain ⟨i, hi, v, hv, h⟩ := h
  simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hdec := hP.decaps _ _ _ _ hss
  have hiv := alloc.slice.Slice.concat_shared_id_ok_val _ (fun _ => rfl) hinfo
  have hiv' : info.val = Spqr.V1.Unchunked.SendCt.sckaKeyLabel ++
      (core.num.U64.to_be_bytes uc.epoch).val := by
    rw [hiv]; simp only [Array.to_slice, Array.make, Array.from_val, Slice.from_val,
        List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil,
        List.cons_append, List.nil_append, Spqr.V1.Unchunked.SendCt.sckaKeyLabel]
  have hsec := (post_of_ok (kdf.hkdf_to_vec_spec _ _ _ _ (by simp only [UScalar.ofNatCore_val_eq,
      Nat.reduceMul, Nat.reduceLeDiff])) hk).1
  have hz : (Array.repeat 32#usize 0#u8).to_slice.val = List.replicate 32 0#u8 := by
    simp only [Array.to_slice, Array.repeat, UScalar.ofNatCore_val_eq, List.reduceReplicate,
        Array.from_val, Slice.from_val]
  simp only [alloc.vec.Vec.deref, Slice.from_val, hiv'] at hsec
  rw [hz, show (32#usize : Std.Usize).val = 32 by simp only [UScalar.ofNatCore_val_eq],
    ← hP.kdfOk, ← hdec] at hsec
  have hau := absAuth_update P hP _ _ _ _ hu
  have hkey := (post_of_ok (authenticator.Authenticator.update_spec _ _ _
    (authenticator.Authenticator.length_le_of_update_ok hu)) hu).2.1
  have hctv := alloc.vec.Vec.extend_from_slice_U8_ok_val hct
  simp only [alloc.vec.Vec.deref, Slice.from_val] at hctv hau
  have hver := post_of_ok (authenticator.Authenticator.verify_ct_spec _ _ _ _
    (by rw [hkey]; scalar_tac)
    (by simp only [alloc.vec.Vec.deref, Slice.length, Slice.from_val, hctv, List.length_append]
        simp only [alloc.vec.Vec.length] at hct1 hct2
        rw [hct1, hct2]; scalar_tac)
    (by simp only [alloc.vec.Vec.deref, Slice.length, Slice.from_val]
        simp only [alloc.vec.Vec.length] at hmac
        rw [hmac, authenticator.Authenticator.MACSIZE_spec])) hr
  have hmc := mac_ct_ok P hP _ _ _ _ (hver.mp rfl)
  simp only [alloc.vec.Vec.deref, Slice.from_val, hctv] at hmc
  refine ⟨rfl, ?_, UScalar.val_of_add_eq_ok hi, ?_, hkey, ?_⟩
  · rw [Slice.to_vec_U8_ok_val hv]; simpa only [alloc.vec.Vec.deref_val] using hsec
  · rw [Slice.to_vec_U8_ok_val hv]; simpa only [alloc.vec.Vec.deref_val, hsec] using hau
  · exact (Slice.from_val _ _).symm.trans hmc

/-- Assume `CodeAgrees P`. Let `st` have a 960-byte `ct1` and a `ct2` decoder
that needs 80 points. If `EkSentCt1Received::recv_ct2_chunk` on `st` at its epoch and a chunk `c`
returns `Ok v`, then the model's `receiveEq` on `ct2` chunk `c` returns a state `σ'` that the
state of `v` refines. The key is none while `ct2` is incomplete (`StillReceiving`), and the code's
key when `ct2` completes and the model takes transition (5) (`Done`). -/
theorem ekSentCt1Received_chunk_ok (P : CodePrims) (hP : CodeAgrees P)
    (st : send_ek.EkSentCt1Received) (c : encoding.Chunk)
    (v : send_ek.EkSentCt1ReceivedRecvChunk) (hct1 : st.uc.ct1.length = 960)
    (hpn : st.receiving_ct2.pts_needed.val = 80)
    (h : send_ek.EkSentCt1Received.recv_ct2_chunk st st.uc.epoch c = ok (.Ok v)) :
    ∃ σ', Braid.receiveEq P (.ekSentCt1Received st.uc.epoch.val (absAuth st.uc.auth)
        st.uc.dk.val st.uc.ct1.val st.receiving_ct2) (.ct2 c) =
        some (σ', match v with
          | .StillReceiving _ => none
          | .Done (_, sec) => some (absKey sec)) ∧
      Refines (match v with
        | .StillReceiving s => .EkSentCt1Received s
        | .Done (s, _) => .NoHeaderReceived s) σ' := by
  simp only [send_ek.EkSentCt1Received.recv_ct2_chunk, massert, Result.bind_eq_ok] at h
  obtain ⟨_, -, d', hadd, o, ho, h⟩ := h
  have h3 := hP.addChunk _ _ _ hadd
  have h4 := hP.message _ _ ho
  cases o with
  | none =>
    simp only [Result.ok.injEq, core.result.Result.Ok.injEq] at h; subst h
    exact ⟨.ekSentCt1Received st.uc.epoch.val (absAuth st.uc.auth) st.uc.dk.val st.uc.ct1.val d',
      by simp only [receiveEq, h3, h4, Option.map_none],
      by simp only [Refines, alloc.vec.Vec.length, hct1, add_chunk_pts_needed hadd, hpn, and_self]⟩
  | some m =>
    simp only [Result.bind_eq_ok] at h
    obtain ⟨sl, hsl, n, hn, s1, hs1, mac, hmac, s2, hs2, ct2, hct2, r, hr, h⟩ := h
    have hn128 : n = 128#usize := ok_unique incremental_mlkem768.CIPHERTEXT2_SIZE_eq hn
    have hml : m.val.length = 160 := by
      rw [decoded_message_length ho, add_chunk_pts_needed hadd, hpn]
    have hmacv : mac.val = m.val.drop 128 := by
      rw [Slice.to_vec_U8_ok_val hmac, Slice.index_range_from_ok_val hs1,
        alloc.vec.Vec.as_slice_ok_val hsl, hn128]; rfl
    have hct2v : ct2.val = m.val.take 128 := by
      rw [Slice.to_vec_U8_ok_val hct2, Slice.index_range_to_ok_val hs2,
        alloc.vec.Vec.as_slice_ok_val hsl, hn128]; rfl
    replace h := continue_of_ok h fun _ => rfl
    obtain ⟨val, rfl, h⟩ := h
    obtain ⟨nh, sec⟩ := val
    simp only [uncurry_apply_pair] at h
    simp only [Result.bind_eq_ok] at h
    obtain ⟨i1, hi1, i2, hi2, dr, hnew, pd, hpd, h⟩ := h
    obtain rfl := eq_Ok_of_expect_eq_ok hpd
    simp only [Result.ok.injEq, core.result.Result.Ok.injEq] at h; subst h
    obtain ⟨hse, hss, hne, hna, hkey, hmc⟩ := recv_ct2_ok P hP _ _ _ _ _ hct1
      (by simp only [alloc.vec.Vec.length, hct2v, List.length_take, hml, Nat.reduceLeDiff,
        inf_of_le_left])
      (by simp only [alloc.vec.Vec.length, hmacv, List.length_drop, hml, Nat.reduceSub]) hr
    have hi1v := post_of_ok incremental_mlkem768.HEADER_SIZE_spec hi1
    have hhb : Spqr.Mlkem.headerBytes = 64 := by decide
    have hi2v := UScalar.val_of_add_eq_ok hi2
    rw [authenticator.Authenticator.MACSIZE_spec, hi1v, hhb] at hi2v
    have hdn := hP.decoderNew _ _ hnew
    rw [UScalar.val_of_add_eq_ok hi2, ← hP.headerSize i1 hi1, ← hP.macSize] at hdn
    have hcs : P.ct2Size = 128 := by rw [hP.ct2Size n hn, hn128]; rfl
    refine ⟨.noHeaderReceived (st.uc.epoch.val + 1) (absAuth nh.auth)
      (P.decoderNew (P.headerSize + P.macSize)), ?_, ?_⟩
    · have hmc' : m.val.drop 128 = Auth.macCt P (absAuth nh.auth) st.uc.epoch.val
          (st.uc.ct1.val ++ m.val.take 128) := by rw [← hmacv, ← hct2v]; exact hmc
      rw [hna] at hmc'
      simp only [Braid.receiveEq, h3, h4, hcs]
      have hss' : P.kdfOk (P.decaps st.uc.dk.val st.uc.ct1.val (m.val.take 128))
          st.uc.epoch.val = sec.secret.val := by rw [hss, hct2v]
      simp only [Option.map_some, hss']
      simp only [hmc', ↓reduceIte, hna, absKey, hse]
    · refine ⟨?_, ?_, ?_, hkey, ?_⟩
      · simp only [hne]
      · rfl
      · rw [hdn]
      · rw [new_pts_needed (by omega) hnew, hi2v]

/-- Assume `CodeAgrees P`. Let `st` have a 32-byte MAC key and a header decoder that needs 48
points. If `NoHeaderReceived::recv_hdr_chunk` on `st` at its epoch and a chunk `c` returns
`Ok v`, then the model's `receiveEq` on header chunk `c` returns a state `σ'` and no key, and the
state of `v` refines `σ'`. The state stays `NoHeaderReceived` while the header is incomplete
(`StillReceiving`), and the model takes transition (6) when it completes (`Done`). -/
theorem noHeaderReceived_chunk_ok (P : CodePrims) (hP : CodeAgrees P)
    (st : send_ct.NoHeaderReceived) (c : encoding.Chunk) (v : send_ct.NoHeaderReceivedRecvChunk)
    (hkey : st.uc.auth.mac_key.length = 32) (hpn : st.receiving_hdr.pts_needed.val = 48)
    (h : send_ct.NoHeaderReceived.recv_hdr_chunk st st.uc.epoch c = ok (.Ok v)) :
    ∃ σ', Braid.receiveEq P (.noHeaderReceived st.uc.epoch.val (absAuth st.uc.auth)
        st.receiving_hdr) (.hdr c) = some (σ', none) ∧
      Refines (match v with
        | .StillReceiving s => .NoHeaderReceived s
        | .Done s => .HeaderReceived s) σ' := by
  simp only [send_ct.NoHeaderReceived.recv_hdr_chunk, massert, Result.bind_eq_ok] at h
  obtain ⟨_, -, d', hadd, o, ho, h⟩ := h
  have h3 := hP.addChunk _ _ _ hadd
  have h4 := hP.message _ _ ho
  cases o with
  | none =>
    simp only [Result.ok.injEq, core.result.Result.Ok.injEq] at h; subst h
    exact ⟨.noHeaderReceived st.uc.epoch.val (absAuth st.uc.auth) d',
      by simp only [receiveEq, h3, h4, Option.map_none],
      by simp only [Refines, alloc.vec.Vec.length, hkey, add_chunk_pts_needed hadd, hpn, and_self]⟩
  | some m =>
    simp only [Result.bind_eq_ok] at h
    obtain ⟨sl, hsl, n, hn, s1, hs1, mac, hmac, s2, hs2, hdr, hhdr, i1, hi1, dr, hnew, r, hr,
      h⟩ := h
    have hn64 : n.val = 64 := by
      rw [post_of_ok incremental_mlkem768.HEADER_SIZE_spec hn]; decide
    have hml : m.val.length = 96 := by
      rw [decoded_message_length ho, add_chunk_pts_needed hadd, hpn]
    have hmacv : mac.val = m.val.drop 64 := by
      rw [Slice.to_vec_U8_ok_val hmac, Slice.index_range_from_ok_val hs1,
        alloc.vec.Vec.as_slice_ok_val hsl, hn64]
    have hhdrv : hdr.val = m.val.take 64 := by
      rw [Slice.to_vec_U8_ok_val hhdr, Slice.index_range_to_ok_val hs2,
        alloc.vec.Vec.as_slice_ok_val hsl, hn64]
    replace h := continue_of_ok h fun _ => rfl
    obtain ⟨val, rfl, h⟩ := h
    simp only [Result.bind_eq_ok] at h
    obtain ⟨pd, hpd, h⟩ := h
    obtain rfl := eq_Ok_of_expect_eq_ok hpd
    simp only [Result.ok.injEq, core.result.Result.Ok.injEq] at h; subst h
    simp only [v1.unchunked.send_ct.NoHeaderReceived.recv_header, massert,
      Result.bind_eq_ok] at hr
    obtain ⟨_, -, vr, hv, hr⟩ := hr
    replace hr := continue_of_ok hr fun _ => rfl
    obtain ⟨u, rfl, hr⟩ := hr
    simp only [Result.ok.injEq, core.result.Result.Ok.injEq] at hr; subst hr
    have hver := post_of_ok (authenticator.Authenticator.verify_hdr_spec _ _ _ _
      (by rw [hkey]; scalar_tac)
      (by
        simp only [alloc.vec.Vec.deref, Slice.length, Slice.from_val, hhdrv, List.length_take,
          hml]
        scalar_tac)
      (by simp only [Slice.length, alloc.vec.Vec.deref, hmacv, Slice.from_val, List.length_drop,
          hml, Nat.reduceSub, authenticator.Authenticator.MACSIZE_spec]))
      hv
    have hmh := mac_hdr_ok P hP _ _ _ _ (hver.mp rfl)
    simp only [alloc.vec.Vec.deref, Slice.from_val] at hmh
    have hhs := hP.headerSize n hn
    have hek := hP.decoderNew _ _ hnew
    rw [← hP.ekSize i1 hi1] at hek
    refine ⟨.headerReceived st.uc.epoch.val (absAuth st.uc.auth) hdr.val
      (P.decoderNew P.ekSize), ?_, ?_⟩
    · simp only [Braid.receiveEq, h3, h4, Option.map_some, hhs, hn64]
      have hmh' : m.val.drop 64 =
          Auth.macHdr P (absAuth st.uc.auth) st.uc.epoch.val (m.val.take 64) := by
        rw [← hmacv, ← hhdrv]; exact (Slice.from_val _ _).symm.trans hmh
      simp only [hmh', ↓reduceIte, hhdrv]
    · simp only [Refines, hek, and_self]

/-- Assume `CodeAgrees P` and `Refines s σ`. If `States::recv` succeeds on `s`,
then the model's `Receive()` on `σ` succeeds with a related state and the code's key. -/
@[correctness_spec, braid_spec "§2.5",
  braid_deviation Deviation.futureEpochError Deviation.ct1AckAccepted Deviation.lateEkChunk]
theorem recv_refines (P : CodePrims) (hP : CodeAgrees P) (s : States)
    (σ : State _ _) (h : Refines s σ) (msg : Message) (out : Recv)
    (hs : States.recv s msg = ok (.Ok out)) :
    ∃ σ', Braid.receive P σ (absMsg msg) = some (σ', out.key.map absKey) ∧
      Refines out.state σ' := by
  have hep := h.epoch
  rcases Nat.lt_trichotomy msg.epoch.val s.epochOf.val with hlt | heq | hgt
  · rw [recv_of_lt s msg hlt, Result.ok.injEq, core.result.Result.Ok.injEq] at hs
    subst hs
    refine ⟨σ, ?_, h⟩
    have hme : (absMsg msg).epoch < σ.epoch := by rw [hep]; exact hlt
    cases σ <;> simp only [Braid.receive, State.epoch] at hme ⊢ <;>
      simp only [gt_iff_lt, Nat.not_lt_of_gt hme, ↓reduceIte, hme, Option.map_none,
          ite_eq_right_iff, Option.some.injEq, Prod.mk.injEq, reduceCtorEq, and_true, imp_false,
          ne_eq]
    all_goals omega
  · have heq' : msg.epoch = s.epochOf := UScalar.eq_of_val_eq heq
    by_cases hx : s.Expects msg.payload
    · have hme : (absMsg msg).epoch = σ.epoch := by rw [hep, ← heq]; rfl
      rw [receive_of_eq P hme]
      obtain ⟨e, p⟩ := msg
      simp only at heq' hx hs ⊢
      subst heq'
      cases s <;> cases σ <;> simp only [Refines] at h <;>
        rcases p with _ | _ | _ | _ | (_ | _) | _ | _ <;>
        simp only [States.Expects] at hx <;>
        simp only [States.recv, States.epochOf, send_ek.KeysSampled.epoch,
          send_ek.HeaderSent.epoch, send_ek.Ct1Received.epoch, send_ek.EkSentCt1Received.epoch,
          send_ct.NoHeaderReceived.epoch, send_ct.Ct1Sampled.epoch,
          send_ct.EkReceivedCt1Sampled.epoch, send_ct.Ct1Acknowledged.epoch, lift,
          core.cmp.impls.OrdU64.cmp, bind_ok, Nat.compare_eq_eq.2 rfl] at hs
      case pos.KeysSampled.keysSampled.Ct1 st e a dk hdr ek enc c =>
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
        simp only [Result.bind_eq_ok, Result.ok.injEq, core.result.Result.Ok.injEq] at hs
        obtain ⟨st', hst, rfl⟩ := hs
        simp only [send_ek.KeysSampled.recv_ct1_chunk, massert, Result.bind_eq_ok] at hst
        obtain ⟨_, -, n, hn, dr, hnew, d, hexp, d', hadd, ⟨uc, ekv⟩, hse, hst⟩ := hst
        simp only [uncurry_apply_pair] at hst
        simp only [Result.bind_eq_ok] at hst
        obtain ⟨er, her, se, hse', hst⟩ := hst
        simp only [Result.ok.injEq] at hst
        subst hst
        obtain rfl := eq_Ok_of_expect_eq_ok hexp
        obtain rfl := eq_Ok_of_expect_eq_ok hse'
        simp only [unchunked.send_ek.HeaderSent.send_ek, Result.ok.injEq, Prod.mk.injEq] at hse
        obtain ⟨rfl, rfl⟩ := hse
        have h1 := hP.ct1Size n hn
        have h2 := hP.decoderNew n _ hnew
        have h3 := hP.addChunk _ _ _ hadd
        have h4 := hP.encode _ _ her
        simp only [alloc.vec.Vec.deref, Slice.from_val] at h4
        have hn960 : n = 960#usize := ok_unique incremental_mlkem768.CIPHERTEXT1_SIZE_eq hn
        have hp : d'.pts_needed.val = 480 := by
          rw [add_chunk_pts_needed hadd, new_pts_needed (by rw [hn960]; rfl) hnew,
            hn960]; rfl
        refine ⟨_, rfl, ?_⟩
        simp only [Refines, h1, h2, h3, h4, hp, and_self]
      case pos.Ct1Received.ct1Received st e a dk ct1 enc c =>
        obtain ⟨rfl, rfl, rfl, rfl, rfl, hct1⟩ := h
        simp only [Result.bind_eq_ok, Result.ok.injEq, core.result.Result.Ok.injEq] at hs
        obtain ⟨st', hst, rfl⟩ := hs
        simp only [send_ek.Ct1Received.recv_ct2_chunk, massert, Result.bind_eq_ok] at hst
        obtain ⟨_, -, n, hn, _, -, _, -, _, -, i3, hi3, dr, hnew, d, hexp, d', hadd, hst⟩ := hst
        simp only [Result.ok.injEq] at hst
        subst hst
        obtain rfl := eq_Ok_of_expect_eq_ok hexp
        have h1 := hP.ct2Size n hn
        have h2 := hP.decoderNew _ _ hnew
        have h3 := hP.addChunk _ _ _ hadd
        have hn128 : n = 128#usize := ok_unique incremental_mlkem768.CIPHERTEXT2_SIZE_eq hn
        have hi3v := UScalar.val_of_add_eq_ok hi3
        rw [hn128, authenticator.Authenticator.MACSIZE_spec] at hi3v
        have hp : d'.pts_needed.val = 80 := by
          rw [add_chunk_pts_needed hadd, new_pts_needed (by rw [hi3v]; rfl) hnew, hi3v]; rfl
        rw [UScalar.val_of_add_eq_ok hi3, ← h1, ← hP.macSize] at h2
        refine ⟨_, rfl, ?_⟩
        simp only [Refines, h2, h3, alloc.vec.Vec.length, hct1, hp, and_self]
      case pos.HeaderSent.headerSent st e a dk d enc c =>
        obtain ⟨rfl, rfl, rfl, rfl, rfl, hpn⟩ := h
        simp only [Result.bind_eq_ok] at hs
        obtain ⟨r, hr, hs⟩ := hs
        simp only [send_ek.HeaderSent.recv_ct1_chunk, massert, Result.bind_eq_ok] at hr
        obtain ⟨_, -, d', hadd, o, ho, hr⟩ := hr
        have h3 := hP.addChunk _ _ _ hadd
        have h4 := hP.message _ _ ho
        cases o with
        | none =>
          simp only [Result.ok.injEq] at hr; subst hr
          simp only [Result.ok.injEq, core.result.Result.Ok.injEq] at hs; subst hs
          refine ⟨.headerSent st.uc.epoch.val (absAuth st.uc.auth) st.uc.dk.val d'
            st.sending_ek, ?_, ?_⟩
          · simp only [receiveEq, absMsg, h3, h4, Option.map_none]
          · simp only [Refines, add_chunk_pts_needed hadd, hpn, and_self]
        | some m =>
          simp only [Result.bind_eq_ok] at hr
          obtain ⟨uc, huc, hr⟩ := hr
          simp only [Result.ok.injEq] at hr; subst hr
          simp only [Result.ok.injEq, core.result.Result.Ok.injEq] at hs; subst hs
          simp only [unchunked.send_ek.EkSent.recv_ct1, massert, Result.bind_eq_ok,
            Result.ok.injEq] at huc
          obtain ⟨_, -, rfl⟩ := huc
          have hml : m.val.length = 960 := by
            rw [decoded_message_length ho, add_chunk_pts_needed hadd, hpn]
          refine ⟨.ct1Received st.uc.epoch.val (absAuth st.uc.auth) st.uc.dk.val m.val
            st.sending_ek, ?_, ?_⟩
          · simp only [receiveEq, absMsg, h3, h4, Option.map_some, Option.map_none]
          · simp only [Refines, alloc.vec.Vec.length, hml, and_self]
      case pos.EkReceivedCt1Sampled.ekReceivedCt1Sampled.EkCt1Ack st e a es ct1 hdr ek enc c =>
        obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
        simp only [↓reduceIte] at hs
        simp only [Result.bind_eq_ok, Result.ok.injEq, core.result.Result.Ok.injEq] at hs
        obtain ⟨st', hst, rfl⟩ := hs
        exact ⟨_, rfl, recv_ct1_ack_ok P hP st _ _ hdr hst⟩
      case pos.EkReceivedCt1Sampled.ekReceivedCt1Sampled.Ct1Ack.true st e a es ct1 hdr ek enc =>
        obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
        simp only [↓reduceIte, bind_ok] at hs
        simp only [Result.bind_eq_ok, Result.ok.injEq, core.result.Result.Ok.injEq] at hs
        obtain ⟨st', hst, rfl⟩ := hs
        exact ⟨_, rfl, recv_ct1_ack_ok P hP st _ _ hdr hst⟩
      case pos.Ct1Acknowledged.ct1Acknowledged.Ek st e a hdr es ct1 d c =>
        obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
        simp only [Result.bind_eq_ok] at hs
        obtain ⟨r, hr, hs⟩ := hs
        replace hs := continue_of_ok hs fun _ => rfl
        obtain ⟨val, rfl, hs⟩ := hs
        obtain ⟨σ', h1, h2⟩ := ct1Acknowledged_chunk_ok P hP st c val hr
        cases val <;>
          simp only [Result.ok.injEq, core.result.Result.Ok.injEq] at hs <;> subst hs <;>
          exact ⟨σ', h1, h2⟩
      case pos.Ct1Acknowledged.ct1Acknowledged.EkCt1Ack st e a hdr es ct1 d c =>
        obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
        simp only [Result.bind_eq_ok] at hs
        obtain ⟨r, hr, hs⟩ := hs
        replace hs := continue_of_ok hs fun _ => rfl
        obtain ⟨val, rfl, hs⟩ := hs
        obtain ⟨σ', h1, h2⟩ := ct1Acknowledged_chunk_ok P hP st c val hr
        cases val <;>
          simp only [Result.ok.injEq, core.result.Result.Ok.injEq] at hs <;> subst hs <;>
          exact ⟨σ', h1, h2⟩
      case pos.Ct1Sampled.ct1Sampled.Ek st e a hdr es ct1 enc d c =>
        obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
        simp only [uncurry_apply_pair] at hs
        simp only [Result.bind_eq_ok] at hs
        obtain ⟨r, hr, hs⟩ := hs
        replace hs := continue_of_ok hs fun _ => rfl
        obtain ⟨val, rfl, hs⟩ := hs
        obtain ⟨σ', h1, h2⟩ := ct1Sampled_chunk_noack_ok P hP st c val hr
        cases val <;>
          simp only [Result.ok.injEq, core.result.Result.Ok.injEq] at hs <;> subst hs <;>
          exact ⟨σ', h1, h2⟩
      case pos.Ct1Sampled.ct1Sampled.EkCt1Ack st e a hdr es ct1 enc d c =>
        obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
        simp only [uncurry_apply_pair] at hs
        simp only [Result.bind_eq_ok] at hs
        obtain ⟨r, hr, hs⟩ := hs
        replace hs := continue_of_ok hs fun _ => rfl
        obtain ⟨val, rfl, hs⟩ := hs
        obtain ⟨σ', h1, h2⟩ := ct1Sampled_chunk_ack_ok P hP st c val hr
        cases val <;>
          simp only [Result.ok.injEq, core.result.Result.Ok.injEq] at hs <;> subst hs <;>
          exact ⟨σ', h1, h2⟩
      case pos.NoHeaderReceived.noHeaderReceived st e a d c =>
        obtain ⟨rfl, rfl, rfl, hkey, hpn⟩ := h
        simp only [Result.bind_eq_ok] at hs
        obtain ⟨r, hr, hs⟩ := hs
        replace hs := continue_of_ok hs fun _ => rfl
        obtain ⟨val, rfl, hs⟩ := hs
        obtain ⟨σ', h1, h2⟩ := noHeaderReceived_chunk_ok P hP st c val hkey hpn hr
        cases val <;>
          simp only [Result.ok.injEq, core.result.Result.Ok.injEq] at hs <;> subst hs <;>
          exact ⟨σ', h1, h2⟩
      case pos.EkSentCt1Received.ekSentCt1Received st e a dk ct1 d c =>
        obtain ⟨rfl, rfl, rfl, rfl, rfl, hct1, hpn⟩ := h
        simp only [Result.bind_eq_ok] at hs
        obtain ⟨r, hr, hs⟩ := hs
        replace hs := continue_of_ok hs fun _ => rfl
        obtain ⟨val, rfl, hs⟩ := hs
        obtain ⟨σ', h1, h2⟩ := ekSentCt1Received_chunk_ok P hP st c val hct1 hpn hr
        cases val with
        | StillReceiving s =>
          simp only [Result.ok.injEq, core.result.Result.Ok.injEq] at hs; subst hs
          exact ⟨σ', h1, h2⟩
        | Done p =>
          obtain ⟨s, sec⟩ := p
          simp only [uncurry_apply_pair, ok.injEq, core.result.Result.Ok.injEq] at hs; subst hs
          exact ⟨σ', h1, h2⟩
    · rw [recv_of_eq_unexpected s msg heq' hx, Result.ok.injEq,
        core.result.Result.Ok.injEq] at hs
      subst hs
      refine ⟨σ, ?_, h⟩
      have hr := receiveEq_of_not_expects P h hx
      have hme : (absMsg msg).epoch = σ.epoch := by rw [hep, ← heq]; rfl
      cases σ <;> simp only [Braid.receive, State.epoch] at hme ⊢ <;>
        simp only [hme, gt_iff_lt, lt_self_iff_false, ↓reduceIte, hr, Option.map_none,
          Nat.left_eq_add, one_ne_zero]
  · by_cases hn : ∃ st, s = .Ct2Sampled st ∧ msg.epoch.val = st.uc.epoch.val + 1
    · obtain ⟨st, rfl, hn⟩ := hn
      rw [recv_Ct2Sampled_next_epoch st msg hn, Result.ok.injEq,
        core.result.Result.Ok.injEq] at hs
      subst hs
      cases σ <;> simp only [Refines] at h
      obtain ⟨rfl, rfl, -⟩ := h
      refine ⟨.keysUnsampled (st.uc.epoch.val + 1) (absAuth st.uc.auth), ?_, ?_⟩
      · simp only [receive, absMsg, hn, ↓reduceIte, Option.map_none]
      · simp only [Refines, hn, and_self]
    · rw [recv_of_gt s msg hgt (fun st hst hm => hn ⟨st, hst, hm⟩)] at hs
      simp only [ok.injEq, reduceCtorEq] at hs

/-- Assume `CodeAgrees P` and `Refines s σ`. Then every finite sequence of successful calls from
`s` (`Run s s' ks`) is a run of the model from `σ`, with a related end state and the same keys. -/
@[correctness_spec, braid_spec "§2.5",
  braid_deviation Deviation.futureEpochError Deviation.ct1AckAccepted Deviation.lateEkChunk]
theorem run_refines (P : CodePrims) (hP : CodeAgrees P) {s s' : States}
    {ks : List EpochSecret} (hr : Run s s' ks) {σ : State _ _} (h : Refines s σ) :
    ∃ σ', Braid.Run P σ σ' (ks.map absKey) ∧ Refines s' σ' := by
  induction hr generalizing σ with
  | nil => exact ⟨σ, .nil σ, h⟩
  | cons hstep _ ih =>
    cases hstep with
    | send i₁ i₂ rng rng' out hs =>
      obtain ⟨r, h1, -, h3⟩ := send_refines P hP i₁ i₂ _ σ h rng rng' out hs
      obtain ⟨σ₂, hrun, h₂⟩ := ih h1
      refine ⟨σ₂, ?_, h₂⟩
      have := Braid.Run.cons (Braid.Step.send σ r) hrun
      rw [← h3] at this
      convert this using 1
      cases out.key <;> simp only [Option.toList_none, List.nil_append, Option.map_none,
          Option.toList_some, List.cons_append, List.map_cons, Option.map_some]
    | recv msg out hs =>
      obtain ⟨σ₁, h1, h2⟩ := recv_refines P hP _ σ h msg out hs
      obtain ⟨σ₂, hrun, h₂⟩ := ih h2
      refine ⟨σ₂, ?_, h₂⟩
      have := Braid.Run.cons (Braid.Step.recv σ σ₁ (absMsg msg) _ h1) hrun
      convert this using 1
      cases out.key <;> simp only [Option.toList_none, List.nil_append, Option.map_none,
          Option.toList_some, List.cons_append, List.map_cons, Option.map_some]

end spqr.v1.chunked.states
