/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Lacramioara Astefanoaei
-/
module

public import Spqr.Specs.Braid.StateMachine.Refinement
public import Spqr.Specs.Encoding.Polynomial.PolyEncoder.FunctionalModels
public import Spqr.Specs.Encoding.Polynomial.PolyDecoder.FunctionalModels
public import Spqr.Specs.Encoding.Polynomial.PolyEncoder.NextChunk
public import Spqr.Specs.Encoding.Polynomial.PolyEncoder.SlotSize
import Spqr.Auxiliary.Aeneas.SpecImpExists
import Spqr.Auxiliary.Aeneas.Array
import Spqr.Specs.Encoding.Polynomial.PolyEncoder.EncodeBytes
import Spqr.Specs.Encoding.Polynomial.PolyDecoder.New
import Spqr.Specs.Encoding.Polynomial.PolyDecoder.AddChunk
import Spqr.Specs.Encoding.Polynomial.PolyDecoder.DecodedMessage.Length
import Spqr.Specs.IncrementalMlkem768.Generate
import Spqr.Specs.IncrementalMlkem768.Encaps1
import Spqr.Specs.IncrementalMlkem768.Encaps2
import Spqr.Specs.IncrementalMlkem768.HEADER_SIZE
import Spqr.Specs.IncrementalMlkem768.CIPHERTEXT1_SIZE
import Spqr.Specs.IncrementalMlkem768.CIPHERTEXT2_SIZE
import Spqr.Specs.IncrementalMlkem768.ENCAPSULATION_KEY_SIZE
import Spqr.Specs.Authenticator.Authenticator.New
import Spqr.Specs.Authenticator.Authenticator.Update
import Spqr.Specs.Authenticator.Authenticator.MacHdr
import Spqr.Specs.Authenticator.Authenticator.MacCt
import Spqr.Specs.Authenticator.Authenticator.MACSIZE
import Spqr.Specs.V1.Chunked.SendCt.SendCt2Encoder
import Spqr.Specs.V1.Chunked.States.States.InitA
import Spqr.Specs.V1.Chunked.States.States.InitB
import Spqr.Specs.Aeneas.ResultExpect
import Spqr.Specs.Aeneas.VecAppend
import Spqr.Specs.Aeneas.VecClone
import Spqr.Specs.Aeneas.VecExtendFromSlice
import Spqr.Specs.Aeneas.VecAsSlice
import Spqr.Specs.Aeneas.SliceListToVec
import Spqr.Specs.Aeneas.SliceConcatListAux
import Spqr.Auxiliary.Aeneas.Slice

/-! # The reachability invariant of the chunked `States` machine

`Inv s` collects the sizes that every state reached from `init_a` or `init_b` has: 32-byte
authenticator keys, the ML-KEM 768 lengths of the stored byte vectors, the slot size of every
encoder and the point count, completion flag and sortedness of every decoder. `init_a_ok` and
`init_b_ok` show that the initial states satisfy it, and `inv_step` that every successful
`send`, with any RNG, and every successful `recv`, of any message, keeps it.

The sizes of `generate` and `encaps1` come from `generate_ok_lengths` and `encaps1_ok_lengths`.
`generate_spec` and `encaps1_spec` assume that `fill_bytes` succeeds on every input. These two
lemmas use only the one call of the run, so `inv_step` holds for any RNG.

**Source**: spqr/src/v1/chunked/states.rs:58-64, spqr/src/v1/chunked/states.rs:115-533 -/

@[expose] public section

open Aeneas Aeneas.Std Result BraidModel

namespace spqr.v1.chunked.states

open WP

/-- Both keys of the authenticator have 32 bytes. -/
def AuthInv (a : authenticator.Authenticator) : Prop :=
  a.root_key.length = 32 ∧ a.mac_key.length = 32

/-- An encoder of a message of `32 * n` bytes: in the `Points` phase every slot holds `n`
points, and in the `Polys` phase every slot holds a polynomial with `n` coefficients. -/
def EncoderInv (n : Nat) (e : encoding.polynomial.PolyEncoder) : Prop :=
  (∀ pts, e.s = .Points pts → ∀ j < 16, (pts[j]!).value.length = n) ∧
  (∀ polys, e.s = .Polys polys → ∀ j < 16, (polys[j]!).coefficients.length = n)

/-- A decoder of a message of `2 * m` bytes: it needs `m` points, is not marked complete, and
every slot has strictly increasing abscissae. -/
def DecoderInv (m : Nat) (d : encoding.polynomial.PolyDecoder) : Prop :=
  d.pts_needed.val = m ∧ d.is_complete = false ∧
    encoding.polynomial.PolyDecoder.PointsValid d.pts

/-- The reachability invariant of the chunked `States` machine. Every state has a 32-byte root
key and MAC key. Stored bytes have their ML-KEM 768 lengths: `dk` 2400, `ek` 1152, `hdr` 64,
`ct1` 960 and `es` 2080. Encoders hold 3 (header and MAC), 36 (`ek`), 30 (`ct1`) or 5 (`ct2`
and MAC) points or coefficients per slot. Decoders need 48 (header and MAC), 576 (`ek`),
480 (`ct1`) or 80 (`ct2` and MAC) points. -/
def Inv : States → Prop
  | .KeysUnsampled s => AuthInv s.uc.auth
  | .KeysSampled s =>
    AuthInv s.uc.auth ∧ s.uc.dk.length = 2400 ∧ s.uc.ek.length = 1152 ∧
      EncoderInv 3 s.sending_hdr
  | .HeaderSent s =>
    AuthInv s.uc.auth ∧ s.uc.dk.length = 2400 ∧ EncoderInv 36 s.sending_ek ∧
      DecoderInv 480 s.receiving_ct1
  | .Ct1Received s =>
    AuthInv s.uc.auth ∧ s.uc.dk.length = 2400 ∧ s.uc.ct1.length = 960 ∧
      EncoderInv 36 s.sending_ek
  | .EkSentCt1Received s =>
    AuthInv s.uc.auth ∧ s.uc.dk.length = 2400 ∧ s.uc.ct1.length = 960 ∧
      DecoderInv 80 s.receiving_ct2
  | .NoHeaderReceived s => AuthInv s.uc.auth ∧ DecoderInv 48 s.receiving_hdr
  | .HeaderReceived s =>
    AuthInv s.uc.auth ∧ s.uc.hdr.length = 64 ∧ DecoderInv 576 s.receiving_ek
  | .Ct1Sampled s =>
    AuthInv s.uc.auth ∧ s.uc.hdr.length = 64 ∧ s.uc.es.length = 2080 ∧
      s.uc.ct1.length = 960 ∧ EncoderInv 30 s.sending_ct1 ∧ DecoderInv 576 s.receiving_ek
  | .EkReceivedCt1Sampled s =>
    AuthInv s.uc.auth ∧ s.uc.es.length = 2080 ∧ s.uc.ek.length = 1152 ∧
      s.uc.ct1.length = 960 ∧ EncoderInv 30 s.sending_ct1
  | .Ct1Acknowledged s =>
    AuthInv s.uc.auth ∧ s.uc.hdr.length = 64 ∧ s.uc.es.length = 2080 ∧
      s.uc.ct1.length = 960 ∧ DecoderInv 576 s.receiving_ek
  | .Ct2Sampled s => AuthInv s.uc.auth ∧ EncoderInv 5 s.sending_ct2

/-- An encoder that satisfies `EncoderInv n` with `n` one of 3, 5, 30 and 36 satisfies the
premises of `next_chunk_spec`, and of `PolyEncoder.into_pb_spec` and the encoder round trip:
no slot is empty, and twice the slot size fits in `usize`. -/
theorem EncoderInv.ready {n : Nat} {e : encoding.polynomial.PolyEncoder}
    (hn : n = 3 ∨ n = 5 ∨ n = 30 ∨ n = 36) (h : EncoderInv n e) :
    encoding.polynomial.PolyEncoder.NextChunkReady e ∧
      (∀ pts, e.s = .Points pts → ∀ j < 16, (pts[j]!).value.val ≠ []) ∧
      encoding.polynomial.PolyEncoder.FunctionalModels.WellFormed e := by
  obtain ⟨hpts, hpolys⟩ := h
  have hn1 : 1 ≤ n ∧ n ≤ 36 := by omega
  refine ⟨⟨fun pts hp j hj => ?_, fun polys hp j hj => ?_⟩, fun pts hp j hj hv => ?_, ?_⟩
  · simp only [hpts pts hp j hj]; omega
  · rw [hpolys polys hp j hj]; scalar_tac
  · have := hpts pts hp j hj
    simp only [alloc.vec.Vec.length, hv, List.length_nil] at this; omega
  · unfold encoding.polynomial.PolyEncoder.FunctionalModels.WellFormed
    split
    · rename_i pts hp
      exact Array.forall_mem_of_forall_lt (P := fun p : encoding.polynomial.Point =>
        2 * p.value.length ≤ Usize.max)
        fun j hj => by simp only [hpts pts hp j hj]; scalar_tac
    · rename_i polys hp
      refine Array.forall_mem_of_forall_lt
        (P := fun p => encoding.polynomial.Poly.FunctionalModels.WellFormed p) fun j hj => ?_
      have := hpolys polys hp j hj
      refine ⟨fun he => ?_, ?_⟩
      · simp only [alloc.vec.Vec.length, he, List.length_nil] at this; omega
      · rw [this]; scalar_tac

/-- A decoder that satisfies `DecoderInv m` has at most 65536 points per slot. So it satisfies
the premises of `add_chunk_spec_valid`, `decoded_message_spec`,
`PolyDecoder.into_pb_spec` and the decoder round trip. -/
theorem DecoderInv.ready {m : Nat} {d : encoding.polynomial.PolyDecoder} (hm : m ≤ 576)
    (h : DecoderInv m d) :
    (∀ sl ∈ d.pts.val, sl.length ≤ 65536) ∧
      (∀ k < 16, (d.pts[k]!).length + 17 ≤ Usize.max) ∧
      2 * d.pts_needed.val ≤ Usize.max ∧
      (∀ sl ∈ d.pts.val, 4 * sl.length ≤ Usize.max) ∧
      encoding.polynomial.PolyDecoder.FunctionalModels.WellFormed d := by
  obtain ⟨hpn, -, hv⟩ := h
  have hs : ∀ sl ∈ d.pts.val, sl.length ≤ 65536 := fun sl hsl =>
    encoding.polynomial.PolyDecoder.SlotSorted.length_le (hv sl hsl)
  refine ⟨hs, fun k hk => ?_, by rw [hpn]; scalar_tac, fun sl hsl => by
    have := hs sl hsl; scalar_tac, by rw [hpn]; scalar_tac, hv⟩
  have hk' : k < d.pts.val.length := by
    have := d.pts.property; simp only [UScalar.ofNatCore_val_eq] at this; omega
  have := hs _ (List.getElem_mem hk')
  rw [Array.getElem!_Nat_eq, getElem!_pos d.pts.val k hk']
  scalar_tac

/-! ## Support lemmas: one call at a time -/

open encoding.polynomial in
/-- A decoder that `PolyDecoder::new` creates for `2 * m` bytes satisfies `DecoderInv m`. -/
theorem DecoderInv.new {n : Std.Usize} {m : Nat} {d : PolyDecoder} (hn : n.val = 2 * m)
    (h : PolyDecoder.Insts.SpqrEncodingDecoder.new n = ok (.Ok d)) : DecoderInv m d := by
  have h1 := post_of_ok (PolyDecoder.Insts.SpqrEncodingDecoder.new_spec n) h
  have h2 := post_of_ok (PolyDecoder.Insts.SpqrEncodingDecoder.new_spec_valid n) h
  simp only [hn, Nat.mul_mod_right, ↓reduceIte] at h1
  obtain ⟨-, -, hc⟩ := h1
  refine ⟨?_, hc, h2⟩
  rw [PolyDecoder.Insts.SpqrEncodingDecoder.new_pts_needed (by omega) h]; omega

open encoding.polynomial in
/-- `add_chunk` keeps `DecoderInv`. -/
theorem DecoderInv.add_chunk {m : Nat} {d d' : PolyDecoder} {c : encoding.Chunk}
    (h : DecoderInv m d) (hm : m ≤ 576)
    (ha : PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk d c = ok d') : DecoderInv m d' := by
  obtain ⟨-, hcap, -, -, -⟩ := DecoderInv.ready hm h
  obtain ⟨hpn, hc, hv⟩ := h
  have hov : c.index * 16 + 16 ≤ Usize.max := by scalar_tac
  obtain ⟨hp', hc', -⟩ := post_of_ok (PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk_spec d c hov
    hcap) ha
  have hv' := post_of_ok (PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk_spec_valid d c hov
    hcap hv) ha
  exact ⟨by rw [hp', hpn], by rw [hc', hc], hv'⟩

open encoding.polynomial in
/-- An encoder that `encode_bytes` builds from a message of `32 * n` bytes satisfies
`EncoderInv n`. -/
theorem EncoderInv.encode {msg : Slice Std.U8} {n : Nat} {e : PolyEncoder}
    (hl : msg.length = 32 * n) (hn : n ≤ 36)
    (h : PolyEncoder.Insts.SpqrEncodingEncoder.encode_bytes msg = ok (.Ok e)) :
    EncoderInv n e := by
  have := post_of_ok (PolyEncoder.Insts.SpqrEncodingEncoder.encode_bytes_spec msg
    (by rw [hl]; omega) (by rw [hl]; omega)) h
  obtain ⟨idx, s⟩ := e
  cases s with
  | Polys _ => exact this.elim
  | Points pts =>
    obtain ⟨-, hlen, -⟩ := this
    refine ⟨fun pts' hp j hj => ?_, fun _ hp => by cases hp⟩
    cases hp
    rw [hlen j hj, hl]
    have h1 : 32 * n / 2 % 16 = 0 := by omega
    have h2 : 32 * n / 2 / 16 = n := by omega
    simp only [h1, Nat.not_lt_zero, ↓reduceIte, h2]

/-- `next_chunk` keeps `EncoderInv`. -/
theorem EncoderInv.next_chunk {n : Nat} {e e' : encoding.polynomial.PolyEncoder}
    {c : encoding.Chunk} (h : EncoderInv n e)
    (hc : encoding.polynomial.PolyEncoder.Insts.SpqrEncodingEncoder.next_chunk e = ok (c, e')) :
    EncoderInv n e' :=
  encoding.polynomial.PolyEncoder.next_chunk_slotSize h hc

/-- `EncoderInv n` is the slot size predicate `PolyEncoder.SlotSize n`. -/
theorem EncoderInv_iff_slotSize {n : Nat} {e : encoding.polynomial.PolyEncoder} :
    EncoderInv n e ↔ encoding.polynomial.PolyEncoder.SlotSize n e := Iff.rfl

/-- A successful `Authenticator::update` gives 32-byte keys. -/
theorem AuthInv.update {a a' : authenticator.Authenticator} {ep : Std.U64} {k : Slice Std.U8}
    (h : authenticator.Authenticator.update a ep k = ok a') : AuthInv a' := by
  obtain ⟨h1, h2, -⟩ := post_of_ok (authenticator.Authenticator.update_spec _ _ _
    (authenticator.Authenticator.length_le_of_update_ok h)) h
  exact ⟨h1, h2⟩

/-- If `generate` returns `ok (k, rng')`, then `k.dk`, `k.ek` and `k.hdr` have 2400, 1152 and 64
bytes. -/
theorem generate_ok_lengths {R : Type} (i₁ : rand_1.rng.Rng R) (i₂ : rand_core_1.CryptoRng R)
    {rng rng' : R} {k : incremental_mlkem768.Keys}
    (h : incremental_mlkem768.generate i₁ i₂ rng = ok (k, rng')) :
    k.dk.length = 2400 ∧ k.ek.length = 1152 ∧ k.hdr.length = 64 := by
  unfold incremental_mlkem768.generate at h
  simp only [Result.bind_eq_ok] at h
  obtain ⟨⟨sl, bk⟩, hsl, h⟩ := h
  simp only [uncurry_apply_pair, Result.bind_eq_ok] at h
  obtain ⟨⟨r1, s1⟩, hf, h⟩ := h
  let i₁' : rand_1.rng.Rng R :=
    ⟨{ i₁.rand_core_1RngCoreInst with fill_bytes := fun _ _ => ok (r1, s1) }⟩
  have h' : incremental_mlkem768.generate i₁' i₂ rng = ok (k, rng') := by
    unfold incremental_mlkem768.generate
    simp only [Result.bind_eq_ok]
    refine ⟨(sl, bk), hsl, ?_⟩
    simp only [uncurry_apply_pair, Result.bind_eq_ok]
    exact ⟨(r1, s1), rfl, h⟩
  obtain ⟨-, -, -, hh, he, hd⟩ := post_of_ok (incremental_mlkem768.generate_spec i₁' i₂ rng
    (fun _ _ => (WP.spec_ok _).mpr trivial)) h'
  refine ⟨?_, ?_, ?_⟩
  · rw [hd]; decide
  · rw [he]; decide
  · rw [hh]; decide

/-- If `hdr` has 64 bytes and `encaps1` on `hdr` returns `ok ((ct1, es, ss), rng')`, then `ct1` has
960 bytes and `es` has 2080 bytes. -/
theorem encaps1_ok_lengths {R : Type} (i₁ : rand_1.rng.Rng R) (i₂ : rand_core_1.CryptoRng R)
    {hdr ct1 es ss : alloc.vec.Vec Std.U8} {rng rng' : R} (hh : hdr.length = 64)
    (h : incremental_mlkem768.encaps1 i₁ i₂ hdr rng = ok ((ct1, es, ss), rng')) :
    ct1.length = 960 ∧ es.length = 2080 := by
  unfold incremental_mlkem768.encaps1 at h
  simp only [Result.bind_eq_ok] at h
  obtain ⟨⟨sl, bk⟩, hsl, h⟩ := h
  simp only [uncurry_apply_pair, Result.bind_eq_ok] at h
  obtain ⟨⟨r1, s1⟩, hf, h⟩ := h
  let i₁' : rand_1.rng.Rng R :=
    ⟨{ i₁.rand_core_1RngCoreInst with fill_bytes := fun _ _ => ok (r1, s1) }⟩
  have h' : incremental_mlkem768.encaps1 i₁' i₂ hdr rng = ok ((ct1, es, ss), rng') := by
    unfold incremental_mlkem768.encaps1
    simp only [Result.bind_eq_ok]
    refine ⟨(sl, bk), hsl, ?_⟩
    simp only [uncurry_apply_pair, Result.bind_eq_ok]
    exact ⟨(r1, s1), rfl, h⟩
  obtain ⟨-, hc, he, -⟩ := post_of_ok (incremental_mlkem768.encaps1_spec i₁' i₂ hdr rng
    (by simp only [alloc.vec.Vec.length] at hh; omega)
    (fun _ _ => (WP.spec_ok _).mpr trivial)) h'
  exact ⟨hc, by rw [he]; decide⟩

/-! ## `send` keeps the invariant -/

/-- Every successful `send`, with any RNG, keeps `Inv`. -/
theorem inv_send {R : Type} (i₁ : rand_1.rng.Rng R) (i₂ : rand_core_1.CryptoRng R)
    (s : States) (h : Inv s) (rng rng' : R) (out : Send)
    (hs : States.send i₁ i₂ s rng = ok (.Ok out, rng')) : Inv out.state := by
  cases s <;> simp only [Inv] at h <;> simp only [States.send,
    Result.bind_eq_ok, Result.ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hs
  case KeysSampled s =>
    obtain ⟨ep, -, ⟨s1, c⟩, hc, hout⟩ := hs
    simp only [send_ek.KeysSampled.send_hdr_chunk, Result.bind_eq_ok] at hc
    obtain ⟨⟨c', e'⟩, hn, hc⟩ := hc
    simp only [uncurry_apply_pair, ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hc hout
    obtain ⟨rfl, rfl⟩ := hc
    obtain ⟨rfl, -⟩ := hout
    obtain ⟨ha, hd, he, henc⟩ := h
    exact ⟨ha, hd, he, henc.next_chunk hn⟩
  case HeaderSent s =>
    obtain ⟨ep, -, ⟨s1, c⟩, hc, hout⟩ := hs
    simp only [send_ek.HeaderSent.send_ek_chunk, Result.bind_eq_ok] at hc
    obtain ⟨⟨c', e'⟩, hn, hc⟩ := hc
    simp only [uncurry_apply_pair, ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hc hout
    obtain ⟨rfl, rfl⟩ := hc
    obtain ⟨rfl, -⟩ := hout
    obtain ⟨ha, hd, henc, hdec⟩ := h
    exact ⟨ha, hd, henc.next_chunk hn, hdec⟩
  case Ct1Received s =>
    obtain ⟨ep, -, ⟨s1, c⟩, hc, hout⟩ := hs
    simp only [send_ek.Ct1Received.send_ek_chunk, Result.bind_eq_ok] at hc
    obtain ⟨⟨c', e'⟩, hn, hc⟩ := hc
    simp only [uncurry_apply_pair, ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hc hout
    obtain ⟨rfl, rfl⟩ := hc
    obtain ⟨rfl, -⟩ := hout
    obtain ⟨ha, hd, hc1, henc⟩ := h
    exact ⟨ha, hd, hc1, henc.next_chunk hn⟩
  case Ct1Sampled s =>
    obtain ⟨ep, -, ⟨s1, c⟩, hc, hout⟩ := hs
    simp only [send_ct.Ct1Sampled.send_ct1_chunk, Result.bind_eq_ok] at hc
    obtain ⟨⟨c', e'⟩, hn, hc⟩ := hc
    simp only [uncurry_apply_pair, ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hc hout
    obtain ⟨rfl, rfl⟩ := hc
    obtain ⟨rfl, -⟩ := hout
    obtain ⟨ha, hh, hes, hc1, henc, hdec⟩ := h
    exact ⟨ha, hh, hes, hc1, henc.next_chunk hn, hdec⟩
  case EkReceivedCt1Sampled s =>
    obtain ⟨ep, -, ⟨s1, c⟩, hc, hout⟩ := hs
    simp only [send_ct.EkReceivedCt1Sampled.send_ct1_chunk, Result.bind_eq_ok] at hc
    obtain ⟨⟨c', e'⟩, hn, hc⟩ := hc
    simp only [uncurry_apply_pair, ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hc hout
    obtain ⟨rfl, rfl⟩ := hc
    obtain ⟨rfl, -⟩ := hout
    obtain ⟨ha, hes, hek, hc1, henc⟩ := h
    exact ⟨ha, hes, hek, hc1, henc.next_chunk hn⟩
  case Ct2Sampled s =>
    obtain ⟨ep, -, ⟨s1, c⟩, hc, hout⟩ := hs
    simp only [send_ct.Ct2Sampled.send_ct2_chunk, Result.bind_eq_ok] at hc
    obtain ⟨⟨c', e'⟩, hn, hc⟩ := hc
    simp only [uncurry_apply_pair, ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at hc hout
    obtain ⟨rfl, rfl⟩ := hc
    obtain ⟨rfl, -⟩ := hout
    obtain ⟨ha, henc⟩ := h
    exact ⟨ha, henc.next_chunk hn⟩
  case EkSentCt1Received s =>
    obtain ⟨ep, -, hout⟩ := hs
    obtain ⟨rfl, -⟩ := hout
    exact h
  case NoHeaderReceived s =>
    obtain ⟨ep, -, hout⟩ := hs
    obtain ⟨rfl, -⟩ := hout
    exact h
  case Ct1Acknowledged s =>
    obtain ⟨ep, -, hout⟩ := hs
    obtain ⟨rfl, -⟩ := hout
    exact h
  case KeysUnsampled s =>
    obtain ⟨ep, -, ⟨⟨s1, c⟩, rng1⟩, hc, hout⟩ := hs
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
    subst h1 h2 h3 h4
    obtain ⟨⟨ts1, z⟩, hap, hrest⟩ := hrest
    simp only [uncurry_apply_pair] at hrest
    simp only [Result.bind_eq_ok] at hrest
    obtain ⟨enc0, henc, sh, hsh, ⟨c', e'⟩, hn, hfin⟩ := hrest
    simp only [uncurry_apply_pair, ok.injEq, Prod.mk.injEq, and_assoc] at hfin
    obtain ⟨rfl, rfl, -⟩ := hfin
    have hsh' := core.result.Result.eq_Ok_of_expect_eq_ok hsh; subst hsh'
    obtain ⟨hdk, hek, hhdr⟩ := generate_ok_lengths i₁ i₂ hg
    obtain ⟨hr, hmk⟩ := h
    have hml := (post_of_ok (authenticator.Authenticator.mac_hdr_spec _ _ _
      (by rw [hmk]; scalar_tac) (by
        simp only [alloc.vec.Vec.deref, Slice.length, Slice.from_val]
        simp only [alloc.vec.Vec.length] at hhdr; rw [hhdr]; scalar_tac)) hm).1
    have hts := alloc.vec.Vec.append_ok_val hap
    refine ⟨⟨hr, hmk⟩, hdk, hek, EncoderInv.next_chunk (EncoderInv.encode ?_ (by omega) henc) hn⟩
    simp only [alloc.vec.Vec.deref, Slice.length, Slice.from_val, hts, List.length_append]
    simp only [alloc.vec.Vec.length] at hhdr hml
    rw [hhdr, hml, authenticator.Authenticator.MACSIZE_spec]
  case HeaderReceived s =>
    obtain ⟨ep, -, ⟨⟨s1, c, k⟩, rng1⟩, hc, hout⟩ := hs
    simp only [uncurry_apply_pair, ok.injEq, Prod.mk.injEq,
        core.result.Result.Ok.injEq] at hout; obtain ⟨rfl, -⟩ := hout
    simp only [send_ct.HeaderReceived.send_ct1_chunk, Result.bind_eq_ok] at hc
    obtain ⟨⟨⟨uc, ct1, k'⟩, r1⟩, hsc, hrest⟩ := hc
    simp only [uncurry_apply_pair] at hrest
    simp only [Result.bind_eq_ok] at hrest
    obtain ⟨enc0, henc, sh, hsh, ⟨c', e'⟩, hn, hfin⟩ := hrest
    simp only [uncurry_apply_pair, ok.injEq, Prod.mk.injEq, and_assoc] at hfin
    obtain ⟨rfl, rfl, rfl, -⟩ := hfin
    have hsh' := core.result.Result.eq_Ok_of_expect_eq_ok hsh; subst hsh'
    simp only [unchunked.send_ct.HeaderReceived.send_ct1, Result.bind_eq_ok] at hsc
    obtain ⟨⟨⟨ct1₀, es, ss₀⟩, rk⟩, he1, hsc⟩ := hsc
    simp only [alloc.slice.Slice.concat_eq, Slice.Insts.AllocSliceConcatTVec.concat_eq,
        Std.bind_assoc, uncurry_apply_pair] at hsc
    simp only [Result.bind_eq_ok] at hsc
    obtain ⟨_, -, _, -, _, -, _, -, l, -, info, -, _, -, sec, -, a', hu, v, hv, hsc⟩ := hsc
    have hv' := post_of_ok (alloc.vec.CloneVec.clone_U8_spec _) hv
    subst hv'
    simp only [Result.ok.injEq, Prod.mk.injEq] at hsc
    obtain ⟨⟨h6, rfl, rfl⟩, -⟩ := hsc
    subst h6
    obtain ⟨-, hh, hdec⟩ := h
    obtain ⟨hc1, hes⟩ := encaps1_ok_lengths i₁ i₂ hh he1
    refine ⟨AuthInv.update hu, hh, hes, hc1,
      EncoderInv.next_chunk (EncoderInv.encode ?_ (by omega) henc) hn, hdec⟩
    simp only [alloc.vec.Vec.deref, Slice.length, Slice.from_val]
    simp only [alloc.vec.Vec.length] at hc1
    rw [hc1]

/-! ## `recv` keeps the invariant -/

/-- Assume that `uc` has 32-byte keys and the ML-KEM 768 sizes. If `send_ct2` and
`send_ct2_encoder` succeed, the new authenticator has 32-byte keys and the encoder satisfies
`EncoderInv 5`. -/
theorem ct2_encoder_inv (uc : v1.unchunked.send_ct.Ct1SentEkReceived)
    (u2 : v1.unchunked.send_ct.Ct2Sent) (ct2 mac : alloc.vec.Vec Std.U8)
    (pe : encoding.polynomial.PolyEncoder) (ha : AuthInv uc.auth) (hek : uc.ek.length = 1152)
    (hes : uc.es.length = 2080) (hct1 : uc.ct1.length = 960)
    (h1 : v1.unchunked.send_ct.Ct1SentEkReceived.send_ct2 uc = ok (u2, ct2, mac))
    (h2 : send_ct.send_ct2_encoder ct2.deref mac.deref = ok pe) :
    AuthInv u2.auth ∧ EncoderInv 5 pe := by
  simp only [v1.unchunked.send_ct.Ct1SentEkReceived.send_ct2, Result.bind_eq_ok] at h1
  obtain ⟨c2, hc2, ct1', hct1', m, hm, h1⟩ := h1
  simp only [Result.ok.injEq, Prod.mk.injEq] at h1
  obtain ⟨rfl, rfl, rfl⟩ := h1
  refine ⟨ha, ?_⟩
  have hc2l := (post_of_ok (incremental_mlkem768.encaps2_spec _ _ hek hes) hc2).2
  have hct := alloc.vec.Vec.extend_from_slice_U8_ok_val hct1'
  have hml := (post_of_ok (authenticator.Authenticator.mac_ct_spec _ _ _
    (by rw [ha.2]; scalar_tac) (by
      simp only [alloc.vec.Vec.deref, Slice.length, Slice.from_val, hct, List.length_append]
      simp only [alloc.vec.Vec.length] at hct1 hc2l
      rw [hct1, hc2l]; scalar_tac)) hm).1
  obtain ⟨-, pts, hps, hpl, -⟩ := post_of_ok (send_ct.send_ct2_encoder_spec _ _
    (by simpa only [alloc.vec.Vec.deref, Slice.length, Slice.from_val] using hc2l)
    (by simpa only [alloc.vec.Vec.deref, Slice.length, Slice.from_val] using hml)) h2
  refine ⟨fun pts' hp j hj => ?_, fun _ hp => by rw [hps] at hp; cases hp⟩
  rw [hps] at hp; cases hp
  exact hpl j hj

/-- `recv_ct1_ack` moves to `Ct2Sampled` and keeps the invariant. -/
theorem recv_ct1_ack_inv (st : send_ct.EkReceivedCt1Sampled) (ep : Std.U64)
    (st' : send_ct.Ct2Sampled) (h : Inv (.EkReceivedCt1Sampled st))
    (hr : send_ct.EkReceivedCt1Sampled.recv_ct1_ack st ep = ok st') :
    Inv (.Ct2Sampled st') := by
  simp only [send_ct.EkReceivedCt1Sampled.recv_ct1_ack, massert, Result.bind_eq_ok] at hr
  obtain ⟨_, -, ⟨u2, ct2, mac⟩, h1, hr⟩ := hr
  simp only [uncurry_apply_pair, Result.bind_eq_ok] at hr
  obtain ⟨pe, h2, hr⟩ := hr
  simp only [Result.ok.injEq] at hr
  subst hr
  obtain ⟨ha, hes, hek, hct1, -⟩ := h
  exact ct2_encoder_inv _ _ _ _ _ ha hek hes hct1 h1 h2

/-- `Ct1Sent::recv_ek` keeps the epoch, authenticator, `es` and `ct1`, and stores `ek`. -/
theorem recv_ek_eq (uc : v1.unchunked.send_ct.Ct1Sent) (ep : Std.U64)
    (ek : alloc.vec.Vec Std.U8) (v : v1.unchunked.send_ct.Ct1SentEkReceived)
    (h : v1.unchunked.send_ct.Ct1Sent.recv_ek uc ep ek = ok (.Ok v)) :
    v = { epoch := uc.epoch, auth := uc.auth, es := uc.es, ek, ct1 := uc.ct1 } := by
  simp only [v1.unchunked.send_ct.Ct1Sent.recv_ek, massert, Result.bind_eq_ok] at h
  obtain ⟨_, -, b, -, h⟩ := h
  cases b with
  | false => simp only [Bool.false_eq_true, ↓reduceIte, ok.injEq, reduceCtorEq] at h
  | true =>
    simp only [↓reduceIte, Result.ok.injEq, core.result.Result.Ok.injEq] at h
    exact h.symm

open encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder
  (add_chunk_pts_needed decoded_message_length) in
/-- `Ct1Acknowledged::recv_ek_chunk` keeps the invariant: the state stays `Ct1Acknowledged`
while `ek` is incomplete, and moves to `Ct2Sampled` when it completes. -/
theorem ct1Acknowledged_chunk_inv (st : send_ct.Ct1Acknowledged) (c : encoding.Chunk)
    (v : send_ct.Ct1AcknowledgedRecvChunk) (h : Inv (.Ct1Acknowledged st))
    (hr : send_ct.Ct1Acknowledged.recv_ek_chunk st st.uc.epoch c = ok (.Ok v)) :
    Inv (match v with
      | .StillReceiving s => .Ct1Acknowledged s
      | .Done s => .Ct2Sampled s) := by
  obtain ⟨ha, hh, hes, hct1, hdec⟩ := h
  simp only [send_ct.Ct1Acknowledged.recv_ek_chunk, Result.bind_eq_ok] at hr
  obtain ⟨d', hadd, o, ho, hr⟩ := hr
  have hdec' := hdec.add_chunk (by norm_num) hadd
  cases o with
  | none =>
    simp only [Result.ok.injEq, core.result.Result.Ok.injEq] at hr; subst hr
    exact ⟨ha, hh, hes, hct1, hdec'⟩
  | some m =>
    simp only [Result.bind_eq_ok] at hr
    obtain ⟨r, hr', hr⟩ := hr
    replace hr := core.result.Result.Insts.CoreOpsTry.continue_of_ok hr fun _ => rfl
    obtain ⟨val, rfl, hr⟩ := hr
    have hv := recv_ek_eq _ _ _ _ hr'
    subst hv
    simp only [Result.bind_eq_ok] at hr
    obtain ⟨⟨u2, ct2, mac⟩, h1, hr⟩ := hr
    simp only [uncurry_apply_pair, Result.bind_eq_ok] at hr
    obtain ⟨pe, h2, hr⟩ := hr
    simp only [Result.ok.injEq, core.result.Result.Ok.injEq] at hr; subst hr
    have hml : m.length = 1152 := by
      simp only [alloc.vec.Vec.length]
      rw [decoded_message_length ho, add_chunk_pts_needed hadd, hdec.1]
    exact ct2_encoder_inv _ _ _ _ _ ha hml hes hct1 h1 h2

open encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder
  (add_chunk_pts_needed decoded_message_length) in
/-- `Ct1Sampled::recv_ek_chunk` keeps the invariant, with or without an acknowledgement. -/
theorem ct1Sampled_chunk_inv (st : send_ct.Ct1Sampled) (c : encoding.Chunk) (ack : Bool)
    (v : send_ct.Ct1SampledRecvChunk) (h : Inv (.Ct1Sampled st))
    (hr : send_ct.Ct1Sampled.recv_ek_chunk st st.uc.epoch c ack = ok (.Ok v)) :
    Inv (match v with
      | .StillReceivingStillSending s => .Ct1Sampled s
      | .StillReceiving s => .Ct1Acknowledged s
      | .StillSending s => .EkReceivedCt1Sampled s
      | .Done s => .Ct2Sampled s) := by
  obtain ⟨ha, hh, hes, hct1, henc, hdec⟩ := h
  simp only [send_ct.Ct1Sampled.recv_ek_chunk, Result.bind_eq_ok] at hr
  obtain ⟨d', hadd, o, ho, hr⟩ := hr
  have hdec' := hdec.add_chunk (by norm_num) hadd
  cases o with
  | none =>
    cases ack <;>
      simp only [Bool.false_eq_true, ↓reduceIte, Result.ok.injEq,
        core.result.Result.Ok.injEq] at hr <;> subst hr
    · exact ⟨ha, hh, hes, hct1, henc, hdec'⟩
    · exact ⟨ha, hh, hes, hct1, hdec'⟩
  | some m =>
    simp only [Result.bind_eq_ok] at hr
    obtain ⟨r, hr', hr⟩ := hr
    replace hr := core.result.Result.Insts.CoreOpsTry.continue_of_ok hr fun _ => rfl
    obtain ⟨val, rfl, hr⟩ := hr
    have hv := recv_ek_eq _ _ _ _ hr'
    subst hv
    have hml : m.length = 1152 := by
      simp only [alloc.vec.Vec.length]
      rw [decoded_message_length ho, add_chunk_pts_needed hadd, hdec.1]
    cases ack
    · simp only [Bool.false_eq_true, ↓reduceIte, Result.ok.injEq,
        core.result.Result.Ok.injEq] at hr
      subst hr
      exact ⟨ha, hes, hml, hct1, henc⟩
    · simp only [↓reduceIte, Result.bind_eq_ok] at hr
      obtain ⟨⟨u2, ct2, mac⟩, h1, hr⟩ := hr
      simp only [uncurry_apply_pair, Result.bind_eq_ok] at hr
      obtain ⟨pe, h2, hr⟩ := hr
      simp only [Result.ok.injEq, core.result.Result.Ok.injEq] at hr; subst hr
      exact ct2_encoder_inv _ _ _ _ _ ha hml hes hct1 h1 h2

open encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder
  (add_chunk_pts_needed decoded_message_length) in
/-- If `NoHeaderReceived::recv_hdr_chunk` returns `ok (.Ok v)` on a state that satisfies `Inv`,
the state that `v` holds satisfies `Inv`. -/
theorem noHeaderReceived_chunk_inv (st : send_ct.NoHeaderReceived) (c : encoding.Chunk)
    (v : send_ct.NoHeaderReceivedRecvChunk) (h : Inv (.NoHeaderReceived st))
    (hr : send_ct.NoHeaderReceived.recv_hdr_chunk st st.uc.epoch c = ok (.Ok v)) :
    Inv (match v with
      | .StillReceiving s => .NoHeaderReceived s
      | .Done s => .HeaderReceived s) := by
  obtain ⟨ha, hdec⟩ := h
  simp only [send_ct.NoHeaderReceived.recv_hdr_chunk, massert, Result.bind_eq_ok] at hr
  obtain ⟨_, -, d', hadd, o, ho, hr⟩ := hr
  have hdec' := hdec.add_chunk (by norm_num) hadd
  cases o with
  | none =>
    simp only [Result.ok.injEq, core.result.Result.Ok.injEq] at hr; subst hr
    exact ⟨ha, hdec'⟩
  | some m =>
    simp only [Result.bind_eq_ok] at hr
    obtain ⟨sl, hsl, n, hn, s1, hs1, mac, -, s2, hs2, hdr, hhdr, i1, hi1, dr, hnew, r, hr',
      hr⟩ := hr
    have hn64 : n.val = 64 := by
      rw [post_of_ok incremental_mlkem768.HEADER_SIZE_spec hn]; decide
    have hml : m.val.length = 96 := by
      rw [decoded_message_length ho, add_chunk_pts_needed hadd, hdec.1]
    have hhdrv : hdr.val = m.val.take 64 := by
      rw [Slice.to_vec_U8_ok_val hhdr, Slice.index_range_to_ok_val hs2,
        alloc.vec.Vec.as_slice_ok_val hsl, hn64]
    replace hr := core.result.Result.Insts.CoreOpsTry.continue_of_ok hr fun _ => rfl
    obtain ⟨val, rfl, hr⟩ := hr
    simp only [Result.bind_eq_ok] at hr
    obtain ⟨pd, hpd, hr⟩ := hr
    obtain rfl := core.result.Result.eq_Ok_of_expect_eq_ok hpd
    simp only [Result.ok.injEq, core.result.Result.Ok.injEq] at hr; subst hr
    simp only [v1.unchunked.send_ct.NoHeaderReceived.recv_header, massert,
      Result.bind_eq_ok] at hr'
    obtain ⟨_, -, vr, -, hr'⟩ := hr'
    replace hr' := core.result.Result.Insts.CoreOpsTry.continue_of_ok hr' fun _ => rfl
    obtain ⟨u, rfl, hr'⟩ := hr'
    simp only [Result.ok.injEq, core.result.Result.Ok.injEq] at hr'; subst hr'
    rw [incremental_mlkem768.ENCAPSULATION_KEY_SIZE_eq, ok.injEq] at hi1; subst hi1
    refine ⟨ha, ?_, DecoderInv.new (by rfl) hnew⟩
    simp only [alloc.vec.Vec.length, hhdrv, List.length_take, hml]; rfl

open encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder
  (add_chunk_pts_needed decoded_message_length) in
/-- If `EkSentCt1Received::recv_ct2_chunk` returns `ok (.Ok v)` on a state that satisfies `Inv`,
the state that `v` holds satisfies `Inv`. -/
theorem ekSentCt1Received_chunk_inv (st : send_ek.EkSentCt1Received) (c : encoding.Chunk)
    (v : send_ek.EkSentCt1ReceivedRecvChunk) (h : Inv (.EkSentCt1Received st))
    (hr : send_ek.EkSentCt1Received.recv_ct2_chunk st st.uc.epoch c = ok (.Ok v)) :
    Inv (match v with
      | .StillReceiving s => .EkSentCt1Received s
      | .Done (s, _) => .NoHeaderReceived s) := by
  obtain ⟨ha, hdk, hct1, hdec⟩ := h
  simp only [send_ek.EkSentCt1Received.recv_ct2_chunk, massert, Result.bind_eq_ok] at hr
  obtain ⟨_, -, d', hadd, o, ho, hr⟩ := hr
  have hdec' := hdec.add_chunk (by norm_num) hadd
  cases o with
  | none =>
    simp only [Result.ok.injEq, core.result.Result.Ok.injEq] at hr; subst hr
    exact ⟨ha, hdk, hct1, hdec'⟩
  | some m =>
    simp only [Result.bind_eq_ok] at hr
    obtain ⟨sl, -, n, -, s1, -, mac, -, s2, -, ct2, -, r, hr', hr⟩ := hr
    replace hr := core.result.Result.Insts.CoreOpsTry.continue_of_ok hr fun _ => rfl
    obtain ⟨val, rfl, hr⟩ := hr
    obtain ⟨nh, sec⟩ := val
    simp only [uncurry_apply_pair] at hr
    simp only [Result.bind_eq_ok] at hr
    obtain ⟨i1, hi1, i2, hi2, dr, hnew, pd, hpd, hr⟩ := hr
    obtain rfl := core.result.Result.eq_Ok_of_expect_eq_ok hpd
    simp only [Result.ok.injEq, core.result.Result.Ok.injEq] at hr; subst hr
    simp only [unchunked.send_ek.EkSentCt1Received.recv_ct2, Result.bind_eq_ok] at hr'
    obtain ⟨_, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -, a', hu, _, -, _, -, hr'⟩ := hr'
    replace hr' := core.result.Result.Insts.CoreOpsTry.continue_of_ok hr' fun _ => rfl
    obtain ⟨u, rfl, hr'⟩ := hr'
    simp only [Result.bind_eq_ok] at hr'
    obtain ⟨_, -, _, -, hr'⟩ := hr'
    simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at hr'
    obtain ⟨rfl, rfl⟩ := hr'
    have hi1v := post_of_ok incremental_mlkem768.HEADER_SIZE_spec hi1
    have hhb : Spqr.Mlkem.headerBytes = 64 := by decide
    have hi2v := UScalar.val_of_add_eq_ok hi2
    rw [authenticator.Authenticator.MACSIZE_spec, hi1v, hhb] at hi2v
    exact ⟨AuthInv.update hu, DecoderInv.new (by rw [hi2v]) hnew⟩

open encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder
  (add_chunk_pts_needed decoded_message_length) in
/-- Every successful `recv`, of any message, keeps `Inv`. -/
theorem inv_recv (s : States) (h : Inv s) (msg : Message) (out : Recv)
    (hs : States.recv s msg = ok (.Ok out)) : Inv out.state := by
  rcases Nat.lt_trichotomy msg.epoch.val s.epochOf.val with hlt | heq | hgt
  · rw [recv_of_lt s msg hlt, Result.ok.injEq, core.result.Result.Ok.injEq] at hs
    subst hs
    exact h
  · have heq' : msg.epoch = s.epochOf := UScalar.eq_of_val_eq heq
    by_cases hx : s.Expects msg.payload
    · obtain ⟨e, p⟩ := msg
      simp only at heq' hx hs
      subst heq'
      cases s <;> simp only [Inv] at h <;>
        rcases p with _ | _ | _ | _ | (_ | _) | _ | _ <;>
        simp only [States.Expects] at hx <;>
        simp only [States.recv, States.epochOf, send_ek.KeysSampled.epoch,
          send_ek.HeaderSent.epoch, send_ek.Ct1Received.epoch, send_ek.EkSentCt1Received.epoch,
          send_ct.NoHeaderReceived.epoch, send_ct.Ct1Sampled.epoch,
          send_ct.EkReceivedCt1Sampled.epoch, send_ct.Ct1Acknowledged.epoch, lift,
          core.cmp.impls.OrdU64.cmp, bind_ok, Nat.compare_eq_eq.2 rfl] at hs
      case pos.KeysSampled.Ct1 st c =>
        obtain ⟨ha, hdk, hek, -⟩ := h
        simp only [Result.bind_eq_ok, Result.ok.injEq, core.result.Result.Ok.injEq] at hs
        obtain ⟨st', hst, rfl⟩ := hs
        simp only [send_ek.KeysSampled.recv_ct1_chunk, massert, Result.bind_eq_ok] at hst
        obtain ⟨_, -, n, hn, dr, hnew, d, hexp, d', hadd, ⟨uc, ekv⟩, hse, hst⟩ := hst
        simp only [uncurry_apply_pair] at hst
        simp only [Result.bind_eq_ok] at hst
        obtain ⟨er, her, se, hse', hst⟩ := hst
        simp only [Result.ok.injEq] at hst
        subst hst
        obtain rfl := core.result.Result.eq_Ok_of_expect_eq_ok hexp
        obtain rfl := core.result.Result.eq_Ok_of_expect_eq_ok hse'
        simp only [unchunked.send_ek.HeaderSent.send_ek, Result.ok.injEq, Prod.mk.injEq] at hse
        obtain ⟨rfl, rfl⟩ := hse
        rw [incremental_mlkem768.CIPHERTEXT1_SIZE_eq, ok.injEq] at hn; subst hn
        refine ⟨ha, hdk, EncoderInv.encode ?_ (by norm_num) her,
          (DecoderInv.new (by rfl) hnew).add_chunk (by norm_num) hadd⟩
        simp only [alloc.vec.Vec.deref, Slice.length, Slice.from_val]
        simp only [alloc.vec.Vec.length] at hek
        rw [hek]
      case pos.Ct1Received.Ct2 st c =>
        obtain ⟨ha, hdk, hct1, -⟩ := h
        simp only [Result.bind_eq_ok, Result.ok.injEq, core.result.Result.Ok.injEq] at hs
        obtain ⟨st', hst, rfl⟩ := hs
        simp only [send_ek.Ct1Received.recv_ct2_chunk, massert, Result.bind_eq_ok] at hst
        obtain ⟨_, -, n, hn, _, -, _, -, _, -, i3, hi3, dr, hnew, d, hexp, d', hadd, hst⟩ := hst
        simp only [Result.ok.injEq] at hst
        subst hst
        obtain rfl := core.result.Result.eq_Ok_of_expect_eq_ok hexp
        rw [incremental_mlkem768.CIPHERTEXT2_SIZE_eq, ok.injEq] at hn; subst hn
        have hi3v := UScalar.val_of_add_eq_ok hi3
        rw [authenticator.Authenticator.MACSIZE_spec] at hi3v
        exact ⟨ha, hdk, hct1,
          (DecoderInv.new (by rw [hi3v]; rfl) hnew).add_chunk (by norm_num) hadd⟩
      case pos.HeaderSent.Ct1 st c =>
        obtain ⟨ha, hdk, henc, hdec⟩ := h
        simp only [Result.bind_eq_ok] at hs
        obtain ⟨r, hr, hs⟩ := hs
        simp only [send_ek.HeaderSent.recv_ct1_chunk, massert, Result.bind_eq_ok] at hr
        obtain ⟨_, -, d', hadd, o, ho, hr⟩ := hr
        have hdec' := hdec.add_chunk (by norm_num) hadd
        cases o with
        | none =>
          simp only [Result.ok.injEq] at hr; subst hr
          simp only [Result.ok.injEq, core.result.Result.Ok.injEq] at hs; subst hs
          exact ⟨ha, hdk, henc, hdec'⟩
        | some m =>
          simp only [Result.bind_eq_ok] at hr
          obtain ⟨uc, huc, hr⟩ := hr
          simp only [Result.ok.injEq] at hr; subst hr
          simp only [Result.ok.injEq, core.result.Result.Ok.injEq] at hs; subst hs
          simp only [unchunked.send_ek.EkSent.recv_ct1, massert, Result.bind_eq_ok,
            Result.ok.injEq] at huc
          obtain ⟨_, -, rfl⟩ := huc
          refine ⟨ha, hdk, ?_, henc⟩
          simp only [alloc.vec.Vec.length]
          rw [decoded_message_length ho, add_chunk_pts_needed hadd, hdec.1]
      case pos.EkReceivedCt1Sampled.EkCt1Ack st c =>
        simp only [↓reduceIte] at hs
        simp only [Result.bind_eq_ok, Result.ok.injEq, core.result.Result.Ok.injEq] at hs
        obtain ⟨st', hst, rfl⟩ := hs
        exact recv_ct1_ack_inv st _ st' h hst
      case pos.EkReceivedCt1Sampled.Ct1Ack.true st =>
        simp only [↓reduceIte, bind_ok] at hs
        simp only [Result.bind_eq_ok, Result.ok.injEq, core.result.Result.Ok.injEq] at hs
        obtain ⟨st', hst, rfl⟩ := hs
        exact recv_ct1_ack_inv st _ st' h hst
      case pos.Ct1Acknowledged.Ek st c =>
        simp only [Result.bind_eq_ok] at hs
        obtain ⟨r, hr, hs⟩ := hs
        replace hs := core.result.Result.Insts.CoreOpsTry.continue_of_ok hs fun _ => rfl
        obtain ⟨val, rfl, hs⟩ := hs
        have hi := ct1Acknowledged_chunk_inv st c val h hr
        cases val <;>
          simp only [Result.ok.injEq, core.result.Result.Ok.injEq] at hs <;> subst hs <;>
          exact hi
      case pos.Ct1Acknowledged.EkCt1Ack st c =>
        simp only [Result.bind_eq_ok] at hs
        obtain ⟨r, hr, hs⟩ := hs
        replace hs := core.result.Result.Insts.CoreOpsTry.continue_of_ok hs fun _ => rfl
        obtain ⟨val, rfl, hs⟩ := hs
        have hi := ct1Acknowledged_chunk_inv st c val h hr
        cases val <;>
          simp only [Result.ok.injEq, core.result.Result.Ok.injEq] at hs <;> subst hs <;>
          exact hi
      case pos.Ct1Sampled.Ek st c =>
        simp only [uncurry_apply_pair] at hs
        simp only [Result.bind_eq_ok] at hs
        obtain ⟨r, hr, hs⟩ := hs
        replace hs := core.result.Result.Insts.CoreOpsTry.continue_of_ok hs fun _ => rfl
        obtain ⟨val, rfl, hs⟩ := hs
        have hi := ct1Sampled_chunk_inv st c _ val h hr
        cases val <;>
          simp only [Result.ok.injEq, core.result.Result.Ok.injEq] at hs <;> subst hs <;>
          exact hi
      case pos.Ct1Sampled.EkCt1Ack st c =>
        simp only [uncurry_apply_pair] at hs
        simp only [Result.bind_eq_ok] at hs
        obtain ⟨r, hr, hs⟩ := hs
        replace hs := core.result.Result.Insts.CoreOpsTry.continue_of_ok hs fun _ => rfl
        obtain ⟨val, rfl, hs⟩ := hs
        have hi := ct1Sampled_chunk_inv st c _ val h hr
        cases val <;>
          simp only [Result.ok.injEq, core.result.Result.Ok.injEq] at hs <;> subst hs <;>
          exact hi
      case pos.NoHeaderReceived.Hdr st c =>
        simp only [Result.bind_eq_ok] at hs
        obtain ⟨r, hr, hs⟩ := hs
        replace hs := core.result.Result.Insts.CoreOpsTry.continue_of_ok hs fun _ => rfl
        obtain ⟨val, rfl, hs⟩ := hs
        have hi := noHeaderReceived_chunk_inv st c val h hr
        cases val <;>
          simp only [Result.ok.injEq, core.result.Result.Ok.injEq] at hs <;> subst hs <;>
          exact hi
      case pos.EkSentCt1Received.Ct2 st c =>
        simp only [Result.bind_eq_ok] at hs
        obtain ⟨r, hr, hs⟩ := hs
        replace hs := core.result.Result.Insts.CoreOpsTry.continue_of_ok hs fun _ => rfl
        obtain ⟨val, rfl, hs⟩ := hs
        have hi := ekSentCt1Received_chunk_inv st c val h hr
        cases val with
        | StillReceiving s =>
          simp only [Result.ok.injEq, core.result.Result.Ok.injEq] at hs; subst hs
          exact hi
        | Done p =>
          obtain ⟨s, sec⟩ := p
          simp only [uncurry_apply_pair, ok.injEq, core.result.Result.Ok.injEq] at hs; subst hs
          exact hi
    · rw [recv_of_eq_unexpected s msg heq' hx, Result.ok.injEq,
        core.result.Result.Ok.injEq] at hs
      subst hs
      exact h
  · by_cases hn : ∃ st, s = .Ct2Sampled st ∧ msg.epoch.val = st.uc.epoch.val + 1
    · obtain ⟨st, rfl, hn⟩ := hn
      rw [recv_Ct2Sampled_next_epoch st msg hn, Result.ok.injEq,
        core.result.Result.Ok.injEq] at hs
      subst hs
      exact h.1
    · rw [recv_of_gt s msg hgt (fun st hst hm => hn ⟨st, hst, hm⟩)] at hs
      simp only [ok.injEq, reduceCtorEq] at hs

/-- If `k.length + 32 ≤ Usize.max`, `init_a k` succeeds, and its state satisfies `Inv` and
refines `InitAlice` for every `P` that agrees with the code. -/
theorem init_a_ok (k : Slice Std.U8) (hk : k.length + 32 ≤ Usize.max) :
    ∃ s, States.init_a k = ok s ∧ Inv s ∧
      ∀ P : CodePrims, CodeAgrees P → Refines s (initAlice P k.val) := by
  obtain ⟨s, hs, ku, rfl, -, hr, hm, -⟩ :=
    WP.spec_imp_exists (States.init_a_spec k hk)
  exact ⟨_, hs, ⟨hr, hm⟩, fun P hP => (init_refines P hP k).1 _ hs⟩

/-- If `k.length + 32 ≤ Usize.max`, `init_b k` succeeds, and its state satisfies `Inv` and
refines `InitBob` for every `P` that agrees with the code. -/
theorem init_b_ok (k : Slice Std.U8) (hk : k.length + 32 ≤ Usize.max) :
    ∃ s, States.init_b k = ok s ∧ Inv s ∧
      ∀ P : CodePrims, CodeAgrees P → Refines s (initBob P k.val) := by
  obtain ⟨s, hs, nh, rfl, -, hr, hm, -, hpn, hpts, hc⟩ :=
    WP.spec_imp_exists (States.init_b_spec k hk)
  refine ⟨_, hs, ⟨⟨hr, hm⟩, hpn, hc, ?_⟩, fun P hP => (init_refines P hP k).2 _ hs⟩
  intro sl hsl
  rw [hpts] at hsl
  rw [List.eq_of_mem_replicate hsl]
  exact encoding.polynomial.PolyDecoder.SlotSorted.nil

/-- Every successful `send`, with any RNG, and every successful `recv`, of any message, keeps
`Inv`. -/
theorem inv_step {s s' : States} {k : Option EpochSecret} (h : Inv s) (hs : Step s s' k) :
    Inv s' := by
  cases hs with
  | send i₁ i₂ rng rng' r hs => exact inv_send i₁ i₂ _ h rng rng' r hs
  | recv msg r hs => exact inv_recv _ h msg r hs

/-- Every state on a run from a state that satisfies `Inv` satisfies `Inv`. -/
theorem inv_run {s s' : States} {ks : List EpochSecret} (hr : Run s s' ks) (h : Inv s) :
    Inv s' := by
  induction hr with
  | nil => exact h
  | cons hs _ ih => exact ih (inv_step h hs)

end spqr.v1.chunked.states
