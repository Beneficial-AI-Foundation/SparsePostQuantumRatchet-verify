/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Lacramioara Astefanoaei
-/
module

public import Spqr.Specs.Braid.StateMachine.ConstRng
public import Spqr.Specs.Braid.StateMachine.SeededPrims
public meta import Spqr.Auxiliary.SpecTags
import Spqr.Specs.Aeneas.SliceConcat
import Spqr.Auxiliary.Aeneas.Result
import Spqr.Specs.Kdf.HkdfToVec
import Spqr.Specs.Aeneas.VecClone
import Spqr.Specs.Aeneas.VecAppend
import Spqr.Specs.Aeneas.SliceListToVec
import Spqr.Specs.Aeneas.SliceConcatListAux
import Spqr.Specs.Aeneas.ResultExpect
import Spqr.Auxiliary.Aeneas.Slice
import Spqr.Auxiliary.Aeneas.Vec

/-! # Runs of the code with one `fill_bytes` buffer per `send`, against the machine

`send_refines` gives the machine's `Send()` for some randomness. Here the randomness is the
buffer that `fill_bytes` returned. Assume `SeededAgrees P` (`SeededPrims.lean`). Then:

* `send_refines_seeded`: if `send` with the constant generator for a buffer of `sendLen s`
  bytes succeeds on `s`, the machine's `Send()` with that buffer as randomness gives a related
  state, the code's message and the code's key;
* `send_refines_fill`: the same for a generator of any type, with the buffer that its
  `fill_bytes` call returned (`send_eq_fill`);
* `run_refines_seeded`: a `SeededRun` (each `send` with its own buffer) is a run of the machine
  on the same inputs (`BraidModel.RunOn`), with a related end state and the same keys.

`SeededRun.toRun` and `RunOn.toRun` erase the inputs to the runs `Run` and `BraidModel.Run`.

**Source**: ML-KEM Braid Rev. 1, §1.2, §2.5; spqr/src/v1/chunked/states.rs:115-273 -/

@[expose] public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP spqr

namespace spqr.v1.chunked.states

/-- The input of one successful call of the code: the buffer that `fill_bytes` returned to a
`send`, or the message given to a `recv`. -/
inductive StepInput where
  | send (buf : Slice Std.U8)
  | recv (msg : Message)

/-- A finite sequence of successful calls from `s` to `s'` with inputs `ins`, that emits keys
`ks`, in order. Each `send` runs with the constant generator for its own buffer, of length
`sendLen` of its state. -/
inductive SeededRun : States → States → List StepInput → List EpochSecret → Prop
  | nil {s : States} : SeededRun s s [] []
  | send {s s' : States} {ins : List StepInput} {ks : List EpochSecret}
      (buf : Slice Std.U8) (out : Send) :
      buf.length = sendLen s →
      States.send (constRng buf) (constCrypto buf) s () = ok (.Ok out, ()) →
      SeededRun out.state s' ins ks →
      SeededRun s s' (.send buf :: ins) (out.key.toList ++ ks)
  | recv {s s' : States} {ins : List StepInput} {ks : List EpochSecret}
      (msg : Message) (out : Recv) :
      States.recv s msg = ok (.Ok out) →
      SeededRun out.state s' ins ks →
      SeededRun s s' (.recv msg :: ins) (out.key.toList ++ ks)

/-- A seeded run is a run. -/
theorem SeededRun.toRun {s s' : States} {ins : List StepInput} {ks : List EpochSecret}
    (h : SeededRun s s' ins ks) : Run s s' ks := by
  induction h with
  | nil => exact .nil
  | send buf out _ hs _ ih => exact .cons (.send _ _ () () out hs) ih
  | recv msg out hs _ ih => exact .cons (.recv msg out hs) ih

end spqr.v1.chunked.states

namespace BraidModel

variable {Enc Dec Chunk : Type}

/-- The input of one step of the machine: the randomness of a `Send()`, or the message of a
`Receive()`. -/
inductive Input (Chunk : Type) where
  | send (r : Bytes)
  | recv (m : Msg Chunk)

/-- A run of the machine from `σ` to `σ'` on the inputs `ins`, that emits the keys `ks`, in
order. A `Send()` uses the randomness of its input; a `Receive()` does not fail. -/
inductive RunOn (P : Prims Enc Dec Chunk) :
    State Enc Dec → State Enc Dec → List (Input Chunk) → List Key → Prop
  | nil (σ : State Enc Dec) : RunOn P σ σ [] []
  | send {σ σ' : State Enc Dec} {ins : List (Input Chunk)} {ks : List Key} (r : Bytes) :
      RunOn P (send P σ r).1 σ' ins ks →
      RunOn P σ σ' (.send r :: ins) ((send P σ r).2.2.toList ++ ks)
  | recv {σ σ₁ σ' : State Enc Dec} {ins : List (Input Chunk)} {ks : List Key}
      (m : Msg Chunk) (k : Option Key) :
      receive P σ m = some (σ₁, k) →
      RunOn P σ₁ σ' ins ks →
      RunOn P σ σ' (.recv m :: ins) (k.toList ++ ks)

/-- A run on given inputs is a run. -/
theorem RunOn.toRun {P : Prims Enc Dec Chunk} {σ σ' : State Enc Dec} {ins : List (Input Chunk)}
    {ks : List Key} (h : RunOn P σ σ' ins ks) : Run P σ σ' ks := by
  induction h with
  | nil σ => exact .nil σ
  | send r _ ih => exact .cons (.send _ r) ih
  | recv m k hm _ ih => exact .cons (.recv _ _ m k hm) ih

end BraidModel

namespace spqr.v1.chunked.states

open core.result.Result (eq_Ok_of_expect_eq_ok)
open BraidModel

/-- The machine's input for the code's: a buffer becomes its bytes, a message its `absMsg`. -/
def absInput : StepInput → Input encoding.Chunk
  | .send buf => .send buf.val
  | .recv msg => .recv (absMsg msg)

/-- Assume `SeededAgrees P` and `Refines s σ`, and let `buf` have `sendLen s` bytes. If `send`
with the constant generator for `buf` succeeds on `s`, then the machine's `Send()` on `σ` with
randomness `buf` gives a related state, the code's message and the code's key. -/
@[correctness_spec, braid_spec "§2.5", braid_deviation Deviation.ct1AckAccepted]
theorem send_refines_seeded (P : CodePrims) (hP : SeededAgrees P) (s : States)
    (σ : State _ _) (h : Refines s σ) (buf : Slice Std.U8) (hbuf : buf.length = sendLen s)
    (out : Send) (hs : States.send (constRng buf) (constCrypto buf) s () = ok (.Ok out, ())) :
    Refines out.state (BraidModel.send P σ buf.val).1 ∧
      absMsg out.msg = (BraidModel.send P σ buf.val).2.1 ∧
      out.key.map absKey = (BraidModel.send P σ buf.val).2.2 := by
  have hC := hP.toCodeAgrees
  cases s
  case KeysUnsampled s =>
    cases σ <;> simp only [Refines] at h
    case keysUnsampled e a =>
      simp only [States.send, Result.bind_eq_ok] at hs
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
      subst h2 h3
      obtain ⟨⟨ts1, z⟩, hap, hrest⟩ := hrest
      simp only [uncurry_apply_pair] at hrest
      simp only [Result.bind_eq_ok] at hrest
      obtain ⟨enc0, henc, sh, hsh, ⟨c', e'⟩, hn, hfin⟩ := hrest
      simp only [uncurry_apply_pair, ok.injEq, Prod.mk.injEq, and_assoc] at hfin
      obtain ⟨rfl, rfl, -⟩ := hfin
      have hsh' := eq_Ok_of_expect_eq_ok hsh; subst hsh'
      have hr := hP.keyGen_seed (constRng buf) (constCrypto buf) () () rk buf keys rfl hbuf hg
      have hmac := mac_hdr_ok P hC _ _ _ _ hm
      have hts := alloc.vec.Vec.append_ok_val hap
      have he := hC.encode _ _ henc
      have hnc := hC.nextChunk _ _ _ hn
      simp only [alloc.vec.Vec.deref, Slice.from_val] at hmac he
      rw [hts, hmac] at he
      subst h1
      simp only [BraidModel.send, hr, he, hnc]
      simp only [Refines, and_self, absMsg, Option.map_none]
  case HeaderReceived s =>
    cases σ <;> simp only [Refines] at h
    case headerReceived e a hdr d =>
      simp only [States.send, Result.bind_eq_ok] at hs
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
      have hsec := (post_of_ok (kdf.hkdf_to_vec_spec _ _ _ _ (by
          simp only [UScalar.ofNatCore_val_eq,
            Nat.reduceMul, Nat.reduceLeDiff])) hk).1
      simp only [alloc.vec.Vec.deref, Slice.from_val, hiv'] at hsec
      have hz : (Array.repeat 32#usize 0#u8).to_slice.val = List.replicate 32 0#u8 := by
        simp only [Array.to_slice, Array.repeat, UScalar.ofNatCore_val_eq, List.reduceReplicate,
            Array.from_val, Slice.from_val]
      rw [hz, show (32#usize : Std.Usize).val = 32 by simp only [UScalar.ofNatCore_val_eq],
        ← hC.kdfOk] at hsec
      have hau := absAuth_update P hC _ _ _ _ hu
      simp only [alloc.vec.Vec.deref, Slice.from_val, hsec] at hau
      have hv' := post_of_ok (alloc.vec.CloneVec.clone_U8_spec _) hv
      subst hv'
      simp only [Result.ok.injEq, Prod.mk.injEq] at hsc
      obtain ⟨⟨h6, rfl, rfl⟩, -⟩ := hsc
      subst h6
      have hr := hP.encaps1_seed (constRng buf) (constCrypto buf) () () rk buf _ _ _ _ rfl hbuf he1
      have he := hC.encode _ _ henc
      have hnc := hC.nextChunk _ _ _ hn
      simp only [alloc.vec.Vec.deref, Slice.from_val] at he
      simp only [BraidModel.send, hr, he, hnc]
      simp only [Refines, hau, and_self, absMsg, Option.map_some, absKey, hsec]
  all_goals
    have hb : buf.val = [] := List.eq_nil_of_length_eq_zero hbuf
    obtain ⟨r, h1, h2, h3⟩ := send_refines P hC _ _ _ σ h () () out hs
    rw [hb]
    cases σ <;> simp only [Refines] at h
    exact ⟨h1, h2, h3⟩

/-- Assume `SeededAgrees P` and `Refines s σ`. If `send` with a generator of any type succeeds
on `s`, then its `fill_bytes` call returned some `buf` and the final generator state, and if
`buf` has `sendLen s` bytes, the machine's `Send()` on `σ` with randomness `buf` gives a related
state, the code's message and the code's key. -/
@[correctness_spec, braid_spec "§2.5", braid_deviation Deviation.ct1AckAccepted]
theorem send_refines_fill (P : CodePrims) (hP : SeededAgrees P) {R : Type}
    (i₁ : rand_1.rng.Rng R) (i₂ : rand_core_1.CryptoRng R) (s : States) (σ : State _ _)
    (h : Refines s σ) (rng rng' : R) (out : Send)
    (hs : States.send i₁ i₂ s rng = ok (.Ok out, rng')) :
    ∃ buf, sendFill i₁ s rng = ok (buf, rng') ∧
      (buf.length = sendLen s →
        Refines out.state (BraidModel.send P σ buf.val).1 ∧
        absMsg out.msg = (BraidModel.send P σ buf.val).2.1 ∧
        out.key.map absKey = (BraidModel.send P σ buf.val).2.2) := by
  rw [send_eq_fill, Result.bind_eq_ok] at hs
  obtain ⟨⟨buf, rng₁⟩, hf, hs⟩ := hs
  rw [Result.bind_eq_ok] at hs
  obtain ⟨r, hr, hs⟩ := hs
  simp only [Result.ok.injEq, Prod.mk.injEq] at hs
  obtain ⟨rfl, rfl⟩ := hs
  refine ⟨buf, hf, fun hbuf => ?_⟩
  simp only [sendRest, Result.bind_eq_ok, Result.ok.injEq] at hr
  obtain ⟨⟨r', u⟩, hr', rfl⟩ := hr
  exact send_refines_seeded P hP s σ h buf hbuf out hr'

/-- Assume `SeededAgrees P` and `Refines s σ`. Then every seeded run from `s` on the inputs
`ins` is a run of the machine from `σ` on the same inputs, with a related end state and the same
keys. Each `Send()` uses the buffer of its `send` as randomness. -/
@[correctness_spec, braid_spec "§2.5",
  braid_deviation Deviation.futureEpochError Deviation.ct1AckAccepted Deviation.lateEkChunk]
theorem run_refines_seeded (P : CodePrims) (hP : SeededAgrees P) {s s' : States}
    {ins : List StepInput} {ks : List EpochSecret} (hr : SeededRun s s' ins ks)
    {σ : State _ _} (h : Refines s σ) :
    ∃ σ', RunOn P σ σ' (ins.map absInput) (ks.map absKey) ∧ Refines s' σ' := by
  induction hr generalizing σ with
  | nil => exact ⟨σ, .nil σ, h⟩
  | send buf out hbuf hs _ ih =>
    obtain ⟨h1, -, h3⟩ := send_refines_seeded P hP _ σ h buf hbuf out hs
    obtain ⟨σ₂, hrun, h₂⟩ := ih h1
    refine ⟨σ₂, ?_, h₂⟩
    have := RunOn.send (P := P) buf.val hrun
    rw [← h3] at this
    convert this using 1 <;> cases out.key <;>
      simp only [absInput, Option.toList_none, List.nil_append, Option.map_none,
        Option.toList_some, List.cons_append, List.map_cons, Option.map_some]
  | recv msg out hs _ ih =>
    obtain ⟨σ₁, h1, h2⟩ := recv_refines P hP.toCodeAgrees _ σ h msg out hs
    obtain ⟨σ₂, hrun, h₂⟩ := ih h2
    refine ⟨σ₂, ?_, h₂⟩
    have := RunOn.recv (absMsg msg) _ h1 hrun
    convert this using 1 <;> cases out.key <;>
      simp only [absInput, Option.toList_none, List.nil_append, Option.map_none,
        Option.toList_some, List.cons_append, List.map_cons, Option.map_some]

end spqr.v1.chunked.states
