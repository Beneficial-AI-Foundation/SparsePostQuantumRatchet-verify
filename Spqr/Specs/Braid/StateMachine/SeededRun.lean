/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Lacramioara Astefanoaei
-/
module

public import Spqr.Specs.Braid.StateMachine.ConstRng
public import Spqr.Specs.Braid.StateMachine.SeededPrims
public meta import Spqr.Auxiliary.SpecTags

/-! # Runs of the code with one `fill_bytes` buffer per `send`, against the machine

`send_refines` gives the machine's `Send()` for some randomness. Here the randomness is the
buffer that `fill_bytes` returned. Assume `SeededAgrees P` (`SeededPrims.lean`). Then:

* `send_refines_seeded`: if `send` with the constant generator for a buffer of `sendLen s`
  bytes succeeds on `s`, the machine's `Send()` with that buffer as randomness gives a related
  state, the code's message and the code's key;
* `send_refines_fill`: the same for a generator of any type, with the buffer that `sendFill`
  returned (`send_eq_fill`): the one that `fill_bytes` returned, or the empty slice in the states
  where `send` does not call `fill_bytes`;
* `run_refines_seeded`: a `SeededRun` (each `send` with its own buffer) is a run of the machine
  on the same inputs (`BraidModel.RunOn`), with a related end state and the same keys.

`SeededRun.toRun` and `RunOn.toRun` erase the inputs to the runs `Run` and `BraidModel.Run`.

**Source**: ML-KEM Braid Rev. 1, §1.2, §2.5; spqr/src/v1/chunked/states.rs:115-273 -/

@[expose] public section

open Aeneas Aeneas.Std Result Aeneas.Std.WP spqr

namespace spqr.v1.chunked.states

/-- The input of one successful call of the code: the buffer of a `send` (the one that
`fill_bytes` returned, or the empty slice when `send` does not call `fill_bytes`), or the message
given to a `recv`. -/
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
    obtain ⟨keys, rk, hg, hk⟩ :=
      send_keysUnsampled_refines P hC _ _ s σ h () () out hs
    exact hk _ (hP.keyGen_seed (constRng buf) (constCrypto buf) () () rk buf keys rfl hbuf hg)
  case HeaderReceived s =>
    obtain ⟨hdr, ct1, es, ss, rk, he1, hk⟩ :=
      send_headerReceived_refines P hC _ _ s σ h () () out hs
    exact hk _
      (hP.encaps1_seed (constRng buf) (constCrypto buf) () () rk buf hdr ct1 es ss rfl hbuf he1)
  all_goals
    have hb : buf.val = [] := List.eq_nil_of_length_eq_zero hbuf
    obtain ⟨r, h1, h2, h3⟩ := send_refines P hC _ _ _ σ h () () out hs
    rw [hb]
    cases σ <;> simp only [Refines] at h
    exact ⟨h1, h2, h3⟩

/-- Assume `SeededAgrees P` and `Refines s σ`. If `send` with a generator of any type succeeds
on `s`, then `sendFill` on `s` returns some `buf` and the final generator state, and if `buf` has
`sendLen s` bytes, the machine's `Send()` on `σ` with randomness `buf` gives a related state, the
code's message and the code's key. -/
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
