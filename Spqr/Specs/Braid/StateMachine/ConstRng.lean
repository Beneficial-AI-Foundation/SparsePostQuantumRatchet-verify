/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Lacramioara Astefanoaei
-/
module

public import SrcTranslated.Funs
public import SrcTranslated.FunsExternal

/-! # The bytes that `States::send` reads from its generator

`send` takes a random number generator. `send_eq_fill` shows that it calls `fill_bytes` once on
64 zero bytes in `KeysUnsampled`, once on 32 zero bytes in `HeaderReceived`, and not in the other
states (`sendFill`). The rest of `send` (`sendRest`) uses the generator only through the buffer
that `fill_bytes` returned: it is `send` with the constant generator for that buffer
(`constRng`, `constCrypto`).

**Source**: spqr/src/v1/chunked/states.rs:115-273, spqr/src/incremental_mlkem768.rs:32-66 -/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace spqr.v1.chunked.states

/-- The `RngCore Unit` whose `fill_bytes` returns `buf` for every argument. `next_u32` and
`next_u64` return 0; `send` does not call them. -/
def constCore (buf : Slice Std.U8) : rand_core_1.RngCore Unit where
  next_u32 _ := ok (0#u32, ())
  next_u64 _ := ok (0#u64, ())
  fill_bytes _ _ := ok ((), buf)

/-- The `Rng` instance of the constant generator for `buf`. -/
def constRng (buf : Slice Std.U8) : rand_1.rng.Rng Unit := ⟨constCore buf⟩

/-- The `CryptoRng` instance of the constant generator for `buf`. -/
def constCrypto (buf : Slice Std.U8) : rand_core_1.CryptoRng Unit := ⟨constCore buf⟩

/-- The number of bytes that `send` asks `fill_bytes` for: 64 in `KeysUnsampled`, 32 in
`HeaderReceived`, and 0 in the other states. -/
def sendLen : States → ℕ
  | .KeysUnsampled _ => 64
  | .HeaderReceived _ => 32
  | _ => 0

/-- The `fill_bytes` call of `send` on `s`, with the buffer it returns and the new generator
state. In `KeysUnsampled` it is one call on 64 zero bytes, in `HeaderReceived` one call on 32
zero bytes. In the other states there is no call: the buffer is empty and the generator state
does not change. -/
def sendFill {R : Type} (i₁ : rand_1.rng.Rng R) (s : States) (rng : R) :
    Result (Slice Std.U8 × R) :=
  match s with
  | .KeysUnsampled _ => do
    let p ← i₁.rand_core_1RngCoreInst.fill_bytes rng (Array.repeat 64#usize 0#u8).to_slice
    ok (p.2, p.1)
  | .HeaderReceived _ => do
    let p ← i₁.rand_core_1RngCoreInst.fill_bytes rng (Array.repeat 32#usize 0#u8).to_slice
    ok (p.2, p.1)
  | _ => ok (Slice.from [] (by simp only [List.length_nil, zero_le]), rng)

/-- The result of `send` on `s` when `fill_bytes` returns `buf`. It takes no generator. -/
noncomputable def sendRest (s : States) (buf : Slice Std.U8) :
    Result (core.result.Result Send Error) := do
  let p ← States.send (constRng buf) (constCrypto buf) s ()
  ok p.1

/-- A destructured pair is its two projections. -/
private theorem uncurry_eq {α β γ : Type} (f : α → β → γ) : uncurry f = fun q => f q.1 q.2 :=
  rfl

/-- `send` with a generator of any type is `sendFill`, then `sendRest` on the buffer that
`sendFill` returned. The new generator state is the one that `sendFill` returned. -/
theorem send_eq_fill {R : Type} (i₁ : rand_1.rng.Rng R) (i₂ : rand_core_1.CryptoRng R)
    (s : States) (rng : R) :
    States.send i₁ i₂ s rng =
      (do
        let p ← sendFill i₁ s rng
        let r ← sendRest s p.1
        ok (r, p.2)) := by
  cases s
  case KeysUnsampled st =>
    simp only [States.send, sendFill, sendRest, v1.chunked.send_ek.KeysUnsampled.send_hdr_chunk,
      v1.unchunked.send_ek.KeysUnsampled.send_header, incremental_mlkem768.generate, lift,
      Array.to_slice_mut, constRng, constCore, Std.bind_assoc, bind_ok, uncurry_eq,
      v1.chunked.send_ek.KeysUnsampled.epoch]
  case HeaderReceived st =>
    simp only [States.send, sendFill, sendRest, v1.chunked.send_ct.HeaderReceived.send_ct1_chunk,
      v1.unchunked.send_ct.HeaderReceived.send_ct1, incremental_mlkem768.encaps1, lift,
      Array.to_slice_mut, constRng, constCore, Std.bind_assoc, bind_ok, uncurry_eq,
      alloc.vec.Vec.deref_mut, v1.chunked.send_ct.HeaderReceived.epoch]
  all_goals
    simp only [States.send, sendFill, sendRest, Std.bind_assoc, bind_ok]
    try
      congr 1; funext e
      congr 1; funext ⟨st, c⟩
      simp only [uncurry_apply_pair, bind_ok]

end spqr.v1.chunked.states
