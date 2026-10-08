/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Lacramioara Astefanoaei
-/
import SrcTranslated.Funs
import SrcTranslated.FunsExternal

/-! # Runs of one party's chunked `States` machine

A `Step s s' k` is one successful `States::send` or `States::recv` call from `s` that returns
the new state `s'` and the optional key `k`. A `Run s s' ks` is a finite sequence of steps from
`s` to `s'`, with any RNG and any message at each step, and `ks` lists the keys it emits, in
order. Both are relations: the RNG or message of a step is a field of its proof.

**Source**: spqr/src/v1/chunked/states.rs:203-220, spqr/src/v1/chunked/states.rs:361-368 -/

open Aeneas Aeneas.Std Result

namespace spqr.v1.chunked.states

/-- One successful call of one party: a `send` with some RNG, or a `recv` of some
message, that returns `Ok` at both the Aeneas and the Rust level. -/
inductive Step : States → States → Option EpochSecret → Prop
  | send {s : States} {R : Type} (i₁ : rand.rng.Rng R) (i₂ : rand_core.CryptoRng R)
      (rng rng' : R) (r : v1.chunked.states.Send) :
      States.send i₁ i₂ s rng = ok (.Ok r, rng') → Step s r.state r.key
  | recv {s : States} (msg : Message) (r : v1.chunked.states.Recv) :
      States.recv s msg = ok (.Ok r) → Step s r.state r.key

/-- A run from `s` to `s'` that emits keys `ks`, in order. -/
inductive Run : States → States → List EpochSecret → Prop
  | nil {s : States} : Run s s []
  | cons {s s₁ s₂ : States} {k : Option EpochSecret} {ks : List EpochSecret} :
      Step s s₁ k → Run s₁ s₂ ks → Run s s₂ (k.toList ++ ks)

/-- Runs compose. -/
theorem Run.append {s₀ s s' : States} {ks₀ ks : List EpochSecret} (h₁ : Run s₀ s ks₀)
    (h₂ : Run s s' ks) : Run s₀ s' (ks₀ ++ ks) := by
  induction h₁ with
  | nil => simpa using h₂
  | cons hs _ ih => simpa [List.append_assoc] using Run.cons hs (ih h₂)

end spqr.v1.chunked.states
