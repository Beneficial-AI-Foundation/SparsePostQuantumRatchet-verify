/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
-/
module

public import Spqr.Specs.Braid.StateMachine.Run

/-! # Successful-call traces as a conservative refinement of `Run`

This experiment records one optional output per successful call of one party. It covers arbitrary
states, retains silent calls, and neither models failed calls nor asserts that calls succeed.
The underlying `Step` is unchanged; erasing silent outputs recovers exactly the existing `Run`.
-/

@[expose] public section

namespace spqr.v1.chunked.states
namespace TraceExperiment

/-- The emitted keys of an optional-output trace, with silent calls erased. -/
def outputs : List (Option EpochSecret) → List EpochSecret
  | [] => []
  | k :: trace => k.toList ++ outputs trace

/-- A finite successful-call trace, with one entry even when a call emits no key. -/
inductive TraceRun : States → States → List (Option EpochSecret) → Prop
  | nil {s : States} : TraceRun s s []
  | cons {s s₁ s₂ : States} {k : Option EpochSecret} {trace : List (Option EpochSecret)} :
      Step s s₁ k → TraceRun s₁ s₂ trace → TraceRun s s₂ (k :: trace)

/-- Erasure respects concatenation. -/
theorem outputs_append (xs ys : List (Option EpochSecret)) :
    outputs (xs ++ ys) = outputs xs ++ outputs ys := by
  induction xs with
  | nil => rfl
  | cons k xs ih => simp only [List.cons_append, outputs, ih, List.append_assoc]

/-- Forgetting silent calls gives a run in the existing definition. -/
theorem TraceRun.toRun {s t : States} {trace : List (Option EpochSecret)}
    (h : TraceRun s t trace) : Run s t (outputs trace) := by
  induction h with
  | nil => exact Run.nil
  | cons hs _ ih => exact Run.cons hs ih

/-- Every existing run admits a successful-call trace with the same endpoints and outputs. -/
theorem Run.exists_trace {s t : States} {ks : List EpochSecret} (h : Run s t ks) :
    ∃ trace, TraceRun s t trace ∧ outputs trace = ks := by
  induction h with
  | nil => exact ⟨[], TraceRun.nil, rfl⟩
  | @cons s s₁ s₂ k ks hs _ ih =>
    obtain ⟨trace, ht, he⟩ := ih
    exact ⟨k :: trace, TraceRun.cons hs ht, congrArg (k.toList ++ ·) he⟩

/-- Conservativity: the old relation is precisely existential erasure of the new one. -/
theorem run_iff_exists_trace {s t : States} {ks : List EpochSecret} :
    Run s t ks ↔ ∃ trace, TraceRun s t trace ∧ outputs trace = ks := by
  constructor
  · exact Run.exists_trace
  · rintro ⟨trace, ht, rfl⟩
    exact ht.toRun

/-- Successful-call traces compose without losing silent-call positions. -/
theorem TraceRun.append {s u t : States} {xs ys : List (Option EpochSecret)}
    (hx : TraceRun s u xs) (hy : TraceRun u t ys) : TraceRun s t (xs ++ ys) := by
  induction hx with
  | nil => exact hy
  | cons hs _ ih => exact TraceRun.cons hs (ih hy)

/-- A specified trace boundary always has a witnessing intermediate state. -/
theorem TraceRun.split {s t : States} (xs ys : List (Option EpochSecret))
    (h : TraceRun s t (xs ++ ys)) : ∃ u, TraceRun s u xs ∧ TraceRun u t ys := by
  induction xs generalizing s with
  | nil => exact ⟨s, TraceRun.nil, h⟩
  | cons k xs ih =>
    cases h with
    | cons hs ht =>
      obtain ⟨u, hx, hy⟩ := ih ht
      exact ⟨u, TraceRun.cons hs hx, hy⟩

/-- Exact decomposition is equivalent to composition, for each specified trace boundary. -/
theorem traceRun_append_iff {s t : States} {xs ys : List (Option EpochSecret)} :
    TraceRun s t (xs ++ ys) ↔ ∃ u, TraceRun s u xs ∧ TraceRun u t ys := by
  constructor
  · exact TraceRun.split xs ys
  · rintro ⟨u, hx, hy⟩
    exact hx.append hy

/-- Cutting after any number of successful calls produces two valid traces. -/
theorem TraceRun.cut {s t : States} {trace : List (Option EpochSecret)}
    (h : TraceRun s t trace) (n : Nat) :
    ∃ u, TraceRun s u (trace.take n) ∧ TraceRun u t (trace.drop n) := by
  apply TraceRun.split
  simpa only [List.take_append_drop] using h

/-- The number of silent calls in a trace. -/
def silentCount : List (Option EpochSecret) → Nat
  | [] => 0
  | none :: trace => 1 + silentCount trace
  | some _ :: trace => silentCount trace

/-- Exact call accounting: every call is either silent or emits one key. -/
theorem length_eq_outputs_add_silent (trace : List (Option EpochSecret)) :
    trace.length = (outputs trace).length + silentCount trace := by
  induction trace with
  | nil => rfl
  | cons k trace ih =>
    cases k <;> simp only [outputs, silentCount, Option.toList_none, Option.toList_some,
      List.nil_append, List.singleton_append, List.length_cons] <;> omega

/-- Emitted-key count is a lower bound on the successful-call count. -/
theorem outputs_length_le (trace : List (Option EpochSecret)) :
    (outputs trace).length ≤ trace.length := by
  rw [length_eq_outputs_add_silent]
  exact Nat.le_add_right _ _

/-- Erasure alone cannot distinguish zero calls from a single silent call.
This is a statement about trace lists, not a claim that both traces are executable. -/
theorem outputs_not_injective : ¬ Function.Injective outputs := by
  intro h
  have he : ([] : List (Option EpochSecret)) = [none] := h rfl
  cases he

end TraceExperiment
end spqr.v1.chunked.states
