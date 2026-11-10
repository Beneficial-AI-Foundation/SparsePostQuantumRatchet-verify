/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
-/
module

public import TraceRun
public import Spqr.Specs.Braid.Scka.EpochUniqueness.KeyFloor

/-! # Epoch clocks at successful-call boundaries

The epoch clock exposes the existing `keyFloor` invariant at each boundary of an optional-output
trace. All claims concern successful calls of one party and inherit the existing step semantics.
-/

@[expose] public section

namespace spqr.v1.chunked.states
namespace TraceExperiment

/-- The next-key epoch at a boundary after `n` successful calls; indices beyond the end saturate. -/
def epochClock (s : States) (trace : List (Option EpochSecret)) (n : Nat) : Nat :=
  keyFloor s + (outputs (trace.take n)).length

/-- Trace endpoint accounting inherited from the existing epoch-consecutiveness theorem. -/
theorem TraceRun.keyFloor_eq {s t : States} {trace : List (Option EpochSecret)}
    (h : TraceRun s t trace) : keyFloor t = keyFloor s + (outputs trace).length :=
  (epochs_consecutive h.toRun).2

/-- Every successful-call boundary has a state whose next-key epoch is the observable clock. -/
theorem TraceRun.cut_epochClock {s t : States} {trace : List (Option EpochSecret)}
    (h : TraceRun s t trace) (n : Nat) :
    ∃ u, TraceRun s u (trace.take n) ∧ TraceRun u t (trace.drop n) ∧
      keyFloor u = epochClock s trace n := by
  obtain ⟨u, hp, hs⟩ := h.cut n
  exact ⟨u, hp, hs, hp.keyFloor_eq⟩

/-- Any two boundary witnesses agree on the next-key epoch, even if their states differ. -/
theorem TraceRun.boundary_keyFloor_unique {s u v : States}
    {pre : List (Option EpochSecret)} (hu : TraceRun s u pre)
    (hv : TraceRun s v pre) : keyFloor u = keyFloor v := by
  rw [hu.keyFloor_eq, hv.keyFloor_eq]

/-- An emitted key has the epoch determined by the outputs preceding its call. -/
theorem TraceRun.emission_epoch {s t : States} {pre suffix : List (Option EpochSecret)}
    {k : EpochSecret} (h : TraceRun s t (pre ++ some k :: suffix)) :
    k.epoch.val = keyFloor s + (outputs pre).length := by
  obtain ⟨u, hp, hs⟩ := h.split pre (some k :: suffix)
  cases hs with
  | cons hstep _ =>
    exact (hstep.keyFloor_step).1.trans hp.keyFloor_eq

/-- An explicit prefix has the same clock as its emitted-key accounting. -/
theorem epochClock_prefix (s : States) (pre suffix : List (Option EpochSecret)) :
    epochClock s (pre ++ suffix) pre.length = keyFloor s + (outputs pre).length := by
  simp only [epochClock, List.take_left]

/-- The epoch of a key emitted at a call boundary is exactly the clock at that boundary. -/
theorem TraceRun.emission_epochClock {s t : States}
    {pre suffix : List (Option EpochSecret)} {k : EpochSecret}
    (h : TraceRun s t (pre ++ some k :: suffix)) :
    k.epoch.val = epochClock s (pre ++ some k :: suffix) pre.length := by
  rw [epochClock_prefix]
  exact h.emission_epoch

/-- Exact accounting for the emissions in an interval delimited by two trace boundaries. -/
theorem epochClock_interval (s : States) (pre middle suffix : List (Option EpochSecret)) :
    epochClock s (pre ++ middle ++ suffix) (pre.length + middle.length) =
      epochClock s (pre ++ middle ++ suffix) pre.length + (outputs middle).length := by
  have hleft : (pre ++ middle ++ suffix).take pre.length = pre := by
    rw [List.append_assoc, List.take_left]
  have hright : (pre ++ middle ++ suffix).take (pre.length + middle.length) =
      pre ++ middle := by
    rw [← List.length_append, List.take_left]
  simp only [epochClock, hleft, hright, outputs_append, List.length_append, Nat.add_assoc]

/-- Erasure is empty exactly when every call in a trace is silent. -/
theorem outputs_eq_nil_iff (trace : List (Option EpochSecret)) :
    outputs trace = [] ↔ ∀ k ∈ trace, k = none := by
  induction trace with
  | nil => simp only [outputs, List.not_mem_nil, false_implies, implies_true]
  | cons k trace ih =>
    cases k with
    | none =>
      simp only [outputs, Option.toList_none, List.nil_append, ih, List.mem_cons,
        forall_eq_or_imp, true_and]
    | some key =>
      simp only [outputs, Option.toList_some, List.singleton_append,
        List.cons_ne_nil, List.mem_cons, forall_eq_or_imp, reduceCtorEq, false_and]

/-- A boundary interval leaves the epoch clock unchanged exactly when all its calls are silent. -/
theorem epochClock_interval_eq_iff (s : States)
    (pre middle suffix : List (Option EpochSecret)) :
    epochClock s (pre ++ middle ++ suffix) (pre.length + middle.length) =
      epochClock s (pre ++ middle ++ suffix) pre.length ↔
      ∀ k ∈ middle, k = none := by
  rw [epochClock_interval]
  rw [Nat.add_eq_left, List.length_eq_zero_iff, outputs_eq_nil_iff]

/-- A successful trace preserves the next-key epoch exactly when every call emits no key. -/
theorem TraceRun.keyFloor_eq_iff_silent {s t : States} {trace : List (Option EpochSecret)}
    (h : TraceRun s t trace) : keyFloor t = keyFloor s ↔ ∀ k ∈ trace, k = none := by
  rw [h.keyFloor_eq, Nat.add_eq_left, List.length_eq_zero_iff, outputs_eq_nil_iff]

end TraceExperiment
end spqr.v1.chunked.states
