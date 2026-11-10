/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
-/
import EpochTrace

namespace spqr.v1.chunked.states.TraceExperiment

-- The zero boundary exposes the initial next-key epoch.
example (s : States) (trace : List (Option EpochSecret)) :
    epochClock s trace 0 = keyFloor s := by
  simp only [epochClock, List.take_zero, outputs, List.length_nil, Nat.add_zero]

-- This pure-list example checks a silent call, an emission, and saturation.
example (s : States) (k : EpochSecret) :
    epochClock s [none, some k, none] 1 = keyFloor s ∧
    epochClock s [none, some k, none] 2 = keyFloor s + 1 ∧
    epochClock s [none, some k, none] 10 = keyFloor s + 1 := by
  simp only [epochClock, List.take_succ_cons, List.take_zero, List.take_nil, outputs,
    Option.toList_none, Option.toList_some, List.nil_append, List.singleton_append,
    List.length_cons, List.length_nil, Nat.add_zero, and_self]

-- A key at the first call is at the source floor, conditional on a valid trace.
example {s t : States} {suffix : List (Option EpochSecret)} {k : EpochSecret}
    (h : TraceRun s t (some k :: suffix)) : k.epoch.val = keyFloor s := by
  have he := TraceRun.emission_epoch (pre := []) h
  simpa only [outputs, List.length_nil, Nat.add_zero] using he

#print axioms TraceRun.keyFloor_eq
#print axioms TraceRun.cut_epochClock
#print axioms TraceRun.boundary_keyFloor_unique
#print axioms TraceRun.emission_epoch
#print axioms epochClock_prefix
#print axioms TraceRun.emission_epochClock
#print axioms epochClock_interval
#print axioms outputs_eq_nil_iff
#print axioms epochClock_interval_eq_iff
#print axioms TraceRun.keyFloor_eq_iff_silent
#print axioms spqr.v1.chunked.states.epochs_consecutive
#print axioms spqr.v1.chunked.states.Step.keyFloor_step

end spqr.v1.chunked.states.TraceExperiment
