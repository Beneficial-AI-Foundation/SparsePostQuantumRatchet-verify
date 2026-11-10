/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
-/
/-! Append this review fragment to `TraceRun.lean` in a temporary file, then run `lake env lean`.
The fragment deliberately does not duplicate or import a separately built experiment module. -/

namespace spqr.v1.chunked.states.TraceExperiment

-- Boundary cuts preserve the endpoint traces, without any realizability assumption on states.
example {s t : States} {trace : List (Option EpochSecret)} (h : TraceRun s t trace) :
    ∃ u, TraceRun s u [] ∧ TraceRun u t trace := by
  simpa only [List.take_zero, List.drop_zero] using h.cut 0

example {s t : States} {trace : List (Option EpochSecret)} (h : TraceRun s t trace) :
    ∃ u, TraceRun s u trace ∧ TraceRun u t [] := by
  simpa only [List.take_length, List.drop_length] using h.cut trace.length

-- These are list-level checks; no claim of an executable SPQR trace is made.
example : outputs [none, none] = [] := rfl
example : silentCount [none, none] = 2 := rfl

#print axioms outputs_append
#print axioms TraceRun.toRun
#print axioms Run.exists_trace
#print axioms run_iff_exists_trace
#print axioms TraceRun.append
#print axioms TraceRun.split
#print axioms traceRun_append_iff
#print axioms TraceRun.cut
#print axioms length_eq_outputs_add_silent
#print axioms outputs_length_le
#print axioms outputs_not_injective
#print axioms spqr.v1.chunked.states.Run.append

end spqr.v1.chunked.states.TraceExperiment
