# Reviewer's guide

## Objectives
The purpose of this document is to provide guidelines for PR reviewers of (functional correctness) formal specifications and proofs.
The purpose of the PRs themselves is to provide a second layer of quality control, ensuring that any specification (or proof thereof) maximizes, to the greatest extent possible, the following criteria:

	- Correctness; as a minimal standard, specifications _must_ be counterexample free. This is less of an issue for specifications with accompanying proofs, and more critical with axiomatic specs.
	- Simplicity; all other aspects being equal, a simple formulation is preferable (this partially also supports readability)
	- Readability / maintainability; the addition of comments, deliberate whitespacing (line-breaks, indents, etc.), and concise formulaic presentation can help ensure that, beyond the correctness provided by the existence of a proof, a specification is more easily understood by human readers
	- Verification performance; proofs have to be verified by CI, so among multiple equivalent proofs, the one with lowest build-time is preferred.

## Recommended steps for reviewers

We assume the typical review deals with a PR that isolates a single implementation-function, for which it provides a specification and a proof thereof, and follows our guideline recommended 500LOC cap.
For other kinds of PRs use the below as guidelines and apply your personal judgement accordingly.

### 1. Check for specification correctness
You can usually omit this step when the PR introduces a `sorry`-free proof, but for `axiom`s there are no such guardrails.
Since `axioms` are required to provide links to justifying sources, you should inspect those sources to ensure they are legitimate, and that the formulation of the axiom has been correctly transcribed. Any comments w.r.t. correctness should be _blocking_.

### 2. Asses the level of abstraction
Unless a particular specification is externally motivated, there is usually some degree of flexibility in the exact formulation. Consider the example of a function `f` returning the `Nat` value `r = 42`. The same function could be equipped with:
	- `r > 1`
	- `r != 0 /\ r % 2 = 0`
	- `r = 42`

All of the above are correct specifications, and they are progressively stronger (in the sense that each line implies the previous).
Which one to chose as _the_ specification usually depends on several factors:

	- Upstream requirements; assuming there is a function `g`, that calls `f`, and requires only that the output of `f` be greater than 1, it may make sense to specify only that much about the return value of `f`. In the example case above, the proof of `r = 42` implying `r > 1` is trivial, but this is not necessarily the case in general, and might represent additional work that would need to happen at the call site. Importantly, this applies mostly to the low-to-intermediate layers of a crate, for which all call-sites are known in advance. Functions in a crate that may be called outside of the known call-sites should have their specification tuned without any particular assumptions about upstream calls.
	- Ease of proof; practically, weaker specifications are often easier to prove, both in the sense of human understanding, as well as machine-verification. The difference might be performance-relevant, so it is often worthwhile to investigate, whenever a proof is particularly resource-intensive, whether a weaker formulation with a better-performant proof is usable.

It is also generally the case, that a specification should not simply re-state the implementation (save for very trivial functions). It is generally expected that specifications operate on the level of mathematical abstractions, as opposed to implementation primitives. For example, functions performing bit level operations (`x << k`, `y & 0xFF`, etc.) should have specifications describing the mathematical equivalent of the bit operations (`x * 2^k`, `y % 2^8`).

Comments regarding the level of abstraction _may_ be _blocking_ or _non-blocking_, according to judgement.

### 3. Observe performance
Due to the low cost and ease of use, it is recommended to prompt `!bench` on all but the shortest PRs, to observe the proof's impact on build time. Not all performance decreases are avoidable, and not all avoidable performance decreases are worth prioritizing immediately. Use your judgement to determine whether to

	- accept the PR as is,
	- accept the PR now, but open an issue to revisit performance in the future, or
	- block the ongoing PR until fixed

### 4. Comment freely
It is highly encouraged to comment any opinions regarding the specifications without reservation, including:

	- requests for adding or changing comments
	- recommendations for the introduction of new constants/functions
	- requests for generalizing proof chunks
	- recommendations for re-use of previously written spec code
	- pointing out incompatibilities with the style guide
	- etc.

These are generally _non-blocking_, and should be expect to be considered at the discretion of the original author, but may be made _blocking_ if particularly egregious (especially w.r.t. chunk generalization and code reuse).

It is recommended, even when only adding comments, to use the "Submit review > Comment" feature, over adding each comment individually.
