# Complete GitHub history catalog

Snapshot date: 2026-10-23. See the [history summary](../REPOSITORY_HISTORY_SUMMARY.md) for the synthesis and [AI review questions](../AI_PR_REVIEW_QUESTIONS.md) for practical use.

Every API-visible issue and PR has an entry below. Titles summarize the work item; body and discussion excerpts retain the original wording, with whitespace and Markdown simplified. An ellipsis marks shortening, not a complete paraphrase. Read the linked thread or [full text snapshot](github-history-2026-10-23.json) for the complete argument and replies. Historical statements may be superseded or disputed; an author saying a finding is fixed is not independent verification.

Coverage: 405 issues, 320 PRs, 442 conversation comments, 414 inline comments, 663 submitted reviews, and 2 commit comments. Empty review bodies are represented by their state; their inline comments appear separately. Review state is historical, not a claim of current approval. Closed PRs explicitly distinguish merged from unmerged.

## Open work index

- [43](#item-43) open: Add property catalog and spec coverage analysis
- [44](#item-44) open: Prove chain guards and state-machine epoch dispatch (PROP-9, PROP-14, PROP-17, PROP-21, PROP-30, D3)
- [48](#item-48) open: Evaluate collectAxioms audit vs probe-lean sorry detection
- [245](#item-245) open: Track potential generalisation of \`libcrux\_hmac.hmac\_sha256\_tag32\_length\_eq\_32\` to additional SHA variants and tag lengths
- [248](#item-248) open: Fully specify \`from\_seed\` behavioral properties (follow-up to #235)
- [277](#item-277) open draft: Model incremental ML-KEM primitives with pure companions and Hoare-style axioms
- [281](#item-281) open: Root Cause of the "No Goals to Be Solved" Error with \`3#usize\` Type Annotations
- [290](#item-290) open: Verify : \`serialize.rs\`
- [304](#item-304) open: Rust docs with per-function Lean verification panels
- [306](#item-306) open: Verify : \`v1/chunked/states/serialize.rs\`
- [317](#item-317) open: Specify and verify : \`spqr::v1::chunked::states::serialize::{spqr::v1::chunked::states::States}::into\_pb\` in \`v1/chunked/states/serialize.rs\`
- [318](#item-318) open: Specify and verify : \`spqr::v1::chunked::states::serialize::{spqr::v1::chunked::states::States}::from\_pb\` in \`v1/chunked/states/serialize.rs\`
- [364](#item-364) open: Consolidate \`Inhabited\` instances into \`Spqr/Auxiliary/Instances.lean\`
- [390](#item-390) open: Verify : \`v1/unchunked/send\_ct/serialize.rs\`
- [407](#item-407) open draft: Find structure: shared @\[step\] spec for Enumerate iterator and loop-body proof dedup
- [412](#item-412) open: Verify : \`lib.rs\`
- [434](#item-434) open: Specify and verify \`spqr::send\` in \`lib.rs\`
- [503](#item-503) open draft: Erasure Codes bridge
- [523](#item-523) open: Verify : \`v1/chunked/send\_ek/serialize.rs\`
- [528](#item-528) open: Specify and verify : \`spqr::v1::chunked::send\_ek::serialize::{spqr::v1::chunked::send\_ek::HeaderSent}::into\_pb\` in \`v1/chunked/send\_ek/serialize.rs\`
- [529](#item-529) open: Specify and verify : \`spqr::v1::chunked::send\_ek::serialize::{spqr::v1::chunked::send\_ek::HeaderSent}::from\_pb\` in \`v1/chunked/send\_ek/serialize.rs\`
- [530](#item-530) open: Specify and verify : \`spqr::v1::chunked::send\_ek::serialize::{spqr::v1::chunked::send\_ek::Ct1Received}::into\_pb\` in \`v1/chunked/send\_ek/serialize.rs\`
- [531](#item-531) open: Specify and verify : \`spqr::v1::chunked::send\_ek::serialize::{spqr::v1::chunked::send\_ek::Ct1Received}::from\_pb\` in \`v1/chunked/send\_ek/serialize.rs\`
- [532](#item-532) open: Specify and verify : \`spqr::v1::chunked::send\_ek::serialize::{spqr::v1::chunked::send\_ek::EkSentCt1Received}::into\_pb\` in \`v1/chunked/send\_ek/serialize.rs\`
- [533](#item-533) open: Specify and verify : \`spqr::v1::chunked::send\_ek::serialize::{spqr::v1::chunked::send\_ek::EkSentCt1Received}::from\_pb\` in \`v1/chunked/send\_ek/serialize.rs\`
- [568](#item-568) open: Harmonise all \`from\_pb/into\_pb\` pairs via functional models and prove round trips
- [587](#item-587) open: Harmonise \`spqr::v1::unchunked::send\_ct::serialize::Ct1Sent::{into\_pb, from\_pb}\` via functional models and prove round trips in \`v1/unchunked/send\_ct/serialize.rs\`
- [590](#item-590) open: Harmonise \`spqr::encoding::polynomial::PolyEncoder::{into\_pb, from\_pb}\` via functional models and prove round trips in \`encoding/polynomial.rs\`
- [591](#item-591) open: Harmonise \`spqr::encoding::polynomial::PolyDecoder::{into\_pb, from\_pb}\` via functional models and prove round trips in \`encoding/polynomial.rs\`
- [592](#item-592) open: Harmonise \`spqr::v1::chunked::send\_ek::serialize::KeysSampled::{into\_pb, from\_pb}\` via functional models and prove round trips in \`v1/chunked/send\_ek/serialize.rs\`
- [593](#item-593) open: Verify : \`v1/chunked/send\_ct/serialize.rs\`
- [594](#item-594) open: Specify and verify : \`spqr::v1::chunked::send\_ct::serialize::{spqr::v1::chunked::send\_ct::NoHeaderReceived}::into\_pb\` in \`v1/chunked/send\_ct/serialize.rs\`
- [595](#item-595) open: Specify and verify : \`spqr::v1::chunked::send\_ct::serialize::{spqr::v1::chunked::send\_ct::NoHeaderReceived}::from\_pb\` in \`v1/chunked/send\_ct/serialize.rs\`
- [596](#item-596) open: Specify and verify : \`spqr::v1::chunked::send\_ct::serialize::{spqr::v1::chunked::send\_ct::HeaderReceived}::into\_pb\` in \`v1/chunked/send\_ct/serialize.rs\`
- [597](#item-597) open: Specify and verify : \`spqr::v1::chunked::send\_ct::serialize::{spqr::v1::chunked::send\_ct::HeaderReceived}::from\_pb\` in \`v1/chunked/send\_ct/serialize.rs\`
- [598](#item-598) open: Specify and verify : \`spqr::v1::chunked::send\_ct::serialize::{spqr::v1::chunked::send\_ct::Ct1Sampled}::into\_pb\` in \`v1/chunked/send\_ct/serialize.rs\`
- [599](#item-599) open: Specify and verify : \`spqr::v1::chunked::send\_ct::serialize::{spqr::v1::chunked::send\_ct::Ct1Sampled}::from\_pb\` in \`v1/chunked/send\_ct/serialize.rs\`
- [600](#item-600) open: Specify and verify : \`spqr::v1::chunked::send\_ct::serialize::{spqr::v1::chunked::send\_ct::EkReceivedCt1Sampled}::into\_pb\` in \`v1/chunked/send\_ct/serialize.rs\`
- [601](#item-601) open: Specify and verify : \`spqr::v1::chunked::send\_ct::serialize::{spqr::v1::chunked::send\_ct::EkReceivedCt1Sampled}::from\_pb\` in \`v1/chunked/send\_ct/serialize.rs\`
- [602](#item-602) open: Specify and verify : \`spqr::v1::chunked::send\_ct::serialize::{spqr::v1::chunked::send\_ct::Ct1Acknowledged}::into\_pb\` in \`v1/chunked/send\_ct/serialize.rs\`
- [603](#item-603) open: Specify and verify : \`spqr::v1::chunked::send\_ct::serialize::{spqr::v1::chunked::send\_ct::Ct1Acknowledged}::from\_pb\` in \`v1/chunked/send\_ct/serialize.rs\`
- [604](#item-604) open: Specify and verify : \`spqr::v1::chunked::send\_ct::serialize::{spqr::v1::chunked::send\_ct::Ct2Sampled}::into\_pb\` in \`v1/chunked/send\_ct/serialize.rs\`
- [605](#item-605) open: Specify and verify : \`spqr::v1::chunked::send\_ct::serialize::{spqr::v1::chunked::send\_ct::Ct2Sampled}::from\_pb\` in \`v1/chunked/send\_ct/serialize.rs\`
- [607](#item-607) open: Harmonise \`spqr::v1::chunked::send\_ek::serialize::HeaderSent::{into\_pb, from\_pb}\` via functional models and prove round trips in \`v1/chunked/send\_ek/serialize.rs\`
- [608](#item-608) open: Harmonise \`spqr::v1::chunked::send\_ek::serialize::Ct1Received::{into\_pb, from\_pb}\` via functional models and prove round trips in \`v1/chunked/send\_ek/serialize.rs\`
- [609](#item-609) open: Harmonise \`spqr::v1::chunked::send\_ek::serialize::EkSentCt1Received::{into\_pb, from\_pb}\` via functional models and prove round trips in \`v1/chunked/send\_ek/serialize.rs\`
- [610](#item-610) open: Harmonise \`spqr::v1::chunked::send\_ct::serialize::NoHeaderReceived::{into\_pb, from\_pb}\` via functional models and prove round trips in \`v1/chunked/send\_ct/serialize.rs\`
- [611](#item-611) open: Harmonise \`spqr::v1::chunked::send\_ct::serialize::HeaderReceived::{into\_pb, from\_pb}\` via functional models and prove round trips in \`v1/chunked/send\_ct/serialize.rs\`
- [612](#item-612) open: Harmonise \`spqr::v1::chunked::send\_ct::serialize::Ct1Sampled::{into\_pb, from\_pb}\` via functional models and prove round trips in \`v1/chunked/send\_ct/serialize.rs\`
- [613](#item-613) open: Harmonise \`spqr::v1::chunked::send\_ct::serialize::EkReceivedCt1Sampled::{into\_pb, from\_pb}\` via functional models and prove round trips in \`v1/chunked/send\_ct/serialize.rs\`
- [614](#item-614) open: Harmonise \`spqr::v1::chunked::send\_ct::serialize::Ct1Acknowledged::{into\_pb, from\_pb}\` via functional models and prove round trips in \`v1/chunked/send\_ct/serialize.rs\`
- [615](#item-615) open: Harmonise \`spqr::v1::chunked::send\_ct::serialize::Ct2Sampled::{into\_pb, from\_pb}\` via functional models and prove round trips in \`v1/chunked/send\_ct/serialize.rs\`
- [616](#item-616) open: Harmonise \`spqr::v1::chunked::states::serialize::States::{into\_pb, from\_pb}\` via functional models and prove round trips in \`v1/chunked/states/serialize.rs\`
- [622](#item-622) open: Specify and verify \`spqr::recv::{impl core::ops::function::FnOnce for spqr::recv::closure}::call\_once\` in \`lib.rs\`
- [623](#item-623) open: Specify and verify \`recv\` in \`lib.rs\`
- [643](#item-643) open draft: Spec and proof of mlkem encaps1
- [645](#item-645) open: Proposal: compositional specs for the \`= ok\` statements
- [659](#item-659) open: Change \`public import\` to \`import\` whenever possible
- [662](#item-662) open: PROP-30: States::recv epoch and payload-type dispatch
- [663](#item-663) open draft: States::recv follows ML-KEM Braid §2.5 Receive, up to three deviations
- [685](#item-685) open: Verify \`src/v1/unchunked/send\_ek.rs\`
- [688](#item-688) open: specify and verify \`spqr::v1::unchunked::send\_ek::{spqr::v1::unchunked::send\_ek::EkSentCt1Received}::recv\_ct2\` in \`src/v1/unchunked/send\_ek.rs\`
- [690](#item-690) open: Specify and verify \`spqr::v1::unchunked::send\_ek::{spqr::v1::unchunked::send\_ek::HeaderSent}::send\_ek\` in 'src/v1/unchunked/send\_ek.rs'
- [693](#item-693) open: Verify \`src/v1/chunked/send\_ct.rs\`
- [696](#item-696) open: Specify and verify \`spqr::v1::chunked::send\_ct::{spqr::v1::chunked::send\_ct::Ct2Sampled}::send\_ct2\_chunk\` in \`src/v1/chunked/send\_ct.rs\`
- [697](#item-697) open: Specify and verify \`spqr::v1::chunked::send\_ct::{spqr::v1::chunked::send\_ct::Ct1Acknowledged}::epoch\` in \`src/v1/chunked/send\_ct.rs\`
- [698](#item-698) open: Specify and verify \`spqr::v1::chunked::send\_ct::{spqr::v1::chunked::send\_ct::EkReceivedCt1Sampled}::epoch\` in \`src/v1/chunked/send\_ct.rs\`
- [699](#item-699) open: Specify and verify \`spqr::v1::chunked::send\_ct::{spqr::v1::chunked::send\_ct::EkReceivedCt1Sampled}::send\_ct1\_chunk\` in \`src/v1/chunked/send\_ct.rs\`
- [700](#item-700) open: Specify and verify \`spqr::v1::chunked::send\_ct::{spqr::v1::chunked::send\_ct::Ct1Sampled}::epoch\` in \`src/v1/chunked/send\_ct.rs\`
- [701](#item-701) open: Specify and verify \`spqr::v1::chunked::send\_ct::{spqr::v1::chunked::send\_ct::Ct1Sampled}::send\_ct1\_chunk\` in \`src/v1/chunked/send\_ct.rs\`
- [702](#item-702) open: Specify and verify \`spqr::v1::unchunked::send\_ct::{spqr::v1::unchunked::send\_ct::HeaderReceived}::send\_ct1\` in \`src/v1/unchunked/send\_ct.rs\`
- [703](#item-703) open: Specify and verify \`spqr::v1::chunked::send\_ct::{spqr::v1::chunked::send\_ct::HeaderReceived}::send\_ct1\_chunk\` in \`src/v1/chunked/send\_ct.rs\`
- [704](#item-704) open: Specify and verify \`spqr::v1::chunked::send\_ct::{spqr::v1::chunked::send\_ct::NoHeaderReceived}::epoch\` in \`src/v1/chunked/send\_ct.rs\`
- [705](#item-705) open: Specify and verify \`spqr::v1::chunked::send\_ct::{spqr::v1::chunked::send\_ct::Ct2Sampled}::recv\_next\_epoch\` in \`src/v1/chunked/send\_ct.rs\`
- [706](#item-706) open: Specify and verify \`spqr::v1::chunked::send\_ct::send\_ct2\_encoder\` in \`src/v1/chunked/send\_ct.rs\`
- [707](#item-707) open: Specify and verify \`spqr::v1::chunked::send\_ct::{spqr::v1::chunked::send\_ct::Ct1Acknowledged}::recv\_ek\_chunk\` in \`src/v1/chunked/send\_ct.rs\`
- [708](#item-708) open: Specify and verify \`spqr::v1::chunked::send\_ct::{spqr::v1::chunked::send\_ct::EkReceivedCt1Sampled}::recv\_ct1\_ack\` in \`src/v1/chunked/send\_ct.rs\`
- [709](#item-709) open: Specify and verify \`spqr::v1::chunked::send\_ct::{spqr::v1::chunked::send\_ct::Ct1Sampled}::recv\_ek\_chunk\` in \`src/v1/chunked/send\_ct.rs\`
- [710](#item-710) open: Specify and verify \`spqr::v1::chunked::send\_ct::{spqr::v1::chunked::send\_ct::NoHeaderReceived}::recv\_hdr\_chunk\` in \`src/v1/chunked/send\_ct.rs\`
- [719](#item-719) open: specify and verify \`spqr::v1::unchunked::send\_ek::{spqr::v1::unchunked::send\_ek::EkSentCt1Received}::recv\_ct2\` in \`src/v1/unchunked/send\_ek.rs\`
- [721](#item-721) open: Remove 8 \`native\_decide\` proofs
- [723](#item-723) open: Specify and verify \`spqr::v1::chunked::send\_ct::{spqr::v1::chunked::send\_ct::Ct2Sampled}::send\_ct2\_chunk\` in \`src/v1/chunked/send\_ct.rs\`
- [724](#item-724) open: Specify and verify spqr::v1::chunked::send\_ct::{spqr::v1::chunked::send\_ct::Ct1Acknowledged}::epoch in src/v1/chunked/send\_ct.rs
- [725](#item-725) open: Specify and verify \`spqr::v1::chunked::send\_ct::{spqr::v1::chunked::send\_ct::EkReceivedCt1Sampled}::epoch\` in \`src/v1/chunked/send\_ct.rs\`
- [726](#item-726) open: Specify and verify \`spqr::v1::chunked::send\_ct::{spqr::v1::chunked::send\_ct::Ct1Sampled}::epoch\` in \`src/v1/chunked/send\_ct.rs\`

## Issues and pull requests

### Item 1

**[PR #1](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/1) — Extract entire crate and setup Lean project**

Status: merged. Opened: 2026-03-18. Author: oliver-butterley.

Body excerpt: All 9 modules extracted. A few functions excluded or made opaque because of extraction issues. However it appears that everything is fine with all the parts that are required for verification.

No recorded comments or reviews.

### Item 2

**[PR #2](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/2) — chore: update extraction scripts and arrange lean project**

Status: merged. Opened: 2026-03-30. Author: oliver-butterley.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 3

**[PR #3](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/3) — Verify some functions**

Status: merged. Opened: 2026-04-16. Author: truonghoangle.

Body excerpt: This PR specifies and verifies some functions

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/3#issuecomment-4263768033) — shaoweilin (2026-04-16): @Kukovec this PR looks good to me. I'm approving it and merging it with main.
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/3#pullrequestreview-4124754400) — shaoweilin (2026-04-16): (No text.)

### Item 4

**[PR #4](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/4) — Update lean.yml**

Status: merged. Opened: 2026-04-28. Author: Kukovec.

Body excerpt: Migrate Lean build action from dalek.

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/4#pullrequestreview-4189287534) — a-dangelo (2026-04-28): (No text.)

### Item 5

**[PR #5](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/5) — Create CODEOWNERS**

Status: merged. Opened: 2026-04-28. Author: Kukovec.

Body excerpt: (No text.)

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/5#pullrequestreview-4189282228) — a-dangelo (2026-04-28): (No text.)

### Item 6

**[PR #6](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/6) — Test PR**

Status: closed unmerged. Opened: 2026-04-28. Author: Kukovec.

Body excerpt: Do not merge

No recorded comments or reviews.

### Item 7

**[PR #7](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/7) — Test PR**

Status: closed unmerged. Opened: 2026-04-28. Author: Kukovec.

Body excerpt: Do not merge

No recorded comments or reviews.

### Item 8

**[Issue #8](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/8) — Create contribution guidelines**

Status: closed. Opened: 2026-04-28. Author: Kukovec.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 9

**[PR #9](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/9) — Action cleanup**

Status: merged. Opened: 2026-04-28. Author: Kukovec.

Body excerpt: Removes CI actions from base repo that got carried over by forking. Since we're not adding rust or editing hax/proverif, those actions only slow down our own CI.

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/9#pullrequestreview-4203992746) — oliver-butterley (2026-04-30): I love it!

### Item 10

**[Issue #10](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/10) — Create progress-tracking automation**

Status: closed. Opened: 2026-04-30. Author: oliver-butterley.

Body excerpt: - The number of target functions should ideally not fluctuate; unless otherwise specified, we target all of the functions in the repo. - Use the progress tracking from https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify/ with minor modifications.

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/10#issuecomment-4395344061) — oliver-butterley (2026-05-07): Update: will be adding a feature to Aeneas so it exports a \`manifest.json\` along with the Lean files. This will happen within a week or so, consequently waiting for this.
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/10#issuecomment-4478385087) — oliver-butterley (2026-05-18): @astefano is this issue solved with one of the probe tools?
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/10#issuecomment-4478695446) — astefano (2026-05-18): &gt; @astefano is this issue solved with one of the probe tools? progress tracking can be done from the info provided in the jsons generated by the probe tools (the progress tracking for dalek verus used \`probe-verus\`; and i remember i proposed something using \`probe-aeneas\` for dalek-lean but in the end, we each got caught up with other more urgent tasks and we didn't get to the point where we see if that PR can bring …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/10#issuecomment-4481427415) — oliver-butterley (2026-05-18): &gt; and i remember i proposed https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify/pull/681 using probe-aeneas for dalek-lean but in the end, we each got caught up with other more urgent tasks and we didn't get to the point where we see if that PR can bring something valuable.) The case of curve-dalek was rather different because there was already a working system so minimal advantage in changing …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/10#issuecomment-4484618624) — astefano (2026-05-19): &gt; If later we manage to extract more then that number increases. to me, public api functions can represent a better target: what we verify; but these public api functions call non public api functions which also need to be verified; meaning that we need to extract as much as possible. (target, to me, is for what we verify, not for what we extract.) &gt; Would you be able to use the probe tool in order to do the …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/10#issuecomment-4485259707) — oliver-butterley (2026-05-19): &gt; in principle, yes (though the devil is in the details); though i don't know how to prioritize stuff i'm working on: the time i'd need for this task is time i'd take from another task i should be doing. OK! I'll work on the assumption that we can't wait for this and implement our own solution for the moment.
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/10#issuecomment-4485894372) — astefano (2026-05-19): &gt; &gt; in principle, yes (though the devil is in the details); though i don't know how to prioritize stuff i'm working on: the time i'd need for this task is time i'd take from another task i should be doing. &gt; &gt; OK! I'll work on the assumption that we can't wait for this and implement our own solution for the moment. if you have the bandwidth (and the interest), could you consider if the output from \`probe-aeneas …

### Item 11

**[Issue #11](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/11) — Create profiling automation**

Status: closed. Opened: 2026-04-30. Author: oliver-butterley.

Body excerpt: Lean build times have previously been a noteworthy metric, we should include discussions on proof-time as part of the PR checklist We will use radar, just like mathlib and other Lean projects.

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/11#issuecomment-4371379393) — Kukovec (2026-05-04): If I may request a slight scope extenstion on tis issue: it would be nice to have a very short readme in our \`doc\` folder, explaining performance tracking (what we track, how to call the command, etc.) and expectations, to link in our PR guidelines.
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/11#issuecomment-4478360459) — oliver-butterley (2026-05-18): Update: Matej has setup the Radar server, @semaraugusto is setting up the scripts for the repos to deliver the appropriate data.
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/11#issuecomment-4488812441) — oliver-butterley (2026-05-19): &gt; If I may request a slight scope extenstion on tis issue: it would be nice to have a very short readme in our \`doc\` folder, explaining performance tracking (what we track, how to call the command, etc.) and expectations, to link in our PR guidelines. Once you have got the profiling active in this repo, can you also add a quick comment as Jure suggests to help users know how to take advantage of the profiling?
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/11#issuecomment-4506291203) — oliver-butterley (2026-05-21): Adding here so we don't forget, the current radar url is: https://radar.18.118.100.156.nip.io
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/11#issuecomment-4544197625) — Kukovec (2026-05-26): Note to self: resolve TODO in PR guide once this issue has been closed.

### Item 12

**[Issue #12](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/12) — Create PR template**

Status: closed. Opened: 2026-05-04. Author: Kukovec.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 13

**[Issue #13](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/13) — Migrate style guide**

Status: closed. Opened: 2026-05-04. Author: Kukovec.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 14

**[PR #14](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/14) — PR template**

Status: merged. Opened: 2026-05-04. Author: Kukovec.

Body excerpt: closes #12

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/14#pullrequestreview-4220246451) — Zhang-Liao (2026-05-04): (No text.)

### Item 15

**[Issue #15](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/15) — Verify: \`authenticator.rs\`**

Status: closed. Opened: 2026-05-04. Author: oliver-butterley.

Body excerpt: I.e., (specify and) verify all the (relevant) functions in this file.

No recorded comments or reviews.

### Item 16

**[Issue #16](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/16) — Specify and verify : \`spqr::authenticator::Authenticator::new\` in \`authenticator.rs\`**

Status: closed. Opened: 2026-05-04. Author: oliver-butterley.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 17

**[Issue #17](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/17) — Verify: \`encoding/gf.rs\`**

Status: closed. Opened: 2026-05-04. Author: truonghoangle.

Body excerpt: I.e., (specify and) verify all the (relevant) functions in this file.

No recorded comments or reviews.

### Item 18

**[Issue #18](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/18) — Verify: \`spqr::encoding::gf::unaccelerated::mul\` in \`gf.rs\`**

Status: closed. Opened: 2026-05-04. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 19

**[Issue #19](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/19) — Verify: \`spqr::encoding::gf::reduce::poly\_reduce\` in \`gf.rs\`**

Status: closed. Opened: 2026-05-04. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 20

**[Issue #20](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/20) — Specify and verify: \`spqr::encoding::gf::reduce::reduce\_bytes\` in \`gf.rs\`**

Status: closed. Opened: 2026-05-04. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 21

**[Issue #21](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/21) — Specify and verify: \`spqr::encoding::gf::reduce::reduce\_from\_byte\` in \`gf.rs\`**

Status: closed. Opened: 2026-05-04. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 22

**[Issue #22](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/22) — Specify and verify: \`spqr::encoding::gf::unaccelerated::mul2\` in \`gf.rs\`**

Status: closed. Opened: 2026-05-04. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 23

**[Issue #23](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/23) — Specify and verify: \`spqr::encoding::gf::GF16::ZERO\` in \`gf.rs\`**

Status: closed. Opened: 2026-05-04. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 24

**[Issue #24](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/24) — Specify and verify: \`spqr::encoding::gf::GF16::ONE\` in \`gf.rs\`**

Status: closed. Opened: 2026-05-04. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 25

**[Issue #25](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/25) — Specify and verify: \`spqr::encoding::gf::GF16::new\` in \`gf.rs\`**

Status: closed. Opened: 2026-05-04. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 26

**[Issue #26](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/26) — Specify and verify: \`spqr::encoding::gf::GF16::const\_mul\` in \`gf.rs\`**

Status: closed. Opened: 2026-05-04. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 27

**[Issue #27](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/27) — Specify and verify: \`spqr::encoding::gf::GF16::const\_sub\` in \`gf.rs\`**

Status: closed. Opened: 2026-05-04. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 28

**[Issue #28](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/28) — Specify and verify: \`spqr::encoding::gf::GF16::const\_div\` in \`gf.rs\`**

Status: closed. Opened: 2026-05-04. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 29

**[PR #29](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/29) — Style and PR guidelines**

Status: merged. Opened: 2026-05-04. Author: Kukovec.

Body excerpt: This PR: - Migrates \`STYLE\_GUIDE.md\` from dalek - Migrates \`CONTRIBUTING.md\` from dalek - Modifies \`WORKFLOW\_AND\_PR\_GUIDE.md\` from dalek: - Removes the \`Sync Status\` section - Changes the contents of the \`PR Workflow and Formatting\` section ❗ - Adds \`Performance\` and \`AI contributions\` sections closes #13 closes #8

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/29#pullrequestreview-4220670596) — truonghoangle (2026-05-04): (No text.)

### Item 30

**[PR #30](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/30) — Verify GF(2¹⁶) core arithmetic and reduction 11 functions in \`gf.rs\`**

Status: closed unmerged. Opened: 2026-05-04. Author: truonghoangle.

Body excerpt: This PR verify the core GF(2¹⁶) arithmetic primitives and reduction infrastructure in \`src/encoding/gf.rs\`. It provides specifications and proofs for eleven functions spanning the unaccelerated multiplication kernel, the table-driven polynomial reduction pipeline, and the \`GF16\` wrapper's constructor, constants, and const-evaluable arithmetic methods. Each function is verified against the algebraic model of GF(2¹⁶) …

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/30#issuecomment-4377102402) — truonghoangle (2026-05-05): bench!
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/30#issuecomment-4378132864) — Kukovec (2026-05-05): My main quesstion is: can you please split this into N PRs (1 per function?) On a side note: - \`bench!\` isn't implemented yet for this repo (the PR template is set up for the future ATM) - \`closes X Y\` parses as \`(closes X) (references Y)\`, not \`(closes X) (closes Y)\` fyi (if you check the issues linked, it will say "truonghoangle linked a pull request that will close this issue 11 hours ago" vs "truonghoangle …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/30#issuecomment-4378680487) — truonghoangle (2026-05-05): Thank you for your comments. I will close this PR and split this into N PRs
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/30#issuecomment-4378686629) — truonghoangle (2026-05-05): closed this PR and split this into N PRs

### Item 31

**[PR #31](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31) — Verify : \`spqr::encoding::gf::reduce::reduce\_from\_byte\` in \`gf.rs\`**

Status: merged. Opened: 2026-05-05. Author: truonghoangle.

Body excerpt: This PR verify \`spqr::encoding::gf::reduce::reduce\_from\_byte\` Function is verified against the algebraic model of \`GF(2¹⁶) ≅ GF(2)\[X\] / (X¹⁶ + X¹² + X³ + X + 1)\` defined in \`Spqr/Math/Gf.lean\`, with postconditions expressed both at the polynomial level \`(natToGF2Poly … %ₘ POLY\_GF2)\` and at the abstract field level \`(Nat.toGF216 = φ ∘ natToGF2Poly\` into \`GF216 = GaloisField 2 16)\`. Closed #21 Closed #33 Closed #37

Discussion and review record:

- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3189237816) — Kukovec (2026-05-05; Spqr/Math/Gf.lean:46): Might be worthwhile to intrtoduce an alias for \`(ZMod 2)\[X\]\`, I see it pop up in several places.
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3189310367) — Kukovec (2026-05-05; Spqr/Math/Gf.lean:205): If it ever happens that the proof gets deferred like this, I recommend opening an accompanying GH issue to track this and putting the issue # in the comment (if we ultimately decide never to prove this we can close that issue then with an appropriate elaboration). I'll integrate this into the PR guidelines as a recommendation (#32 )
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3189464960) — Kukovec (2026-05-05; Spqr/Math/Gf.lean:258): This lemma seems to be unused, do we need it for anything?
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3189581406) — Kukovec (2026-05-05; Spqr/Specs/Encoding/Gf/GF16/Add.lean:96): This is my Lean/Aeneas inexperience showing, where do I find the def of the GF216 overloaded \`+\`?
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3189661806) — Kukovec (2026-05-05; Spqr/Specs/Encoding/Gf/Reduce/PolyReduce.lean:92): This theorem appears to be unused.
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3189666919) — Kukovec (2026-05-05; Spqr/Specs/Encoding/Gf/Reduce/PolyReduce.lean:154): This theorem appears to be unused.
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3189672434) — Kukovec (2026-05-05; Spqr/Specs/Encoding/Gf/Reduce/PolyReduce.lean:214): This is the 2nd theorem that uses \`sorry\`, not flagged in the issue.
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3189681786) — Kukovec (2026-05-05; Spqr/Specs/Encoding/Gf/Reduce/ReduceFromByte.lean:80): Do we need this? The entire proof is just reflexivity.
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3189729818) — Kukovec (2026-05-05; Spqr/Specs/Encoding/Gf/Reduce/ReduceFromByte.lean:105): This theorem appears to be unused.
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3189731468) — Kukovec (2026-05-05; Spqr/Specs/Encoding/Gf/Reduce/ReduceFromByte.lean:106): This theorem appears to be unused.
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3189765687) — Kukovec (2026-05-05; Spqr/Specs/Encoding/Gf/Reduce/ReduceFromByte.lean:148): AFAICT this property only shows termination, but no actual properties of \`out/result\`. Since this is a reduction, I would expect a property that says something about the value of \`out\` after \`j\` steps. Also, this theorem appears to be unused.
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3189800578) — Kukovec (2026-05-05; Spqr/Specs/Encoding/Gf/Reduce/ReduceFromByte.lean:382): I'll defer to others to evaluate whether or not this Lean proof admits optimizations.
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3189808013) — Kukovec (2026-05-05; Spqr/Specs/Encoding/Gf/Reduce/ReduceFromByte.lean:529): This theorem appears to be unused.
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3189833077) — Kukovec (2026-05-05; Spqr/Specs/Encoding/Gf/Reduce/ReduceFromByte.lean:604): This theorem appears to be unused.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#pullrequestreview-4228965928) — Kukovec (2026-05-05): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3189957012) — truonghoangle (2026-05-05; Spqr/Math/Gf.lean:205): thank you for comments. I will follow the PR guidelines
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#pullrequestreview-4229791889) — truonghoangle (2026-05-05): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3189957426) — truonghoangle (2026-05-05; Spqr/Math/Gf.lean:258): Since this PR is split from a larger PR as required, I don't want to further subdivide the Gf.lean file for background help. The lemmas here will be used in the future. In general, when closing the PR for the gf.rs file, I will edit all related files and remove unused lemmas (that's my plan, but I'm not sure if this approach is suitable).
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#pullrequestreview-4229792379) — truonghoangle (2026-05-05): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3189997123) — truonghoangle (2026-05-05; Spqr/Math/Gf.lean:46): Is my choice as follows reasonable? \`abbrev GF2Poly := (ZMod 2)\[X\]\`
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#pullrequestreview-4229842578) — truonghoangle (2026-05-05): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3190040324) — truonghoangle (2026-05-05; Spqr/Specs/Encoding/Gf/GF16/Add.lean:96): In the \`Gf.lean\` file, line 30: \`abbrev GF216 := GaloisField 2 16\` GF216 stands for GaloisField 2 16. You can click on it to go to \`.lake/packages/mathlib/Mathlib/FieldTheory/Finite/GaloisField.lean\` I used \`GaloisField\` as the basis for writing these specs.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#pullrequestreview-4229889902) — truonghoangle (2026-05-05): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3190099308) — truonghoangle (2026-05-05; Spqr/Specs/Encoding/Gf/Reduce/ReduceFromByte.lean:105): yes it unused. I will remove it
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3190103884) — truonghoangle (2026-05-05; Spqr/Specs/Encoding/Gf/Reduce/ReduceFromByte.lean:106): it used in line 259
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3190149707) — truonghoangle (2026-05-05; Spqr/Specs/Encoding/Gf/Reduce/ReduceFromByte.lean:148): This theorem is used in the tactic \`step\*\`. In general, I usually write loop-related theorems so that the results are used to prove our main functions and I don't expect to write every desired property here. Furthermore, it will often depend on the final expectation of how the main function is specified. Each approach to the main function will give us an approach to creating loop theorems. This is my approach. …
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3190154954) — truonghoangle (2026-05-05; Spqr/Specs/Encoding/Gf/Reduce/ReduceFromByte.lean:529): I wil remove it
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3190188440) — truonghoangle (2026-05-05; Spqr/Specs/Encoding/Gf/Reduce/ReduceFromByte.lean:604): Actually, there are two ways to write the specification for reduce\_from\_byte, and I want to keep both.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#pullrequestreview-4229943280) — truonghoangle (2026-05-05): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3199621353) — oliver-butterley (2026-05-07; Spqr/Math/Gf.lean:54): Is it intentional that the identifier is in caps? If we are respecting notation in some paper, RFC, or code, let's follow that notation. Otherwise let's use the standard mathlib type formatting of names. Similar with various theorem names, let's use the mathlib conventions unless there are good reasons not to.
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3199689040) — oliver-butterley (2026-05-07; Spqr/Math/Gf.lean:62): \`\`\`suggestion lemma natToGF2Poly\_coeff (n m : Nat) : (natToGF2Poly n).coeff m = if n.testBit m then (1 : ZMod 2) else 0 := by \`\`\`
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3199783773) — oliver-butterley (2026-05-07; Spqr/Math/Gf.lean:47): Did you consider using \`Nat.bitIndices\` for this definition? I.e., something like: \`\`\`lean noncomputable def natToGF2Poly (n : ℕ) : (ZMod 2)\[X\] := (n.bitIndices.map (X ^ ·)).sum \`\`\` I think this would mean that there is already some machinery available for the types of problems we will encounter. Also, when we build new machinery we can upstream it in many cases.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#pullrequestreview-4241922963) — oliver-butterley (2026-05-07): First couple of comments, particularly concerning the choice of using \`Nat.bitIndices\`. I see that theory isn't fully developed but that can always be solved later. Does it seem a reasonable approach or there is a reason to have a custom definition in this case?
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3199859145) — oliver-butterley (2026-05-07; Spqr/Math/Gf.lean:47): Or maybe Nat.ofDigits... I'll look a bit more...
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#pullrequestreview-4242185369) — oliver-butterley (2026-05-07): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3200288669) — truonghoangle (2026-05-07; Spqr/Math/Gf.lean:54): Yes, that was intentional, since we are following the notation used in the original definition of \`Funs.lean\`. In particular, the \`constants\` in \`Funs.lean\` are themselves written in caps, so I kept the identifiers capitalized. That said, I am still trying to follow standard \`Mathlib\` naming conventions overall, although I admit I have occasionally been somewhat inconsistent or arbitrary in naming certain lemmas.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#pullrequestreview-4242670308) — truonghoangle (2026-05-07): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3200302325) — truonghoangle (2026-05-07; Spqr/Math/Gf.lean:47): I will try it!
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#pullrequestreview-4242685298) — truonghoangle (2026-05-07): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3201713559) — truonghoangle (2026-05-07; Spqr/Math/Gf.lean:47): Now I used \`\`\`noncomputable def natToGF2Poly (n : ℕ) : (ZMod 2)\[X\] := (n.bitIndices.map (X ^ ·)).sum\`\`\` and connect \`bitIndices\` to \`testBit\`
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#pullrequestreview-4244313482) — truonghoangle (2026-05-07): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3201768202) — truonghoangle (2026-05-07; Spqr/Specs/Encoding/Gf/Reduce/ReduceFromByte.lean:604): I removed it
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#pullrequestreview-4244372991) — truonghoangle (2026-05-07): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3215449135) — oliver-butterley (2026-05-10; Spqr/Math/Gf.lean:62): \`\`\`suggestion m ∈ n.bitIndices ↔ n.testBit m := by \`\`\` No need to write \`= true\`
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3215451446) — oliver-butterley (2026-05-10; Spqr/Math/Gf.lean:6): \`\`\`suggestion \`\`\` Remove \`import Spqr.Code.Funs\`, this is not required for these mathematical foundations.
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3215452363) — oliver-butterley (2026-05-10; Spqr/Math/Gf.lean:29): \`\`\`suggestion \`\`\` No need to \`open Aeneas Aeneas.Std Result\`, nothing from Aeneas is used in this file of mathematical foundations.
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3215454524) — oliver-butterley (2026-05-10; Spqr/Math/Gf.lean:330): The docstring for \`exists\_ringHom\_modByMonic\` seems to relate to something different. Am I missing something here?
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3215457656) — oliver-butterley (2026-05-10; Spqr/Math/Gf.lean:36): This choice of namespace doesn't match the contents of the file.
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3215463017) — oliver-butterley (2026-05-10; Spqr/Math/Gf.lean:306): \`\`\`suggestion simpa \[hφ\] using congrArg φ (Polynomial.modByMonic\_add\_div p hMonic) \`\`\` This lemma is a special case of \`modByMonic\_add\_div\`, is it useful having it as a separate statement?
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3215471103) — oliver-butterley (2026-05-10; Spqr/Math/Gf.lean:250): The docstring should describe what the theorem says (and maybe why it's true), not why the proof is hard.
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3215473170) — oliver-butterley (2026-05-10; Spqr/Math/Gf.lean:206): Better to restate this as \`Function.Injective natToGF2Poly\`. This matches the standard Mathlib API and will allow results related to injectivity to be used easily.
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3215474198) — oliver-butterley (2026-05-10; Spqr/Math/Gf.lean:139): \`\`\`suggestion @\[simp\] lemma natToGF2Poly\_zero : natToGF2Poly 0 = 0 := by \`\`\` This is a clear candidate as a simp lemma, one would always want to replace the LHS with the RHS.
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3215494907) — oliver-butterley (2026-05-10; Spqr/Math/Gf.lean:228): \`\`\`suggestion unfold POLY\_GF2; monicity! \`\`\`
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3215496700) — oliver-butterley (2026-05-10; Spqr/Math/Gf.lean:140): \`\`\`suggestion simp \[natToGF2Poly\] \`\`\` although this proof is so simple, maybe this doesn't need to be a lemma?
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3215507656) — oliver-butterley (2026-05-10; Spqr/Math/Gf.lean:109): \`\`\`suggestion rw \[List.sum\_map\_eq\_nsmul\_single a \_ fun \_ ha \_ =&gt; if\_neg ha.symm\] simp \[hnd.count, hmem\] \`\`\` This proof can be much shorter. On the other hand, I think this shouldn't be a separate lemma and instead just take advantage of lemmas already in Mathlib inline where this is currently used.
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3215531482) — oliver-butterley (2026-05-10; Spqr/Math/Gf.lean:87): \`\`\`suggestion theorem mem\_bitIndices\_iff\_testBit {n m : ℕ} : m ∈ n.bitIndices ↔ n.testBit m := by induction n using Nat.binaryRec generalizing m with | zero =&gt; simp | bit b n ih =&gt; cases m with | zero =&gt; rw \[Nat.testBit\_bit\_zero\]; cases b simp | succ m =&gt; rw \[Nat.testBit\_bit\_succ\]; cases b simp \[ih\] \`\`\` The proof can be shortened. As far as I can see this result isn't yet in Mathlib and is a rather fundamental and …
- [review CHANGES_REQUESTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#pullrequestreview-4259855091) — oliver-butterley (2026-05-10): I have several more comments. It's worthwhile us spending time to get the Lean code in \`Spqr/Math/Gf.lean\` done well since it will be used in many places. For the individual spec files this is less important. Also just some comments related to was to improve proofs.
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3216427950) — truonghoangle (2026-05-11; Spqr/Math/Gf.lean:36): These lemmas were initially developed to assist in establishing the specifications for the function \`spqr::encoding::gf::unaccelerated::mul\`; however, they subsequently found numerous applications in the development of other functions. Since I have now completed the implementation of the functions within the \`gf.rs\` file on my local machine-and have begun the process of editing and polishing the code to align with …
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#pullrequestreview-4260824910) — truonghoangle (2026-05-11): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3216473518) — truonghoangle (2026-05-11; Spqr/Math/Gf.lean:330): These homomorphisms were initially developed to assist in establishing the formal specification for the function \`spqr::encoding::gf::unaccelerated::mul\`. Originally, I intended to define this specification solely in terms of operations on \`GF2Poly\` (or \`POLY\_GF2\`), specifically using the multiplication form: \`natToGF2Poly result.val % (POLY\_GF2) = (natToGF2Poly a.val \* natToGF2Poly b.val) % (POLY\_GF2)\`. However, I …
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#pullrequestreview-4260872300) — truonghoangle (2026-05-11): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3216480658) — truonghoangle (2026-05-11; Spqr/Math/Gf.lean:6): I plan to place the definition \`noncomputable def GF16toGF216 (g : GF16) : GF216 := g.value.val.toGF216\` at the very end of the file; therefore, this import is required.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#pullrequestreview-4260881346) — truonghoangle (2026-05-11): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3216783995) — oliver-butterley (2026-05-11; Spqr/Math/Gf.lean:6): I see. However the main component of this file is purely mathematical, not dependent on the Rust code. I would keep the file truly independent and have a separate file which imports both this one and Spqr.Code.Funs. This way there is a clear separation of interests.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#pullrequestreview-4261208227) — oliver-butterley (2026-05-11): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3216788561) — oliver-butterley (2026-05-11; Spqr/Math/Gf.lean:330): RIght, I now understand how this came to exist in this form. Yes, this docstring should be reduced to describe exactly the theorem it is attached to.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#pullrequestreview-4261212922) — oliver-butterley (2026-05-11): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3216800855) — oliver-butterley (2026-05-11; Spqr/Math/Gf.lean:36): Of those two I would opt for spqr.math.gf. Easy to refactor later if we decide different terminology for the namespaces but important that it isn't mixed up in the other namespace which has a very particular meaning.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#pullrequestreview-4261225225) — oliver-butterley (2026-05-11): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3216872675) — oliver-butterley (2026-05-11; Spqr/Math/Gf.lean:205): I very much like systematically tracking any new sorry using an issue and linking it as a todo note. Let's do this in general. However, in this very specific case it is worth pushing a bit more on completing this proof at the moment since it is closely tided to the rest of the contents of this file. Since this file is mathematical foundation for much of the other work, it is useful to get it complete. I was able to …
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#pullrequestreview-4261306502) — oliver-butterley (2026-05-11): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3216940196) — truonghoangle (2026-05-11; Spqr/Math/Gf.lean:205): Over the weekend, I successfully resolved this issue by following a guide similar to the one you saw. Although there are alternative approaches to the proof, I found that this method aligns well with the specific relationships between Nat-level operations and polynomial-level operations required within our specification framework. I will open a new PR once this current one has been finalized.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#pullrequestreview-4261393002) — truonghoangle (2026-05-11): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3216993591) — truonghoangle (2026-05-11; Spqr/Math/Gf.lean:6): I also believe that this is crucial for ensuring clarity. However, I have not yet determined where the file should be located or what its name should be. For instance, in the folder corresponding to \`Spqr/Specs/Encoding/Gf\`-specifically \`gf.rs\`-we have a file named \`Basic.lean\` that contains these fundamental definitions. Yet, this approach also strikes me as somewhat illogical.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#pullrequestreview-4261451544) — truonghoangle (2026-05-11): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3217064215) — oliver-butterley (2026-05-11; Spqr/Math/Gf.lean:6): Yes, it is not such an easy problem to solve but crucial for ensuring clarity!
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#pullrequestreview-4261532754) — oliver-butterley (2026-05-11): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3217071769) — oliver-butterley (2026-05-11; Spqr/Math/Gf.lean:87): So we can remember this, can you add a comment close to this lemma, something like: \`-- prepare and upstream to Mathlib/Data/Nat/BitIndices.lean\`.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#pullrequestreview-4261540685) — oliver-butterley (2026-05-11): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3217085646) — oliver-butterley (2026-05-11; Spqr/Math/Gf.lean:205): Well done! I'm guessing we took a similar approach, using the nat level operations to produce a concrete representation. Did your proof work without using native\_decide?
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#pullrequestreview-4261555766) — oliver-butterley (2026-05-11): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3217114314) — truonghoangle (2026-05-11; Spqr/Math/Gf.lean:205): I do not use \`native\_decide\`. To me, the \`native\_decide\` tactic is off-limits-much like \`sorry\`.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#pullrequestreview-4261587843) — truonghoangle (2026-05-11): (No text.)
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#issuecomment-4418567040) — oliver-butterley (2026-05-11): Hi @truonghoangle! Great work. Sorry for all the comments but it is important that we get the mathematical foundations reasonably solid. Really this PR should have been the complete mathematical foundations (including the irreducibility proof) but not including the proofs of the spec theorems. This way it is a complete logical unit. Let's try to do this in the future. However, for this occasion let's proceed like …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#issuecomment-4418754982) — truonghoangle (2026-05-11): @oliver-butterley Your review and the proposed file structure for the mathematical theory are entirely accurate. However, I suggest that all these components be placed under \`Spqr/Math/Gf\` or \`Spqr/Math/Encoding/Gf\`. This is because we will also need to further develop the mathematical theory for the \`polynomial.rs\` file-as illustrated in the diagram below-at which point those developments would reside in …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#issuecomment-4418811297) — oliver-butterley (2026-05-11): &gt; However, I suggest that all these components be placed under \`Spqr/Math/Gf\` or \`Spqr/Math/Encoding/Gf\`. Quite possibly! You surely know better the best way to structure the files. I would avoid "encoding" here since this files contain the mathematical notions of specific galois fields. They aren't encoding until they are applied. How about folders \`Spqr/Math/Gf2Poly/\`, \`Spqr/Math/Gf16/\`, \`Spqr/Math/Poly/\`, each …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#issuecomment-4418843541) — truonghoangle (2026-05-11): &gt; \`Spqr/Math/Gf2Poly/\`, \`Spqr/Math/Gf16/\`, \`Spqr/Math/Poly/\` I think it's reasonable. I will re-split the file according to this arrangement.
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#issuecomment-4419050671) — truonghoangle (2026-05-11): What exactly is the \`namespace\` that we place here during the separation process? In general, what are the rules regarding \`namespaces\` in this context?
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#issuecomment-4419271266) — oliver-butterley (2026-05-11): &gt; What exactly is the \`namespace\` that we place here during the separation process? In general, what are the rules regarding \`namespaces\` in this context? For the moment choose something which makes it clear that this is abstract mathematical work and not connected to the implementation code. As long as it is separate, it is easy to refactor later.
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#issuecomment-4419323572) — oliver-butterley (2026-05-11): Two more comments: 1. Currently \`φ\` is defined using classical.choice using a theorem which guarantees the existence but isn't constructive. Typically it's good to avoid this approach unless there is no other option. In this case we can explicitly construct the object. I tried the following and was able to complete the full argument. It makes some stuff later rather simpler. (I can share the full file if useful but …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#issuecomment-4423941240) — truonghoangle (2026-05-11): The latest revision of this PR focuses on restructuring the mathematical theory layer. The previously monolithic Spqr/Math/Gf.lean file has been refactored into a set of smaller, specialized modules, and Mathlib-consistent naming conventions have been propagated throughout all dependent specification files.
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3224167056) — oliver-butterley (2026-05-12; Spqr/Math/Gf2Poly/Basic.lean:203): Add \`import Mathlib.Algebra.CharP.Two\` at the top of the file and then this proof is instant: \`\`\`suggestion /-- In characteristic \`2\`, negation is the identity on \`BinaryPoly\`. -/ lemma BinaryPoly.neg\_eq (a : BinaryPoly) : -a = a := CharTwo.neg\_eq a \`\`\`
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3224171265) — oliver-butterley (2026-05-12; Spqr/Math/Gf2Poly/Basic.lean:208): Add import Mathlib.Algebra.CharP.Two at the top of the file and then this proof is instant: \`\`\`suggestion /-- In characteristic \`2\`, subtraction in \`BinaryPoly\` agrees with addition. -/ lemma BinaryPoly.sub\_eq\_add (a b : BinaryPoly) : a - b = a + b := CharTwo.sub\_eq\_add a b \`\`\`
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3224215277) — oliver-butterley (2026-05-12; Spqr/Math/Gf2Poly/Basic.lean:30): \`\`\`suggestion \`\`\` The updated identifiers are great! Nice work. However best to remove this paragraph from the module doc string and keep just the essentials here.
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3224223522) — oliver-butterley (2026-05-12; Spqr/Math/Gf2Poly/Basic.lean:54): Was it a conscious decision to define \`BinaryPoly\` without namespace? Maybe you intended to put it in the names space with all the other things?
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3224236985) — oliver-butterley (2026-05-12; Spqr/Math/Gf2Poly/Basic.lean:99): \`\`\`suggestion · simp only \[hm\] \`\`\` Here and in 3 other places in this file \`↓reduceIte\` can be removed, simp automatically does this.
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3224241650) — oliver-butterley (2026-05-12; Spqr/Math/Gf2Poly/Basic.lean:103): \`\`\`suggestion simp only \[hm\] \`\`\`
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3224249102) — oliver-butterley (2026-05-12; Spqr/Math/Gf2Poly/NatRep.lean:261): \`\`\`suggestion private lemma natBinaryPolyNoDivisorOfDeg\_polyGF2 (d : Nat) (hd : 1 ≤ d) (hd8 : d ≤ 8) : \`\`\` I think this change makes it consistent. Is that correct?
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3224295982) — oliver-butterley (2026-05-12; Spqr/Math/Gf2Poly/NatRep.lean:42): I believe it would be better for this to be \`well-founded\` rather than using fuel. However, shall we finish this PR and leave this refactor until another occasion? If so, open an issue for this refactor and then add a \`TODO\` comment here linking to the issue.
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3224404171) — oliver-butterley (2026-05-12; Spqr/Math/Gf16/Basic.lean:61): 1 or 0?
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3224407372) — oliver-butterley (2026-05-12; Spqr/Math/Gf16/Field.lean:17): \`\`\`suggestion \`\`\`
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3224409814) — oliver-butterley (2026-05-12; Spqr/Math/Gf16/Field.lean:27): \`\`\`suggestion \`\`\`
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3224421718) — oliver-butterley (2026-05-12; Spqr/Math/Gf2Poly/NatRep.lean:26): \`\`\`suggestion \`\`\`
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3224446512) — oliver-butterley (2026-05-12; Spqr/Math/Gf16/Field.lean:72): Could you instead define \`GF16.toGF216\` so that using dot-notation one can use \`.toGF216\` for more concise spec theorem statements?
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3224467142) — oliver-butterley (2026-05-12; Spqr/Specs/Encoding/Gf/Reduce/PolyReduce.lean:92): @truonghoangle Are these theorems which are now covered in the mathematical foundation lean files in Spqr/Math/...? As such they should be removed from this file?
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3224493131) — oliver-butterley (2026-05-12; Spqr/Specs/Encoding/Gf/Reduce/PolyReduce.lean:92): What's the plan with this theorem? This doesn't belong here.
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3224518112) — oliver-butterley (2026-05-12; Spqr/Specs/Encoding/Gf/Unaccelerated/Mul.lean:66): In this file various partial results have been added. It's hard to look at this and see what makes sense. Can we avoid this additions until there is a complete proof which hence justifies the additions?
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#pullrequestreview-4269657835) — oliver-butterley (2026-05-12): Great improvements! I have a few more comments. - New identifier choices are fantastic. - BinaryPoly.neg\_eq and BinaryPoly.sub\_eq\_add appear good candidates as simp lemmas. - I thought a bit more about namespaces. It's uncomfortable how all the math foundation related to GF16 and Gf2Poly are in \`spqr.math.gf\` which mentions spqr whilst all of this maths is abstract, independent of spqr. It would be better if these …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#issuecomment-4428424710) — truonghoangle (2026-05-12): &gt; \* I thought a bit more about namespaces. It's uncomfortable how all the math foundation related to GF16 and Gf2Poly are in \`spqr.math.gf\` which mentions spqr whilst all of this maths is abstract, independent of spqr. It would be better if these were in their own namespace, following mathlib conventions. Shall we leave this adjustment to the next PR? I think we should treat this as a separate discussion point, …
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3224692390) — truonghoangle (2026-05-12; Spqr/Math/Gf2Poly/Basic.lean:54): I plan to design a set of common notations for the entire projecs -notations that do not belong to any specific namespace- in order to ensure consistency across the whole project. Placing such symbols within a namespace would imply that they are intended for local use only.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#pullrequestreview-4270306762) — truonghoangle (2026-05-12): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3224813695) — truonghoangle (2026-05-12; Spqr/Math/Gf2Poly/Basic.lean:99): It is actually generated when I use \`simp?\`. I've never tried removing the output of \`simp?\` without triggering unnecessary errors. Thank you!
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#pullrequestreview-4270469207) — truonghoangle (2026-05-12): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3224858873) — truonghoangle (2026-05-12; Spqr/Math/Gf16/Field.lean:72): I would like to transform the following form: \`\`\` @\[step\] theorem add\_assign\_spec (self other : GF16) : add\_assign self other ⦃ (result : GF16) =&gt; GF16toGF216 result = GF16toGF216 self + GF16toGF216 other ⦄ := by \`\`\` into: \`\`\` @\[step\] theorem add\_assign\_spec (self other : GF16) : add\_assign self other ⦃ (result : GF16) =&gt; result.toGF216 = self.toGF216 + other.toGF216 ⦄ := by \`\`\` Do you know how to handle this?
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#pullrequestreview-4270517747) — truonghoangle (2026-05-12): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3224915366) — truonghoangle (2026-05-12; Spqr/Specs/Encoding/Gf/Reduce/PolyReduce.lean:92): Since this PR was split off from a larger, more comprehensive PR, I have not deleted the comments related to it. I will revisit this matter in subsequent PRs.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#pullrequestreview-4270582526) — truonghoangle (2026-05-12): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3224927377) — truonghoangle (2026-05-12; Spqr/Specs/Encoding/Gf/Unaccelerated/Mul.lean:66): Since this PR was split off from a larger one, with the aim of proving this theorem, I have not deleted the objectives I intended to pursue. I will revisit this matter in subsequent PRs.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#pullrequestreview-4270595729) — truonghoangle (2026-05-12): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3224985523) — truonghoangle (2026-05-12; Spqr/Math/Gf16/Field.lean:72): I have found the solution to the problem!
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#pullrequestreview-4270661105) — truonghoangle (2026-05-12): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3224994090) — oliver-butterley (2026-05-12; Spqr/Math/Gf16/Field.lean:72): Yes! That is exactly what I had in mind. Very smooth statemetns. Doesn't it work if you define \`def GF16.toGF216 (g : GF16) : GF216 := g.value.val.toGF216\`?
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#pullrequestreview-4270672074) — oliver-butterley (2026-05-12): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3224998478) — oliver-butterley (2026-05-12; Spqr/Math/Gf2Poly/Basic.lean:99): Ah! That explains why there were extra things that weren't required in the proof. :wink:
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#pullrequestreview-4270676615) — oliver-butterley (2026-05-12): (No text.)
- [review DISMISSED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#pullrequestreview-4271369034) — oliver-butterley (2026-05-12): It's all a bit confused because of some of the spec theorem files are edited but haven't been fully proven. In future let's keep all the PRs with a precise limited scope so it is easy for everyone to see what is happening. Great work with so much solid mathematical foundations! That's going to make things much smoother for everyone. Given the current situation, merge this when you are ready. Then in more issues and …
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#discussion_r3226526445) — truonghoangle (2026-05-12; Spqr/Math/Gf16/Basic.lean:61): 1
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#pullrequestreview-4272420505) — truonghoangle (2026-05-12): (No text.)
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#issuecomment-4430763677) — truonghoangle (2026-05-12): I wasn't able to merge it. How do I do that?
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#pullrequestreview-4274673036) — oliver-butterley (2026-05-12): (No text.)
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#issuecomment-4433183984) — oliver-butterley (2026-05-12): &gt; I wasn't able to merge it. How do I do that? This is mysterious... I'm trying to troubleshoot. It claims that it is waiting for one check but I don't understand why it doesn't just run the check!
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#issuecomment-4433237946) — oliver-butterley (2026-05-12): &gt; &gt; I wasn't able to merge it. How do I do that? &gt; &gt; This is mysterious... I'm trying to troubleshoot. It claims that it is waiting for one check but I don't understand why it doesn't just run the check! I think I've understood the issue: I see the aeneas extraction workflow is a required check before merging. However it is only set to run on \`push\` not on \`pull\_request\`. I believe this leads to github waiting for a …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/31#issuecomment-4442464061) — Kukovec (2026-05-13): &gt; I think I've understood the issue: I see the aeneas extraction workflow is a required check before merging. Yeah, seems to be the same issue we had originally with the Lean Verification workflow. I can fix the CI in a sperate PR, merge that and merge this pr afterwards

### Item 32

**[Issue #32](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/32) — Update PR guidelines**

Status: closed. Opened: 2026-05-05. Author: Kukovec.

Body excerpt: Add: - Section on who is expected to perform merging - Section on code length - Section on how to track \`sorry\`s as inspired by Slack discussions and live conversations.

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/32#issuecomment-4395488473) — oliver-butterley (2026-05-07): Notes: - It's the PR author's responsibility to merge the PR - Small PR to largest extent possible and PR only touches a single issue - How to deal with changing numbers of sorry - Open issue when a sorry is left within the code and add the link as a comment in the source - Statement about AI contributions.

### Item 33

**[Issue #33](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/33) — Verify: \`Irreducible X¹⁶ + X¹² + X³ + X + 1\` in \`Spqr/Math/Gf.lean\`**

Status: closed. Opened: 2026-05-06. Author: truonghoangle.

Body excerpt: Verify: \`theorem POLY\_GF2\_irreducible : Irreducible POLY\_GF2 := by sorry\` in the file Spqr/Math/Gf.lean.

No recorded comments or reviews.

### Item 34

**[Issue #34](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/34) — Add warning diff infrastructure**

Status: closed. Opened: 2026-05-07. Author: oliver-butterley.

Body excerpt: Similar to what is currently in curve-dalek repo. Runs on CI to display how the numbers of warnings have increased and decreased.

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/34#issuecomment-4420361664) — oliver-butterley (2026-05-11): It seems likely that the warning diffs can be integrated into the radar profiling. I'm investigating further.
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/34#issuecomment-4478375489) — oliver-butterley (2026-05-18): @astefano is this issue covered with your recent PR? Otherwise I'll go ahead and copy over what we have in curve-dalek (I had forgotten about this issue and two weeks passed 🤣).
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/34#issuecomment-4485429954) — astefano (2026-05-19): &gt; @astefano is this issue covered with your recent PR? Otherwise I'll go ahead and copy over what we have in curve-dalek (I had forgotten about this issue and two weeks passed 🤣). https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/39 only looks into tracking sorries and providing an axiom audit, it doesn't look into all Lean warnings. Note that the warnings workflow from dalek lean …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/34#issuecomment-4485554597) — oliver-butterley (2026-05-19): &gt; https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/39 builds once. https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/39 also tries to do the reporting with minimal permissions. Yep, that workflow can be improved when someone has some bandwidth. 😉

### Item 35

**[Issue #35](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/35) — add vscode rule setting and paragraph width guidelines**

Status: closed. Opened: 2026-05-12. Author: oliver-butterley.

Body excerpt: And various other settings like tab width, trailing new lines.

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/35#issuecomment-4478347984) — oliver-butterley (2026-05-18): closed with #36

### Item 36

**[PR #36](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/36) — Chore: add vscode settings and style\_guide comment**

Status: merged. Opened: 2026-05-12. Author: oliver-butterley.

Body excerpt: Add the vscode settings file. Notable effects: - Ruler at column 100 as a visual guide. Tab key inserts 2 spaces (no tab characters). - On save: file is UTF-8 with LF line endings, trailing whitespace stripped, single final newline enforced. - .elan/ and .lake/ are read-only in the editor. - VSCode's git UI warns before direct commits or force-pushes to main. Add a paragraph to the style guide concerning paragraphs …

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/36#pullrequestreview-4274713501) — truonghoangle (2026-05-12): (No text.)

### Item 37

**[Issue #37](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/37) — add mathematical foundations for GF216 and GFPoly**

Status: closed. Opened: 2026-05-12. Author: oliver-butterley.

Body excerpt: Mathematical foundations and full API for these mathematical objects so they can be used easily for writing and proving specs.

No recorded comments or reviews.

### Item 38

**[Issue #38](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/38) — Automate sorry-delta detection on PRs**

Status: closed. Opened: 2026-05-12. Author: astefano.

Body excerpt: ## Problem When a PR introduces new \`sorry\` uses (directly or transitively), reviewers have no automated way to spot them. The PR template asks contributors to manually call out proof cheats, but this relies on self-reporting and is easy to miss — especially for transitive sorry dependencies introduced through helper lemmas. The \`sorry\` axiom (\`sorryAx\`) is Lean's escape hatch for unfinished proofs. Any theorem that …

No recorded comments or reviews.

### Item 39

**[PR #39](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/39) — Add audit sorries**

Status: merged. Opened: 2026-05-12. Author: astefano.

Body excerpt: This PR adds: \* \*\*Axiom audit and sorry-manifest generation\*\* (\`Audit.lean\`): a single Lean metaprogram that runs on every CI build, reports all non-builtin axioms used by the project (with focused output for \`sorryAx\` traces through \`Spqr.Specs.\*\`), and writes a machine-readable \`sorry-manifest.txt\` classifying each sorry-tainted declaration as \_direct\_ or \_transitive\_. \* \*\*Sorry-delta reporting\*\* …

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/39#issuecomment-4435054059) — astefano (2026-05-12): tested on a toy project: https://github.com/Beneficial-AI-Foundation/test\_sorry\_detection/pull/1; feel free to experiment there with creating PRs with sorries or not to see if what happens is what you want to see.
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/39#issuecomment-4435068154) — github-actions[bot] (2026-05-12): ### Sorry Delta No baseline available for comparison. Current sorry-tainted declarations: 164
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/39#issuecomment-4435150863) — github-actions[bot] (2026-05-12): ### Sorry Delta No baseline available for comparison. Current sorry-tainted declarations: 165
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/39#discussion_r3230106785) — Copilot (2026-05-12; .github/workflows/lean.yml:52): \`actions/cache/restore\` is configured with \`restore-keys: sorry-manifest-\`, so if the exact base SHA cache entry is missing it may restore an unrelated manifest (potentially even from the PR branch). That can produce incorrect sorry deltas (false positives/negatives). Prefer restoring only the exact \`${{ github.event.pull\_request.base.sha }}\` cache, and if it’s missing treat it as “no baseline” (or gate the baseline …
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/39#discussion_r3230106826) — Copilot (2026-05-12; .github/workflows/lean.yml:29): The job-level token permissions include \`pull-requests: write\` and \`issues: write\` for all events (including \`push\`). For least privilege, consider splitting into a PR-only job with write permissions (for commenting) and a push-only job that keeps permissions read-only.
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/39#discussion_r3230106846) — Copilot (2026-05-12; .github/workflows/lean.yml:98): On \`pull\_request\` workflows from forks, \`GITHUB\_TOKEN\` is typically read-only and cannot create/update PR comments even if \`permissions\` are set. If fork PRs are in scope, consider a \`pull\_request\_target\`-based reporter job (with a safe checkout strategy) or fall back to job summary only when comment writes aren’t permitted.
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/39#discussion_r3230106861) — Copilot (2026-05-12; .github/workflows/lean.yml:98): PR description mentions \`sorry-diff.sh\`, but the workflow runs \`scripts/sorry-diff.py\`. Please align the PR description and/or filenames so reviewers know which artifact is actually used in CI.
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/39#discussion_r3230106879) — Copilot (2026-05-12; scripts/sorry-diff.py:105): The manifest diff compares whole lines, so if an existing declaration changes kind (e.g. \`transitive\` → \`direct\`), it will be reported as a “new sorry-tainted declaration” even though it wasn’t newly introduced. Consider diffing by declaration identity (module+name) and optionally reporting kind-changes separately.
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/39#discussion_r3230106894) — Copilot (2026-05-12; scripts/sorry-diff.py:93): \`gh api repos/{repo}/issues/{pr\_number}/comments\` returns only the first page by default; if the marker comment isn’t in the first page, the script may post duplicates instead of updating. Consider using \`--paginate\` (or \`?per\_page=100\` plus pagination) when listing comments.
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/39#discussion_r3230106917) — Copilot (2026-05-12; scripts/SorryLister.lean:10): The header comment says it considers only theorem/def/opaque, but the implementation also includes \`.axiomInfo\` in \`allProjectDecls\`. Either update the docstring to include axioms, or filter them out to match the stated behavior.
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/39#discussion_r3230106947) — Copilot (2026-05-12; scripts/PrintAxioms.lean:180): In Section 2, a specs theorem that is itself \`directSorrySet\` won’t be reported as a sorry origin because of \`cur != nm\`, and will fall through to the “origin not in project” message. Handle the \`nm ∈ directSorrySet\` case explicitly (e.g., treat \`nm\` as an origin) so direct-sorry specs are reported correctly.
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/39#discussion_r3230106970) — Copilot (2026-05-12; scripts/PrintAxioms.lean:9): The file header says it audits axioms for each theorem/def/opaque, but \`env.constants.fold\` also includes \`.axiomInfo\`. Please align the comment with the actual behavior (or exclude axioms from the scan).
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/39#pullrequestreview-4276543160) — copilot-pull-request-reviewer (2026-05-12): ## Pull request overview Adds CI automation to audit axiom usage and surface newly introduced \`sorry\`-tainted declarations on pull requests, aiming to make proof unsoundness visible to reviewers without manual tracking. \*\*Changes:\*\* - Introduces Lean metaprograms to (a) print non-builtin axiom usage and trace \`sorryAx\` into \`Spqr.Specs.\*\`, and (b) generate a machine-readable \`sorry-manifest.txt\`. - Adds a Python …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/39#issuecomment-4435237684) — github-actions[bot] (2026-05-12): ### Sorry Delta No baseline available for comparison. Current sorry-tainted declarations: 165
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/39#discussion_r3230192969) — Copilot (2026-05-12; scripts/sorry-diff.py:35): \`read\_manifest\` keys entries by \`(module, decl)\`. Since \`decl\` is globally unique in Lean, including \`module\` in the identity will cause false positives when a declaration is moved between files/modules (same decl name, different module) — it will be reported as “new” even though no new sorry-tainted declaration was introduced. Consider keying by \`decl\` only (and keeping \`module\` just for display), and adjust the …
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/39#discussion_r3230193017) — Copilot (2026-05-12; .github/workflows/lean.yml:82): The cache key for restoring the baseline manifest is an exact match on \`pull\_request.base.sha\`, and there are no \`restore-keys\` fallbacks. If the base commit didn’t run this workflow (e.g., because the \`push.paths\` filter skipped a docs-only commit), the baseline will be missing and the delta becomes unavailable even though an older baseline would still be valid. Consider adding a branch-scoped key + \`restore-keys\` …
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/39#discussion_r3230193049) — Copilot (2026-05-12; .github/workflows/lean.yml:94): The workflow saves a sorry-manifest cache on every non-PR run using a per-commit key (\`sorry-manifest-${{ github.sha }}\`). Since \`push\` runs on all branches, this will create a new cache entry for every commit on every branch, which can quickly exhaust Actions cache quota and evict useful entries. Consider restricting the save step to the default branch (or whichever branches can serve as PR bases), and/or use a …
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/39#discussion_r3230193079) — Copilot (2026-05-12; .github/workflows/lean.yml:33): The job-level \`permissions\` grant \`pull-requests: write\` and \`issues: write\` for all events, including \`push\`. That increases the blast radius of any compromised build step on branch pushes. Consider splitting into separate jobs (or workflows) so \`push\` runs with read-only permissions, and only the PR-commenting job uses write permissions.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/39#pullrequestreview-4276640814) — copilot-pull-request-reviewer (2026-05-12): ## Pull request overview Copilot reviewed 4 out of 4 changed files in this pull request and generated 4 comments.
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/39#issuecomment-4439141256) — github-actions[bot] (2026-05-13): ### Sorry Delta No baseline available for comparison. Current sorry-tainted declarations: 165
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/39#discussion_r3232869954) — Copilot (2026-05-13; scripts/sorry-diff.py:111): The GitHub REST endpoint used to update an existing PR comment is incorrect. \`PATCH /repos/{owner}/{repo}/issues/{issue\_number}/comments/{comment\_id}\` is not a valid update route, so this will likely fail and fall back to creating a new comment each run (duplicates). Use \`PATCH /repos/{owner}/{repo}/issues/comments/{comment\_id}\` (no PR number in the path), or use \`gh api repos/{repo}/issues/comments/{id} -X PATCH …
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/39#discussion_r3232870005) — Copilot (2026-05-13; scripts/SorryLister.lean:11): The header comment says this script “discovers all modules whose name starts with \`Spqr\`”, but the implementation only inspects \`env.header.moduleNames\` after \`import Spqr\`, which includes only modules currently imported into the environment. If new \`Spqr.\*\` modules are added but not imported by \`Spqr.lean\`, they won’t be scanned. Either update the documentation to match the reachable-module behavior, or extend the …
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/39#discussion_r3232870038) — Copilot (2026-05-13; scripts/PrintAxioms.lean:9): The header comment claims to “discover all modules whose name starts with \`Spqr\`”, but the code is limited to the modules already imported into the environment by \`import Spqr\` (via \`env.header.moduleNames\`). This can miss \`Spqr.\*\` modules that exist in the repo but aren’t imported by \`Spqr.lean\`. Consider either updating the comment to clarify scope, or importing all \`Spqr\` modules programmatically before building …
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/39#pullrequestreview-4280011050) — copilot-pull-request-reviewer (2026-05-13): ## Pull request overview Copilot reviewed 4 out of 4 changed files in this pull request and generated 3 comments.
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/39#discussion_r3233075458) — Copilot (2026-05-13; scripts/sorry-diff.py:103): \`gh api --paginate\` can emit multiple JSON documents (one per page) when there are many PR comments, which makes \`json.loads(result.stdout)\` fail and causes the upsert logic to miss the existing marker comment (leading to duplicate comments). Consider either removing pagination (request a higher \`per\_page\`), or using \`--paginate --slurp\` / \`--jq\` so the output is always valid JSON before parsing.
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/39#discussion_r3233075524) — Copilot (2026-05-13; scripts/sorry-diff.py:97): \`upsert\_pr\_comment\` returns early when \`PR\_NUMBER\` is missing, but still calls the API even if \`GITHUB\_REPOSITORY\` is empty. Adding a guard for \`repo\` (and emitting a clear warning when required env vars are missing) would make local/CI failures easier to diagnose.
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/39#discussion_r3233075564) — Copilot (2026-05-13; .github/workflows/lean.yml:62): The PR description says the sorry manifest is generated and cached on \*every push\*, but this workflow only saves the manifest when pushing to \`main\`. If PRs can target other base branches, they will consistently have no baseline to diff against. Either update the description to match the current behavior (baseline only for \`main\`) or broaden the save condition to cover the intended branches.
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/39#discussion_r3233075603) — Copilot (2026-05-13; .github/workflows/lean.yml:10): The push \`paths:\` filter includes \`lakefile.toml\` but not \`lake-manifest.json\`. If dependencies are updated via \`lake update\` (changing only \`lake-manifest.json\`), the workflow won’t run on \`main\`, so the cached \`sorry-manifest.txt\` baseline can become stale relative to the base branch. Consider adding \`lake-manifest.json\` to the push paths so the baseline stays aligned with dependency changes.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/39#pullrequestreview-4280261185) — copilot-pull-request-reviewer (2026-05-13): ## Pull request overview Copilot reviewed 4 out of 4 changed files in this pull request and generated 4 comments.
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/39#discussion_r3233227930) — Copilot (2026-05-13; .github/workflows/lean.yml:27): The workflow sets \`permissions: contents: read\` for the build job, which removes all other token scopes. \`actions/cache\` (including \`actions/cache/restore\` + \`actions/cache/save\`) requires the \`actions\` permission (read for restore, write for save). As written, the cache steps may fail or become no-ops, defeating both the Lean build cache and the sorry-manifest caching. Add the appropriate \`actions: read\`/\`actions: …
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/39#discussion_r3233227991) — Copilot (2026-05-13; scripts/sorry-diff.py:103): \`gh api --paginate\` can emit multiple JSON documents (one per page) rather than a single valid JSON array. If a PR has enough comments to paginate, \`json.loads(result.stdout)\` will fail and the script will fall back to creating a new comment, causing duplicates. Use \`gh api --paginate --slurp ...\` (or handle paging differently) so the output is always valid JSON.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/39#pullrequestreview-4280435733) — copilot-pull-request-reviewer (2026-05-13): ## Pull request overview Copilot reviewed 4 out of 4 changed files in this pull request and generated 2 comments.
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/39#discussion_r3233630068) — Copilot (2026-05-13; .github/workflows/lean.yml:135): \`actions/download-artifact@v4\` typically extracts files into a subdirectory named after the artifact (e.g. \`./sorry-manifests/\`). With the current step, \`sorry-manifest.txt\` / \`sorry-manifest-base.txt\` may not be in the workspace root, causing the subsequent \`sorry-diff.py\` invocation to fail to find the manifests. Consider either setting an explicit download \`path\` (and/or disabling the extra directory) or updating …
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/39#discussion_r3233630131) — Copilot (2026-05-13; .github/workflows/lean.yml:75): The cache restore uses a broad \`restore-keys\` fallback. If the exact \`${base.sha}\` entry is missing/evicted, a different commit’s manifest may be restored, which can make the “new sorries” delta inaccurate (false positives/negatives). If accuracy is important, consider removing the fallback or at least surfacing in the report when the baseline came from a non-exact cache hit.
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/39#discussion_r3233630152) — Copilot (2026-05-13; .github/workflows/lean.yml:28): The build job grants \`actions: write\` for all events, including pull\_request. Since cache writes only happen on \`push\` to \`main\`, consider reducing permissions (e.g. split the cache-save into a separate job limited to main pushes) so PR runs operate with the least privileges necessary.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/39#pullrequestreview-4280883706) — copilot-pull-request-reviewer (2026-05-13): ## Pull request overview Copilot reviewed 4 out of 4 changed files in this pull request and generated 3 comments.
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/39#discussion_r3233671589) — astefano (2026-05-13; .github/workflows/lean.yml:28): @copilot apply changes based on this feedback
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/39#pullrequestreview-4280931150) — astefano (2026-05-13): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/39#discussion_r3233784609) — Copilot (2026-05-13; .github/workflows/lean.yml:28): Implemented in 8f25296. The build job now scopes \`actions\` permission by event/ref so PR runs use \`actions: read\`, while \`actions: write\` is only granted for pushes to \`main\` where cache-save runs.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/39#pullrequestreview-4281062429) — copilot-swe-agent (2026-05-13): (No text.)
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/39#issuecomment-4444485765) — github-actions[bot] (2026-05-13): ### Sorry Delta No baseline available for comparison. Current sorry-tainted declarations: 161
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/39#discussion_r3258933381) — Kukovec (2026-05-18; .github/workflows/lean.yml:10): I'm not 100% sure we want Lean checking to rerun whenever a file in scripts change
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/39#discussion_r3258951088) — Kukovec (2026-05-18; .github/workflows/lean.yml:49): Oh yeah, nice catch.
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/39#discussion_r3259002687) — Kukovec (2026-05-18; scripts/PrintAxioms.lean:115): IIUC, \`sorryAx\` is an internal solver technicality, in a person-facing log, I wonder if just \`sorry\` wouldn't be more readable.
- [review DISMISSED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/39#pullrequestreview-4310187114) — Kukovec (2026-05-18): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/39#discussion_r3265114156) — astefano (2026-05-19; .github/workflows/lean.yml:10): right, thanks
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/39#pullrequestreview-4317543574) — astefano (2026-05-19): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/39#discussion_r3265305667) — astefano (2026-05-19; scripts/PrintAxioms.lean:115): Hm, i thought \`collectAxioms\` with sorryAx gives "better" insights than just accounting for lean \`sorry\` like we do with \`probe-lean\`; but this is no longer clear to me, in which case, the approach we take in \`probe-lean\` is more efficient. I've created an issue to try to clarify this later on, in the meantime, we can experiment if the current audit is too verbose/slow.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/39#pullrequestreview-4317776178) — astefano (2026-05-19): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/39#discussion_r3265379374) — astefano (2026-05-19; scripts/PrintAxioms.lean:115): so we now have https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/48 for reference
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/39#pullrequestreview-4317865699) — astefano (2026-05-19): (No text.)
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/39#issuecomment-4487540084) — astefano (2026-05-19): @Kukovec commit 324ad3d89112f285c1ccf70a6bf06da5129384f1 simplifies so that we only need one lean script.
- [review DISMISSED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/39#pullrequestreview-4318853947) — Kukovec (2026-05-19): (No text.)
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/39#issuecomment-4488194880) — astefano (2026-05-19): @Kukovec i also noticed there's github.com/leanprover/lean-action so c4bd0d632150b33dae51b892f1d2747d094ba3e0 simplifies lean.yml to use the action.
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/39#pullrequestreview-4320405047) — Kukovec (2026-05-19): (No text.)
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/39#issuecomment-4492378017) — oliver-butterley (2026-05-19): I see in this PR the sorry reporting becomes part of the the lean build workflow. Is this desired? The lean build workflow checks the project builds correctly and is a check before a PR can be merged. The sorry audit is informative rather than a requirement, perhaps it makes sense to separate the required from the informative?
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/39#issuecomment-4494547489) — astefano (2026-05-20): &gt; I see in this PR the sorry reporting becomes part of the the lean build workflow. Is this desired? The lean build workflow checks the project builds correctly and is a check before a PR can be merged. The sorry audit is informative rather than a requirement, perhaps it makes sense to separate the required from the informative? I see your point. For the sorry audit, we run \`lake env lean scripts/Audit.lean\` which …

### Item 40

**[PR #40](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/40) — Hotfix aeneas.yml**

Status: merged. Opened: 2026-05-13. Author: Kukovec.

Body excerpt: No associated issue, hotfix to unblock #31

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/40#pullrequestreview-4283136300) — oliver-butterley (2026-05-13): (No text.)

### Item 41

**[PR #41](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/41) — Specify and verify: \`spqr::encoding::gf::reduce::reduce\_bytes\` in \`gf.rs\`**

Status: merged. Opened: 2026-05-13. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::encoding::gf::reduce::reduce\_bytes\` in \`gf.rs\`. Closed #20

Discussion and review record:

- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/41#discussion_r3252497230) — oliver-butterley (2026-05-16; Spqr/Specs/Encoding/Gf/Reduce/ReduceBytes.lean:220): In this PR there are several spec theorems for \`reduce\_bytes\`. What was our plan for the naming of such? I though at the very minimum the spec theorem should be the name of the theorem with some suffix but \`reduce\_byte\_poly\_spec\` doesn't satisfy this property.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/41#pullrequestreview-4303363154) — oliver-butterley (2026-05-16): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/41#discussion_r3252498432) — oliver-butterley (2026-05-16; Spqr/Specs/Encoding/Gf/Reduce/ReduceBytes.lean:16): Isn't this or something very similar already available in Aeneas? Same for the next lemma.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/41#pullrequestreview-4303364351) — oliver-butterley (2026-05-16): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/41#discussion_r3252524240) — truonghoangle (2026-05-16; Spqr/Specs/Encoding/Gf/Reduce/ReduceBytes.lean:220): This serves as an excellent example of the issue we have been discussing. We have a single function, yet we can write its specification in two distinct ways, reflecting two different approaches- in this case, one based on \`Nat\` and the other on \`polynomial\`. I am unsure which naming convention is preferable; for instance, while the function is currently coupled with the Nat-based specification, the polynomial-based …
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/41#pullrequestreview-4303389003) — truonghoangle (2026-05-16): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/41#discussion_r3252533060) — truonghoangle (2026-05-16; Spqr/Specs/Encoding/Gf/Reduce/ReduceBytes.lean:16): Yes, I have written it in a more useful format that doesn't require going through the specs.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/41#pullrequestreview-4303396542) — truonghoangle (2026-05-16): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/41#discussion_r3252533737) — oliver-butterley (2026-05-16; Spqr/Specs/Encoding/Gf/Reduce/ReduceBytes.lean:220): Yes, I see, this is a great example of the issue! My personal preference for names: \_spec Here the optional 2nd suffix can be used to distinguish between multiple spec theorems for the same function. This has the advantage that all spec theorem names for a given function start with \_spec and can be found easily by text search when required.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/41#pullrequestreview-4303397114) — oliver-butterley (2026-05-16): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/41#discussion_r3252536823) — oliver-butterley (2026-05-16; Spqr/Specs/Encoding/Gf/Reduce/ReduceBytes.lean:16): Does it belong centrally in this repo, not just in the file for this spec theorem?
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/41#pullrequestreview-4303399691) — oliver-butterley (2026-05-16): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/41#discussion_r3252537187) — truonghoangle (2026-05-16; Spqr/Specs/Encoding/Gf/Reduce/ReduceBytes.lean:220): As in this case \`reduce\_byte\_spec\_poly\` or \`reduce\_byte\_poly\_spec.poly\` which one would you choose?
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/41#pullrequestreview-4303400154) — truonghoangle (2026-05-16): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/41#discussion_r3252539366) — oliver-butterley (2026-05-16; Spqr/Specs/Encoding/Gf/Reduce/ReduceBytes.lean:220): I prefer with \_ not . because otherwise it does strange things with the namespacing.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/41#pullrequestreview-4303402485) — oliver-butterley (2026-05-16): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/41#discussion_r3252542296) — truonghoangle (2026-05-16; Spqr/Specs/Encoding/Gf/Reduce/ReduceBytes.lean:16): This is also a point I wanted to discuss. Regarding the many theorems that are either not yet included in Aeneas-or that possess significant practical applications and have had their utility verified-should we place them in a separate folder right from the start, as @a-dangelo suggested \`toAeneas\`, or should we consolidate them later on?
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/41#pullrequestreview-4303405821) — truonghoangle (2026-05-16): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/41#discussion_r3252543638) — truonghoangle (2026-05-16; Spqr/Specs/Encoding/Gf/Reduce/ReduceBytes.lean:220): Ok, I'll fix it, and we should make it a standard rule in our documentation.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/41#pullrequestreview-4303406959) — truonghoangle (2026-05-16): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/41#discussion_r3252551987) — oliver-butterley (2026-05-16; Spqr/Specs/Encoding/Gf/Reduce/ReduceBytes.lean:16): Yes, choose some folder which serves this purpose. I believe most of the stuff fits into the categories: - Seems like it belongs in Aeneas - Seems like it belongs in Mathlib - Specific to this particular verification project but shared by many files - A well-defined abstraction of something (like GF216 in this case) which can be isolated and shared with other projects but doesn't belong in Mathlib I don't have a …
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/41#pullrequestreview-4303414496) — oliver-butterley (2026-05-16): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/41#discussion_r3252631395) — truonghoangle (2026-05-16; Spqr/Specs/Encoding/Gf/Reduce/ReduceBytes.lean:16): I will refactor once there is enough such lemmas.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/41#pullrequestreview-4303501047) — truonghoangle (2026-05-16): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/41#discussion_r3261592319) — oliver-butterley (2026-05-18; Spqr/Specs/Encoding/Gf/Reduce/ReduceBytes.lean:90): \`\`\`suggestion reduce\_bytes ⦃ (result : Array U16 256#usize) =&gt; ∀ (j : Usize) (\_ : j.val &lt; 256), result\[j\]! = reduceByteTable j ⦄ := by \`\`\` In this theorem and several others, the statement contains ∃ and this is likely to cause problems later and there is no need for this. For instance my suggestion is another option.
- [review CHANGES_REQUESTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/41#pullrequestreview-4313242870) — oliver-butterley (2026-05-18): Many of the spec statements looked strange so it took me a while to understand why they were as stated. As far as I can see there isn't a reason. Am I missing something? I made a suggestion for one in particular and several others are just the same pattern. Having \`∃ v : U16\` is likely to make life harder down the road. I see also that \`reduceByteTable\` is used as a key definition in many of the spec theorem …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/41#issuecomment-4481629177) — oliver-butterley (2026-05-18): &gt; I see also that \`reduceByteTable\` is used as a key definition in many of the spec theorem statements and so deserves to be in a central place rather than in a file designed for a single spec theorem. Also, can \`reduceByteTable\` be defined more directly since it is used as part of spec theorems? At the moment the definition isn't very direct.
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/41#issuecomment-4481641280) — truonghoangle (2026-05-18): In practice, \`reduceByteTable\` is indeed necessary and is used to accelerate computation. However, for specification theorems, it is less essential. In general, it is similar to a logarithm table: computationally important, but not theoretically fundamental. Therefore, we just need to keep it locally. Ultimately, the entire \`Reduce\` folder is only geared towards proving the theorem. \`\`\` @\[step\] theorem …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/41#issuecomment-4481983221) — truonghoangle (2026-05-18): What do you think if the center of the spec theorem in file is in polynomial form instead of Nat form? \`\`\` @\[step\] theorem reduce\_byte\_spec : reduce\_bytes ⦃ (result : Std.Array U16 256#usize) =&gt; ∀ (j : Usize) (\_: j.val &lt; 256), natToBinaryPoly (result\[j\]!).val = (natToBinaryPoly j.val \* X ^ 16) %ₘ polyGF2 ⦄ := by \`\`\`
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/41#discussion_r3262493623) — truonghoangle (2026-05-18; Spqr/Specs/Encoding/Gf/Reduce/ReduceBytes.lean:90): I have rewritten the spec in the format you suggested.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/41#pullrequestreview-4314334717) — truonghoangle (2026-05-18): (No text.)
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/41#issuecomment-4485560575) — oliver-butterley (2026-05-19): &gt; In practice, \`reduceByteTable\` is indeed necessary and is used to accelerate computation. However, for specification theorems, it is less essential. In general, it is similar to a logarithm table: computationally important, but not theoretically fundamental. Therefore, we just need to keep it locally. Ultimately, the entire \`Reduce\` folder is only geared towards proving the theorem. &gt; &gt; \`\`\` &gt; @\[step\] &gt; theorem …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/41#issuecomment-4485572884) — oliver-butterley (2026-05-19): &gt; What do you think if the center of the spec theorem in file is in polynomial form instead of Nat form? &gt; &gt; \`\`\` &gt; @\[step\] &gt; theorem reduce\_byte\_spec : &gt; reduce\_bytes ⦃ (result : Std.Array U16 256#usize) =&gt; &gt; ∀ (j : Usize) (\_: j.val natToBinaryPoly (result\[j\]!).val = (natToBinaryPoly j.val \* X ^ 16) %ₘ polyGF2 ⦄ := by &gt; \`\`\` That looks better to my eyes. Although you surely know more the details now and can judge …
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/41#pullrequestreview-4316882469) — oliver-butterley (2026-05-19): That's great! Thanks for the updates

### Item 42

**[Issue #42](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/42) — extract lib.rs**

Status: closed. Opened: 2026-05-15. Author: astefano.

Body excerpt: initial\_state, send, recv from lib.rs do not seem to be aeneas extracted.

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/42#issuecomment-4502757625) — oliver-butterley (2026-05-20): Will modify the extraction to start from all public functions, previously lib.rs was missed by mistake.

### Item 43

**[Issue #43](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/43) — Add property catalog and spec coverage analysis**

Status: open. Opened: 2026-05-15. Author: astefano.

Body excerpt: Organize the correctness obligations from the mlkembraid spec into a structured property catalog, covering the three architectural layers (SCKA interface, incremental KEM, protocol state machine). Include a spec coverage analysis quantifying what percentage of the spec is addressed and what gaps remain. Deliverables: - \`docs/mlkembraid\_spec/\` — property catalog organized by spec layer - \`docs/SPQR\_SPEC\_COVERAGE.md\` …

No recorded comments or reviews.

### Item 44

**[Issue #44](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/44) — Prove chain guards and state-machine epoch dispatch (PROP-9, PROP-14, PROP-17, PROP-21, PROP-30, D3)**

Status: open. Opened: 2026-05-15. Author: astefano.

Body excerpt: Lean proofs for protocol-level properties of \`chain.rs\` and the v1 chunked state machine (\`src/v1/chunked/states.rs\`, the eleven-variant \`States\` enum). The IDs refer to the property catalog on \`la/spec-catalog\`, which is not on \`main\`. \*\*Chain layer\*\* (catalog §10). All three are proved on \`main\`. - PROP-9 (\`src/chain.rs:350-368\`): \`add\_epoch(es)\` with \`es.epoch = current\_epoch + 1\` sets \`current\_epoch = es.epoch\`, …

No recorded comments or reviews.

### Item 45

**[PR #45](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/45) — Revert Rust setup workaround in Aeneas workflow**

Status: closed unmerged. Opened: 2026-05-15. Author: astefano.

Body excerpt: This PR reverts the prior workaround for the failing \*\*Check Aeneas Extraction\*\* job and restores the original Rust setup action. We are keeping the workflow configuration unchanged while waiting on the suspected upstream GitHub Actions issue. - \*\*Description\*\* - Reverted the commit that replaced \`dtolnay/rust-toolchain@stable\` with a manual \`rustup\` install. - Restored the original action-based Rust setup in …

No recorded comments or reviews.

### Item 46

**[PR #46](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/46) — Prove chain and state machine invariants (PROP-9,14,17,21,26,30,33,39)**

Status: closed unmerged. Opened: 2026-05-15. Author: astefano.

Body excerpt: This PR adds Lean proofs for 9 protocol-level properties over the chain module and the v1 chunked state machine. Property IDs refer to the catalog in \`docs/mlkembraid\_spec/\`. Chain proofs (\`Spqr/Specs/Chain/\`): - PROP-9: epoch monotonicity — add\_epoch increments current\_epoch - PROP-14: send key guard — send\_key rejects epoch &lt; current\_epoch - PROP-17/17b: key jump guard — key rejects out-of-range epochs State …

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/46#issuecomment-5908752479) — astefano (2026-09-30): Closing: this branch predates the current layout and most of it is now covered on main by stronger per-function specs. - PROP-9 (\`add\_epoch\`): \`add\_epoch\_spec\` in #541 - PROP-14 (\`send\_key\` epoch guard): first case of \`send\_key\_spec\` in #546 - PROP-17/17b (\`key\` jump and already-requested guards): \`key\_spec\_greater\` and \`key\_spec\_equal\` in #508 - PROP-21 (only \`HeaderReceived.send\` emits a key): \`send\_key\_epoch\` and …

### Item 47

**[Issue #47](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/47) — Specify and verify: \`spqr::encoding::gf::reduce::REDUCE\_BYTES\` in \`gf.rs\`**

Status: closed. Opened: 2026-05-19. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 48

**[Issue #48](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/48) — Evaluate collectAxioms audit vs probe-lean sorry detection**

Status: open. Opened: 2026-05-19. Author: astefano.

Body excerpt: ## Context The CI pipeline uses \`scripts/Audit.lean\` for axiom auditing and sorry-manifest generation. Separately, \`probe-lean\` exists as a tool that can detect sorry usage by parsing build warnings. These are two independent approaches to sorry detection; only the first is currently in CI. 1. \*\*\`scripts/Audit.lean\` (collectAxioms, in CI)\*\* — Loads the full Lean environment after build, calls \`Lean.collectAxioms\` on …

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/48#issuecomment-4514945148) — astefano (2026-05-22): ## Time complexity analysis: \`collectAxioms\` vs reverse-BFS contamination Following up on the comparison in this issue, here's a time-complexity analysis of the two transitive-sorry-detection approaches. This is relevant for deciding whether to extend probe-lean with transitive verification status (Option A below) or reuse \`collectAxioms\` (Option B). ### Variables - \*\*N\*\* = number of project atoms (declarations) - …

### Item 49

**[PR #49](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/49) — Verify : \`spqr::encoding::gf::reduce::poly\_reduce\` and \`spqr::encoding::gf::reduce::REDUCE\_BYTES\`**

Status: merged. Opened: 2026-05-19. Author: truonghoangle.

Body excerpt: This PR verifies \`spqr::encoding::gf::reduce::poly\_reduce\` and \`spqr::encoding::gf::reduce::REDUCE\_BYTES\`. Note that REDUCE\_BYTES is a consequence of the spec theorem of the function \`spqr::encoding::gf::reduce::reduce\_bytes\`, so it should be included in this PR. closes #19 closes #47

Discussion and review record:

- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/49#discussion_r3265703098) — oliver-butterley (2026-05-19; Spqr/Specs/Encoding/Gf/Reduce/REDUCE_BYTES.lean:38): \`\`\`suggestion REDUCE\_BYTES ⦃ (result : Std.Array U16 256#usize) =&gt; \`\`\`
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/49#discussion_r3265716818) — oliver-butterley (2026-05-19; Spqr/Specs/Encoding/Gf/Reduce/REDUCE_BYTES.lean:43): Did we decide a policy on adding docstrings to spec theorems? I think at some point in time we decided that we always would add a concise one because this was the convenient place to record and easily access the natural language spec. @Kukovec?
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/49#discussion_r3265740307) — oliver-butterley (2026-05-19; Spqr/Specs/Encoding/Gf/Reduce/PolyReduce.lean:188): Is it possible for this docstring to be more concise whilst still communicating the essentials of the natural language spec? Also I would prefer that the source link and natural general discussion was in the module docstring (/-!) rather than the theorem docstring. Did we specify our convention for this in the style guide?
- [review DISMISSED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/49#pullrequestreview-4318242038) — oliver-butterley (2026-05-19): Great!
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/49#discussion_r3266068335) — Kukovec (2026-05-19; Spqr/Specs/Encoding/Gf/Reduce/REDUCE_BYTES.lean:43): I recall the conversation, and I remember us agreeing on these docs being helpful, though I can't say whether we made a hard rule of it. Regardless, I'd definitely support adding them here.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/49#pullrequestreview-4318651023) — Kukovec (2026-05-19): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/49#discussion_r3266192287) — truonghoangle (2026-05-19; Spqr/Specs/Encoding/Gf/Reduce/REDUCE_BYTES.lean:38): done
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/49#pullrequestreview-4318792402) — truonghoangle (2026-05-19): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/49#discussion_r3266283255) — truonghoangle (2026-05-19; Spqr/Specs/Encoding/Gf/Reduce/PolyReduce.lean:188): After \`import\`, the docstrings starts with /-! but before the theorem /--. I have updated the content of docstrings
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/49#pullrequestreview-4318909743) — truonghoangle (2026-05-19): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/49#discussion_r3266305859) — truonghoangle (2026-05-19; Spqr/Specs/Encoding/Gf/Reduce/REDUCE_BYTES.lean:43): With theorems that are consequences of the spec theorem, I think we don't need to describe the theorem further in natural language because its content has essentially already been described in the spec theorem.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/49#pullrequestreview-4318937147) — truonghoangle (2026-05-19): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/49#pullrequestreview-4319123123) — oliver-butterley (2026-05-19): (No text.)

### Item 50

**[PR #50](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/50) — Verify: \`spqr::encoding::gf::unaccelerated::mul\` in \`gf.rs\`**

Status: merged. Opened: 2026-05-19. Author: truonghoangle.

Body excerpt: This PR verified \`spqr::encoding::gf::unaccelerated::mul\` in \`gf.rs\` closes #18

Discussion and review record:

- [review DISMISSED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/50#pullrequestreview-4319452379) — oliver-butterley (2026-05-19): lgtm
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/50#pullrequestreview-4319894392) — oliver-butterley (2026-05-19): (No text.)

### Item 51

**[Issue #51](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/51) — Chore: update Aeneas to 3fb1cd4b**

Status: closed. Opened: 2026-05-19. Author: oliver-butterley.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 52

**[PR #52](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/52) — Update Aeneas to version 3fb1cd4b**

Status: merged. Opened: 2026-05-19. Author: oliver-butterley.

Body excerpt: Update the Aeneas pins, re-extract the crate, mend the errors due to the update. One extraction tweak could be removed but another had to be added because of a regression in Aeneas A few modifications to the proofs required. closes #51

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/52#issuecomment-4492371152) — github-actions[bot] (2026-05-19): ### Sorry Delta No baseline available for comparison. Current sorry-tainted declarations: 155
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/52#pullrequestreview-4325484856) — truonghoangle (2026-05-20): (No text.)

### Item 53

**[PR #53](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/53) — Specify and verify: \`spqr::encoding::gf::unaccelerated::mul2\` in \`gf.rs\`**

Status: merged. Opened: 2026-05-19. Author: truonghoangle.

Body excerpt: This PR specified and verified \`spqr::encoding::gf::unaccelerated::mul2\` in \`gf.rs\` closes #22

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/53#issuecomment-4491004038) — semaraugusto (2026-05-19): !bench
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/53#issuecomment-4491135700) — truonghoangle (2026-05-19): @astefano I don't understand why \`Report Sorry Delta\` didn't pass.
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/53#issuecomment-4491567932) — astefano (2026-05-19): &gt; @astefano I don't understand why \`Report Sorry Delta\` didn't pass. Oh, i borrowed the sticky-pull-request-comment@v2 from the warning-diff workflow from dalek-lean and apparently, there's a permission issue with fork PRs... i've proposed a fix in commit ebae2f9f854c94de2d2205cab425baa626d2fb66 i've tested with a fork PR using the test repo https://github.com/Beneficial-AI-Foundation/test\_sorry\_detection/pull/6. …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/53#issuecomment-4494834647) — truonghoangle (2026-05-20): @astefano Mostly habit, to be honest. I tend to use fork PRs everywhere for isolation/consistency. Usually, when I start a project, everything is very chaotic and disorganized. But I still want to document that chaos because I might need it later. I usually try to solve it myself before discussing it, or when creating a PR, it's rarely in draft form. I usually treat the PR process like submitting \`a paper for open …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/53#issuecomment-4495671098) — oliver-butterley (2026-05-20): !bench
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/53#issuecomment-4495673492) — oliver-butterley (2026-05-20): &gt; !bench Just testing the new feature
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/53#issuecomment-4495690108) — oliver-butterley (2026-05-20): &gt; @truonghoangle : just curious, what is the reason for you to use fork PRs instead of branch PRs? I mean, being a collaborator on this repo, wouldn't it be easier to just create a branch PR instead? We should definitely permit people working in forks with all our workflows, it's very common practice and will be essential if we have any external contributors.
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/53#issuecomment-4495759939) — oliver-butterley (2026-05-20): &gt; @Beneficial-AI-Foundation/fc-team please see i introduced some workflow changes in commit ebae2f9 to see if the proposed solution fixes the issue. I can move it in a separate PR if it's preferred. @astefano Yes, please make this a separate PR otherwise we have chaos with all the different things happening all together. Would it be possible to revert the basic lean build PR to its original form and keep the sorry …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/53#issuecomment-4495881068) — astefano (2026-05-20): &gt; &gt; @Beneficial-AI-Foundation/fc-team please see i introduced some workflow changes in commit ebae2f9 to see if the proposed solution fixes the issue. I can move it in a separate PR if it's preferred. &gt; &gt; @astefano Yes, please make this a separate PR otherwise we have chaos with all the different things happening all together. Would it be possible to revert the basic lean build PR to its original form and keep the …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/53#issuecomment-4495888822) — astefano (2026-05-20): &gt; &gt; @truonghoangle : just curious, what is the reason for you to use fork PRs instead of branch PRs? I mean, being a collaborator on this repo, wouldn't it be easier to just create a branch PR instead? &gt; &gt; We should definitely permit people working in forks with all our workflows, it's very common practice and will be essential if we have any external contributors. sure, as i said, i was just curious (in that, to …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/53#issuecomment-4495915973) — oliver-butterley (2026-05-20): &gt; @oliver-butterley are you fine with this PR waiting for a separate PR containing only commit ebae2f9 and then have this PR rebase on main once that PR is merged? That would be very convenient! Thank you!
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/53#issuecomment-4496418073) — astefano (2026-05-20): &gt; &gt; @oliver-butterley are you fine with this PR waiting for a separate PR containing only commit ebae2f9 and then have this PR rebase on main once that PR is merged? &gt; &gt; That would be very convenient! Thank you! Sure. The commit with the workflow fix has been dropped from this PR and moved to PR #55 which makes it possible to have sorry deltas comments on fork PRs.
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/53#issuecomment-4496533710) — github-actions[bot] (2026-05-20): ### Sorry Delta No baseline available for comparison. Current sorry-tainted declarations: 155
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/53#pullrequestreview-4326891416) — oliver-butterley (2026-05-20): lgtm

### Item 54

**[Issue #54](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/54) — Open issues with MWEs for the Aeneas extract problems**

Status: closed. Opened: 2026-05-19. Author: oliver-butterley.

Body excerpt: - For each of the 4 problems we still have with extraction of this repo, open an issue in the Aeneas repo together with a MWE to reproduce the problem. - Add links within aeneas-config.yml at each tweak to the corresponding issue.

No recorded comments or reviews.

### Item 55

**[PR #55](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/55) — ci: move sorry-delta comment to workflow\_run for fork PR support**

Status: merged. Opened: 2026-05-20. Author: astefano.

Body excerpt: This PR moves the sorry-delta PR comment posting from an inline job in \`lean.yml\` to a separate \`sorry-delta-comment.yml\` workflow triggered by \`workflow\_run\`. Because \`workflow\_run\` executes in the base repo context, the \`GITHUB\_TOKEN\` has write access even for fork PRs. The PR number is passed via artifact so the comment targets the correct PR. Closes #56

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/55#pullrequestreview-4326841765) — truonghoangle (2026-05-20): (No text.)

### Item 56

**[Issue #56](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/56) — CI: sorry-delta comment fails on fork PRs**

Status: closed. Opened: 2026-05-20. Author: astefano.

Body excerpt: ## Problem The \`Report Sorry Delta\` job in \`lean.yml\` fails on fork PRs with: &gt; Resource not accessible by integration This happens because GitHub gives fork PR workflows a \*\*read-only \`GITHUB\_TOKEN\`\*\*, so the \`marocchino/sticky-pull-request-comment\` action cannot post comments to the upstream PR. First observed on PR #53 (from \`truonghoangle/SparsePostQuantumRatchet\`): …

No recorded comments or reviews.

### Item 57

**[Issue #57](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/57) — Specify and verify : \`spqr::encoding::gf::sub\_assign\` in \`gf.rs\`**

Status: closed. Opened: 2026-05-20. Author: truonghoangle.

Body excerpt: Notice that we have two function - spqr::encoding::gf::{impl ops::SubAssign for GF16}::sub\_assign - spqr::encoding::gf::{impl ops::SubAssign for GF16}::sub\_assign

No recorded comments or reviews.

### Item 58

**[PR #58](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/58) — Specify and verify : \`spqr::encoding::gf::sub\_assign\` in \`gf.rs\`**

Status: merged. Opened: 2026-05-20. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::encoding::gf::sub\_assign\` in \`gf.rs\` Notice we have two functions - spqr::encoding::gf::{impl ops::SubAssign for GF16}::sub\_assign - spqr::encoding::gf::{impl ops::SubAssign for GF16}::sub\_assign and spqr::encoding::gf::{impl ops::Sub for GF16}::sub Closes #57

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/58#issuecomment-4497021076) — github-actions[bot] (2026-05-20): ### Sorry Delta No new sorry-tainted declarations introduced. (155 total)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/58#pullrequestreview-4327609023) — oliver-butterley (2026-05-20): lgtm

### Item 59

**[PR #59](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/59) — Specify and verify \`spqr::encoding::gf::GF16::const\_sub\` in \`gf.rs\`**

Status: merged. Opened: 2026-05-20. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::encoding::gf::GF16::const\_sub\` in \`gf.rs\` closes #27

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/59#issuecomment-4497662622) — github-actions[bot] (2026-05-20): ### Sorry Delta No new sorry-tainted declarations introduced. (155 total)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/59#pullrequestreview-4327800541) — oliver-butterley (2026-05-20): lgtm

### Item 60

**[PR #60](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/60) — Specify and verify: \`spqr::encoding::gf::GF16::ZERO\` in \`gf.rs\`**

Status: merged. Opened: 2026-05-20. Author: truonghoangle.

Body excerpt: This PR specifies and verifies: \`spqr::encoding::gf::GF16::ZERO\` in \`gf.rs\` closes #23

Discussion and review record:

- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/60#pullrequestreview-4329205634) — oliver-butterley (2026-05-20): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/60#discussion_r3274554435) — oliver-butterley (2026-05-20; Spqr/Specs/Encoding/Gf/GF16/ZERO.lean:49): I think you intended to attach this docstring to \`ZERO\_spec\` rather than to \`ZERO\_value. Move later?
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/60#discussion_r3274577808) — truonghoangle (2026-05-20; Spqr/Specs/Encoding/Gf/GF16/ZERO.lean:49): I want to express all the forms of ZERO in this docstrings so that they can be used later in \`simp\`, rather than just ZERO\_spec. I will remove \`\*\*The underlying \`u16\` of \`ZERO\` is \`0\_u16\`\*\*.\`
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/60#pullrequestreview-4329232096) — truonghoangle (2026-05-20): (No text.)
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/60#issuecomment-4499227703) — github-actions[bot] (2026-05-20): ### Sorry Delta No new sorry-tainted declarations introduced. (155 total)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/60#discussion_r3274642060) — oliver-butterley (2026-05-20; Spqr/Specs/Encoding/Gf/GF16/ZERO.lean:49): I can understand that it can be useful to have a docstring for each of the theorems. However the \`/-- ... -/\` docstring attaches to the definition following it, it doesn't attach to any of the others. This is useful because this is the text that is shown in vscode when hovering over the identifier, whenever it is used. It's also the convenient way we extract the text of the natural language spec from the lean code …
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/60#pullrequestreview-4329304907) — oliver-butterley (2026-05-20): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/60#discussion_r3274708418) — truonghoangle (2026-05-20; Spqr/Specs/Encoding/Gf/GF16/ZERO.lean:49): I now understand the best way to display information. I fixed it
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/60#pullrequestreview-4329379112) — truonghoangle (2026-05-20): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/60#pullrequestreview-4329401684) — oliver-butterley (2026-05-20): lgtm

### Item 61

**[PR #61](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/61) — Specify and verify: \`spqr::encoding::gf::GF16::ONE\` in \`gf.rs\`**

Status: merged. Opened: 2026-05-20. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::encoding::gf::GF16::ONE\` in \`gf.rs\` closes #24

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/61#issuecomment-4499855344) — github-actions[bot] (2026-05-20): ### Sorry Delta No new sorry-tainted declarations introduced. (155 total)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/61#pullrequestreview-4329953646) — oliver-butterley (2026-05-20): lgtm

### Item 62

**[PR #62](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/62) — Specify and verify: \`spqr::encoding::gf::GF16::new\` in \`gf.rs\`**

Status: merged. Opened: 2026-05-20. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::encoding::gf::GF16::new\` in \`gf.rs\` closes #25

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/62#issuecomment-4500298088) — github-actions[bot] (2026-05-20): ### Sorry Delta No baseline available for comparison. Current sorry-tainted declarations: 155
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/62#discussion_r3277159541) — oliver-butterley (2026-05-20; Spqr/Specs/Encoding/Gf/GF16/New.lean:29): I think this is fine as a simp lemma but keep it in mind if it causes problems elsewhere. could the be a scenario where you would like to keep \`new value\` as it is so that \`step\*\` acts on it rather than do this simp? Anyway, I think it will be fine.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/62#pullrequestreview-4332232819) — oliver-butterley (2026-05-20): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/62#pullrequestreview-4332233886) — oliver-butterley (2026-05-20): lgtm
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/62#discussion_r3277197155) — truonghoangle (2026-05-20; Spqr/Specs/Encoding/Gf/GF16/New.lean:29): I will keep this in mind and check it in the future.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/62#pullrequestreview-4332275273) — truonghoangle (2026-05-20): (No text.)

### Item 63

**[PR #63](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/63) — Add links to the aeneas issues as comments with the tweaks**

Status: merged. Opened: 2026-05-20. Author: oliver-butterley.

Body excerpt: Adds links in the comments in aeneas-config.yml to document the reason for the current tweaks and to clarify how we can unfold the tweaks when the issues are solved upstream. closes #54

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/63#issuecomment-4502486199) — github-actions[bot] (2026-05-20): ### Sorry Delta No new sorry-tainted declarations introduced. (155 total)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/63#pullrequestreview-4332256408) — truonghoangle (2026-05-20): (No text.)

### Item 64

**[PR #64](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/64) — Specify and verify: \`spqr::encoding::gf::GF16::const\_mul\` in \`gf.rs\`**

Status: merged. Opened: 2026-05-21. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::encoding::gf::GF16::const\_mul\` in \`gf.rs\` closes #26

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/64#issuecomment-4505272061) — github-actions[bot] (2026-05-21): ### Sorry Delta No new sorry-tainted declarations introduced. (155 total)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/64#pullrequestreview-4335155815) — Kukovec (2026-05-21): LGTM

### Item 65

**[Issue #65](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/65) — Specify and verify : \`spqr::encoding::gf::mul\_assign\` in \`gf.rs\`**

Status: closed. Opened: 2026-05-21. Author: truonghoangle.

Body excerpt: Specify and verify two function: - spqr::encoding::gf::{impl ops::MulAssign for GF16}::mul\_assign - spqr::encoding::gf::{impl ops::MulAssign for GF16}::mul\_assign

No recorded comments or reviews.

### Item 66

**[Issue #66](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/66) — Specify and verify : \`spqr::encoding::gf::mul\` in \`gf.rs\`**

Status: closed. Opened: 2026-05-21. Author: truonghoangle.

Body excerpt: Specify and verify two functions - spqr::encoding::gf::{impl ops::Mul for GF16}::mul - spqr::encoding::gf::{impl ops::Mul for GF16}::mul

No recorded comments or reviews.

### Item 67

**[Issue #67](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/67) — Specify and verify : \`spqr::encoding::gf::div\_assign\` in \`gf.rs\`**

Status: closed. Opened: 2026-05-21. Author: truonghoangle.

Body excerpt: Specify and verify two functions: - spqr::encoding::gf::{impl ops::DivAssign for GF16}::div\_assign - spqr::encoding::gf::{impl ops::DivAssign for GF16}::div\_assign

No recorded comments or reviews.

### Item 68

**[Issue #68](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/68) — Specify and verify : \`spqr::encoding::gf::div\` in \`gf.rs\`**

Status: closed. Opened: 2026-05-21. Author: truonghoangle.

Body excerpt: Specify and verify two functions - spqr::encoding::gf::{impl ops::Div for GF16}::div - spqr::encoding::gf::{impl ops::Div for GF16}::div

No recorded comments or reviews.

### Item 69

**[Issue #69](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/69) — Specify and verify: \`spqr::encoding::gf::parallel\_mult\` in \`gf.rs\`**

Status: closed. Opened: 2026-05-21. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 70

**[Issue #70](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/70) — Specify and verify : \`spqr::encoding::gf::mul2\_u16\` in \`gf.rs\`**

Status: closed. Opened: 2026-05-21. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 71

**[Issue #71](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/71) — Specify and verify : \`spqr::encoding::gf::GF16::div\_impl\` in \`gf.rs\`**

Status: closed. Opened: 2026-05-21. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 72

**[PR #72](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/72) — Specify and verify: \`spqr::encoding::gf::GF16::const\_div\` in \`gf.rs\`**

Status: merged. Opened: 2026-05-21. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::encoding::gf::GF16::const\_div\` in \`gf.rs\` closes #28

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/72#issuecomment-4506731906) — github-actions[bot] (2026-05-21): ### Sorry Delta No new sorry-tainted declarations introduced. (155 total)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/72#pullrequestreview-4336129530) — oliver-butterley (2026-05-21): lgtm

### Item 73

**[Issue #73](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/73) — Fix \`axiom encoding.gf.GF16.Insts.CoreOpsArithMulAssignShared0GF16.mul\_assign\` in \`gf.rs\`**

Status: closed. Opened: 2026-05-21. Author: truonghoangle.

Body excerpt: The goal is to change the axioms later \`\`\` /-- \[spqr::encoding::gf::{core::ops::arith::MulAssign for spqr::encoding::gf::GF16}::mul\_assign\]: Source: 'src/encoding/gf.rs', lines 127:4-137:5 Visibility: public -/ axiom encoding.gf.GF16.Insts.CoreOpsArithMulAssignShared0GF16.mul\_assign : encoding.gf.GF16 → encoding.gf.GF16 → Result encoding.gf.GF16 \`\`\` into definition. \`\`\` in aeneas-config.yml line 53 opaque: - …

No recorded comments or reviews.

### Item 74

**[PR #74](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/74) — Modify extraction to start\_from\_pub**

Status: merged. Opened: 2026-05-21. Author: oliver-butterley.

Body excerpt: Primary change: switch Aeneas extraction from an explicit \`start\_from\` list to \`start\_from\_pub: true\`, which uses all \`pub\` items as extraction entry points automatically. This is accompanied by a substantial cleanup of \`FunsExternal.lean\` and \`TypesExternal.lean\`, resolution of five distinct Lean compilation blockers, extraction of previously-opaque top-level API functions. ## Functions newly extracted ### …

Discussion and review record:

- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/74#pullrequestreview-4337969371) — oliver-butterley (2026-05-21): I think this makes sense but needs to be checked carefully. If required I can look again very carefully at everything after the weekend.
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/74#issuecomment-4509456400) — Kukovec (2026-05-21): &gt; Additional tweaks to cope with another issue What other issue?
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/74#issuecomment-4509493441) — oliver-butterley (2026-05-21): &gt; &gt; Additional tweaks to cope with another issue &gt; &gt; What other issue? https://github.com/AeneasVerif/aeneas/issues/1051 But I suspect it is far better that I look at this very clearly when I get back to work after the weekend. Particularly the failing CI here.
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/74#issuecomment-4606343163) — oliver-butterley (2026-06-02): In total a large diff for this PR! :scream: However the majority of the changes are in files auto generated by Aeneas: +3,854-4,760 in Funs.lean and +451-246 in Types.lean.
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/74#pullrequestreview-4415426634) — truonghoangle (2026-06-03): (No text.)

### Item 75

**[Issue #75](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/75) — PR sorry-delta comment fires on all declarations, not just hand-written specs**

Status: closed. Opened: 2026-05-21. Author: astefano.

Body excerpt: ## Problem The sorry-delta PR comment (posted by \`scripts/sorry-diff.py\` via the \`report-sorry-delta\` job) currently reports \*\*all\*\* newly introduced sorry-tainted declarations, including those in \`Spqr.Code.\*\` (machine-generated by Aeneas). This is noisy: most new sorry-tainted entries come from Aeneas output, where sorries are expected and not directly actionable. The comment should only fire when there are new …

No recorded comments or reviews.

### Item 76

**[PR #76](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/76) — Scope sorry-delta PR comment to hand-written specs only**

Status: merged. Opened: 2026-05-21. Author: astefano.

Body excerpt: This PR filters the sorry-diff report to only flag new sorry-tainted declarations in \`Spqr.Specs.\*\` modules, ignoring Aeneas-generated \`Spqr.Code.\*\` entries. The PR comment is now posted only when new specs sorries exist and is automatically hidden when they are resolved. closes #75 Made with Cursor

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/76#issuecomment-4509677035) — github-actions[bot] (2026-05-21): ### Sorry Delta No baseline available for comparison. Current sorry-tainted declarations: 155
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/76#discussion_r3282332376) — Kukovec (2026-05-21; .github/workflows/sorry-delta-comment.yml:53): I don't think PR comments should ever be deleted.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/76#pullrequestreview-4338252578) — Kukovec (2026-05-21): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/76#discussion_r3283426970) — astefano (2026-05-21; .github/workflows/sorry-delta-comment.yml:53): right, i changed it to be hidden
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/76#pullrequestreview-4339561123) — astefano (2026-05-21): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/76#pullrequestreview-4363164261) — Kukovec (2026-05-26): (No text.)

### Item 77

**[Issue #77](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/77) — make the CI fail on warnings except sorries**

Status: closed. Opened: 2026-05-22. Author: astefano.

Body excerpt: if PR authors are forced to not introduce linting warnings such as line length then reviewers can focus on things more important than checking warnings.

No recorded comments or reviews.

### Item 78

**[PR #78](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/78) — make CI fail except on sorries**

Status: closed unmerged. Opened: 2026-05-22. Author: astefano.

Body excerpt: This PR adds \`--wfail -- -Dwarn.sorry=false\` to \`lake build\` args in CI so that \`lake build\` fails on warnings except sorries. closes #77

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/78#issuecomment-4516041165) — astefano (2026-05-22): in fact, i don't have a good solution: -Dwarn.sorry=false doesn't seem to play a role in \`lake build\`, might be related to https://github.com/leanprover/lean4/issues/12907

### Item 79

**[PR #79](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/79) — Fix axiom encoding.gf.GF16.Insts.CoreOpsArithMulAssignShared0GF16.mul\_assign in gf.rs**

Status: merged. Opened: 2026-05-22. Author: truonghoangle.

Body excerpt: This PR is to replace the \`mul\_assign\` axiom with a definition. This is currently blocked because it depends on \`unaccelerated::mul\`, which is generated after related functions due to function ordering. Reordering the Rust functions should resolve the issue. closes #73

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/79#issuecomment-4516549688) — github-actions[bot] (2026-05-22): ### Sorry Delta No baseline available for comparison. Current sorry-tainted declarations: 155
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/79#issuecomment-4553418459) — oliver-butterley (2026-05-27): Can you explain why we can't achieve the same result by modifying FunsExternal.lean, changing the axiom \`encoding.gf.GF16.Insts.CoreOpsArithMulAssignShared0GF16.mul\_assign\` to the definition as written here using a tweak?
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/79#issuecomment-4553511375) — truonghoangle (2026-05-27): In Rust the \`encoding.gf.GF16.Insts.CoreOpsArithMulAssignShared0GF16.mul\_assign\` function depends on two functions \`unaccelerated::mul\` and \`accelerated::mul\`. Function \`accelerated::mul\` is not defined via Aeneas because of platform-specific SIMD intrinsics. And the \`unaccelerated::mul\` function is defined in the \`Funs.lean\` file by Aeneas and the \`FunsExternal.lean\` file is an \`import\` of the \`Funs.lean\` file. In …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/79#issuecomment-4561244670) — oliver-butterley (2026-05-28): Thanks for the explanation. I see that there is something rather complicated to understand about the Aeneas extraction in this case before we have the proper solution to this problem. I have a few ideas but won't be able to work on it until next week. Do I understand correctly that this is a blocker to other work that needs to be done? If so, then it is worthwhile we merge it so other work can proceed whilst we are …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/79#issuecomment-4561404160) — truonghoangle (2026-05-28): &gt; Do I understand correctly that this is a blocker to other work that needs to be done? Yes, this is the main bottleneck for moving forward. In particular, all subsequent functions depend on passing through this stage. Any unrelated functions have already been handled. After temporarily accepting and merging, I will reopen this issue and we will return to it. Do you want to open it in Aeneas or in this project?
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/79#issuecomment-4561423665) — oliver-butterley (2026-05-28): &gt; Do you want to open it in Aeneas or in this project? Open the issue in this project. When we have understood the root cause(s) then we might open issues on the Aeneas repo.
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/79#pullrequestreview-4378466986) — oliver-butterley (2026-05-28): (No text.)

### Item 80

**[PR #80](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/80) — Fix Batteries lint errors in hand-written Lean files**

Status: merged. Opened: 2026-05-22. Author: astefano.

Body excerpt: This PR: - adds missing doc strings for \`GF216\` and \`polyReduce\` - removes redundant \`@\[simp\]\` from \`ONE\_value\_val\` and \`ZERO\_value\_val\` (simp can already prove these from \`ONE\_value\`/\`ZERO\_value\`) so that we have a green Batteries \`runLinter\`. ## Test plan - \[x\] \`lake build\` succeeds locally - \[x\] CI passes closes https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/82 Made with Cursor

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/80#issuecomment-4518899707) — github-actions[bot] (2026-05-22): ### Sorry Delta No baseline available for comparison. Current sorry-tainted declarations: 155
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/80#pullrequestreview-4353921395) — Zhang-Liao (2026-05-25): (No text.)

### Item 81

**[PR #81](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/81) — CI: fail on non-sorry warnings and lint errors in hand-written code**

Status: merged. Opened: 2026-05-22. Author: astefano.

Body excerpt: This PR: - splits \`lean-action\` into setup-only step (\`build: false\`) and a custom \`lake build\` step that captures output for warning analysis - adds \*\*Build and check for non-sorry warnings\*\* step: fails CI if any warnings other than \`declaration uses 'sorry'\` are found - adds \*\*Lint hand-written code\*\* step: runs Batteries \`runLinter\` and fails CI on lint errors outside \`Spqr/Code/\` (Aeneas-generated files) - adds …

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/81#issuecomment-4531091128) — Zhang-Liao (2026-05-25): Please check why the CI build is failing before opening a PR.
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/81#issuecomment-4536527564) — astefano (2026-05-25): &gt; Please check why the CI build is failing before opening a PR. Sure, i mentioned in the PR description that this PR depends on #80 (it fails on warnings which are fixed in #80, once #80 is merged, this one should be green as well) Now it's green.
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/81#issuecomment-4536598427) — github-actions[bot] (2026-05-25): ### Sorry Delta No new sorry-tainted declarations introduced. (155 total)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/81#pullrequestreview-4363179056) — Kukovec (2026-05-26): You probably meant to write "closes #77", 78 is another PR

### Item 82

**[Issue #82](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/82) — fix warnings from Batteries runLinter**

Status: closed. Opened: 2026-05-22. Author: astefano.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 83

**[Issue #83](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/83) — CI: Lean Verification runs twice on PR pushes**

Status: closed. Opened: 2026-05-22. Author: astefano.

Body excerpt: When pushing to a PR branch that touches Lean-related files, the Lean Verification workflow runs twice — once from the \`push\` trigger (matching \`branches: \['\*\*'\]\`) and once from the \`pull\_request\` trigger. This doubles CI usage with no benefit since only the \`pull\_request\` run matters for the merge gate. \*\*Root cause:\*\* the \`push\` trigger matches all branches (\`'\*\*'\`), so it fires alongside \`pull\_request\` for every …

No recorded comments or reviews.

### Item 84

**[PR #84](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/84) — CI: deduplicate Lean Verification runs on PR branches**

Status: merged. Opened: 2026-05-22. Author: astefano.

Body excerpt: This PR: - restricts the \`push\` trigger in \`lean.yml\` to \`main\` only, so that pushes to PR branches no longer fire both \`push\` and \`pull\_request\` runs of the same workflow - keeps the \`pull\_request\` trigger (which already covers all PRs) and the \`push\`-on-main path (needed for the sorry-manifest cache save step) ## Test plan - \[x\] verify that this PR itself only triggers a single Lean Verification run (not two) - …

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/84#issuecomment-4519101812) — github-actions[bot] (2026-05-22): ### Sorry Delta No baseline available for comparison. Current sorry-tainted declarations: 155
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/84#pullrequestreview-4353944626) — Zhang-Liao (2026-05-25): (No text.)

### Item 85

**[Issue #85](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/85) — CI: Aeneas extraction runs twice on PR pushes**

Status: closed. Opened: 2026-05-22. Author: astefano.

Body excerpt: Same issue as #83 but for the Aeneas extraction workflow: when pushing to a PR branch that touches relevant files, the workflow runs twice — once from the \`push\` trigger (matching \`branches: \['\*\*'\]\`) and once from the \`pull\_request\` trigger. Additionally, the \`paths\` filter references \`.github/workflows/lean.yml\` instead of \`.github/workflows/aeneas.yml\`, and is missing \`aeneas-config.yml\`. \*\*Fix:\*\* restrict the …

No recorded comments or reviews.

### Item 86

**[PR #86](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/86) — CI: deduplicate Aeneas extraction runs on PR branches**

Status: merged. Opened: 2026-05-22. Author: astefano.

Body excerpt: This PR: - restricts the \`push\` trigger in \`aeneas.yml\` to \`main\` only, so that pushes to PR branches no longer fire both \`push\` and \`pull\_request\` runs of the same workflow - fixes the \`paths\` filter: it was referencing \`.github/workflows/lean.yml\` instead of \`.github/workflows/aeneas.yml\`, and was missing \`aeneas-config.yml\` ## Test plan - \[x\] verify that this PR itself only triggers a single Aeneas extraction run …

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/86#issuecomment-4519129713) — github-actions[bot] (2026-05-22): ### Sorry Delta No baseline available for comparison. Current sorry-tainted declarations: 155
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/86#pullrequestreview-4353947099) — Zhang-Liao (2026-05-25): (No text.)

### Item 87

**[PR #87](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/87) — test: verify CI lint warning gate**

Status: closed unmerged. Opened: 2026-05-26. Author: astefano.

Body excerpt: ## Summary - Introduces an intentional unused-variable warning in \`Spqr/Specs/Encoding/Gf/GF16/ZERO.lean\` to verify that the CI lint gate from #81 correctly catches and fails on non-sorry warnings. ## Expected outcome The \*\*"Build and check for non-sorry warnings"\*\* step in the Lean Verification workflow should \*\*fail\*\* with a message about the unused variable \`unusedBinding\`. ## Cleanup Close/delete this PR after …

No recorded comments or reviews.

### Item 88

**[PR #88](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/88) — CI: harden sorry manifest cache with restore-keys fallback**

Status: closed unmerged. Opened: 2026-05-26. Author: astefano.

Body excerpt: This PR: - allows \`workflow\_dispatch\` to save the sorry manifest cache (previously only \`push\` events could save) - adds \`restore-keys\` prefix fallback to the cache restore step so it uses the most recent available manifest when an exact SHA match isn't available Context: The sorry manifest caching added in #81 works correctly under normal conditions (each merge to main triggers a Lean workflow run that saves the …

No recorded comments or reviews.

### Item 89

**[PR #89](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/89) — Updated guidelines**

Status: merged. Opened: 2026-05-27. Author: Kukovec.

Body excerpt: closes #32

Discussion and review record:

- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/89#discussion_r3318525347) — truonghoangle (2026-05-28; doc/WORKFLOW_AND_PR_GUIDE.md:33): Is there a specific number for this?
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/89#pullrequestreview-4381887790) — truonghoangle (2026-05-28): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/89#discussion_r3318575559) — truonghoangle (2026-05-28; doc/WORKFLOW_AND_PR_GUIDE.md:25): With functions defined through multiple loops, and by rule they are in the same file, often far exceeding 500 PCs, what should we do in this case? Should we continue creating a PR for each loop function, or create a PR for all loop functions simultaneously until we obtain the spec theorem describing the function we need to verify?
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/89#pullrequestreview-4381950135) — truonghoangle (2026-05-28): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/89#discussion_r3324223632) — Kukovec (2026-05-29; doc/WORKFLOW_AND_PR_GUIDE.md:33): Do you want there to be one? Would it be clearer if it said e.g. "within 3 days"?
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/89#discussion_r3324244180) — Kukovec (2026-05-29; doc/WORKFLOW_AND_PR_GUIDE.md:25): Well, the line does start with \`whenever possible\`. The LOC number, it's just a general guideline, not an iron rule. Besides, even if the function definition is split, the non-documentation part of the spec/proof code is generally still under 500 LOC, imex. Tanking a step back, I think it's more important to identify that the guidelines call for a mimimization effort from PR authors. Any attempt to give ironclad …
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/89#pullrequestreview-4389382718) — Kukovec (2026-05-29): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/89#discussion_r3324383689) — truonghoangle (2026-05-29; doc/WORKFLOW_AND_PR_GUIDE.md:33): "within 3 days"'s necessary because many people might have to wait for other people's results.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/89#pullrequestreview-4389588347) — truonghoangle (2026-05-29): (No text.)
- [review DISMISSED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/89#pullrequestreview-4389599692) — truonghoangle (2026-05-29): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/89#discussion_r3324726407) — Kukovec (2026-05-29; doc/WORKFLOW_AND_PR_GUIDE.md:33): \`\`\`suggestion After review the author is solely responsible for merging in the accepted PR, and is expected to do so in a timely manner (ideally within 3 days). \`\`\` Like this?
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/89#pullrequestreview-4390031032) — Kukovec (2026-05-29): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/89#discussion_r3325039682) — truonghoangle (2026-05-29; doc/WORKFLOW_AND_PR_GUIDE.md:33): Yes, it's clear to everyone.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/89#pullrequestreview-4390443542) — truonghoangle (2026-05-29): (No text.)
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/89#issuecomment-4576408346) — truonghoangle (2026-05-29): Do you know why the src doesn't pass? You haven't changed everything.
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/89#issuecomment-4578202283) — Kukovec (2026-05-29): &gt; Do you know why the src doesn't pass? You haven't changed everything. Yes, https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/79 desynced the file, and was merged anyway because "Source modification check" was (and currently still is) not mandatory for merging. All PRs since have had this issue
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/89#pullrequestreview-4400464931) — oliver-butterley (2026-06-01): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/89#discussion_r3333486007) — oliver-butterley (2026-06-01; doc/WORKFLOW_AND_PR_GUIDE.md:50): We haven't activated "externally\_verified" in this repo and I'm not inclined to do so. Moreover there is both the case of a spec theorem and some mathematics theorem. How about rephrasing as follows? \`\`\` if the \`sorry\` substitutes the proof of something proven externally, the documentation must list the source. \`\`\`
- [review DISMISSED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/89#pullrequestreview-4400467498) — oliver-butterley (2026-06-01): LGTM modulo the comment I made
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/89#discussion_r3333515836) — Kukovec (2026-06-01; doc/WORKFLOW_AND_PR_GUIDE.md:50): So I spoke with @astefano about how probe detects axioms, and the 2 ways (correct me if I'm wrong) are: - via the \`axiom\` keyword, and - via the \`externally\_verified\` tag but things that are named \`axiom\_X ... by := sorry\` do not get picked up as axioms (though, IIUC, these are the most common in e.g. dalek-lean). I'm wondering then if we should mandate the use of \`axiom\`, and omit the case where we have axioms …
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/89#pullrequestreview-4400495507) — Kukovec (2026-06-01): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/89#discussion_r3333656513) — oliver-butterley (2026-06-01; doc/WORKFLOW_AND_PR_GUIDE.md:50): - \`externally\_verified\` was a hack to satisfy Max when he wanted certain data displayed in plots, - using sorry where axiom was natural was a hack because in the past Harmonic's Aristotle didn't like axioms We should base anything on hacks, they were just useful at that time and not required any longer. Let's make the guidelines say that a sorry is for something where there proof will be added later, axiom is used …
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/89#pullrequestreview-4400651698) — oliver-butterley (2026-06-01): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/89#discussion_r3334183542) — astefano (2026-06-01; doc/WORKFLOW_AND_PR_GUIDE.md:50): &gt; please let us keep the correct focus: we do what works best for verifying functional correctness, if required the probe tools have to adapt for improvements, they are not our guide. I'd push back on the framing here: looking at what probe-lean does was useful (in that it led to the question "should we use the convention axiom\_"), and surely not a case of letting the tool drive design. My read of Jure's comment was …
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/89#pullrequestreview-4401242118) — astefano (2026-06-01): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/89#discussion_r3334652353) — oliver-butterley (2026-06-01; doc/WORKFLOW_AND_PR_GUIDE.md:50): I suggest we use axiom rather than theorem, I don't think a prefix of axiom\_ makes sense.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/89#pullrequestreview-4401768117) — oliver-butterley (2026-06-01): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/89#pullrequestreview-4427344771) — oliver-butterley (2026-06-04): it's perfect!

### Item 90

**[Issue #90](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/90) — Issue for \`encoding.gf.GF16.Insts.CoreOpsArithMulAssignShared0GF16.mul\_assign\` in \`gf.rs\`**

Status: closed. Opened: 2026-05-28. Author: truonghoangle.

Body excerpt: The goal is to eventually replace the \`mul\_assign\` axiom with a proper definition. Currently, it is axiomatized because its Rust implementation depends on both \`accelerated::mul\` and \`unaccelerated::mul\`, while \`accelerated::mul\` is omitted by Aeneas due to platform-specific SIMD intrinsics. In principle, \`mul\_assign\` can be defined solely using \`unaccelerated::mul\`. However, this is currently blocked by function …

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/90#issuecomment-4677805173) — oliver-butterley (2026-06-11): @truonghoangle is this issue still current or was the problem solved in the later updates?
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/90#issuecomment-4677936013) — truonghoangle (2026-06-11): this issue was the problem solved in #106

### Item 91

**[PR #91](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/91) — Specify and verify : \`spqr::encoding::gf::mul\_assign\` in \`gf.rs\`**

Status: merged. Opened: 2026-05-28. Author: truonghoangle.

Body excerpt: This PR specifies and verifies two function: spqr::encoding::gf::{impl ops::MulAssign for GF16}::mul\_assign spqr::encoding::gf::{impl ops::MulAssign for GF16}::mul\_assign closes #65

Discussion and review record:

- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/91#discussion_r3317428251) — Kukovec (2026-05-28; src-modifications.diff:1): Why is this PR triggering source modification file diffs, when I don't see it modifying \`src\`?
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/91#pullrequestreview-4380534907) — Kukovec (2026-05-28): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/91#discussion_r3317584395) — truonghoangle (2026-05-28; src-modifications.diff:1): I don't know why when I first tried to PR it, it gave an error saying it needed to run \`src\`.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/91#pullrequestreview-4380716416) — truonghoangle (2026-05-28): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/91#discussion_r3317606612) — Kukovec (2026-05-28; src-modifications.diff:1): Is this an artifact of some un-commited ongoing work?
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/91#pullrequestreview-4380741975) — Kukovec (2026-05-28): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/91#discussion_r3317683844) — truonghoangle (2026-05-28; src-modifications.diff:1): I think you're right, after the PR is approved and merged, I continue working on the fork I PRed. On the fork, I need to update it with the main file, then the issue might be reported.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/91#pullrequestreview-4380835869) — truonghoangle (2026-05-28): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/91#discussion_r3317853625) — Kukovec (2026-05-28; src-modifications.diff:1): Ok, then if it's not a part of this PR, roll it back here.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/91#pullrequestreview-4381049664) — Kukovec (2026-05-28): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/91#discussion_r3317912850) — truonghoangle (2026-05-28; src-modifications.diff:1): Ah, I realize that it seems the original Spqr rust has changed and PR is asking me to run it instead of the issue you mentioned.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/91#pullrequestreview-4381119549) — truonghoangle (2026-05-28): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/91#discussion_r3318222437) — truonghoangle (2026-05-28; src-modifications.diff:1): I actually went back to not run \`src\`
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/91#pullrequestreview-4381510889) — truonghoangle (2026-05-28): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/91#pullrequestreview-4383218267) — Kukovec (2026-05-28): (No text.)

### Item 92

**[PR #92](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/92) — Specify and verify : \`spqr::encoding::gf::mul\` in \`gf.rs\`**

Status: merged. Opened: 2026-05-28. Author: truonghoangle.

Body excerpt: This PR specifies and verifies two functions spqr::encoding::gf::{impl ops::Mul for GF16}::mul spqr::encoding::gf::{impl ops::Mul for GF16}::mul closes #66

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/92#pullrequestreview-4389414478) — Kukovec (2026-05-29): (No text.)

### Item 93

**[PR #93](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/93) — Triger source-diff check on PR + push**

Status: closed unmerged. Opened: 2026-05-29. Author: Kukovec.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 94

**[Issue #94](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/94) — Write contents of README.md**

Status: closed. Opened: 2026-05-29. Author: MarkusFerdinandDablander.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 95

**[PR #95](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/95) — Update README.md and add Apache Licence**

Status: merged. Opened: 2026-05-29. Author: MarkusFerdinandDablander.

Body excerpt: This PR replaces the content of the current placeholder README.md with some high-level project information: - a short description of the SPQR verification effort, - links to upstream SPQR, Aeneas, Lean, and BAIF, - a repo-structure table giving an overview of the repo organisation, - pointers to CONTRIBUTING.md and the doc/ guides, - the project's code-of-conduct policy (link to Rust CoC), and - an AGPL-3.0-only …

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/95#issuecomment-4576354927) — truonghoangle (2026-05-29): Do you know why the src doesn't pass?
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/95#issuecomment-4576407241) — MarkusFerdinandDablander (2026-05-29): Hi @truonghoangle , it believe that in a prior PR it may have been forgotten to run npm run src-diff and thus the current state of "src-modifications.diff" in "main" is not appropriately regenerated. I can try to fix this right here in this PR by regenerating "src-modifications.diff" and then updating this PR, which should also fix this issue for subsequent PRs by updating the offending file in main. What do you …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/95#issuecomment-4576471467) — truonghoangle (2026-05-29): I ran it in PR #79: \`npm run src-diff\` In any case, we have a problem here. If I didn't run it in PR #79, then I still need to fix it. I also encountered this error yesterday, but it disappeared afterward. Could you try running it on a different branch to check whether the original Rust code we mentioned has changed? @Kukovec Perhaps we should discuss the same issue in your PR in this thread.
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/95#issuecomment-4576575926) — MarkusFerdinandDablander (2026-05-29): I just ran npm run src-diff in the "main" branch and this results in a modified src-modifications.diff file. My current interpretation of this is that this means that "main" itself is broken, i.e., the committed src-modifications.diff does not match what the script regenerates from the current src/ + pinned upstream commit. A possible fix would be to create a novel PR just to fix this issue by simply running npm run …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/95#issuecomment-4576860060) — MarkusFerdinandDablander (2026-05-29): I think merging PR #96 ahead of this PR may now resolve the CI issue by appropriately syncing the changed Rust source with the diff file. It remains not quite clear to me though why these were out of sync within "main" in the first place, and whether there perhaps was a deeper reason for this.
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/95#issuecomment-4578148190) — Kukovec (2026-05-29): There's a slack discussion about this, we'll address the src suff during Monday's meeting.
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/95#discussion_r3333268989) — oliver-butterley (2026-06-01; README.md:44): Ah! This is the licence for the original code in the repo! We are adding all the specs and proofs under Apache license. Can you add this clarification here?
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/95#pullrequestreview-4400235828) — oliver-butterley (2026-06-01): (No text.)
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/95#pullrequestreview-4400247758) — oliver-butterley (2026-06-01): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/95#discussion_r3333280629) — oliver-butterley (2026-06-01; README.md:22): Remove the line about extraction-notes.md, this is likely to go stale soon. They are just notes and probably will stop existing sometime soon since everything relevant is written as comments in other places
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/95#discussion_r3333293281) — oliver-butterley (2026-06-01; README.md:17): Remove mention of Spqr.lean, everyone who works with Lean knows this and those that don't know don't benefit from knowing about it. 😉
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/95#pullrequestreview-4400260732) — oliver-butterley (2026-06-01): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/95#discussion_r3342512277) — MarkusFerdinandDablander (2026-06-02; README.md:44): Hi @oliver-butterley , thanks for the useful comment, this all makes sense! So if I understand correctly, this means that the LICENSE.md file currently in the root of the SPQR repo reflects the license for the upstream source code, and this upstream license is a GNU Affero General Public License v3 (= abbreviated as \[AGPL-3.0-only\]). Presumably I should then do the following three things (let me know if this makes …
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/95#pullrequestreview-4411314591) — MarkusFerdinandDablander (2026-06-02): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/95#discussion_r3342594643) — oliver-butterley (2026-06-02; README.md:44): Actually... this is perhaps something we should have thought more about! Would it be better if all the code we add is also contributed under the same license as upstream? Might make it easier when we want to PR into upstream. I know that licences can be changed if everyone who holds them agrees, so we can at this stage change the licence of everything we have contributed. But best to do this sooner rather than …
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/95#pullrequestreview-4411411067) — oliver-butterley (2026-06-02): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/95#discussion_r3344877729) — oliver-butterley (2026-06-02; README.md:44): I thought a bit more: I like the style of the apache licence and the copyright headers which also mention the authors. It matches what is common in the lean world and I like the feeling it gives of a massively collaborative effort. I'm inlined to keep with this unless there is some other strong reason. I.e., the Rust code is all with the upstream licence but all the lean code is done according the the common lean …
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/95#pullrequestreview-4414153993) — oliver-butterley (2026-06-02): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/95#discussion_r3349236395) — MarkusFerdinandDablander (2026-06-03; README.md:44): Hi @oliver-butterley , thanks for the comment this all makes sense! Similar to in Dalek-Lean, we also seem to have a bit of a messy situation with our license files in this repo. We have one file at the root called "LICENSE" (presumably from the original source) which contains a "GNU Affero General Public License v3.0 only" license. But once again, our Lean spec theorem files refer to a (not yet existing) Apache …
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/95#pullrequestreview-4419441656) — MarkusFerdinandDablander (2026-06-03): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/95#discussion_r3349248995) — MarkusFerdinandDablander (2026-06-03; README.md:22): Removed!
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/95#pullrequestreview-4419456374) — MarkusFerdinandDablander (2026-06-03): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/95#discussion_r3349251230) — MarkusFerdinandDablander (2026-06-03; README.md:17): Removed!
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/95#pullrequestreview-4419458782) — MarkusFerdinandDablander (2026-06-03): (No text.)
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/95#issuecomment-4631183442) — oliver-butterley (2026-06-05): @MarkusFerdinandDablander I added the \*\*Awaiting Author\*\* tag whilst you are still working on this. Remove it when you are done and it is ready for review again.
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/95#issuecomment-4632692614) — MarkusFerdinandDablander (2026-06-05): Hi @oliver-butterley thanks for the message! The PR is now once again ready for you to review; as proposed, I have thus now removed the \*\*Awaiting Author\*\* tag again. Here are the changes I implemented following our recent discussion: - Added "LICENSE-APACHE" to repo root (copied over from Dalek-Lean and named after conventions suitable for dual-license repos) - Changed all 31 Lean spec theorem file headers to now …
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/95#discussion_r3364290063) — oliver-butterley (2026-06-05; Cargo.toml:9): Let's remove this comment since this is the cargo.toml and so applies only to the Rust project, nothing else. This is unambiguous. It's also somewhat strange to mention the other work outside of the rust project here.
- [review CHANGES_REQUESTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/95#pullrequestreview-4438266679) — oliver-butterley (2026-06-05): Great! Well done for all the leg work tracking the location of mentions of different licences! Just one little request about the cargo.toml
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/95#discussion_r3371873179) — MarkusFerdinandDablander (2026-06-08; Cargo.toml:9): Removed!
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/95#pullrequestreview-4447854769) — MarkusFerdinandDablander (2026-06-08): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/95#pullrequestreview-4448474036) — oliver-butterley (2026-06-08): Great!
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/95#pullrequestreview-4449230575) — oliver-butterley (2026-06-08): (No text.)

### Item 96

**[PR #96](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/96) — Fix src diff CI issue**

Status: merged. Opened: 2026-05-29. Author: MarkusFerdinandDablander.

Body excerpt: This PR addresses the CI issue discussed in PR #95 by running npm run src-diff to make the committed src-modifications.diff match what the script regenerates from the current src/ + pinned upstream commit. Closes #97 PS: This seems to resolve the CI issue, but it remains not quite clear to me why this discrepancy existed within "main" in the first place, and whether there perhaps was a deeper reason for this.

Discussion and review record:

- [review CHANGES_REQUESTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/96#pullrequestreview-4391711959) — Kukovec (2026-05-29): Blocking this for now, we need to address the underlying reason for the desync instead of patching it. See slack.
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/96#issuecomment-4591525642) — oliver-butterley (2026-06-01): This corrects what was done in #79 where the Rust source was modified but the src-diff file wasn't updated accordingly. We should merge this PR so the repo is consistent. Later we need to understand how to revert these modifications to the Rust source.
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/96#pullrequestreview-4401171448) — Kukovec (2026-06-01): (No text.)

### Item 97

**[Issue #97](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/97) — Fix the CI issue discussed in PR #95 related to src diff tracking**

Status: closed. Opened: 2026-05-29. Author: MarkusFerdinandDablander.

Body excerpt: See discussion in PR #95 and the proposed fix in PR #96.

No recorded comments or reviews.

### Item 98

**[PR #98](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/98) — Specify and verify \`spqr::encoding::gf::div\_impl\` in \`gf.rs\`**

Status: merged. Opened: 2026-05-29. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::encoding::gf::div\_impl\` in \`gf.rs\` closes #71

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/98#issuecomment-4592911592) — oliver-butterley (2026-06-01): !radar
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/98#issuecomment-4592912634) — baif-radar (2026-06-01): Benchmark results for 80f809e2bb6d4af7ae6c5e651d87f4efa375a08e against 4798c4bf5cd3ec2b868c5011bff9d18e535dfd97 are in. No significant results found. @oliver-butterley No significant changes detected.
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/98#issuecomment-4593041755) — truonghoangle (2026-06-01): @Kukovec @oliver-butterley Do you know why \`check src\` is not passing?
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/98#issuecomment-4593161275) — oliver-butterley (2026-06-01): &gt; @Kukovec @oliver-butterley Do you know why \`check src\` is not passing? @Kukovec is it because \`\`\` pull\_request: branches: \[ '\*\*' \] \`\`\` needs to be set in the src-diff workflow? I think this workflow is not being triggered even though it is a required check for PRs.
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/98#issuecomment-4593193142) — Kukovec (2026-06-01): &gt; &gt; @Kukovec @oliver-butterley Do you know why \`check src\` is not passing? &gt; &gt; @Kukovec is it because &gt; &gt; \`\`\` &gt; pull\_request: &gt; branches: \[ '\*\*' \] &gt; \`\`\` &gt; &gt; needs to be set in the src-diff workflow? I think this workflow is not being triggered even though it is a required check for PRs. I made https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/100 My understanding is that chaning the …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/98#issuecomment-4593482077) — truonghoangle (2026-06-01): @Kukovec @oliver-butterley Thank you for your help!
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/98#issuecomment-4601753899) — truonghoangle (2026-06-02): @Kukovec @oliver-butterley Could you please let me know the review results of the PR?
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/98#discussion_r3355394116) — oliver-butterley (2026-06-04; Spqr/Specs/Encoding/Gf/GF16/DivImpl.lean:96): An alternate way of writing the spec is as follows. All the same proof works with zero edits. I think it is more readable like this. What do you think? \`\`\` match opt with | some z =&gt; start.val + 1 ≤ I32.max ∧ z.val = start.val + 1 | none =&gt; ¬ start.val + 1 ≤ I32.max \`\`\`
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/98#discussion_r3355402310) — oliver-butterley (2026-06-04; Spqr/Specs/Encoding/Gf/GF16/DivImpl.lean:111): \`\`\`suggestion | some z =&gt; exact ⟨some z, rfl, fun \_ =&gt; ⟨z, rfl, by grind⟩, fun h =&gt; by grind⟩ \`\`\` These 4 lines can naturally be a single line. But just my personal preference!
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/98#discussion_r3355409864) — oliver-butterley (2026-06-04; Spqr/Specs/Encoding/Gf/GF16/DivImpl.lean:132): As before, consider the possibility of the equivalent statement for the post condition: \`\`\`suggestion (match opt with | none =&gt; ¬ iter.start.val iter.start.val &lt; iter.end.val ∧ v = iter.start ∧ iter1.start.val = iter.start.val + 1 ∧ iter1.end = iter.end ⦄ := by \`\`\` Again the current proofs hold without any modification.
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/98#discussion_r3355414252) — oliver-butterley (2026-06-04; Spqr/Specs/Encoding/Gf/GF16/DivImpl.lean:191): \`\`\`suggestion step\* \`\`\` Replacing \`step\` with \`step\*\` in this proof closes the goal with no extra work.
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/98#discussion_r3355417226) — oliver-butterley (2026-06-04; Spqr/Specs/Encoding/Gf/GF16/DivImpl.lean:202): I was about to ask why \`div\_impl\_loop\_spec\` isn't tagged as \`\[step\]\` but then I tested and see it causes a problem with the final proof. Can you add a comment in the file to remind us of this. If everything worked correctly I would expect this tagging would allow \`step\*\` to close the proof of \`div\_impl\_spec\`.
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/98#discussion_r3355423891) — oliver-butterley (2026-06-04; Spqr/Specs/Encoding/Gf/GF16/DivImpl.lean:113): The loop invariant is inconsistent with the use in the other statements which makes this proof a little more inefficient. Changing the invariant to match allows the proof to be more concise. The following is a complete proof: \`\`\` theorem div\_impl\_loop\_spec (iter : Range I32) (square out : GF16) (h\_le : iter.start.val ≤ iter.end.val) : div\_impl\_loop iter square out ⦃ (result : GF16) =&gt; result.toGF216 = out.toGF216 \* …
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/98#discussion_r3355426225) — oliver-butterley (2026-06-04; Spqr/Specs/Encoding/Gf/GF16/DivImpl.lean:273): I'm surprised that the docstring is much longer than the theorem statement. Could it be more concise whilst still communicating the key detail?
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/98#discussion_r3355429393) — oliver-butterley (2026-06-04; Spqr/Code/FunsExternal.lean:191): there is no need to add the \`↑\` in \`↑n.val\`.
- [review CHANGES_REQUESTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/98#pullrequestreview-4427124931) — oliver-butterley (2026-06-04): Looks great! The first three theorems don't relate directly to \`div\_impl\` and so it's best that these are in different files. We are likely to reuse these same theorems in other places. ## \`next\_spec\` \`next\_spec\` should have the name \`Aeneas.Std.core.iter.range.IteratorRange.next\_spec\` (currently in the wrong namespace). I would put this in a file called \`Spqr/Aux/AeneasStdSpecs.lean\` or something similar. ## …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/98#issuecomment-4621644537) — truonghoangle (2026-06-04): I was expecting to see this discussion. Based on my perspective and the suggestions here, I propose that: For functions generated from the \`axiom\` in the \`FunsExternal.lean\` file, when additional specification theorems are needed, write them immediately after the definition (if concise). For specification theorems for functions in Aeneas, place them in the \`Aux/Aeneas\` folder. Regarding names, use …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/98#issuecomment-4621656798) — oliver-butterley (2026-06-04): &gt; I was expecting to see this discussion. Based on my perspective and the suggestions here, I propose that: &gt; &gt; For functions generated from the \`axiom\` in the \`FunsExternal.lean\` file, when additional specification theorems are needed, write them immediately after the definition (if concise). &gt; &gt; For specification theorems for functions in Aeneas, place them in the \`Aux/Aeneas\` folder. &gt; &gt; Regarding names, use …
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/98#discussion_r3355949086) — truonghoangle (2026-06-04; Spqr/Specs/Encoding/Gf/GF16/DivImpl.lean:202): If I use the \`\[step\]\`, it takes 2 minutes and 21 seconds. While without the \`\[step\]\`, it takes about 3 seconds.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/98#pullrequestreview-4427762787) — truonghoangle (2026-06-04): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/98#discussion_r3356014994) — oliver-butterley (2026-06-04; Spqr/Specs/Encoding/Gf/GF16/DivImpl.lean:202): Right! That explains your choice! I suspect that step\* will get better soon but best avoided in this use case at the moment!
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/98#pullrequestreview-4427842418) — oliver-butterley (2026-06-04): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/98#discussion_r3356138489) — truonghoangle (2026-06-04; Spqr/Specs/Encoding/Gf/GF16/DivImpl.lean:273): I fixed it
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/98#pullrequestreview-4427991388) — truonghoangle (2026-06-04): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/98#pullrequestreview-4428287697) — oliver-butterley (2026-06-04): LGTM!

### Item 99

**[Issue #99](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/99) — Revert source code modifications introduced by #79**

Status: closed. Opened: 2026-06-01. Author: Kukovec.

Body excerpt: Rust source got modified in #79 in order to permit verification of other functions. We need to: - Understand what the source issue is - Upstream to Aeneas the solution of open an issue - After using the updated version of Aeneas, revert the changes

No recorded comments or reviews.

### Item 100

**[PR #100](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/100) — Update src-diff.yml**

Status: merged. Opened: 2026-06-01. Author: Kukovec.

Body excerpt: unblocks PRs that hang due to workflow changes midway.

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/100#pullrequestreview-4401734952) — oliver-butterley (2026-06-01): 🚀

### Item 101

**[Issue #101](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/101) — Solve the extraction problem for spqr::send using chain.Chain**

Status: closed. Opened: 2026-06-02. Author: oliver-butterley.

Body excerpt: Local variable name shadowing module namespace causes field projection error. Aeneas generates Lean code where subsequent namespace-qualified calls become ambiguous. Lean resolves x.M.f as a field projection from the local variable x rather than as a namespace-qualified call M.f. Example (from spqr::send): \`\`\` let chain: Chain = ...; let (index, msg\_key) = chain.send\_key(...)?; // chain:: namespace call \`\`\`\` …

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/101#issuecomment-6233585268) — oliver-butterley (2026-10-17): Closing this since it is replaced by the Aeneas issue.

### Item 102

**[Issue #102](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/102) — Extraction problem: self-referential when field names match the trait's Lean structure fields**

Status: closed. Opened: 2026-06-02. Author: oliver-butterley.

Body excerpt: Investigate the problem seen with some functions in this repo. Claude tells: Trait instance struct literals are self-referential when field names match the trait's Lean structure fields, causing termination errors When Aeneas generates a trait implementation as a Lean struct literal, each field value is named after the instance itself (e.g. \`X.Insts.Foo.method\`). If the method name is also a genuine field of the …

No recorded comments or reviews.

### Item 103

**[Issue #103](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/103) — Extraction problem: spqr::encoding::polynomial::{...}::decoded\_message**

Status: closed. Opened: 2026-06-02. Author: oliver-butterley.

Body excerpt: Figure out the problem, solve and extract this function. Rather \*\*high priority\*\*!

No recorded comments or reviews.

### Item 104

**[Issue #104](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/104) — Extraction problem: spqr::kdf::hkdf\_to\_slice**

Status: closed. Opened: 2026-06-02. Author: oliver-butterley.

Body excerpt: Figure out the problem, fix it and extract this function

No recorded comments or reviews.

### Item 105

**[Issue #105](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/105) — Update Aeneas to latest version (ac9f1bc)**

Status: closed. Opened: 2026-06-02. Author: oliver-butterley.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 106

**[PR #106](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/106) — Update Aeneas to version ac9f1bc5**

Status: merged. Opened: 2026-06-02. Author: oliver-butterley.

Body excerpt: Primary change: update pinned Aeneas from \`3fb1cd4b\` to \`ac9f1bc5\` (both for extraction and for Lean) and fix all resulting breakage in extraction and proofs. - \`MulAssign\` is now transparent and hence we revert the source modifications previously used for mul\_assign (see issue #99) - \`--start-from-pub\` cannot be used with the new Aeneas/Charon because it triggers the Try trait error. Switched to whole-crate …

Discussion and review record:

- [review DISMISSED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/106#pullrequestreview-4415404944) — truonghoangle (2026-06-03): (No text.)
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/106#issuecomment-4622592018) — oliver-butterley (2026-06-04): I merged main and then noticed a few improvements and updated a the PR slightly.
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/106#pullrequestreview-4428247093) — truonghoangle (2026-06-04): (No text.)

### Item 107

**[Issue #107](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/107) — Fix licensing file inconsistencies**

Status: closed. Opened: 2026-06-03. Author: MarkusFerdinandDablander.

Body excerpt: Similar to in Dalek-Lean, we also seem to have a bit of a messy situation with our license files in this repo. We have one file at the root called "LICENSE" (presumably from the original source) which contains a "GNU Affero General Public License v3.0 only" license. But once again, our Lean spec theorem files refer to a (not yet existing) Apache license, and incorrectly claim that this Apache license is in the …

No recorded comments or reviews.

### Item 108

**[Issue #108](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/108) — Lean model for \`core::result\` methods and \`Try\` trait**

Status: closed. Opened: 2026-06-04. Author: oliver-butterley.

Body excerpt: For each of the following functions from the standard library, convert the axiom to a def and add appropriate spec theorem(s). - \[x\] \`core.result.Result.ok\` - \[ \] \`core.result.Result.is\_ok\` - \[ \] \`core.result.Result.map\` - \[ \] \`core.result.Result.map\_err\` - \[ \] \`core.result.Result.unwrap\_or\` - \[ \] \`core.result.Result.Insts.CoreOpsTry\_traitTryTResultInfallibleE.branch\` - \[ \] …

No recorded comments or reviews.

### Item 109

**[Issue #109](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/109) — Lean model for \`core::option\` methods and trait instances**

Status: closed. Opened: 2026-06-04. Author: oliver-butterley.

Body excerpt: For each of the following functions from the standard library, convert the axiom to a def and add appropriate spec theorem(s). - \[ \] \`core.option.Option.as\_ref\` - \[ \] \`core.option.Option.ok\_or\` - \[ \] \`core.option.Option.Insts.CoreCloneClone.clone\` - \[ \] \`core.option.Option.Insts.CoreDefaultDefault.default\` - \[ \] \`core.option.Option.Insts.CoreCmpPartialEqOption.eq\` \*\*Rust docs:\*\* - \`Option::as\_ref\` - \`Option::ok\_or\` …

No recorded comments or reviews.

### Item 110

**[Issue #110](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/110) — Lean model for \`alloc::collections::vec\_deque\`: VecDeque and its IntoIter**

Status: closed. Opened: 2026-06-04. Author: oliver-butterley.

Body excerpt: For each of the following functions from the standard library, convert the axiom to a def and add appropriate spec theorem(s). - \[ \] \`alloc.collections.vec\_deque.VecDeque.len\` - \[ \] \`alloc.collections.vec\_deque.VecDeque.pop\_front\` - \[ \] \`alloc.collections.vec\_deque.VecDeque.push\_back\` - \[ \] \`alloc.collections.vec\_deque.VecDeque.Insts.CoreOpsIndexIndexMutUsizeT.index\_mut\` - \[ \] …

No recorded comments or reviews.

### Item 111

**[Issue #111](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/111) — Lean model for \`alloc::vec\` mutation methods**

Status: closed. Opened: 2026-06-04. Author: oliver-butterley.

Body excerpt: For each of the following functions from the standard library, convert the axiom to a def and add appropriate spec theorem(s). - \[ \] \`alloc.vec.Vec.truncate\` - \[ \] \`alloc.vec.Vec.as\_slice\` - \[ \] \`alloc.vec.Vec.remove\` - \[ \] \`alloc.vec.Vec.append\` - \[ \] \`alloc.vec.Vec.clear\` - \[ \] \`alloc.vec.Vec.is\_empty\` - \[ \] \`alloc.vec.Vec.split\_off\` - \[ \] \`alloc.vec.Vec.Insts.CoreDefaultDefault.default\` \*\*Rust docs:\*\* - …

No recorded comments or reviews.

### Item 112

**[Issue #112](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/112) — Lean model for \`core::slice\`, \`alloc::slice\`, and \`core::array::from\_fn\`**

Status: closed. Opened: 2026-06-04. Author: oliver-butterley.

Body excerpt: For each of the following functions from the standard library, convert the axiom to a def and add appropriate spec theorem(s). - \[x\] \`core.slice.Slice.clone\_from\_slice\` - \[ \] \`core.slice.Slice.copy\_within\` - \[ \] \`Slice.Insts.CoreCmpPartialEqArray.eq\` - \[ \] \`Slice.Insts.CoreCmpOrd.cmp\` - \[ \] \`alloc.slice.Slice.concat\` - \[ \] \`Slice.Insts.AllocSliceConcatTVec.concat\` - \[ \] \`core.array.from\_fn\` \*\*Rust docs:\*\* - …

No recorded comments or reviews.

### Item 113

**[Issue #113](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/113) — Lean model for \`core::slice::iter\`: slice iteration**

Status: closed. Opened: 2026-06-04. Author: oliver-butterley.

Body excerpt: For each of the following functions from the standard library, convert the axiom to a def and add appropriate spec theorem(s). - \[x\] \`SharedASlice.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into\_iter\` - \[x\] \`core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.map\` - \[x\] ~\`core.slice.iter.ChunksExact.Insts.CoreIterTraitsIteratorIteratorSharedASlice.collect\`~ - \[x\] …

No recorded comments or reviews.

### Item 114

**[Issue #114](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/114) — Lean model for \`core::iter::adapters\`: \`Enumerate\` and \`Map\`**

Status: closed. Opened: 2026-06-04. Author: oliver-butterley.

Body excerpt: For each of the following functions from the standard library, convert the axiom to a def and add appropriate spec theorem(s). - \[x\] \`core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0\_Item.next\` - \[x\] ~\`core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0\_Item.collect\`~ redundant - \[x\] …

No recorded comments or reviews.

### Item 115

**[Issue #115](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/115) — Lean model for \`core::ops::range\`: \`RangeFull\` and \`RangeFrom\` indexing**

Status: closed. Opened: 2026-06-04. Author: oliver-butterley.

Body excerpt: For each of the following functions from the standard library, convert the axiom to a def and add appropriate spec theorem(s). - \[x\] \`core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index\` - \[ \] \`core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index\_mut\` - \[ \] \`core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get\_unchecked\_mut\` - \[ \] …

No recorded comments or reviews.

### Item 116

**[Issue #116](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/116) — Lean model for \`core::borrow\`, \`core::convert\`, \`core::iter::range\`: small utilities**

Status: closed. Opened: 2026-06-04. Author: oliver-butterley.

Body excerpt: For each of the following functions from the standard library, convert the axiom to a def and add appropriate spec theorem(s). - \[ \] \`Shared0T.Insts.CoreBorrowBorrow.borrow\` - \[ \] \`U32.Insts.CoreConvertTryFromU64TryFromIntError.try\_from\` - \[ \] \`I32.Insts.CoreIterRangeStep.backward\_checked\` - \[ \] \`I32.Insts.CoreIterRangeStep.forward\_checked\` - \[ \] \`I32.Insts.CoreIterRangeStep.steps\_between\` \*\*Rust docs:\*\* - …

No recorded comments or reviews.

### Item 117

**[Issue #117](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/117) — Aeneas/Charon issue ofter update: \`core::ops::try\_trait::Try\` now has 2 parent clauses**

Status: closed. Opened: 2026-06-04. Author: oliver-butterley.

Body excerpt: After updating Aeneas/Charon we get: \`\`\` Error: Invalid builtin information for trait decl: core::ops::try\_trait::Try; expected 2 parent clauses, found 1 \`\`\` "Expected 2" = what the LLBC provides; "found 1" = what \`ExtractBuiltinLean.ml\` declares. ## Minimal Rust example \`\`\`rust pub fn example(x: Result) -&gt; Result { Ok(x?) } \`\`\` \*\*Note: the problem appears when we use \`--start-from-pub\` and doesn't when we extract …

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/117#issuecomment-4636007251) — oliver-butterley (2026-06-05): Solved in https://github.com/AeneasVerif/charon/pull/1271, just need to update our use of Aeneas to the latest version.

### Item 118

**[PR #118](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/118) — Specify and verify : \`spqr::encoding::gf::div\_assign\` in \`gf.rs\`**

Status: merged. Opened: 2026-06-04. Author: truonghoangle.

Body excerpt: This PR specifies and verifies two functions: - spqr::encoding::gf::{impl ops::DivAssign for GF16}::div\_assign - spqr::encoding::gf::{impl ops::DivAssign for GF16}::div\_assign closes #67

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/118#pullrequestreview-4435737853) — oliver-butterley (2026-06-05): Great! LGTM! Again I am surprised that the docstrings are so much longer than the spec theorem statements but I'm sure you are the better judge of what is most convenient in this situation.
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/118#issuecomment-4630982147) — truonghoangle (2026-06-05): Actually, this is an intermediate function defined in Rust to implement the \`Div\` function. I simply repeated its core idea without referring to the preceding functions. Do we need documentation for intermediate functions like this? If complete documentation is required, it could be written in this style; otherwise, it may be sufficient to just indicate where it can be found.
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/118#issuecomment-4631173663) — oliver-butterley (2026-06-05): &gt; Actually, this is an intermediate function defined in Rust to implement the \`Div\` function. I simply repeated its core idea without referring to the preceding functions. &gt; &gt; Do we need documentation for intermediate functions like this? If complete documentation is required, it could be written in this style; otherwise, it may be sufficient to just indicate where it can be found. My person opinion: I prefer files …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/118#issuecomment-4631239182) — truonghoangle (2026-06-05): Ok, I will rewrite it in next PR(because it still follows this pattern).

### Item 119

**[PR #119](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/119) — Specify and verify \`spqr::encoding::gf::div\` in \`gf.rs\`**

Status: merged. Opened: 2026-06-05. Author: truonghoangle.

Body excerpt: This PR specifies and verifies two functions - spqr::encoding::gf::{impl ops::Div for GF16}::div - spqr::encoding::gf::{impl ops::Div for GF16}::div and rewrite documentations in \`Spqr/Specs/Encoding/Gf/GF16/DivAssign.lean\` closes #68

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/119#pullrequestreview-4436136667) — Kukovec (2026-06-05): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/119#pullrequestreview-4436222212) — oliver-butterley (2026-06-05): That's great! So much cleaner! 🤩

### Item 120

**[Issue #120](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/120) — Fix axiom \`spqr::encoding::gf::mul2\_u16\` in \`gf\`**

Status: closed. Opened: 2026-06-05. Author: truonghoangle.

Body excerpt: The goal is to change the following axiom \`\`\` /-- \[spqr::encoding::gf::mul2\_u16\]: Source: 'src/encoding/gf.rs', lines 216:0-225:1 -/ axiom encoding.gf.mul2\_u16 : Std.U16 → Std.U16 → Std.U16 → Result (Std.U16 × Std.U16) \`\`\` to definition. We will use a following tweak in \`aeneas-config.yml\` \`\`\` # Insert concrete mul2\_u16 body before parallel\_mult loop (opaque because Rust dispatches to SIMD) - find: | /-- …

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/120#issuecomment-4631305292) — truonghoangle (2026-06-05): @oliver-butterley What do you think about this plan?
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/120#issuecomment-4631411682) — oliver-butterley (2026-06-05): Ah! I see the issue. I think instead we can modify the aeneas extraction config and avoid the problem. I'm checking now. (We are forced to exclude the accelerated code in extraction but the filtering was a bit too coarse on this occasion.)
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/120#issuecomment-4631477921) — oliver-butterley (2026-06-05): I belive the problem is solved in #121 in a rather more robust way, avoiding a tweak. Nice work identifying this issue!

### Item 121

**[PR #121](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/121) — Fix axiom \`spqr::encoding::gf::mul2\_u16\` in \`gf\`**

Status: merged. Opened: 2026-06-05. Author: oliver-butterley.

Body excerpt: We can't extract the accelearated code in mul2\_u16 so previously the entire function was marked as opaque. Instead here we make the filter more precise so the extraction takes the unaccelerated code. Precisely we add a \`not(feature = "extraction"),\` gate in one place in the rust source, in the same place which also has a similar hax gate. Fixes #120

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/121#pullrequestreview-4436204409) — Kukovec (2026-06-05): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/121#pullrequestreview-4436214174) — truonghoangle (2026-06-05): (No text.)

### Item 122

**[PR #122](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/122) — Specify and verify : \`spqr::encoding::gf::mul2\_u16\` in \`gf.rs\`**

Status: merged. Opened: 2026-06-05. Author: truonghoangle.

Body excerpt: This PR specify and verify : \`spqr::encoding::gf::mul2\_u16\` in \`gf.rs\` closes #70

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/122#pullrequestreview-4438387600) — oliver-butterley (2026-06-05): LGTM!

### Item 123

**[PR #123](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/123) — Specify and verify: spqr::encoding::gf::parallel\_mult in gf.rs**

Status: merged. Opened: 2026-06-05. Author: truonghoangle.

Body excerpt: This PR specify and verify \`spqr::encoding::gf::parallel\_mult\` in \`gf.rs\`. So, every functions in \`gf.rs\` are verified! closes #69 closes #17

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/123#pullrequestreview-4438592983) — oliver-butterley (2026-06-05): Lgtm

### Item 124

**[Issue #124](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/124) — Verify: \`encoding/polynomial.rs\`**

Status: closed. Opened: 2026-06-05. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 125

**[Issue #125](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/125) — Specify and verify : \`spqr::encoding::polynomial::Poly::zero\` in \`polynomial.rs\`**

Status: closed. Opened: 2026-06-05. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 126

**[Issue #126](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/126) — Specify and verify : \`spqr::encoding::polynomial::Poly::lagrange\_interpolate\` in \`polynomial.rs\`**

Status: closed. Opened: 2026-06-05. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 127

**[Issue #127](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/127) — Specify and verify : \`spqr::encoding::polynomial::Poly::lagrange\_interpolate\_prepare\` in \`polynomial.rs\`**

Status: closed. Opened: 2026-06-05. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 128

**[Issue #128](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/128) — Specify and verify : \`spqr::encoding::polynomial::Poly::mult\_xdiff\_assign\_trailing\` in \`polynomial.rs\`**

Status: closed. Opened: 2026-06-05. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 129

**[Issue #129](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/129) — Specify and verify : \`spqr::encoding::polynomial::Poly::lagrange\_interpolate\_complete\` in \`polynomial.rs\`**

Status: closed. Opened: 2026-06-05. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 130

**[Issue #130](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/130) — Specify and verify : \`spqr::encoding::polynomial::Poly::lagrange\_interpolate\_pt\` in \`polynomial.rs\`**

Status: closed. Opened: 2026-06-05. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 131

**[Issue #131](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/131) — Specify and verify : \`spqr::encoding::polynomial::Poly::add\_assign\` in \`polynomial.rs\`**

Status: closed. Opened: 2026-06-05. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 132

**[Issue #132](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/132) — Specify and verify : \`spqr::encoding::polynomial::Poly::mult\_assign\` in \`polynomial.rs\`**

Status: closed. Opened: 2026-06-05. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 133

**[Issue #133](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/133) — Specify and verify : \`spqr::encoding::polynomial::Poly::compute\_at\` in \`polynomial.rs\`**

Status: closed. Opened: 2026-06-05. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 134

**[Issue #134](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/134) — Specify and verify : \`spqr::encoding::polynomial::Poly::lagrange\_sum\` in \`polynomial.rs\`**

Status: closed. Opened: 2026-06-05. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 135

**[Issue #135](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/135) — Specify and verify : \`spqr::encoding::polynomial::Poly::from\_complete\_points\` in \`polynomial.rs\`**

Status: closed. Opened: 2026-06-05. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 136

**[Issue #136](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/136) — Specify and verify : \`spqr::encoding::polynomial::Poly::serialize\` in \`polynomial.rs\`**

Status: closed. Opened: 2026-06-05. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 137

**[Issue #137](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/137) — Specify and verify : \`spqr::encoding::polynomial::Poly::deserialize\` in \`polynomial.rs\`**

Status: closed. Opened: 2026-06-05. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 138

**[PR #138](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/138) — Specify and verify : \`spqr::encoding::polynomial::Poly::zero\` in \`polynomial.rs\`**

Status: merged. Opened: 2026-06-08. Author: truonghoangle.

Body excerpt: This PR specify and verify : \`spqr::encoding::polynomial::Poly::zero\` in \`polynomial.rs\` and defined and proved some basic properties of the zero polynomial closes #125

Discussion and review record:

- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/138#discussion_r3372403391) — oliver-butterley (2026-06-08; Spqr/Math/Poly/Basic/Defs.lean:40): Is it useful to have this abbrev? It doesn't save any characters and I couldn't immediately see the benefit. If we do need it, can we add a docstring for the abbrev?
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/138#pullrequestreview-4448515669) — oliver-butterley (2026-06-08): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/138#discussion_r3372691003) — truonghoangle (2026-06-08; Spqr/Math/Poly/Basic/Defs.lean:40): I fixed it and remove it.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/138#pullrequestreview-4448870497) — truonghoangle (2026-06-08): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/138#pullrequestreview-4449262212) — oliver-butterley (2026-06-08): lgtm

### Item 139

**[Issue #139](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/139) — Specify and verify : \`spqr::encoding::polynomial::MAX\_INTERMEDIATE\_POLYNOMIAL\_DEGREE\_V1\` in \`polynomial.rs\`**

Status: closed. Opened: 2026-06-08. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 140

**[PR #140](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/140) — Specify and verify : \`spqr::encoding::polynomial::MAX\_INTERMEDIATE\_POLYNOMIAL\_DEGREE\_V1\` in \`polynomial.rs\`**

Status: merged. Opened: 2026-06-08. Author: truonghoangle.

Body excerpt: This PR specify and verify \`spqr::encoding::polynomial::MAX\_INTERMEDIATE\_POLYNOMIAL\_DEGREE\_V1\` in \`polynomial.rs\` closes #139

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/140#issuecomment-4649207081) — truonghoangle (2026-06-08): @Kukovec @oliver-butterley I don't understand the necessary rule I need to follow here, or what needs to be fixed in this case. https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/actions/runs/27137784920/job/80096018054?pr=140#step:5:429
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/140#issuecomment-4649874000) — oliver-butterley (2026-06-08): &gt; @Kukovec @oliver-butterley I don't understand the necessary rule I need to follow here, or what needs to be fixed in this case. https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/actions/runs/27137784920/job/80096018054?pr=140#step:5:429 Adding the simp attribute to the theorem: \`\`\`lean @\[simp\] theorem MAX\_INTERMEDIATE\_POLYNOMIAL\_DEGREE\_V1\_val : MAX\_INTERMEDIATE\_POLYNOMIAL\_DEGREE\_V1.val = …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/140#issuecomment-4650069567) — oliver-butterley (2026-06-08): Ah! I've understood it now, some of the linters do run on \`lake build\` but there are others which only run on \`lake exe runLinter\`. Running this locally we can catch other linting errors which we don't catch normally.
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/140#issuecomment-4650117762) — truonghoangle (2026-06-08): In that case, it would make more sense to include it as a requirement in the local execution process before creating the PR. I had assumed the error occurred during the \`lake build\` step.
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/140#issuecomment-4650194371) — oliver-butterley (2026-06-08): &gt; In that case, it would make more sense to include it as a requirement in the local execution process before creating the PR. I had assumed the error occurred during the \`lake build\` step. Additionally it would help a lot if the output of the CI clearly communicates the problem when a failure happens. It's terribly annoying for something to not work but few clues to explain it.
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/140#issuecomment-4650206743) — oliver-butterley (2026-06-08): Concerning the real content of this PR, wouldn't it be reasonable to remove the first two theorems (\`MAX\_INTERMEDIATE\_POLYNOMIAL\_DEGREE\_V1\_eq\` and \`MAX\_INTERMEDIATE\_POLYNOMIAL\_DEGREE\_V1\_val\`) and instead have just the main spec theorem proven by \` simp \[MAX\_INTERMEDIATE\_POLYNOMIAL\_DEGREE\_V1\]\`? I checked and this works fine.
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/140#issuecomment-4650248698) — truonghoangle (2026-06-08): For future applications, using \`simp\` is easier than using our specialization theorem (\`step\`).
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/140#issuecomment-4650301732) — oliver-butterley (2026-06-08): &gt; For future applications, using \`simp\` is easier than using our specialization theorem (\`step\`). Ahhh!!! I now looked more closely. It seems to me this shouldn't be a spec theroem at all, it is rather artificial to make it a spec theorem by add \`ok\` before the name of the constant. Is this what you really wanted? Maybe you just want to keep the second theorem, \`MAX\_INTERMEDIATE\_POLYNOMIAL\_DEGREE\_V1\_val\`, and add …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/140#issuecomment-4650452180) — truonghoangle (2026-06-08): With constants, I actually only wanted the second theorem and added \`simp\`, without needing the specification theorem. However, this violates the rules for writing specification theorems with functions in general. Essentially, I have only written a specification function along with the necessary theorem for the applications, without changing the general rules - although the approach feels somewhat mechanical. What …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/140#issuecomment-4650617392) — oliver-butterley (2026-06-08): My inclination is to have a single theorem in this file. You could just have: \`\`\` @\[simp\] theorem MAX\_INTERMEDIATE\_POLYNOMIAL\_DEGREE\_V1\_val : MAX\_INTERMEDIATE\_POLYNOMIAL\_DEGREE\_V1.val = 36 := by simp \[MAX\_INTERMEDIATE\_POLYNOMIAL\_DEGREE\_V1\] \`\`\` That won't cause any errors and should be useful. Alternatively, have the single theorem: \`\`\` @\[simp\] theorem MAX\_INTERMEDIATE\_POLYNOMIAL\_DEGREE\_V1\_eq : …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/140#issuecomment-4650914225) — truonghoangle (2026-06-08): &gt; @\[simp\] &gt; theorem MAX\_INTERMEDIATE\_POLYNOMIAL\_DEGREE\_V1\_val : &gt; MAX\_INTERMEDIATE\_POLYNOMIAL\_DEGREE\_V1.val = 36 := by &gt; simp \[MAX\_INTERMEDIATE\_POLYNOMIAL\_DEGREE\_V1\] I have selected this theorem and named it MAX\_INTERMEDIATE\_POLYNOMIAL\_DEGREE\_V1\_spec. Is that okay?
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/140#pullrequestreview-4451265465) — oliver-butterley (2026-06-08): LGTM

### Item 141

**[Issue #141](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/141) — Specify and verify : \`spqr::encoding::polynomial::MAX\_STORED\_POLYNOMIAL\_DEGREE\_V1\` in \`polynomial.rs\`**

Status: closed. Opened: 2026-06-08. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 142

**[Issue #142](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/142) — Specify and verify : \`spqr::util::inz\` in \`util.rs\`**

Status: closed. Opened: 2026-06-08. Author: MarkusFerdinandDablander.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 143

**[Issue #143](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/143) — Understand the errors shown by \`lake exe runLinter\` and remove the causes**

Status: closed. Opened: 2026-06-08. Author: oliver-butterley.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 144

**[Issue #144](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/144) — Specìy and verify : \`spqr::encoding::polynomial::{impl core::clone::Clone for spqr::encoding::polynomial::Poly}::clone\` in \`polynomial.rs\`**

Status: closed. Opened: 2026-06-08. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 145

**[Issue #145](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/145) — Update Aeneas to version 39c6a720**

Status: closed. Opened: 2026-06-08. Author: oliver-butterley.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 146

**[PR #146](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/146) — Update Aeneas to version 39c6a720**

Status: merged. Opened: 2026-06-08. Author: oliver-butterley.

Body excerpt: Update Aeneas to version ac9f1bc5 closes #145

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/146#pullrequestreview-4455465972) — truonghoangle (2026-06-09): (No text.)

### Item 147

**[PR #147](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/147) — Specify and verify : \`spqr::encoding::polynomial::MAX\_STORED\_POLYNOMIAL\_DEGREE\_V1\` in \`polynomial.rs\`**

Status: merged. Opened: 2026-06-08. Author: truonghoangle.

Body excerpt: This PR specify and verify \`spqr::encoding::polynomial::MAX\_STORED\_POLYNOMIAL\_DEGREE\_V1\` in \`polynomial.rs\` closes #141

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/147#pullrequestreview-4453002324) — oliver-butterley (2026-06-08): (No text.)

### Item 148

**[PR #148](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/148) — Add core::option models**

Status: merged. Opened: 2026-06-08. Author: oliver-butterley.

Body excerpt: Convert the \`core::option\` axioms to defs with spec theorems. - \[x\] \`core.option.Option.as\_ref\` — identity (references are transparent in the model) - \[x\] \`core.option.Option.ok\_or\` — \`some v ↦ Ok v\`, \`none ↦ Err e\` - \[x\] \`core.option.Option.Insts.CoreCmpPartialEqOption.eq\` — structural; the \`some\`/\`some\` case delegates to the element \`PartialEq\` instance - \[ \] \`core.option.Option.Insts.CoreCloneClone.clone\` — …

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/148#pullrequestreview-4455461971) — truonghoangle (2026-06-09): (No text.)

### Item 149

**[PR #149](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/149) — Add core::result models**

Status: merged. Opened: 2026-06-08. Author: oliver-butterley.

Body excerpt: Convert the \`core::result\` axioms to defs with spec theorems. - \[x\] \`core.result.Result.ok\` — already a def (unchanged) - \[x\] \`core.result.Result.is\_ok\` — \`true\` on \`Ok\`, \`false\` on \`Err\` - \[x\] \`core.result.Result.unwrap\_or\` — \`Ok\` payload, or the default on \`Err\` - \[x\] \`core.result.Result.map\_err\` — \`Ok\` unchanged; \`Err\` applies the \`FnOnce\` closure (\`@\[simp\]\` unfolding lemmas on the constructors) - \[x\] …

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/149#pullrequestreview-4455476698) — truonghoangle (2026-06-09): (No text.)

### Item 150

**[PR #150](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/150) — Add core::ops::range models**

Status: merged. Opened: 2026-06-08. Author: oliver-butterley.

Body excerpt: Convert the \`core::ops::range\` axioms to defs with spec theorems. - \[x\] \`…RangeFull…SliceIndex…index\` — already a def; \*\*spec added\*\* (returns the whole slice) - \[x\] \`…RangeFull…SliceIndex…index\_mut\` — whole-slice mutable borrow, identity write-back - \[x\] \`…RangeFull…SliceIndex…get\` — always \`some s\` (whole slice is in bounds) - \[x\] \`…RangeFull…SliceIndex…get\_mut\` — \`some s\` + write-back installing the new slice - …

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/150#pullrequestreview-4455483302) — truonghoangle (2026-06-09): (No text.)

### Item 151

**[PR #151](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/151) — Add alloc::vec mutation models**

Status: merged. Opened: 2026-06-08. Author: oliver-butterley.

Body excerpt: Convert the remaining \`alloc::vec\` axioms to defs with spec theorems. - \[x\] \`alloc.vec.Vec.is\_empty\` — underlying list is empty - \[x\] \`alloc.vec.Vec.as\_slice\` — slice view sharing the elements - \[x\] \`alloc.vec.Vec.clear\` — empties the vector - \[x\] \`alloc.vec.Vec.truncate\` — keeps the first \`n\` elements (\`List.take\`) - \[x\] \`alloc.vec.Vec.remove\` — removes/returns element at index, shifts the rest (fails when out of …

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/151#pullrequestreview-4457345769) — truonghoangle (2026-06-09): (No text.)

### Item 152

**[PR #152](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/152) — Add core::slice / alloc::slice / core::array models**

Status: merged. Opened: 2026-06-08. Author: oliver-butterley.

Body excerpt: Convert the slice/array axioms to defs with spec theorems. - \[x\] \`core.slice.Slice.clone\_from\_slice\` — already a def; \*\*spec added\*\* (copies the source when the element \`Clone\` acts as identity) - \[x\] \`Slice.Insts.CoreCmpOrd.cmp\` — lexicographic comparison, via the \`Slice.lexCmpAux\` list helper (delegates per element to the \`Ord\` instance) - \[x\] \`Slice.Insts.CoreCmpPartialEqArray.eq\` — element-wise slice-vs-array …

Discussion and review record:

- [review DISMISSED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/152#pullrequestreview-4457218692) — truonghoangle (2026-06-09): (No text.)
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/152#pullrequestreview-4458721321) — oliver-butterley (2026-06-09): I added one more def which was now possible since #115 was closed.
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/152#pullrequestreview-4458818049) — truonghoangle (2026-06-09): (No text.)

### Item 153

**[Issue #153](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/153) — \`clone\_from\_slice\` model does not capture the length-mismatch panic**

Status: closed. Opened: 2026-06-08. Author: oliver-butterley.

Body excerpt: The Lean model of \`::clone\_from\_slice\` in \`Spqr/Code/FunsExternal.lean\` is an over-approximation: it always succeeds, whereas the real Rust function \*\*panics\*\* when the destination and source slices have different lengths. \`::clone\_from\_slice(&amp;mut self, src: &amp;\[T\])\` where \`T: Clone\`: - \*\*Panics\*\* if \`self.len() != src.len()\` ("This function will panic if the two slices have different lengths"). - Otherwise clones …

No recorded comments or reviews.

### Item 154

**[PR #154](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/154) — Lean model for \`core::borrow\`, \`core::convert\`, \`core::iter::range\`: small utilities**

Status: merged. Opened: 2026-06-09. Author: Zhang-Liao.

Body excerpt: closes #116

Discussion and review record:

- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/154#discussion_r3380757085) — oliver-butterley (2026-06-09; Spqr/Code/TypesExternal.lean:28): Are you sure about this? This isn't an identifier that Aeneas is expecting. Although, I know this is a draft PR so feel free to ignore this, just mentioning in cases it is useful.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/154#pullrequestreview-4458742559) — oliver-butterley (2026-06-09): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/154#discussion_r3395763532) — Zhang-Liao (2026-06-11; Spqr/Code/TypesExternal.lean:28): @oliver-butterley After more consideration, I feel that the original definition of TryFromIntError seems to be wrong. I think it should be an inductive definition instead of a theorem. A type of error should at least have an instance, such as errors defined in \`Types.lean\`. If we do not have such an inductive type definition for \`TryFromIntError\`, it would be impossible to define try\_from.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/154#pullrequestreview-4476577496) — Zhang-Liao (2026-06-11): (No text.)
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/154#issuecomment-4700307288) — oliver-butterley (2026-06-14): I would suggest the following definition for the type: \`\`\`lean4 /-- \[core::num::error::TryFromIntError\] Source: '/rustc/library/core/src/num/error.rs', lines 10:0-10:26 Name pattern: \[core::num::error::TryFromIntError\] Rust docs: https://doc.rust-lang.org/std/num/struct.TryFromIntError.html In Rust \`TryFromIntError\` is the error type returned when a checked integral type conversion fails. Modeled as a fieldless …
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/154#discussion_r3420916154) — oliver-butterley (2026-06-16; SrcTranslated/TypesExternal.lean:21): \`\`\`suggestion \`\`\` Remove the commented out axiom now it's a real definition
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/154#pullrequestreview-4506598456) — oliver-butterley (2026-06-16): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/154#discussion_r3421609628) — truonghoangle (2026-06-16; SrcTranslated/FunsExternal.lean:255): Why did you write the specification for only step 1?
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/154#pullrequestreview-4507444357) — truonghoangle (2026-06-16): (No text.)
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/154#issuecomment-4720405735) — truonghoangle (2026-06-16): The definitions correspond to the Rust code. I suggest writing the definitions below using a match style whenever there are options, rather than using an implicit ok form. This would make the blocking conditions much clearer. The specification theorems should also be written in this explicit style so that all conditions and their applicability are transparent and easy to reason about. Example: \`\`\` @\[step\] theorem …
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/154#discussion_r3425035700) — Zhang-Liao (2026-06-17; SrcTranslated/FunsExternal.lean:255): I choose step one since previous specification theorems uses step one to confirm the correctness of the function defintion. I use the same convention.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/154#pullrequestreview-4511561796) — Zhang-Liao (2026-06-17): (No text.)
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/154#issuecomment-4726907188) — Zhang-Liao (2026-06-17): @truonghoangle The issue mentioned by you has be resolved. I use \`| none =&gt; False\` instead of \`| none =&gt; ¬ (diff ≤ Usize.max) ∧ pair.1.val = Usize.max\` since this branch never occurs in the program running. The reason is explained in the annotations \`\`\` The \`none\` branch is \`False\`: since \`i32\` is no wider than \`usize\`, \`diff = end\_.val - start.val\` always fits in \`usize\`, so \`UScalar.tryMkOpt\` always returns \`some\` …
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/154#pullrequestreview-4513129482) — truonghoangle (2026-06-17): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/154#discussion_r3427696824) — oliver-butterley (2026-06-17; SrcTranslated/FunsExternal.lean:255): Nice observation, both of you! At first glance I would say the spec should be for \`n\`, not just for \`1\`. Does anyone have some insight on what is useful where the spec is used? Perhaps we need to update both of these spec theorems.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/154#pullrequestreview-4515025989) — oliver-butterley (2026-06-17): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/154#discussion_r3428067666) — truonghoangle (2026-06-17; SrcTranslated/FunsExternal.lean:255): I don't have an answer regarding this specification, but for the specification of the theorem @Zhang-Liao mentioned, using \`1\` is fine because it is used for induction across loop steps (though, of course, using \`n\` would be better).
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/154#pullrequestreview-4515485056) — truonghoangle (2026-06-17): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/154#discussion_r3432548549) — Zhang-Liao (2026-06-18; SrcTranslated/FunsExternal.lean:255): Currently, the only consumption of such specifications is in RangeIteratorNext. It only uses step \`1\`. However, our codebase also has Rust code with steps other than \`1\`. step\_by(Self::KEY\_SIZE) and step\_by(2) also exist in our project. In this case, step \`1\` might be insufficient. Hence, I propose to change all such specifications to use step \`n\` and open an issue about it.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/154#pullrequestreview-4520973854) — Zhang-Liao (2026-06-18): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/154#discussion_r3433695842) — oliver-butterley (2026-06-18; SrcTranslated/FunsExternal.lean:255): Great, that's very useful info. @Zhang-Liao could you open an issue listing the spec theorems that need updating so we don't forget?
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/154#pullrequestreview-4522322735) — oliver-butterley (2026-06-18): (No text.)

### Item 155

**[PR #155](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/155) — Specify and verify : \`spqr::util::inz\` in \`util.rs\`**

Status: merged. Opened: 2026-06-09. Author: MarkusFerdinandDablander.

Body excerpt: Closes #142

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/155#pullrequestreview-4457485459) — oliver-butterley (2026-06-09): LGTM nice use of bv\_tac!

### Item 156

**[PR #156](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/156) — Specify and verify : \`spqr::encoding::polynomial::Poly::lagrange\_interpolate\_complete\` in \`polynomial.rs\`**

Status: merged. Opened: 2026-06-09. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`Poly::lagrange\_interpolate\_complete\`. As this is the first Lagrange-interpolation function verified, the PR also lands the polynomial math foundation (\`Spqr/Math/Poly/\`, \`Spqr/Math/List.lean\`) and generic Aeneas iterator/formatter specs (\`Spqr/Specs/Aeneas/\`). In fact, one axiom is removed: \`SharedASlice.…into\_iter\` in \`Spqr/Code/FunsExternal.lean\` is replaced with a concrete \`def\` …

Discussion and review record:

- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/156#pullrequestreview-4466265307) — oliver-butterley (2026-06-10): As always, it's rather hard to look at the content of a PR when it does many things all together. It appears this PR does the following things: - Polynomial math library (Spqr/Math/Poly/\*\*, Spqr/Math/List.lean): definitions + lemmas for Horner evaluation/accumulation, the Lagrange denominator product and scale factor, linear-factor products, Lagrange basis/interpolant, expected-trailing-coefficient reasoning, and …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/156#issuecomment-4668609120) — truonghoangle (2026-06-10): &gt; What you summarized here is accurate. Sorry for not summarizing everything; I will attach the detailed report for the major PRs later. Great! Could you edit the description of this PR and add these details? That would be very useful because it keeps track of everything for later. &gt; I want to know if the current classifications are appropriate? I'm sorry, I didn't understand the question. Which classifications?
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/156#issuecomment-4668729088) — truonghoangle (2026-06-10): The new PR description is great! That really helps to understand everything that is happening. &gt; I'm sorry, I didn't understand the question. Which classifications? Just like with the earlier restructuring of the \`gf.lean\` file, we have appropriately categorized the knowledge into separate files. I would like to ask whether this categorization is reasonable. Ah, I see what you mean. It looks reasonable to me. …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/156#issuecomment-4670369468) — oliver-butterley (2026-06-10): The namespacing in Spqr/Math/List.lean is strange. Aren't these generic List lemmas? Do you really want them in the spqr namespace?
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/156#issuecomment-4670975961) — truonghoangle (2026-06-10): I removed the namespace in Spqr/Math/List.lean
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/156#pullrequestreview-4468678010) — oliver-butterley (2026-06-10): (No text.)

### Item 157

**[Issue #157](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/157) — Verify : \`util.rs\`**

Status: closed. Opened: 2026-06-09. Author: MarkusFerdinandDablander.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 158

**[Issue #158](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/158) — Specify and verify : \`spqr::util::is\_non\_zero\` in \`util.rs\`**

Status: closed. Opened: 2026-06-09. Author: MarkusFerdinandDablander.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 159

**[Issue #159](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/159) — Specify and verify : \`spqr::util::compare\` in \`util.rs\`**

Status: closed. Opened: 2026-06-09. Author: MarkusFerdinandDablander.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 160

**[Issue #160](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/160) — Verify : \`encoding.rs\`**

Status: closed. Opened: 2026-06-10. Author: Zhang-Liao.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 161

**[Issue #161](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/161) — Specify and verify : \`spqr::encoding::{impl core::convert::From for spqr::encoding::EncodingError}::from\` in \`encoding.rs\`**

Status: closed. Opened: 2026-06-10. Author: Zhang-Liao.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 162

**[Issue #162](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/162) — Specify and verify : \`spqr::encoding::{impl spqr::encoding::Encoder for core::option::Option}::encode\_bytes\` in \`encoding.rs\`**

Status: closed. Opened: 2026-06-10. Author: Zhang-Liao.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 163

**[Issue #163](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/163) — Specify and verify : \`spqr::encoding::{impl spqr::encoding::Encoder for core::option::Option}::next\_chunk\` in \`encoding.rs\`**

Status: closed. Opened: 2026-06-10. Author: Zhang-Liao.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 164

**[Issue #164](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/164) — Specify and verify : \`spqr::encoding::{impl spqr::encoding::Decoder for core::option::Option}::new\` in \`encoding.rs\`**

Status: closed. Opened: 2026-06-10. Author: Zhang-Liao.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 165

**[Issue #165](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/165) — Specify and verify : \`spqr::encoding::{impl spqr::encoding::Decoder for core::option::Option}::add\_chunk\` in \`encoding.rs\`**

Status: closed. Opened: 2026-06-10. Author: Zhang-Liao.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 166

**[Issue #166](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/166) — Specify and verify : \`spqr::encoding::{impl spqr::encoding::Decoder for core::option::Option}::decoded\_message\` in \`encoding.rs\`**

Status: closed. Opened: 2026-06-10. Author: Zhang-Liao.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 167

**[PR #167](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/167) — Specify and verify : \`spqr::util::is\_non\_zero\` in \`util.rs\`**

Status: merged. Opened: 2026-06-10. Author: MarkusFerdinandDablander.

Body excerpt: This PR specifies and verifies \`spqr::util::is\_non\_zero\` in \`util.rs\`. Verifying this spec theorem requires a usable model of\`core::hint::black\_box\`, which was previously declared as an axiom. This PR therefore also replaces the \`core.hint.black\_box\` axiom in \`FunsExternal.lean\` with an appropriate definition and an associated spec theorem. Closes #158

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/167#pullrequestreview-4466282348) — oliver-butterley (2026-06-10): LGTM

### Item 168

**[Issue #168](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/168) — Verify : \`incremental\_mlkem768.rs\`**

Status: closed. Opened: 2026-06-10. Author: Zhang-Liao.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 169

**[Issue #169](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/169) — Specify and verify : \`spqr::incremental\_mlkem768::ek\_matches\_header\` in \`incremental\_mlkem768.rs\`**

Status: closed. Opened: 2026-06-10. Author: Zhang-Liao.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 170

**[Issue #170](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/170) — Specify and verify : \`spqr::incremental\_mlkem768::generate\` in \`incremental\_mlkem768.rs\`**

Status: closed. Opened: 2026-06-10. Author: Zhang-Liao.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 171

**[Issue #171](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/171) — Specify and verify : \`spqr::incremental\_mlkem768::encaps1\` in \`incremental\_mlkem768.rs\`**

Status: closed. Opened: 2026-06-10. Author: Zhang-Liao.

Body excerpt: (No text.)

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/171#issuecomment-6025439636) — a-dangelo (2026-10-06): @Zhang-Liao do you mind if I try this one out since you asked for help from the protocol team? I self assigned the issue to me and I will try to open a draft PR soon
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/171#issuecomment-6029796509) — Zhang-Liao (2026-10-07): @a-dangelo As far as I know, @truonghoangle has started to work on it. Maybe we should leave it to Truong to reduce duplication of work. Moreover, @sergiubur mentioned that proving the properties of \`incremental\_mlkem768.rs\` seem to belong to the realm of functional correctness.
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/171#issuecomment-6031736081) — truonghoangle (2026-10-07): @a-dangelo @Zhang-Liao This is the branch where I am working on this issue: https://github.com/truonghoangle/SparsePostQuantumRatchet/tree/mlkem768 The plan I am implementing is as follows: https://github.com/truonghoangle/SparsePostQuantumRatchet/blob/mlkem768/doc/plan.md If you have the time, please let me know whether I should proceed with the implementation or if any adjustments are needed.
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/171#issuecomment-6032628004) — a-dangelo (2026-10-07): @truonghoangle the plan is very comprehensive. I can tell you what we did on the protocols side: we decided that since mlkem is imported externally from libcrux, and hence opaqued by aeneas, we can treat it as a black box. In the future it would be nice to prove it correct e2e (from FC up to the protocol/model level), but it's a second tier priority for us: we decided to treat MLKEM as correct and secure as a …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/171#issuecomment-6032830560) — truonghoangle (2026-10-07): @a-dangelo The completion timeline depends more on the review process than the verification process (I have already verified over half of the procedure). However, I haven't submitted any PRs yet because, once the plan is finalized and agreed upon, I will need to break the work down into smaller PRs to facilitate easier review. Regarding \`opaqued\`: verifying the efficiency of the computational capabilities is …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/171#issuecomment-6033194129) — sergiubur (2026-10-07): - something similar was done by SymCrypt, no ? Maybe we could reuse much of their specs to avoid redoing stuff. - also, this is indeed part of an external crate, not sure it is currently under the scope of the signal shot, but it is interesting in general.
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/171#issuecomment-6033218548) — sergiubur (2026-10-07): more specifically described in this paper recently circulated on our slack https://arxiv.org/pdf/2609.15648
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/171#issuecomment-6033470921) — a-dangelo (2026-10-07): for FC there's also this: https://github.com/apple/corecrypto/blob/main/corecrypto\_verify/technical\_overview/formal-verification-for-apple-corecrypto.md for the NTT verification in Rocq there's this paper from Alix as well: https://cic.iacr.org/p/2/4/1/pdf

### Item 172

**[Issue #172](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/172) — Specify and verify : \`spqr::incremental\_mlkem768::encaps2\` in \`incremental\_mlkem768.rs\`**

Status: closed. Opened: 2026-06-10. Author: Zhang-Liao.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 173

**[Issue #173](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/173) — Specify and verify : \`spqr::incremental\_mlkem768::potentially\_fix\_state\_incorrectly\_encoded\_by\_libcrux\_issue\_1275\` in \`incremental\_mlkem768.rs\`**

Status: closed. Opened: 2026-06-10. Author: Zhang-Liao.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 174

**[Issue #174](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/174) — Specify and verify : \`spqr::incremental\_mlkem768::flip\_endianness\_of\_encapsulation\_state\` in \`incremental\_mlkem768.rs\`**

Status: closed. Opened: 2026-06-10. Author: Zhang-Liao.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 175

**[Issue #175](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/175) — Specify and verify : \`spqr::incremental\_mlkem768::decaps\` in \`incremental\_mlkem768.rs\`**

Status: closed. Opened: 2026-06-10. Author: Zhang-Liao.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 176

**[Issue #176](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/176) — Specify and verify : \`spqr::encoding::polynomial::CHUNK\_SIZE\` in \`polynomial.rs\`**

Status: closed. Opened: 2026-06-10. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 177

**[Issue #177](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/177) — Specify and verify : \`spqr::encoding::polynomial::NUM\_POLYS\` in \`polynomial.rs\`**

Status: closed. Opened: 2026-06-10. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 178

**[Issue #178](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/178) — Specify and verify : \`spqr::encoding::polynomial::PolyConst::ZEROS\` in \`polynomial.rs\`**

Status: closed. Opened: 2026-06-10. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 179

**[PR #179](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/179) — Specify and verify : s\`pqr::encoding::polynomial::CHUNK\_SIZE\` in \`polynomial.rs\`**

Status: merged. Opened: 2026-06-10. Author: truonghoangle.

Body excerpt: This PR specify and verify \`spqr::encoding::polynomial::CHUNK\_SIZE\` in \`polynomial.rs\` closes #176

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/179#pullrequestreview-4474247765) — oliver-butterley (2026-06-11): LGTM

### Item 180

**[Issue #180](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/180) — Add a Linter for identation**

Status: closed. Opened: 2026-06-11. Author: Zhang-Liao.

Body excerpt: Import the Linter from dalek-lean. It is helpful for the new project's development.

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/180#issuecomment-4739410910) — Zhang-Liao (2026-06-18): Closed by #203

### Item 181

**[Issue #181](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/181) — Make the Aeneas extracted code a separate lean\_lib**

Status: closed. Opened: 2026-06-11. Author: oliver-butterley.

Body excerpt: This improves the separation of pieces of Lean code which are logically very different. Also convenient so that the linter can be targeted correctly.

No recorded comments or reviews.

### Item 182

**[PR #182](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/182) — Specify and verify : \`spqr::encoding::polynomial::NUM\_POLYS\` in \`polynomial.rs\`**

Status: merged. Opened: 2026-06-11. Author: truonghoangle.

Body excerpt: This PR specify and verify \`spqr::encoding::polynomial::NUM\_POLYS\` in \`polynomial.rs\` closes #177

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/182#pullrequestreview-4474535089) — oliver-butterley (2026-06-11): LGTM

### Item 183

**[PR #183](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/183) — Correct the model for clone\_from\_slice**

Status: merged. Opened: 2026-06-11. Author: oliver-butterley.

Body excerpt: This PR adjusts the model for clone\_from\_slice to correctly describe how it panics if the destination and source don't have equal length. The associated spec theorems are also adjusted. However the previous usage of these spec theroems is not affected. fixes #153

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/183#pullrequestreview-4474762117) — Kukovec (2026-06-11): LGTM

### Item 184

**[PR #184](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/184) — Specify and verify : \`spqr::encoding::polynomial::PolyConst::ZEROS\` in \`polynomial.rs\`**

Status: merged. Opened: 2026-06-11. Author: truonghoangle.

Body excerpt: This PR specify and verify \`spqr::encoding::polynomial::PolyConst::ZEROS\` in \`polynomial.rs\` closes #178

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/184#pullrequestreview-4475585598) — oliver-butterley (2026-06-11): LGTM I see that you chose not to name any of the theroems as \`ZEROS\_spec\`. I think this makes sense in this case. I interpret our system that the \`\_spec\` convention is just for the functions that really have a spec theorem.
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/184#issuecomment-4679302238) — truonghoangle (2026-06-11): I am currently following our discussion guidelines regarding constant functions: no \`\_spec\` is written if \`ok\` is used.

### Item 185

**[PR #185](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/185) — Make the Aeneas extracted code a separate lean\_lib**

Status: merged. Opened: 2026-06-11. Author: oliver-butterley.

Body excerpt: This PR moves the Lean code produced by Aeneas to a separate folder which is its own lean\_lib. This gives good logical separation between the logically separate parts of the lean code. In particular it means that lake exe runLinter only runs the linter of the Lean code we added, not on the Lean code produced by Aeneas. Note: changes many files, but the majority are just to update the \`import SrcTranslated.Funs\`. …

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/185#pullrequestreview-4476135446) — truonghoangle (2026-06-11): (No text.)

### Item 186

**[PR #186](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/186) — Specify and verify \`spqr::encoding::polynomial::Poly::mult\_xdiff\_assign\_trailing\` in \`polynomial.rs\`**

Status: merged. Opened: 2026-06-11. Author: truonghoangle.

Body excerpt: This PR specify and verify \`spqr::encoding::polynomial::Poly::mult\_xdiff\_assign\_trailing\` in \`polynomial.rs\` closes #128

Discussion and review record:

- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/186#pullrequestreview-4485459164) — oliver-butterley (2026-06-12): ## mult\_xdiff\_poly\_identity The theorem \`mult\_xdiff\_poly\_identity\` looks useful but the file location &amp; name (\`Spqr/Math/Poly/Aeneas/MultXdiff.lean\`) are misleading. This theorem references \*\*nothing\*\* from the extraction, the statement and proof are purely about \`listToGF216Poly\` and \`GF16.toGF216\`. Rename and relocate! Next to \`listToGF216Poly\_coeff\` in \`Spqr/Math/Poly/Coeff/\` (where \`listToGF216Poly\` and its …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/186#issuecomment-4691352752) — truonghoangle (2026-06-12): @oliver-butterley Thank you for your suggestions. I have fixed it according to your suggestions.
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/186#pullrequestreview-4488072432) — oliver-butterley (2026-06-12): (No text.)

### Item 187

**[PR #187](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/187) — Specify and verify : \`spqr::util::compare\` in \`util.rs\`**

Status: merged. Opened: 2026-06-11. Author: MarkusFerdinandDablander.

Body excerpt: This PR specifies and verifies \`spqr::util::compare\` in \`util.rs\` by proving an appropriately formulated main theorem \`compare\_spec\` via an associated loop invariant helper theorem \`compare\_loop\_spec\`. Closes #157 Closes #159 \*\*Note:\*\* This PR also drops four \`SrcTranslated.\*\` imports from Spqr.lean (potentially left over from #185 ?). Running \`lake exe mk\_all\` removed them automatically.

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/187#pullrequestreview-4477622178) — Kukovec (2026-06-11): (No text.)

### Item 188

**[Issue #188](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/188) — Specify and verify : \`spqr::authenticator::Authenticator::MACSIZE\` in \`authenticator.rs\`**

Status: closed. Opened: 2026-06-11. Author: MarkusFerdinandDablander.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 189

**[Issue #189](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/189) — Specify and verify : \`spqr::authenticator::Authenticator::mac\_ct\` in \`authenticator.rs\`**

Status: closed. Opened: 2026-06-11. Author: MarkusFerdinandDablander.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 190

**[Issue #190](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/190) — Specify and verify : \`spqr::authenticator::Authenticator::mac\_hdr\` in \`authenticator.rs\`**

Status: closed. Opened: 2026-06-11. Author: MarkusFerdinandDablander.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 191

**[Issue #191](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/191) — Specify and verify : \`spqr::authenticator::Authenticator::update\` in \`authenticator.rs\`**

Status: closed. Opened: 2026-06-11. Author: MarkusFerdinandDablander.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 192

**[Issue #192](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/192) — Specify and verify : \`spqr::authenticator::Authenticator::verify\_ct\` in \`authenticator.rs\`**

Status: closed. Opened: 2026-06-11. Author: MarkusFerdinandDablander.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 193

**[Issue #193](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/193) — Specify and verify : \`spqr::authenticator::Authenticator::verify\_hdr\` in \`authenticator.rs\`**

Status: closed. Opened: 2026-06-11. Author: MarkusFerdinandDablander.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 194

**[Issue #194](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/194) — Verify : \`authenticator/serialize.rs\`**

Status: closed. Opened: 2026-06-11. Author: MarkusFerdinandDablander.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 195

**[Issue #195](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/195) — Specify and verify : \`spqr::authenticator::Authenticator::into\_pb\` in \`authenticator/serialize.rs\`**

Status: closed. Opened: 2026-06-11. Author: MarkusFerdinandDablander.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 196

**[Issue #196](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/196) — Specify and verify : \`spqr::authenticator::Authenticator::from\_pb\` in \`authenticator/serialize.rs\`**

Status: closed. Opened: 2026-06-11. Author: MarkusFerdinandDablander.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 197

**[PR #197](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/197) — Add status tracking utilities**

Status: merged. Opened: 2026-06-11. Author: oliver-butterley.

Body excerpt: This PR: - Activates the new Aeneas feature to emit translation.json which describes the connection between the Lean code and the Rust source. - Adds the utility \`lake exe status\` which reports, per function, whether it has a Lean spec, which axioms that spec uses, and its verification status. The large diff in this PR is mostly due to committing the auto generated file: translation.json (which is controlled by the …

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/197#issuecomment-4689114512) — oliver-butterley (2026-06-12): A possible improvement would be to add a step in the procedure which produces the full list of functions in the Rust code, this current setup works only with the data from Charon/Aeneas so it is self-consistent but limited by the current extraction coverage of Charon/Aeneas.
- [review DISMISSED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/197#pullrequestreview-4496126057) — Kukovec (2026-06-15): (No text.)
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/197#issuecomment-4768126326) — oliver-butterley (2026-06-22): Since this feature recently landed in Aeneas, I'm going to update this PR to incorporate it.
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/197#issuecomment-4801943610) — oliver-butterley (2026-06-25): I updated this to use the latest upstream version of Aeneas which produces the \`translation.json\` file alongside the Lean files. This is now the official Aeneas way of tracking the connection between Lean code and source rust code. The PR looks big because this is now added and it contains full info, not only concerning the functions but also types and traits.
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/197#issuecomment-4831125248) — oliver-butterley (2026-06-29): Remaining to do: follow the suggestion here to make sure the paths in the json are machine independent.
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/197#pullrequestreview-4636174093) — Kukovec (2026-07-06): (No text.)

### Item 198

**[PR #198](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/198) — Specify and verify : \`spqr::authenticator::Authenticator::MACSIZE\` in \`authenticator.rs\`**

Status: merged. Opened: 2026-06-12. Author: MarkusFerdinandDablander.

Body excerpt: Closes #188

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/198#pullrequestreview-4491242284) — truonghoangle (2026-06-13): (No text.)

### Item 199

**[Issue #199](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/199) — axiom : core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0\_Item.next**

Status: closed. Opened: 2026-06-12. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 200

**[PR #200](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/200) — Specify and verify : spqr::encoding::polynomial::Poly::add\_assign in polynomial.rs**

Status: merged. Opened: 2026-06-13. Author: truonghoangle.

Body excerpt: This PR formally verifies \`spqr::encoding::polynomial::Poly::add\_assign\`, proving that the Rust implementation correctly computes polynomial addition in GF(2¹⁶)\[X\]. \`Poly::add\_assign\` iterates over \`other\`’s coefficients (\`deref → iter → enumerate\`), performing coefficient-wise \`+=\` (XOR in characteristic 2) for in-range indices and extending \`self\` with \`push\` otherwise. The verification has three layers: 0. …

Discussion and review record:

- [review CHANGES_REQUESTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/200#pullrequestreview-4492196282) — oliver-butterley (2026-06-14): Nice work, the final theorem looks good. However I have various comments about multiple other details. ## Def of \`.next\` Can you check the definition for \`core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0\_Item.next\`? Rust docs for the function: https://doc.rust-lang.org/std/iter/struct.Enumerate.html#method.next It seems to me that this Lean model defined in this PR isn't …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/200#issuecomment-4701214766) — truonghoangle (2026-06-14): Thank you for your comments. My initial intention was to use UScalar.wrapping\_add so that the bounded condition wasn't needed (it would be automatically checked), but later I still needed the bounded condition. Currently, I've simplified the definition to eliminate UScalar.wrapping\_add. I've removed the spec theorem and removed \`private\` for lemmas that I think I'll use again in the future.
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/200#pullrequestreview-4492729131) — oliver-butterley (2026-06-14): (No text.)

### Item 201

**[PR #201](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/201) — build(lean): add SrcTranslated to defaultTargets**

Status: merged. Opened: 2026-06-13. Author: astefano.

Body excerpt: Closes #202 This PR adds "SrcTranslated" to defaultTargets. This enables \`probe-lean extract\` to generate deps for srcTranslated as well.

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/201#issuecomment-4699958398) — oliver-butterley (2026-06-13): I don't love this, it means that \`lake exe runLinter\` will also run the linter on \`SrcTranslated\`, not only on the \`Spqr\` lean lib. The correct linting job is then \`lake exe runLinter Spqr\` and people working in the repo will need to know this. On the other hand \`SrcTranslated\` isn't required in \`defaultTargets\` because \`lake build\` will build \`Spqr\` and also build \`SrcTranslated\` as one of its dependencies. Is …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/201#issuecomment-4700035719) — oliver-butterley (2026-06-13): On the other hand, there is a reasonable argument to add SrcTranslated to the defaultTargets: Before any of the specs written in Spqr use anything from SrcTranslated, this lean lib won't get built by lake build whereas lake build should check everything. So, add to defaultTargets as you propose but also add a note to the appropriate document in the repo to explain to those working in the repo that \`lake exe …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/201#issuecomment-4700970490) — astefano (2026-06-14): &gt; I don't love this, it means that \`lake exe runLinter\` will also run the linter on \`SrcTranslated\`, not only on the \`Spqr\` lean lib. The correct linting job is then \`lake exe runLinter Spqr\` and people working in the repo will need to know this. On the other hand \`SrcTranslated\` isn't required in \`defaultTargets\` because \`lake build\` will build \`Spqr\` and also build \`SrcTranslated\` as one of its dependencies. &gt; &gt; …
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/201#discussion_r3409340764) — oliver-butterley (2026-06-14; doc/WORKFLOW_AND_PR_GUIDE.md:24): This is very long text for something very simple, it doesn't deserve so much space in the docs. Just add something like: "To lint the Lean code, use \`lake exe runLinter Spqr\`." Please check the AI generated text and make it something sensible.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/201#pullrequestreview-4492736178) — oliver-butterley (2026-06-14): (No text.)
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/201#issuecomment-4701379440) — oliver-butterley (2026-06-14): &gt; probe-lean's job is to detect sorries in the dep graph; to do this, it needs to know what to build and for this, it looks at defaultTargets. My understanding is that spqr should cover/needs all that is generated by aeneas (otherwise why generate some lean code if it's not planned to be verified) so to me, in this particular case of aeneas projects, there is no difference between SrcTranslated being built as a dep …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/201#issuecomment-4701394974) — astefano (2026-06-14): &gt; &gt; probe-lean's job is to detect sorries in the dep graph; to do this, it needs to know what to build and for this, it looks at defaultTargets. My understanding is that spqr should cover/needs all that is generated by aeneas (otherwise why generate some lean code if it's not planned to be verified) so to me, in this particular case of aeneas projects, there is no difference between SrcTranslated being built as a …
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/201#discussion_r3409390063) — astefano (2026-06-14; doc/WORKFLOW_AND_PR_GUIDE.md:24): (it was long because it was providing context for what's the reason to run linter only on spqr -- which, i thought, it's good to have -- not because it was smth complicated; fine if you don't want that context in this repo, but i don't agree it wasn't smth sensible, i mean, to me, it's more a matter of taste.)
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/201#pullrequestreview-4492778211) — astefano (2026-06-14): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/201#pullrequestreview-4496658746) — oliver-butterley (2026-06-15): (No text.)

### Item 202

**[Issue #202](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/202) — SrcTranslated library is missing from defaultTargets, so tooling drops the Aeneas output**

Status: closed. Opened: 2026-06-13. Author: astefano.

Body excerpt: Since #185 moved the Aeneas-generated Lean code into its own \`SrcTranslated\` lean\_lib, \`lakefile.toml\` still has \`defaultTargets = \["Spqr"\]\`. Tooling that keys off \`defaultTargets\` to decide what to build/extract (\`probe-lean\`, and through it \`probe-aeneas\`) then only sees the handwritten \`Spqr\` library and \*\*silently drops the entire \`SrcTranslated\` library\*\*. \`probe-aeneas extract\` runs without error but produces …

No recorded comments or reviews.

### Item 203

**[PR #203](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/203) — Import spec-indent linter, fix it, and clean up warnings**

Status: merged. Opened: 2026-06-14. Author: Zhang-Liao.

Body excerpt: ## Summary Imports the spec-theorem indentation linter from dalek-lean, fixes a bug in it, and manually cleans up the warnings it surfaces. - \*\*Import linter\*\*: brings over \`Spqr/Lint/SpecIndent.lean\` (the \`linter.curve25519.specIndent\` linter that checks spec theorems follow the style-guide indentation), plus \`Spqr/Lint/Basic.lean\`, wiring (\`Spqr.lean\`, \`lakefile.toml\`) and tests …

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/203#issuecomment-4704168439) — Zhang-Liao (2026-06-15): I think this PR is ready for review now.
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/203#pullrequestreview-4496160540) — Kukovec (2026-06-15): (No text.)

### Item 204

**[Issue #204](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/204) — Rename spec-indent linter option from \`linter.curve25519.specIndent\` to a SPQR namespace**

Status: closed. Opened: 2026-06-14. Author: Zhang-Liao.

Body excerpt: Import the spec-theorem indentation linter from \`dalek-lean\` and fix the warnings discovered by the Linter.

No recorded comments or reviews.

### Item 205

**[PR #205](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/205) — Specify and verify : \`spqr::encoding::polynomial::Poly::mult\_assign\` in \`polynomial.rs\`**

Status: merged. Opened: 2026-06-14. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::encoding::polynomial::Poly::mult\_assign\` in \`polynomial.rs\` closes #132

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/205#pullrequestreview-4494903268) — Zhang-Liao (2026-06-15): (No text.)

### Item 206

**[PR #206](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/206) — Specify and verify : \`spqr::encoding::polynomial::Poly::serialize\` in \`polynomial.rs\`**

Status: merged. Opened: 2026-06-15. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::encoding::polynomial::Poly::serialize\` in \`polynomial.rs\` closes #136

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/206#pullrequestreview-4498297984) — oliver-butterley (2026-06-15): LGTM

### Item 207

**[PR #207](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/207) — Profiling documentation**

Status: merged. Opened: 2026-06-15. Author: Kukovec.

Body excerpt: Updates the PR template and docs with the new \`!radar\` command and adds a brief paragraph on it in \`doc/\`. closes #11

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/207#pullrequestreview-4496665038) — oliver-butterley (2026-06-15): LGTM

### Item 208

**[PR #208](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/208) — Specify and verify : \`spqr::encoding::polynomial::Poly::deserialize\` in \`polynomial.rs\`**

Status: merged. Opened: 2026-06-15. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::encoding::polynomial::Poly::deserialize\` in \`polynomial.rs\` closes #137

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/208#pullrequestreview-4506588079) — oliver-butterley (2026-06-16): LGTM

### Item 209

**[Issue #209](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/209) — Specify and verify: \`spqr::encoding::polynomial::PolyConst::lagrange\_interpolate\_pt\` in \`polynomial.rs\`**

Status: closed. Opened: 2026-06-15. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 210

**[Issue #210](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/210) — Specify and verify: \`spqr::encoding::polynomial::PolyConst::mult\` in \`polynomial.rs\`**

Status: closed. Opened: 2026-06-15. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 211

**[Issue #211](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/211) — Specify and verify: \`spqr::encoding::polynomial::PolyConst::mult\_xdiff\` in \`polynomial.rs\`**

Status: closed. Opened: 2026-06-15. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 212

**[Issue #212](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/212) — Specify and verify: \`spqr::encoding::polynomial::PolyConst::to\_poly\` in \`polynomial.rs\`**

Status: closed. Opened: 2026-06-15. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 213

**[Issue #213](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/213) — Specify and verify: \`spqr::encoding::polynomial::const\_polys\_to\_polys\` in \`polynomial.rs\`**

Status: closed. Opened: 2026-06-15. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 214

**[Issue #214](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/214) — Specify and verify: \`spqr::encoding::polynomial::lagrange\_polys\_for\_complete\_points\` in \`polynomial.rs\`**

Status: closed. Opened: 2026-06-15. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 215

**[Issue #215](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/215) — Specify and verify: \`spqr::encoding::polynomial::PolyEncoder::get\_encoder\_state\` in \`polynomial.rs\`**

Status: closed. Opened: 2026-06-15. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 216

**[Issue #216](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/216) — Specify and verify: \`spqr::encoding::polynomial::PolyEncoder::into\_pb\` in \`polynomial.rs\`**

Status: closed. Opened: 2026-06-15. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 217

**[Issue #217](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/217) — Specify and verify: \`spqr::encoding::polynomial::PolyEncoder::from\_pb\` in \`polynomial.rs\`**

Status: closed. Opened: 2026-06-15. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 218

**[Issue #218](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/218) — Specify and verify: \`spqr::encoding::polynomial::PolyEncoder::point\_at\` in \`polynomial.rs\`**

Status: closed. Opened: 2026-06-15. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 219

**[Issue #219](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/219) — Specify and verify: \`spqr::encoding::polynomial::PolyEncoder::encode\_bytes\_base\` in \`polynomial.rs\`**

Status: closed. Opened: 2026-06-15. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 220

**[Issue #220](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/220) — Specify and verify: \`spqr::encoding::polynomial::PolyEncoder::chunk\_at\` in \`polynomial.rs\`**

Status: closed. Opened: 2026-06-15. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 221

**[Issue #221](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/221) — Specify and verify: \`spqr::encoding::polynomial::PolyEncoder::into\_pb\_test\` in \`polynomial.rs\`**

Status: closed. Opened: 2026-06-15. Author: truonghoangle.

Body excerpt: (No text.)

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/221#issuecomment-5174830776) — truonghoangle (2026-08-04): The function into\_pb\_test is a test function, so we don't need to verify it.

### Item 222

**[PR #222](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/222) — Specify and verify : \`spqr::authenticator::Authenticator::into\_pb\` in \`authenticator/serialize.rs\`**

Status: merged. Opened: 2026-06-16. Author: MarkusFerdinandDablander.

Body excerpt: Closes #195

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/222#pullrequestreview-4506197988) — truonghoangle (2026-06-16): (No text.)

### Item 223

**[PR #223](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/223) — Specify and verify : \`spqr::authenticator::Authenticator::from\_pb\` in \`authenticator/serialize.rs\`**

Status: merged. Opened: 2026-06-16. Author: MarkusFerdinandDablander.

Body excerpt: Closes #194 Closes #196

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/223#pullrequestreview-4507900242) — oliver-butterley (2026-06-16): LGTM

### Item 224

**[PR #224](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/224) — Specify and verify : \`spqr::encoding::polynomial::Poly::compute\_at\` in \`polynomial.rs\`**

Status: merged. Opened: 2026-06-16. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::encoding::polynomial::Poly::compute\_at\` in \`polynomial.rs\` closes #133

Discussion and review record:

- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/224#discussion_r3427657501) — Zhang-Liao (2026-06-17; Spqr/Specs/Encoding/Polynomial/Poly/ComputeAt.lean:56): The namespace \`spqr.encoding.polynomial.Poly.compute\_at\_loop0\` is opened and closed twice in this file. I think it's better to only open once.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/224#pullrequestreview-4514978741) — Zhang-Liao (2026-06-17): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/224#discussion_r3427714566) — Zhang-Liao (2026-06-17; Spqr/Math/Poly/Eval/DotProduct.lean:42): The theorems \`zero\_toGF216\_eq\_empty\_sum\` and \`max\_two\_succ\_le\_usize\_max\` are not used in any other proof. Why do we need it?
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/224#pullrequestreview-4515048846) — Zhang-Liao (2026-06-17): (No text.)
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/224#issuecomment-4729544008) — Zhang-Liao (2026-06-17): I think is PR is almost ready for merge with minor comments.
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/224#discussion_r3428026248) — truonghoangle (2026-06-17; Spqr/Specs/Encoding/Polynomial/Poly/ComputeAt.lean:56): I fixed it!
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/224#pullrequestreview-4515433984) — truonghoangle (2026-06-17): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/224#discussion_r3428027158) — truonghoangle (2026-06-17; Spqr/Math/Poly/Eval/DotProduct.lean:42): I’ll be using this in future PRs, so I want to update it right within the PR itself to save myself from having to recall the details later.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/224#pullrequestreview-4515435185) — truonghoangle (2026-06-17): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/224#discussion_r3428041049) — Zhang-Liao (2026-06-17; Spqr/Specs/Encoding/Polynomial/Poly/ComputeAt.lean:56): The namespace \`spqr.encoding.polynomial.Poly.compute\_at\_loop1\` is also opened twice.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/224#pullrequestreview-4515451969) — Zhang-Liao (2026-06-17): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/224#discussion_r3428213975) — truonghoangle (2026-06-17; Spqr/Specs/Encoding/Polynomial/Poly/ComputeAt.lean:56): I fixed it!
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/224#pullrequestreview-4515668372) — truonghoangle (2026-06-17): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/224#pullrequestreview-4516792002) — Zhang-Liao (2026-06-17): (No text.)

### Item 225

**[Issue #225](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/225) — Specify: \`spqr::authenticator::Authenticator::mac\_ct\` in \`authenticator.rs\`**

Status: closed. Opened: 2026-06-17. Author: MarkusFerdinandDablander.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 226

**[Issue #226](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/226) — Extend / interpret axiom \`libcrux\_hmac.hmac\` in FunsExternal**

Status: closed. Opened: 2026-06-17. Author: MarkusFerdinandDablander.

Body excerpt: The axiom stub \`\`\`lean /-- \[libcrux\_hmac::hmac\]: Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/libcrux-hmac-0.0.6/src/hmac.rs', lines 51:0-51:90 Name pattern: \[libcrux\_hmac::hmac\] -/ @\[rust\_fun "libcrux\_hmac::hmac"\] axiom libcrux\_hmac.hmac : libcrux\_hmac.Algorithm → Slice Std.U8 → Slice Std.U8 → Option Std.Usize → Result (alloc.vec.Vec Std.U8) \`\`\` in FunsExternal.lean needs to somehow be interpreted …

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/226#issuecomment-4744466047) — MarkusFerdinandDablander (2026-06-18): @oliver-butterley @Kukovec @truonghoangle following our helpful discussion today, I spent some hours digging into this and the situation appears to be a little more convoluted than initially expected. ### Recap of the agreed plan In today's meeting, we agreed that I would: 1. Look up the externally verified F\* specs for \`libcrux\_hmac::hmac\` in cryspen/libcrux. 2. Translate those specs into Lean and add them as an …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/226#issuecomment-4789527661) — MarkusFerdinandDablander (2026-06-24): @oliver-butterley @Kukovec @truonghoangle @Zhang-Liao following the philosophy of minimalism I have invested some more work in an attempt to construct a suitable axiom in \`FunsExternal.lean\` to model \`libcrux\_hmac.hmac\`. My aims were to maximise for the following: (a) Enable a spec and proof of a reasonable version of \`mac\_ct\_spec\` (this will also unblock a variety of other spec theorems). (b) Keep the semantic …

### Item 227

**[PR #227](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/227) — Specify: \`spqr::authenticator::Authenticator::mac\_ct\` in \`authenticator.rs\`**

Status: closed unmerged. Opened: 2026-06-17. Author: MarkusFerdinandDablander.

Body excerpt: Closes #225 \*\*Note:\*\* While the content of this spec theorem appears correct and faithful to the realities of the underlying Rust in my estimation, the function in question (and thus its spec theorem proof) depends on an uninterpreted axiom stub in FunsExternal, namely on \`\`\`lean /-- \[libcrux\_hmac::hmac\]: Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/libcrux-hmac-0.0.6/src/hmac.rs', lines 51:0-51:90 …

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/227#issuecomment-4730215506) — truonghoangle (2026-06-17): @MarkusFerdinandDablander I think we need to establish a theoretical framework not just for this function, but for the other functions in this file as well. Once that framework is in place and we agree on what should be specified and how the relationships between components should be defined, we can write precise specifications for each function and for their interactions. As I understand it, the key task is to …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/227#issuecomment-4739626039) — github-actions[bot] (2026-06-18): ### Sorry Delta — hand-written specs \*\*2 new sorry-tainted declarations in \`Spqr.Specs.\*\`:\*\* | Module | Declaration | Kind | |--------|-------------|------| | \`Spqr.Specs.Authenticator.Authenticator.MacCt\` | \`spqr.authenticator.Authenticator.mac\_ct\_spec\` | direct | | \`Spqr.Specs.Authenticator.Authenticator.MacCt\` | \`spqr.authenticator.Authenticator.mac\_ct\_spec.mvcgen\_spec\` | transitive |

### Item 228

**[PR #228](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/228) — Lean model for \`Map\`**

Status: merged. Opened: 2026-06-17. Author: Kukovec.

Body excerpt: This PR: - Partially addresses #114. - Adds semantics for iteration over a \`.map\` produced iterator (as an \`Iterator -&gt; Iterator\` transformer) - Adds utility for generating an \`Iterator\` from a \`next\` function definition Per our conversation, the current Aeneas treatment of iterators does not seem to define semantics for iterators produced by map. This code aims to supplement that.

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/228#pullrequestreview-4522870048) — oliver-butterley (2026-06-18): It all looks reasonable to me. I suppose that the next work is to convert \`axiom core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.collect\` to a def and at that point we will see how all the components are used and connect together. I see the underlying Rust code in our repo which produces all of this is \`let pt\_vec: Vec = s.iter().enumerate().map(|(i, &amp;g)| …Pt…).collect();\` and only when that entire …

### Item 229

**[PR #229](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/229) — Specify and verify : \`spqr::encoding::polynomial::Poly::lagrange\_interpolate\_prepare\` in \`polynomial.rs\`**

Status: merged. Opened: 2026-06-17. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::encoding::polynomial::Poly::lagrange\_interpolate\_prepare\` in \`polynomial.rs\` closes #127

Discussion and review record:

- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/229#discussion_r3464248428) — Zhang-Liao (2026-06-24; Spqr/Specs/Encoding/Polynomial/Poly/LagrangeInterpolatePrepare.lean:258): Do we really indeed both \`result.coefficients\[pts.length\]! = ONE\` and \`(∀ (hoff : pts.length &lt; result.degree), (result.coefficients\[pts.length\]).toGF216 = 1)\` in premises? It seems that the latter can be derived from the first.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/229#pullrequestreview-4558688533) — Zhang-Liao (2026-06-24): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/229#discussion_r3464345473) — Zhang-Liao (2026-06-24; Spqr/Specs/Encoding/Polynomial/Poly/LagrangeInterpolatePrepare.lean:43): We do not need the \`Std\` prefix for \`Std.Usize\` here.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/229#pullrequestreview-4558800645) — Zhang-Liao (2026-06-24): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/229#discussion_r3464605031) — truonghoangle (2026-06-24; Spqr/Specs/Encoding/Polynomial/Poly/LagrangeInterpolatePrepare.lean:258): I removed the second intermediate result. In fact, to prove the first result, I needed to prove the second one due to the inductive nature of the loops, but I forgot to delete it when formulating the theorem.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/229#pullrequestreview-4559108044) — truonghoangle (2026-06-24): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/229#discussion_r3464606028) — truonghoangle (2026-06-24; Spqr/Specs/Encoding/Polynomial/Poly/LagrangeInterpolatePrepare.lean:43): I fixed it
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/229#pullrequestreview-4559109765) — truonghoangle (2026-06-24): (No text.)
- [review DISMISSED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/229#pullrequestreview-4559450351) — Zhang-Liao (2026-06-24): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/229#pullrequestreview-4562624657) — Zhang-Liao (2026-06-24): (No text.)

### Item 230

**[Issue #230](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/230) — Generalize step-1 \`Step\`/range-iterator spec theorems to arbitrary step \`n\`**

Status: closed. Opened: 2026-06-18. Author: Zhang-Liao.

Body excerpt: ## Summary Several \`Step\` / range-iterator spec theorems are stated \*\*only for step \`1\`\*\*, even though the underlying model functions take an arbitrary step count \`n\`. Our Rust code base uses \`step\_by(..)\` with steps other than \`1\`, so these specs might be insufficient to verify those loops and should be generalized to an arbitrary step \`n\`. This issue tracks the spec theorems that need updating (follow-up from the …

No recorded comments or reviews.

### Item 231

**[PR #231](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/231) — Generalize \`Step\` forward/backward\_checked specs to arbitrary step \`n\`**

Status: merged. Opened: 2026-06-18. Author: Zhang-Liao.

Body excerpt: ## Summary Generalizes the \`Step\` \`forward\_checked\` / \`backward\_checked\` spec theorems from step \`1\` to an arbitrary step \`n\`, as tracked in #230. The model \`def\`s in \`SrcTranslated/FunsExternal.lean\` already take an arbitrary count \`n : Usize\`, but the spec theorems only covered \`n = 1\`. Our Rust code base uses \`step\_by(..)\` with other steps (\`step\_by(2)\` in \`src/incremental\_mlkem768.rs:147\`, …

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/231#pullrequestreview-4524259089) — Kukovec (2026-06-18): (No text.)

### Item 232

**[Issue #232](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/232) — Lean model for alloc::collections::vec\_deque: VecDeque and its IntoIter (group B)**

Status: closed. Opened: 2026-06-18. Author: oliver-butterley.

Body excerpt: For each of the following functions from the standard library, convert the axiom to a def and add appropriate spec theorem(s). - \[x\] \`alloc.collections.vec\_deque.into\_iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next\` - \[x\] ~\`alloc.collections.vec\_deque.into\_iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.enumerate\`~ - \[x\] …

No recorded comments or reviews.

### Item 233

**[Issue #233](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/233) — Add links to issues for everything tweaked in aeneas-config.yml**

Status: closed. Opened: 2026-06-18. Author: oliver-butterley.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 234

**[PR #234](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/234) — Lean model for alloc::collections::vec\_deque: VecDeque and its IntoIter**

Status: merged. Opened: 2026-06-19. Author: truonghoangle.

Body excerpt: This PR replaces the previously axiomatized \`VecDeque\` and \`IntoIter\` models in the Aeneas-generated external Lean files with concrete executable implementations and verified specification theorems. ### Changes \*\*\`SrcTranslated/TypesExternal.lean\`\*\* \* Replaced \`VecDeque\` axiom with a ring-buffer structure (\`buf\`, \`head\`, \`length\`). \* Replaced \`IntoIter\` axiom with a structure wrapping a \`VecDeque\`. …

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/234#issuecomment-4761388140) — Zhang-Liao (2026-06-21): I claim that I am reviewing it.
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/234#discussion_r3448295835) — Zhang-Liao (2026-06-21; SrcTranslated/FunsExternal.lean:1047): \`push\_back\` is inconsistent with \`pop\_front\` and \`index\_mut\`. The latter two treat buf as a fixed-capacity ring buffer — they index with \`(head + i) % cap\` where \`cap = buf.length\`. But \`push\_back\` appends \`buf ++ \[value\]\`, which grows the physical buffer on every call instead of writing into the existing capacity at the ring's back slot. \`pop\_front\` advances head but never shrinks \`buf\` — \`buf\` keeps its old length …
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/234#pullrequestreview-4539566750) — Zhang-Liao (2026-06-21): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/234#discussion_r3448729080) — truonghoangle (2026-06-21; SrcTranslated/FunsExternal.lean:1047): Thank you for your comments. I have selected option 2 and fixed it.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/234#pullrequestreview-4539976147) — truonghoangle (2026-06-21): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/234#discussion_r3449648088) — Zhang-Liao (2026-06-22; SrcTranslated/FunsExternal.lean:979): I think it should be tagged with @\[step\].
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/234#discussion_r3449648341) — Zhang-Liao (2026-06-22; SrcTranslated/FunsExternal.lean:985): I think it should be tagged with @\[step\].
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/234#pullrequestreview-4540910316) — Zhang-Liao (2026-06-22): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/234#discussion_r3449867039) — truonghoangle (2026-06-22; SrcTranslated/FunsExternal.lean:979): I combined the two theorems into one and added the @\[step\] tag.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/234#pullrequestreview-4541192836) — truonghoangle (2026-06-22): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/234#discussion_r3449979808) — Zhang-Liao (2026-06-22; SrcTranslated/TypesExternal.lean:30): There is a double space. Overall, the PR is fine, and I have approved it.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/234#pullrequestreview-4541348357) — Zhang-Liao (2026-06-22): (No text.)
- [review DISMISSED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/234#pullrequestreview-4541348699) — Zhang-Liao (2026-06-22): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/234#pullrequestreview-4542369978) — Zhang-Liao (2026-06-22): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/234#discussion_r3451131013) — Kukovec (2026-06-22; SrcTranslated/FunsExternal.lean:991): Shouldn't this be \`res.1 = some ...\` ?
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/234#pullrequestreview-4542757042) — Kukovec (2026-06-22): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/234#discussion_r3451216723) — truonghoangle (2026-06-22; SrcTranslated/FunsExternal.lean:991): I am not using \`some\` here because it ensures that the existence conditions have already been verified, so we do not need to check them again when applying it.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/234#pullrequestreview-4542856337) — truonghoangle (2026-06-22): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/234#discussion_r3451245166) — Kukovec (2026-06-22; SrcTranslated/FunsExternal.lean:991): But how is this type correct? \`res : (Option T) x ...\` so shouldn't \`res.1\` have \`Option\` type?
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/234#pullrequestreview-4542888952) — Kukovec (2026-06-22): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/234#discussion_r3451354145) — truonghoangle (2026-06-22; SrcTranslated/FunsExternal.lean:991): Lean implicitly performs type-directed reconstruction in this situation. The left-hand side has type \`Option T\`, and the right-hand side expression \`self.buf.val\[self.head.val\]'hidx\` has type \`T\`. Under the surrounding proof context-where the branch guarantees a successful lookup-the system automatically inserts the constructor some, interpreting the expression as \`some (self.buf.val\[self.head.val\]'hidx)\`. This is …
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/234#pullrequestreview-4543022704) — truonghoangle (2026-06-22): (No text.)

### Item 235

**[PR #235](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/235) — Model KeyPairCompressedBytes as a concrete struct with proved specs**

Status: merged. Opened: 2026-06-22. Author: Zhang-Liao.

Body excerpt: ## Summary Towards #170 (specify and verify \`spqr::incremental\_mlkem768::generate\`). Verifying \`generate\` requires specs for the libcrux \`KeyPairCompressedBytes\` interface it calls. This PR provides those specs by replacing the opaque axiomatized type and its externals with an honest Lean model, so the \`generate\` proof can depend on proved \`@\[step\]\` theorems instead of trusted axioms. ## Changes - …

Discussion and review record:

- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/235#discussion_r3449880311) — truonghoangle (2026-06-22; SrcTranslated/FunsExternal.lean:1333): A "True" clause is not what we need.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/235#pullrequestreview-4541212758) — truonghoangle (2026-06-22): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/235#discussion_r3449886058) — truonghoangle (2026-06-22; Spqr/Specs/IncrementalMlkem768/Generate.lean:60): We need to know more about the relationships between HDR, EK, and DK; relying solely on length properties fails to capture the true nature of the function.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/235#pullrequestreview-4541221360) — truonghoangle (2026-06-22): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/235#discussion_r3449887850) — truonghoangle (2026-06-22; SrcTranslated/FunsExternal.lean:1352): A "True" clause is not what we need
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/235#pullrequestreview-4541223606) — truonghoangle (2026-06-22): (No text.)
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/235#issuecomment-4765082635) — truonghoangle (2026-06-22): To fully describe the properties of this functions in this section, we need to construct supporting structures that facilitate such a description. For instance, the following parameters are required to characterize the invariants discussed in this section: \`\`\`lean structure MlkemParams where n q k η₁ η₂ dᵤ dᵥ : ℕ q\_prime : Nat.Prime q -- ⇒ ℤ\_q is a field n\_dvd\_q1 : n ∣ (q - 1) -- ⇒ a primitive n-th root of unity …
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/235#discussion_r3472142826) — Zhang-Liao (2026-06-25; Spqr/Specs/IncrementalMlkem768/Generate.lean:60): It takes me a long time to consider how to describe the relationship. I propose to ignore the complex relationship and maintain the current status. There are two reasons. 1. The Hax specification only specifies the length of bytes. 2. I have carefully checked the F\* library libcrux mentioned by @MarkusFerdinandDablander. I notice that there is no specification for from\_seed, which is essential for the specification …
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/235#pullrequestreview-4568163167) — Zhang-Liao (2026-06-25): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/235#discussion_r3472578358) — truonghoangle (2026-06-25; Spqr/Specs/IncrementalMlkem768/Generate.lean:60): It depends on the framework adopted to define the specifications that fully and unambiguously characterize the entities under consideration. For example, establishing precise relationships among these outputs requires either a dedicated foundational framework or a selected set of axioms as a point of departure. I believe the first step should be to conduct a survey of the topic and develop a clear work plan. …
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/235#pullrequestreview-4568760736) — truonghoangle (2026-06-25): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/235#discussion_r3485577178) — Zhang-Liao (2026-06-27; Spqr/Specs/IncrementalMlkem768/Generate.lean:60): Could we first just specify the relationship between \`hdr\`, \`ek\`, and \`dk\`? I want to postpone the specification of the cryptographic property to make this PR small. I will open a new PR about the cryptographic property.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/235#pullrequestreview-4584566426) — Zhang-Liao (2026-06-27): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/235#discussion_r3485672978) — truonghoangle (2026-06-27; Spqr/Specs/IncrementalMlkem768/Generate.lean:60): In my opinion, you should break it down into smaller PRs corresponding to the specific issues you've identified, making it much easier to track (i.e., addressing the smaller components of the overall problem you want to solve here).
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/235#pullrequestreview-4584706568) — truonghoangle (2026-06-27): (No text.)
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/235#issuecomment-4839647146) — Zhang-Liao (2026-06-30): @truonghoangle I have specified the relationships and parameter set mentioned by you. I propose not to write the cryptographic properties to make the PR smaller. I think it is ready for review now.
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/235#discussion_r3496004603) — Zhang-Liao (2026-06-30; SrcTranslated/FunsExternal.lean:1333): I choose to only write \`⦃ fun kp =&gt; kp.value.length = mlkem768Params.decapsulationKeyBytes ⦄\` here since I propose to submit the cryptographic property in another PR.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/235#pullrequestreview-4597084192) — Zhang-Liao (2026-06-30): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/235#discussion_r3496009018) — Zhang-Liao (2026-06-30; Spqr/Specs/IncrementalMlkem768/Generate.lean:60): I have specified the relationship between \`hdr\`, \`ek\`, and \`dk\` in the same buffer in the specification. I propose not to write the cryptographic properties to make the PR smaller
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/235#pullrequestreview-4597089112) — Zhang-Liao (2026-06-30): (No text.)
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/235#issuecomment-4839662662) — Zhang-Liao (2026-06-30): &gt; To fully describe the properties of this functions in this section, we need to construct supporting structures that facilitate such a description. For instance, the following parameters are required to characterize the invariants discussed in this section: I have done it.
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/235#issuecomment-4852668773) — truonghoangle (2026-07-01): With the minimum required level of properties, this PR is completed, but if we want to fully describe the properties, we need to open another PR. specifically, with the \`from\_seed\` \`axiom\` being incomplete with properties. The \`from\_seed\` function is specified as a deterministic \`ML-KEM-768 key-generation\` routine that takes a fixed \`64-byte\` seed and produces a key pair of a fixed, well-defined \`serialized size\`. …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/235#issuecomment-4854078321) — Kukovec (2026-07-01): &gt; With the minimum required level of properties, this PR is completed, but if we want to fully describe the properties, we need to open another PR. specifically, with the \`from\_seed\` \`axiom\` being incomplete with properties. The \`from\_seed\` function is specified as a deterministic \`ML-KEM-768 key-generation\` routine that takes a fixed \`64-byte\` seed and produces a key pair of a fixed, well-defined \`serialized size\`. …
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/235#pullrequestreview-4609118692) — truonghoangle (2026-07-01): (No text.)

### Item 236

**[Issue #236](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/236) — Update Aeneas to 34d3b272**

Status: closed. Opened: 2026-06-22. Author: oliver-butterley.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 237

**[Issue #237](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/237) — Extend / interpret axiom \`kdf.hkdf\_to\_slice\` in FunsExternal**

Status: closed. Opened: 2026-06-23. Author: MarkusFerdinandDablander.

Body excerpt: The axiom stub \`\`\`lean /-- \[spqr::kdf::hkdf\_to\_slice\]: Source: 'src/kdf.rs', lines 14:0-18:1 Visibility: public -/ axiom kdf.hkdf\_to\_slice : Slice Std.U8 → Slice Std.U8 → Slice Std.U8 → Slice Std.U8 → Result (Slice Std.U8) \`\`\` in FunsExternal.lean needs to somehow be interpreted / extended to make Issue #189 verifiable. This is in particular necessary to specify and verify \`Authenticator::update\` (Issue #191) and …

No recorded comments or reviews.

### Item 238

**[PR #238](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/238) — Update Aeneas to 34d3b272**

Status: merged. Opened: 2026-06-23. Author: oliver-butterley.

Body excerpt: Updating Aeneas required a few minor changes: - Updating Aeneas convenience script to accept a new arg for charon - Updating iterator specs and related proofs because of iterator theorems added upstream - Updating proofs for minor changes - Output of Aeneas includes some extra code closes #236

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/238#issuecomment-4786109199) — truonghoangle (2026-06-24): Great job! Since some additional axioms have appeared in the \`FunsExternal.lean\` file, could you create an issue for this? Do we need to address it right away? If so, I can take a look at it. I also like the way the function names have been shortened in this PR.
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/238#pullrequestreview-4559267234) — truonghoangle (2026-06-24): (No text.)
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/238#issuecomment-4786377162) — oliver-butterley (2026-06-24): &gt; Great job! Since some additional axioms have appeared in the \`FunsExternal.lean\` file, could you create an issue for this? Do we need to address it right away? If so, I can take a look at it. I also like the way the function names have been shortened in this PR. Sure, I will investigate these new axioms and open the appropriate issue. At the moment I don't know anything more than Aeneas produced these extra axioms …

### Item 239

**[PR #239](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/239) — Specify and verify : \`spqr::encoding::polynomial::{impl core::clone::Clone for spqr::encoding::polynomial::Poly}::clone\` in \`polynomial.rs\`**

Status: merged. Opened: 2026-06-24. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::encoding::polynomial::{impl core::clone::Clone for spqr::encoding::polynomial::Poly}::clone\` in \`polynomial.rs\` closes #144

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/239#pullrequestreview-4561579019) — Kukovec (2026-06-24): (No text.)

### Item 240

**[PR #240](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/240) — Specify and verify : \`spqr::encoding::polynomial::Poly::lagrange\_sum\` in \`polynomial.rs\`**

Status: merged. Opened: 2026-06-24. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::encoding::polynomial::Poly::lagrange\_sum\` in \`polynomial.rs\` closes #134

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/240#issuecomment-4790055317) — Kukovec (2026-06-24): !radar
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/240#issuecomment-4790061841) — baif-radar (2026-06-24): Benchmark results for fb0d96b91117c709aca815bce783b5caf51d203b against edb899ca35fed160f0520007178a9e338e530e1c are in. No significant results found. @Kukovec No significant changes detected.
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/240#pullrequestreview-4562961016) — Kukovec (2026-06-24): (No text.)

### Item 241

**[PR #241](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/241) — Specify and verify : \`spqr::encoding::polynomial::Poly::lagrange\_interpolate\_pt\` in \`polynomial.rs\`**

Status: merged. Opened: 2026-06-24. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::encoding::polynomial::Poly::lagrange\_interpolate\_pt\` in \`polynomial.rs\` closes #130

Discussion and review record:

- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/241#discussion_r3496809370) — Zhang-Liao (2026-06-30; Spqr/Specs/Encoding/Polynomial/Poly/LagrangeInterpolatePt.lean:49): I want to replace \`Cancelling (X − pts\[i\].x) yields\` with \`yields\` since there is no explanation of \`(X − pts\[i\].x)\` in \*\*Spec theorem for \`spqr.encoding.polynomial.Poly.lagrange\_interpolate\_pt\`\*\*
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/241#pullrequestreview-4598053140) — Zhang-Liao (2026-06-30): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/241#discussion_r3496999728) — truonghoangle (2026-06-30; Spqr/Specs/Encoding/Polynomial/Poly/LagrangeInterpolatePt.lean:49): I fixed it
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/241#pullrequestreview-4598302095) — truonghoangle (2026-06-30): (No text.)
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/241#issuecomment-4844642204) — truonghoangle (2026-06-30): @Zhang-Liao I have modified the theorem formatting styles to improve their appearance and make them more effective for practical application.
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/241#pullrequestreview-4610471768) — Zhang-Liao (2026-07-01): (No text.)

### Item 242

**[PR #242](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/242) — Lean model for \`core::iter::adapters:\_\` \`Enumerate\` and \`Map\`**

Status: merged. Opened: 2026-06-25. Author: Kukovec.

Body excerpt: This PR: - Deletes \`.default\` implementations, that have since been added to the base Aeneas translation - Removes unused \`axiom core.iter.adapters.enumerate.Enumerate.Insts.CoreIterTraitsIteratorIteratorPairUsizeClause0\_Item.collect\` - turns axioms from #114 into defs, using recently added Aeneas defaults, whenever applicable closes #114

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/242#pullrequestreview-4576995625) — truonghoangle (2026-06-26): (No text.)

### Item 243

**[PR #243](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/243) — Add axiom to model essential properties of \`libcrux\_hmac::hmac\`**

Status: merged. Opened: 2026-06-25. Author: MarkusFerdinandDablander.

Body excerpt: ## Summary This PR adds the axiom \`libcrux\_hmac.hmac\_sha256\_tag32\_length\_eq\_32\` to \`SrcTranslated/FunsExternal.lean\`, which states: &gt; If \`key.length ≤ u32::MAX\` and \`data.length ≤ u32::MAX\`, then &gt; \`libcrux\_hmac::hmac(Sha256, key, data, Some(32))\` is panic-free and returns &gt; an \`alloc::vec::Vec\` of length exactly \`32\`. The new axiom is a partial behavioral spec for the opaque \`axiom libcrux\_hmac.hmac\` in …

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/243#issuecomment-4800910941) — truonghoangle (2026-06-25): Great job! The content of this axiom is completely correct when \`libcrux\_hmac.hmac\` is applied with the \`Sha256\` algorithm. However, I would like to see this single axiom extended to also cover \`SHA1\`, \`SHA384\`, and \`SHA512\`. That way, it would encompass all the cases that we may want to verify and use in the future.
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/243#issuecomment-4801183843) — MarkusFerdinandDablander (2026-06-25): Hi @truonghoangle thanks a lot for your useful feedback, and for double-checking property (b)! Very much appreciated! Note that currently there are only two calls of \`libcrux\_hmac.hmac\` in our entire codebase; both can be found in \`Funs.lean\` (in lines 5011 and 5052), and both of these calls are of the same specialised form, namely \`libcrux\_hmac.hmac libcrux\_hmac.Algorithm.Sha256 s3 s4 (some …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/243#issuecomment-4801333596) — truonghoangle (2026-06-25): Everything is very clear for me. From a minimality standpoint, the axiom is probably reasonable and does not need to be extended further. However, since the behavior of \`HMAC\` essentially depends only on the underlying \`SHA algorithm\`, I wonder whether we could avoid using the tagged \`step\` here. This might make future maintenance easier: if we ever need to support additional SHA variants, we could simply reuse the …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/243#issuecomment-4807954819) — MarkusFerdinandDablander (2026-06-26): Hi @truonghoangle , thanks a lot for your quick and valuable answer, and for explaining your thinking; it certainly makes sense as well to consider all of this from an engineering and future-maintenance perspective! However, I am wondering whether a more general version of this axiom may indeed ever be needed in the future to complete the verification efforts in our repo. In my understanding SPQR is associated only …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/243#issuecomment-4808103983) — truonghoangle (2026-06-26): I think this is a difficult question because I'm not sure whether the Signal Protocol's HMAC implementation is expected to support hash functions other than SHA-256. From a theoretical perspective, HMAC is intentionally designed to be flexible so that different hash functions can be substituted while preserving its security properties. In particular, if a SHA algorithm were ever found to be vulnerable, it should be …
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/243#discussion_r3481482725) — Kukovec (2026-06-26; SrcTranslated/FunsExternal.lean:1512): My 2c: If I understand correctly, and what is being asked for by @truonghoangle is exactly \`\`\`suggestion axiom libcrux\_hmac.hmac\_algo\_tag32\_length\_eq\_32 (algo: libcrux\_hmac.Algorithm) (key data : Slice Std.U8) (hkey : key.length ≤ Std.U32.max) (hdata : data.length ≤ Std.U32.max) : libcrux\_hmac.hmac algo key data (some 32#usize) ⦃ (r : alloc.vec.Vec Std.U8) =&gt; r.length = 32 ⦄ \`\`\` and we can explain in no more than 1 …
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/243#pullrequestreview-4579561483) — Kukovec (2026-06-26): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/243#discussion_r3482536150) — MarkusFerdinandDablander (2026-06-26; SrcTranslated/FunsExternal.lean:1512): Unfortunately I think the proposed suggestion (simply adding the \`algo\` input) would be unsound and incorrectly model the original Rust source, since \`r.length\` (the postcondition) depends on the input \`algo\`. For example, for \`algo = Sha1\` I believe it should hold that \`r.length = 20\` and not \`32\`. So I am afraid generalizing the axiom would require distinguishing cases according to the input \`algo\`, and would thus …
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/243#pullrequestreview-4580782911) — MarkusFerdinandDablander (2026-06-26): (No text.)
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/243#issuecomment-4830603524) — MarkusFerdinandDablander (2026-06-29): Hi @truonghoangle and @Kukovec, Thank you both very much for the careful review and valuable technical discussion on this PR! @truonghoangle, thanks again for your observation that HMAC is designed to be hash-agnostic, and that a more general axiom could make future maintenance smoother. I very much agree that this is a valuable and forward-looking point that should be properly preserved. I also had another brief …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/243#issuecomment-4831152405) — truonghoangle (2026-06-29): I fully agree with this clear and flexible approach. @MarkusFerdinandDablander, I will approve this PR unless you have any further changes.
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/243#pullrequestreview-4590738921) — truonghoangle (2026-06-29): (No text.)

### Item 244

**[PR #244](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/244) — Specify and verify: \`spqr::encoding::polynomial::PolyConst::mult\` in \`polynomial.rs\`**

Status: merged. Opened: 2026-06-27. Author: truonghoangle.

Body excerpt: This PR specifies and verifies: \`spqr::encoding::polynomial::PolyConst::mult\` in \`polynomial.rs\` closes #210

Discussion and review record:

- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/244#discussion_r3489074750) — Zhang-Liao (2026-06-29; Spqr/Specs/Encoding/Polynomial/PolyConst/Mult.lean:119): \`0 &lt;= j\` is not needed since \`j\` is a natural number.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/244#pullrequestreview-4588644441) — Zhang-Liao (2026-06-29): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/244#discussion_r3489088590) — Zhang-Liao (2026-06-29; Spqr/Specs/Encoding/Polynomial/PolyConst/Mult.lean:58): I am unsure whether it is \`this file\` since this file is for \`mult\` not for \`loop 0\`. I think the \`theorem below\` is more appropriate.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/244#pullrequestreview-4588658684) — Zhang-Liao (2026-06-29): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/244#discussion_r3489100377) — Zhang-Liao (2026-06-29; Spqr/Specs/Encoding/Polynomial/PolyConst/Mult.lean:13): I am unsure whether it is \`this file specifies\`, since this file is for \`mult\` not for \`loop body 0\`. I think the \`theorem below\` is more appropriate.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/244#pullrequestreview-4588672921) — Zhang-Liao (2026-06-29): (No text.)
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/244#issuecomment-4828617691) — Zhang-Liao (2026-06-29): Fix my comments, and then I will approve it.
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/244#discussion_r3489382082) — truonghoangle (2026-06-29; Spqr/Specs/Encoding/Polynomial/PolyConst/Mult.lean:13): it is written based on the name of the function in the \`Funs.lean\` file, specifically /-- \[spqr::encoding::polynomial::{spqr::encoding::polynomial::PolyConst}::mult\]: loop body 0: Source: 'src/encoding/polynomial.rs', lines 403:8-408:9 -/ https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/blob/cfd06d1cdd9cc3120ac4b28cf87689591e13dc27/SrcTranslated/Funs.lean#L7727
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/244#pullrequestreview-4588991193) — truonghoangle (2026-06-29): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/244#discussion_r3489384947) — truonghoangle (2026-06-29; Spqr/Specs/Encoding/Polynomial/PolyConst/Mult.lean:58): it is written based on the name of the function in the Funs.lean file, specifically /-- \[spqr::encoding::polynomial::{spqr::encoding::polynomial::PolyConst}::mult\]: loop 0: Source: 'src/encoding/polynomial.rs', lines 403:8-408:9 -/ https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/blob/cfd06d1cdd9cc3120ac4b28cf87689591e13dc27/SrcTranslated/Funs.lean#L7745
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/244#pullrequestreview-4588994267) — truonghoangle (2026-06-29): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/244#discussion_r3489385634) — truonghoangle (2026-06-29; Spqr/Specs/Encoding/Polynomial/PolyConst/Mult.lean:119): I fixed it
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/244#pullrequestreview-4588994949) — truonghoangle (2026-06-29): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/244#pullrequestreview-4589217244) — Zhang-Liao (2026-06-29): (No text.)

### Item 245

**[Issue #245](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/245) — Track potential generalisation of \`libcrux\_hmac.hmac\_sha256\_tag32\_length\_eq\_32\` to additional SHA variants and tag lengths**

Status: open. Opened: 2026-06-29. Author: MarkusFerdinandDablander.

Body excerpt: ## Context PR #243 added the axiom \`libcrux\_hmac.hmac\_sha256\_tag32\_length\_eq\_32\` to \`SrcTranslated/FunsExternal.lean\`. In its current form the axiom is specialised to the exact call shape that occurs in this codebase: - \*\*Algorithm:\*\* \`libcrux\_hmac.Algorithm.Sha256\` - \*\*Tag length:\*\* 32 (i.e. \`MACSIZE = 32\`) This shape currently covers both existing calls of \`libcrux\_hmac.hmac\` in \`Funs.lean\` (lines 5011 and 5052). …

No recorded comments or reviews.

### Item 246

**[PR #246](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/246) — Specify and verify: \`spqr::encoding::polynomial::PolyConst::mult\_xdiff\` in \`polynomial.rs\`**

Status: merged. Opened: 2026-06-29. Author: truonghoangle.

Body excerpt: This PR specifies and verifies: \`spqr::encoding::polynomial::PolyConst::mult\_xdiff\` in \`polynomial.rs\` closes #211

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/246#pullrequestreview-4614118023) — Zhang-Liao (2026-07-02): (No text.)

### Item 247

**[PR #247](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/247) — Specify and verify : \`spqr::authenticator::Authenticator::mac\_ct\` in \`authenticator.rs\`**

Status: merged. Opened: 2026-06-30. Author: MarkusFerdinandDablander.

Body excerpt: Closes #225 Closes #189

Discussion and review record:

- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/247#discussion_r3499592148) — truonghoangle (2026-06-30; Spqr/Specs/Authenticator/Authenticator/MacCt.lean:40): Shouldn't we also describe the relationship between \`self \`ep\` \`ct\` and the \`result\`?
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/247#pullrequestreview-4601351717) — truonghoangle (2026-06-30): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/247#discussion_r3506900715) — MarkusFerdinandDablander (2026-07-01; Spqr/Specs/Authenticator/Authenticator/MacCt.lean:40): Hi @truonghoangle thanks for the useful comment; I think you are right that the postcondition should be enriched further to capture such a relationship. I have done some extra work to incorporate such an extension (along with a streamlining of the underlying axiom which lists the no-panic condition explicitly to make the axiom fire more smoothly with step\* while keeping the semantics and trust base equivalent). All …
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/247#pullrequestreview-4610189537) — MarkusFerdinandDablander (2026-07-01): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/247#discussion_r3507929109) — truonghoangle (2026-07-01; Spqr/Specs/Authenticator/Authenticator/MacCt.lean:53): Everything is perfect. I'm just wondering if there's a way to phrase this without using \`ok\`
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/247#pullrequestreview-4611566864) — truonghoangle (2026-07-01): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/247#pullrequestreview-4611569543) — truonghoangle (2026-07-01): (No text.)

### Item 248

**[Issue #248](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/248) — Fully specify \`from\_seed\` behavioral properties (follow-up to #235)**

Status: open. Opened: 2026-07-01. Author: Zhang-Liao.

Body excerpt: ## Context PR #235 (merged, closes #170) modeled \`KeyPairCompressedBytes\` as a concrete struct and replaced the opaque externals with honest \`def\`s plus proved \`@\[step\]\` specs. That PR intentionally captured only the \*\*minimum required level of properties\*\* to unblock the \`generate\` proof. Per @truonghoangle's review on #235, the \`from\_seed\` axiom remains \*\*incomplete with respect to its properties\*\*. Its current …

No recorded comments or reviews.

### Item 249

**[PR #249](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/249) — Specify and verify : \`spqr::encoding::polynomial::Poly::lagrange\_interpolate\` in \`polynomial.rs\`**

Status: merged. Opened: 2026-07-01. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::encoding::polynomial::Poly::lagrange\_interpolate\` in \`polynomial.rs\` closes #126

Discussion and review record:

- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/249#pullrequestreview-4634211813) — Zhang-Liao (2026-07-06): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/249#discussion_r3527504427) — Zhang-Liao (2026-07-06; Spqr/Specs/Encoding/Polynomial/Poly/LagrangeInterpolate.lean:394): We should add \`result.degree = pts.length\` to the spec. The function \`lagrange\_interpolate\` is used to get polys. Later, \`ploys\` is used to calculate \`compute\_at(pt.x)\`. In the specification of ComputeAt, \`degree\` is defined as \`coefficients.val.length\`. So we need to add a post-condition \`result.degree = pts.length\`.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/249#pullrequestreview-4634521849) — Zhang-Liao (2026-07-06): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/249#discussion_r3527756611) — Zhang-Liao (2026-07-06; Spqr/Specs/Encoding/Polynomial/Poly/LagrangeInterpolate.lean:67): \`LagrangeInterpolateLoopBoby1\` is a typo. It should be \`LagrangeInterpolateLoopBody1\`
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/249#issuecomment-4891302420) — Zhang-Liao (2026-07-06): Style Notes - Missing spaces: iter.start&lt; iter.end (line 137), p.2.2.degree= template.degree (line 249), ∀ j (line 147), apply mul\_right\_cancel₀ (line 427), rw\[degree\] (lines 440/453).
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/249#discussion_r3528178110) — truonghoangle (2026-07-06; Spqr/Specs/Encoding/Polynomial/Poly/LagrangeInterpolate.lean:394): I have added the clause as you requested.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/249#pullrequestreview-4635027133) — truonghoangle (2026-07-06): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/249#discussion_r3528179015) — truonghoangle (2026-07-06; Spqr/Specs/Encoding/Polynomial/Poly/LagrangeInterpolate.lean:67): I fixed it
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/249#pullrequestreview-4635028191) — truonghoangle (2026-07-06): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/249#pullrequestreview-4635221146) — Zhang-Liao (2026-07-06): (No text.)

### Item 250

**[PR #250](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/250) — Specify and verify : \`spqr::authenticator::Authenticator::mac\_hdr\` in \`authenticator.rs\`**

Status: merged. Opened: 2026-07-02. Author: MarkusFerdinandDablander.

Body excerpt: Closes #190 \*\*Note:\*\* This PR provides a spec theorem file for \`mac\_hdr\`. The contributed spec theorem file for \`mac\_hdr\` is very similar to the one for \`mac\_ct\` that was recently merged in PR #247. This is because \`mac\_hdr\` and \`mac\_ct\` are almost-identical sister functions, for processing headers (\`hdr\`) and ciphertexts (\`ct\`) respectively. The only technical implementation difference (next to parameter naming) …

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/250#pullrequestreview-4619633176) — truonghoangle (2026-07-02): (No text.)

### Item 251

**[Issue #251](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/251) — Move \`add\_assign\_spec\` for \`Poly\` out of the \`test\` namespace**

Status: closed. Opened: 2026-07-02. Author: astefano.

Body excerpt: The spec theorem for \`spqr::encoding::polynomial::Poly::add\_assign\` is declared inside \`namespace spqr.encoding.polynomial.Poly.test\` (\`Spqr/Specs/Encoding/Polynomial/Poly/AddAssign.lean:307\`), giving it the full name \`spqr.encoding.polynomial.Poly.test.add\_assign\_spec\`. Verification tooling (probe-lean/probe-aeneas) links a def's primary spec via the \`\_spec\` naming convention, which expects …

No recorded comments or reviews.

### Item 252

**[PR #252](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/252) — Move \`add\_assign\_spec\` for \`Poly\` out of the \`test\` namespace**

Status: merged. Opened: 2026-07-02. Author: astefano.

Body excerpt: This PR renames \`namespace spqr.encoding.polynomial.Poly.test\` to \`spqr.encoding.polynomial.Poly\` in \`Spqr/Specs/Encoding/Polynomial/Poly/AddAssign.lean\`, so the spec theorem for \`spqr::encoding::polynomial::Poly::add\_assign\` gets the full name \`spqr.encoding.polynomial.Poly.add\_assign\_spec\`. This matches the \`\_spec\` convention the verification tooling uses to link a def's primary spec (and the convention of the …

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/252#pullrequestreview-4619629446) — truonghoangle (2026-07-02): (No text.)

### Item 253

**[PR #253](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/253) — Specify and verify: \`spqr::encoding::polynomial::PolyConst::lagrange\_interpolate\_pt\` in \`polynomial.rs\`**

Status: merged. Opened: 2026-07-02. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::encoding::polynomial::PolyConst::lagrange\_interpolate\_pt\` in \`polynomial.rs\` closes #209

Discussion and review record:

- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/253#discussion_r3517293781) — Zhang-Liao (2026-07-03; Spqr/Specs/Encoding/Polynomial/PolyConst/LagrangeInterpolatePt.lean:217): Why do we need this private lemma? It is never used in this file.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/253#pullrequestreview-4622568885) — Zhang-Liao (2026-07-03): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/253#discussion_r3517295093) — Zhang-Liao (2026-07-03; Spqr/Specs/Encoding/Polynomial/PolyConst/LagrangeInterpolatePt.lean:194): Why do we need this private lemma? It is never used in this file.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/253#pullrequestreview-4622570494) — Zhang-Liao (2026-07-03): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/253#discussion_r3517339702) — Zhang-Liao (2026-07-03; Spqr/Specs/Encoding/Polynomial/PolyConst/LagrangeInterpolatePt.lean:152): The annotation A between 173 and 189, and the annotation B between 241 and 250, seem to be duplicated.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/253#pullrequestreview-4622628029) — Zhang-Liao (2026-07-03): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/253#discussion_r3517531194) — truonghoangle (2026-07-03; Spqr/Specs/Encoding/Polynomial/PolyConst/LagrangeInterpolatePt.lean:217): I removed it-previously, I had used the condition specifying a polynomial of degree less than \`N\`, where the coefficient at the (N-1)-th position of the list was zero. I subsequently replaced this with the condition that the polynomial has a degree strictly less than N-1, matching the form we currently use. This makes the definition easier to understand and more intuitive-aligning better with natural human reasoning …
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/253#pullrequestreview-4622861810) — truonghoangle (2026-07-03): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/253#discussion_r3517532347) — truonghoangle (2026-07-03; Spqr/Specs/Encoding/Polynomial/PolyConst/LagrangeInterpolatePt.lean:194): I removed it
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/253#pullrequestreview-4622863095) — truonghoangle (2026-07-03): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/253#discussion_r3517544510) — truonghoangle (2026-07-03; Spqr/Specs/Encoding/Polynomial/PolyConst/LagrangeInterpolatePt.lean:152): I have followed the instructions. Annotation A corresponds to: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/blob/5a686d4a8425530ae9e0b9c6e9d7280d82664936/doc/STYLE\_GUIDE.md?plain=1#L61 Annotation B corresponds to: https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/blob/5a686d4a8425530ae9e0b9c6e9d7280d82664936/doc/STYLE\_GUIDE.md?plain=1#L79 Basically, comments …
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/253#pullrequestreview-4622876937) — truonghoangle (2026-07-03): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/253#pullrequestreview-4623310020) — Zhang-Liao (2026-07-03): (No text.)

### Item 254

**[Issue #254](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/254) — Specify and verify : \`spqr::encoding::polynomial::{impl Encoder for PolyEncoder}::encode\_bytes\` in \`polynomial.rs\`**

Status: closed. Opened: 2026-07-02. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 255

**[Issue #255](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/255) — Specify and verify : \`spqr::encoding::polynomial::{impl Encoder for PolyEncoder}::next\_chunk\` in \`polynomial.rs\`**

Status: closed. Opened: 2026-07-02. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 256

**[Issue #256](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/256) — Specify and verify: \`spqr::encoding::polynomial::PolyDecoder::get\_pts\_needed\` in \`polynomial.rs\`**

Status: closed. Opened: 2026-07-02. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 257

**[Issue #257](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/257) — Specify and verify \`spqr::encoding::polynomial::PolyDecoder::necessary\_points\` in \`polynomial.rs\`**

Status: closed. Opened: 2026-07-02. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 258

**[Issue #258](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/258) — Specify and verify: \`spqr::encoding::polynomial::PolyDecoder::new\_with\_poly\_count\` in \`polynomial.rs\`**

Status: closed. Opened: 2026-07-02. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 259

**[Issue #259](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/259) — Specify and verify : \`spqr::encoding::polynomial::PolyDecoder::into\_pb\` in \`polynomial.rs\`**

Status: closed. Opened: 2026-07-02. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 260

**[Issue #260](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/260) — Specify and verify: \`spqr::encoding::polynomial::PolyDecoder::from\_pb\` in \`polynomial.rs\`**

Status: closed. Opened: 2026-07-02. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 261

**[Issue #261](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/261) — Specify and verify : \`spqr::encoding::polynomial::{impl Decoder for PolyDecoder}::new\` in \`polynomial.rs\`**

Status: closed. Opened: 2026-07-02. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 262

**[Issue #262](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/262) — Specify and verify : \`spqr::encoding::polynomial::{impl Decoder for PolyDecoder}::add\_chunk\` in \`polynomial.rs\`**

Status: closed. Opened: 2026-07-02. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 263

**[Issue #263](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/263) — Specify and verify: \`spqr::encoding::polynomial::{impl Decoder for PolyDecoder}::decoded\_message\` in \`polynomial.rs\`**

Status: closed. Opened: 2026-07-02. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 264

**[Issue #264](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/264) — Specify and verify: \`spqr::encoding::polynomial::COMPLETE\_POINTS\_POLYS\_1\` in \`polynomial.rs\`**

Status: closed. Opened: 2026-07-02. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 265

**[Issue #265](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/265) — Specify and verify: \`spqr::encoding::polynomial::COMPLETE\_POINTS\_POLYS\_3\` in \`polynomial.rs\`**

Status: closed. Opened: 2026-07-02. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 266

**[Issue #266](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/266) — Specify and verify : \`spqr::encoding::polynomial::COMPLETE\_POINTS\_POLYS\_5\` in \`polynomial.rs\`**

Status: closed. Opened: 2026-07-02. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 267

**[Issue #267](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/267) — Specify and verify: \`spqr::encoding::polynomial::COMPLETE\_POINTS\_POLYS\_30\` in \`polynomial.rs\`**

Status: closed. Opened: 2026-07-02. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 268

**[Issue #268](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/268) — Specify and verify: \`spqr::encoding::polynomial::COMPLETE\_POINTS\_POLYS\_34\` in \`polynomial.rs\`**

Status: closed. Opened: 2026-07-02. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 269

**[Issue #269](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/269) — Specify and verify: \`spqr::encoding::polynomial::COMPLETE\_POINTS\_POLYS\_36\` in \`polynomial.rs\`**

Status: closed. Opened: 2026-07-02. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 270

**[PR #270](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/270) — Specify and verify: \`From for EncodingError::from\` in \`encoding.rs\`**

Status: merged. Opened: 2026-07-03. Author: Zhang-Liao.

Body excerpt: Closes #161. Adds a Lean spec theorem for the \`From\` conversion that lifts a \`polynomial::PolynomialError\` into the wider \`EncodingError\` type (\`src/encoding.rs\`, lines 18–22) — the conversion the \`?\` operator uses to turn a polynomial-layer error into an encoding-layer error.

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/270#pullrequestreview-4626356327) — truonghoangle (2026-07-03): (No text.)

### Item 271

**[PR #271](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/271) — Specify and verify: \`spqr::encoding::polynomial::PolyConst::to\_poly\` in \`polynomial.rs\`**

Status: merged. Opened: 2026-07-03. Author: truonghoangle.

Body excerpt: This PR specifies and verifies : \`spqr::encoding::polynomial::PolyConst::to\_poly\` in \`polynomial.rs\` closes #212

Discussion and review record:

- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/271#discussion_r3528408497) — Zhang-Liao (2026-07-06; Spqr/Specs/Encoding/Polynomial/PolyConst/ToPoly.lean:6): I confirm \`import Spqr.Math.Poly.Basic.Defs\` also works here. \`import Spqr.Math.Poly.Lagrange.InterpolantSum\` is a little heavier than \`import Spqr.Math.Poly.Lagrange.InterpolantSum\`.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/271#pullrequestreview-4635308487) — Zhang-Liao (2026-07-06): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/271#discussion_r3529122752) — truonghoangle (2026-07-06; Spqr/Specs/Encoding/Polynomial/PolyConst/ToPoly.lean:6): I fixed it
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/271#pullrequestreview-4636138823) — truonghoangle (2026-07-06): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/271#pullrequestreview-4642010723) — Zhang-Liao (2026-07-07): (No text.)

### Item 272

**[Issue #272](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/272) — Fix omitted y field in lagrange\_polys\_for\_complete\_points record update**

Status: closed. Opened: 2026-07-06. Author: truonghoangle.

Body excerpt: In the definition \`\`\` lean /-- \[spqr::encoding::polynomial::lagrange\_polys\_for\_complete\_points\]: loop body 0: Source: 'src/encoding/polynomial.rs', lines 477:8–482:9 -/ \`\`\` at the line \`\`\`lean let a := index\_mut\_back { p with x := { value := i1 } } \`\`\` Aeneas omitted part of the record update. It should instead be \`\`\`lean let a := index\_mut\_back { p with x := { value := i1 }, y := encoding.gf.GF16.ONE } \`\`\` so that …

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/272#issuecomment-4892992030) — oliver-butterley (2026-07-06): That's great, thanks for highlighting the issue. I believe this is one that is already in the pipeline but it's important to have the extra examples for checking and testing. I'll assign myself to this issue so I remember it.
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/272#issuecomment-5216453754) — astefano (2026-08-07): by chance, i came across this issue (i was debugging something in probe-lean). my understanding from the exchange i had with claude is that the proposal to add \`y := encoding.gf.GF16.ONE\` would lead to an unfaithful translation wrt \`lagrange\_polys\_for\_complete\_points\`. we have: \`\`\` // src/encoding/polynomial.rs:469-482 const fn lagrange\_polys\_for\_complete\_points() -&gt; \[PolyConst; N\] { let mut ones = \[Pt { x: …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/272#issuecomment-5216564309) — astefano (2026-08-07): furthermore, \`lagrange\_polys\_for\_complete\_points\_loop0.body\_spec\` quantifies over an arbitrary \`ones : Array Pt N\` with no hypothesis about \`y\`, but its cont postcondition asserts \`(ones1\[i\]!).y = GF16.ONE\`. since Pt has two independent GF16 fields and the body leaves \`y\` alone, \`ones1\[i\].y = ones\[i\].y\`, which is unconstrained. claude shows that it's concretely refutable: \`\`\` import Spqr open Aeneas Aeneas.Std …

### Item 273

**[PR #273](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/273) — Specify and verify: spqr::encoding::polynomial::lagrange\_polys\_for\_complete\_points in polynomial.rs**

Status: merged. Opened: 2026-07-06. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::encoding::polynomial::lagrange\_polys\_for\_complete\_points\` in \`polynomial.rs.\` The verification follows the Rust implementation by proving: - Loop 0 initializes the complete points 0, 1, …, N−1 in GF(2¹⁶). - Loop 1 computes the corresponding scaled Lagrange basis polynomials. - The top-level specification composes both loops to prove the correctness of the returned array and the …

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/273#issuecomment-4900657051) — github-actions[bot] (2026-07-07): ### Sorry Delta — hand-written specs \*\*6 new sorry-tainted declarations in \`Spqr.Specs.\*\`:\*\* | Module | Declaration | Kind | |--------|-------------|------| | \`Spqr.Specs.Encoding.Polynomial.LagrangePolysForCompletePoints\` | \`spqr.encoding.polynomial.lagrange\_polys\_for\_complete\_points\_loop0.body\_spec\` | direct | | \`Spqr.Specs.Encoding.Polynomial.LagrangePolysForCompletePoints\` | …
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/273#discussion_r3533992349) — Zhang-Liao (2026-07-07; Spqr/Specs/Encoding/Polynomial/LagrangePolysForCompletePoints.lean:48): Do we really need \`(\_ : i &lt; ones1.length)\` to construct a proof?
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/273#pullrequestreview-4642123378) — Zhang-Liao (2026-07-07): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/273#discussion_r3534102836) — truonghoangle (2026-07-07; Spqr/Specs/Encoding/Polynomial/LagrangePolysForCompletePoints.lean:48): It is required by the index definition of the \`Array Pt N\` type.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/273#pullrequestreview-4642266445) — truonghoangle (2026-07-07): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/273#pullrequestreview-4642297536) — Zhang-Liao (2026-07-07): (No text.)

### Item 274

**[PR #274](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/274) — Specify and verify: \`spqr::encoding::polynomial::COMPLETE\_POINTS\_POLYS\_1\` in \`polynomial.rs\`**

Status: merged. Opened: 2026-07-07. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::encoding::polynomial::COMPLETE\_POINTS\_POLYS\_1\` in \`polynomial.rs\` closes #264

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/274#issuecomment-4901423955) — github-actions[bot] (2026-07-07): ### Sorry Delta — hand-written specs \*\*2 new sorry-tainted declarations in \`Spqr.Specs.\*\`:\*\* | Module | Declaration | Kind | |--------|-------------|------| | \`Spqr.Specs.Encoding.Polynomial.COMPLETE\_POINTS\_POLYS\_1\` | \`spqr.encoding.polynomial.COMPLETE\_POINTS\_POLYS\_1\_spec\` | transitive | | \`Spqr.Specs.Encoding.Polynomial.COMPLETE\_POINTS\_POLYS\_1\` | \`spqr.encoding.polynomial.COMPLETE\_POINTS\_POLYS\_1\_spec.mvcgen\_spec\` | …
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/274#pullrequestreview-4643735582) — Kukovec (2026-07-07): (No text.)
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/274#issuecomment-4902428838) — Kukovec (2026-07-07): Why is the sorry delta bot triggering on \_this\_ PR, it doesn't introduce any \`sorry\`?
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/274#issuecomment-4902476984) — truonghoangle (2026-07-07): I don't know why, either, nor do I know why this comment appeared.

### Item 275

**[PR #275](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/275) — Specify and verify: \`spqr::encoding::polynomial::PolyEncoder::into\_pb\` in \`polynomial.rs\`**

Status: merged. Opened: 2026-07-07. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::encoding::polynomial::PolyEncoder::into\_pb\` in \`polynomial.rs\` closes #216

Discussion and review record:

- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/275#discussion_r3544156399) — Zhang-Liao (2026-07-08; Spqr/Specs/Encoding/Polynomial/PolyEncoder/IntoPb.lean:255): Inhabited encoding.polynomial.Poly duplicates the existing instance at Spqr/Math/Poly/Identities/Basic.lean:101, which is already in this file's import closure
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/275#pullrequestreview-4654370336) — Zhang-Liao (2026-07-08): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/275#discussion_r3544171728) — Zhang-Liao (2026-07-08; Spqr/Specs/Encoding/Polynomial/PolyEncoder/IntoPb.lean:48): Spacing inconsistencies: IntoPb.lean:47 (hi + lo), :282 (serialized\[2 \* k\]! + and \[2 \* k +1\]!), :348 (\[2 \* k\]!+), :411 (∀ j), :412 (=2 \*), :414 (\[2 \* k \]!), :478 (:ℕ )).
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/275#pullrequestreview-4654387789) — Zhang-Liao (2026-07-08): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/275#discussion_r3544575533) — truonghoangle (2026-07-08; Spqr/Specs/Encoding/Polynomial/PolyEncoder/IntoPb.lean:255): I fixed it
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/275#pullrequestreview-4654847005) — truonghoangle (2026-07-08): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/275#discussion_r3544575999) — truonghoangle (2026-07-08; Spqr/Specs/Encoding/Polynomial/PolyEncoder/IntoPb.lean:48): I fixed it
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/275#pullrequestreview-4654847566) — truonghoangle (2026-07-08): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/275#pullrequestreview-4655455463) — Zhang-Liao (2026-07-08): (No text.)

### Item 276

**[PR #276](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/276) — Specify and verify: \`spqr::encoding::polynomial::COMPLETE\_POINTS\_POLYS\_3\` in \`polynomial.rs\`**

Status: merged. Opened: 2026-07-08. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::encoding::polynomial::COMPLETE\_POINTS\_POLYS\_3\` in \`polynomial.rs\` closes #265

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/276#issuecomment-4912066540) — github-actions[bot] (2026-07-08): ### Sorry Delta — hand-written specs \*\*2 new sorry-tainted declarations in \`Spqr.Specs.\*\`:\*\* | Module | Declaration | Kind | |--------|-------------|------| | \`Spqr.Specs.Encoding.Polynomial.COMPLETE\_POINTS\_POLYS\_3\` | \`spqr.encoding.polynomial.COMPLETE\_POINTS\_POLYS\_3\_spec\` | transitive | | \`Spqr.Specs.Encoding.Polynomial.COMPLETE\_POINTS\_POLYS\_3\` | \`spqr.encoding.polynomial.COMPLETE\_POINTS\_POLYS\_3\_spec.mvcgen\_spec\` | …
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/276#discussion_r3550450758) — Zhang-Liao (2026-07-09; Spqr/Specs/Encoding/Polynomial/COMPLETE_POINTS_POLYS_3.lean:38): By the style guideline, we need the type of \`result\`.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/276#pullrequestreview-4661679702) — Zhang-Liao (2026-07-09): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/276#discussion_r3550463574) — Zhang-Liao (2026-07-09; Spqr/Specs/Encoding/Polynomial/COMPLETE_POINTS_POLYS_3.lean:58): Proof uses non-terminal \`simp \[BitVec.toNat\_ofNat\]\` before \`grind\`; mathlib convention is \`simp only\` for non-terminal \`simp\`s (robustness against simp-set drift).
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/276#pullrequestreview-4661694292) — Zhang-Liao (2026-07-09): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/276#discussion_r3550998849) — truonghoangle (2026-07-09; Spqr/Specs/Encoding/Polynomial/COMPLETE_POINTS_POLYS_3.lean:38): If we add type \`Array (PolyConst 3#usize) 3#usize\` of result then we have the "No goals to be solved" error. The root cause was that the \`3#usize\` macro expands to \`Usize.ofNat 3 (by first | decide | scalar\_tac)\`, and when used inside the WP \`⦃ ⦄\` binder's type annotation, Lean's unification with the already-known return type of \`COMPLETE\_POINTS\_POLYS\_3\` would resolve the proof obligation before the explicit tactic …
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/276#pullrequestreview-4662308307) — truonghoangle (2026-07-09): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/276#discussion_r3550999686) — truonghoangle (2026-07-09; Spqr/Specs/Encoding/Polynomial/COMPLETE_POINTS_POLYS_3.lean:58): I fixed it
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/276#pullrequestreview-4662309206) — truonghoangle (2026-07-09): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/276#discussion_r3572051230) — Kukovec (2026-07-13; Spqr/Specs/Encoding/Polynomial/COMPLETE_POINTS_POLYS_3.lean:38): I'm personally fine with not adding the type annotation, but please do add the above comment explaining why in the .lean file.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/276#pullrequestreview-4686340902) — Kukovec (2026-07-13): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/276#discussion_r3572134775) — oliver-butterley (2026-07-13; Spqr/Specs/Encoding/Polynomial/COMPLETE_POINTS_POLYS_3.lean:38): @mpenciak what's your opinion on this behaviour? We prefer to write the type of result so that the spec statement is very readable as text without needing the elaborator. Is there over zealous reduction happening in this specific case?
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/276#pullrequestreview-4686439029) — oliver-butterley (2026-07-13): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/276#discussion_r3574226772) — truonghoangle (2026-07-13; Spqr/Specs/Encoding/Polynomial/COMPLETE_POINTS_POLYS_3.lean:38): I've added comments in the .lean file. @oliver-butterley Do we need to create an issue for this?
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/276#pullrequestreview-4688825637) — truonghoangle (2026-07-13): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/276#discussion_r3574324911) — mpenciak (2026-07-13; Spqr/Specs/Encoding/Polynomial/COMPLETE_POINTS_POLYS_3.lean:38): Yeah, this is definitely a bug in the elaborator for the postcondition notation. It'd be great if you make an issue! It doesn't have to have an absolutely minimal reproduction, but something relatively simple could also help significantly in guiding the fix (though @truonghoangle's comment looks spot on, and seems like a great starting point for a fix).
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/276#pullrequestreview-4688941629) — mpenciak (2026-07-13): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/276#pullrequestreview-4693209934) — Zhang-Liao (2026-07-14): (No text.)

### Item 277

**[PR #277](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/277) — Model incremental ML-KEM primitives with pure companions and Hoare-style axioms**

Status: open draft. Opened: 2026-07-08. Author: Zhang-Liao.

Body excerpt: ## Summary - Move incremental ML-KEM primitive axioms into per-function spec files - Restate the incremental ML-KEM axioms in Hoare-triple style - Model \`keygen\` and its accessors with pure companions and bridging axioms - Model \`encapsulate1\` with conditional pure companions ## Test plan - \[ \] \`lake build\` succeeds with no new \`sorry\`/axiom warnings beyond the intended bridging axioms 🤖 Generated with Claude Code

No recorded comments or reviews.

### Item 278

**[PR #278](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/278) — Specify and verify: spqr::encoding::polynomial::PolyEncoder::from\_pb in polynomial.rs**

Status: merged. Opened: 2026-07-08. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::encoding::polynomial::PolyEncoder::from\_pb\` in \`polynomial.rs\` closes #217

Discussion and review record:

- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/278#discussion_r3559924601) — Zhang-Liao (2026-07-10; Spqr/Specs/Encoding/Polynomial/PolyEncoder/FromPb.lean:290): FromPb.lean:290 re-declares instance : Inhabited encoding.polynomial.Point, identical to the one in IntoPb.lean:121.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/278#pullrequestreview-4672625217) — Zhang-Liao (2026-07-10): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/278#discussion_r3559933864) — Zhang-Liao (2026-07-10; Spqr/Specs/Encoding/Polynomial/PolyEncoder/FromPb.lean:270): Dead case split: in from\_pb\_loop1\_loop0.loop\_spec (lines 268-270), by\_cases hj\_lt : j &lt; iter'.start.val with grind in both branches — I verified a single grind closes the goal.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/278#pullrequestreview-4672636038) — Zhang-Liao (2026-07-10): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/278#discussion_r3574141813) — truonghoangle (2026-07-13; Spqr/Specs/Encoding/Polynomial/PolyEncoder/FromPb.lean:270): I fixed it
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/278#pullrequestreview-4688732408) — truonghoangle (2026-07-13): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/278#discussion_r3574142822) — truonghoangle (2026-07-13; Spqr/Specs/Encoding/Polynomial/PolyEncoder/FromPb.lean:290): I fixed it
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/278#pullrequestreview-4688733701) — truonghoangle (2026-07-13): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/278#pullrequestreview-4690428863) — Zhang-Liao (2026-07-14): (No text.)

### Item 279

**[PR #279](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/279) — Specify and verify: \`spqr::incremental\_mlkem768::flip\_endianness\_of\_encapsulation\_state\` in \`incremental\_mlkem768.rs\`**

Status: merged. Opened: 2026-07-13. Author: Zhang-Liao.

Body excerpt: This PR specifies and verifies \`spqr::incremental\_mlkem768::flip\_endianness\_of\_encapsulation\_state\` in \`incremental\_mlkem768.rs\`, and extracts two reusable Aeneas-std spec theorems that keep the proof fully \`step\`-driven. ## Main spec: \`Spqr/Specs/IncrementalMlkem768/FlipEndianness.lean\` The spec is functional: for any input of even length &gt; 32, the function returns a vector of the same length whose prefix \`\[0, len …

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/279#issuecomment-4956712841) — Kukovec (2026-07-13): !radar
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/279#pullrequestreview-4683625267) — Kukovec (2026-07-13): Spec looks fine, though I'm convinced the proof of this could be shortened. If radar shows no notable delta I'll approve.
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/279#issuecomment-4956718306) — baif-radar (2026-07-13): Benchmark results for 03ae38dabda401ca9e3b958f2770afa9b824d0b7 against 7fd414149947267c6d92ae59c7cb5970603812cd are in. No significant results found. @Kukovec No significant changes detected.
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/279#pullrequestreview-4683682172) — Kukovec (2026-07-13): (No text.)

### Item 280

**[PR #280](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/280) — Specify and verify: \`spqr::encoding::polynomial::PolyEncoder::get\_encoder\_state\` in \`polynomial.rs\`**

Status: merged. Opened: 2026-07-14. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::encoding::polynomial::PolyEncoder::get\_encoder\_state\` in \`polynomial.rs\` closes #215

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/280#pullrequestreview-4692711717) — Kukovec (2026-07-14): (No text.)

### Item 281

**[Issue #281](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/281) — Root Cause of the "No Goals to Be Solved" Error with \`3#usize\` Type Annotations**

Status: open. Opened: 2026-07-14. Author: truonghoangle.

Body excerpt: In PR #276, we encountered the following issue. If we explicitly annotate the result with the type Array (PolyConst 3#usize) 3#usize, Lean reports the error "No goals to be solved." The root cause is that the macro 3#usize expands to \`\`\` lean Usize.ofNat 3 (by first | decide | scalar\_tac) \`\`\` Consequently, the type annotation already contains a proof term. Inside the WP ⦃ ... ⦄ binder, Lean unifies this annotated …

No recorded comments or reviews.

### Item 282

**[PR #282](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/282) — Lean model for \`core::slice::iter\`: slice iteration**

Status: merged. Opened: 2026-07-14. Author: Kukovec.

Body excerpt: - \`SharedASlice.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into\_iter\` already defined from previous PR - \`core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.map\` def and spec added - \`core.slice.iter.ChunksExact.Insts.CoreIterTraitsIteratorIteratorSharedASlice.collect\` and \`.map\` had axioms with no discernble use cases, so they were removed. closes #113

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/282#pullrequestreview-4694647749) — truonghoangle (2026-07-14): (No text.)

### Item 283

**[PR #283](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/283) — Specify and verify : \`spqr::encoding::polynomial::COMPLETE\_POINTS\_POLYS\_5\` in \`polynomial.rs\`**

Status: merged. Opened: 2026-07-14. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::encoding::polynomial::COMPLETE\_POINTS\_POLYS\_5\` in \`polynomial.rs\` closes #266

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/283#issuecomment-4969204086) — github-actions[bot] (2026-07-14): ### Sorry Delta — hand-written specs \*\*2 new sorry-tainted declarations in \`Spqr.Specs.\*\`:\*\* | Module | Declaration | Kind | |--------|-------------|------| | \`Spqr.Specs.Encoding.Polynomial.COMPLETE\_POINTS\_POLYS\_5\` | \`spqr.encoding.polynomial.COMPLETE\_POINTS\_POLYS\_5\_spec\` | transitive | | \`Spqr.Specs.Encoding.Polynomial.COMPLETE\_POINTS\_POLYS\_5\` | \`spqr.encoding.polynomial.COMPLETE\_POINTS\_POLYS\_5\_spec.mvcgen\_spec\` | …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/283#issuecomment-4969211440) — Kukovec (2026-07-14): !radar
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/283#issuecomment-4969214669) — baif-radar (2026-07-14): Benchmark results for 78c2cf5011d711795c802efe45adacfc8b2b73f4 against 52ee3f3d0a02339832d8e5bf28dff1cbc1d74d7e are in. No significant results found. @Kukovec No significant changes detected.
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/283#pullrequestreview-4694368206) — Kukovec (2026-07-14): LGTM, sorry-alert unrelated to changes in this PR.

### Item 284

**[PR #284](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/284) — Specify and verify: \`spqr::encoding::polynomial::PolyEncoder::encode\_bytes\_base\` in \`polynomial.rs\`**

Status: merged. Opened: 2026-07-14. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::encoding::polynomial::PolyEncoder::encode\_bytes\_base\` in \`polynomial.rs\`. It also replaces the axiom for \`core::array::from\_fn\` with a proper definition and accompanying specification theorem. Closes #219.

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/284#issuecomment-4979115951) — Kukovec (2026-07-15): !radar
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/284#issuecomment-4979117976) — baif-radar (2026-07-15): Benchmark results for 9a46249af8fc47f7ec6885a75af508fd4b7edf87 against d0fd1982ce7afe4af9a26ad0142ba6193739f2b3 are in. No significant results found. @Kukovec No significant changes detected.
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/284#discussion_r3586160150) — Kukovec (2026-07-15; Spqr/Specs/Aeneas/SliceChunksExact.lean:35): I think a more precise theorem would be that the number is LE than \`length / n\` (flooring division).
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/284#discussion_r3586168497) — Kukovec (2026-07-15; Spqr/Specs/Aeneas/SliceChunksExact.lean:58): See previous comment
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/284#pullrequestreview-4702875217) — Kukovec (2026-07-15): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/284#discussion_r3587217356) — truonghoangle (2026-07-15; Spqr/Specs/Aeneas/SliceChunksExact.lean:35): thank you for your comments. I fixed it
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/284#pullrequestreview-4704049613) — truonghoangle (2026-07-15): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/284#discussion_r3587218786) — truonghoangle (2026-07-15; Spqr/Specs/Aeneas/SliceChunksExact.lean:58): I fixed it
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/284#pullrequestreview-4704051261) — truonghoangle (2026-07-15): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/284#pullrequestreview-4720874448) — Zhang-Liao (2026-07-17): (No text.)

### Item 285

**[Issue #285](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/285) — Use Mathlib.Linter.linter.style.header**

Status: closed. Opened: 2026-07-14. Author: oliver-butterley.

Body excerpt: Mathlib includes a file header linter (https://leanprover-community.github.io/mathlib4\_docs/Mathlib/Tactic/Linter/Header.html) which is active by default in the latest version of Lean. When we allow it to be active we will need to adjust a few of the files.

No recorded comments or reviews.

### Item 286

**[PR #286](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/286) — Specify and verify \`spqr::encoding::polynomial::COMPLETE\_POINTS\_POLYS\_30\` in \`polynomial.rs\`**

Status: merged. Opened: 2026-07-14. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::encoding::polynomial::COMPLETE\_POINTS\_POLYS\_30\` in \`polynomial.rs\` closes #267

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/286#issuecomment-4979111638) — Kukovec (2026-07-15): !radar
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/286#issuecomment-4979117875) — baif-radar (2026-07-15): Benchmark results for 65a5c58e74feabb19ffa504b454cc9e6b19351ab against d0fd1982ce7afe4af9a26ad0142ba6193739f2b3 are in. No significant results found. @Kukovec No significant changes detected.
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/286#pullrequestreview-4702891175) — Kukovec (2026-07-15): (No text.)
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/286#issuecomment-4979354806) — github-actions[bot] (2026-07-15): ### Sorry Delta — hand-written specs \*\*2 new sorry-tainted declarations in \`Spqr.Specs.\*\`:\*\* | Module | Declaration | Kind | |--------|-------------|------| | \`Spqr.Specs.Encoding.Polynomial.COMPLETE\_POINTS\_POLYS\_30\` | \`spqr.encoding.polynomial.COMPLETE\_POINTS\_POLYS\_30\_spec\` | transitive | | \`Spqr.Specs.Encoding.Polynomial.COMPLETE\_POINTS\_POLYS\_30\` | …

### Item 287

**[PR #287](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/287) — Update to Aeneas b059c34a**

Status: merged. Opened: 2026-07-15. Author: oliver-butterley.

Body excerpt: Update to the latest Aeneas. This involved: - Some tweaks can now be removed since they are solved - Some definitions / theorems in the external files are no longer required - A few proofs updated - There is another linter now active that doesn't like underscores so added scripts/nolints.json - Lean now forbids using \`Aux\` as a folder name, apparently that causes a problem on windows so this folder is renamed

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/287#issuecomment-4978779961) — oliver-butterley (2026-07-15): !radar
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/287#issuecomment-4978785485) — baif-radar (2026-07-15): Benchmark results for 1ba4fdc6d1280150aec7bf657c664b6ca50bd34f against d0fd1982ce7afe4af9a26ad0142ba6193739f2b3 are in. No significant results found. @oliver-butterley No significant changes detected.
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/287#discussion_r3586096226) — Kukovec (2026-07-15; Spqr/Specs/Encoding/Polynomial/PolyConst/MultXdiff.lean:1): Any idea what causes this to need a longer proof?
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/287#pullrequestreview-4702799359) — Kukovec (2026-07-15): LGTM, though I didn't inspect \`Funs\`,\`Types\` and the \`json\`, since they're presumably autogen.
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/287#discussion_r3586209836) — oliver-butterley (2026-07-15; Spqr/Specs/Encoding/Polynomial/PolyConst/MultXdiff.lean:1): It appears that grind no longer has access to something. I tried hard to find a way to have a proof which was just grind with some helper suggestions but failed. It could well be due to how something in the way Aeneas represents objects changed in the background. Although the proof is longer it is quicker than before and I don't see a way to make it better.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/287#pullrequestreview-4702934038) — oliver-butterley (2026-07-15): (No text.)
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/287#issuecomment-4979232846) — oliver-butterley (2026-07-15): &gt; LGTM, though I didn't inspect \`Funs\`,\`Types\` and the \`json\`, since they're presumably autogen. yep, all those are auto generated
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/287#discussion_r3586220094) — oliver-butterley (2026-07-15; Spqr/Specs/Encoding/Polynomial/PolyConst/MultXdiff.lean:1): As such I would go for this current proof. It would take a lot of effort to try to find a better way and a better way might not exist now. It doesn't seem worthwhile to me.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/287#pullrequestreview-4702944896) — oliver-butterley (2026-07-15): (No text.)

### Item 288

**[PR #288](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/288) — Add aeneas doc**

Status: merged. Opened: 2026-07-15. Author: oliver-butterley.

Body excerpt: Concise doc which explains how to update Aeneas in this repo.

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/288#pullrequestreview-4702818708) — Kukovec (2026-07-15): (No text.)

### Item 289

**[PR #289](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/289) — Lean model for alloc::collections::vec\_deque: VecDeque and its IntoIter (group B)**

Status: merged. Opened: 2026-07-15. Author: Kukovec.

Body excerpt: - \`alloc.collections.vec\_deque.into\_iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next\`, \`.enumerate\`, and \`.step\_by\` are redundant - Added def for \`.map\` closes #232

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/289#issuecomment-4979374195) — truonghoangle (2026-07-15): !radar
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/289#issuecomment-4979378544) — baif-radar (2026-07-15): Benchmark results for 34b1302e7ad31ab1764ab149bb68fa39e8bbb8fd against 076a85df23187811999929b14afb996dac3ce56f are in. There are significant results. @truonghoangle - 🟥 \`bench\` exited with code \*\*1\*\* No significant changes detected.
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/289#pullrequestreview-4713631806) — truonghoangle (2026-07-16): (No text.)

### Item 290

**[Issue #290](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/290) — Verify : \`serialize.rs\`**

Status: open. Opened: 2026-07-15. Author: Zhang-Liao.

Body excerpt: - \[x\] #291 - \[x\] #292 - \[x\] #293 - \[x\] #294 - \[x\] #295

No recorded comments or reviews.

### Item 291

**[Issue #291](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/291) — Specify and verify : \`spqr::serialize::{impl core::convert::From for spqr::serialize::Error}::from\` in \`serialize.rs\`**

Status: closed. Opened: 2026-07-15. Author: Zhang-Liao.

Body excerpt: Parent: #290

No recorded comments or reviews.

### Item 292

**[Issue #292](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/292) — Specify and verify : \`spqr::serialize::{impl core::clone::Clone for spqr::serialize::Error}::clone\` in \`serialize.rs\`**

Status: closed. Opened: 2026-07-15. Author: Zhang-Liao.

Body excerpt: Parent: #290

No recorded comments or reviews.

### Item 293

**[Issue #293](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/293) — Specify and verify : \`spqr::serialize::{impl core::cmp::PartialEq for spqr::serialize::Error}::eq\` in \`serialize.rs\`**

Status: closed. Opened: 2026-07-15. Author: Zhang-Liao.

Body excerpt: Parent: #290

No recorded comments or reviews.

### Item 294

**[Issue #294](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/294) — Specify and verify : \`spqr::serialize::{impl core::fmt::Debug for spqr::serialize::Error}::fmt\` in \`serialize.rs\`**

Status: closed. Opened: 2026-07-15. Author: Zhang-Liao.

Body excerpt: Parent: #290

No recorded comments or reviews.

### Item 295

**[Issue #295](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/295) — Specify and verify : \`spqr::serialize::{impl core::fmt::Display for spqr::serialize::Error}::fmt\` in \`serialize.rs\`**

Status: closed. Opened: 2026-07-15. Author: Zhang-Liao.

Body excerpt: Parent: #290

No recorded comments or reviews.

### Item 296

**[PR #296](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/296) — Specify and verify: \`spqr::serialize::{impl core::convert::From for spqr::serialize::Error}::from\` in \`serialize.rs\`**

Status: merged. Opened: 2026-07-15. Author: Zhang-Liao.

Body excerpt: Closes #291 (part of #290). Adds \`Spqr/Specs/Serialize/Error/From.lean\` with the \`@\[step\]\` spec theorem \`from\_spec\` for the extracted function \`serialize.Error.Insts.CoreConvertFromPolynomialError.from\`: - The call always succeeds (no panic). - The result is the constant \`serialize.Error.EncodingDecoding\`, regardless of the input \`PolynomialError\` (the input error is discarded, unlike the analogous \`EncodingError\` …

Discussion and review record:

- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/296#discussion_r3593879439) — truonghoangle (2026-07-16; Spqr/Specs/Serialize/Error/From.lean:33): why do you use \`\_e\`? what does this mean?
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/296#pullrequestreview-4711916266) — truonghoangle (2026-07-16): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/296#discussion_r3593945594) — Zhang-Liao (2026-07-16; Spqr/Specs/Serialize/Error/From.lean:33): I use \`\_e\` to denote that it does not change the final output. From the related function definition (src/serialize.rs (lines 14:0-18:1)), no matter what PolynomialError is input, the output is always a serialization error.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/296#pullrequestreview-4711992103) — Zhang-Liao (2026-07-16): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/296#pullrequestreview-4712004006) — truonghoangle (2026-07-16): (No text.)

### Item 297

**[PR #297](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/297) — Add spec axiom: kdf.hkdf\_to\_slice\_spec**

Status: merged. Opened: 2026-07-15. Author: oliver-butterley.

Body excerpt: Add the spec axiom which relates to RFC 5869 HKDF-SHA256. fixes #237

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/297#pullrequestreview-4706148623) — truonghoangle (2026-07-15): (No text.)

### Item 298

**[PR #298](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/298) — Specify and verify: \`spqr::encoding::polynomial::COMPLETE\_POINTS\_POLYS\_34\` in \`polynomial.rs\`**

Status: merged. Opened: 2026-07-15. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::encoding::polynomial::COMPLETE\_POINTS\_POLYS\_34\` in \`polynomial.rs\` closes #268

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/298#pullrequestreview-4711583161) — Zhang-Liao (2026-07-16): (No text.)

### Item 299

**[PR #299](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/299) — Refactor \`mac\_hdr\_spec\` and \`mac\_ct\_spec\` (authenticator)**

Status: merged. Opened: 2026-07-16. Author: oliver-butterley.

Body excerpt: This PR involves the refactor of the statements of \`mac\_hdr\_spec\` and \`mac\_ct\_spec\`, together with updates of the proofs and multiple other small improvement to things those proofs depend on. In particular the isolation of multiple results which are staged for upstream to Aeneas (in addition to the results required presently, this PR also add the others of the same pattern so the full set is ready for upstreaming). …

Discussion and review record:

- [review DISMISSED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/299#pullrequestreview-4727743053) — truonghoangle (2026-07-18): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/299#pullrequestreview-4733144796) — truonghoangle (2026-07-20): (No text.)

### Item 300

**[PR #300](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/300) — Specify and verify: \`spqr::encoding::polynomial::COMPLETE\_POINTS\_POLYS\_36\` in \`polynomial.rs\`**

Status: merged. Opened: 2026-07-16. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::encoding::polynomial::COMPLETE\_POINTS\_POLYS\_36\` in \`polynomial.rs\` closes #269

Discussion and review record:

- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/300#discussion_r3595569871) — Kukovec (2026-07-16; Spqr/Specs/Encoding/Polynomial/COMPLETE_POINTS_POLYS_36.lean:31): Presumably, this can also use \`lagrange\_polys\_for\_complete\_points\_scaled\_spec\` from #302
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/300#pullrequestreview-4713853642) — Kukovec (2026-07-16): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/300#discussion_r3595620997) — truonghoangle (2026-07-16; Spqr/Specs/Encoding/Polynomial/COMPLETE_POINTS_POLYS_36.lean:31): ok. I will change after @Zhang-Liao merge #302
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/300#pullrequestreview-4713911376) — truonghoangle (2026-07-16): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/300#discussion_r3601546828) — truonghoangle (2026-07-17; Spqr/Specs/Encoding/Polynomial/COMPLETE_POINTS_POLYS_36.lean:31): I fixed it!
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/300#pullrequestreview-4720744021) — truonghoangle (2026-07-17): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/300#pullrequestreview-4720763504) — Zhang-Liao (2026-07-17): (No text.)
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/300#issuecomment-5000686586) — github-actions[bot] (2026-07-17): ### Sorry Delta — hand-written specs \*\*2 new sorry-tainted declarations in \`Spqr.Specs.\*\`:\*\* | Module | Declaration | Kind | |--------|-------------|------| | \`Spqr.Specs.Encoding.Polynomial.COMPLETE\_POINTS\_POLYS\_36\` | \`spqr.encoding.polynomial.COMPLETE\_POINTS\_POLYS\_36\_spec\` | transitive | | \`Spqr.Specs.Encoding.Polynomial.COMPLETE\_POINTS\_POLYS\_36\` | …

### Item 301

**[Issue #301](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/301) — Refactor: factor the COMPLETE\_POINTS\_POLYS\_\* specs through a generic scaled-basis lemma**

Status: closed. Opened: 2026-07-16. Author: Zhang-Liao.

Body excerpt: ## Problem The spec proofs for \`COMPLETE\_POINTS\_POLYS\_3\` / \`\_5\` / \`\_30\` (and \`\_34\` from #298) are four near-identical copies of the same ~30-line proof, differing only in the numeric constant. Each file also declares its own \`Inhabited (PolyConst n#usize)\` instance. Nothing in the proof body actually depends on the concrete value of \`N\`, so this duplication: - makes every future constant (\`COMPLETE\_POINTS\_POLYS\_36\` …

No recorded comments or reviews.

### Item 302

**[PR #302](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/302) — Refactor: factor COMPLETE\_POINTS\_POLYS\_\* specs through a generic scaled-basis lemma**

Status: merged. Opened: 2026-07-16. Author: Zhang-Liao.

Body excerpt: closes #301 ## Summary Adds \`lagrange\_polys\_for\_complete\_points\_scaled\_spec\`, a generic (\`N : Usize\`, \`0 &lt; N ≤ 65536\`) version of the per-constant \`COMPLETE\_POINTS\_POLYS\_\*\` proofs: each \`result\[j\]\` is the \`j\`-th scaled Lagrange basis polynomial for the complete points \`0, …, N−1\`. The proof is the previous per-constant proof body with the numeric literal generalised to \`N\`; it identifies the existential witness …

Discussion and review record:

- [review DISMISSED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/302#pullrequestreview-4713807331) — Kukovec (2026-07-16): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/302#pullrequestreview-4720522787) — truonghoangle (2026-07-17): (No text.)

### Item 303

**[PR #303](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/303) — Specify and verify: \`spqr::serialize::{impl core::cmp::PartialEq for spqr::serialize::Error}::eq\` in \`serialize.rs\`**

Status: merged. Opened: 2026-07-16. Author: Zhang-Liao.

Body excerpt: Closes #293 (parent: #290) ## Summary - Adds \`Spqr/Specs/Serialize/Error/Eq.lean\` with a \`@\[step\]\` spec theorem for the derived \`PartialEq for serialize::Error\`: - the call always succeeds (no panic), and - \`result = true ↔ self = other\` — since both variants are fieldless, the discriminant comparison performed by the extracted code coincides with propositional equality. - Registers the new spec in \`Spqr.lean\`. ## …

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/303#pullrequestreview-4721230736) — truonghoangle (2026-07-17): (No text.)

### Item 304

**[PR #304](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/304) — Rust docs with per-function Lean verification panels**

Status: open. Opened: 2026-07-17. Author: jinxinglim.

Body excerpt: # Description Adds a Rust documentation pipeline for the \`spqr\` crate in which every function/constant with a Lean spec theorem displays an embedded "Lean specification" panel, graded ✓✓ proven / △ axiomatized / ◑ incomplete (mirroring curve25519-dalek-lean-verify's rustdoc augmentation, adapted to this repo). The docs are built in the verified configuration (\`--features extraction\`, private items documented) so the …

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/304#issuecomment-5010466746) — oliver-butterley (2026-07-18): As noted above by @jinxinglim, currently we can't use github pages here. Options are: - Remove this repo from the fork network - Deploy the website to a separate server - Something else?

### Item 305

**[Issue #305](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/305) — Upstream various stuff to Aeneas**

Status: closed. Opened: 2026-07-17. Author: oliver-butterley.

Body excerpt: | File | Upstream target | Contents | |---|---|---| | \`Slice.lean\` | \`Std/Slice.lean\` | \`Slice.make\` + \`val\_make\` / \`length\_make\` / \`make\_val\` / \`make\_inj\` | | \`Vec.lean\` | \`Std/Vec.lean\` | \`Vec.deref\_val\` / \`Vec.deref\_length\` | | \`Array.lean\` | \`Std/Array/Array.lean\` | \`Array.val\_make\` / \`length\_make\` / \`make\_val\` / \`make\_inj\` | | \`ArraySlice.lean\` | \`Std/Array/ArraySlice.lean\` | \`Array.as\_slice\_spec\` | | …

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/305#issuecomment-5298182111) — oliver-butterley (2026-08-14): All of these are now PRs in the Aeneas repo, waiting to be merged.

### Item 306

**[Issue #306](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/306) — Verify : \`v1/chunked/states/serialize.rs\`**

Status: open. Opened: 2026-07-17. Author: Zhang-Liao.

Body excerpt: - \[x\] #307 - \[x\] #308 - \[x\] #309 - \[x\] #310 - \[x\] #311 - \[x\] #312 - \[x\] #313 - \[x\] #314 - \[x\] #315 - \[x\] #316 - \[ \] #317 - \[ \] #318

No recorded comments or reviews.

### Item 307

**[Issue #307](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/307) — Specify and verify : \`spqr::v1::chunked::states::serialize::MAX\_VARINT\_BYTES\_LEN\` in \`v1/chunked/states/serialize.rs\`**

Status: closed. Opened: 2026-07-17. Author: Zhang-Liao.

Body excerpt: Parent: #306

No recorded comments or reviews.

### Item 308

**[Issue #308](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/308) — Specify and verify : \`spqr::v1::chunked::states::serialize::{impl core::convert::From for u8}::from\` in \`v1/chunked/states/serialize.rs\`**

Status: closed. Opened: 2026-07-17. Author: Zhang-Liao.

Body excerpt: Parent: #306

No recorded comments or reviews.

### Item 309

**[Issue #309](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/309) — Specify and verify : \`spqr::v1::chunked::states::serialize::{impl core::convert::TryFrom for spqr::v1::chunked::states::serialize::MessageType}::try\_from\` in \`v1/chunked/states/serialize.rs\`**

Status: closed. Opened: 2026-07-17. Author: Zhang-Liao.

Body excerpt: Parent: #306

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/309#issuecomment-5086986479) — Zhang-Liao (2026-07-27): Closes by #343

### Item 310

**[Issue #310](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/310) — Specify and verify : \`spqr::v1::chunked::states::serialize::{spqr::v1::chunked::states::serialize::MessageType}::from\_payload\` in \`v1/chunked/states/serialize.rs\`**

Status: closed. Opened: 2026-07-17. Author: Zhang-Liao.

Body excerpt: Parent: #306

No recorded comments or reviews.

### Item 311

**[Issue #311](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/311) — Specify and verify : \`spqr::v1::chunked::states::serialize::encode\_varint\` in \`v1/chunked/states/serialize.rs\`**

Status: closed. Opened: 2026-07-17. Author: Zhang-Liao.

Body excerpt: Parent: #306

No recorded comments or reviews.

### Item 312

**[Issue #312](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/312) — Specify and verify : \`spqr::v1::chunked::states::serialize::decode\_varint\` in \`v1/chunked/states/serialize.rs\`**

Status: closed. Opened: 2026-07-17. Author: Zhang-Liao.

Body excerpt: Parent: #306

No recorded comments or reviews.

### Item 313

**[Issue #313](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/313) — Specify and verify : \`spqr::v1::chunked::states::serialize::encode\_chunk\` in \`v1/chunked/states/serialize.rs\`**

Status: closed. Opened: 2026-07-17. Author: Zhang-Liao.

Body excerpt: Parent: #306

No recorded comments or reviews.

### Item 314

**[Issue #314](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/314) — Specify and verify : \`spqr::v1::chunked::states::serialize::decode\_chunk\` in \`v1/chunked/states/serialize.rs\`**

Status: closed. Opened: 2026-07-17. Author: Zhang-Liao.

Body excerpt: Parent: #306

No recorded comments or reviews.

### Item 315

**[Issue #315](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/315) — Specify and verify : \`spqr::v1::chunked::states::serialize::{spqr::v1::chunked::states::Message}::serialize\` in \`v1/chunked/states/serialize.rs\`**

Status: closed. Opened: 2026-07-17. Author: Zhang-Liao.

Body excerpt: Parent: #306

No recorded comments or reviews.

### Item 316

**[Issue #316](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/316) — Specify and verify : \`spqr::v1::chunked::states::serialize::{spqr::v1::chunked::states::Message}::deserialize\` in \`v1/chunked/states/serialize.rs\`**

Status: closed. Opened: 2026-07-17. Author: Zhang-Liao.

Body excerpt: Parent: #306 Includes the two extracted error-mapping closures (\`closure\` for \`TryFromIntError\` and \`closure#1\` for \`alloc::string::String\`).

No recorded comments or reviews.

### Item 317

**[Issue #317](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/317) — Specify and verify : \`spqr::v1::chunked::states::serialize::{spqr::v1::chunked::states::States}::into\_pb\` in \`v1/chunked/states/serialize.rs\`**

Status: open. Opened: 2026-07-17. Author: Zhang-Liao.

Body excerpt: Parent: #306

No recorded comments or reviews.

### Item 318

**[Issue #318](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/318) — Specify and verify : \`spqr::v1::chunked::states::serialize::{spqr::v1::chunked::states::States}::from\_pb\` in \`v1/chunked/states/serialize.rs\`**

Status: open. Opened: 2026-07-17. Author: Zhang-Liao.

Body excerpt: Parent: #306

No recorded comments or reviews.

### Item 319

**[PR #319](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/319) — Enable a header-style linter and correct problems flagged by the linter**

Status: merged. Opened: 2026-07-17. Author: oliver-butterley.

Body excerpt: Mathlib has a header linter (\`linter.style.header\`) which is now active by default. However it hardcodes the required copyright line and so is incompatible with this project's LICENSE-APACHE file. There is a PR to mathlib which adds a config option for that linter. This PR adds a copy of that modified linter locally so that we can use it immediately (+469 lines from this file). This local version …

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/319#issuecomment-5004389878) — oliver-butterley (2026-07-17): @truonghoangle @Kukovec @Zhang-Liao Would you all be fine to modify our style to include the \`(c)\` in the copyright notice so we conform what is most common?
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/319#pullrequestreview-4727740729) — truonghoangle (2026-07-18): (No text.)

### Item 320

**[PR #320](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/320) — Specify and verify : \`spqr::encoding::polynomial::{impl Encoder for PolyEncoder}::encode\_bytes\` in \`polynomial.rs\`**

Status: merged. Opened: 2026-07-17. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::encoding::polynomial::{impl Encoder for PolyEncoder}::encode\_bytes\` in \`polynomial.rs\` closes #254

Discussion and review record:

- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/320#discussion_r3607920101) — Zhang-Liao (2026-07-18; Spqr/Specs/Encoding/Polynomial/PolyEncoder/EncodeBytes.lean:21): Why do we need \`encode\_bytes\_spec\_nat\`? It looks very similar to \`encode\_bytes\_spec\`.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/320#pullrequestreview-4728054809) — Zhang-Liao (2026-07-18): (No text.)
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/320#pullrequestreview-4728062062) — oliver-butterley (2026-07-18): I don't understand the part of the statement: \`\`\`lean ∃ (c : Slice U8), c.length ≥ 2 ∧ g.toGF216 = (256 \* c\[0\]! + c\[1\]!).toGF216) \`\`\` Why a slice of length at least 2, rather than just (a b : U8) with the properties required? However, all this is saying is that there exists (n &lt; 2 ^ 32) such that \`g.toGF216 = n.toGF216\`, wouldn't it be easier to write like this? Possibly there is some context I'm missing here! From …
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/320#pullrequestreview-4728107089) — Zhang-Liao (2026-07-18): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/320#discussion_r3607966578) — Zhang-Liao (2026-07-18; Spqr/Specs/Encoding/Polynomial/PolyEncoder/EncodeBytes.lean:56): \`\`\` ∀ g ∈ pts\[j\]!.value.val, ∃ (c : Slice U8), c.length ≥ 2 ∧ g.toGF216 = (256 \* c\[0\]! + c\[1\]!).toGF216) \`\`\` seems always to be true. We may not need it in the postcondition. It has been proven in the file Spqr/Specs/Encoding/Polynomial/PolyEncoder/EncodeBytesBase.lean using \`\`\` private theorem gf16\_representable (g : GF16) : ∃ (c : Slice U8), c.length ≥ 2 ∧ g.toGF216 = (256 \* c\[0\]! + c\[1\]!).toGF216 := by \`\`\`.
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/320#discussion_r3611124716) — truonghoangle (2026-07-19; Spqr/Specs/Encoding/Polynomial/PolyEncoder/EncodeBytes.lean:21): I removed it
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/320#pullrequestreview-4731271921) — truonghoangle (2026-07-19): (No text.)
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/320#issuecomment-5016942650) — truonghoangle (2026-07-19): &gt; I don't understand the part of the statement: &gt; &gt; \`\`\`lean &gt; ∃ (c : Slice U8), &gt; c.length ≥ 2 ∧ &gt; g.toGF216 = (256 \* c\[0\]! + c\[1\]!).toGF216) &gt; \`\`\` &gt; &gt; Why a slice of length at least 2, rather than just (a b : U8) with the properties required? However, all this is saying is that there exists (n match result with | core.result.Result.Ok ⟨idx, EncoderState.Points pts⟩ =&gt; idx = 0#u32 ∧ (∀ (j : Nat), j False ⦄ := by \`\`\`
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/320#issuecomment-5018621713) — Zhang-Liao (2026-07-20): @truonghoangle \`pts\[j\]!.value\[k\]!.toGF216\` seems to be idential to \`(listToGF216Poly pts\[j\]!.value).coeff k\` but it is shorter. Which is better from your perspective for future proof construction?
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/320#issuecomment-5019088571) — truonghoangle (2026-07-20): Use \`pts\[j\]!.value\[k\]!.toGF216\`. we have 1. \*\*Simpler proofs.\*\* The loop invariant naturally produces the direct form; \`encode\_bytes\_base\_spec\` currently adds \`← getElem!\_toGF216\_eq\_coeff\` (line 442) just to convert to polynomial form. Using the direct form eliminates that step. 2. \*\*Matches the encoding layer convention.\*\* \`FromPb.lean\` and \`IntoPb.lean\` specs use direct indexing, not polynomial coefficients. The …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/320#issuecomment-5019348964) — Zhang-Liao (2026-07-20): @truonghoangle Thanks for your patient explanation! I agree that the polynomial form is better since it is more descriptive and will choose it.
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/320#issuecomment-5020412445) — truonghoangle (2026-07-20): @Zhang-Liao @oliver-butterley Could you continue the review so I can proceed with the work on this branch?
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/320#pullrequestreview-4734625246) — Zhang-Liao (2026-07-20): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/320#pullrequestreview-4734628363) — Zhang-Liao (2026-07-20): (No text.)

### Item 321

**[Issue #321](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/321) — Specify and verify: \`spqr::encoding::polynomial::{impl Ord for Pt}::cmp\` in \`polynomial.rs\`**

Status: closed. Opened: 2026-07-17. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 322

**[Issue #322](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/322) — Specify and verify: \`spqr::encoding::polynomial::{impl PartialOrd for Pt}::partial\_cmp\` in \`polynomial.rs\`**

Status: closed. Opened: 2026-07-17. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 323

**[Issue #323](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/323) — Specify and verify: \`spqr::encoding::polynomial::{impl PartialEq for Pt}::eq\` in \`polynomial.rs\`**

Status: closed. Opened: 2026-07-17. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 324

**[PR #324](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/324) — Specify and verify: \`spqr::encoding::polynomial::{impl PartialOrd for Pt}::partial\_cmp\` in \`polynomial.rs\`**

Status: merged. Opened: 2026-07-17. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::encoding::polynomial::{impl PartialOrd for Pt}::partial\_cmp\` in \`polynomial.rs\` closes #322

Discussion and review record:

- [review DISMISSED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/324#pullrequestreview-4728063146) — oliver-butterley (2026-07-18): LGTM
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/324#pullrequestreview-4733174272) — oliver-butterley (2026-07-20): (No text.)

### Item 325

**[PR #325](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/325) — Move headerLinter.lean to the correct location**

Status: merged. Opened: 2026-07-18. Author: oliver-butterley.

Body excerpt: In PR #319 the lean\_lib headerLinter was added but the file/folder arrangement didn't follow the standard arrangement for lean projects. This caused \`lake exe mk\_all\` to fail. This PR rearranges the HeaderLinter.lean file to fit the standard format. Note: no code has been added or removed, simply moved to the other file.

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/325#pullrequestreview-4731579231) — truonghoangle (2026-07-19): (No text.)

### Item 326

**[PR #326](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/326) — Specify and verify: \`spqr::v1::chunked::states::serialize::MAX\_VARINT\_BYTES\_LEN\` in \`v1/chunked/states/serialize.rs\`**

Status: merged. Opened: 2026-07-19. Author: Zhang-Liao.

Body excerpt: Closes #307 Adds the spec theorem \`MAX\_VARINT\_BYTES\_LEN\_val\` proving \`MAX\_VARINT\_BYTES\_LEN.val = 10\`, following the existing pattern for plain \`Usize\` constants (e.g. \`CHUNK\_SIZE\`, \`MACSIZE\`). This is the first spec under the new \`Spqr/Specs/V1/\` directory tree. Verified with \`lake build Spqr\` (2399 jobs, no errors).

Discussion and review record:

- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/326#discussion_r3611144767) — truonghoangle (2026-07-19; Spqr/Specs/V1/Chunked/States/Serialize/MAX_VARINT_BYTES_LEN.lean:23): Which is better to use: \`Simp\` or \`Step\`?
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/326#pullrequestreview-4731289466) — truonghoangle (2026-07-19): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/326#discussion_r3611779526) — Zhang-Liao (2026-07-20; Spqr/Specs/V1/Chunked/States/Serialize/MAX_VARINT_BYTES_LEN.lean:23): I think \`simp\` is better for two reasons 1. The extracted definition is a pure constant, not a monadic computation. In \`SrcTranslated/Funs.lean\`, Aeneas extracts it as \`def v1.chunked.states.serialize.MAX\_VARINT\_BYTES\_LEN : Std.Usize := 10#usize\` — a plain \`Std.Usize\` value. Since the Rust initializer is a literal with no fallible arithmetic, the extraction does not wrap it in Result, so the spec is a plain equation …
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/326#pullrequestreview-4731889569) — Zhang-Liao (2026-07-20): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/326#pullrequestreview-4732368088) — truonghoangle (2026-07-20): (No text.)

### Item 327

**[PR #327](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/327) — Specify and verify: \`spqr::v1::chunked::states::serialize::{impl core::convert::From for u8}::from\` in \`v1/chunked/states/serialize.rs\`**

Status: merged. Opened: 2026-07-20. Author: Zhang-Liao.

Body excerpt: This PR specifies and verifies \`spqr::v1::chunked::states::serialize::{impl core::convert::From for u8}::from\` in \`v1/chunked/states/serialize.rs\`. The \`From\` conversion is derived by \`#\[derive(IntoPrimitive)\]\` on the \`#\[repr(u8)\]\` fieldless enum \`MessageType\`. It reads the discriminant of the input variant and returns it as a \`u8\`. The spec theorem \`from\_spec\` states that the call always succeeds and returns the …

Discussion and review record:

- [review DISMISSED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/327#pullrequestreview-4733524490) — truonghoangle (2026-07-20): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/327#pullrequestreview-4734830480) — truonghoangle (2026-07-20): (No text.)

### Item 328

**[PR #328](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/328) — Specify and verify: \`spqr::encoding::polynomial::{impl Ord for Pt}::cmp\` in \`polynomial.rs\`**

Status: merged. Opened: 2026-07-20. Author: truonghoangle.

Body excerpt: This PR specifies and verifies: \`spqr::encoding::polynomial::{impl Ord for Pt}::cmp\` in \`polynomial.rs\` closes #321

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/328#pullrequestreview-4735374524) — Zhang-Liao (2026-07-20): (No text.)

### Item 329

**[PR #329](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/329) — Specify and verify: \`spqr::v1::chunked::states::serialize::{spqr::v1::chunked::states::serialize::MessageType}::from\_payload\` in \`v1/chunked/states/serialize.rs\`**

Status: merged. Opened: 2026-07-20. Author: Zhang-Liao.

Body excerpt: This PR specifies and verifies \`spqr::v1::chunked::states::serialize::{spqr::v1::chunked::states::serialize::MessageType}::from\_payload\` in \`v1/chunked/states/serialize.rs\`. \`from\_payload\` is a total function that classifies a \`MessagePayload\` by returning the \`MessageType\` tag corresponding to its variant. It discards the payload contents and maps each \`MessagePayload\` variant to the identically-named \`MessageType\` …

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/329#pullrequestreview-4733544292) — truonghoangle (2026-07-20): (No text.)

### Item 330

**[PR #330](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/330) — Specify and verify: \`spqr::serialize::{impl core::clone::Clone for spqr::serialize::Error}::clone\` in \`serialize.rs\`**

Status: merged. Opened: 2026-07-20. Author: Zhang-Liao.

Body excerpt: This PR specifies and verifies \`spqr::serialize::{impl core::clone::Clone for spqr::serialize::Error}::clone\` in \`serialize.rs\`. The \`Clone\` implementation is derived by \`#\[derive(Clone)\]\` on the fieldless enum \`serialize::Error\`. Since the enum carries no data, the clone is exactly the input value. The spec theorem \`clone\_spec\` states that the call always succeeds (no panic) and returns a value equal to its input …

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/330#pullrequestreview-4735426778) — truonghoangle (2026-07-20): (No text.)

### Item 331

**[Issue #331](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/331) — Specify and verify : \`spqr::encoding::polynomial::const\_polys\_to\_polys::closure::call\_mut\` in \`polynomial.rs\`**

Status: closed. Opened: 2026-07-20. Author: truonghoangle.

Body excerpt: encoding.polynomial.const\_polys\_to\_polys. closure.Insts.CoreOpsFunctionFnMutTupleSharedPolyConstPoly.call\_mut

No recorded comments or reviews.

### Item 332

**[PR #332](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/332) — Specify and verify : \`spqr::encoding::polynomial::const\_polys\_to\_polys::closure::call\_mut in \`polynomial.rs\`**

Status: merged. Opened: 2026-07-20. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::encoding::polynomial::const\_polys\_to\_polys::closure::call\_mut\` in \`polynomial.rs\` closes #331

Discussion and review record:

- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/332#discussion_r3619311677) — Zhang-Liao (2026-07-21; Spqr/Specs/Encoding/Polynomial/ConstPolysToPolys/CallMut.lean:17): \`open Aeneas Aeneas.Std\` is enough for the compilation of this file.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/332#pullrequestreview-4741079633) — Zhang-Liao (2026-07-21): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/332#discussion_r3619444423) — truonghoangle (2026-07-21; Spqr/Specs/Encoding/Polynomial/ConstPolysToPolys/CallMut.lean:17): I fixed it
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/332#pullrequestreview-4741257508) — truonghoangle (2026-07-21): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/332#pullrequestreview-4741605147) — Zhang-Liao (2026-07-21): (No text.)

### Item 333

**[Issue #333](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/333) — specify and verify: \`spqr::encoding::polynomial::const\_polys\_to\_polys::closure::call\_once\` in \`polynomial.rs\`**

Status: closed. Opened: 2026-07-20. Author: truonghoangle.

Body excerpt: /-- \[spqr::encoding::polynomial::const\_polys\_to\_polys::{impl core::ops::function::FnOnce,), spqr::encoding::polynomial::Poly&gt; for spqr::encoding::polynomial::const\_polys\_to\_polys::closure}::call\_once\]: Source: 'src/encoding/polynomial.rs', lines 466:19-466:34 -/

No recorded comments or reviews.

### Item 334

**[Issue #334](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/334) — Specify and verify : \`PolyDecoder::new\_with\_poly\_count\` closure \`call\_mut\` in \`polynomial.rs\`**

Status: closed. Opened: 2026-07-20. Author: truonghoangle.

Body excerpt: /-- \[spqr::encoding::polynomial::{spqr::encoding::polynomial::PolyDecoder}::new\_with\_poly\_count::{impl core::ops::function::FnMut&gt; for spqr::encoding::polynomial::{spqr::encoding::polynomial::PolyDecoder}::new\_with\_poly\_count::closure}::call\_mut\]: Source: 'src/encoding/polynomial.rs', lines 788:38-788:58 -/

No recorded comments or reviews.

### Item 335

**[Issue #335](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/335) — Specify and verify : \`PolyDecoder::new\_with\_poly\_count\` closure \`call\_once\` in \`polynomial.rs\`**

Status: closed. Opened: 2026-07-20. Author: truonghoangle.

Body excerpt: /-- \[spqr::encoding::polynomial::{spqr::encoding::polynomial::PolyDecoder}::new\_with\_poly\_count::{impl core::ops::function::FnOnce&gt; for spqr::encoding::polynomial::{spqr::encoding::polynomial::PolyDecoder}::new\_with\_poly\_count::closure}::call\_once\]: Source: 'src/encoding/polynomial.rs', lines 788:38-788:58 -/

No recorded comments or reviews.

### Item 336

**[PR #336](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/336) — Specify and verify : \`PolyDecoder::new\_with\_poly\_count\` closure \`call\_mut\` in \`polynomial.rs\`**

Status: merged. Opened: 2026-07-20. Author: truonghoangle.

Body excerpt: This PR specifies and verifies the \`call\_mut\` closure of \`PolyDecoder::new\_with\_poly\_count\` in \`polynomial.rs\`. Additionally, this PR makes the following changes: \* Replaces the axiom \`@\[rust\_fun "sorted\_vec::{sorted\_vec::SortedSet}::new"\] axiom sorted\_vec.SortedSet.new\` with a definition and a corresponding specification theorem. \* Replaces the following type axioms with definitions: \`@\[rust\_type …

Discussion and review record:

- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/336#discussion_r3620006988) — Zhang-Liao (2026-07-21; Spqr/Specs/Encoding/Polynomial/PolyDecoder/CallMut.lean:34): Shall we also state the \`result.1\` field, or can we just ignore it since it is an empty set?
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/336#pullrequestreview-4741994062) — Zhang-Liao (2026-07-21): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/336#discussion_r3620129291) — truonghoangle (2026-07-21; Spqr/Specs/Encoding/Polynomial/PolyDecoder/CallMut.lean:34): Thank you for your comments. I have added the postcondition and explained why I did not include it initially. The postcondition \`result.1 = alloc.vec.Vec.new Pt\` is needed despite not having information because it serves a specific purpose in the verification chain: \*\*What it says:\*\* The returned \`SortedSet Pt\` is an \*\*empty collection\*\*. Since \`SortedSet T = SortedVec T = Vec T\` (by the type definitions in …
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/336#pullrequestreview-4742142627) — truonghoangle (2026-07-21): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/336#pullrequestreview-4742604769) — Zhang-Liao (2026-07-21): (No text.)

### Item 337

**[PR #337](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/337) — Specify and verify: \`spqr::encoding::polynomial::{impl PartialEq for Pt}::eq\` in \`polynomial.rs\`**

Status: merged. Opened: 2026-07-21. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::encoding::polynomial::{impl PartialEq for Pt}::eq\` in \`polynomial.rs\` closes #323

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/337#pullrequestreview-4750514219) — Zhang-Liao (2026-07-22): (No text.)

### Item 338

**[PR #338](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/338) — Specify and verify : \`PolyDecoder::new\_with\_poly\_count\` closure \`call\_once\` in \`polynomial.rs\`**

Status: merged. Opened: 2026-07-21. Author: truonghoangle.

Body excerpt: This PR specifies and verifies : \`PolyDecoder::new\_with\_poly\_count\` closure \`call\_once\` in \`polynomial.rs\` closes #335

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/338#pullrequestreview-4751744815) — Zhang-Liao (2026-07-22): (No text.)

### Item 339

**[PR #339](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/339) — Specify and verify: \`spqr::v1::chunked::states::serialize::decode\_varint\` in \`v1/chunked/states/serialize.rs\`**

Status: merged. Opened: 2026-07-21. Author: Zhang-Liao.

Body excerpt: Closes #312 Adds \`Spqr/Specs/V1/Chunked/States/Serialize/DecodeVarint.lean\` with three \`@\[step\]\` spec theorems, proving both the Rust \`#\[hax\_lib::ensures\]\` cursor contract \*\*and functional correctness\*\* of the LEB128 decoder. ## Pure model \`\`\`lean def varintVal (bytes : List Std.U8) (start : ℕ) : ℕ → ℕ | 0 =&gt; 0 | n + 1 =&gt; varintVal bytes start n + (bytes\[start + n\]!.val % 128) \* 2 ^ (7 \* n) \`\`\` ## Spec theorems - …

Discussion and review record:

- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/339#pullrequestreview-4761248800) — truonghoangle (2026-07-23): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/339#discussion_r3635935066) — truonghoangle (2026-07-23; Spqr/Specs/V1/Chunked/States/Serialize/DecodeVarint.lean:285): Great job! Could you explain the appearance of the number \`10\` here? It doesn't seem natural to me.
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/339#discussion_r3636400467) — Zhang-Liao (2026-07-23; Spqr/Specs/V1/Chunked/States/Serialize/DecodeVarint.lean:285): The 10 comes straight from the Rust source, which bounds the decode loop via \`max\_i = min(MAX\_VARINT\_BYTES\_LEN, from.len() - start\_at)\`. And that constant is the natural bound for a LEB128-encoded u64: each byte carries 7 payload bits (the 8th bit is the continuation flag), so encoding 64 bits needs at most \`⌈64 / 7⌉ = 10\` bytes. Nine bytes only hold 63 bits, which isn't enough; ten hold 70, which is. So the spec's …
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/339#pullrequestreview-4761882964) — Zhang-Liao (2026-07-23): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/339#discussion_r3636433776) — truonghoangle (2026-07-23; Spqr/Specs/V1/Chunked/States/Serialize/DecodeVarint.lean:285): Thank you for your explanation!
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/339#pullrequestreview-4761927065) — truonghoangle (2026-07-23): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/339#pullrequestreview-4761928320) — truonghoangle (2026-07-23): (No text.)

### Item 340

**[PR #340](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/340) — e2e PoC for FC+protocol models**

Status: closed unmerged. Opened: 2026-07-21. Author: a-dangelo.

Body excerpt: This draft PR is implementing a PoC for something that goes into the direction of formally verify end to end the rust code in libsignal, using the transpiled code from Aeneas and the 'models' we formalised starting from theory, papers, open standards, etc. I tried to make it as self contained as possible, and again it's not the end 'correctness' result we need for the incremental ml-kem, but the Correctness.lean …

No recorded comments or reviews.

### Item 341

**[PR #341](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/341) — specify and verify: \`spqr::encoding::polynomial::const\_polys\_to\_polys::closure::call\_once\` in \`polynomial.rs\`**

Status: merged. Opened: 2026-07-22. Author: truonghoangle.

Body excerpt: This PR specifies and verifies: \`spqr::encoding::polynomial::const\_polys\_to\_polys::closure::call\_once\` in \`polynomial.rs\` closes #333

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/341#pullrequestreview-4760277255) — Zhang-Liao (2026-07-23): (No text.)

### Item 342

**[PR #342](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/342) — Specify and verify: \`spqr::encoding::polynomial::PolyDecoder::new\_with\_poly\_count\` in \`polynomial.rs\`**

Status: merged. Opened: 2026-07-22. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::encoding::polynomial::PolyDecoder::new\_with\_poly\_count\` in \`polynomial.rs\` closes #258

Discussion and review record:

- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/342#discussion_r3635249344) — Zhang-Liao (2026-07-23; Spqr/Specs/Encoding/Polynomial/PolyDecoder/NewWithPolyCount.lean:22): I confirm the nolinter attribute is not needed.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/342#pullrequestreview-4760391969) — Zhang-Liao (2026-07-23): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/342#discussion_r3635881800) — truonghoangle (2026-07-23; Spqr/Specs/Encoding/Polynomial/PolyDecoder/NewWithPolyCount.lean:22): I fixed it. Thanks!
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/342#pullrequestreview-4761179787) — truonghoangle (2026-07-23): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/342#pullrequestreview-4761189453) — Zhang-Liao (2026-07-23): (No text.)

### Item 343

**[PR #343](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/343) — Specify and verify : \`MessageType::try\_from\` (TryFrom impl) in \`v1/chunked/states/serialize.rs\`**

Status: merged. Opened: 2026-07-23. Author: Zhang-Liao.

Body excerpt: Closes #311. ## Summary Specifies and verifies \`MessageType::try\_from\` (\`TryFrom for MessageType\` in \`src/v1/chunked/states/serialize.rs\`) over the \*\*full\*\* \`u8\` input range: - For \`value ≤ 6\` the result is \`Ok\` of the variant with that discriminant (\`0 ↦ None\`, \`1 ↦ Hdr\`, \`2 ↦ Ek\`, \`3 ↦ EkCt1Ack\`, \`4 ↦ Ct1Ack\`, \`5 ↦ Ct1\`, \`6 ↦ Ct2\`), i.e. \`try\_from\` is a left inverse of \`From for u8\`. - For \`value &gt; 6\` the result …

Discussion and review record:

- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/343#discussion_r3643305330) — truonghoangle (2026-07-24; SrcTranslated/FunsExternal.lean:1487): Why do you need to write this lemma instead of putting the proof directly into the spec theorem? Wouldn't it be more applicable later?
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/343#pullrequestreview-4770596705) — truonghoangle (2026-07-24): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/343#discussion_r3644300239) — Zhang-Liao (2026-07-24; SrcTranslated/FunsExternal.lean:1487): Thanks for the suggestion! I have moved it inside the specification theorem.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/343#pullrequestreview-4771886299) — Zhang-Liao (2026-07-24): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/343#pullrequestreview-4771961490) — truonghoangle (2026-07-24): (No text.)

### Item 344

**[Issue #344](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/344) — Shows that \`collect\` on \`Map\` equals calling \`FromIterator.from\_iter\` in \`polynomial.rs\`**

Status: closed. Opened: 2026-07-23. Author: truonghoangle.

Body excerpt: \`Map\` lazily applies \`F\` to each element of iterator \`I\`. \`collect\` drives iteration to completion, assembling results into a collection \`B1\` via \`FromIterator\`. It works in two stages: 1. \*\*Map-iterator construction\*\* — \`mapIteratorTransformer\` wraps \`I\` so that \`next\` applies \`FnMut.call\_mut\` with closure \`map.f\` to each yielded item. 2. \*\*Collection\*\* — the transformed iterator is passed to …

No recorded comments or reviews.

### Item 345

**[PR #345](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/345) — Shows that collect on Map equals calling FromIterator.from\_iter in polynomial.rs**

Status: merged. Opened: 2026-07-23. Author: truonghoangle.

Body excerpt: This PR shows that \`collect\` on \`Map\` equals calling \`FromIterator.from\_iter\` in \`polynomial.rs\`. \`Map\` lazily applies \`F\` to each element produced by iterator \`I\`. The \`collect\` operation drives this iteration to completion and assembles the resulting elements into a collection \`B1\` using \`FromIterator\`. The process has two stages: 1. \*\*Map-iterator construction.\*\* \`mapIteratorTransformer\` wraps \`I\` so that each …

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/345#issuecomment-5056543722) — Zhang-Liao (2026-07-23): The function \`collect\` does not exist in the function \`polynomial.rs\`. I think the specification theorem should be put in the directory \`Spqr/Specs/Aeneas\`.
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/345#issuecomment-5056791029) — truonghoangle (2026-07-23): I agree with your point of view. That was my initial thought as well.
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/345#issuecomment-5058070633) — Zhang-Liao (2026-07-23): Why do you change your initial decision to not put the file in \`Spqr/Specs/Aeneas\`?
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/345#issuecomment-5058249586) — truonghoangle (2026-07-23): Because the purpose of this is to provide a proof within \`const\_polys\_to\_polys\`.
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/345#issuecomment-5058645001) — Zhang-Liao (2026-07-23): I think we can put it here first. We can move it to \`Spqr/Specs/Aeneas\` if the specification is needed for another file/function.
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/345#pullrequestreview-4764236579) — Zhang-Liao (2026-07-23): (No text.)

### Item 346

**[PR #346](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/346) — Specify and verify : \`spqr::encoding::polynomial::{impl Decoder for PolyDecoder}::new\` in \`polynomial.rs\`**

Status: merged. Opened: 2026-07-23. Author: truonghoangle.

Body excerpt: This PR specifies and verifies : \`spqr::encoding::polynomial::{impl Decoder for PolyDecoder}::new\` in \`polynomial.rs\` closes #261

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/346#pullrequestreview-4770533442) — Zhang-Liao (2026-07-24): (No text.)

### Item 347

**[Issue #347](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/347) — Implementation of the \`Map Iterator Transformer\` in \`polynomial.rs\`**

Status: closed. Opened: 2026-07-23. Author: truonghoangle.

Body excerpt: \`Map\` lazily applies \`F\` to each element produced by iterator \`I\`. The \`mapIteratorTransformer\` first calls \`I.next\`, then applies \`FnMut.call\_mut\` using \`map.f\` to each yielded item. It composes \`iterInst.next\` with \`FnMut.call\_mut\`: it returns \`none\` when the iterator is exhausted and \`some (f val)\` otherwise.

No recorded comments or reviews.

### Item 348

**[PR #348](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/348) — Implementation of the \`Map Iterator Transformer\` in \`polynomial.rs\`**

Status: merged. Opened: 2026-07-23. Author: truonghoangle.

Body excerpt: This PR verifies Map Iterator Transformer\` in \`polynomial.rs\`. \`Map\` lazily applies \`F\` to each element produced by iterator \`I\`. The \`mapIteratorTransformer\` first calls \`I.next\`, then applies \`FnMut.call\_mut\` using \`map.f\` to each yielded item. It composes \`iterInst.next\` with \`FnMut.call\_mut\`: it returns \`none\` when the iterator is exhausted and \`some (f val)\` otherwise. closes #347

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/348#pullrequestreview-4770751531) — Zhang-Liao (2026-07-24): (No text.)

### Item 349

**[PR #349](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/349) — Specify and verify: \`spqr::encoding::polynomial::PolyDecoder::get\_pts\_needed\` in \`polynomial.rs\`**

Status: merged. Opened: 2026-07-24. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::encoding::polynomial::PolyDecoder::get\_pts\_needed\` in \`polynomial.rs\` closes #256

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/349#pullrequestreview-4781225768) — Zhang-Liao (2026-07-26): (No text.)

### Item 350

**[Issue #350](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/350) — Specify and verify \`core::slice::{\[@T\]}::iter\`**

Status: closed. Opened: 2026-07-24. Author: truonghoangle.

Body excerpt: Need show that \`core.slice.Slice.iter\` constructs an iterator over a slice \`s\` with: - the original \`slice\` preserved unchanged; - the iterator \`index\` initialized to \`0\`. In other words, for any slice \`s\`, the result is \`ok ⟨s, 0⟩\`.

No recorded comments or reviews.

### Item 351

**[PR #351](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/351) — Specify and verify \`core::slice::{\[@T\]}::iter\`**

Status: merged. Opened: 2026-07-24. Author: truonghoangle.

Body excerpt: This PR showed that \`core.slice.Slice.iter\` constructs an iterator over a slice \`s\` with: - the original \`slice\` preserved unchanged; - the iterator \`index\` initialized to \`0\`. In other words, for any slice \`s\`, the result is \`ok ⟨s, 0⟩\`. closes #350

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/351#pullrequestreview-4781232290) — Zhang-Liao (2026-07-26): (No text.)

### Item 352

**[Issue #352](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/352) — specify and verify \`collect\`specialized to \`const\_polys\_to\_polys\` in \`polynomial.rs\`**

Status: closed. Opened: 2026-07-26. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 353

**[PR #353](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/353) — specify and verify \`collect\` specialized to \`const\_polys\_to\_polys\` in \`polynomial.rs\`**

Status: merged. Opened: 2026-07-26. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`collect\` specialized to \`const\_polys\_to\_polys\` in \`polynomial.rs\` The \`iterToList\` call using \`mapIteratorTransformer\` with state \`Iter (PolyConst N)\` produces the same result as the custom \`MapIterT N\` instance, since the \`const\_polys\_to\_polys\` closure state is never modified by \`call\_mut\`. This establishes the connection between the generic \`collect\_spec\` unfolding, which uses …

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/353#pullrequestreview-4785469321) — Zhang-Liao (2026-07-27): (No text.)

### Item 354

**[PR #354](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/354) — Specify and verify \`spqr::encoding::polynomial::PolyDecoder::necessary\_points\` in \`polynomial.rs\`**

Status: merged. Opened: 2026-07-26. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::encoding::polynomial::PolyDecoder::necessary\_points\` in \`polynomial.rs\` closes #257

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/354#pullrequestreview-4794737961) — Zhang-Liao (2026-07-28): (No text.)

### Item 355

**[PR #355](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/355) — Specify and verify: \`spqr::v1::chunked::states::serialize::encode\_varint\`**

Status: merged. Opened: 2026-07-27. Author: Zhang-Liao.

Body excerpt: Closes #311. Specifies and verifies \`spqr::v1::chunked::states::serialize::encode\_varint\` (\`src/v1/chunked/states/serialize.rs\`, lines 139–149), the LEB128-style varint encoder. ## Pure model \`varintBytes : ℕ → List ℕ\`, \`if a u64::MAX\`). Standard axioms only. \`lake build Spqr.Specs.V1.Chunked.States.Serialize.EncodeVarint\` succeeds against current \`main\`.

Discussion and review record:

- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/355#discussion_r3655841064) — truonghoangle (2026-07-27; Spqr/Specs/V1/Chunked/States/Serialize/EncodeVarint.lean:75): why do we need example in file?
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/355#pullrequestreview-4785453313) — truonghoangle (2026-07-27): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/355#discussion_r3655853067) — truonghoangle (2026-07-27; Spqr/Specs/V1/Chunked/States/Serialize/EncodeVarint.lean:248): We need to remove unnecessary prefixes like \`Std.\`
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/355#pullrequestreview-4785468485) — truonghoangle (2026-07-27): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/355#discussion_r3663447357) — Zhang-Liao (2026-07-28; Spqr/Specs/V1/Chunked/States/Serialize/EncodeVarint.lean:75): Thanks, it is not needed. I have removed it.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/355#pullrequestreview-4794624232) — Zhang-Liao (2026-07-28): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/355#discussion_r3663484741) — Zhang-Liao (2026-07-28; Spqr/Specs/V1/Chunked/States/Serialize/EncodeVarint.lean:248): Thanks! I have removed all \`Std.\` in \`Spqr/Specs/V1/Chunked/States/Serialize/EncodeVarint.lean\`.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/355#pullrequestreview-4794670875) — Zhang-Liao (2026-07-28): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/355#pullrequestreview-4795085557) — truonghoangle (2026-07-28): (No text.)

### Item 356

**[PR #356](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/356) — Specify and verify: \`spqr::encoding::polynomial::const\_polys\_to\_polys\` in \`polynomial.rs\`**

Status: merged. Opened: 2026-07-27. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::encoding::polynomial::const\_polys\_to\_polys\` in \`polynomial.rs\`. It also replaces the axiom \`core.iter.traits.iterator.Iterator.map.default\` with a definition and a corresponding specification theorem. Due to \[Aeneas issue #1043\](https://github.com/AeneasVerif/aeneas/issues/1043), the \`Map.Insts\` implementation currently has \`next := sorry\`. Consequently, the bridge between the …

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/356#issuecomment-5090417903) — github-actions[bot] (2026-07-27): ### Sorry Delta — hand-written specs \*\*3 new sorry-tainted declarations in \`Spqr.Specs.\*\`:\*\* | Module | Declaration | Kind | |--------|-------------|------| | \`Spqr.Specs.Encoding.Polynomial.ConstPolysToPolys\` | \`\_private.Spqr.Specs.Encoding.Polynomial.ConstPolysToPolys.0.spqr.encoding.polynomial.collect\_default\_bridge\` | direct | | \`Spqr.Specs.Encoding.Polynomial.ConstPolysToPolys\` | …
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/356#discussion_r3663682064) — Zhang-Liao (2026-07-28; Spqr/Specs/Encoding/Polynomial/ConstPolysToPolys.lean:53): Please add the type of \`result\`
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/356#pullrequestreview-4794936091) — Zhang-Liao (2026-07-28): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/356#discussion_r3663690125) — Zhang-Liao (2026-07-28; Spqr/Specs/Encoding/Polynomial/ConstPolysToPolys.lean:6): \`import Spqr.Specs.Encoding.Polynomial.ConstPolysToPolys.CallOnce\` is not needed for the compilation
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/356#pullrequestreview-4794948355) — Zhang-Liao (2026-07-28): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/356#discussion_r3664913837) — truonghoangle (2026-07-28; Spqr/Specs/Encoding/Polynomial/ConstPolysToPolys.lean:53): I fixed it
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/356#pullrequestreview-4796487196) — truonghoangle (2026-07-28): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/356#discussion_r3664914419) — truonghoangle (2026-07-28; Spqr/Specs/Encoding/Polynomial/ConstPolysToPolys.lean:6): I fixed it
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/356#pullrequestreview-4796487914) — truonghoangle (2026-07-28): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/356#pullrequestreview-4796533440) — Zhang-Liao (2026-07-28): (No text.)

### Item 357

**[Issue #357](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/357) — Temporary \`sorry\` in the \`collect\` Specification Bridge**

Status: closed. Opened: 2026-07-27. Author: truonghoangle.

Body excerpt: the bridge between the Aeneas-generated collect.default theorem and the external Map.Insts.collect theorem- which uses the proper mapIteratorTransformer- must currently be left as sorry. PR #356

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/357#issuecomment-6185400060) — truonghoangle (2026-10-15): This issue has been resolved in PR #660 by @oliver-butterley.

### Item 358

**[PR #358](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/358) — Simplify the \`collect\` proof for \`const\_polys\_to\_polys\` (321 → 152 lines)**

Status: merged. Opened: 2026-07-27. Author: Zhang-Liao.

Body excerpt: Closes #360. Same theorem, same imports, no new axioms — the proof of \`Spqr/Specs/Encoding/Polynomial/ConstPolysToPolys/SliceIterMapCollect.lean\` goes from \*\*321 to 152 lines\*\*. ## What changed #353 proves the inductive characterisation twice: 1. \`iterToList\_map\_acc\` (~95 lines) — about an \*\*abstract\*\* \`Iterator (MapIterT N) Poly\` instance, taken as a parameter together with a 12-line \`h\_next\` hypothesis pinning …

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/358#pullrequestreview-4795467651) — truonghoangle (2026-07-28): (No text.)

### Item 359

**[PR #359](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/359) — Update aeneas 6e167c9b**

Status: merged. Opened: 2026-07-27. Author: oliver-butterley.

Body excerpt: Updates to Aeneas version 6e167c9b, very minor change of proofs required.

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/359#pullrequestreview-4789941921) — truonghoangle (2026-07-27): (No text.)

### Item 360

**[Issue #360](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/360) — Refactoring notes for #358: \`iterToList\_map\_acc\` → \`iterToList\_trans\`**

Status: closed. Opened: 2026-07-28. Author: Zhang-Liao.

Body excerpt: Notes on the refactoring carried out in #358, for \`Spqr/Specs/Encoding/Polynomial/ConstPolysToPolys/SliceIterMapCollect.lean\` (321 → 152 lines). ## The idea The old \`iterToList\_map\_acc\` carries the iterator around as an \*\*abstract parameter plus a hypothesis\*\*, so every unfolding step has to re-derive how \`next\` behaves and how the state was rebuilt. The new \`iterToList\_trans\` states the induction about the …

No recorded comments or reviews.

### Item 361

**[PR #361](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/361) — Specify and verify: \`spqr::v1::chunked::states::serialize::encode\_chunk\` in \`v1/chunked/states/serialize.rs\`**

Status: merged. Opened: 2026-07-28. Author: Zhang-Liao.

Body excerpt: This PR specifies and verifies \`spqr::v1::chunked::states::serialize::encode\_chunk\` (\`src/v1/chunked/states/serialize.rs\`, lines 184-188), the serializer that appends the wire encoding of a \`Chunk\` to a byte buffer. A chunk is a 16-bit index plus a fixed 32-byte payload, and it goes on the wire as \`varint(index) ++ data\`. The spec theorem \`encode\_chunk\_spec\` concludes that \`encode\_chunk c into\` succeeds and returns …

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/361#issuecomment-5105914375) — truonghoangle (2026-07-28): Great job! Could the lemmas related to \`varintBytes\` be set aside and considered in a generalized state and potentially applied further? &gt; No \`sorry\`, no new axioms: beyond the standard three, the theorem depends only on the &gt; pre-existing extracted-model axioms \`RangeFull...get\_unchecked{,\_mut}\` in &gt; \`SrcTranslated/FunsExternal.lean\`, pulled in by the \`RangeFull\` slice-index instance. The axiom &gt; closures of …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/361#issuecomment-5112621692) — Zhang-Liao (2026-07-29): &gt; Could the lemmas related to varintBytes be set aside and considered in a generalized state and potentially applied further? The lemmas can be rewritten to a more generalized form. The lemmas \`varintBytes\_length\_le\_three\` and \`\_le\_ten\` are one-line instantiations of \`varintBytes\_length\_le : ∀ n a, 1 ≤ n → a Could you please clarify this comment? I created a file\`Spqr/Specs/Aeneas/IndexRangeFull.lean\` that contains …
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/361#pullrequestreview-4804722295) — truonghoangle (2026-07-29): (No text.)

### Item 362

**[PR #362](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/362) — Specify and verify \`spqr::encoding::polynomial::PolyDecoder::into\_pb\` in \`polynomial.rs\`**

Status: merged. Opened: 2026-07-28. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::encoding::polynomial::PolyDecoder::into\_pb\` in \`polynomial.rs\`. It also replaces the following two \`axioms\` with verified definitions and corresponding specification theorems: \`sorted\_vec::{core::ops::deref::Deref, alloc::vec::Vec&gt;}::deref\` \`sorted\_vec::{core::ops::deref::Deref, sorted\_vec::SortedVec&gt;}::deref\` closes #259

Discussion and review record:

- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/362#pullrequestreview-4805506235) — Zhang-Liao (2026-07-29): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/362#discussion_r3672175720) — Zhang-Liao (2026-07-29; Spqr/Specs/Encoding/Polynomial/PolyDecoder/IntoPb.lean:286): Shouldn't we add the attribute \`\[step\]\`?
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/362#pullrequestreview-4805535614) — Zhang-Liao (2026-07-29): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/362#discussion_r3672196887) — Zhang-Liao (2026-07-29; SrcTranslated/FunsExternal.lean:2021): The implementation returns \`fun sv =&gt; ok sv\` not the default inhabitant.
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/362#discussion_r3672265809) — Zhang-Liao (2026-07-29; Spqr/Specs/Encoding/Polynomial/PolyDecoder/IntoPb.lean:24): Both instances above already exist. One is in \`PolyDecoder/NewWithPolyCount.lean:22\` and the other is in \`instInhabitedPt\_spqr(Spqr/Math/Poly/Basic/Defs.lean:32\`. I see such duplicated implementations of instances multiple times. Shall we add all such instances into a particular file for reuse? If you agree, we can first merge and then open another issue to discuss where to put all such instances.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/362#pullrequestreview-4805626126) — Zhang-Liao (2026-07-29): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/362#discussion_r3672353865) — truonghoangle (2026-07-29; Spqr/Specs/Encoding/Polynomial/PolyDecoder/IntoPb.lean:286): I added \[step\].
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/362#pullrequestreview-4805749877) — truonghoangle (2026-07-29): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/362#discussion_r3672355777) — truonghoangle (2026-07-29; SrcTranslated/FunsExternal.lean:2021): I rewrite comments.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/362#pullrequestreview-4805752720) — truonghoangle (2026-07-29): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/362#discussion_r3672384445) — truonghoangle (2026-07-29; Spqr/Specs/Encoding/Polynomial/PolyDecoder/IntoPb.lean:24): Yes, I agree with you that we will add all such instances into a particular file. I couldn't remember if it actually existed, or if I remembered it existed, I couldn't remember where it was located, and searching for it was very time-consuming for me, so your solution is perfect. Thank you for your suggestion.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/362#pullrequestreview-4805793556) — truonghoangle (2026-07-29): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/362#pullrequestreview-4805884403) — Zhang-Liao (2026-07-29): (No text.)

### Item 363

**[PR #363](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/363) — Specify and verify : \`spqr::encoding::polynomial::Poly::from\_complete\_points\` in \`polynomial.rs\`**

Status: merged. Opened: 2026-07-28. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::encoding::polynomial::Poly::from\_complete\_points\` in \`polynomial.rs\` closes #135

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/363#issuecomment-5105890173) — github-actions[bot] (2026-07-28): ### Sorry Delta — hand-written specs \*\*18 new sorry-tainted declarations in \`Spqr.Specs.\*\`:\*\* | Module | Declaration | Kind | |--------|-------------|------| | \`Spqr.Specs.Encoding.Polynomial.Poly.FromCompletePoints\` | \`\_private.Spqr.Specs.Encoding.Polynomial.Poly.FromCompletePoints.0.spqr.encoding.polynomial.Poly.from\_complete\_points\_loop.body\_spec\_none\_0\` | transitive | | …
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/363#discussion_r3672904962) — Zhang-Liao (2026-07-29; Spqr/Specs/Encoding/Polynomial/Poly/FromCompletePoints.lean:14): The docstring is incomplete. We need the source of the function and the natural language description of the function.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/363#pullrequestreview-4806476283) — Zhang-Liao (2026-07-29): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/363#discussion_r3673020465) — Zhang-Liao (2026-07-29; Spqr/Specs/Encoding/Polynomial/Poly/FromCompletePoints.lean:545): I feel it is not reasonable to use the capitalized \`N\` here. Moreover, \`not\` is not meaningful. I think \`from\_complete\_points\_spec\_of\_invalid\_index\` is more self-contained.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/363#pullrequestreview-4806622231) — Zhang-Liao (2026-07-29): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/363#discussion_r3673062981) — truonghoangle (2026-07-29; Spqr/Specs/Encoding/Polynomial/Poly/FromCompletePoints.lean:14): I will add comments
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/363#pullrequestreview-4806678344) — truonghoangle (2026-07-29): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/363#discussion_r3673064756) — truonghoangle (2026-07-29; Spqr/Specs/Encoding/Polynomial/Poly/FromCompletePoints.lean:545): I will fix it
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/363#pullrequestreview-4806680645) — truonghoangle (2026-07-29): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/363#pullrequestreview-4808224627) — Zhang-Liao (2026-07-29): (No text.)

### Item 364

**[Issue #364](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/364) — Consolidate \`Inhabited\` instances into \`Spqr/Auxiliary/Instances.lean\`**

Status: open. Opened: 2026-07-29. Author: Zhang-Liao.

Body excerpt: There is currently no single home for typeclass instances, so each spec file declares the ones it needs at the top. This has already produced one redundant instance and is a recurring source of duplication in review. ## Current state All six instances in the project are \`Inhabited\`, and every one of them exists only so that \`getElem!\` notation (\`xs\[j\]!\`) elaborates: | Location | Instance | |---|---| | …

No recorded comments or reviews.

### Item 365

**[PR #365](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/365) — Specify and verify: \`spqr::encoding::polynomial::PolyDecoder::from\_pb\` in \`polynomial.rs\`**

Status: merged. Opened: 2026-07-29. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::encoding::polynomial::PolyDecoder::from\_pb\` in \`polynomial.rs\` It also replaces the following two \`axioms\` with verified definitions and corresponding specification theorems: \`sorted\_vec.SortedSet.push\` and \`sorted\_vec.SortedSet.with\_capacity\` closes #260

Discussion and review record:

- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/365#discussion_r3679471029) — Zhang-Liao (2026-07-30; SrcTranslated/FunsExternal.lean:2212): The definition of \`push\` appears to be wrong even if we ignore the sort invariants. It simply appends an element to the end of the list. However, elements in a sorted set should be sorted, and no duplicates are allowed to exist. Especially when an element is equal to the last element: replace the last element, return (len-1, Some(old element)) — the length stays unchanged. The current implementation changes the …
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/365#pullrequestreview-4814682069) — Zhang-Liao (2026-07-30): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/365#discussion_r3679569648) — Zhang-Liao (2026-07-30; Spqr/Specs/Encoding/Polynomial/PolyDecoder/FromPb.lean:580): We should add the \`@\[step\]\` attribute.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/365#pullrequestreview-4814796732) — Zhang-Liao (2026-07-30): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/365#discussion_r3679749975) — Zhang-Liao (2026-07-30; Spqr/Specs/Encoding/Polynomial/PolyDecoder/FromPb.lean:607): I think you also need to add the condition of \`(vs 0).val = \[ \]\` here. Since we have constraints \`(vs (k+1)).val = (vs k).val ++ \[p\_k\]\`, \`vs n = v\_final\`, and \`v\_final.val = (vs 0).val ++ \[p\_0, p\_1, …, p\_{n-1}\]\`. If we do not give any constraint to \`vs 0 = \[ \]\`, \`vs\_final\` can be \`v\_final.val = 500 ++ \[p\_0, p\_1, …, p\_{n-1}\]\`, which seems to be different from the Rust implementaiton.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/365#pullrequestreview-4815009125) — Zhang-Liao (2026-07-30): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/365#discussion_r3684545401) — truonghoangle (2026-07-30; SrcTranslated/FunsExternal.lean:2212): Thank you for your comments. I fixed it
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/365#pullrequestreview-4821125838) — truonghoangle (2026-07-30): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/365#discussion_r3684547641) — truonghoangle (2026-07-30; Spqr/Specs/Encoding/Polynomial/PolyDecoder/FromPb.lean:580): I fixed it
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/365#pullrequestreview-4821128594) — truonghoangle (2026-07-30): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/365#discussion_r3685039738) — truonghoangle (2026-07-30; Spqr/Specs/Encoding/Polynomial/PolyDecoder/FromPb.lean:607): I added the condition which you suggest.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/365#pullrequestreview-4821745999) — truonghoangle (2026-07-30): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/365#pullrequestreview-4824497209) — Zhang-Liao (2026-07-31): (No text.)

### Item 366

**[Issue #366](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/366) — Specify and verify : \`PolyEncoder::point\_at\` closure \`call\_mut\` in \`polynomial.rs\`**

Status: closed. Opened: 2026-07-29. Author: truonghoangle.

Body excerpt: The Rust method \`PolyEncoder::point\_at\` (in \`src/encoding/polynomial.rs\`, lines 633–660) converts an array of \`Point\`s (evaluation-data vectors) into polynomials for later evaluation. During this process, each \`Point\`'s inner \`Vec\` is enumerated and mapped through a closure (lines 641:25–644:21): \`\`\` .map(|(x, y)| Pt { x: GF16::new(x as u16), y: \*y, }) \`\`\` This closure converts an enumerated \`(usize, &amp;GF16)\` pair - …

No recorded comments or reviews.

### Item 367

**[Issue #367](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/367) — Specify and verify : \`PolyEncoder::point\_at\` closure \`call\_once\` in \`polynomial.rs\`**

Status: closed. Opened: 2026-07-29. Author: truonghoangle.

Body excerpt: The Rust method \`PolyEncoder::point\_at\` (in \`src/encoding/polynomial.rs\`, lines 633–660) converts an array of \`Point\`s (evaluation-data vectors) into polynomials for later evaluation. During this process, each \`Point\`'s inner \`Vec\` is enumerated and mapped through a closure (lines 641:25–644:21): \`\`\` .map(|(x, y)| Pt { x: GF16::new(x as u16), y: \*y, }) \`\`\` This closure converts an enumerated \`(usize, &amp;GF16)\` pair — …

No recorded comments or reviews.

### Item 368

**[PR #368](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/368) — Specify and verify : \`PolyEncoder::point\_at\` closure \`call\_mut\` in \`polynomial.rs\`**

Status: merged. Opened: 2026-07-29. Author: truonghoangle.

Body excerpt: This PR specifies and verifies : \`PolyEncoder::point\_at\` closure \`call\_mut\` in \`polynomial.rs\` closes #366

Discussion and review record:

- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/368#discussion_r3687637271) — Zhang-Liao (2026-07-31; Spqr/Specs/Encoding/Polynomial/PolyEncoder/PointAt/CallMut.lean:45): The proof can be completed after \`simp only \[\] at h ⊢\` is removed. It is hence unnecessary.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/368#pullrequestreview-4824945391) — Zhang-Liao (2026-07-31): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/368#discussion_r3688221885) — truonghoangle (2026-07-31; Spqr/Specs/Encoding/Polynomial/PolyEncoder/PointAt/CallMut.lean:45): I fixed it. thank you for your comments
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/368#pullrequestreview-4825677481) — truonghoangle (2026-07-31): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/368#pullrequestreview-4825694641) — Zhang-Liao (2026-07-31): (No text.)

### Item 369

**[PR #369](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/369) — Specify and verify: \`spqr::v1::chunked::states::serialize::decode\_chunk\` in \`v1/chunked/states/serialize.rs\`**

Status: merged. Opened: 2026-07-30. Author: Zhang-Liao.

Body excerpt: Closes #314 ## Summary Adds \`Spqr/Specs/V1/Chunked/States/Serialize/DecodeChunk.lean\` with the spec theorem \`decode\_chunk\_spec\`, proving functional correctness of \`decode\_chunk\`: - \*\*Cursor contract\*\*: the cursor never moves backwards; on success it ends at \`at + n + 32 ≤ from.len()\`, where \`n\` (\`1 ≤ n ≤ 10\`) is the number of varint bytes consumed by \`decode\_varint\`. - \*\*Index\*\*: \`c.index.val\` is the LEB128 decoding …

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/369#issuecomment-5136794978) — truonghoangle (2026-07-30): The success branch does not explicitly capture the \`u16\` range check mentioned in the description. It only states the relation between \`c.index\` and the decoded varint value modulo \`2^64\`, which does not reflect the fact that the implementation rejects indices that cannot be represented as a \`u16\`. I suggest adding an explicit bound on the decoded value in the success case, for example: \`\`\`varintVal from1.val …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/369#issuecomment-5138158052) — Zhang-Liao (2026-07-31): The type of \`c.index\` is \`Std.U16\`. Hence, \`c.index.val &lt; 2^16\` can be automatically inferred from the type. I think we may not need to make such a change.
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/369#pullrequestreview-4825633980) — truonghoangle (2026-07-31): (No text.)

### Item 370

**[PR #370](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/370) — Specify and verify: \`spqr::v1::chunked::states::serialize::{spqr::v1::chunked::states::Message}::serialize\` in \`v1/chunked/states/serialize.rs\`**

Status: merged. Opened: 2026-07-31. Author: Zhang-Liao.

Body excerpt: This PR specifies and verifies \`spqr::v1::chunked::states::serialize::{spqr::v1::chunked::states::Message}::serialize\` (Lean: \`spqr.v1.chunked.states.serialize.Message.serialize\_spec\`). The spec proves functional correctness against the pure model \`messageBytes\`: the output is exactly \`\[version byte 1\] ++ varint(epoch) ++ varint(index) ++ \[message-type tag\]\`, followed by the chunk block \`varint(chunk.index) ++ …

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/370#pullrequestreview-4839290206) — truonghoangle (2026-08-02): (No text.)

### Item 371

**[PR #371](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/371) — Specify and verify : \`PolyEncoder::point\_at\` closure \`call\_once\` in \`polynomial.rs\`**

Status: merged. Opened: 2026-07-31. Author: truonghoangle.

Body excerpt: This PR specifies and verifies : \`PolyEncoder::point\_at\` closure \`call\_once\` in \`polynomial.rs\` closes #367

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/371#pullrequestreview-4840371089) — Zhang-Liao (2026-08-03): (No text.)

### Item 372

**[PR #372](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/372) — Specify and verify: \`spqr::v1::chunked::states::serialize::{spqr::v1::chunked::states::Message}::deserialize\` in \`v1/chunked/states/serialize.rs\`**

Status: merged. Opened: 2026-07-31. Author: Zhang-Liao.

Body excerpt: This PR specifies and verifies \`spqr::v1::chunked::states::serialize::{spqr::v1::chunked::states::Message}::deserialize\` (Lean: \`spqr.v1.chunked.states.serialize.Message.deserialize\_spec\`). On success (\`Ok (msg, index, at)\`) the spec proves that the consumed prefix \`from\[0 .. at)\` has exactly the wire layout produced by \`Message::serialize\`: \`\`\` \[version = 1\] ++ \[varint(epoch)\] ++ \[varint(index)\] ++ \[tag byte\] \`\`\` …

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/372#pullrequestreview-4850858764) — truonghoangle (2026-08-04): (No text.)
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/372#issuecomment-5174914349) — truonghoangle (2026-08-04): Well done! Viewed from a "hax" perspective, this theorem actually yields more properties than expected.

### Item 373

**[PR #373](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/373) — Specify and verify : \`spqr::encoding::polynomial::{impl Decoder for PolyDecoder}::add\_chunk\` in \`polynomial.rs\`**

Status: merged. Opened: 2026-08-02. Author: truonghoangle.

Body excerpt: This PR specifies and verifies : \`spqr::encoding::polynomial::{impl Decoder for PolyDecoder}::add\_chunk\` in \`polynomial.rs\` The proofs of the theorems are divided into several cases, based on the definition of the \`sorted\_vec.SortedSet.push\` function and the \`spqr::encoding::polynomial::{impl Decoder for PolyDecoder}::add\_chunk\` function itself. closes #262

Discussion and review record:

- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/373#discussion_r3701161751) — Zhang-Liao (2026-08-03; Spqr/Specs/Encoding/Polynomial/PolyDecoder/AddChunk.lean:208): The same \`h\_absurd\` helper is inlined seven times in the file. It is better to abstract it as a lemma.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/373#pullrequestreview-4840605778) — Zhang-Liao (2026-08-03): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/373#discussion_r3701301920) — truonghoangle (2026-08-03; Spqr/Specs/Encoding/Polynomial/PolyDecoder/AddChunk.lean:208): I extracted the repeated \`h\_absurd\` pattern into a private lemma \`Pt\_cmp\_exhaustive\` and replaced all 7 inline occurrences with calls to it.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/373#pullrequestreview-4840768571) — truonghoangle (2026-08-03): (No text.)
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/373#pullrequestreview-4841333597) — Zhang-Liao (2026-08-03): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/373#discussion_r3701769334) — Zhang-Liao (2026-08-03; Spqr/Specs/Encoding/Polynomial/PolyDecoder/AddChunk.lean:680): The postcondition gives only an upper bound on pts\[i\].len() (body\_pts\_length\_le), never a lower bound, because the \`selfs (j+1) = selfs j\` disjunct is unconditional. Since \`selfs (j+1) = selfs j\` means that an element is not inserted, the current specification blocks any compositional result over a sequence of \`add\_chunk\` calls — e.g. "after calling add\_chunk n times, decoded\_message returns Some rather than None". …
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/373#discussion_r3701815816) — Zhang-Liao (2026-08-03; Spqr/Specs/Encoding/Polynomial/PolyDecoder/AddChunk.lean:28): The theorem \`sortedInsert\_always\_ok\` is the same as that in \`FromPb.lean:29\`. It is better to put it in a shared upstream file. For instance, we can move it to a place near the theorem \`sortedInsert\_spec\` in \`FunsExternal.lean\`.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/373#pullrequestreview-4841393341) — Zhang-Liao (2026-08-03): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/373#discussion_r3707049286) — truonghoangle (2026-08-03; Spqr/Specs/Encoding/Polynomial/PolyDecoder/AddChunk.lean:680): I fixed it
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/373#pullrequestreview-4847801575) — truonghoangle (2026-08-03): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/373#discussion_r3707050597) — truonghoangle (2026-08-03; Spqr/Specs/Encoding/Polynomial/PolyDecoder/AddChunk.lean:28): I fixed it
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/373#pullrequestreview-4847803364) — truonghoangle (2026-08-03): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/373#pullrequestreview-4849609116) — Zhang-Liao (2026-08-04): (No text.)

### Item 374

**[PR #374](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/374) — Specify and verify: \`spqr::encoding::polynomial::PolyEncoder::point\_at\` in \`polynomial.rs\`**

Status: merged. Opened: 2026-08-03. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::encoding::polynomial::PolyEncoder::point\_at\` in \`polynomial.rs\` In this PR, we use the same \`sorry\` for the \`map\` + \`collect\` pipeline as in PR #357. Concretely, \`Iterator.collect.default\` on a \`Map (Enumerate (Iter GF16)) closure\_1\` equals \`FromIteratorVec.from\_iter\` with \`mapIteratorTransformer\`, using \`m.iter\` as initial state. The theorem \`map\_collect\_eq\_point\_at\` connects …

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/374#issuecomment-5171877144) — github-actions[bot] (2026-08-03): ### Sorry Delta — hand-written specs \*\*7 new sorry-tainted declarations in \`Spqr.Specs.\*\`:\*\* | Module | Declaration | Kind | |--------|-------------|------| | \`Spqr.Specs.Encoding.Polynomial.PolyEncoder.PointAt\` | \`\_private.Spqr.Specs.Encoding.Polynomial.PolyEncoder.PointAt.0.spqr.encoding.polynomial.PolyEncoder.point\_at\_loop.map\_collect\_eq\_point\_at\` | direct | | \`Spqr.Specs.Encoding.Polynomial.PolyEncoder.PointAt\` …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/374#issuecomment-5173429107) — Zhang-Liao (2026-08-04): I notice that there is a new axiom \`private theorem map\_collect\_eq\_point\_at\`. Do you intentionally leave the proof as a sorry?
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/374#issuecomment-5174800696) — truonghoangle (2026-08-04): @Zhang-Liao This PR uses the same \`sorry\` for the \`map\` + \`collect\` pipeline as PR #357. The theorem \`map\_collect\_eq\_point\_at\` bridges the Aeneas-generated code with the verified \`from\_iter\_point\_at\_spec\`. Therefore, resolving the issue in PR #357 will also resolve the issue in this PR. Once this PR is approved, I will create an issue for this problem.
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/374#pullrequestreview-4851012386) — Zhang-Liao (2026-08-04): (No text.)

### Item 375

**[Issue #375](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/375) — Verify : \`v1/unchunked/send\_ek/serialize.rs\`**

Status: closed. Opened: 2026-08-04. Author: Zhang-Liao.

Body excerpt: - \[x\] #376 - \[x\] #377 - \[x\] #378 - \[x\] #379 - \[x\] #380 - \[x\] #381 - \[x\] #382 - \[x\] #383

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/375#issuecomment-5187873125) — Zhang-Liao (2026-08-05): Closes it since all sub-issues have been completed.

### Item 376

**[Issue #376](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/376) — Specify and verify : \`spqr::v1::unchunked::send\_ek::serialize::{spqr::v1::unchunked::send\_ek::KeysUnsampled}::into\_pb\` in \`v1/unchunked/send\_ek/serialize.rs\`**

Status: closed. Opened: 2026-08-04. Author: Zhang-Liao.

Body excerpt: Parent: #375

No recorded comments or reviews.

### Item 377

**[Issue #377](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/377) — Specify and verify : \`spqr::v1::unchunked::send\_ek::serialize::{spqr::v1::unchunked::send\_ek::KeysUnsampled}::from\_pb\` in \`v1/unchunked/send\_ek/serialize.rs\`**

Status: closed. Opened: 2026-08-04. Author: Zhang-Liao.

Body excerpt: Parent: #375

No recorded comments or reviews.

### Item 378

**[Issue #378](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/378) — Specify and verify : \`spqr::v1::unchunked::send\_ek::serialize::{spqr::v1::unchunked::send\_ek::HeaderSent}::into\_pb\` in \`v1/unchunked/send\_ek/serialize.rs\`**

Status: closed. Opened: 2026-08-04. Author: Zhang-Liao.

Body excerpt: Parent: #375

No recorded comments or reviews.

### Item 379

**[Issue #379](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/379) — Specify and verify : \`spqr::v1::unchunked::send\_ek::serialize::{spqr::v1::unchunked::send\_ek::HeaderSent}::from\_pb\` in \`v1/unchunked/send\_ek/serialize.rs\`**

Status: closed. Opened: 2026-08-04. Author: Zhang-Liao.

Body excerpt: Parent: #375

No recorded comments or reviews.

### Item 380

**[Issue #380](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/380) — Specify and verify : \`spqr::v1::unchunked::send\_ek::serialize::{spqr::v1::unchunked::send\_ek::EkSent}::into\_pb\` in \`v1/unchunked/send\_ek/serialize.rs\`**

Status: closed. Opened: 2026-08-04. Author: Zhang-Liao.

Body excerpt: Parent: #375

No recorded comments or reviews.

### Item 381

**[Issue #381](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/381) — Specify and verify : \`spqr::v1::unchunked::send\_ek::serialize::{spqr::v1::unchunked::send\_ek::EkSent}::from\_pb\` in \`v1/unchunked/send\_ek/serialize.rs\`**

Status: closed. Opened: 2026-08-04. Author: Zhang-Liao.

Body excerpt: Parent: #375

No recorded comments or reviews.

### Item 382

**[Issue #382](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/382) — Specify and verify : \`spqr::v1::unchunked::send\_ek::serialize::{spqr::v1::unchunked::send\_ek::EkSentCt1Received}::into\_pb\` in \`v1/unchunked/send\_ek/serialize.rs\`**

Status: closed. Opened: 2026-08-04. Author: Zhang-Liao.

Body excerpt: Parent: #375

No recorded comments or reviews.

### Item 383

**[Issue #383](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/383) — Specify and verify : \`spqr::v1::unchunked::send\_ek::serialize::{spqr::v1::unchunked::send\_ek::EkSentCt1Received}::from\_pb\` in \`v1/unchunked/send\_ek/serialize.rs\`**

Status: closed. Opened: 2026-08-04. Author: Zhang-Liao.

Body excerpt: Parent: #375

No recorded comments or reviews.

### Item 384

**[PR #384](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/384) — Specify and verify unchunked send\_ek \`KeysUnsampled::into\_pb\`**

Status: closed unmerged. Opened: 2026-08-04. Author: Zhang-Liao.

Body excerpt: Adds a precondition-free spec theorem for \`spqr::v1::unchunked::send\_ek::serialize::KeysUnsampled::into\_pb\`: - The call always succeeds (no panic). - \`epoch\` is copied verbatim. - \`auth\` is \`some\` of the protobuf form, with \`root\_key\`/\`mac\_key\` preserved. Proof is a one-line \`simp\` unfolding the two field-copy bodies. Tagged \`@\[step\]\` for reuse by the chunked layer and the future \`States::into\_pb\` spec (#317). …

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/384#issuecomment-5175515535) — Zhang-Liao (2026-08-04): Folded into #385 (cherry-picked e7e59d3 as 9e15662); #385 now covers all four into\_pb states.

### Item 385

**[PR #385](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/385) — Specify and verify unchunked send\_ek \`into\_pb\` (all four states)**

Status: merged. Opened: 2026-08-04. Author: Zhang-Liao.

Body excerpt: Adds precondition-free spec theorems for the four \`into\_pb\` conversions in \`spqr::v1::unchunked::send\_ek::serialize\`: - \`KeysUnsampled::into\_pb\` (#376) - \`HeaderSent::into\_pb\` (#378) - \`EkSent::into\_pb\` (#380) - \`EkSentCt1Received::into\_pb\` (#382) All four share the same shape: - The call always succeeds (no panic). - All plain fields (\`epoch\`, \`ek\`/\`dk\`/\`ct1\` as applicable) are copied verbatim. - \`auth\` is \`some\` …

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/385#pullrequestreview-4855219224) — truonghoangle (2026-08-04): (No text.)

### Item 386

**[PR #386](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/386) — Specify and verify unchunked send\_ek \`from\_pb\` (all four states)**

Status: merged. Opened: 2026-08-04. Author: Zhang-Liao.

Body excerpt: Adds precondition-free spec theorems for the four \`from\_pb\` conversions in \`spqr::v1::unchunked::send\_ek::serialize\`: - \`KeysUnsampled::from\_pb\` (#377) - \`HeaderSent::from\_pb\` (#379) - \`EkSent::from\_pb\` (#381) - \`EkSentCt1Received::from\_pb\` (#383) All four share the same shape: - The call always succeeds (no panic). - A missing \`auth\` field, or a wrong key/ciphertext length (\`dk\` 2400, \`ek\` 1152, \`ct1\` 960 bytes as …

Discussion and review record:

- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/386#discussion_r3713186479) — truonghoangle (2026-08-04; Spqr/Specs/V1/Unchunked/SendEk/Serialize/EkSent/FromPb.lean:39): Could \`match\` be used instead of \`∃ st, result = .Ok st\`? It would make the underlying nature clearer and easier to work with. (Similar problem with other files.)
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/386#pullrequestreview-4855298747) — truonghoangle (2026-08-04): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/386#discussion_r3717675397) — Zhang-Liao (2026-08-05; Spqr/Specs/V1/Unchunked/SendEk/Serialize/EkSent/FromPb.lean:39): Thanks for the constructive comments! I have replaced \`exists st, results = .Ok st\` with the following format to make it more exact. \`\`\` result = .Ok { epoch := pb.epoch, auth := { root\_key := a.root\_key, mac\_key := a.mac\_key }, dk := pb.dk } \`\`\`
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/386#pullrequestreview-4860683710) — Zhang-Liao (2026-08-05): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/386#pullrequestreview-4861231016) — truonghoangle (2026-08-05): (No text.)

### Item 387

**[PR #387](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/387) — Specify and verify : \`spqr::encoding::{impl spqr::encoding::Decoder for core::option::Option}::new\` in \`encoding.rs\`**

Status: merged. Opened: 2026-08-04. Author: truonghoangle.

Body excerpt: This PR specifies and verifies : \`spqr::encoding::{impl spqr::encoding::Decoder for core::option::Option}::new\` in \`encoding.rs\` The \`Decoder\` impl for \`Option\` delegates to the inner \`T::new\`, wraps success in \`Some\`, and forwards errors unchanged. After hax extraction the \`?\`-desugared body becomes: \`DecoderInst.new\` → \`Try.branch\` → match on \`Continue\`/\`Break\`. Two theorems: • \`new\_spec\_lift\` - lifts an arbitrary …

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/387#pullrequestreview-4851464224) — Zhang-Liao (2026-08-04): (No text.)

### Item 388

**[Issue #388](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/388) — \`map\` + \`collect\` proof from PR #357 for \`point\_at\` in \`polynomial.rs\`**

Status: closed. Opened: 2026-08-04. Author: truonghoangle.

Body excerpt: This issue reuses the same \`sorry\` for the \`map + collect\` pipeline as in PR #357. Specifically, it shows that \`Iterator.collect.default\` on \`Map (Enumerate (Iter GF16)) closure\_1\` is equivalent to \`FromIteratorVec.from\_iter\` with \`mapIteratorTransformer\`, using \`m.iter\` as the initial state. Consequently, once the issue in PR #357 is resolved, the corresponding proof in this issue can be completed as well.

No recorded comments or reviews.

### Item 389

**[PR #389](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/389) — Specify and verify: \`spqr::encoding::polynomial::PolyEncoder::chunk\_at\` in \`polynomial.rs\`**

Status: merged. Opened: 2026-08-04. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::encoding::polynomial::PolyEncoder::chunk\_at\` in \`polynomial.rs\` closes #220

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/389#issuecomment-5186544467) — Zhang-Liao (2026-08-05): @truonghoangle The CI failed. Please fix it.
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/389#issuecomment-5188384465) — github-actions[bot] (2026-08-05): ### Sorry Delta — hand-written specs \*\*7 new sorry-tainted declarations in \`Spqr.Specs.\*\`:\*\* | Module | Declaration | Kind | |--------|-------------|------| | \`Spqr.Specs.Encoding.Polynomial.PolyEncoder.ChunkAt\` | \`spqr.encoding.polynomial.PolyEncoder.chunk\_at\_loop.body\_spec\` | transitive | | \`Spqr.Specs.Encoding.Polynomial.PolyEncoder.ChunkAt\` | …
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/389#pullrequestreview-4862505089) — Zhang-Liao (2026-08-05): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/389#discussion_r3719075417) — Zhang-Liao (2026-08-05; Spqr/Specs/Encoding/Polynomial/PolyEncoder/ChunkAt.lean:410): \`h\_coeff\_bound\` is wrong since we can use it to prove False. \`\`\` theorem h\_coeff\_bound\_implies\_false (h\_coeff\_bound : ∀ (polys : Array encoding.polynomial.Poly 16#usize), ∀ (j : Nat), j &lt; 16 → (polys.val\[j\]!).coefficients.length + 1 ≤ Usize.max) : False := by let badVec : alloc.vec.Vec encoding.gf.GF16 := ⟨List.replicate Usize.max ⟨0#u16⟩, by simp⟩ let badPoly : encoding.polynomial.Poly := ⟨badVec⟩ let badPolys : …
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/389#discussion_r3722459082) — truonghoangle (2026-08-05; Spqr/Specs/Encoding/Polynomial/PolyEncoder/ChunkAt.lean:410): I fixed it
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/389#pullrequestreview-4866800278) — truonghoangle (2026-08-05): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/389#pullrequestreview-4871818164) — Zhang-Liao (2026-08-06): (No text.)
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/389#issuecomment-5202300221) — github-actions[bot] (2026-08-06): ### Sorry Delta — hand-written specs \*\*7 new sorry-tainted declarations in \`Spqr.Specs.\*\`:\*\* | Module | Declaration | Kind | |--------|-------------|------| | \`Spqr.Specs.Encoding.Polynomial.PolyEncoder.ChunkAt\` | \`spqr.encoding.polynomial.PolyEncoder.chunk\_at\_loop.body\_spec\` | transitive | | \`Spqr.Specs.Encoding.Polynomial.PolyEncoder.ChunkAt\` | …

### Item 390

**[Issue #390](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/390) — Verify : \`v1/unchunked/send\_ct/serialize.rs\`**

Status: open. Opened: 2026-08-05. Author: Zhang-Liao.

Body excerpt: - \[x\] #391 - \[x\] #392 - \[x\] #393 - \[x\] #394 - \[x\] #395 - \[x\] #396 - \[x\] #397 - \[x\] #398 - \[x\] #399 - \[x\] #400

No recorded comments or reviews.

### Item 391

**[Issue #391](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/391) — Specify and verify : \`spqr::v1::unchunked::send\_ct::serialize::{spqr::v1::unchunked::send\_ct::NoHeaderReceived}::into\_pb\` in \`v1/unchunked/send\_ct/serialize.rs\`**

Status: closed. Opened: 2026-08-05. Author: Zhang-Liao.

Body excerpt: Parent: #390

No recorded comments or reviews.

### Item 392

**[Issue #392](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/392) — Specify and verify : \`spqr::v1::unchunked::send\_ct::serialize::{spqr::v1::unchunked::send\_ct::NoHeaderReceived}::from\_pb\` in \`v1/unchunked/send\_ct/serialize.rs\`**

Status: closed. Opened: 2026-08-05. Author: Zhang-Liao.

Body excerpt: Parent: #390

No recorded comments or reviews.

### Item 393

**[Issue #393](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/393) — Specify and verify : \`spqr::v1::unchunked::send\_ct::serialize::{spqr::v1::unchunked::send\_ct::HeaderReceived}::into\_pb\` in \`v1/unchunked/send\_ct/serialize.rs\`**

Status: closed. Opened: 2026-08-05. Author: Zhang-Liao.

Body excerpt: Parent: #390

No recorded comments or reviews.

### Item 394

**[Issue #394](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/394) — Specify and verify : \`spqr::v1::unchunked::send\_ct::serialize::{spqr::v1::unchunked::send\_ct::HeaderReceived}::from\_pb\` in \`v1/unchunked/send\_ct/serialize.rs\`**

Status: closed. Opened: 2026-08-05. Author: Zhang-Liao.

Body excerpt: Parent: #390

No recorded comments or reviews.

### Item 395

**[Issue #395](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/395) — Specify and verify : \`spqr::v1::unchunked::send\_ct::serialize::{spqr::v1::unchunked::send\_ct::Ct1Sent}::into\_pb\` in \`v1/unchunked/send\_ct/serialize.rs\`**

Status: closed. Opened: 2026-08-05. Author: Zhang-Liao.

Body excerpt: Parent: #390

No recorded comments or reviews.

### Item 396

**[Issue #396](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/396) — Specify and verify : \`spqr::v1::unchunked::send\_ct::serialize::{spqr::v1::unchunked::send\_ct::Ct1Sent}::from\_pb\` in \`v1/unchunked/send\_ct/serialize.rs\`**

Status: closed. Opened: 2026-08-05. Author: Zhang-Liao.

Body excerpt: Parent: #390

No recorded comments or reviews.

### Item 397

**[Issue #397](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/397) — Specify and verify : \`spqr::v1::unchunked::send\_ct::serialize::{spqr::v1::unchunked::send\_ct::Ct1SentEkReceived}::into\_pb\` in \`v1/unchunked/send\_ct/serialize.rs\`**

Status: closed. Opened: 2026-08-05. Author: Zhang-Liao.

Body excerpt: Parent: #390

No recorded comments or reviews.

### Item 398

**[Issue #398](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/398) — Specify and verify : \`spqr::v1::unchunked::send\_ct::serialize::{spqr::v1::unchunked::send\_ct::Ct1SentEkReceived}::from\_pb\` in \`v1/unchunked/send\_ct/serialize.rs\`**

Status: closed. Opened: 2026-08-05. Author: Zhang-Liao.

Body excerpt: Parent: #390

No recorded comments or reviews.

### Item 399

**[Issue #399](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/399) — Specify and verify : \`spqr::v1::unchunked::send\_ct::serialize::{spqr::v1::unchunked::send\_ct::Ct2Sent}::into\_pb\` in \`v1/unchunked/send\_ct/serialize.rs\`**

Status: closed. Opened: 2026-08-05. Author: Zhang-Liao.

Body excerpt: Parent: #390

No recorded comments or reviews.

### Item 400

**[Issue #400](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/400) — Specify and verify : \`spqr::v1::unchunked::send\_ct::serialize::{spqr::v1::unchunked::send\_ct::Ct2Sent}::from\_pb\` in \`v1/unchunked/send\_ct/serialize.rs\`**

Status: closed. Opened: 2026-08-05. Author: Zhang-Liao.

Body excerpt: Parent: #390

No recorded comments or reviews.

### Item 401

**[PR #401](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/401) — Specify and verify unchunked send\_ct serialize: all \`into\_pb\` states and \`NoHeaderReceived::from\_pb\`**

Status: merged. Opened: 2026-08-05. Author: Zhang-Liao.

Body excerpt: Closes #391, closes #392, closes #393, closes #395, closes #397, closes #399 (parent #390). Adds six spec theorems for \`src/v1/unchunked/send\_ct/serialize.rs\`, under \`Spqr/Specs/V1/Unchunked/SendCt/Serialize/\`: | File | Issue | Function | |------|-------|----------| | \`NoHeaderReceived/IntoPb.lean\` | #391 | \`NoHeaderReceived::into\_pb\` | | \`NoHeaderReceived/FromPb.lean\` | #392 | \`NoHeaderReceived::from\_pb\` | | …

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/401#pullrequestreview-4876401231) — truonghoangle (2026-08-06): (No text.)

### Item 402

**[PR #402](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/402) — Specify and verify : \`spqr::encoding::{impl spqr::encoding::Decoder for core::option::Option}::add\_chunk\` in \`encoding.rs\`**

Status: merged. Opened: 2026-08-05. Author: truonghoangle.

Body excerpt: This PR specifies and verifies : \`spqr::encoding::{impl spqr::encoding::Decoder for core::option::Option}::add\_chunk\` in \`encoding.rs\` \`Option::add\_chunk\` requires \`self.isSome\`, delegates to \`T::add\_chunk\` on the inner value, and re-wraps the result in \`Some\`. The extracted Lean code decomposes this into four steps: \`take\`, \`unwrap\`, inner \`add\_chunk\`, and \`ok (some ·)\` — a pure structural lift with no extra math. …

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/402#pullrequestreview-4870621416) — Zhang-Liao (2026-08-06): (No text.)

### Item 403

**[PR #403](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/403) — Specify and verify : \`spqr::encoding::{impl spqr::encoding::Encoder for core::option::Option}::encode\_bytes\` in \`encoding.rs\`**

Status: merged. Opened: 2026-08-06. Author: truonghoangle.

Body excerpt: This PR specifies and verifies : \`spqr::encoding::{impl spqr::encoding::Encoder for core::option::Option}::encode\_bytes\` in \`encoding.rs\`. The \`Option\` encoder wraps the inner \`T\` encoder: successes are tagged with \`Some\`, errors pass through unchanged. Two theorems: • \`encode\_bytes\_spec\_lift\` — lifts any postcondition of the inner encoder through the wrapper. • \`encode\_bytes\_spec\_poly\_encoder\` — instantiates the …

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/403#issuecomment-5200589863) — github-actions[bot] (2026-08-06): ### Sorry Delta — hand-written specs \*\*2 new sorry-tainted declarations in \`Spqr.Specs.\*\`:\*\* | Module | Declaration | Kind | |--------|-------------|------| | \`Spqr.Specs.Encoding.Encoder.EncodeBytes\` | \`spqr.core.option.Option.Insts.SpqrEncodingEncoder.encode\_bytes\_spec\_poly\_encoder\` | transitive | | \`Spqr.Specs.Encoding.Encoder.EncodeBytes\` | …
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/403#pullrequestreview-4872180016) — Zhang-Liao (2026-08-06): Please close the correct issue before merging. The current issue is just a placeholder

### Item 404

**[Issue #404](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/404) — External Lean decls use root names while translation.json uses \`spqr.\` prefix**

Status: closed. Opened: 2026-08-06. Author: astefano.

Body excerpt: Not sure where this issue should be, i draft it here and later we can move it to other repos (like probe-lean or/and aeneas). We noticed that \`SrcTranslated/FunsExternal.lean\` declares external/opaque functions at the crate \*\*root\*\* (e.g. \`kdf.hkdf\_to\_slice\`, \`core.result.Result.map\`, \`libcrux\_hmac.hmac\`), but: - \`SrcTranslated/Funs.lean\` wraps translated definitions in \`namespace spqr\`, and - \`translation.json\` …

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/404#issuecomment-5205679208) — astefano (2026-08-06): I note also that a root cause is an upstream Aeneas codegen potential bug @oliver-butterley please check. Aeneas emits external/opaque decls at the crate root but records them namespace-prefixed in translation.json. Traced in aeneas @ 6e167c9b: - src/Translate.ml:2041: the FunsExternal file is configured in\_namespace = false, so opaque \`kdf.hkdf\_to\_slice\` is declared at the root. (Funs.lean is in\_namespace = true → …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/404#issuecomment-5450239448) — oliver-butterley (2026-08-28): Fixed upstream in https://github.com/AeneasVerif/aeneas/pull/1254

### Item 405

**[PR #405](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/405) — Specify and verify : \`spqr::encoding::polynomial::{impl Encoder for PolyEncoder}::next\_chunk\` in \`polynomial.rs\`**

Status: merged. Opened: 2026-08-06. Author: truonghoangle.

Body excerpt: This PR specifies and verifies : \`spqr::encoding::polynomial::{impl Encoder for PolyEncoder}::next\_chunk\` in \`polynomial.rs\` closes #255

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/405#issuecomment-5207254335) — github-actions[bot] (2026-08-06): ### Sorry Delta — hand-written specs \*\*2 new sorry-tainted declarations in \`Spqr.Specs.\*\`:\*\* | Module | Declaration | Kind | |--------|-------------|------| | \`Spqr.Specs.Encoding.Polynomial.PolyEncoder.NextChunk\` | \`spqr.encoding.polynomial.PolyEncoder.Insts.SpqrEncodingEncoder.next\_chunk\_spec\` | transitive | | \`Spqr.Specs.Encoding.Polynomial.PolyEncoder.NextChunk\` | …
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/405#pullrequestreview-4888471986) — Zhang-Liao (2026-08-08): (No text.)
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/405#issuecomment-5226402566) — github-actions[bot] (2026-08-08): ### Sorry Delta — hand-written specs \*\*2 new sorry-tainted declarations in \`Spqr.Specs.\*\`:\*\* | Module | Declaration | Kind | |--------|-------------|------| | \`Spqr.Specs.Encoding.Polynomial.PolyEncoder.NextChunk\` | \`spqr.encoding.polynomial.PolyEncoder.Insts.SpqrEncodingEncoder.next\_chunk\_spec\` | transitive | | \`Spqr.Specs.Encoding.Polynomial.PolyEncoder.NextChunk\` | …

### Item 406

**[PR #406](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/406) — Specify and verify unchunked send\_ct serialize: remaining from\_pb states**

Status: merged. Opened: 2026-08-07. Author: Zhang-Liao.

Body excerpt: Closes #394, closes #396, closes #398, closes #400. Adds spec theorems for the four remaining \`from\_pb\` conversions in \`v1/unchunked/send\_ct/serialize.rs\`, completing the send\_ct serialize series started in #401: | File | Issue | Length checks | |---|---|---| | \`HeaderReceived/FromPb.lean\` | #394 | \`hdr = 64\` | | \`Ct1Sent/FromPb.lean\` | #396 | \`hdr = 64\`, \`es = 2080\`, \`ct1 = 960\` | | \`Ct1SentEkReceived/FromPb.lean\` …

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/406#pullrequestreview-4884049456) — truonghoangle (2026-08-07): (No text.)

### Item 407

**[PR #407](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/407) — Find structure: shared @\[step\] spec for Enumerate iterator and loop-body proof dedup**

Status: open draft. Opened: 2026-08-07. Author: Zhang-Liao.

Body excerpt: ## Summary - Add shared \`@\[step\]\` spec for \`Enumerate&gt;::next\` and deduplicate loop-body proofs - Use \`step\` tactic for range-iterator preambles in loop-body proofs - Add \`learn\_structure.md\` notes on proof structure findings Draft PR for comparing the structure-finding work against latest \`main\`. 🤖 Generated with Claude Code

No recorded comments or reviews.

### Item 408

**[PR #408](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/408) — Remove \`sorry\` from \`lagrange\_polys\_for\_complete\_points\_loop0.body\_spec\` (#272)**

Status: merged. Opened: 2026-08-07. Author: astefano.

Body excerpt: This PR closes the \`sorry\` at \`Spqr/Specs/Encoding/Polynomial/LagrangePolysForCompletePoints.lean:57\`. The \`sorry\` was hiding a false statement, not an unproven one, see https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/272#issuecomment-5216564309 for context. This PR proposes as a fix to state a frame condition, not the caller's invariant: \`body\_spec\` and \`loop\_spec\` now say …

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/408#pullrequestreview-4883663077) — Kukovec (2026-08-07): (No text.)

### Item 409

**[Issue #409](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/409) — \`.map(...).collect()\` semantics is assumed, not derived (blocked on aeneas#1043)**

Status: closed. Opened: 2026-08-07. Author: astefano.

Body excerpt: \`Map\`'s \`Iterator::next\` is \`sorry\` in the model, so every \`.map(...).collect()\` in the project is verified against an \*assumption\* rather than against Aeneas output. \`SrcTranslated/Funs.lean\`: \`\`\`lean impl\_def core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator ... := { next := sorry -- See https://github.com/AeneasVerif/aeneas/issues/1043 step\_by := ... enumerate := ... } \`\`\` Upstream: aeneas#1043 …

No recorded comments or reviews.

### Item 410

**[PR #410](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/410) — Unify the two \`.map(...).collect()\` bridges into one named assumption**

Status: merged. Opened: 2026-08-07. Author: astefano.

Body excerpt: \`ConstPolysToPolys.collect\_default\_bridge\` and \`PolyEncoder.point\_at\_loop.map\_collect\_eq\_point\_at\` were two separate \`sorry\`s asserting the same thing at different type arguments: that collecting through the Aeneas-generated \`Map\` iterator instance agrees with the hand-written \`mapIteratorTransformer\` semantics. The generated instance is generic in \`I\`/\`F\`/\`B\`, so one lemma covers both. Both are now proved …

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/410#issuecomment-5218648898) — github-actions[bot] (2026-08-07): ### Sorry Delta — hand-written specs \*\*1 new sorry-tainted declaration in \`Spqr.Specs.\*\`:\*\* | Module | Declaration | Kind | |--------|-------------|------| | \`Spqr.Specs.Aeneas.MapCollectBridge\` | \`Spqr.Aeneas.collect\_default\_bridge\` | direct |
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/410#pullrequestreview-4884019872) — truonghoangle (2026-08-07): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/410#discussion_r3736697797) — truonghoangle (2026-08-07; Spqr/Specs/Aeneas/MapCollectBridge.lean:4): why is authors \`The Beneficial AI Foundation\`
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/410#issuecomment-5218704180) — truonghoangle (2026-08-07): Great job! Could you add your name to the files you modified?
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/410#discussion_r3736788419) — astefano (2026-08-07; Spqr/Specs/Aeneas/MapCollectBridge.lean:4): sorry, i didn't know the convention in this repo was to use our names (in the other repos i contribute to, the author is BAIF)
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/410#pullrequestreview-4884128514) — astefano (2026-08-07): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/410#pullrequestreview-4884185638) — truonghoangle (2026-08-07): (No text.)

### Item 411

**[PR #411](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/411) — Specify and verify : \`spqr::encoding::{impl spqr::encoding::Decoder for core::option::Option}::decoded\_message\` in \`encoding.rs\`**

Status: merged. Opened: 2026-08-07. Author: truonghoangle.

Body excerpt: This PR specifies and verifies : \`spqr::encoding::{impl spqr::encoding::Decoder for core::option::Option}::decoded\_message\` in \`encoding.rs\` \`Option::decoded\_message\` unwraps \`self\` and delegates to \`T::decoded\_message\`. Extracted body: \`as\_ref\` → \`unwrap\` → \`DecoderInst.decoded\_message\`. Theorem: • \`decoded\_message\_spec\_lift\` — lifts a postcondition through the \`Option\` wrapper. Note that, unlike other functions in …

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/411#pullrequestreview-4888503283) — Zhang-Liao (2026-08-08): (No text.)

### Item 412

**[Issue #412](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/412) — Verify : \`lib.rs\`**

Status: open. Opened: 2026-08-07. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 413

**[Issue #413](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/413) — Specify and verify : \`spqr::empty\_state\` in \`lib.rs\`**

Status: closed. Opened: 2026-08-07. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 414

**[Issue #414](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/414) — Specify and verify : \`spqr::{impl core::cmp::PartialEq for spqr::SecretOutput}::eq\` in \`lib.rs\`**

Status: closed. Opened: 2026-08-07. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 415

**[Issue #415](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/415) — Specify and verify \`spqr::{impl core::fmt::Debug for spqr::SecretOutput}::fmt\` in \`lib.rs\`**

Status: closed. Opened: 2026-08-07. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 416

**[Issue #416](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/416) — Specify and verify : \`spqr::{impl core::convert::From for spqr::Error}::from\` in \`lib.rs\`**

Status: closed. Opened: 2026-08-07. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 417

**[Issue #417](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/417) — Specify and verify : \`spqr::{impl core::convert::From for spqr::Error}::from\` in \`lib.rs\`**

Status: closed. Opened: 2026-08-07. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 418

**[Issue #418](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/418) — Specify and verify : \`spqr::{spqr::SecretOutput}::send\_secret\` in \`lib.rs\`**

Status: closed. Opened: 2026-08-07. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 419

**[Issue #419](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/419) — Specify and verify : \`spqr::{spqr::SecretOutput}::recv\_secret\` in \`lib.rs\`**

Status: closed. Opened: 2026-08-07. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 420

**[Issue #420](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/420) — Specify and verify : \`spqr::{spqr::SecretOutput}::secret\` in \`lib.rs\`**

Status: closed. Opened: 2026-08-07. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 421

**[Issue #421](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/421) — Specify and verify : \`spqr::{spqr::SecretOutput}::has\_secret\` in \`lib.rs\`**

Status: closed. Opened: 2026-08-07. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 422

**[Issue #422](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/422) — Specify and verify : \`spqr::{impl core::convert::TryFrom for spqr::proto::pq\_ratchet::Version}::try\_from\` in \`lib.rs\`**

Status: closed. Opened: 2026-08-07. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 423

**[Issue #423](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/423) — Specify and verify : \`spqr::{impl core::convert::From for u8}::from\` in \`lib.rs\`**

Status: closed. Opened: 2026-08-07. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 424

**[Issue #424](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/424) — Specify and verify : \`spqr::v1::unchunked::send\_ct::{spqr::v1::unchunked::send\_ct::NoHeaderReceived}::new\` in \`lib.rs\`**

Status: closed. Opened: 2026-08-07. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 425

**[Issue #425](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/425) — Specify and verify \`spqr::init\_inner\` in \`lib.rs\`**

Status: closed. Opened: 2026-08-07. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 426

**[Issue #426](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/426) — Specify and verify : \`spqr::initial\_state\` in \`lib.rs\`**

Status: closed. Opened: 2026-08-07. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 427

**[Issue #427](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/427) — Specify and verify : \`spqr::{spqr::proto::pq\_ratchet::Version}::DISABLED\` in \`lib.rs\`**

Status: closed. Opened: 2026-08-07. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 428

**[Issue #428](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/428) — Specify and verify : \`spqr::{spqr::proto::pq\_ratchet::Version}::MAX\` in \`lib.rs\`**

Status: closed. Opened: 2026-08-07. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 429

**[Issue #429](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/429) — Specify and verify : \`spqr::decode\_state\` in \`lib.rs\`**

Status: closed. Opened: 2026-08-07. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 430

**[Issue #430](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/430) — Specify and verify \`spqr::current\_version::{impl core::ops::function::FnOnce for spqr::current\_version::closure}::call\_once\` in \`lib.rs\`**

Status: closed. Opened: 2026-08-07. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 431

**[Issue #431](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/431) — Specify and verify : \`spqr::current\_version\` in \`lib.rs\`**

Status: closed. Opened: 2026-08-07. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 432

**[Issue #432](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/432) — Specify and verify : \`spqr::chain\_from\_version\_negotiation::{impl core::ops::function::FnOnce for spqr::chain\_from\_version\_negotiation::closure}::call\_once\` in \`lib.rs\`**

Status: closed. Opened: 2026-08-07. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 433

**[Issue #433](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/433) — Specify and verify \`spqr::chain\_from\_version\_negotiation\` in \`lib.rs\`**

Status: closed. Opened: 2026-08-07. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 434

**[Issue #434](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/434) — Specify and verify \`spqr::send\` in \`lib.rs\`**

Status: open. Opened: 2026-08-07. Author: truonghoangle.

Body excerpt: (No text.)

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/434#issuecomment-6336930333) — MarkusFerdinandDablander (2026-10-22): Hi @truonghoangle as discussed in today's meeting, I will take over this issue and attempt to specify this function ASAP!

### Item 435

**[Issue #435](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/435) — Specify and verify \`spqr::chain\_from\` in \`lib.rs\`**

Status: closed. Opened: 2026-08-07. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 436

**[PR #436](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/436) — Specify and verify : \`spqr::encoding::{impl spqr::encoding::Encoder for core::option::Option}::next\_chunk\` in \`encoding.rs\`**

Status: merged. Opened: 2026-08-08. Author: truonghoangle.

Body excerpt: This PR specifies and verifies : \`spqr::encoding::{impl spqr::encoding::Encoder for core::option::Option}::next\_chunk\` in \`encoding.rs\`. This PR also completes the file \`encoding.rs\`. The \`Option\` encoder's \`next\_chunk\` unwraps \`self\`, delegates to \`T::next\_chunk\`, and re-wraps the result in \`Some\`. It is a pure structural lift adding no mathematical content. This file proves: • \`next\_chunk\_spec\_lift\` — lifts any …

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/436#issuecomment-5227010737) — github-actions[bot] (2026-08-08): ### Sorry Delta — hand-written specs \*\*2 new sorry-tainted declarations in \`Spqr.Specs.\*\`:\*\* | Module | Declaration | Kind | |--------|-------------|------| | \`Spqr.Specs.Encoding.Encoder.NextChunk\` | \`spqr.core.option.Option.Insts.SpqrEncodingEncoder.next\_chunk\_spec\_poly\_encoder\` | transitive | | \`Spqr.Specs.Encoding.Encoder.NextChunk\` | …
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/436#pullrequestreview-4893427391) — Zhang-Liao (2026-08-10): (No text.)

### Item 437

**[PR #437](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/437) — Specify and verify : \`spqr::empty\_state\` in \`lib.rs\`**

Status: merged. Opened: 2026-08-08. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::empty\_state\` in \`lib.rs\` closes #413

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/437#pullrequestreview-4893538246) — Zhang-Liao (2026-08-10): (No text.)

### Item 438

**[PR #438](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/438) — Specify and verify : \`spqr::{impl core::cmp::PartialEq for spqr::SecretOutput}::eq\` in \`lib.rs\`**

Status: merged. Opened: 2026-08-10. Author: truonghoangle.

Body excerpt: This PR specifies and verifies : \`spqr::{impl core::cmp::PartialEq for spqr::SecretOutput}::eq\` in \`lib.rs\` closes #414

Discussion and review record:

- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/438#discussion_r3750531882) — Zhang-Liao (2026-08-10; Spqr/Specs/Lib/SecretOutput/Eq.lean:88): The specifications from lines 80 to 88 seems to be equivalent to \`result = true self = other\`.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/438#pullrequestreview-4897917314) — Zhang-Liao (2026-08-10): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/438#discussion_r3750708368) — truonghoangle (2026-08-10; Spqr/Specs/Lib/SecretOutput/Eq.lean:88): I fixed it. Thank you for your comment
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/438#pullrequestreview-4898135134) — truonghoangle (2026-08-10): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/438#pullrequestreview-4898166355) — Zhang-Liao (2026-08-10): (No text.)

### Item 439

**[PR #439](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/439) — Specify and verify \`spqr::{impl core::fmt::Debug for spqr::SecretOutput}::fmt\` in \`lib.rs\`**

Status: merged. Opened: 2026-08-10. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::{impl core::fmt::Debug for spqr::SecretOutput}::fmt\` in \`lib.rs\` closes #415

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/439#pullrequestreview-4903808046) — Zhang-Liao (2026-08-11): (No text.)

### Item 440

**[PR #440](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/440) — Specify and verify : \`spqr::{impl core::convert::From for spqr::Error}::from\` in \`lib.rs\`**

Status: merged. Opened: 2026-08-10. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::{impl core::convert::From for spqr::Error}::from\` in \`lib.rs\` closes #416

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/440#pullrequestreview-4904104530) — Zhang-Liao (2026-08-11): (No text.)

### Item 441

**[PR #441](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/441) — Specify and verify : \`spqr::{impl core::convert::From for spqr::Error}::from\` in \`lib.rs\`**

Status: merged. Opened: 2026-08-11. Author: truonghoangle.

Body excerpt: This PR specifies and verifies : \`spqr::{impl core::convert::From for spqr::Error}::from\` in \`lib.rs\` closes #417

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/441#pullrequestreview-4913390493) — Zhang-Liao (2026-08-12): (No text.)

### Item 442

**[PR #442](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/442) — Specify and verify : \`spqr::{spqr::SecretOutput}::send\_secret\` in \`lib.rs\`**

Status: merged. Opened: 2026-08-11. Author: truonghoangle.

Body excerpt: This PR specifies and verifies : \`spqr::{spqr::SecretOutput}::send\_secret\` in \`lib.rs\` closes #418

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/442#pullrequestreview-4913567120) — Zhang-Liao (2026-08-12): (No text.)

### Item 443

**[PR #443](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/443) — Specify and verify : \`spqr::{spqr::SecretOutput}::recv\_secret\` in \`lib.rs\`**

Status: merged. Opened: 2026-08-12. Author: truonghoangle.

Body excerpt: This PR specifies and verifies : \`spqr::{spqr::SecretOutput}::recv\_secret\` in \`lib.rs\` closes #419

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/443#pullrequestreview-4915445901) — Zhang-Liao (2026-08-12): (No text.)

### Item 444

**[PR #444](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/444) — Specify and verify : \`spqr::{spqr::SecretOutput}::secret\` in \`lib.rs\`**

Status: merged. Opened: 2026-08-12. Author: truonghoangle.

Body excerpt: This PR specifies and verifies : \`spqr::{spqr::SecretOutput}::secret\` in \`lib.rs\` closes #420

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/444#pullrequestreview-4916578325) — Kukovec (2026-08-12): (No text.)

### Item 445

**[PR #445](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/445) — Specify and verify : \`spqr::{spqr::SecretOutput}::has\_secret\` in \`lib.rs\`**

Status: merged. Opened: 2026-08-12. Author: truonghoangle.

Body excerpt: This PR specifies and verifies : \`spqr::{spqr::SecretOutput}::has\_secret\` in \`lib.rs\` closes #421

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/445#pullrequestreview-4916581122) — Kukovec (2026-08-12): (No text.)

### Item 446

**[PR #446](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/446) — Specify and verify : \`spqr::{impl core::convert::From for u8}::from\` in \`lib.rs\`**

Status: merged. Opened: 2026-08-12. Author: truonghoangle.

Body excerpt: This PR specifies and verifyies : \`spqr::{impl core::convert::From for u8}::from\` in \`lib.rs\` @Zhang-Liao @Kukovec @oliver-butterley The rules for where to store files are based on full name of function; however, in the case of the full name of function here, I'm confused and unsure if I've done it correctly. If possible, please double-check this with the functions in the \`Lib\` folder . closes #423

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/446#issuecomment-5277646833) — Zhang-Liao (2026-08-13): I think you should run \`lake exe mk\_all\` to update \`Spar.lean\` before the merge.
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/446#issuecomment-5277687183) — truonghoangle (2026-08-13): I ran this command \`lake exe mk\_all\` before the merge.
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/446#issuecomment-5277924598) — Zhang-Liao (2026-08-13): But the \`Spqr.lean\` is not changed. I assume it should be changed.
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/446#issuecomment-5278046564) — truonghoangle (2026-08-13): Sorry, I forgot to run \`git add .\` before pushing. I fixed it.
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/446#pullrequestreview-4925267335) — Zhang-Liao (2026-08-13): (No text.)

### Item 447

**[PR #447](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/447) — Specify and verify : \`spqr::{impl core::convert::TryFrom for spqr::proto::pq\_ratchet::Version}::try\_from\` in \`lib.rs\`**

Status: merged. Opened: 2026-08-12. Author: truonghoangle.

Body excerpt: This PR specifies and verifies : \`spqr::{impl core::convert::TryFrom for spqr::proto::pq\_ratchet::Version}::try\_from\` in \`lib.rs\` closes #422

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/447#pullrequestreview-4933585661) — Zhang-Liao (2026-08-14): (No text.)

### Item 448

**[PR #448](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/448) — Specify and verify : \`spqr::{spqr::proto::pq\_ratchet::Version}::DISABLED\` in \`lib.rs\`**

Status: merged. Opened: 2026-08-13. Author: truonghoangle.

Body excerpt: This PR specifies and verifies : \`spqr::{spqr::proto::pq\_ratchet::Version}::DISABLED\` in \`lib.rs\` closes #427

Discussion and review record:

- [review DISMISSED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/448#pullrequestreview-4933647638) — Zhang-Liao (2026-08-14): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/448#pullrequestreview-4945679162) — Zhang-Liao (2026-08-16): (No text.)

### Item 449

**[PR #449](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/449) — Specify and verify : \`spqr::{spqr::proto::pq\_ratchet::Version}::MAX\` in \`lib.rs\`**

Status: merged. Opened: 2026-08-14. Author: truonghoangle.

Body excerpt: This PR specifies and verifies : \`spqr::{spqr::proto::pq\_ratchet::Version}::MAX\` in \`lib.rs\` closes #428

Discussion and review record:

- [review DISMISSED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/449#pullrequestreview-4945683009) — Zhang-Liao (2026-08-16): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/449#pullrequestreview-4949267399) — Kukovec (2026-08-17): (No text.)

### Item 450

**[Issue #450](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/450) — Specify and verify \`spqr::proto::pq\_ratchet::{impl core::convert::TryFrom for spqr::proto::pq\_ratchet::Version}::try\_from\` in support \`lib.rs\`**

Status: closed. Opened: 2026-08-14. Author: truonghoangle.

Body excerpt: /-- \[spqr::proto::pq\_ratchet::{impl core::convert::TryFrom for spqr::proto::pq\_ratchet::Version}::try\_from\]: Source: 'generated/signal.proto.pq\_ratchet.rs', lines 373:67-373:87 Visibility: public -/

No recorded comments or reviews.

### Item 451

**[Issue #451](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/451) — Specify and Verify \`spqr::decode\_state::closure::call\_once\` in \`lib.rs\`**

Status: closed. Opened: 2026-08-16. Author: truonghoangle.

Body excerpt: /-- \[spqr::decode\_state::{impl core::ops::function::FnOnce for spqr::decode\_state::closure}::call\_once\]: Source: 'src/lib.rs', lines 480:72-480:94 -/

No recorded comments or reviews.

### Item 452

**[PR #452](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/452) — Specify and Verify \`spqr::decode\_state::closure::call\_once\` in \`lib.rs\`**

Status: merged. Opened: 2026-08-16. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::decode\_state::closure::call\_once\` in \`lib.rs\` closes #451

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/452#pullrequestreview-4949247431) — Kukovec (2026-08-17): (No text.)

### Item 453

**[Issue #453](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/453) — Verify : \`chain.rs\`**

Status: closed. Opened: 2026-08-16. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 454

**[Issue #454](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/454) — Verify and specify \`spqr::chain::ChainParams::clone\` in \`chain.rs\`**

Status: closed. Opened: 2026-08-16. Author: truonghoangle.

Body excerpt: /-- \[spqr::chain::{impl core::clone::Clone for spqr::chain::ChainParams}::clone\]: Source: 'src/chain.rs', lines 16:9-16:14 Visibility: public -/

No recorded comments or reviews.

### Item 455

**[Issue #455](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/455) — Specify and verify: \`spqr::chain::DEFAULT\_CHAIN\_PARAMS\` in \`chain.rs\`**

Status: closed. Opened: 2026-08-16. Author: truonghoangle.

Body excerpt: /-- \[spqr::chain::DEFAULT\_CHAIN\_PARAMS\] Source: 'src/chain.rs', lines 34:0-37:2 -/

No recorded comments or reviews.

### Item 456

**[Issue #456](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/456) — Specify and verify \`spqr::chain::ChainParams::default\` in \`chain.rs\`**

Status: closed. Opened: 2026-08-16. Author: truonghoangle.

Body excerpt: /-- \[spqr::chain::{impl core::default::Default for spqr::chain::ChainParams}::default\]: Source: 'src/chain.rs', lines 29:4-31:5 Visibility: public -/

No recorded comments or reviews.

### Item 457

**[Issue #457](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/457) — Specify and verify : \`spqr::chain::ChainParams::into\_pb\` in \`chain.rs\`**

Status: closed. Opened: 2026-08-16. Author: truonghoangle.

Body excerpt: /-- \[spqr::chain::{spqr::chain::ChainParams}::into\_pb\]: Source: 'src/chain.rs', lines 40:4-53:5 -/

No recorded comments or reviews.

### Item 458

**[Issue #458](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/458) — Specify and verify : \`spqr::chain::ChainParams::max\_jump\_or\_default\` in \`chain.rs\`**

Status: closed. Opened: 2026-08-16. Author: truonghoangle.

Body excerpt: /-- \[spqr::chain::{spqr::proto::pq\_ratchet::ChainParams}::max\_jump\_or\_default\]: Source: 'src/chain.rs', lines 68:4-74:5 -/

No recorded comments or reviews.

### Item 459

**[Issue #459](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/459) — Specify and verify : \`spqr::chain::ChainParams::max\_ooo\_keys\_or\_default\` in \`chain.rs\`**

Status: closed. Opened: 2026-08-16. Author: truonghoangle.

Body excerpt: /-- \[spqr::chain::{spqr::proto::pq\_ratchet::ChainParams}::max\_ooo\_keys\_or\_default\]: Source: 'src/chain.rs', lines 75:4-81:5 -/

No recorded comments or reviews.

### Item 460

**[Issue #460](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/460) — Specify and verify \`spqr::chain::ChainParams::trim\_size\` in \`chain.rs\`**

Status: closed. Opened: 2026-08-16. Author: truonghoangle.

Body excerpt: /-- \[spqr::chain::{spqr::proto::pq\_ratchet::ChainParams}::trim\_size\]: Source: 'src/chain.rs', lines 84:4-88:5 -/

No recorded comments or reviews.

### Item 461

**[PR #461](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/461) — Specify : \`spqr::decode\_state\` in \`lib.rs\`**

Status: merged. Opened: 2026-08-17. Author: truonghoangle.

Body excerpt: This PR specifies : \`spqr::decode\_state\` in \`lib.rs\` Cannot complete this proof because it requires unfolding \`proto.pq\_ratchet.PqRatchetState.Insts.ProstMessageMessage\`, which is the \`prost::message::Message\` trait impl for \`PqRatchetState\`. That definition is auto-generated protobuf serialization code replaced with \`sorry\` during translation (see aeneas-config.yml and …

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/461#issuecomment-5313914955) — github-actions[bot] (2026-08-17): ### Sorry Delta — hand-written specs \*\*2 new sorry-tainted declarations in \`Spqr.Specs.\*\`:\*\* | Module | Declaration | Kind | |--------|-------------|------| | \`Spqr.Specs.Lib.DecodeState\` | \`spqr.decode\_state\_spec\` | direct | | \`Spqr.Specs.Lib.DecodeState\` | \`spqr.decode\_state\_spec.mvcgen\_spec\` | transitive |
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/461#discussion_r3795503322) — Kukovec (2026-08-17; Spqr/Specs/Lib/DecodeState.lean:52): \`\`\`suggestion -- in the non-empty branch cannot be discharged. -- TODO: #102 \`\`\` I'd just add the TODO keyword line so it's easily searchable later.
- [review DISMISSED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/461#pullrequestreview-4950560202) — Kukovec (2026-08-17): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/461#discussion_r3795956525) — truonghoangle (2026-08-17; Spqr/Specs/Lib/DecodeState.lean:52): I fixed it as your suggestion.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/461#pullrequestreview-4951105383) — truonghoangle (2026-08-17): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/461#pullrequestreview-4951244297) — Kukovec (2026-08-17): (No text.)

### Item 462

**[PR #462](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/462) — Specify and verify \`spqr::current\_version::{impl core::ops::function::FnOnce for spqr::current\_version::closure}::call\_once\` in \`lib.rs\`**

Status: merged. Opened: 2026-08-17. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::current\_version::{impl core::ops::function::FnOnce for spqr::current\_version::closure}::call\_once\` in \`lib.rs\` closes #430

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/462#pullrequestreview-4950568677) — Kukovec (2026-08-17): (No text.)

### Item 463

**[PR #463](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/463) — Specify and verify \`spqr::proto::pq\_ratchet::{impl core::convert::TryFrom for spqr::proto::pq\_ratchet::Version}::try\_from\` in support \`lib.rs\`**

Status: merged. Opened: 2026-08-17. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::proto::pq\_ratchet::{impl core::convert::TryFrom for spqr::proto::pq\_ratchet::Version}::try\_from\` in support \`lib.rs\` closes #450

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/463#pullrequestreview-4951260464) — Kukovec (2026-08-17): (No text.)

### Item 464

**[PR #464](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/464) — Specify and verify \`spqr::current\_version\` in \`lib.rs\`**

Status: merged. Opened: 2026-08-17. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::current\_version\` in \`lib.rs\` closes #431

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/464#issuecomment-5316890161) — github-actions[bot] (2026-08-17): ### Sorry Delta — hand-written specs \*\*4 new sorry-tainted declarations in \`Spqr.Specs.\*\`:\*\* | Module | Declaration | Kind | |--------|-------------|------| | \`Spqr.Specs.Lib.CurrentVersion\` | \`spqr.current\_version\_spec\` | transitive | | \`Spqr.Specs.Lib.CurrentVersion\` | \`spqr.current\_version\_spec.match\_1\_25\` | transitive | | \`Spqr.Specs.Lib.CurrentVersion\` | \`spqr.current\_version\_spec.match\_1\_42\` | transitive | | …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/464#issuecomment-5325042805) — Kukovec (2026-08-18): !bench
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/464#issuecomment-5325044818) — baif-radar (2026-08-18): Benchmark results for 0ec265616aa300cad252af1c898c3bd07691219f against 7e68a5bd3dd3fa367137c97fdc7c9a6865d5732b are in. No significant results found. @Kukovec No significant changes detected.
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/464#discussion_r3803248102) — Kukovec (2026-08-18; Spqr/Specs/Lib/CurrentVersion.lean:52): This looks correct, but some abstraction would probably make this more readable.
- [review DISMISSED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/464#pullrequestreview-4960033334) — Kukovec (2026-08-18): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/464#discussion_r3803717432) — truonghoangle (2026-08-18; Spqr/Specs/Lib/CurrentVersion.lean:52): I rewrote it by introducing new definitions to make it easier to read
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/464#pullrequestreview-4960607015) — truonghoangle (2026-08-18): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/464#pullrequestreview-4960814995) — Kukovec (2026-08-18): (No text.)

### Item 465

**[PR #465](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/465) — Verify and specify \`spqr::chain::ChainParams::clone\` in \`chain.rs\`**

Status: merged. Opened: 2026-08-18. Author: truonghoangle.

Body excerpt: This PR verifies and specifies \`spqr::chain::ChainParams::clone\` in \`chain.rs\` closes #454

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/465#pullrequestreview-4958417090) — Kukovec (2026-08-18): (No text.)

### Item 466

**[PR #466](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/466) — Specify and verify: \`spqr::chain::DEFAULT\_CHAIN\_PARAMS\` in \`chain.rs\`**

Status: merged. Opened: 2026-08-18. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::chain::DEFAULT\_CHAIN\_PARAMS\` in \`chain.rs\` closes #455

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/466#pullrequestreview-4960929979) — Kukovec (2026-08-18): (No text.)

### Item 467

**[PR #467](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/467) — Specify and verify : \`spqr::authenticator::Authenticator::verify\_ct\`**

Status: merged. Opened: 2026-08-18. Author: oliver-butterley.

Body excerpt: Add \`spqr.authenticator.Authenticator.verify\_ct\_spec\` together with the proof Closes #192

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/467#pullrequestreview-4964290308) — truonghoangle (2026-08-18): (No text.)

### Item 468

**[PR #468](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/468) — Specify and verify : \`spqr::authenticator::Authenticator::verify\_hdr\`…**

Status: merged. Opened: 2026-08-18. Author: oliver-butterley.

Body excerpt: Add \`spqr.authenticator.Authenticator.verify\_hdr\_spec\` Closes #193

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/468#pullrequestreview-4964853639) — truonghoangle (2026-08-18): (No text.)

### Item 469

**[PR #469](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/469) — Specify and verify : \`spqr::authenticator::Authenticator::update\` and \`new\` in \`authenticator.rs\`**

Status: merged. Opened: 2026-08-18. Author: oliver-butterley.

Body excerpt: Add \`spqr.authenticator.Authenticator.update\` and \`spqr.authenticator.Authenticator.new\_spec\`. Including a refactor of axiom \`spqr.kdf.hkdf\_to\_slice\_spec\` in order to make it convenient to write these spec statements. Closes #191 Closes #16

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/469#issuecomment-5333137599) — oliver-butterley (2026-08-18): !bench
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/469#issuecomment-5333145202) — baif-radar (2026-08-18): Benchmark results for 371a962589f5f086d51c4f5da5e3b7e602dcdcb9 against e5b30e6cd36b3b60aeef1082e3aed559f531cdd2 are in. No significant results found. @oliver-butterley No significant changes detected.
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/469#pullrequestreview-4969099842) — truonghoangle (2026-08-19): (No text.)
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/469#issuecomment-5338445618) — truonghoangle (2026-08-19): Great job! I like this approach where axioms and definitions are clearly organized, especially the Crypto section.

### Item 470

**[Issue #470](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/470) — refactoring \`spqr::encoding::polynomial::{impl Decoder for PolyDecoder}::add\_chunk\` in \`polynomial.rs\`**

Status: closed. Opened: 2026-08-18. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 471

**[PR #471](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/471) — refactoring \`spqr::encoding::polynomial::{impl Decoder for PolyDecoder}::add\_chunk\` in \`polynomial.rs\`**

Status: merged. Opened: 2026-08-18. Author: truonghoangle.

Body excerpt: This PR refactored \`spqr::encoding::polynomial::{impl Decoder for PolyDecoder}::add\_chunk\` in \`polynomial.rs\`. closes #470

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/471#issuecomment-5333001491) — truonghoangle (2026-08-18): !bench
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/471#issuecomment-5333006309) — baif-radar (2026-08-18): Benchmark results for c605d1f167e5546b724375378aa490d8711e2c21 against 428af86f89dcac9df8fb7a5406782c6c323454fb are in. No significant results found. @truonghoangle No significant changes detected.
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/471#issuecomment-5339010712) — truonghoangle (2026-08-19): !bench
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/471#issuecomment-5339022107) — baif-radar (2026-08-19): Benchmark results for eb3bb4b7e1897505823e16f1c339d7e067175071 against e5b30e6cd36b3b60aeef1082e3aed559f531cdd2 are in. No significant results found. @Kukovec @truonghoangle No significant changes detected.
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/471#pullrequestreview-4969658097) — Kukovec (2026-08-19): Per Radar, this is down 14% in build time, well done.
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/471#issuecomment-5340908133) — oliver-butterley (2026-08-19): &gt; Per Radar, this is down 14% in build time, well done. For the specific file, this is a 37.8% improvement! Nicely done, @truonghoangle!

### Item 472

**[PR #472](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/472) — Specify and verify \`spqr::chain::ChainParams::default\` in \`chain.rs\`**

Status: merged. Opened: 2026-08-18. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::chain::ChainParams::default\` in \`chain.rs\` closes #456

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/472#pullrequestreview-4969729636) — Kukovec (2026-08-19): (No text.)

### Item 473

**[PR #473](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/473) — Specify and verify : spqr::chain::ChainParams::into\_pb in chain.rs**

Status: merged. Opened: 2026-08-19. Author: truonghoangle.

Body excerpt: This PR specifies and verifies : \`spqr::chain::ChainParams::into\_pb\` in \`chain.rs\` closes #457

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/473#pullrequestreview-4980357620) — Zhang-Liao (2026-08-20): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/473#pullrequestreview-4980367888) — Kukovec (2026-08-20): (No text.)

### Item 474

**[PR #474](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/474) — Specify and verify \`spqr::chain::ChainParams::max\_jump\_or\_default\` in \`chain.rs\`**

Status: merged. Opened: 2026-08-19. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::chain::ChainParams::max\_jump\_or\_default\` in \`chain.rs\` closes #458

Discussion and review record:

- [review DISMISSED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/474#pullrequestreview-4980330084) — Kukovec (2026-08-20): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/474#pullrequestreview-4991372163) — Zhang-Liao (2026-08-21): (No text.)

### Item 475

**[Issue #475](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/475) — Create Reviewer Guidelines**

Status: closed. Opened: 2026-08-19. Author: Kukovec.

Body excerpt: Complementary to PR author guidelines. Write a list of things that a reviewer should pay close attention to when looking at PRs.

No recorded comments or reviews.

### Item 476

**[PR #476](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/476) — Specify and verify : \`spqr::chain::ChainParams::max\_ooo\_keys\_or\_default\` in \`chain.rs\`**

Status: merged. Opened: 2026-08-20. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::chain::ChainParams::max\_ooo\_keys\_or\_default\` in \`chain.rs\` closes #459

Discussion and review record:

- [review DISMISSED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/476#pullrequestreview-4991433462) — Zhang-Liao (2026-08-21): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/476#pullrequestreview-4994555990) — Zhang-Liao (2026-08-21): (No text.)

### Item 477

**[Issue #477](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/477) — Specify and verify : \`spqr::chain::EPOCHS\_TO\_KEEP\_PRIOR\_TO\_SEND\_EPOCH\` in \`chain.rs\`**

Status: closed. Opened: 2026-08-20. Author: truonghoangle.

Body excerpt: /-- \[spqr::chain::EPOCHS\_TO\_KEEP\_PRIOR\_TO\_SEND\_EPOCH\] Source: 'src/chain.rs', lines 125:0-125:52 -/

No recorded comments or reviews.

### Item 478

**[Issue #478](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/478) — Specify and verify \`spqr::chain::{spqr::chain::KeyHistory}::KEY\_SIZE\` in \`chain.rs\`**

Status: closed. Opened: 2026-08-20. Author: truonghoangle.

Body excerpt: /-- \[spqr::chain::{spqr::chain::KeyHistory}::KEY\_SIZE\] Source: 'src/chain.rs', lines 130:4-130:35 -/

No recorded comments or reviews.

### Item 479

**[Issue #479](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/479) — Specify and verify \`spqr::chain::{spqr::chain::KeyHistory}::new\` in \`chain.rs\`**

Status: closed. Opened: 2026-08-20. Author: truonghoangle.

Body excerpt: /-- \[spqr::chain::{spqr::chain::KeyHistory}::new\]: Source: 'src/chain.rs', lines 132:4-136:5 -/

No recorded comments or reviews.

### Item 480

**[Issue #480](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/480) — Specify and verify : \`spqr::chain::{spqr::chain::KeyHistory}::add\` in \`chain.rs\`**

Status: closed. Opened: 2026-08-20. Author: truonghoangle.

Body excerpt: /-- \[spqr::chain::{spqr::chain::KeyHistory}::add\]: Source: 'src/chain.rs', lines 139:4-142:5 -/

No recorded comments or reviews.

### Item 481

**[Issue #481](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/481) — Specify and verify : \`spqr::chain::{spqr::chain::KeyHistory}::remove\` in \`chain.rs\`**

Status: closed. Opened: 2026-08-20. Author: truonghoangle.

Body excerpt: /-- \[spqr::chain::{spqr::chain::KeyHistory}::remove\]: Source: 'src/chain.rs', lines 175:4-182:5 -/

No recorded comments or reviews.

### Item 482

**[Issue #482](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/482) — Specify and verify : \`spqr::chain::{spqr::chain::KeyHistory}::gc\` in \`chain.rs\`**

Status: closed. Opened: 2026-08-20. Author: truonghoangle.

Body excerpt: /-- \[spqr::chain::{spqr::chain::KeyHistory}::gc\]: loop body 0: Source: 'src/chain.rs', lines 155:18-157:58 -/ /-- \[spqr::chain::{spqr::chain::KeyHistory}::gc\]: loop 0: Source: 'src/chain.rs', lines 155:18-157:58 -/ /-- \[spqr::chain::{spqr::chain::KeyHistory}::gc\]: Source: 'src/chain.rs', lines 145:4-168:5 -/

No recorded comments or reviews.

### Item 483

**[Issue #483](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/483) — Specify and verify : \`spqr::chain::{spqr::chain::KeyHistory}::clear\` in \`chain.rs\`**

Status: closed. Opened: 2026-08-20. Author: truonghoangle.

Body excerpt: /-- \[spqr::chain::{spqr::chain::KeyHistory}::clear\]: Source: 'src/chain.rs', lines 170:4-172:5 -/

No recorded comments or reviews.

### Item 484

**[Issue #484](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/484) — Specify and verify : \`spqr::chain::{spqr::chain::KeyHistory}::get\` in \`chain.rs\`**

Status: closed. Opened: 2026-08-20. Author: truonghoangle.

Body excerpt: /-- \[spqr::chain::{spqr::chain::KeyHistory}::get\]: loop body 0: Source: 'src/chain.rs', lines 197:8-207:5 -/ /-- \[spqr::chain::{spqr::chain::KeyHistory}::get\]: loop 0: Source: 'src/chain.rs', lines 197:8-207:5 -/ /-- \[spqr::chain::{spqr::chain::KeyHistory}::get\]: Source: 'src/chain.rs', lines 185:4-207:5 -/

No recorded comments or reviews.

### Item 485

**[PR #485](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/485) — Specify and verify : \`spqr::chain::EPOCHS\_TO\_KEEP\_PRIOR\_TO\_SEND\_EPOCH\` in \`chain.rs\`**

Status: merged. Opened: 2026-08-21. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::chain::EPOCHS\_TO\_KEEP\_PRIOR\_TO\_SEND\_EPOCH\` in \`chain.rs\` closes #477

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/485#pullrequestreview-5000188701) — Zhang-Liao (2026-08-22): (No text.)

### Item 486

**[PR #486](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/486) — Specify and verify \`spqr::chain::ChainParams::trim\_size\` in \`chain.rs\`**

Status: merged. Opened: 2026-08-21. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::chain::ChainParams::trim\_size\` in \`chain.rs\` closes #460

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/486#pullrequestreview-5000204744) — Zhang-Liao (2026-08-22): (No text.)

### Item 487

**[PR #487](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/487) — Specify and verify \`spqr::chain::{spqr::chain::KeyHistory}::KEY\_SIZE\` in \`chain.rs\`**

Status: merged. Opened: 2026-08-22. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::chain::{spqr::chain::KeyHistory}::KEY\_SIZE\` in \`chain.rs\` closes #478

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/487#pullrequestreview-5004769241) — Zhang-Liao (2026-08-24): (No text.)

### Item 488

**[PR #488](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/488) — Specify and verify \`spqr::chain::{spqr::chain::KeyHistory}::new\` in \`chain.rs\`**

Status: merged. Opened: 2026-08-24. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::chain::{spqr::chain::KeyHistory}::new\` in \`chain.rs\` closes #479

Discussion and review record:

- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/488#discussion_r3843355743) — Zhang-Liao (2026-08-24; Spqr/Specs/Chain/KeyHistory/New.lean:29): Could we use \`simp only\` as suggested by the style guide?
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/488#pullrequestreview-5007677079) — Zhang-Liao (2026-08-24): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/488#discussion_r3847068408) — truonghoangle (2026-08-24; Spqr/Specs/Chain/KeyHistory/New.lean:29): I fixed it
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/488#pullrequestreview-5012093540) — truonghoangle (2026-08-24): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/488#pullrequestreview-5014422610) — Zhang-Liao (2026-08-25): (No text.)

### Item 489

**[PR #489](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/489) — Specify and verify : \`spqr::chain::{spqr::chain::KeyHistory}::add\` in \`chain.rs\`**

Status: merged. Opened: 2026-08-24. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::chain::{spqr::chain::KeyHistory}::add\` in \`chain.rs\` closes #480

Discussion and review record:

- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/489#pullrequestreview-5007732071) — Zhang-Liao (2026-08-24): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/489#discussion_r3843404366) — Zhang-Liao (2026-08-24; Spqr/Specs/Chain/KeyHistory/Add.lean:7): \`import Spqr.Specs.Chain.KeyHistory.KEY\_SIZE\` seems not to be used.
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/489#discussion_r3847029084) — truonghoangle (2026-08-24; Spqr/Specs/Chain/KeyHistory/Add.lean:7): I fixed it
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/489#pullrequestreview-5012049553) — truonghoangle (2026-08-24): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/489#pullrequestreview-5014424912) — Zhang-Liao (2026-08-25): (No text.)

### Item 490

**[PR #490](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/490) — Specify and verify : \`spqr::chain::{spqr::chain::KeyHistory}::remove\` in \`chain.rs\`**

Status: merged. Opened: 2026-08-25. Author: truonghoangle.

Body excerpt: This PR specifies and verifies : \`spqr::chain::{spqr::chain::KeyHistory}::remove\` in \`chain.rs\` closes #481

Discussion and review record:

- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/490#discussion_r3850162976) — Zhang-Liao (2026-08-25; Spqr/Specs/Chain/KeyHistory/Remove.lean:46): \`h\_bound\` is not needed since its type \`Vec α := { l // l.length ≤ Usize.max }\` already gives it. Drop.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/490#pullrequestreview-5015642476) — Zhang-Liao (2026-08-25): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/490#discussion_r3850340218) — truonghoangle (2026-08-25; Spqr/Specs/Chain/KeyHistory/Remove.lean:46): I fixed it. Thank you for your comments!
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/490#pullrequestreview-5015848142) — truonghoangle (2026-08-25): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/490#pullrequestreview-5018742440) — Zhang-Liao (2026-08-25): (No text.)

### Item 491

**[PR #491](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/491) — Specify and verify : \`spqr::chain::{spqr::chain::KeyHistory}::gc\` in \`chain.rs\`**

Status: merged. Opened: 2026-08-25. Author: truonghoangle.

Body excerpt: This PR specifies and verifies : \`spqr::chain::{spqr::chain::KeyHistory}::gc\` in \`chain.rs\` closes #482

Discussion and review record:

- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/491#discussion_r3859395024) — Zhang-Liao (2026-08-26; Spqr/Specs/Chain/KeyHistory/Gc.lean:358): \`h\_platform\` does not exist in the preconditions of \`gc\_spec\`
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/491#pullrequestreview-5026477376) — Zhang-Liao (2026-08-26): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/491#discussion_r3859790813) — Zhang-Liao (2026-08-26; Spqr/Specs/Chain/KeyHistory/Gc.lean:393): The specification is too weak. The error is that it does not confirm if \`self.data\` contains valid data, they should be kept in \`result\`. Below is a counterexample: Assume the code \`\`\` fn gc2(&amp;mut self, current\_key: u32, params: &amp;ChainParams) { if self.data.len() &gt;= params.trim\_size() \* Self::KEY\_SIZE { self.data.clear(); // remove all keys including thoese unexpired } } \`\`\` The function \`gc2\` is clearly wrong since …
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/491#pullrequestreview-5026938943) — Zhang-Liao (2026-08-26): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/491#discussion_r3885432901) — truonghoangle (2026-08-29; Spqr/Specs/Chain/KeyHistory/Gc.lean:358): I removed it.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/491#pullrequestreview-5056699220) — truonghoangle (2026-08-29): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/491#discussion_r3885433452) — truonghoangle (2026-08-29; Spqr/Specs/Chain/KeyHistory/Gc.lean:393): I fixed it
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/491#pullrequestreview-5056699934) — truonghoangle (2026-08-29): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/491#discussion_r3891545574) — Zhang-Liao (2026-08-31; Spqr/Specs/Chain/KeyHistory/Gc.lean:393): I think it is still insufficient. If \`self = \[A(live), E(expired)\]\` and \`result = \[A, A\]\`, the \`gc\` function is still wrong since \`A\` is doubled. We should confirm that multiset(live in result) = multiset(live in A).
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/491#pullrequestreview-5062937816) — Zhang-Liao (2026-08-31): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/491#discussion_r3891643031) — Zhang-Liao (2026-08-31; Spqr/Specs/Chain/KeyHistory/Gc.lean:432): The requirement for \`current\_key.val\` is \`assert!(current\_key &gt;= max\_ooo\_keys\_or\_default())\`. The defintion of \`max\_ooo\_keys\_or\_default\`(chain.rs:75-81) is \`\`\` fn max\_ooo\_keys\_or\_default(&amp;self) -&gt; u32 { if self.max\_ooo\_keys &gt; 0 { self.max\_ooo\_keys } else { DEFAULT\_CHAIN\_PARAMS.max\_ooo\_keys } } \`\`\` When \`max\_ooo\_keys = 5\`, then \`current\_key.val\` can be \`6,\` which does not satisfy \`h\_key\_def\`
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/491#pullrequestreview-5063043847) — Zhang-Liao (2026-08-31): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/491#discussion_r3894086145) — truonghoangle (2026-08-31; Spqr/Specs/Chain/KeyHistory/Gc.lean:393): I have updated it to fully include the properties and preconditions.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/491#pullrequestreview-5065992838) — truonghoangle (2026-08-31): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/491#discussion_r3894091191) — truonghoangle (2026-08-31; Spqr/Specs/Chain/KeyHistory/Gc.lean:432): I fixed it. Thank you for the very valuable comments.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/491#pullrequestreview-5065999155) — truonghoangle (2026-08-31): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/491#pullrequestreview-5066194476) — Zhang-Liao (2026-08-31): (No text.)

### Item 492

**[PR #492](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/492) — Update mechanism for installing charon/aeneas**

Status: merged. Opened: 2026-08-27. Author: oliver-butterley.

Body excerpt: This PR uses an updated mechanism for installing charon and aeneas: instead of building from source it downloads the github release artifact. This is quicker and uses much less storage locally. Moreover the lean project is set to use aeneas from the github release tag and so can automatically obtain cache from there rather than rebuilding aeneas.

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/492#pullrequestreview-5039860291) — Kukovec (2026-08-27): (No text.)

### Item 493

**[PR #493](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/493) — Update aeneas to nightly 2026.08.27 5b9dcf3**

Status: merged. Opened: 2026-08-27. Author: oliver-butterley.

Body excerpt: Update Aeneas to the latest version. Two proofs needed a very minor change to make them work. Another proof (Spqr/Specs/V1/Chunked/States/Serialize/Message/Deserialize.lean) also broke. This PR substatially refactors the proof. Surely it was possible to mend the proof with very minor changes but the refactored proof is also shorter than the previous version.

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/493#issuecomment-5440274454) — oliver-butterley (2026-08-27): !bench
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/493#issuecomment-5440276448) — baif-radar (2026-08-27): Benchmark results for bf478da73fe530c87d7a7137281bf325d5f6e816 against 4cf0b6d184f906e2e30c9634a646d8bbb0a02ff1 are in. No significant results found. @oliver-butterley No significant changes detected.
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/493#pullrequestreview-5042507260) — Kukovec (2026-08-27): (No text.)

### Item 494

**[PR #494](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/494) — Specify and verify : \`spqr::chain::{spqr::chain::KeyHistory}::get\` in \`chain.rs\`**

Status: merged. Opened: 2026-08-31. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::chain::{spqr::chain::KeyHistory}::get\` in \`chain.rs\` closes #484

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/494#pullrequestreview-5076074132) — Zhang-Liao (2026-09-01): (No text.)

### Item 495

**[Issue #495](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/495) — Specify and verify \`spqr::chain::{spqr::chain::ChainEpochDirection}::new\` in \`chain.rs\`**

Status: closed. Opened: 2026-08-31. Author: truonghoangle.

Body excerpt: /-- \[spqr::chain::{spqr::chain::ChainEpochDirection}::new\]: Source: 'src/chain.rs', lines 212:4-218:5 -/

No recorded comments or reviews.

### Item 496

**[PR #496](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/496) — Specify and verify : \`spqr::chain::{spqr::chain::KeyHistory}::clear\` in \`chain.rs\`**

Status: merged. Opened: 2026-08-31. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::chain::{spqr::chain::KeyHistory}::clear\` in \`chain.rs\` closes #483

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/496#pullrequestreview-5076267570) — Zhang-Liao (2026-09-01): (No text.)

### Item 497

**[Issue #497](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/497) — specify and verify \`spqr::chain::{spqr::chain::ChainEpochDirection}::next\_key\_internal\` in \`chain.rs\`**

Status: closed. Opened: 2026-08-31. Author: truonghoangle.

Body excerpt: /-- \[spqr::chain::{spqr::chain::ChainEpochDirection}::next\_key\_internal\]: Source: 'src/chain.rs', lines 228:4-245:5 -/

No recorded comments or reviews.

### Item 498

**[Issue #498](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/498) — Specify and verify \`spqr::chain::{spqr::chain::ChainEpochDirection}::next\_key\` in \`chain.rs\`**

Status: closed. Opened: 2026-08-31. Author: truonghoangle.

Body excerpt: /-- \[spqr::chain::{spqr::chain::ChainEpochDirection}::next\_key\]: Source: 'src/chain.rs', lines 221:4-224:5 -/

No recorded comments or reviews.

### Item 499

**[Issue #499](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/499) — Specify and verify \`spqr::chain::{spqr::chain::ChainEpochDirection}::key\` in \`chain.rs\`**

Status: closed. Opened: 2026-08-31. Author: truonghoangle.

Body excerpt: /-- \[spqr::chain::{spqr::chain::ChainEpochDirection}::key\]: loop body 0: Source: 'src/chain.rs', lines 270:8-286:9 -/ /-- \[spqr::chain::{spqr::chain::ChainEpochDirection}::key\]: loop 0: Source: 'src/chain.rs', lines 270:8-286:9 -/ /-- \[spqr::chain::{spqr::chain::ChainEpochDirection}::key\]: Source: 'src/chain.rs', lines 247:4-296:5 -/

No recorded comments or reviews.

### Item 500

**[Issue #500](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/500) — Specify and verify \`spqr::chain::{spqr::chain::ChainEpochDirection}::into\_pb\` in \`chain.rs\`**

Status: closed. Opened: 2026-08-31. Author: truonghoangle.

Body excerpt: /-- \[spqr::chain::{spqr::chain::ChainEpochDirection}::into\_pb\]: Source: 'src/chain.rs', lines 298:4-304:5 -/

No recorded comments or reviews.

### Item 501

**[Issue #501](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/501) — Specify and verify : \`spqr::chain::{spqr::chain::ChainEpochDirection}::from\_pb\` in \`chain.rs\`**

Status: closed. Opened: 2026-08-31. Author: truonghoangle.

Body excerpt: /-- \[spqr::chain::{spqr::chain::ChainEpochDirection}::from\_pb\]: Source: 'src/chain.rs', lines 306:4-312:5 -/

No recorded comments or reviews.

### Item 502

**[Issue #502](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/502) — specify and verify \`spqr::chain::{spqr::chain::ChainEpochDirection}::clear\_next\` in \`chain.rs\`**

Status: closed. Opened: 2026-08-31. Author: truonghoangle.

Body excerpt: /-- \[spqr::chain::{spqr::chain::ChainEpochDirection}::clear\_next\]: Source: 'src/chain.rs', lines 314:4-316:5 -/

No recorded comments or reviews.

### Item 503

**[PR #503](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/503) — Erasure Codes bridge**

Status: open draft. Opened: 2026-09-01. Author: a-dangelo.

Body excerpt: This PR adds a \`Protocols\` library and proves that the extracted SPQR erasure code, wrapped as an \`ErasureCode\`, is correct in the model's sense: \`concreteSpqrErasureCode\_correct\` in \`Protocols/ErasureCode/Correct.lean\`. For a message of \`k\` chunks, decoding any \`k\` of its encoded chunks (distinct indices, any order) returns the message, and decoding fewer returns \`none\`. The proof goes through the secure-messaging …

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/503#issuecomment-5496178451) — github-actions[bot] (2026-09-01): ### Sorry Delta — hand-written specs \*\*4 new sorry-tainted declarations in \`Spqr.Specs.\*\`:\*\* | Module | Declaration | Kind | |--------|-------------|------| | \`Spqr.Specs.Encoding.Polynomial.PolyEncoder.ChunkAt\` | \`\_private.Spqr.Specs.Encoding.Polynomial.PolyEncoder.ChunkAt.0.spqr.encoding.polynomial.PolyEncoder.chunk\_at\_loop\_spec\_points\` | transitive | | \`Spqr.Specs.Encoding.Polynomial.PolyEncoder.ChunkAt\` | …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/503#issuecomment-5590685000) — github-actions[bot] (2026-09-08): ### Sorry Delta — hand-written specs \*\*4 new sorry-tainted declarations in \`Spqr.Specs.\*\`:\*\* | Module | Declaration | Kind | |--------|-------------|------| | \`Spqr.Specs.Encoding.Polynomial.PolyEncoder.ChunkAt\` | \`\_private.Spqr.Specs.Encoding.Polynomial.PolyEncoder.ChunkAt.0.spqr.encoding.polynomial.PolyEncoder.chunk\_at\_loop\_spec\_points\` | transitive | | \`Spqr.Specs.Encoding.Polynomial.PolyEncoder.ChunkAt\` | …

### Item 504

**[PR #504](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/504) — Specify and verify \`spqr::chain::{spqr::chain::ChainEpochDirection}::new\` in \`chain.rs\`**

Status: merged. Opened: 2026-09-02. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::chain::{spqr::chain::ChainEpochDirection}::new\` in \`chain.rs\` closes #495

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/504#pullrequestreview-5086365114) — Zhang-Liao (2026-09-02): (No text.)

### Item 505

**[PR #505](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/505) — specify and verify \`spqr::chain::{spqr::chain::ChainEpochDirection}::next\_key\_internal\` in \`chain.rs\`**

Status: merged. Opened: 2026-09-02. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::chain::{spqr::chain::ChainEpochDirection}::next\_key\_internal\` in \`chain.rs\` closes #497

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/505#issuecomment-5505978037) — Zhang-Liao (2026-09-02): !radar
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/505#issuecomment-5506003339) — Zhang-Liao (2026-09-02): !bench
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/505#issuecomment-5506345829) — truonghoangle (2026-09-02): !bench
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/505#issuecomment-5510342564) — baif-radar (2026-09-02): Benchmark results for a29a1f0d63713b1ed734e0f580c187b3d241de56 against f858b0951311717a0ef0dc04839be745cd23ba3f are in. (These commits have already been benchmarked in a previous command.) No significant results found. @Zhang-Liao \*\*Small changes (2🟥)\*\* - 🟥 \`build/module/Spqr.Crypto.Hkdf//instructions\`: \*\*+561.4M\*\* (\*\*+7.21%\*\*) - 🟥 \`build/profile/import//wall-clock\`: \*\*+1m 7s\*\* (\*\*+11.76%\*\*)
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/505#issuecomment-5510342750) — baif-radar (2026-09-02): Benchmark results for a29a1f0d63713b1ed734e0f580c187b3d241de56 against f858b0951311717a0ef0dc04839be745cd23ba3f are in. (These commits have already been benchmarked in a previous command.) No significant results found. @Zhang-Liao \*\*Small changes (2🟥)\*\* - 🟥 \`build/module/Spqr.Crypto.Hkdf//instructions\`: \*\*+561.4M\*\* (\*\*+7.21%\*\*) - 🟥 \`build/profile/import//wall-clock\`: \*\*+1m 7s\*\* (\*\*+11.76%\*\*)
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/505#issuecomment-5510342982) — baif-radar (2026-09-02): Benchmark results for a29a1f0d63713b1ed734e0f580c187b3d241de56 against f858b0951311717a0ef0dc04839be745cd23ba3f are in. (These commits have already been benchmarked in a previous command.) No significant results found. @truonghoangle \*\*Small changes (2🟥)\*\* - 🟥 \`build/module/Spqr.Crypto.Hkdf//instructions\`: \*\*+561.4M\*\* (\*\*+7.21%\*\*) - 🟥 \`build/profile/import//wall-clock\`: \*\*+1m 7s\*\* (\*\*+11.76%\*\*)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/505#discussion_r3920623273) — Zhang-Liao (2026-09-03; Spqr/Specs/Aeneas/SliceListToVec.lean:4): Who is Cline?
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/505#pullrequestreview-5097302527) — Zhang-Liao (2026-09-03): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/505#discussion_r3921247441) — truonghoangle (2026-09-03; Spqr/Specs/Aeneas/SliceListToVec.lean:4): I fixed it. I fixed it. I used AI to generate the initial drafts, and it occasionally changed the names like this when I asked it to split large files into smaller ones for better control.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/505#pullrequestreview-5097996427) — truonghoangle (2026-09-03): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/505#pullrequestreview-5098928950) — Zhang-Liao (2026-09-03): (No text.)

### Item 506

**[PR #506](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/506) — Specify and verify \`serialize::Error\` \`Debug::fmt\` and \`Display::fmt\` in \`serialize.rs\`**

Status: merged. Opened: 2026-09-02. Author: Zhang-Liao.

Body excerpt: This PR specifies and verifies \`spqr::serialize::{impl core::fmt::Debug for spqr::serialize::Error}::fmt\` and \`spqr::serialize::{impl core::fmt::Display for spqr::serialize::Error}::fmt\` in \`serialize.rs\`. Both are two-branch dispatches on the fieldless enum calling \`Formatter::write\_str\`. Spec: \`result.1 = .Ok () ∧ result.2 = f\`, same shape and proof as \`Spqr/Specs/Lib/SecretOutput/Fmt.lean\`. New files: - …

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/506#pullrequestreview-5105335613) — truonghoangle (2026-09-03): (No text.)

### Item 507

**[PR #507](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/507) — Specify and verify \`spqr::chain::{spqr::chain::ChainEpochDirection}::next\_key\` in \`chain.rs\`**

Status: merged. Opened: 2026-09-03. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::chain::{spqr::chain::ChainEpochDirection}::next\_key\` in \`chain.rs\` closes #498

Discussion and review record:

- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/507#discussion_r3949215071) — w-woloszyn (2026-09-07; Spqr/Specs/Aeneas/VecDerefMut.lean:32): \`\`\`suggestion rw \[WP.spec\_ok\] constructor · rfl · intro s rfl \`\`\`
- [review DISMISSED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/507#pullrequestreview-5131376116) — w-woloszyn (2026-09-07): This has been waiting for review for a little while, so I took a pass over it. I don’t see any blocking issues. That said, I’m not that familiar with this codebase, so I’m also completely fine if you wait for a reviewer with more context before merging.
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/507#discussion_r3949348219) — truonghoangle (2026-09-07; Spqr/Specs/Aeneas/VecDerefMut.lean:32): I fixed it as you suggested. Thank you for the comments.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/507#pullrequestreview-5131536572) — truonghoangle (2026-09-07): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/507#pullrequestreview-5131580299) — w-woloszyn (2026-09-07): Approved, pending CI checks :)

### Item 508

**[PR #508](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/508) — Specify and verify \`spqr::chain::{spqr::chain::ChainEpochDirection}::key\` in \`chain.rs\`**

Status: merged. Opened: 2026-09-07. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::chain::{spqr::chain::ChainEpochDirection}::key\` in \`chain.rs\`. Note that I have split the task into two separate files: one for the 32-byte case and one for the 64-byte case. closes #499

Discussion and review record:

- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/508#discussion_r3953811367) — Zhang-Liao (2026-09-08; Spqr/Specs/Chain/ChainEpochDirection/Key32.lean:19): The \`h\_platform\` hypothesis is never used in any specification of this file.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/508#pullrequestreview-5136662355) — Zhang-Liao (2026-09-08): (No text.)
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/508#issuecomment-5578209580) — Zhang-Liao (2026-09-08): &gt; one for the 32-byte case and one for the 64-byte case. A minor comment is that they are 32-bit case and 64-bit case in the description of the PR.
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/508#discussion_r3954422046) — truonghoangle (2026-09-08; Spqr/Specs/Chain/ChainEpochDirection/Key32.lean:19): I fixed it.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/508#pullrequestreview-5137432686) — truonghoangle (2026-09-08): (No text.)
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/508#issuecomment-5579470804) — truonghoangle (2026-09-08): &gt; A minor comment is that they are 32-bit case and 64-bit case in the description of the PR. In the 64-bit case, the hypotheses are specific to 64-bit systems because the required bounds do not hold for 32-bit systems. However, a theorem proved for the 32-bit case also applies to the 64-bit case, since the corresponding bounds are satisfied there as well.
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/508#pullrequestreview-5137938965) — Zhang-Liao (2026-09-08): (No text.)

### Item 509

**[PR #509](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/509) — Specify and verify \`spqr::chain::{spqr::chain::ChainEpochDirection}::into\_pb\` in \`chain.rs\`**

Status: merged. Opened: 2026-09-08. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::chain::{spqr::chain::ChainEpochDirection}::into\_pb\` in \`chain.rs\` closes #500

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/509#pullrequestreview-5150551790) — Zhang-Liao (2026-09-09): (No text.)

### Item 510

**[Issue #510](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/510) — Specify and verify \`spqr::chain::{spqr::chain::Chain}::ced\_for\_direction\` in \`chain.rs\`**

Status: closed. Opened: 2026-09-08. Author: truonghoangle.

Body excerpt: /-- \[spqr::chain::{spqr::chain::Chain}::ced\_for\_direction\]: Source: 'src/chain.rs', lines 322:4-327:5 -/

No recorded comments or reviews.

### Item 511

**[Issue #511](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/511) — Specify and verify \`spqr::chain::{spqr::chain::Chain}::new\` in \`chain.rs\`**

Status: closed. Opened: 2026-09-08. Author: truonghoangle.

Body excerpt: /-- \[spqr::chain::{spqr::chain::Chain}::new\]: Source: 'src/chain.rs', lines 329:4-348:5 Visibility: public -/

No recorded comments or reviews.

### Item 512

**[Issue #512](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/512) — Specify and verify : \`spqr::{spqr::proto::pq\_ratchet::Direction}::switch\` in \`lib.rs\`**

Status: closed. Opened: 2026-09-08. Author: truonghoangle.

Body excerpt: /-- \[spqr::{spqr::proto::pq\_ratchet::Direction}::switch\]: Source: 'src/lib.rs', lines 65:4-70:5 Visibility: public -/

No recorded comments or reviews.

### Item 513

**[Issue #513](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/513) — Specify and verify \`spqr::chain::{spqr::chain::Chain}::add\_epoch\` in \`chain.rs\`**

Status: closed. Opened: 2026-09-08. Author: truonghoangle.

Body excerpt: /-- \[spqr::chain::{spqr::chain::Chain}::add\_epoch\]: Source: 'src/chain.rs', lines 350:4-369:5 Visibility: public -/

No recorded comments or reviews.

### Item 514

**[Issue #514](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/514) — Specify and verify \`spqr::chain::{spqr::chain::Chain}::epoch\_idx\` in \`chain.rs\`**

Status: closed. Opened: 2026-09-08. Author: truonghoangle.

Body excerpt: /-- \[spqr::chain::{spqr::chain::Chain}::epoch\_idx\]: Source: 'src/chain.rs', lines 372:4-382:5 -/

No recorded comments or reviews.

### Item 515

**[Issue #515](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/515) — Specify and verify \`spqr::chain::{spqr::chain::Chain}::send\_key\` in \`chain.rs\`**

Status: closed. Opened: 2026-09-08. Author: truonghoangle.

Body excerpt: /-- \[spqr::chain::{spqr::chain::Chain}::send\_key\]: loop body 0: Source: 'src/chain.rs', lines 391:12-395:13 Visibility: public -/ /-- \[spqr::chain::{spqr::chain::Chain}::send\_key\]: loop 0: Source: 'src/chain.rs', lines 391:12-395:13 Visibility: public -/ /-- \[spqr::chain::{spqr::chain::Chain}::send\_key\]: loop body 1: Source: 'src/chain.rs', lines 396:12-399:13 Visibility: public -/ /-- …

No recorded comments or reviews.

### Item 516

**[Issue #516](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/516) — specify and verify \`spqr::chain::{spqr::chain::Chain}::recv\_key\` in \`chain.rs\`**

Status: closed. Opened: 2026-09-08. Author: truonghoangle.

Body excerpt: /-- \[spqr::chain::{spqr::chain::Chain}::recv\_key\]: Source: 'src/chain.rs', lines 409:4-412:5 Visibility: public -/

No recorded comments or reviews.

### Item 517

**[Issue #517](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/517) — Specify and verify \`spqr::chain::call\_mut\` in \`chain.rs\`**

Status: closed. Opened: 2026-09-08. Author: truonghoangle.

Body excerpt: /-- \[spqr::chain::{spqr::chain::Chain}::into\_pb::{impl core::ops::function::FnMut for spqr::chain::{spqr::chain::Chain}::into\_pb::closure}::call\_mut\]: Source: 'src/chain.rs', lines 423:21-426:17 -/

No recorded comments or reviews.

### Item 518

**[Issue #518](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/518) — Specify and verify \`spqr::chain::call\_once\` in \`chain.rs\`**

Status: closed. Opened: 2026-09-08. Author: truonghoangle.

Body excerpt: /-- \[spqr::chain::{spqr::chain::Chain}::into\_pb::{impl core::ops::function::FnOnce for spqr::chain::{spqr::chain::Chain}::into\_pb::closure}::call\_once\]: Source: 'src/chain.rs', lines 423:21-426:17 -/

No recorded comments or reviews.

### Item 519

**[Issue #519](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/519) — Specify \`spqr::chain::{spqr::chain::Chain}::into\_pb\` in \`chain.rs\`**

Status: closed. Opened: 2026-09-08. Author: truonghoangle.

Body excerpt: /-- \[spqr::chain::{spqr::chain::Chain}::into\_pb\]: Source: 'src/chain.rs', lines 415:4-431:5 -/

No recorded comments or reviews.

### Item 520

**[Issue #520](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/520) — Specify and verify \`spqr::chain::{spqr::chain::Chain}::into\_pb::closure::call\_mut\` in \`chain.rs\`**

Status: closed. Opened: 2026-09-08. Author: truonghoangle.

Body excerpt: /-- \[spqr::chain::{spqr::chain::Chain}::from\_pb::{impl core::ops::function::FnMut&gt; for spqr::chain::{spqr::chain::Chain}::from\_pb::closure#1}::call\_mut\]: Source: 'src/chain.rs', lines 443:21-448:17 -/

No recorded comments or reviews.

### Item 521

**[Issue #521](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/521) — Specify and verify \`spqr::chain::{spqr::chain::Chain}::into\_pb::closure::call\_once\` in \`chain.rs\`**

Status: closed. Opened: 2026-09-08. Author: truonghoangle.

Body excerpt: /-- \[spqr::chain::{spqr::chain::Chain}::into\_pb::{impl core::ops::function::FnOnce for spqr::chain::{spqr::chain::Chain}::into\_pb::closure}::call\_once\]: Source: 'src/chain.rs', lines 423:21-426:17 -/

No recorded comments or reviews.

### Item 522

**[Issue #522](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/522) — Specify \`spqr::chain::{spqr::chain::Chain}::from\_pb\` in \`chain.rs\`**

Status: closed. Opened: 2026-09-08. Author: truonghoangle.

Body excerpt: /-- \[spqr::chain::{spqr::chain::Chain}::from\_pb\]: Source: 'src/chain.rs', lines 434:4-452:5 -/

No recorded comments or reviews.

### Item 523

**[Issue #523](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/523) — Verify : \`v1/chunked/send\_ek/serialize.rs\`**

Status: open. Opened: 2026-09-08. Author: MarkusFerdinandDablander.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 524

**[Issue #524](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/524) — Specify and verify : \`spqr::v1::chunked::send\_ek::serialize::{spqr::v1::chunked::send\_ek::KeysUnsampled}::into\_pb\` in \`v1/chunked/send\_ek/serialize.rs\`**

Status: closed. Opened: 2026-09-08. Author: MarkusFerdinandDablander.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 525

**[Issue #525](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/525) — Specify and verify : \`spqr::v1::chunked::send\_ek::serialize::{spqr::v1::chunked::send\_ek::KeysUnsampled}::from\_pb\` in \`v1/chunked/send\_ek/serialize.rs\`**

Status: closed. Opened: 2026-09-08. Author: MarkusFerdinandDablander.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 526

**[Issue #526](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/526) — Specify and verify : \`spqr::v1::chunked::send\_ek::serialize::{spqr::v1::chunked::send\_ek::KeysSampled}::into\_pb\` in \`v1/chunked/send\_ek/serialize.rs\`**

Status: closed. Opened: 2026-09-08. Author: MarkusFerdinandDablander.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 527

**[Issue #527](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/527) — Specify and verify : \`spqr::v1::chunked::send\_ek::serialize::{spqr::v1::chunked::send\_ek::KeysSampled}::from\_pb\` in \`v1/chunked/send\_ek/serialize.rs\`**

Status: closed. Opened: 2026-09-08. Author: MarkusFerdinandDablander.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 528

**[Issue #528](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/528) — Specify and verify : \`spqr::v1::chunked::send\_ek::serialize::{spqr::v1::chunked::send\_ek::HeaderSent}::into\_pb\` in \`v1/chunked/send\_ek/serialize.rs\`**

Status: open. Opened: 2026-09-08. Author: MarkusFerdinandDablander.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 529

**[Issue #529](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/529) — Specify and verify : \`spqr::v1::chunked::send\_ek::serialize::{spqr::v1::chunked::send\_ek::HeaderSent}::from\_pb\` in \`v1/chunked/send\_ek/serialize.rs\`**

Status: open. Opened: 2026-09-08. Author: MarkusFerdinandDablander.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 530

**[Issue #530](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/530) — Specify and verify : \`spqr::v1::chunked::send\_ek::serialize::{spqr::v1::chunked::send\_ek::Ct1Received}::into\_pb\` in \`v1/chunked/send\_ek/serialize.rs\`**

Status: open. Opened: 2026-09-08. Author: MarkusFerdinandDablander.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 531

**[Issue #531](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/531) — Specify and verify : \`spqr::v1::chunked::send\_ek::serialize::{spqr::v1::chunked::send\_ek::Ct1Received}::from\_pb\` in \`v1/chunked/send\_ek/serialize.rs\`**

Status: open. Opened: 2026-09-08. Author: MarkusFerdinandDablander.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 532

**[Issue #532](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/532) — Specify and verify : \`spqr::v1::chunked::send\_ek::serialize::{spqr::v1::chunked::send\_ek::EkSentCt1Received}::into\_pb\` in \`v1/chunked/send\_ek/serialize.rs\`**

Status: open. Opened: 2026-09-08. Author: MarkusFerdinandDablander.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 533

**[Issue #533](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/533) — Specify and verify : \`spqr::v1::chunked::send\_ek::serialize::{spqr::v1::chunked::send\_ek::EkSentCt1Received}::from\_pb\` in \`v1/chunked/send\_ek/serialize.rs\`**

Status: open. Opened: 2026-09-08. Author: MarkusFerdinandDablander.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 534

**[PR #534](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/534) — Specify and verify: \`spqr::v1::chunked::send\_ek::serialize::{spqr::v1::chunked::send\_ek::KeysUnsampled}::into\_pb\` in \`v1/chunked/send\_ek/serialize.rs\`**

Status: merged. Opened: 2026-09-08. Author: MarkusFerdinandDablander.

Body excerpt: Hi, I am back :-) hope you have been well. This PR specifies and verifies \`spqr::v1::chunked::send\_ek::serialize::{spqr::v1::chunked::send\_ek::KeysUnsampled}::into\_pb\` in \`v1/chunked/send\_ek/serialize.rs\`. Closes #524

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/534#pullrequestreview-5145462347) — truonghoangle (2026-09-08): (No text.)
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/534#issuecomment-5589857742) — truonghoangle (2026-09-08): Great job! Welcome back!

### Item 535

**[PR #535](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/535) — Specify and verify : \`spqr::chain::{spqr::chain::ChainEpochDirection}::from\_pb\` in \`chain.rs\`**

Status: merged. Opened: 2026-09-09. Author: truonghoangle.

Body excerpt: This PR specifies and verifies : \`spqr::chain::{spqr::chain::ChainEpochDirection}::from\_pb\` in \`chain.rs\` closes #501

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/535#pullrequestreview-5163456480) — Zhang-Liao (2026-09-10): (No text.)

### Item 536

**[PR #536](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/536) — specify and verify \`spqr::chain::{spqr::chain::ChainEpochDirection}::clear\_next\` in \`chain.rs\`**

Status: merged. Opened: 2026-09-09. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::chain::{spqr::chain::ChainEpochDirection}::clear\_next\` in \`chain.rs\` closes #502

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/536#pullrequestreview-5163491773) — Zhang-Liao (2026-09-10): (No text.)

### Item 537

**[PR #537](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/537) — Specify and verify: \`spqr::v1::chunked::send\_ek::serialize::{spqr::v1::chunked::send\_ek::KeysUnsampled}::from\_pb\` in \`v1/chunked/send\_ek/serialize.rs\`**

Status: merged. Opened: 2026-09-09. Author: MarkusFerdinandDablander.

Body excerpt: This PR specifies and verifies \`spqr::v1::chunked::send\_ek::serialize::{spqr::v1::chunked::send\_ek::KeysUnsampled}::from\_pb\` in \`v1/chunked/send\_ek/serialize.rs\`. Closes #525

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/537#pullrequestreview-5158310776) — truonghoangle (2026-09-09): (No text.)

### Item 538

**[PR #538](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/538) — Specify and verify \`spqr::chain::{spqr::chain::Chain}::ced\_for\_direction\` in \`chain.rs\`**

Status: merged. Opened: 2026-09-10. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::chain::{spqr::chain::Chain}::ced\_for\_direction\` in \`chain.rs\` closes #510

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/538#pullrequestreview-5175256263) — Zhang-Liao (2026-09-11): (No text.)

### Item 539

**[PR #539](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/539) — Specify and verify : \`spqr::{spqr::proto::pq\_ratchet::Direction}::switch\` in \`lib.rs\`**

Status: merged. Opened: 2026-09-10. Author: truonghoangle.

Body excerpt: This PR specifies and verifies : \`spqr::{spqr::proto::pq\_ratchet::Direction}::switch\` in \`lib.rs\` closes #512

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/539#pullrequestreview-5175262270) — Zhang-Liao (2026-09-11): (No text.)

### Item 540

**[PR #540](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/540) — Specify and verify \`spqr::chain::{spqr::chain::Chain}::new\` in \`chain.rs\`**

Status: merged. Opened: 2026-09-11. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::chain::{spqr::chain::Chain}::new\` in \`chain.rs\` closes #511

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/540#pullrequestreview-5193493432) — Zhang-Liao (2026-09-14): (No text.)

### Item 541

**[PR #541](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/541) — Specify and verify \`spqr::chain::{spqr::chain::Chain}::add\_epoch\` in \`chain.rs\`**

Status: merged. Opened: 2026-09-11. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::chain::{spqr::chain::Chain}::add\_epoch\` in \`chain.rs\` closes #513

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/541#pullrequestreview-5193549287) — Zhang-Liao (2026-09-14): (No text.)

### Item 542

**[PR #542](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/542) — Specify and verify: \`spqr::v1::chunked::send\_ek::serialize::{spqr::v1::chunked::send\_ek::KeysSampled}::into\_pb\` in \`v1/chunked/send\_ek/serialize.rs\`**

Status: merged. Opened: 2026-09-11. Author: MarkusFerdinandDablander.

Body excerpt: This PR specifies and verifies \`spqr::v1::chunked::send\_ek::serialize::{spqr::v1::chunked::send\_ek::KeysSampled}::into\_pb\` in \`v1/chunked/send\_ek/serialize.rs\`. Closes #526

Discussion and review record:

- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/542#discussion_r3989732968) — truonghoangle (2026-09-11; Spqr/Specs/V1/Chunked/SendEk/Serialize/KeysSampled/IntoPb.lean:49): Can we replace ∃ by using \`match\`?
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/542#pullrequestreview-5179333655) — truonghoangle (2026-09-11): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/542#discussion_r3990454547) — MarkusFerdinandDablander (2026-09-11; Spqr/Specs/V1/Chunked/SendEk/Serialize/KeysSampled/IntoPb.lean:49): Hi @truonghoangle, thanks for the quick and useful comment! :-) I used the existential in order to avoid restating the very long postcondition of \`PolyEncoder::into\_pb\` inside this theorem. But I agree that \`\`\`lean ∃ pe, PolyEncoder.into\_pb self.sending\_hdr = ok pe ∧ … \`\`\` may be somewhat shallow, as it only characterises the result in terms of the extracted function rather than in terms of values. Before I …
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/542#pullrequestreview-5180163021) — MarkusFerdinandDablander (2026-09-11): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/542#discussion_r3991864628) — truonghoangle (2026-09-11; Spqr/Specs/V1/Chunked/SendEk/Serialize/KeysSampled/IntoPb.lean:49): You have pinpointed exactly what I wanted to see. We could have two spec theorems for the same function here: one, like (a), simply describes the value returned by the function; the second (b)-which I prefer-connects the different components and is more broadly useful externally. For the second type, since the specification is quite long, it could obscure the main idea for human readers and make future applications …
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/542#pullrequestreview-5181763489) — truonghoangle (2026-09-11): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/542#discussion_r4004142721) — MarkusFerdinandDablander (2026-09-14; Spqr/Specs/V1/Chunked/SendEk/Serialize/KeysSampled/IntoPb.lean:49): Hi @truonghoangle thanks for your useful answer; this all makes sense! :-) I will then aim for the following plan: - I will create a separate PR where I implement a suitable predicate in \`Spqr.Specs.Encoding.Polynomial.PolyEncoder.IntoPb\` to condense the long postcondition and refactor the spec theorem \`PolyEncoder.into\_pb\_spec\` to a more concise, human-readable form via the new predicate. - I will then submit this …
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/542#pullrequestreview-5196423083) — MarkusFerdinandDablander (2026-09-14): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/542#discussion_r4017596856) — MarkusFerdinandDablander (2026-09-15; Spqr/Specs/V1/Chunked/SendEk/Serialize/KeysSampled/IntoPb.lean:49): Hi @truonghoangle following our recent useful discussion from above, I have now used the newly introduced predicate for \`PolyEncoder::into\_pb\` to contruct an improved version of the spec theorem for \`spqr::v1::chunked::send\_ek::serialize::KeysSampled::into\_pb\`. The core part is now formulated as follows: \`\`\`lean4 into\_pb self ⦃ (result : proto.pq\_ratchet.v1\_state.chunked.KeysSampled) =&gt; ∃ pe, …
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/542#pullrequestreview-5212425827) — MarkusFerdinandDablander (2026-09-15): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/542#discussion_r4022595423) — truonghoangle (2026-09-16; Spqr/Specs/V1/Chunked/SendEk/Serialize/KeysSampled/IntoPb.lean:49): I think we still lack the uniqueness of \`pe\` when writing with \`∃\`. What do you think if it is in form \`\`\` lean theorem into\_pb\_spec (self : v1.chunked.send\_ek.KeysSampled) (h\_overflow\_points : ∀ points, self.sending\_hdr.s = .Points points → ∀ j match result with | { uc := some uc, sending\_hdr := some pe } =&gt; uc = { epoch := self.uc.epoch, auth := some { root\_key := self.uc.auth.root\_key, mac\_key := …
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/542#pullrequestreview-5218617461) — truonghoangle (2026-09-16): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/542#discussion_r4024972267) — MarkusFerdinandDablander (2026-09-16; Spqr/Specs/V1/Chunked/SendEk/Serialize/KeysSampled/IntoPb.lean:49): Hi @truonghoangle thanks for your comments! I think both final proposed forms of the spec theorem (the one with \`match\` and the one with the existential) are mathematically equivalent, and the uniqueness of \`pe\` strictly follows in both cases from the truth of \`PolyEncoder.IntoPbPostCond self.sending\_hdr pe\`, since this predicate is only true for at most one \`pe\` (the unique \`pe\` compatible with \`self.sending\_hdr\`). …
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/542#pullrequestreview-5221461179) — MarkusFerdinandDablander (2026-09-16): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/542#pullrequestreview-5221932153) — truonghoangle (2026-09-16): (No text.)

### Item 543

**[PR #543](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/543) — Specify and verify \`spqr::chain::{spqr::chain::Chain}::epoch\_idx\` in \`chain.rs\`**

Status: merged. Opened: 2026-09-14. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::chain::{spqr::chain::Chain}::epoch\_idx\` in \`chain.rs\` closes #514

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/543#pullrequestreview-5207654402) — Zhang-Liao (2026-09-15): (No text.)

### Item 544

**[Issue #544](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/544) — Implement predicate to condense spec theorem for \`PolyEncoder.into\_pb\`**

Status: closed. Opened: 2026-09-14. Author: MarkusFerdinandDablander.

Body excerpt: See discussion #542

No recorded comments or reviews.

### Item 545

**[PR #545](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/545) — Implement predicate to condense spec theorem for \`PolyEncoder.into\_pb\`**

Status: merged. Opened: 2026-09-14. Author: MarkusFerdinandDablander.

Body excerpt: This PR executes part of the plan laid out in @truonghoangle's and my discussion in #542 via implementing the postcondition for \`PolyEncoder.into\_pb\_spec\` as a separate predicate. This allows a concise, more human-readable formulation of \`PolyEncoder.into\_pb\_spec\` and other related downstream spec theorems associated with the conversion of PolyEncoder types into protobuffer form. Closes #544

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/545#pullrequestreview-5201843175) — truonghoangle (2026-09-14): (No text.)

### Item 546

**[PR #546](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/546) — Specify and verify \`spqr::chain::{spqr::chain::Chain}::send\_key\` in \`chain.rs\`**

Status: merged. Opened: 2026-09-15. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::chain::{spqr::chain::Chain}::send\_key\` in \`chain.rs\` closes #515

Discussion and review record:

- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/546#discussion_r4017476950) — Zhang-Liao (2026-09-15; Spqr/Specs/Chain/Chain/SendKey.lean:350): There seems to be some problem here. I will look at it in detail tomorrow.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/546#pullrequestreview-5212272383) — Zhang-Liao (2026-09-15): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/546#discussion_r4024173386) — Zhang-Liao (2026-09-16; Spqr/Specs/Chain/Chain/SendKey.lean:367): I think there should also be a condition on \`self.send\_epoch == epoch -&gt;\`. When \`self.send\_epoch == epoch -&gt;\`, something can also be inferred. Claude Code suggests \`\`\` (self.send\_epoch = epoch → ∀ j, j ≠ phys → result.2.links.buf.val\[j\]? = self.links.buf.val\[j\]?) ∧ \`\`\` The above condition may be incorrect, but it may give you some inspiration.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/546#pullrequestreview-5220521768) — Zhang-Liao (2026-09-16): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/546#discussion_r4025449229) — truonghoangle (2026-09-16; Spqr/Specs/Chain/Chain/SendKey.lean:367): Thank you for your comment! I have added the specific property for this branch.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/546#pullrequestreview-5221999778) — truonghoangle (2026-09-16): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/546#discussion_r4033049095) — Zhang-Liao (2026-09-17; Spqr/Specs/Chain/Chain/Defs.lean:34): I suggest you remove \`@\[simp\]\` for \`sendKeyEi\`. It causes a linting error \`\`\` lake exe runLinter Spqr Running linter on specified modules: \[Spqr\] -- Found 1 error in 949 declarations (plus 9984 automatically generated ones) in Spqr with 16 linters /- The \`simpNF\` linter reports: SOME SIMP LEMMAS ARE NOT IN SIMP-NORMAL FORM. Please change the lemma to make sure their left-hand sides are in simp normal form. To learn …
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/546#pullrequestreview-5230952725) — Zhang-Liao (2026-09-17): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/546#discussion_r4033104845) — truonghoangle (2026-09-17; Spqr/Specs/Chain/Chain/Defs.lean:34): I fixed it. I tried out a few technical things and forgot to remove them!
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/546#pullrequestreview-5231028693) — truonghoangle (2026-09-17): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/546#pullrequestreview-5231437068) — Zhang-Liao (2026-09-17): (No text.)

### Item 547

**[PR #547](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/547) — Phase 1 PR A: verification gates and catalog provenance**

Status: closed unmerged. Opened: 2026-09-15. Author: astefano.

Body excerpt: Builds the five-gate local runner and retrofits a resolving \`Source:\` citation onto every row of the SPQR correctness catalog, so a property's provenance is machine-checkable before any proof work starts. \*\*Deliverables\*\* - \`docs/ISSUE\_TEMPLATE.md\` becomes a per-property \*\*PR\*\* checklist, and the phantom \`#check\_no\_sorry\` gate — which does not exist in this repository — is removed from …

No recorded comments or reviews.

### Item 548

**[Issue #548](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/548) — CI lint step misses linter errors on auto-generated declarations (greps for \`error:\`, ignores exit code)**

Status: closed. Opened: 2026-09-17. Author: Zhang-Liao.

Body excerpt: ## Summary The "Lint hand-written code" step in \`.github/workflows/lean.yml\` only fails when the linter output contains the literal string \`error:\`. The Batteries linter does not always print that string, so a whole class of lint failures passes CI silently. ## How the linter formats its output \`runLinter\` calls \`formatLinterResults ... (useErrorFormat := true)\`. In \`Batteries/Tactic/Lint/Frontend.lean\` …

No recorded comments or reviews.

### Item 549

**[PR #549](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/549) — Fail CI lint step on runLinter exit code instead of grepping for \`error:\`**

Status: merged. Opened: 2026-09-17. Author: Zhang-Liao.

Body excerpt: This PR makes the "Lint hand-written code" step in \`.github/workflows/lean.yml\` fail whenever \`lake exe runLinter Spqr\` exits non-zero, instead of grepping its output for the literal string \`error:\`. Previously the step ran the linter with \`|| true\`, discarding its exit code, and only failed if the log contained \`error:\`. The Batteries linter uses the \`file:line:col: error:\` format only for declarations with a …

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/549#pullrequestreview-5233135217) — truonghoangle (2026-09-17): (No text.)

### Item 550

**[PR #550](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/550) — specify and verify \`spqr::chain::{spqr::chain::Chain}::recv\_key\` in \`chain.rs\`**

Status: merged. Opened: 2026-09-17. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::chain::{spqr::chain::Chain}::recv\_key\` in \`chain.rs\` closes #516 closes #552 closes #553 closes #554 closes #555 closes #556

Discussion and review record:

- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/550#pullrequestreview-5245489209) — Zhang-Liao (2026-09-18): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/550#discussion_r4044840558) — Zhang-Liao (2026-09-18; Spqr/Specs/Chain/Chain/RecvKey.lean:82): The postcondition should also constrain \`result.2.links\`. Currently it specifies the returned key/error but drops the state transition performed by \`ChainEpochDirection.key\`. Consider extracting the existing postcondition of \`key\_spec\` into a reusable predicate \`keyPost\`, and lifting it through the deque update, for example: \`\`\` | some ce =&gt; ∃ newRecv : chain.ChainEpochDirection, result.2.dir = self.dir ∧ …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/550#issuecomment-5750540674) — truonghoangle (2026-09-20): !bench
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/550#issuecomment-5750543748) — baif-radar (2026-09-20): Benchmark results for 1e54b6639a8553a77ed9783adb07c04d8a8a9f8b against f7cea5daa90f888c7689aa5145ff57949249d799 are in. There are significant results. @truonghoangle - 🟥 \`bench\` exited with code \*\*1\*\* \*\*Large changes (1🟥)\*\* - 🟥 \`build/module/Spqr.Specs.Chain.Chain.Defs//instructions\`: \*\*+9.5G\*\* (\*\*+127.50%\*\*) \*\*Medium changes (1✅)\*\* - ✅ \`build/profile/grind ematch//wall-clock\`: \*\*-2m 28s\*\* (\*\*-48.21%\*\*) \*\*Small …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/550#issuecomment-5750833434) — truonghoangle (2026-09-20): !bench
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/550#issuecomment-5750837721) — baif-radar (2026-09-20): Benchmark results for 7d386a868fcea08b77a4fd2156bc5186da4e7d2c against f7cea5daa90f888c7689aa5145ff57949249d799 are in. There are significant results. @truonghoangle \*\*Large changes (3✅, 1🟥)\*\* - 🟥 \`build/module/Spqr.Specs.Chain.Chain.Defs//instructions\`: \*\*+9.5G\*\* (\*\*+127.66%\*\*) - ✅ \`build/module/Spqr.Specs.Chain.ChainEpochDirection.Key//instructions\`: \*\*-195.3G\*\* (\*\*-35.89%\*\*) - ✅ …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/550#issuecomment-5756975917) — truonghoangle (2026-09-21): !bench
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/550#issuecomment-5756976341) — baif-radar (2026-09-21): Benchmark results for dd7d5a640f35de9dd06abf1f5a404e01139b13b3 against f7cea5daa90f888c7689aa5145ff57949249d799 are in. There are significant results. @truonghoangle \*\*Large changes (3✅, 1🟥)\*\* - 🟥 \`build/module/Spqr.Specs.Chain.Chain.Defs//instructions\`: \*\*+8.7G\*\* (\*\*+116.78%\*\*) - ✅ \`build/module/Spqr.Specs.Chain.ChainEpochDirection.Key//instructions\`: \*\*-213.9G\*\* (\*\*-39.32%\*\*) - ✅ …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/550#issuecomment-5762758242) — truonghoangle (2026-09-21): !bench
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/550#issuecomment-5762771706) — baif-radar (2026-09-21): Benchmark results for ed794bb2e4487c4697c3d4f8ee6607a04b83e532 against f7cea5daa90f888c7689aa5145ff57949249d799 are in. There are significant results. @truonghoangle \*\*Large changes (3✅, 1🟥)\*\* - 🟥 \`build/module/Spqr.Specs.Chain.Chain.Defs//instructions\`: \*\*+8.7G\*\* (\*\*+116.73%\*\*) - ✅ \`build/module/Spqr.Specs.Chain.ChainEpochDirection.Key//instructions\`: \*\*-213.3G\*\* (\*\*-39.19%\*\*) - ✅ …
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/550#pullrequestreview-5273987530) — Zhang-Liao (2026-09-22): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/550#discussion_r4068318647) — Zhang-Liao (2026-09-22; Spqr/Specs/Chain/Chain/Defs.lean:162): Lines 156–162 are vacuous: \`khPreGc := ce'.recv.prev\` satisfies them (clauses 2–5 of \`keyPostGc\` with \`f = g = id\`), so \`prev\` is unconstrained in the advance case. Suggest reusing \`cedKeyPost\` defined in this file and we can write \`recvKeyEpochPost\` like \`\`\` def recvKeyEpochPost (self : chain.Chain) (index : U32) (ce ce' : chain.ChainEpoch) (result : core.result.Result (alloc.vec.Vec U8) Error) : Prop := ce'.send = …
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/550#discussion_r4069282830) — Zhang-Liao (2026-09-22; Spqr/Specs/Chain/Chain/Defs.lean:240): \`recvKeyPost32\` does not constrain \`self'.links\` (see my earlier comment on \`recv\_key\_spec\`): it only fixes five scalar fields of \`self'\`, and \`recvKeyEpochPost32\` does not even take the updated entry \`ce'\`. The 32-bit and 64-bit versions differ only in the precondition constants; the postcondition should be the same. Since \`key\_spec\_32\` already yields \`cedKeyPost\` with no platform hypothesis, \`recv\_key\_spec\_32\` can …
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/550#pullrequestreview-5275136066) — Zhang-Liao (2026-09-22): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/550#discussion_r4071426176) — truonghoangle (2026-09-22; Spqr/Specs/Chain/Chain/Defs.lean:162): I fixed it! thank you for your comments!
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/550#pullrequestreview-5277804650) — truonghoangle (2026-09-22): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/550#discussion_r4071426957) — truonghoangle (2026-09-22; Spqr/Specs/Chain/Chain/Defs.lean:240): I fixed it! thank you for your comments!
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/550#pullrequestreview-5277805685) — truonghoangle (2026-09-22): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/550#pullrequestreview-5279630882) — Zhang-Liao (2026-09-22): (No text.)

### Item 551

**[Issue #551](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/551) — Generalise and condense spec theorem for \`PolyEncoder.from\_pb\`**

Status: closed. Opened: 2026-09-18. Author: MarkusFerdinandDablander.

Body excerpt: @truonghoangle I am proposing to use the already introduced predicate \`IntoPbPostCond\` for \`PolyEncoder.into\_pb\` from Issue #544 to formulate a higher-level and slightly stronger, total version of the spec theorem for \`PolyEncoder.from\_pb\` which does not require input hypotheses and is significantly more concise and human-readable, while mathematically implying the currently formulated spec theorem. The new theorem …

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/551#issuecomment-5730707292) — truonghoangle (2026-09-18): It's absolutely wonderful. Great job!

### Item 552

**[Issue #552](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/552) — refactor \`Spqr/Specs/Chain/KeyHistory/Gc.lean\`**

Status: closed. Opened: 2026-09-20. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 553

**[Issue #553](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/553) — refactor \`Spqr/Specs/Chain/ChainEpochDirection/Key.lean\`**

Status: closed. Opened: 2026-09-20. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 554

**[Issue #554](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/554) — refactoring \`Spqr/Specs/Chain/ChainEpochDirection/Key32.lean\`**

Status: closed. Opened: 2026-09-20. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 555

**[Issue #555](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/555) — refactoring \`Spqr/Specs/Chain/Chain/SendKey.lean\`**

Status: closed. Opened: 2026-09-20. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 556

**[Issue #556](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/556) — refactoring \`Spqr/Specs/Chain/Chain/SendKey64.lean\`**

Status: closed. Opened: 2026-09-20. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 557

**[PR #557](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/557) — Strengthen spec theorem for \`PolyEncoder.from\_pb\` into a concise, high-level, total characterisation**

Status: merged. Opened: 2026-09-21. Author: MarkusFerdinandDablander.

Body excerpt: This PR replaces the spec theorem for \`spqr::encoding::polynomial::PolyEncoder::from\_pb\` with a total one: it drops all three input hypotheses and explicitly pins down the error case. The previous \`from\_pb\_spec\` assumed \`h\_polys\_nonempty\`, \`h\_polys\_even\` and \`h\_pts\_even\`, and stayed silent about inputs the function rejects. Callers therefore had to discharge those hypotheses on downstream specs and could not …

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/557#issuecomment-5760640006) — MarkusFerdinandDablander (2026-09-21): !bench
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/557#issuecomment-5760646021) — baif-radar (2026-09-21): Benchmark results for ea47c33863491dd662e296904e57b2d552cba81d against f7cea5daa90f888c7689aa5145ff57949249d799 are in. There are significant results. @MarkusFerdinandDablander \*\*Large changes (1🟥)\*\* - 🟥 \`build/module/Spqr.Specs.Encoding.Polynomial.PolyEncoder.FromPb//instructions\`: \*\*+76.6G\*\* (\*\*+73.27%\*\*) \*\*Small changes (3🟥)\*\* - 🟥 \`build/module/Spqr.Auxiliary.Aeneas.ArraySlice//instructions\`: \*\*+367.0M\*\* …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/557#issuecomment-5761704276) — truonghoangle (2026-09-21): Great job! When formulating this theorem, I was unsure whether to include the error branches in the postcondition. While doing so makes the theorem more comprehensive, it might also increase the number of branches to handle during application. What do you think about placing the postcondition definitions in a separate file, distinct from the theorem itself, and reorganizing and rephrasing their implications(if it …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/557#issuecomment-5775915588) — MarkusFerdinandDablander (2026-09-22): Hi @truonghoangle thank you for your useful comments! :-) \*\*Concerning the refactoring of the predicates and connecting lemma into a separate \`Defs.lean\` file:\*\* Thank you for this great suggestion, which I believe would indeed be a much better and cleaner approach going forward. I have thus refactored this PR based on your idea to reflect this new, more maintainable and clearer structure by introducing a …
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/557#pullrequestreview-5277656657) — truonghoangle (2026-09-22): (No text.)
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/557#issuecomment-5776027739) — truonghoangle (2026-09-22): Great job!

### Item 558

**[Issue #558](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/558) — Consolidate duplicated \`Inhabited Point\` and \`Inhabited Poly\` instances**

Status: closed. Opened: 2026-09-22. Author: MarkusFerdinandDablander.

Body excerpt: ## Problem Spec statements index into extracted collections with \`xs\[j\]!\`. That form is total, so it needs an \`Inhabited\` instance to supply the value returned when the index is out of range. Those instances were declared ad hoc, once per file that needed one, rather than once per type. Two filler types are declared 8 times between them, seven of those under \`Spqr/Specs/Encoding/Polynomial/\` and one under …

No recorded comments or reviews.

### Item 559

**[PR #559](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/559) — Specify and verify \`spqr::chain::call\_mut\` in \`chain.rs\`**

Status: merged. Opened: 2026-09-23. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::chain::call\_mut\` in \`chain.rs\` closes #517

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/559#pullrequestreview-5287179083) — Zhang-Liao (2026-09-23): (No text.)

### Item 560

**[PR #560](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/560) — Consolidate duplicated \`Inhabited Point\` and \`Inhabited Poly\` instances**

Status: merged. Opened: 2026-09-23. Author: MarkusFerdinandDablander.

Body excerpt: ## Summary This PR consolidates scattered instance duplicates, so that \`Point\` and \`Poly\` now each have exactly one \`Inhabited\` instance, and all specs use it: | Type | Single origin | | --- | --- | | \`Point\` | \`PolyEncoder.instInhabitedPoint\` in \`PolyEncoder/Defs.lean\` | | \`Poly\` | \`instInhabitedPoly\_spqr\` in \`Math/Poly/Identities/Basic.lean\` (unchanged) | Before, there were 8 declarations (\`Point\` ×5, \`Poly\` ×3). …

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/560#pullrequestreview-5288579371) — truonghoangle (2026-09-23): (No text.)

### Item 561

**[PR #561](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/561) — Specify and verify \`spqr::chain::call\_once\` in \`chain.rs\`**

Status: merged. Opened: 2026-09-23. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::chain::call\_once\` in \`chain.rs\` closes #518

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/561#pullrequestreview-5289399289) — Zhang-Liao (2026-09-23): (No text.)

### Item 562

**[PR #562](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/562) — Specify and verify \`spqr::chain\_from\_version\_negotiation::{impl core::ops::function::FnOnce for spqr::chain\_from\_version\_negotiation::closure}::call\_once\` in \`lib.rs\`**

Status: merged. Opened: 2026-09-23. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::chain\_from\_version\_negotiation::{impl core::ops::function::FnOnce for spqr::chain\_from\_version\_negotiation::closure}::call\_once\` in \`lib.rs\` closes #432

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/562#issuecomment-5797295010) — Zhang-Liao (2026-09-23): This file is in the wrong directory. The closure belongs to chain\_from\_version\_negotiation; Error is only its return type. The repo convention is to file closure specs under the enclosing function, e.g. \`Lib/DecodeState/CallOnce.lean\`, \`Lib/CurrentVersion/CallOnce.lean\`, and \`Chain/Chain/Epoch/CallOnce.lean\`. Please move it to \`Spqr/Specs/Lib/ChainFromVersionNegotiation/CallOnce.lean\` and update the import in …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/562#issuecomment-5797422751) — truonghoangle (2026-09-23): I fixed it. Thank you for your comments.
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/562#pullrequestreview-5298889923) — Zhang-Liao (2026-09-24): (No text.)

### Item 563

**[PR #563](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/563) — Specify and verify: \`spqr::v1::chunked::send\_ek::serialize::{spqr::v1::chunked::send\_ek::KeysSampled}::from\_pb\` in \`v1/chunked/send\_ek/serialize.rs\`**

Status: merged. Opened: 2026-09-23. Author: MarkusFerdinandDablander.

Body excerpt: This PR specifies and verifies \`spqr::v1::chunked::send\_ek::serialize::{spqr::v1::chunked::send\_ek::KeysSampled}::from\_pb\` in \`v1/chunked/send\_ek/serialize.rs\`. Due to the recently introduced mathematical predicates, refactorings and generalisations (see PRs #545 and #557), this spec theorem can now be formulated in line with the following desired properties: - Totality (includes and pins down all error paths) - …

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/563#pullrequestreview-5292987823) — truonghoangle (2026-09-23): (No text.)
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/563#issuecomment-5797586194) — truonghoangle (2026-09-23): Great job!

### Item 564

**[Issue #564](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/564) — Specify and verify : \`spqr::proto::pq\_ratchet::{impl core::convert::TryFrom for spqr::proto::pq\_ratchet::Direction}::try\_from\`**

Status: closed. Opened: 2026-09-24. Author: truonghoangle.

Body excerpt: /-- \[spqr::proto::pq\_ratchet::{impl core::convert::TryFrom for spqr::proto::pq\_ratchet::Direction}::try\_from\]: Source: 'generated/signal.proto.pq\_ratchet.rs', lines 402:67-402:87 Visibility: public -/

No recorded comments or reviews.

### Item 565

**[PR #565](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/565) — Specify and verify : spqr::proto::pq\_ratchet::{impl core::convert::TryFrom for spqr::proto::pq\_ratchet::Direction}::try\_from**

Status: merged. Opened: 2026-09-24. Author: truonghoangle.

Body excerpt: This PR specifies and verifies : spqr::proto::pq\_ratchet::{impl core::convert::TryFrom for spqr::proto::pq\_ratchet::Direction}::try\_from closes #564

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/565#pullrequestreview-5315167974) — Zhang-Liao (2026-09-25): (No text.)

### Item 566

**[Issue #566](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/566) — \`Poly::serialize/deserialize\` fail to round-trip zero polynomials**

Status: closed. Opened: 2026-09-24. Author: truonghoangle.

Body excerpt: \`Poly::serialize\` encodes a zero polynomial as \`\[\]\`, but \`Poly::deserialize\` rejects empty input. Therefore, \`PolyEncoder::from\_pb(into\_pb(e))\` fails whenever a \`PolyEncoder\` contains an \`empty/zero\` polynomial. This occurs for short messages where some of the \`16\` polynomial slots receive no points (e.g. a \`10\`-byte message leaves \`11\` empty slots). Although \`V1 protocol\` message sizes do not trigger this, …

No recorded comments or reviews.

### Item 567

**[PR #567](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/567) — \`Poly::serialize/deserialize\` fail to round-trip zero polynomials**

Status: merged. Opened: 2026-09-24. Author: truonghoangle.

Body excerpt: This PR worked as follows: \*\*\`Spqr/Specs/Encoding/Polynomial/Poly/Deserialize.lean\`\*\* \`deserialize\_spec\` rewritten on the basis of defect 16: - Dropped the \`h\_nonempty\` and \`h\_even\` hypotheses, which previously \*assumed away\* exactly the behaviour the defect is about. Only the \`Usize\` overflow side condition remains. - The postcondition is now a \*\*total characterisation\*\*: - \`Ok poly\` ⇒ \`serialized.length ≠ 0 ∧ …

Discussion and review record:

- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/567#discussion_r4102706242) — Zhang-Liao (2026-09-25; Spqr/Specs/Encoding/Polynomial/Poly/Deserialize.lean:151): I cannot find the file \`docs/defects.md\` in this repo.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/567#pullrequestreview-5315470465) — Zhang-Liao (2026-09-25): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/567#discussion_r4102711062) — Zhang-Liao (2026-09-25; Spqr/Specs/Encoding/Polynomial/Poly/Serialize.lean:175): I cannot find \`docs/defects.md\` in this repo.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/567#pullrequestreview-5315476176) — Zhang-Liao (2026-09-25): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/567#discussion_r4103321688) — truonghoangle (2026-09-25; Spqr/Specs/Encoding/Polynomial/Poly/Deserialize.lean:151): I am going to remove this comment, as it belongs to a record of how I identify these types of errors when writing specifications. In fact, I have been systematically reviewing specifications and their representations, specifically looking at how functions link together, where the postcondition of one function serves as the precondition for another, to better understand their interdependencies. During this process, I …
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/567#pullrequestreview-5316207421) — truonghoangle (2026-09-25): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/567#discussion_r4103360294) — truonghoangle (2026-09-25; Spqr/Specs/Encoding/Polynomial/Poly/Deserialize.lean:151): I fixed it
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/567#pullrequestreview-5316251440) — truonghoangle (2026-09-25): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/567#discussion_r4103378027) — truonghoangle (2026-09-25; Spqr/Specs/Encoding/Polynomial/Poly/Serialize.lean:175): I fixed it
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/567#pullrequestreview-5316273178) — truonghoangle (2026-09-25): (No text.)
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/567#issuecomment-5831998133) — Zhang-Liao (2026-09-25): After I reviewed the PR, I noticed that there may be a small bug in the Rust implementation. Do you think it is really a bug? \*\*Bug\*\*: \`Poly::serialize\` and \`Poly::deserialize\` are not inverses on the zero polynomial. Location: src/encoding/polynomial.rs:343 Cause: zero polynomial has empty coefficients, so serialize outputs \`\[\]\`. deserialize starts with if \`serialized.is\_empty() { return Err(SerializationInvalid) …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/567#issuecomment-5832246093) — truonghoangle (2026-09-25): Yes, this is a \`real bug\` from a theoretical standpoint: \`serialize\` and \`deserialize\` lack round-trip consistency for the zero polynomial (empty coefficients). \`serialize\` produces \`\[\]\`, but \`deserialize\` rejects empty input at line 343. However, the impact assessment in your description is accurate: \*\*it's a latent/theoretical bug with no practical impact in V1\*\*. Zero polynomials do not arise in actual protocol …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/567#issuecomment-5833780919) — Zhang-Liao (2026-09-25): @oliver-butterley I wonder what your opinion is. Do you think we should consider it a bug in the implementation? I feel it may be wrong if a future version of SPQR does not constrain the length of the input to be serialized.
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/567#issuecomment-5834508133) — oliver-butterley (2026-09-25): Do I understand correctly that zero polynomials never occur is an invariant of the way the code is defined? I.e., it is guaranteed that the polynomial is never zero and hence the round trip property does hold given the invariant? As such, perhaps the specs could also describe this? If so then it's similar to with the elliptic curve points we worked with before: the bare Rust structure could have any tuple of numbers …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/567#issuecomment-5836674678) — truonghoangle (2026-09-25): &gt; Do I understand correctly that zero polynomials never occur is an invariant of the way the code is defined? I.e., it is guaranteed that the polynomial is never zero and hence the round trip property does hold given the invariant? Yes, that's correct for V1 protocol usage. Here's why: \`encode\_bytes\` distributes 2-byte words round-robin across 16 polynomial slots. Each "round" consumes 16 × 2 = 32 bytes. So a …
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/567#pullrequestreview-5379221174) — Zhang-Liao (2026-10-01): (No text.)

### Item 568

**[Issue #568](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/568) — Harmonise all \`from\_pb/into\_pb\` pairs via functional models and prove round trips**

Status: open. Opened: 2026-09-24. Author: MarkusFerdinandDablander.

Body excerpt: ## Overview 26 different \`from\_pb\` functions are in scope for specification and verification. 15 have a sorry-free spec theorem; 11 are open. 14 of the 15 use only the builtin axioms; \`PolyDecoder.from\_pb\_spec\` also depends on the Aeneas library type axiom \`core.fmt.Formatter\`. | File | \`from\_pb\` of | Status | |---|---|---| | \`authenticator/serialize.rs\` | \`Authenticator\` | ✅ | | \`chain.rs\` | \`ChainEpochDirection\` | …

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/568#issuecomment-5813244694) — MarkusFerdinandDablander (2026-09-24): @truonghoangle what do you think about this proposed strategy to harmonise all spec theorems for \`from\_pb\` via the abstract, general form I outlined above in order to create a more unified interface for these specs? If you indeed agree that this would be a good idea, I would attempt to tackle this issue; otherwise, if you have any concerns, or other thoughts, kindly let me know :-)
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/568#issuecomment-5814065774) — truonghoangle (2026-09-24): @MarkusFerdinandDablander The specifications of \`from\_pb\` need to be related to the specifications of \`into\_pb\` in a relationship as follows. - \*\*\`into\_pb\` / \`from\_pb\`\*\*: These are \*\*serialization and deserialization inverses\*\* (a roundtrip pair). The natural Lean relationship would be a \*\*roundtrip theorem\*\*: \`\`\`lean theorem from\_pb\_into\_pb\_roundtrip (x : NoHeaderReceived) : from\_pb (into\_pb x) = Ok x \`\`\` This …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/568#issuecomment-5867171067) — MarkusFerdinandDablander (2026-09-28): Hi @truonghoangle, thank you for your useful reply! :-) I agree on the following points: - \*\*\`match\` over \`if\`:\*\* \`match\` is likely clearer and better suited to the round-trip proofs, so I will go with it! - \*\*Abstract general form for \`into\_pb\`:\*\* as far as I can see \`into\_pb\` never has any error type paths, so a general spec theorem template likely needs only the no-panic input hypotheses and a postcondition that …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/568#issuecomment-5868901413) — truonghoangle (2026-09-28): I support this plan; everything is clear and transparent.
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/568#issuecomment-5910626915) — MarkusFerdinandDablander (2026-09-30): @truonghoangle here again our strategy for reference :-) After further discussion and comments in PR #571, we have now converged to the following strategy to achieve an elegant, harmonised and scalable high-level architecture for the verification of the many \`from\_pb\` and \`into\_pb\` pairs which has already shown some early success: ## The strategy 1. \*\*Every \`into\_pb\` and \`from\_pb\` gets a functional model:\*\* a total, …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/568#issuecomment-5912032304) — MarkusFerdinandDablander (2026-09-30): \*\*Scope note on chain.rs\*\* The 24 sub-issues attached here cover 24 of the 26 \`from\_pb\`/\`into\_pb\` pairs. The two remaining pairs, \`ChainEpochDirection::{into\_pb, from\_pb}\` and \`Chain::{into\_pb, from\_pb}\` in \`chain.rs\`, are owned by @truonghoangle under #577 and PR #578. Also, for the record, \`ChainParams::into\_pb\` has no \`from\_pb\` partner and is thus out of scope here.
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/568#issuecomment-5913345450) — truonghoangle (2026-09-30): @MarkusFerdinandDablander I would also suggest that, when examining round-trip behavior, you carefully consider whether the preconditions of \`from\_pb\` match the postconditions of \`into\_pb\`, and vice versa. You may encounter incompatibilities in certain areas, which would then warrant further investigation.
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/568#issuecomment-6016972167) — MarkusFerdinandDablander (2026-10-06): @truonghoangle this is a great point! In purely mathematical language, one could perhaps think about this via the following formal framework: \*\*Setting.\*\* Let $\`T\`$ be the translated state type, $\`P\`$ its protobuf type and $\`E\`$ the error type. The functional models are total functions \`\`\`math \\mathsf{intoPb} \\colon T \\to P, \\qquad \\mathsf{fromPb} \\colon P \\to \\mathrm{Ok}(T) \\sqcup \\mathrm{Err}(E). \`\`\` Let \`\`\`math S …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/568#issuecomment-6018220959) — truonghoangle (2026-10-06): @MarkusFerdinandDablander Great job! The proposed RT1/RT2 framework is mathematically sound for a canonical, information-preserving serialization pair. However, RT2 implicitly assumes that successful decoding is injective at the protobuf-representation level. In realistic protobuf parsers, decoding may be many-to-one due to noncanonical encodings, omitted or default fields, unknown fields, normalization, or other …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/568#issuecomment-6036065894) — MarkusFerdinandDablander (2026-10-07): Hi @truonghoangle thanks for usefully extending this framework with this brilliant analysis of the non-canonical case; this all makes sense! A quick survey conducted by me with assistance from Claude Code suggests the following numbers: - In total, there are \*\*26\*\* \`from\_pb\`/\`into\_pb\` pairs in \`src\` (\`ChainParams\` is excluded since it has \`into\_pb\` only). - \*\*18\*\* are strictly canonical, i.e. \`C\_P = S\_P\` and the …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/568#issuecomment-6036206068) — truonghoangle (2026-10-07): @MarkusFerdinandDablander Great job! That is basically what I had envisioned, but this detailed and meticulous classification will help us pinpoint any bugs.

### Item 569

**[PR #569](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/569) — Specify and verify \`spqr::chain\_from\_version\_negotiation\` in \`lib.rs\`**

Status: merged. Opened: 2026-09-25. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::chain\_from\_version\_negotiation\` in \`lib.rs\` closes #433

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/569#pullrequestreview-5338955815) — Zhang-Liao (2026-09-28): (No text.)

### Item 570

**[PR #570](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/570) — Specify and verify \`spqr::chain::{spqr::chain::Chain}::into\_pb::closure::call\_mut\` in \`chain.rs\`**

Status: merged. Opened: 2026-09-28. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::chain::{spqr::chain::Chain}::into\_pb::closure::call\_mut\` in \`chain.rs\` closes #520

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/570#issuecomment-5887743763) — Zhang-Liao (2026-09-29): I find the title and issue don't match the code. The title and closes #520 say \`from\_pb::call\_mut\`, but the file specs \`into\_pb::closure::call\_mut\` (chain.rs:423-426). \`from\_pb::closure#1::call\_mut\` already has a spec in \`Spqr/Specs/Chain/Chain/Epoch/CallMut.lean\`. The title needs changing to \`into\_pb\`, and #520 needs a check: either it's already done, or this PR needs its own issue.
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/570#issuecomment-5887942044) — truonghoangle (2026-09-29): I fixed title and issue!
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/570#pullrequestreview-5351080011) — Zhang-Liao (2026-09-29): (No text.)

### Item 571

**[PR #571](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/571) — New proposed verification architecture for \`from\_pb\` and \`into\_pb\` pairs based on functional models**

Status: merged. Opened: 2026-09-28. Author: MarkusFerdinandDablander.

Body excerpt: Hi @truonghoangle, I hope you are well! :-) After further reflection on our discussion in #568, I think there may be a way to make the specification and verification of the \`into\_pb\`/\`from\_pb\` pairs even more scalable and elegant than the predicate-based templates I proposed earlier this morning in #568. This PR prototypes the proposed verification architecture on two hierarchically connected \`from\_pb\` and \`into\_pb\` …

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/571#pullrequestreview-5350245112) — truonghoangle (2026-09-29): (No text.)

### Item 572

**[PR #572](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/572) — Specify and verify \`spqr::chain::{spqr::chain::Chain}::into\_pb::closure::call\_once\` in \`chain.rs\`**

Status: merged. Opened: 2026-09-29. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::chain::{spqr::chain::Chain}::into\_pb::closure::call\_once\` in \`chain.rs\` closes #521

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/572#pullrequestreview-5362705472) — Zhang-Liao (2026-09-30): (No text.)

### Item 573

**[Issue #573](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/573) — PROP-21: each party outputs at most one key per epoch**

Status: closed. Opened: 2026-09-30. Author: astefano.

Body excerpt: Prove that along any run of successful \`States::send\` / \`States::recv\` calls by one party, from any state, the emitted keys carry pairwise distinct epochs (ML-KEM Braid Rev. 1 §1.1, p. 4: "Each party outputs at most one key per epoch"; SCKA Fig. 1, \`Send-P\` line 14 and \`Receive-P\` line 7; \`src/v1/chunked/states.rs:203-220\`, \`:361-368\`). Part of #44.

No recorded comments or reviews.

### Item 574

**[PR #574](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/574) — Prove that each party outputs at most one key per epoch**

Status: merged. Opened: 2026-09-30. Author: astefano.

Body excerpt: This PR proves that each party outputs at most one key per epoch (ML-KEM Braid Rev. 1 §1.1, p. 4; SCKA Fig. 1, \`Send-P\` line 14 and \`Receive-P\` line 7). \`Run s s' ks\` is any finite sequence of successful \`States::send\` / \`States::recv\` calls by one party, from any state, with any RNG and any message, and \`ks\` is the list of keys it emits. \`epochs\_nodup\` says those keys carry pairwise distinct epochs. \`#print axioms …

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/574#issuecomment-5904619380) — github-actions[bot] (2026-09-30): ### Sorry Delta — hand-written specs \*\*46 new sorry-tainted declarations in \`Spqr.Specs.\*\`:\*\* | Module | Declaration | Kind | |--------|-------------|------| | \`Spqr.Specs.V1.Chunked.States.EpochUniqueness.CalleeEpoch\` | \`spqr.v1.chunked.send\_ct.Ct1Sampled.send\_ct1\_chunk.eq\_1\` | transitive | | \`Spqr.Specs.V1.Chunked.States.EpochUniqueness.CalleeEpoch\` | \`spqr.v1.chunked.send\_ct.Ct2Sampled.send\_ct2\_chunk.eq\_1\` | …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/574#issuecomment-5905599129) — truonghoangle (2026-09-30): The results of this PR are quite interesting. However, their current arrangement disrupts the structure of the Rust functions corresponding to the theorem specifications. Since these results are derived from the theorem specifications, I would suggest placing them outside the Spec module. What would be the appropriate approach here? In short, what is the standard way to organize these kinds of components within the …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/574#issuecomment-5907070429) — astefano (2026-09-30): &gt; The results of this PR are quite interesting. However, their current arrangement disrupts the structure of the Rust functions corresponding to the theorem specifications. &gt; &gt; Since these results are derived from the theorem specifications, I would suggest placing them outside the Spec module. What would be the appropriate approach here? &gt; &gt; In short, what is the standard way to organize these kinds of components …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/574#issuecomment-5907157958) — astefano (2026-09-30): i'd also propose that you guys rename Specs as FunctionSpecs or Contracts? or something as Specs is too generic for what's in there. And it leaves little options for other classes of specs like the one proposed in this PR.
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/574#issuecomment-5907898265) — github-actions[bot] (2026-09-30): ### Sorry Delta — hand-written specs \*\*46 new sorry-tainted declarations in \`Spqr.Specs.\*\`:\*\* | Module | Declaration | Kind | |--------|-------------|------| | \`Spqr.Specs.Braid.Scka.EpochUniqueness.CalleeEpoch\` | \`spqr.v1.chunked.send\_ct.Ct1Sampled.send\_ct1\_chunk.eq\_1\` | transitive | | \`Spqr.Specs.Braid.Scka.EpochUniqueness.CalleeEpoch\` | \`spqr.v1.chunked.send\_ct.Ct2Sampled.send\_ct2\_chunk.eq\_1\` | transitive | | …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/574#issuecomment-5908166071) — astefano (2026-09-30): in fact, i would be for keeping specs as the umbrella of all sorts of specs and soften the docs where it appears smth like "Lean spec theorem files for individual Rust functions, organised to mirror the Rust module tree." I proposed smth in https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/576.
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/574#issuecomment-6016433846) — github-actions[bot] (2026-10-06): ### Sorry Delta — hand-written specs \*\*46 new sorry-tainted declarations in \`Spqr.Specs.\*\`:\*\* | Module | Declaration | Kind | |--------|-------------|------| | \`Spqr.Specs.Braid.Scka.EpochUniqueness.CalleeEpoch\` | \`spqr.v1.chunked.send\_ct.Ct1Sampled.send\_ct1\_chunk.eq\_1\` | transitive | | \`Spqr.Specs.Braid.Scka.EpochUniqueness.CalleeEpoch\` | \`spqr.v1.chunked.send\_ct.Ct2Sampled.send\_ct2\_chunk.eq\_1\` | transitive | | …
- [review DISMISSED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/574#pullrequestreview-5529576513) — truonghoangle (2026-10-15): (No text.)
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/574#issuecomment-6186845304) — truonghoangle (2026-10-15): !radar
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/574#issuecomment-6186855395) — baif-radar (2026-10-15): Benchmark results for 4089e070fd0dbd88940f38b10888db4fb96f3f95 against 5b474a9dc5bf32bcb4f8ed3b2f654a1a82d16ee8 are in. There are significant results. @truonghoangle \*\*Medium changes (6✅)\*\* - ✅ \`build/module/Spqr.Auxiliary.Aeneas.Scalar//instructions\`: \*\*-806.0M\*\* (\*\*-11.05%\*\*) - ✅ \`build/module/Spqr.Auxiliary.Aeneas.Slice//instructions\`: \*\*-744.1M\*\* (\*\*-11.40%\*\*) - ✅ …
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/574#pullrequestreview-5529708468) — truonghoangle (2026-10-15): (No text.)

### Item 575

**[Issue #575](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/575) — Document where specs that are not about one Rust function go**

Status: closed. Opened: 2026-09-30. Author: astefano.

Body excerpt: The README and the style guide describe \\\`Spqr/Specs/\\\` as one spec file per Rust function, at a path mirroring \\\`src/\\\`. #574 adds specs from the ML-KEM Braid specification that range over runs of the state machine rather than one function (\\\`epochs\_nodup\\\` and its support lemmas), which fit neither the mirror rule nor the \\\`\_spec\\\` / \\\`@\[step\]\\\` / \\\`⦃ ... ⦄\\\` conventions. The question was raised in …

No recorded comments or reviews.

### Item 576

**[PR #576](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/576) — Document Braid specs alongside function specs in Spqr/Specs**

Status: merged. Opened: 2026-09-30. Author: astefano.

Body excerpt: This PR widens what the README and \`doc/STYLE\_GUIDE.md\` say \`Spqr/Specs/\` holds. So far both described it as one spec file per Rust function, at a path mirroring \`src/\`. #574 adds specs from the ML-KEM Braid specification that are about runs of the \`States\` machine, not one function, and puts them in \`Spqr/Specs/Braid/\`. The style guide now names two kinds of specs. Function specs keep every existing rule, which is …

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/576#issuecomment-5926534934) — Zhang-Liao (2026-10-01): The docstring rule ("gives the Rust source lines it covers") doesn't say whether it applies to lemma files. In #574, \`EpochUniqueness.lean\` cites line ranges, but the lemma files (\`EpochUniqueness/KeyFloor.lean\`, \`CalleeEpoch.lean\`, …) only name the source files. Could you clarify whether line numbers are required only in the property file or in every file?
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/576#issuecomment-5926930697) — astefano (2026-10-01): &gt; The docstring rule ("gives the Rust source lines it covers") doesn't say whether it applies to lemma files. In #574, \`EpochUniqueness.lean\` cites line ranges, but the lemma files (\`EpochUniqueness/KeyFloor.lean\`, \`CalleeEpoch.lean\`, …) only name the source files. Could you clarify whether line numbers are required only in the property file or in every file? right Liao, thanks. done in …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/576#issuecomment-5987542717) — Zhang-Liao (2026-10-05): I have two final comments. This PR can be merged once you have fixed them 1. Please specify the ML-KEM Braid revision (Rev. 1) and link to it so the section references remain unambiguous. 2. Please require module docstrings to state whether the property covers one or both parties, arbitrary or initialized states, and only successful calls. Assuming calls succeed does not prove that they will succeed.
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/576#issuecomment-5988521493) — astefano (2026-10-05): &gt; I have two final comments. This PR can be merged once you have fixed them &gt; &gt; 1. Please specify the ML-KEM Braid revision (Rev. 1) and link to it so the section references remain unambiguous. &gt; &gt; 2. Please require module docstrings to state whether the property covers one or both parties, arbitrary or initialized states, and only successful calls. Assuming calls succeed does not prove that they will succeed. …
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/576#pullrequestreview-5411500521) — Zhang-Liao (2026-10-05): (No text.)

### Item 577

**[Issue #577](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/577) — refactoring \`into\_pb/from\_pb pairs\` in \`chain.rs\`**

Status: closed. Opened: 2026-09-30. Author: truonghoangle.

Body excerpt: Rewrite there may be a way to make the specification and verification of into\_pb/from\_pb pairs in chain.rs pairs even more scalable and elegant than the predicate-based templates according to the patterns discussed in #568

No recorded comments or reviews.

### Item 578

**[PR #578](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/578) — Add functional models for Chain ↔ protobuf conversion with round-trip proofs. Completed \`Chain.rs\`**

Status: merged. Opened: 2026-09-30. Author: truonghoangle.

Body excerpt: This PR changed set introduces \*\*functional models\*\* (pure, total Lean functions) for the \`Chain\` and \`ChainEpochDirection\` protobuf serialization/deserialization (\`into\_pb\` / \`from\_pb\`) and refactors existing spec theorems to use those models instead of inline field-by-field postconditions (the specification and verification of the (\`into\_pb\` / \`from\_pb\`)pairs even more scalable and elegant than the predicate-based …

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/578#issuecomment-5913320124) — github-actions[bot] (2026-09-30): ### Sorry Delta — hand-written specs \*\*4 new sorry-tainted declarations in \`Spqr.Specs.\*\`:\*\* | Module | Declaration | Kind | |--------|-------------|------| | \`Spqr.Specs.Chain.Chain.FromPb\` | \`spqr.chain.Chain.from\_pb\_spec\` | direct | | \`Spqr.Specs.Chain.Chain.FromPb\` | \`spqr.chain.Chain.from\_pb\_spec.mvcgen\_spec\` | transitive | | \`Spqr.Specs.Chain.Chain.IntoPb\` | \`spqr.chain.Chain.into\_pb\_spec\` | direct | | …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/578#issuecomment-5929353428) — MarkusFerdinandDablander (2026-10-01): @truonghoangle thanks for your great work, I will provide a review on this soon!
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/578#pullrequestreview-5379570568) — MarkusFerdinandDablander (2026-10-01): Partial review so far, covering the following files: - \`scripts/nolints.json\` - \`Spqr/Specs/Chain/ChainEpochDirection/FunctionalModels.lean\` - \`Spqr/Specs/Chain/ChainEpochDirection/IntoPb.lean\` - \`Spqr/Specs/Chain/ChainEpochDirection/FromPb.lean\` - \`Spqr/Specs/Chain/Chain/ChainEpoch/CallMut.lean\` - \`Spqr/Specs/Chain/Chain/ChainEpoch/CallOnce.lean\` - \`Spqr/Specs/Chain/Chain/Epoch/CallMut.lean\` --- ### …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/578#issuecomment-5935561276) — truonghoangle (2026-10-01): @MarkusFerdinandDablander Thank you for your comments! - I have chosen Option (2): \*\*drop the monadic round-trip theorems\*\*. \*\*Rationale:\*\* The monadic round-trip theorems are straightforward corollaries of the pure round-trip theorems, which have already been established in \`FunctionalModels.lean\`, together with the specification theorems. Adding a separate \`MonadicRoundTrips.lean\` file for each module would …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/578#issuecomment-5948869752) — MarkusFerdinandDablander (2026-10-02): Brilliant; this all looks fantastic! Thanks for the great work! I will soon post feedback on the last three remaining files \`Chain/FunctionalModels.lean\`, \`Chain/Chain/IntoPb.lean\` and \`Chain/Chain/FromPb.lean\` which I am currently reviewing.
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/578#issuecomment-5993871487) — MarkusFerdinandDablander (2026-10-05): Hi @truonghoangle , I hope you had a great weekend! As promised, here is the rest of my feedback for your great work on the three remaining files: ### \`Chain/FunctionalModels.lean\` Great work! Here are some comments: - \*\*Suggestion: move the file next to the \`Chain\` spec files.\*\* Would it be possible to move this file to \`Spqr/Specs/Chain/Chain/FunctionalModels.lean\`, next to the \`Chain\` spec files, matching the …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/578#issuecomment-5997298488) — truonghoangle (2026-10-05): @MarkusFerdinandDablander Thank your for your comments. I fixed everything basis on your comments. Here's a summary of all changes made: ## Summary ### 1. \_\_Moved \`FunctionalModels.lean\`\_\_ - From: \`Spqr/Specs/Chain/FunctionalModels.lean\` - To: \`Spqr/Specs/Chain/Chain/FunctionalModels.lean\` - Deleted the old file ### 2. \_\_Updated imports\_\_ (6 files) Changed \`import Spqr.Specs.Chain.FunctionalModels\` → \`import …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/578#issuecomment-6013409665) — MarkusFerdinandDablander (2026-10-06): Hi @truonghoangle Thank you for your swift response; this all looks fantastic now! It seems the CI lint step failed due to nine \`docBlame\` errors because the definitions in the new \`Spqr/Specs/Chain/Chain/FunctionalModels.lean\` (\`epochIntoPb\`, \`epochFromPb\`, \`traverseResult\`, \`traverseVec\`, \`dequeContents\`, \`directionToI32\`, \`directionFromI32\`, \`intoPb\`, \`fromPb\`) do not have the required \`/-- ... -/\` docstring …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/578#issuecomment-6013958373) — truonghoangle (2026-10-06): @MarkusFerdinandDablander Thank you for your comments. I fixed it.
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/578#pullrequestreview-5427160069) — MarkusFerdinandDablander (2026-10-06): Brilliant; ready to merge!

### Item 579

**[Issue #579](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/579) — Harmonise \`spqr::authenticator::serialize::Authenticator::{into\_pb, from\_pb}\` via functional models and prove round trips in \`authenticator/serialize.rs\`**

Status: closed. Opened: 2026-09-30. Author: MarkusFerdinandDablander.

Body excerpt: See #568

No recorded comments or reviews.

### Item 580

**[Issue #580](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/580) — Harmonise \`spqr::v1::unchunked::send\_ek::serialize::KeysUnsampled::{into\_pb, from\_pb}\` via functional models and prove round trips in \`v1/unchunked/send\_ek/serialize.rs\`**

Status: closed. Opened: 2026-09-30. Author: MarkusFerdinandDablander.

Body excerpt: See #568

No recorded comments or reviews.

### Item 581

**[Issue #581](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/581) — Harmonise \`spqr::v1::chunked::send\_ek::serialize::KeysUnsampled::{into\_pb, from\_pb}\` via functional models and prove round trips in \`v1/chunked/send\_ek/serialize.rs\`**

Status: closed. Opened: 2026-09-30. Author: MarkusFerdinandDablander.

Body excerpt: See #568

No recorded comments or reviews.

### Item 582

**[Issue #582](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/582) — Harmonise \`spqr::v1::unchunked::send\_ek::serialize::HeaderSent::{into\_pb, from\_pb}\` via functional models and prove round trips in \`v1/unchunked/send\_ek/serialize.rs\`**

Status: closed. Opened: 2026-09-30. Author: MarkusFerdinandDablander.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 583

**[Issue #583](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/583) — Harmonise \`spqr::v1::unchunked::send\_ek::serialize::EkSent::{into\_pb, from\_pb}\` via functional models and prove round trips in \`v1/unchunked/send\_ek/serialize.rs\`**

Status: closed. Opened: 2026-09-30. Author: MarkusFerdinandDablander.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 584

**[Issue #584](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/584) — Harmonise \`spqr::v1::unchunked::send\_ek::serialize::EkSentCt1Received::{into\_pb, from\_pb}\` via functional models and prove round trips in \`v1/unchunked/send\_ek/serialize.rs\`**

Status: closed. Opened: 2026-09-30. Author: MarkusFerdinandDablander.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 585

**[Issue #585](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/585) — Harmonise \`spqr::v1::unchunked::send\_ct::serialize::NoHeaderReceived::{into\_pb, from\_pb}\` via functional models and prove round trips in \`v1/unchunked/send\_ct/serialize.rs\`**

Status: closed. Opened: 2026-09-30. Author: MarkusFerdinandDablander.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 586

**[Issue #586](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/586) — Harmonise \`spqr::v1::unchunked::send\_ct::serialize::HeaderReceived::{into\_pb, from\_pb}\` via functional models and prove round trips in \`v1/unchunked/send\_ct/serialize.rs\`**

Status: closed. Opened: 2026-09-30. Author: MarkusFerdinandDablander.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 587

**[Issue #587](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/587) — Harmonise \`spqr::v1::unchunked::send\_ct::serialize::Ct1Sent::{into\_pb, from\_pb}\` via functional models and prove round trips in \`v1/unchunked/send\_ct/serialize.rs\`**

Status: open. Opened: 2026-09-30. Author: MarkusFerdinandDablander.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 588

**[Issue #588](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/588) — Harmonise \`spqr::v1::unchunked::send\_ct::serialize::Ct1SentEkReceived::{into\_pb, from\_pb}\` via functional models and prove round trips in \`v1/unchunked/send\_ct/serialize.rs\`**

Status: closed. Opened: 2026-09-30. Author: MarkusFerdinandDablander.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 589

**[Issue #589](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/589) — Harmonise \`spqr::v1::unchunked::send\_ct::serialize::Ct2Sent::{into\_pb, from\_pb}\` via functional models and prove round trips in \`v1/unchunked/send\_ct/serialize.rs\`**

Status: closed. Opened: 2026-09-30. Author: MarkusFerdinandDablander.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 590

**[Issue #590](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/590) — Harmonise \`spqr::encoding::polynomial::PolyEncoder::{into\_pb, from\_pb}\` via functional models and prove round trips in \`encoding/polynomial.rs\`**

Status: open. Opened: 2026-09-30. Author: MarkusFerdinandDablander.

Body excerpt: (No text.)

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/590#issuecomment-5912379587) — MarkusFerdinandDablander (2026-09-30): Potential overlap / interaction with @truonghoangle's #567

### Item 591

**[Issue #591](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/591) — Harmonise \`spqr::encoding::polynomial::PolyDecoder::{into\_pb, from\_pb}\` via functional models and prove round trips in \`encoding/polynomial.rs\`**

Status: open. Opened: 2026-09-30. Author: MarkusFerdinandDablander.

Body excerpt: (No text.)

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/591#issuecomment-5912381638) — MarkusFerdinandDablander (2026-09-30): Potential overlap / interaction with @truonghoangle's #567

### Item 592

**[Issue #592](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/592) — Harmonise \`spqr::v1::chunked::send\_ek::serialize::KeysSampled::{into\_pb, from\_pb}\` via functional models and prove round trips in \`v1/chunked/send\_ek/serialize.rs\`**

Status: open. Opened: 2026-09-30. Author: MarkusFerdinandDablander.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 593

**[Issue #593](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/593) — Verify : \`v1/chunked/send\_ct/serialize.rs\`**

Status: open. Opened: 2026-09-30. Author: MarkusFerdinandDablander.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 594

**[Issue #594](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/594) — Specify and verify : \`spqr::v1::chunked::send\_ct::serialize::{spqr::v1::chunked::send\_ct::NoHeaderReceived}::into\_pb\` in \`v1/chunked/send\_ct/serialize.rs\`**

Status: open. Opened: 2026-09-30. Author: MarkusFerdinandDablander.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 595

**[Issue #595](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/595) — Specify and verify : \`spqr::v1::chunked::send\_ct::serialize::{spqr::v1::chunked::send\_ct::NoHeaderReceived}::from\_pb\` in \`v1/chunked/send\_ct/serialize.rs\`**

Status: open. Opened: 2026-09-30. Author: MarkusFerdinandDablander.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 596

**[Issue #596](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/596) — Specify and verify : \`spqr::v1::chunked::send\_ct::serialize::{spqr::v1::chunked::send\_ct::HeaderReceived}::into\_pb\` in \`v1/chunked/send\_ct/serialize.rs\`**

Status: open. Opened: 2026-09-30. Author: MarkusFerdinandDablander.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 597

**[Issue #597](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/597) — Specify and verify : \`spqr::v1::chunked::send\_ct::serialize::{spqr::v1::chunked::send\_ct::HeaderReceived}::from\_pb\` in \`v1/chunked/send\_ct/serialize.rs\`**

Status: open. Opened: 2026-09-30. Author: MarkusFerdinandDablander.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 598

**[Issue #598](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/598) — Specify and verify : \`spqr::v1::chunked::send\_ct::serialize::{spqr::v1::chunked::send\_ct::Ct1Sampled}::into\_pb\` in \`v1/chunked/send\_ct/serialize.rs\`**

Status: open. Opened: 2026-09-30. Author: MarkusFerdinandDablander.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 599

**[Issue #599](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/599) — Specify and verify : \`spqr::v1::chunked::send\_ct::serialize::{spqr::v1::chunked::send\_ct::Ct1Sampled}::from\_pb\` in \`v1/chunked/send\_ct/serialize.rs\`**

Status: open. Opened: 2026-09-30. Author: MarkusFerdinandDablander.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 600

**[Issue #600](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/600) — Specify and verify : \`spqr::v1::chunked::send\_ct::serialize::{spqr::v1::chunked::send\_ct::EkReceivedCt1Sampled}::into\_pb\` in \`v1/chunked/send\_ct/serialize.rs\`**

Status: open. Opened: 2026-09-30. Author: MarkusFerdinandDablander.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 601

**[Issue #601](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/601) — Specify and verify : \`spqr::v1::chunked::send\_ct::serialize::{spqr::v1::chunked::send\_ct::EkReceivedCt1Sampled}::from\_pb\` in \`v1/chunked/send\_ct/serialize.rs\`**

Status: open. Opened: 2026-09-30. Author: MarkusFerdinandDablander.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 602

**[Issue #602](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/602) — Specify and verify : \`spqr::v1::chunked::send\_ct::serialize::{spqr::v1::chunked::send\_ct::Ct1Acknowledged}::into\_pb\` in \`v1/chunked/send\_ct/serialize.rs\`**

Status: open. Opened: 2026-09-30. Author: MarkusFerdinandDablander.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 603

**[Issue #603](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/603) — Specify and verify : \`spqr::v1::chunked::send\_ct::serialize::{spqr::v1::chunked::send\_ct::Ct1Acknowledged}::from\_pb\` in \`v1/chunked/send\_ct/serialize.rs\`**

Status: open. Opened: 2026-09-30. Author: MarkusFerdinandDablander.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 604

**[Issue #604](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/604) — Specify and verify : \`spqr::v1::chunked::send\_ct::serialize::{spqr::v1::chunked::send\_ct::Ct2Sampled}::into\_pb\` in \`v1/chunked/send\_ct/serialize.rs\`**

Status: open. Opened: 2026-09-30. Author: MarkusFerdinandDablander.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 605

**[Issue #605](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/605) — Specify and verify : \`spqr::v1::chunked::send\_ct::serialize::{spqr::v1::chunked::send\_ct::Ct2Sampled}::from\_pb\` in \`v1/chunked/send\_ct/serialize.rs\`**

Status: open. Opened: 2026-09-30. Author: MarkusFerdinandDablander.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 606

**[Issue #606](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/606) — Stylistically streamline \`FunctionalModels.lean\` files for \`spqr::authenticator::serialize::Authenticator::{into\_pb, from\_pb}\` and \`spqr::v1::unchunked::send\_ek::serialize::KeysUnsampled::{into\_pb, from\_pb}\`**

Status: closed. Opened: 2026-09-30. Author: MarkusFerdinandDablander.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 607

**[Issue #607](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/607) — Harmonise \`spqr::v1::chunked::send\_ek::serialize::HeaderSent::{into\_pb, from\_pb}\` via functional models and prove round trips in \`v1/chunked/send\_ek/serialize.rs\`**

Status: open. Opened: 2026-09-30. Author: MarkusFerdinandDablander.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 608

**[Issue #608](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/608) — Harmonise \`spqr::v1::chunked::send\_ek::serialize::Ct1Received::{into\_pb, from\_pb}\` via functional models and prove round trips in \`v1/chunked/send\_ek/serialize.rs\`**

Status: open. Opened: 2026-09-30. Author: MarkusFerdinandDablander.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 609

**[Issue #609](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/609) — Harmonise \`spqr::v1::chunked::send\_ek::serialize::EkSentCt1Received::{into\_pb, from\_pb}\` via functional models and prove round trips in \`v1/chunked/send\_ek/serialize.rs\`**

Status: open. Opened: 2026-09-30. Author: MarkusFerdinandDablander.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 610

**[Issue #610](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/610) — Harmonise \`spqr::v1::chunked::send\_ct::serialize::NoHeaderReceived::{into\_pb, from\_pb}\` via functional models and prove round trips in \`v1/chunked/send\_ct/serialize.rs\`**

Status: open. Opened: 2026-09-30. Author: MarkusFerdinandDablander.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 611

**[Issue #611](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/611) — Harmonise \`spqr::v1::chunked::send\_ct::serialize::HeaderReceived::{into\_pb, from\_pb}\` via functional models and prove round trips in \`v1/chunked/send\_ct/serialize.rs\`**

Status: open. Opened: 2026-09-30. Author: MarkusFerdinandDablander.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 612

**[Issue #612](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/612) — Harmonise \`spqr::v1::chunked::send\_ct::serialize::Ct1Sampled::{into\_pb, from\_pb}\` via functional models and prove round trips in \`v1/chunked/send\_ct/serialize.rs\`**

Status: open. Opened: 2026-09-30. Author: MarkusFerdinandDablander.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 613

**[Issue #613](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/613) — Harmonise \`spqr::v1::chunked::send\_ct::serialize::EkReceivedCt1Sampled::{into\_pb, from\_pb}\` via functional models and prove round trips in \`v1/chunked/send\_ct/serialize.rs\`**

Status: open. Opened: 2026-09-30. Author: MarkusFerdinandDablander.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 614

**[Issue #614](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/614) — Harmonise \`spqr::v1::chunked::send\_ct::serialize::Ct1Acknowledged::{into\_pb, from\_pb}\` via functional models and prove round trips in \`v1/chunked/send\_ct/serialize.rs\`**

Status: open. Opened: 2026-09-30. Author: MarkusFerdinandDablander.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 615

**[Issue #615](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/615) — Harmonise \`spqr::v1::chunked::send\_ct::serialize::Ct2Sampled::{into\_pb, from\_pb}\` via functional models and prove round trips in \`v1/chunked/send\_ct/serialize.rs\`**

Status: open. Opened: 2026-09-30. Author: MarkusFerdinandDablander.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 616

**[Issue #616](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/616) — Harmonise \`spqr::v1::chunked::states::serialize::States::{into\_pb, from\_pb}\` via functional models and prove round trips in \`v1/chunked/states/serialize.rs\`**

Status: open. Opened: 2026-09-30. Author: MarkusFerdinandDablander.

Body excerpt: (No text.)

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/616#issuecomment-5912110480) — MarkusFerdinandDablander (2026-09-30): \*\*Note:\*\* Potential overlap with two issues claimed by @Zhang-Liao (#317 and #318)

### Item 617

**[PR #617](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/617) — Harmonise \`spqr::v1::chunked::send\_ek::serialize::KeysUnsampled::{into\_pb, from\_pb}\` via functional models and prove round trips in \`v1/chunked/send\_ek/serialize.rs\`**

Status: merged. Opened: 2026-09-30. Author: MarkusFerdinandDablander.

Body excerpt: This PR harmonises the chunked \`KeysUnsampled\` serializer pair following the architecture discussed in #568. - Adds \`KeysUnsampled/FunctionalModels.lean\` with pure models \`intoPb\` and \`fromPb\` - Adds the two associated round-trip theorems. - Repins \`into\_pb\_spec\` and \`from\_pb\_spec\` to \`result = FunctionalModels.{intoPb, fromPb} …\` ### Why the new functional-model architecture already seems to pay off here Note that …

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/617#issuecomment-5913147596) — truonghoangle (2026-09-30): Great job!
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/617#pullrequestreview-5367479536) — truonghoangle (2026-09-30): (No text.)

### Item 618

**[Issue #618](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/618) — \`VecDeque::into\_iter\` model wrong when \`head ≠ 0\` in Lean model at \`FunsExternal.lean\` L3733–3759**

Status: closed. Opened: 2026-10-04. Author: truonghoangle.

Body excerpt: \`VecDeque::into\_iter\` model wrong when \`head ≠ 0\` No proved theorem currently falsified, but blocks future \`Chain::into\_pb\` proofs. \*\*Location.\*\* \`SrcTranslated/FunsExternal.lean\` L3733–3759. \*\*Defect.\*\* The model uses ring-buffer \`wrapping\_add\` modulo \`length\` (inconsistent with the project's growing-list model for \`pop\_front\`/\`push\_back\`/\`index\`) and never decrements \`length\` (never terminates). \*\*Consequence.\*\* …

No recorded comments or reviews.

### Item 619

**[PR #619](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/619) — Fix \`VecDeque::into\_iter\` model wrong when \`head ≠ 0\` in Lean model at \`FunsExternal.lean L3733–3759\`**

Status: merged. Opened: 2026-10-04. Author: truonghoangle.

Body excerpt: This PR fixes \`VecDeque::into\_iter\` model wrong when \`head ≠ 0\`. ## Problem The \`into\_iter.IntoIter.next\` model in \`FunsExternal.lean\` (L3733–3759) used ring-buffer semantics (\`wrapping\_add\` modulo \`length\`) and \*\*never decremented \`length\`\*\*, making the iterator non-terminating and inconsistent with the growing-list model used by \`pop\_front\`, \`push\_back\`, and \`index\` throughout the codebase. After one \`pop\_front\` …

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/619#pullrequestreview-5409100823) — Zhang-Liao (2026-10-05): (No text.)

### Item 620

**[Issue #620](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/620) — Specify and verify \`:msg\_version\` in \`lib.rs\`**

Status: closed. Opened: 2026-10-05. Author: truonghoangle.

Body excerpt: /-- \[spqr::msg\_version\]: Source: 'src/lib.rs', lines 464:0-470:1 -/

No recorded comments or reviews.

### Item 621

**[Issue #621](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/621) — Specify and verify : \`state\_version\` in \`lib.rs\`**

Status: closed. Opened: 2026-10-05. Author: truonghoangle.

Body excerpt: /-- \[spqr::state\_version\]: Source: 'src/lib.rs', lines 457:0-462:1 -/

No recorded comments or reviews.

### Item 622

**[Issue #622](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/622) — Specify and verify \`spqr::recv::{impl core::ops::function::FnOnce for spqr::recv::closure}::call\_once\` in \`lib.rs\`**

Status: open. Opened: 2026-10-05. Author: truonghoangle.

Body excerpt: /-- \[spqr::recv::{impl core::ops::function::FnOnce for spqr::recv::closure}::call\_once\]: Source: 'src/lib.rs', lines 395:64-395:86 -/

No recorded comments or reviews.

### Item 623

**[Issue #623](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/623) — Specify and verify \`recv\` in \`lib.rs\`**

Status: open. Opened: 2026-10-05. Author: truonghoangle.

Body excerpt: /-- \[spqr::recv\]: Source: 'src/lib.rs', lines 356:0-455:1 Visibility: public -/

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/623#issuecomment-6336956781) — MarkusFerdinandDablander (2026-10-22): As discussed in today's meeting, perhaps @truonghoangle and / or @Zhang-Liao can try to specify this function while I am working on #434 :-)
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/623#issuecomment-6337114355) — truonghoangle (2026-10-22): @MarkusFerdinandDablander I am working on it!

### Item 624

**[PR #624](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/624) — Specify and verify for \`spqr::msg\_version\` in \`lib.rs\`**

Status: merged. Opened: 2026-10-05. Author: truonghoangle.

Body excerpt: This PR specifies and verifies for \`spqr::msg\_version\` in \`lib.rs\` closes #620

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/624#issuecomment-6051048086) — Zhang-Liao (2026-10-08): - The file is in the wrong place. All the other lib.rs specs live under \`Spqr/Specs/Lib/\`, so this one should be \`Spqr/Specs/Lib/MsgVersion.lean\` too (there was no \`Spqr/Lib/\` directory before this PR). - Why do you use two \`@\[step\]\` theorems? Right now \`msg\_version\_spec\` needs \`msg\` non-empty and \`msg\_version\_spec\_empty\` needs it empty, so whoever calls step has to prove the side condition first. A single theorem …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/624#issuecomment-6054821247) — truonghoangle (2026-10-08): @Zhang-Liao Thank you for your comments. I fixed it and rewrote it such that more high-level, human-readable form
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/624#pullrequestreview-5453290535) — Zhang-Liao (2026-10-08): (No text.)

### Item 625

**[Issue #625](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/625) — Verify : \`src/v1/unchunked/send\_ct.rs\`**

Status: closed. Opened: 2026-10-05. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 626

**[Issue #626](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/626) — Specify and verify : \`spqr::v1::unchunked::send\_ct::{spqr::v1::unchunked::send\_ct::NoHeaderReceived}::new\` in \`'src/v1/unchunked/send\_ct.rs'\`**

Status: closed. Opened: 2026-10-05. Author: truonghoangle.

Body excerpt: /-- \[spqr::v1::unchunked::send\_ct::{spqr::v1::unchunked::send\_ct::NoHeaderReceived}::new\]: Source: 'src/v1/unchunked/send\_ct.rs', lines 92:4-97:5 Visibility: public -/

No recorded comments or reviews.

### Item 627

**[Issue #627](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/627) — Specify and verify \`spqr::v1::unchunked::send\_ct::{spqr::v1::unchunked::send\_ct::HeaderReceived}::send\_ct1\` in 'src/v1/unchunked/send\_ct.rs'**

Status: closed. Opened: 2026-10-05. Author: truonghoangle.

Body excerpt: /-- \[spqr::v1::unchunked::send\_ct::{spqr::v1::unchunked::send\_ct::HeaderReceived}::send\_ct1\]: Source: 'src/v1/unchunked/send\_ct.rs', lines 120:4-148:5 Visibility: public -/

No recorded comments or reviews.

### Item 628

**[Issue #628](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/628) — specify and verify : \`spqr::v1::unchunked::send\_ct::{spqr::v1::unchunked::send\_ct::Ct2Sent}::recv\_next\_epoch\` in 'src/v1/unchunked/send\_ct.rs'**

Status: closed. Opened: 2026-10-05. Author: truonghoangle.

Body excerpt: /-- \[spqr::v1::unchunked::send\_ct::{spqr::v1::unchunked::send\_ct::Ct2Sent}::recv\_next\_epoch\]: Source: 'src/v1/unchunked/send\_ct.rs', lines 201:4-208:5 Visibility: public -/

No recorded comments or reviews.

### Item 629

**[Issue #629](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/629) — Specify and verify \`spqr::v1::unchunked::send\_ct::{spqr::v1::unchunked::send\_ct::Ct1SentEkReceived}::send\_ct2\` in 'src/v1/unchunked/send\_ct.rs'**

Status: closed. Opened: 2026-10-05. Author: truonghoangle.

Body excerpt: /-- \[spqr::v1::unchunked::send\_ct::{spqr::v1::unchunked::send\_ct::Ct1SentEkReceived}::send\_ct2\]: Source: 'src/v1/unchunked/send\_ct.rs', lines 177:4-195:5 Visibility: public -/

No recorded comments or reviews.

### Item 630

**[Issue #630](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/630) — Specify and verify : \`spqr::v1::unchunked::send\_ct::{spqr::v1::unchunked::send\_ct::Ct1Sent}::recv\_ek\` in 'src/v1/unchunked/send\_ct.rs'**

Status: closed. Opened: 2026-10-05. Author: truonghoangle.

Body excerpt: /-- \[spqr::v1::unchunked::send\_ct::{spqr::v1::unchunked::send\_ct::Ct1Sent}::recv\_ek\]: Source: 'src/v1/unchunked/send\_ct.rs', lines 154:4-171:5 Visibility: public -/

No recorded comments or reviews.

### Item 631

**[Issue #631](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/631) — Specify and verify \`spqr::v1::unchunked::send\_ct::{spqr::v1::unchunked::send\_ct::NoHeaderReceived}::recv\_header\` in 'src/v1/unchunked/send\_ct.rs'**

Status: closed. Opened: 2026-10-05. Author: truonghoangle.

Body excerpt: /-- \[spqr::v1::unchunked::send\_ct::{spqr::v1::unchunked::send\_ct::NoHeaderReceived}::recv\_header\]: Source: 'src/v1/unchunked/send\_ct.rs', lines 100:4-113:5 Visibility: public -/

No recorded comments or reviews.

### Item 632

**[Issue #632](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/632) — Migrate this repo to the module system**

Status: closed. Opened: 2026-10-05. Author: oliver-butterley.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 633

**[Issue #633](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/633) — Verify \`spqr::chain::{spqr::chain::Chain}::from\_pb\` in \`chain.rs\`**

Status: closed. Opened: 2026-10-05. Author: truonghoangle.

Body excerpt: (No text.)

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/633#issuecomment-6185370793) — truonghoangle (2026-10-15): This issue has been resolved in PR #660 by @oliver-butterley.

### Item 634

**[Issue #634](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/634) — Verify \`spqr::chain::{spqr::chain::Chain}::into\_pb\` in \`chain.rs\`**

Status: closed. Opened: 2026-10-05. Author: truonghoangle.

Body excerpt: (No text.)

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/634#issuecomment-6185374697) — truonghoangle (2026-10-15): This issue has been resolved in PR #660 by @oliver-butterley.

### Item 635

**[PR #635](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/635) — Update to nightly-2026.10.07-aa66752**

Status: merged. Opened: 2026-10-05. Author: oliver-butterley.

Body excerpt: Updates Aeneas to latest version and fixes proofs throughout. \*\*Note\*\*: - the "2 new sorry-tainted declarations" aren't actually new but they are auto-generated names which changed so it seems they are new. - About ~3000 changed lines are the auto-generated files \*\*Spec statement changes\*\* (forced by the new \`Std\` types): - \`mac\_ct\_spec\`, \`mac\_hdr\_spec\`: \`self.mac\_key.deref\` - \`verify\_ct\_spec\`, \`verify\_hdr\_spec\`: …

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/635#issuecomment-6037150725) — github-actions[bot] (2026-10-07): ### Sorry Delta — hand-written specs \*\*2 new sorry-tainted declarations in \`Spqr.Specs.\*\`:\*\* | Module | Declaration | Kind | |--------|-------------|------| | \`Spqr.Specs.Encoding.Polynomial.Poly.FromCompletePoints\` | \`spqr.encoding.polynomial.Poly.from\_complete\_points\_loop.body\_spec.\_proof\_1\_4\` | transitive | | \`Spqr.Specs.Encoding.Polynomial.PolyEncoder.ChunkAt\` | …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/635#issuecomment-6060775507) — oliver-butterley (2026-10-08): !radar
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/635#issuecomment-6060788701) — baif-radar (2026-10-08): Benchmark results for 24ca1a3773902b9c70d25eb7b9ba49e46683c7b7 against e944f165396acb170f866b461fb6329cdebfb24f are in. There are significant results. @oliver-butterley \*\*Large changes (9✅, 16🟥)\*\* Too many entries to display here. View the full report on radar instead. \*\*Medium changes (3✅, 7🟥)\*\* - 🟥 \`build/module/Spqr.Specs.Chain.Chain.CedForDirection//instructions\`: \*\*+1.2G\*\* (\*\*+14.48%\*\*) - ✅ …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/635#issuecomment-6061642335) — oliver-butterley (2026-10-08): !radar
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/635#issuecomment-6061649943) — baif-radar (2026-10-08): Benchmark results for cd4e766bc4e7cfc83af3069a4783e10d855c5028 against e944f165396acb170f866b461fb6329cdebfb24f are in. There are significant results. @oliver-butterley \*\*Large changes (9✅, 12🟥)\*\* Too many entries to display here. View the full report on radar instead. \*\*Medium changes (5✅, 6🟥)\*\* - ✅ \`build/module/Spqr.Specs.Authenticator.Authenticator.VerifyCt//instructions\`: \*\*-1.4G\*\* (\*\*-11.32%\*\*) - ✅ …
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/635#pullrequestreview-5458714240) — truonghoangle (2026-10-08): That's impressive!
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/635#issuecomment-6064038252) — oliver-butterley (2026-10-08): I see that overall the build is now quicker. However there are some files which are slower. I'll do a little more investigating to see if I can improve those files. However for efficiency let's merge this now and I'll do the improvements if possible in another PR. And then in another PR I will extend the coverage of translation to included everything which is still missing.

### Item 636

**[PR #636](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/636) — Added Reviewer's Guide**

Status: merged. Opened: 2026-10-06. Author: Kukovec.

Body excerpt: First version of the reviewer's guide, as discussed at our latest standup. closes #475

Discussion and review record:

- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/636#discussion_r4201774831) — truonghoangle (2026-10-07; doc/REVIEWER_GUIDE.md:21): change \`Asses\` to \`Assess\`
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/636#pullrequestreview-5436078138) — truonghoangle (2026-10-07): (No text.)
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/636#pullrequestreview-5516314100) — oliver-butterley (2026-10-14): Looks good to me!
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/636#pullrequestreview-5533269282) — truonghoangle (2026-10-15): (No text.)

### Item 637

**[PR #637](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/637) — Add \`chain\_from\` spec and refactor \`chainFromVersionNegotiation\` to use functional models**

Status: merged. Opened: 2026-10-06. Author: truonghoangle.

Body excerpt: This PR specifies and verify for \`chain\_from\` and refactors the existing \`chainFromVersionNegotiation\` spec to use \*\*functional models\*\* instead of verbose inline postconditions, making the specs more high-level, human-readable form and the proofs simpler. ### 1. \*\*\`Spqr/Specs/Lib/ChainFrom.lean\`\*\* A brand-new spec theorem for the \`spqr::chain\_from\` Rust function. This function reconstructs a \`Chain\` from an …

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/637#issuecomment-6016985843) — github-actions[bot] (2026-10-06): ### Sorry Delta — hand-written specs \*\*2 new sorry-tainted declarations in \`Spqr.Specs.\*\`:\*\* | Module | Declaration | Kind | |--------|-------------|------| | \`Spqr.Specs.Lib.ChainFrom\` | \`spqr.chain\_from\_spec\` | transitive | | \`Spqr.Specs.Lib.ChainFrom\` | \`spqr.chain\_from\_spec.mvcgen\_spec\` | transitive |
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/637#discussion_r4207110474) — Zhang-Liao (2026-10-07; Spqr/Specs/Lib/ChainFromVersionNegotiation.lean:26): This notation is defined but not used.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/637#pullrequestreview-5442563820) — Zhang-Liao (2026-10-07): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/637#discussion_r4207726349) — truonghoangle (2026-10-07; Spqr/Specs/Lib/ChainFromVersionNegotiation.lean:26): I fixed it
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/637#pullrequestreview-5443326196) — truonghoangle (2026-10-07): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/637#pullrequestreview-5450684622) — Zhang-Liao (2026-10-08): (No text.)
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/637#issuecomment-6053691764) — github-actions[bot] (2026-10-08): ### Sorry Delta — hand-written specs \*\*2 new sorry-tainted declarations in \`Spqr.Specs.\*\`:\*\* | Module | Declaration | Kind | |--------|-------------|------| | \`Spqr.Specs.Lib.ChainFrom\` | \`spqr.chain\_from\_spec\` | transitive | | \`Spqr.Specs.Lib.ChainFrom\` | \`spqr.chain\_from\_spec.mvcgen\_spec\` | transitive |

### Item 638

**[Issue #638](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/638) — Stale axioms**

Status: closed. Opened: 2026-10-07. Author: truonghoangle.

Body excerpt: in \`SrcTranslated/FunsExternal.lean\` (lines 3674–3711): \`encoding.gf.mul2\_u16\`, \`initial\_state\`, \`send\`, \`recv\`. These are now fully translated as \`defs\` in \`Funs.lean\`, but the old axioms remain with 0 users - they'll display on VeriLib as misleading unverified local axioms.

No recorded comments or reviews.

### Item 639

**[PR #639](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/639) — Stale axioms**

Status: merged. Opened: 2026-10-07. Author: truonghoangle.

Body excerpt: This PR removed \`encoding.gf.mul2\_u16\`, \`initial\_state\`, \`send\`, \`recv\` in \`SrcTranslated/FunsExternal.lean (lines 3674–3711)\`. These are now fully translated as \`defs\` in Funs.lean, but the old axioms remain with 0 users - they'll display on VeriLib as misleading unverified local axioms. closes #638

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/639#pullrequestreview-5450687012) — Zhang-Liao (2026-10-08): (No text.)

### Item 640

**[PR #640](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/640) — Stylistically streamline a few of the novel FunctionalModel and spec files**

Status: merged. Opened: 2026-10-07. Author: MarkusFerdinandDablander.

Body excerpt: This PR stylistically aligns the Authenticator and unchunked \`KeysUnsampled\` functional-model and spec files with the conventions of the chunked \`KeysUnsampled\` pilot. The changes are only stylistic, no definition, theorem statement, or proof was changed. Closes #606

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/640#pullrequestreview-5440248170) — truonghoangle (2026-10-07): (No text.)

### Item 641

**[PR #641](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/641) — Harmonise \`spqr::v1::unchunked::send\_ct::serialize::NoHeaderReceived::{into\_pb, from\_pb}\` via functional models and prove round trips in \`v1/unchunked/send\_ct/serialize.rs\`**

Status: merged. Opened: 2026-10-07. Author: MarkusFerdinandDablander.

Body excerpt: This PR adds \`FunctionalModels.lean\` for the unchunked \`NoHeaderReceived\` state, proves both model-level round trips, and pins the existing \`into\_pb\` and \`from\_pb\` spec theorems to those models. Closes #585

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/641#pullrequestreview-5443454201) — truonghoangle (2026-10-07): Great job!

### Item 642

**[PR #642](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/642) — Harmonise \`spqr::v1::unchunked::send\_ct::serialize::Ct2Sent::{into\_pb, from\_pb}\` via functional models and prove round trips in \`v1/unchunked/send\_ct/serialize.rs\`**

Status: merged. Opened: 2026-10-07. Author: MarkusFerdinandDablander.

Body excerpt: This PR adds \`FunctionalModels.lean\` for the unchunked \`Ct2Sent\` state, proves both model-level round trips, and pins the existing \`into\_pb\` and \`from\_pb\` spec theorems to those models, following the architecture discussed in #568. Closes #589

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/642#pullrequestreview-5443749249) — truonghoangle (2026-10-07): Great job!

### Item 643

**[PR #643](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/643) — Spec and proof of mlkem encaps1**

Status: open draft. Opened: 2026-10-07. Author: a-dangelo.

Body excerpt: This PR adds the spec theorem for \`spqr::incremental\_mlkem768::encaps1\` (\`src/incremental\_mlkem768.rs\`, lines 46–66) in \`Spqr/Specs/IncrementalMlkem768/Encaps1.lean\`, and registers it in \`Spqr.lean\`. \`encaps1\_spec\` shows that, given a 64-byte header and the component contracts below, \`encaps1\` succeeds and returns ciphertext, state and secret vectors of lengths 960, 2080 and 32. Their bytes equal the corresponding …

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/643#issuecomment-6043232064) — a-dangelo (2026-10-07): @truonghoangle not sure if this aligns with what you had in mind or not. I guess we need to decide what to do with rng functions. I tried to kind of take inspiration from the EasyCrypt works and other sources that are mentioned. This is not really meant as a real PR, but more to spark discussion on how we want to model these kind of interfaces at the boundary with external crates like libcrux

### Item 644

**[PR #644](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/644) — Specify and verify : \`state\_version\` in \`lib.rs\`**

Status: merged. Opened: 2026-10-08. Author: truonghoangle.

Body excerpt: This PR specifies and verifies : \`state\_version\` in \`lib.rs\` closes #621

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/644#issuecomment-6064356823) — truonghoangle (2026-10-08): !radar
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/644#issuecomment-6064361298) — baif-radar (2026-10-08): Benchmark results for 2fa8fd3a27841a640cf3b21741223ac6511a38d6 against b5a4cb90b41a1577134fa8398d1bc87fea32b899 are in. No significant results found. @truonghoangle No significant changes detected.
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/644#pullrequestreview-5467002917) — Zhang-Liao (2026-10-09): (No text.)

### Item 645

**[Issue #645](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/645) — Proposal: compositional specs for the \`= ok\` statements**

Status: open. Opened: 2026-10-08. Author: oliver-butterley.

Body excerpt: \*\*Context.\*\* Aeneas \`nightly-2026.10.07\` removed \`WP.spec\_imp\_exists\`/\`exists\_imp\_spec\`. We re-prove them in \`Spqr/Auxiliary/Aeneas/SpecImpExists.lean\` as a temporary shim. Various statements have a postcondition of the form \`= ok\`. This is a proposal for updating these statements. \*\*Principle.\*\* A spec should say what the result \*is\*, through a pure model, rather than "the result equals what this other computation …

No recorded comments or reviews.

### Item 646

**[PR #646](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/646) — Harmonise \`spqr::v1::unchunked::send\_ct::serialize::HeaderReceived::{into\_pb, from\_pb}\` via functional models and prove round trips**

Status: merged. Opened: 2026-10-08. Author: MarkusFerdinandDablander.

Body excerpt: This PR adds \`FunctionalModels.lean\` for the unchunked \`HeaderReceived\` state, proves round trips, and pins the existing \`into\_pb\` and \`from\_pb\` spec theorems to the functional models, following the architecture discussed in #568. \*\*Note:\*\* This is the first pair requiring a non-trivial\`WellFormed\` predicate, which here simply transcribes the struct's \`#\[hax\_lib::refine(hdr.len() == 64)\]\` requirement. The round …

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/646#issuecomment-6076246900) — truonghoangle (2026-10-09): @MarkusFerdinandDablander can you resolve conflicts?
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/646#issuecomment-6077508668) — MarkusFerdinandDablander (2026-10-09): @truonghoangle thanks, conflict resolved!
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/646#pullrequestreview-5470073108) — truonghoangle (2026-10-09): (No text.)

### Item 647

**[PR #647](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/647) — Performance improvements**

Status: merged. Opened: 2026-10-08. Author: oliver-butterley.

Body excerpt: Having noticed, during the work on updating Aeneas in #635, several potential performance improvements, this PR implements them. Note: none of the spec theorems were made weaker however 12 theorems were made stronger in the sense that there was a hypothesis in each that was redundant and could be dropped. These 12 theorems are: key\_spec, key\_spec\_equal, key\_spec\_less, key\_spec\_greater, key\_spec\_greater\_jump, …

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/647#issuecomment-6067905790) — oliver-butterley (2026-10-08): !radar
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/647#issuecomment-6067910957) — baif-radar (2026-10-08): Benchmark results for 354f6ed74bd52b456ec1d4ecc81288739a03048c against b5a4cb90b41a1577134fa8398d1bc87fea32b899 are in. There are significant results. @oliver-butterley \*\*Large changes (6✅)\*\* - ✅ \`build/module/Spqr.Specs.Authenticator.Authenticator.MacCt//instructions\`: \*\*-8.7G\*\* (\*\*-31.86%\*\*) - ✅ \`build/module/Spqr.Specs.Authenticator.Authenticator.MacHdr//instructions\`: \*\*-8.0G\*\* (\*\*-31.09%\*\*) - ✅ …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/647#issuecomment-6069560911) — oliver-butterley (2026-10-08): !radar
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/647#issuecomment-6069562969) — baif-radar (2026-10-08): Benchmark results for 64fa367709c8ee0e12aaf678113995d9a2973ff9 against b5a4cb90b41a1577134fa8398d1bc87fea32b899 are in. There are significant results. @oliver-butterley \*\*Large changes (6✅)\*\* - ✅ \`build/module/Spqr.Specs.Authenticator.Authenticator.MacCt//instructions\`: \*\*-8.7G\*\* (\*\*-31.80%\*\*) - ✅ \`build/module/Spqr.Specs.Authenticator.Authenticator.MacHdr//instructions\`: \*\*-8.0G\*\* (\*\*-31.10%\*\*) - ✅ …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/647#issuecomment-6069759774) — oliver-butterley (2026-10-08): In the two key files there was an argument that was repeated several times. It's possible to have fewer lines and much quicker proofs.
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/647#issuecomment-6070783406) — oliver-butterley (2026-10-08): !radar
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/647#issuecomment-6070796929) — baif-radar (2026-10-08): Benchmark results for 0f01564db601263ab4a7af674db1b99e9c665380 against b5a4cb90b41a1577134fa8398d1bc87fea32b899 are in. There are significant results. @oliver-butterley \*\*Large changes (7✅)\*\* - ✅ \`build/module/Spqr.Specs.Authenticator.Authenticator.MacCt//instructions\`: \*\*-8.7G\*\* (\*\*-31.78%\*\*) - ✅ \`build/module/Spqr.Specs.Authenticator.Authenticator.MacHdr//instructions\`: \*\*-8.0G\*\* (\*\*-31.05%\*\*) - ✅ …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/647#issuecomment-6071017700) — oliver-butterley (2026-10-08): !radar
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/647#issuecomment-6071018394) — baif-radar (2026-10-08): Benchmark results for e951677236fa5c4509fcfbed6bd81ad66f162bfc against b5a4cb90b41a1577134fa8398d1bc87fea32b899 are in. There are significant results. @oliver-butterley \*\*Large changes (7✅)\*\* - ✅ \`build/module/Spqr.Specs.Authenticator.Authenticator.MacCt//instructions\`: \*\*-8.6G\*\* (\*\*-31.73%\*\*) - ✅ \`build/module/Spqr.Specs.Authenticator.Authenticator.MacHdr//instructions\`: \*\*-8.0G\*\* (\*\*-30.99%\*\*) - ✅ …
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/647#pullrequestreview-5466619363) — truonghoangle (2026-10-09): (No text.)

### Item 648

**[Issue #648](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/648) — fix tag \`step\`**

Status: closed. Opened: 2026-10-09. Author: truonghoangle.

Body excerpt: there are 4 rust functions in spqr-verify which you verified but probe-aeneas says they're unverified; the issue is that they have 2 @\[step\] and probe-lean doesn't decide because the human should say which is the primary-spec; so probe-lean says that these functions don't have a primary-spec thus they're unverified. here are the functions: | Lean def (\`spqr.core.option.Option.Insts.…\`) | Specs, both \`@\[step\]\` | File …

No recorded comments or reviews.

### Item 649

**[PR #649](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/649) — fix tag \`step\` and verify and specify \`spqr::init\_inner\` in \`lib.rs\`**

Status: merged. Opened: 2026-10-09. Author: truonghoangle.

Body excerpt: This PR verifies and specifies \`spqr::init\_inner\` in \`lib.rs\` and fix tag \`step\` the issue is that they have 2 @\[step\] and probe-lean doesn't decide because the human should say which is the primary-spec; so probe-lean says that these functions don't have a primary-spec thus they're unverified. I was wondering, is it the case that one of these step thms can be chosen as the primary\_spec? in which case, we can add …

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/649#pullrequestreview-5486139392) — Zhang-Liao (2026-10-12): (No text.)

### Item 650

**[PR #650](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/650) — Harmonise \`spqr::v1::unchunked::send\_ek::serialize::EkSent::{into\_pb, from\_pb}\` via functional models and prove round trips**

Status: merged. Opened: 2026-10-09. Author: MarkusFerdinandDablander.

Body excerpt: This PR adds \`FunctionalModels.lean\` for the unchunked \`EkSent\` state, proves round trips, and pins the existing \`into\_pb\` and \`from\_pb\` spec theorems to the functional models, following the mathematical verification architecture discussed in #568. Closes #583

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/650#pullrequestreview-5471931275) — truonghoangle (2026-10-09): (No text.)

### Item 651

**[PR #651](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/651) — Migrate to \`module\` system**

Status: merged. Opened: 2026-10-11. Author: truonghoangle.

Body excerpt: This PR migrates the entire codebase (266 files, +1698/−595 lines) to the Lean 4 \`module\`. The key changes are: ### What changed - \*\*\`module\` headers\*\*: All 261 \`.lean\` files now use explicit \`module\` declarations instead of bare \`import\` lists. - \*\*\`public import\`\*\*: 580 imports converted from \`import\` to \`public import\`, making re-export semantics explicit. - \*\*\`@\[expose\] public section\`\*\*: 256 files wrapped their …

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/651#issuecomment-6104515485) — truonghoangle (2026-10-11): !radar
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/651#issuecomment-6104516002) — baif-radar (2026-10-11): Benchmark results for 6229c713d4e44ee6fe07c503c4ee03b2dc562ee5 against a70dff77a15d5f275c80570dd9b53576c1ee44e6 are in. There are significant results. @truonghoangle - 🟥 \`bench\` exited with code \*\*1\*\* \*\*Large changes (8✅)\*\* - ✅ \`build/module/HeaderLinter//instructions\`: \*\*-1.1G\*\* (\*\*-27.08%\*\*) - ✅ \`build/module/Spqr.Lint.Basic//instructions\`: \*\*-879.4M\*\* (\*\*-20.04%\*\*) - ✅ …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/651#issuecomment-6119514257) — oliver-butterley (2026-10-12): Nice work! I see that some stuff isn't properly exposed in Aeneas. Probably just string? I'll sort out a PR to Aeneas to solve that. I see this PR has another tweak to solve this but I believe there is a more elegant work around for this problem. Does an import all of the correct file in our repo also solve the problem?
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/651#discussion_r4245477782) — oliver-butterley (2026-10-12; SrcTranslated/FunsExternal.lean:7): Great! Yes, I see that the import all solve the Aeneas error with exposing String.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/651#pullrequestreview-5487491651) — oliver-butterley (2026-10-12): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/651#discussion_r4245486011) — oliver-butterley (2026-10-12; SrcTranslated/FunsExternal.lean:7): I.e., write here: -- \`to\_owned\_spec\` unfolds \`toStr\`, whose body upstream does not \`@\[expose\]\`. Remove this when mended in Aeneas. import all Aeneas.Std.String
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/651#pullrequestreview-5487501432) — oliver-butterley (2026-10-12): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/651#discussion_r4245490819) — oliver-butterley (2026-10-12; aeneas-config.yml:67): This is not required because instead we can \`import all Aeneas.Std.String\` in \`FunsExternal.lean\`.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/651#pullrequestreview-5487508211) — oliver-butterley (2026-10-12): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/651#discussion_r4245492038) — oliver-butterley (2026-10-12; aeneas-config.yml:67): I checked that this works correctly
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/651#issuecomment-6119816639) — oliver-butterley (2026-10-12): Link the Aeneas issue for toStr at the import all line to track the problem and revert soon. https://github.com/AeneasVerif/aeneas/issues/1415
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/651#issuecomment-6125118246) — oliver-butterley (2026-10-12): !radar
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/651#issuecomment-6125123099) — baif-radar (2026-10-12): Benchmark results for f5be41faaba479014c5434462ebbb5673ed7674d against 87aa1e7e5bab8324c469d52398a4cefa6cef84ba are in. There are significant results. @oliver-butterley \*\*Large changes (105✅, 1🟥)\*\* Too many entries to display here. View the full report on radar instead. \*\*Medium changes (118✅)\*\* Too many entries to display here. View the full report on radar instead. \*\*Small changes (24✅, 1🟥)\*\* Too many entries to …
- [review DISMISSED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/651#pullrequestreview-5487510073) — oliver-butterley (2026-10-12): 🚀
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/651#issuecomment-6126183902) — oliver-butterley (2026-10-12): FunctionalModels.lean needs \`module\` added, switch \`import\` to \`public import\`, and wrap the body in \`@\[expose\] public section\`.
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/651#issuecomment-6127792711) — github-actions[bot] (2026-10-12): ### Sorry Delta — hand-written specs \*\*7 new sorry-tainted declarations in \`Spqr.Specs.\*\`:\*\* | Module | Declaration | Kind | |--------|-------------|------| | \`Spqr.Specs.Encoding.Polynomial.Poly.FromCompletePoints\` | \`\_private.Spqr.Specs.Encoding.Polynomial.Poly.FromCompletePoints.0.spqr.encoding.polynomial.Poly.from\_complete\_points\_loop.body\_spec.\_proof\_1\_4\` | transitive | | …
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/651#pullrequestreview-5493586371) — oliver-butterley (2026-10-12): (No text.)
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/651#issuecomment-6139892261) — oliver-butterley (2026-10-13): &gt; ### Sorry Delta — hand-written specs &gt; &gt; \*\*7 new sorry-tainted declarations in \`Spqr.Specs.\*\`:\*\* &gt; Module Declaration Kind &gt; \`Spqr.Specs.Encoding.Polynomial.Poly.FromCompletePoints\` \`\_private.Spqr.Specs.Encoding.Polynomial.Poly.FromCompletePoints.0.spqr.encoding.polynomial.Poly.from\_complete\_points\_loop.body\_spec.\_proof\_1\_4\` transitive &gt; \`Spqr.Specs.Encoding.Polynomial.Poly.FromCompletePoints\` …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/651#issuecomment-6139908325) — oliver-butterley (2026-10-13): @Kukovec Both @truonghoangle and I have looked closely at this PR. However, since we have both made edits here, neither of us can approve the PR.
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/651#pullrequestreview-5499984276) — Zhang-Liao (2026-10-13): (No text.)

### Item 652

**[PR #652](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/652) — Harmonise \`spqr::v1::unchunked::send\_ek::serialize::EkSentCt1Received::{into\_pb, from\_pb}\` via functional models and prove round trips**

Status: merged. Opened: 2026-10-12. Author: MarkusFerdinandDablander.

Body excerpt: This PR adds \`FunctionalModels.lean\` for the unchunked \`EkSentCt1Received\` state, proves round trips, and pins the existing \`into\_pb\` and \`from\_pb\` spec theorems to the functional models, following the mathematical verification architecture discussed in #568. Closes #584

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/652#pullrequestreview-5491567628) — truonghoangle (2026-10-12): Great job!

### Item 653

**[Issue #653](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/653) — Extend Aeneas translation to the full verification scope**

Status: closed. Opened: 2026-10-12. Author: oliver-butterley.

Body excerpt: Using patches as and when required to complete the process.

No recorded comments or reviews.

### Item 654

**[PR #654](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/654) — Harmonise \`spqr::v1::unchunked::send\_ek::serialize::HeaderSent::{into\_pb, from\_pb}\` via functional models and prove round trips**

Status: merged. Opened: 2026-10-12. Author: MarkusFerdinandDablander.

Body excerpt: This PR adds \`FunctionalModels.lean\` for the unchunked \`HeaderSent\` state, proves round trips, and pins the existing \`into\_pb\` and \`from\_pb\` spec theorems to the functional models, following the architecture discussed in #568. Closes #582

Discussion and review record:

- [review DISMISSED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/654#pullrequestreview-5491575114) — truonghoangle (2026-10-12): Great job!
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/654#issuecomment-6126184006) — MarkusFerdinandDablander (2026-10-12): Hi @truonghoangle, thanks for reviewing! I had to resolve some minor conflicts now in here relative to main, so I think this branch requires your re-approval before I can merge. All the best and thanks for your help!
- [review DISMISSED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/654#pullrequestreview-5494179106) — truonghoangle (2026-10-12): (No text.)
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/654#issuecomment-6265332917) — MarkusFerdinandDablander (2026-10-19): Hi @truonghoangle , I have now made the work in this branch consistent with your recent migration to the Lean module system; waiting for your re-approval :-) !
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/654#pullrequestreview-5571304475) — truonghoangle (2026-10-19): (No text.)

### Item 655

**[PR #655](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/655) — Update to nightly-2026.10.12-d119a47**

Status: merged. Opened: 2026-10-12. Author: oliver-butterley.

Body excerpt: Update Aeneas. Rather minor changes. Also add module to some files that got missed before. - \[ \] depends on #651 (i.e., that one needs to be merged and then main merged here so the diff is small)

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/655#issuecomment-6127048661) — github-actions[bot] (2026-10-12): ### Sorry Delta — hand-written specs \*\*7 new sorry-tainted declarations in \`Spqr.Specs.\*\`:\*\* | Module | Declaration | Kind | |--------|-------------|------| | \`Spqr.Specs.Encoding.Polynomial.Poly.FromCompletePoints\` | \`\_private.Spqr.Specs.Encoding.Polynomial.Poly.FromCompletePoints.0.spqr.encoding.polynomial.Poly.from\_complete\_points\_loop.body\_spec.\_proof\_1\_4\` | transitive | | …
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/655#pullrequestreview-5499999718) — truonghoangle (2026-10-13): (No text.)

### Item 656

**[PR #656](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/656) — Translation patch files**

Status: merged. Opened: 2026-10-12. Author: oliver-butterley.

Body excerpt: Change how we deal will translation issues to use patch files instead. The faithfulness of the translation is audited by checking that within each patch file the Rust code is equivalent. Preparation for extending translation to the entire crate. - \[ \] depends on #655 (i.e., that other needs to be merged prior to this else the diff will be huge)

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/656#issuecomment-6129507294) — github-actions[bot] (2026-10-12): ### Sorry Delta — hand-written specs \*\*7 new sorry-tainted declarations in \`Spqr.Specs.\*\`:\*\* | Module | Declaration | Kind | |--------|-------------|------| | \`Spqr.Specs.Encoding.Polynomial.Poly.FromCompletePoints\` | \`\_private.Spqr.Specs.Encoding.Polynomial.Poly.FromCompletePoints.0.spqr.encoding.polynomial.Poly.from\_complete\_points\_loop.body\_spec.\_proof\_1\_4\` | transitive | | …
- [review DISMISSED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/656#pullrequestreview-5500003045) — truonghoangle (2026-10-13): (No text.)
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/656#issuecomment-6140456390) — oliver-butterley (2026-10-13): @truonghoangle I handled the merge conflict but now it needs approving again.
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/656#pullrequestreview-5500237270) — truonghoangle (2026-10-13): (No text.)

### Item 657

**[PR #657](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/657) — Merge Signal upstream v1.6.0**

Status: merged. Opened: 2026-10-12. Author: oliver-butterley.

Body excerpt: Update the Rust code to the latest upstream. This then has various other effects locally with some changes to the lean code. - \[ \] depends on #656 (i.e., diff will be huge unless the other is merged first)

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/657#issuecomment-6131274016) — github-actions[bot] (2026-10-12): ### Sorry Delta — hand-written specs \*\*1 new sorry-tainted declaration in \`Spqr.Specs.\*\`:\*\* | Module | Declaration | Kind | |--------|-------------|------| | \`Spqr.Specs.Encoding.Polynomial.PolyEncoder.ChunkAt\` | \`\_private.Spqr.Specs.Encoding.Polynomial.PolyEncoder.ChunkAt.0.spqr.encoding.polynomial.PolyEncoder.chunk\_at\_loop.body\_spec.\_proof\_1\_56\` | transitive |
- [review DISMISSED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/657#pullrequestreview-5500006548) — truonghoangle (2026-10-13): (No text.)
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/657#issuecomment-6141169967) — oliver-butterley (2026-10-13): @truonghoangle this also needs approving again since I merged in main.
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/657#pullrequestreview-5500705089) — truonghoangle (2026-10-13): (No text.)

### Item 658

**[PR #658](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/658) — Complete translation**

Status: merged. Opened: 2026-10-12. Author: oliver-butterley.

Body excerpt: Remove some more tweaks and replace them with patch files. Add patches for prost. - depends on #657 (i.e., the diff will look huge prior to that being merged) fixes #653

Discussion and review record:

- [review DISMISSED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/658#pullrequestreview-5500349500) — truonghoangle (2026-10-13): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/658#pullrequestreview-5500772074) — truonghoangle (2026-10-13): (No text.)

### Item 659

**[Issue #659](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/659) — Change \`public import\` to \`import\` whenever possible**

Status: open. Opened: 2026-10-13. Author: oliver-butterley.

Body excerpt: If an import is only used in the proofs we don't need it to be public. This will improve build efficiency because fewer files need to be rebuilt when certain files are modified.

No recorded comments or reviews.

### Item 660

**[PR #660](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/660) — Adjust imports for performance**

Status: merged. Opened: 2026-10-14. Author: oliver-butterley.

Body excerpt: Many files had public imports which didn't need to be public. These have been removed. The longest rebuild path is significantly quicker after these changes because it means that many of the files are now independent of each other.

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/660#issuecomment-6163383396) — oliver-butterley (2026-10-14): !radar
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/660#issuecomment-6163386404) — baif-radar (2026-10-14): Benchmark results for 21c8400026ba3d742e7a04e87e0e9291a1069bd9 against 339d49a5f09bc7c6a8f24a8835ae59ec577602cc are in. No significant results found. @oliver-butterley &gt; \[!WARNING\] &gt; These warnings may indicate that the benchmark results are not directly comparable, for example due to changes in the runner configuration or hardware. &gt; &gt; - Bench repo commit hashes for run bench differ between commits. \*\*Medium …
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/660#pullrequestreview-5514763447) — truonghoangle (2026-10-14): (No text.)

### Item 661

**[PR #661](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/661) — Specify and verifies NIST FIPS 203 (ML-KEM, August 2024) and all five public functions in \`incremental\_mlkem768.rs\`**

Status: merged. Opened: 2026-10-14. Author: truonghoangle.

Body excerpt: This PR provides a complete formal specification and verification of all five public functions in \`incremental\_mlkem768.rs\` against NIST FIPS 203 (ML-KEM, August 2024). Every FIPS 203 algorithm (1–18) is translated into human-readable Lean 4 definitions, and equational bridge proofs connect them to the Aeneas-extracted Lean code from \`libcrux-ml-kem\`. The end-to-end KEM round-trip is verified with \*\*no custom axioms …

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/661#issuecomment-6181727783) — Zhang-Liao (2026-10-15): The lean build fails
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/661#issuecomment-6184285393) — truonghoangle (2026-10-15): !radar
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/661#issuecomment-6184287066) — baif-radar (2026-10-15): Benchmark results for af89eda6f294ec9a1f799c8667f4703f15b04e4c against 5b474a9dc5bf32bcb4f8ed3b2f654a1a82d16ee8 are in. There are significant results. @truonghoangle - 🟥 \`bench\` exited with code \*\*1\*\* \*\*Large changes (2✅, 1🟥)\*\* - ✅ \`build/profile/blocked (unaccounted)//wall-clock\`: \*\*-6m 30s\*\* (\*\*-46.98%\*\*) - ✅ \`build/profile/import//wall-clock\`: \*\*-8m 15s\*\* (\*\*-85.43%\*\*) - 🟥 \`build/profile/type …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/661#issuecomment-6184402152) — truonghoangle (2026-10-15): @Zhang-Liao @a-dangelo I have now completed the specification and verification of all functions related to ML\_KEM 768. I have also compared my implementation of \`encaps1\` with the version provided by @a-dangelo (using both versions in a top-down approach for verification). Since the pull request (PR) is quite large - though the functions share a common verification background- I have pushed them all at once. If you …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/661#issuecomment-6184670282) — Zhang-Liao (2026-10-15): @truonghoangle I will find a quick way to review. Thanks for the great work!
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/661#issuecomment-6187160020) — a-dangelo (2026-10-15): Very nice and impressive work! It will take me a while to review, but you can keep it as it is, no need to split, just have a little patience!
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/661#discussion_r4293672752) — a-dangelo (2026-10-16; Spqr/Crypto/Fips203/PKE/KeyGen.lean:67): I think matrix the matrix we get is the transpose of FIPS 203's. It also uses that transpose consistently in both key generation and encryption. That consistency keeps the PR's round-trip proof valid while the bytes the specs describe differ from FIPS 203 and libcrux. ### FIPS 203 In Alg 13 step 5 and Alg 14 step 6 (FIPS-203.txt:1658, :1729), FIPS defines \`Â\[i,j\] ← SampleNTT(ρ‖j‖i)\`. The margin note says "j and i …
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/661#discussion_r4293699481) — a-dangelo (2026-10-16; SrcTranslated/FunsExternal.lean:1937): It looks like this is a bit different from libcrux's \`validate\_pk\_bytes\`. libcrux 0.0.10 (\`ind\_cca/incremental.rs:297-339\`) (1) requires \`pk1.len() == 64\` and \`pk2.len() == 1152\` exactly, (2) checks \`H(pk2 ‖ pk1\[0..32\]) == pk1\[32..64\]\`, and (3) returns \`InvalidPublicKey\` on a hash or modulus failure. The model uses \`&lt;\` tests, never reads the header bytes, and returns \`InvalidInputLength\`. So \`ek\_matches\_header\_spec\` …
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/661#discussion_r4293714770) — a-dangelo (2026-10-16; Spqr/Crypto/Fips203/Refinement/EncapsBytes.lean:97): The state codec is unsigned; libcrux stores signed \`i16\`. This section is titled "little-endian \`i16\`", but \`coeffLo\`/\`coeffHi\` serialise the canonical representative in \`\[0, q)\` and \`polyOfBytes\` reads it back unsigned. libcrux 0.0.10 \`EncapsState::to\_bytes\`/\`from\_bytes\` store the raw signed \`i16\` (ŷ in \`\[-3328, 3328\]\`, \`e2\` in \`\[-2, 2\]\`), and SPQR's repair code relies on that …
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/661#discussion_r4293769923) — a-dangelo (2026-10-16; SrcTranslated/FunsExternal.lean:2538): The issue-1275 workaround is stubbed to \`none\`. This function is SPQR's own Rust (\`src/incremental\_mlkem768.rs:85-138\`), not libcrux. It returns \`Some(flip\_endianness\_of\_encapsulation\_state es)\` when the first \`e2\` word other than \`0000\`/\`FFFF\` is \`0100\`, \`0200\` or \`FEFF\`. At base it was opaque. Here, \`encaps2\_spec\` unfolds the stub (\`Encaps2.lean:133-143\`) and claims \`result = ct2List es ek\` for every 2080-byte …
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/661#discussion_r4293840225) — a-dangelo (2026-10-16; SrcTranslated/FunsExternal.lean:1760): The libcrux trust assumption moved into \`def\` bodies. At base, \`encapsulate1/2\`, \`decapsulate\_compressed\_key\`, \`validate\_pk\_bytes\`, \`encaps\_state\_len\` and \`SHARED\_SECRET\_SIZE\` were \`noncomputable opaque\`, and \`from\_seed\` had a named axiom. Here they are \`def\`s whose bodies are the FIPS model (also \`:1790\`, \`:1936\`, \`:1974\`, \`:2041\`), and the Bridge equations are \`rfl\`. "libcrux computes this model" is now assumed by …
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/661#discussion_r4293878051) — a-dangelo (2026-10-16; Spqr/Crypto/Fips203/Refinement/LibcruxDecaps.lean:97): \`ssBytes\_roundTrip\` is stated over \`keyPairArray\`, \`ct1Array\`, \`ct2Array\` and \`ssBytes\`. It does not mention \`spqr.incremental\_mlkem768.generate/encaps1/encaps2/decaps\` or the externals, and no theorem composes the four SPQR spec theorems. The PR body ("The end-to-end KEM round-trip is verified") and \`Decaps.lean:32-35\` might convey a more general scenario being verified. Could you either add a more general …
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/661#discussion_r4293904689) — a-dangelo (2026-10-16; Spqr/Crypto/Fips203/Refinement/LibcruxDecaps.lean:1): shouldn't all the Libcrux related specs be in FunsExternal or some other place? it's an external crate so treated as a blackbox, it might need it's own place (idk some LibcruxExternal/ folder next to FunsExternal), because I guess we're just modelling the boudnaries of the libcrux primitives needed for the actual FC work in SPQR, right? related to this, the PR description kind of masks a bit the trust base. libcrux …
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/661#discussion_r4293963626) — a-dangelo (2026-10-16; Spqr/Crypto/Fips203/Conversion/BitsToBytes.lean:10): In FIPS 203 (August 2024) BitsToBytes is Algorithm 3, not 1. The docstrings shift Algorithms 3-12 down by two throughout (\`NTT.lean:9\` "Algorithm 7", \`NTT/RoundTrip.lean:15-16\`, …). They call Compress/Decompress "Algorithms 11-12", but those are MultiplyNTTs/BaseCaseMultiply; Compress/Decompress are eqs. (4.7)/(4.8). \`Ring.lean:32\` cites § 2.4, which is "Interpreting the Pseudocode". Docstrings also cite an absent …
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/661#discussion_r4294019707) — a-dangelo (2026-10-16; Spqr/Crypto/Fips203/Params.lean:2): \`Spqr/Crypto/Fips203/\*\*\` re-specifies, concept by concept, the model in VCVio \`LatticeCrypto.MLKEM\` (Params, Rq/Tq, NTT and its inverse laws, ByteEncode/Decode, Compress, SampleNTT/CBD, K-PKE, KEM). secure-messaging's ML-KEM correctness and security models build on that model, and this PR has no reuse statement or adapter. Within this repo, \`ParamSet\` duplicates \`Spqr.Mlkem.MlkemParams\` …
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/661#discussion_r4294035871) — a-dangelo (2026-10-16; Spqr/Crypto/Fips203/KEM/EncapsIncremental.lean:43): This incremental split duplicates secure-messaging's interface without a link. \`EncapsHeader (ρ, h)\`, \`EncapsState (ŷ, e2, m)\`, \`mlkemEncapsPhase1/2\` and \`mlkemEncaps\_ct\_eq\_phases\` mirror secure-messaging's \`incrementalHeader\`, \`EncapsulationState\`, \`incrementalEncaps1/2\` and \`encaps\_eq\_stagedEncaps\` (\`KEM/IncrementalKEM/{FromMLKEM,Defs}.lean\`). The K-PKE recovery step (\`kpke\_roundTrip\`, \`&lt; ⌊q/4⌋\`) mirrors its …
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/661#discussion_r4294050647) — a-dangelo (2026-10-16; Spqr/Crypto/Fips203/PKE/RoundTrip.lean:633): Nitpic: the "noise bound" hypothesis is the decryption-success event. \`kpke\_roundTrip\` (and \`mlkem\_roundTrip\`) assume \`absZq(honestW − Decompress₁(m)) &lt; ⌊q/4⌋\`, where \`honestW\` is the full decryption polynomial computed from the compressed honest ciphertext. The proof then rewrites decryption to \`recoverMsg honestW\`. That is close to assuming the conclusion, and it is not stated over the sampled noise terms that a …
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/661#discussion_r4294069785) — a-dangelo (2026-10-16; Spqr/Specs/IncrementalMlkem768/Encaps1.lean:86): \`encaps1\_spec\` (and \`generate\_spec\`, \`Generate.lean:70-73\`) expose the message or seed only as \`∃ m\` or \`∃ seed\`. Yet the proofs use exactly the bytes \`fill\_bytes\` wrote (\`Encaps1.lean:124\`, \`Generate.lean:92\`), and the docstrings say so. For the secure-messaging refinement, the coins must be identified with the RNG output so that a distribution can be attached. Could you state that the witness is the byte string …
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/661#discussion_r4294080482) — a-dangelo (2026-10-16; Spqr/Specs/IncrementalMlkem768/Decaps.lean:26): nitpic: this line says ML-KEM.Decaps' input validation "concerns only byte lengths". § 7.3 also requires the hash check \`H(dk\[384k:768k+32\]) = dk\[768k+32:768k+64\]\`. libcrux \`decapsulate\_compressed\_key\` skips that check, and \`decaps\_spec\` admits any 2400-byte \`dk\` and returns \`Decaps\_internal\`. Up to you if you want to edit it or not
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/661#discussion_r4294195252) — a-dangelo (2026-10-16; Spqr/Crypto/Fips203/Sampling/SampleNTT.lean:113): Nitpic: - FIPS 203 Alg 7 loops while j &lt; 256 with no upper bound. Each pass takes 3 fresh XOF bytes and accepts up to two candidates below q. - Appendix B allows a cap, but only under two conditions: - the cap is at least 280 iterations; - when it is hit, the algorithm must "destroy all intermediate results", and any return value or exception must be "the same value for any execution in which the maximum number of …
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/661#discussion_r4294215688) — a-dangelo (2026-10-16; Spqr/Crypto/Fips203/PKE/KeyGen.lean:45): \`hashG\`, \`prf\`, \`hashH\`, \`hashJ\` and \`xof\` are global \`opaque\` constants. The theorems are about one fixed, unspecified family. They cannot be instantiated with SHA3/SHAKE or transported to another family. VCVio's ML-KEM, which secure-messaging uses, is parameterised by a \`Primitives\` structure. So the PR's "theorems hold for any instantiation" is a bit misleading, but the real concern I have is that the SM→SPQR …
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/661#discussion_r4294227003) — a-dangelo (2026-10-16; Spqr/Crypto/Fips203/Noise/FailureRate.lean:1): \`Noise/\` is unused and overlaps secure-messaging. The five \`Noise\` modules (about 600 lines) are imported only by \`Spqr.lean\` and by each other. No Bridge, KEM, PKE or Specs statement uses them, and the numeric failure bound is conditional on a hypothesis. secure-messaging already hosts the ML-KEM noise and failure-rate model (\`KEM/MLKEM/Correctness/Noise\*.lean\`). Could you drop \`Noise/\*\*\` from this PR? It can be …
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/661#discussion_r4294256126) — a-dangelo (2026-10-16; Spqr/Crypto/Fips203/PKE/Decrypt.lean:146): Some theorems do not constrain the function they are named for. \`kpkeDecrypt\_msg\_size\` states \`∀ i, ∃ b, kpkeDecrypt p dk c i = b\`, which holds for any function. \`byteDecode\_lt\_4096\` (\`ByteDecode.lean:163-167\`) takes \`B\` but applies \`byteDecode\` to a term built from \`by omega\`. \`samplePolyCBD\_eta2\_input\_bits\` and \`\_input\_bytes\` (\`SamplePolyCBD.lean:127-132\`) are arithmetic identities.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/661#pullrequestreview-5546541269) — a-dangelo (2026-10-16): Nice and impressive work! I left some comments. If I may suggest: we should probably avoid the word 'bridge' as much as possible since in libsignal there's a whole folder/crate named as such that 'bridges different backends', so it might create confusion to have this word used in many different contexts. Also the bridge between the secuirty games. andproofs of the protocols requires a bit more than FC, so you'd have …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/661#issuecomment-6230132464) — truonghoangle (2026-10-17): @a-dangelo thank your for your comments. \*\*Summary of changes addressing your comments:\*\* 1. \*\*Renamed \`Bridge\` → \`Refinement\`\*\*: All files under \`Spqr/Crypto/Fips203/Bridge/\` have been renamed to \`Spqr/Crypto/Fips203/Refinement/\` (DecapsBytes, EncapsBytes, KeyPairBytes, LibcruxDecaps, LibcruxEncaps1, LibcruxEncaps2, LibcruxKeygen). All references throughout the codebase (imports, namespace qualifiers, doc comments) …
- [review DISMISSED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/661#pullrequestreview-5582255983) — a-dangelo (2026-10-20): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/661#pullrequestreview-5584355344) — a-dangelo (2026-10-20): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/661#pullrequestreview-5584575265) — Zhang-Liao (2026-10-20): (No text.)

### Item 662

**[Issue #662](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/662) — PROP-30: States::recv epoch and payload-type dispatch**

Status: open. Opened: 2026-10-15. Author: astefano.

Body excerpt: Prove that \`States::recv\` dispatches on the message epoch and payload type as the ML-KEM Braid Rev. 1 §2.5 \`Receive\` functions do (\`src/v1/chunked/states.rs:275-533\`). - A message from an earlier epoch leaves the state unchanged and emits no key. - A message from a later epoch returns \`Err(EpochOutOfRange)\`, except in \`Ct2Sampled\` at exactly the next epoch, which moves to \`KeysUnsampled\` (transition 13). The spec …

No recorded comments or reviews.

### Item 663

**[PR #663](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/663) — States::recv follows ML-KEM Braid §2.5 Receive, up to three deviations**

Status: open draft. Opened: 2026-10-15. Author: astefano.

Body excerpt: \`States::recv\` (\`src/v1/chunked/states.rs:275-533\`) computes a party's next state, and possibly a message key, when a message arrives. This PR proves that it agrees with the \`Receive\` functions of ML-KEM Braid Rev. 1 §2.5, except in three places. Code links point to \`src/\` at \`dd8e6b9\`, which is the same as \`src/\` at the head of this PR. ## Main result For every state and every message, \`States::recv\` and §2.5 give …

Discussion and review record:

- [review DISMISSED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/663#pullrequestreview-5561875391) — truonghoangle (2026-10-18): (No text.)
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/663#issuecomment-6336002467) — astefano (2026-10-22): !radar
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/663#issuecomment-6336019237) — baif-radar (2026-10-22): Benchmark results for 06f999b53039d0f093efbc68e9028bc5498cb8a9 against 2ab18fd7ed5890c79e80935edcb0ccdae36f446f are in. There are significant results. @astefano - 🟥 \`bench\` exited with code \*\*1\*\* \*\*Medium changes (1✅, 1🟥)\*\* - 🟥 \`build/module/Spqr.Crypto.Fips203.NTT.InvKernel2//instructions\`: \*\*+12.9G\*\* (\*\*+15.36%\*\*) - ✅ \`build/module/Spqr.Crypto.Fips203.NTT.InvKernel3//instructions\`: \*\*-10.8G\*\* (\*\*-11.20%\*\*) \*\*Small …

### Item 665

**[Issue #665](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/665) — Specify and verify \`From\` in \`spqr::proto::pq\_ratchet::Direction\`**

Status: closed. Opened: 2026-10-16. Author: truonghoangle.

Body excerpt: \`spqr::proto::pq\_ratchet::{impl core::convert::From for i32}\` \`::from\`

No recorded comments or reviews.

### Item 666

**[Issue #666](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/666) — Specify and verify \`From\` in \`spqr::proto::pq\_ratchet::Version\`**

Status: closed. Opened: 2026-10-16. Author: truonghoangle.

Body excerpt: \`spqr::proto::pq\_ratchet::{impl core::convert::From for i32}\` \`::from\`

No recorded comments or reviews.

### Item 667

**[PR #667](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/667) — specifies and verifies \`From\` in \`spqr::proto::pq\_ratchet::Direction\`**

Status: merged. Opened: 2026-10-16. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`From\` in \`spqr::proto::pq\_ratchet::Direction\` and Add back the spqr::init\_inner file in lib.rs because it was removed during the Aeneas update process. (See PR #649) closes #665

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/667#pullrequestreview-5548885217) — Zhang-Liao (2026-10-16): (No text.)

### Item 668

**[PR #668](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/668) — Perf: Key/Key32**

Status: merged. Opened: 2026-10-16. Author: oliver-butterley.

Body excerpt: Note that the two statements (key\_spec, key\_spec\_32) are now stronger, each has two fewer hypothesis. No other spec theorems have been touched.

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/668#issuecomment-6213409228) — oliver-butterley (2026-10-16): !radar
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/668#issuecomment-6213415201) — baif-radar (2026-10-16): Benchmark results for 8285668c6435a8b72bd52dcf77f350550c964fd8 against 236adcc15e4405bfd7baafb87c9a9cb3afa7a011 are in. There are significant results. @oliver-butterley \*\*Large changes (2✅)\*\* - ✅ \`build/module/Spqr.Specs.Chain.ChainEpochDirection.Key//instructions\`: \*\*-62.2G\*\* (\*\*-63.57%\*\*) - ✅ \`build/module/Spqr.Specs.Chain.ChainEpochDirection.Key32//instructions\`: \*\*-85.6G\*\* (\*\*-92.13%\*\*) \*\*Medium changes (2✅)\*\* - …
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/668#pullrequestreview-5550966521) — truonghoangle (2026-10-16): Great job!

### Item 669

**[PR #669](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/669) — Specify and verify \`From\` in \`spqr::proto::pq\_ratchet::Version\`**

Status: merged. Opened: 2026-10-16. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`From\` in \`spqr::proto::pq\_ratchet::Version\` closes #666

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/669#pullrequestreview-5566556943) — Zhang-Liao (2026-10-19): (No text.)

### Item 670

**[PR #670](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/670) — Perf: speed up gc**

Status: merged. Opened: 2026-10-17. Author: oliver-butterley.

Body excerpt: (No text.)

Discussion and review record:

- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/670#pullrequestreview-5558361171) — oliver-butterley (2026-10-17): !radar
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/670#issuecomment-6235582398) — oliver-butterley (2026-10-17): !radar
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/670#issuecomment-6235586922) — baif-radar (2026-10-17): Benchmark results for 18920b61382a3ddc20a69e77019aaf6abd2a6a2d against c6f9bc07684958dec56f4c67e3941e399afe4263 are in. There are significant results. @oliver-butterley \*\*Large changes (1✅)\*\* - ✅ \`build/module/Spqr.Specs.Chain.KeyHistory.Gc//instructions\`: \*\*-45.7G\*\* (\*\*-41.11%\*\*) \*\*Small changes (1✅, 1🟥)\*\* - ✅ \`build/module/Spqr.Auxiliary.SpecTags//instructions\`: \*\*-270.7M\*\* (\*\*-8.30%\*\*) - 🟥 \`build/profile/blocked …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/670#issuecomment-6235819100) — oliver-butterley (2026-10-17): Build time increases in this PR... investigating! The test data seems inconsistent, perhaps it is noise. :thinking:
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/670#issuecomment-6235871792) — oliver-butterley (2026-10-17): !radar
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/670#issuecomment-6235884931) — baif-radar (2026-10-17): Benchmark results for 18920b61382a3ddc20a69e77019aaf6abd2a6a2d against c6f9bc07684958dec56f4c67e3941e399afe4263 are in. (These commits have already been benchmarked in a previous command.) There are significant results. @oliver-butterley \*\*Large changes (1✅)\*\* - ✅ \`build/module/Spqr.Specs.Chain.KeyHistory.Gc//instructions\`: \*\*-45.7G\*\* (\*\*-41.11%\*\*) \*\*Small changes (1✅, 1🟥)\*\* - ✅ …
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/670#pullrequestreview-5558690541) — truonghoangle (2026-10-17): (No text.)

### Item 671

**[PR #671](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/671) — Perf: improve sendkey**

Status: merged. Opened: 2026-10-17. Author: oliver-butterley.

Body excerpt: (No text.)

Discussion and review record:

- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/671#pullrequestreview-5558372867) — oliver-butterley (2026-10-17): !radar
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/671#issuecomment-6235833791) — oliver-butterley (2026-10-17): !radar
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/671#issuecomment-6235840675) — baif-radar (2026-10-17): Benchmark results for cb6790bd9a8f345cb122a363424d9fe0639ee543 against c6f9bc07684958dec56f4c67e3941e399afe4263 are in. There are significant results. @oliver-butterley \*\*Large changes (1✅)\*\* - ✅ \`build/module/Spqr.Specs.Chain.Chain.SendKey//instructions\`: \*\*-20.1G\*\* (\*\*-31.66%\*\*) \*\*Medium changes (1🟥)\*\* - 🟥 \`build/profile/blocked (unaccounted)//wall-clock\`: \*\*+1m 43s\*\* (\*\*+16.31%\*\*)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/671#pullrequestreview-5558692150) — truonghoangle (2026-10-17): (No text.)

### Item 672

**[PR #672](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/672) — Perf: improve 4 poly encoder files**

Status: merged. Opened: 2026-10-17. Author: oliver-butterley.

Body excerpt: (No text.)

Discussion and review record:

- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/672#pullrequestreview-5558381748) — oliver-butterley (2026-10-17): !radar
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/672#issuecomment-6235518452) — oliver-butterley (2026-10-17): !radar
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/672#issuecomment-6235525878) — baif-radar (2026-10-17): Benchmark results for b94f42cdf177f43a01e91e45ac9826512c73c2d4 against c6f9bc07684958dec56f4c67e3941e399afe4263 are in. There are significant results. @oliver-butterley \*\*Large changes (4✅)\*\* - ✅ \`build/module/Spqr.Specs.Encoding.Polynomial.Poly.FromCompletePoints//instructions\`: \*\*-84.5G\*\* (\*\*-69.74%\*\*) - ✅ \`build/module/Spqr.Specs.Encoding.Polynomial.PolyEncoder.ChunkAt//instructions\`: \*\*-49.0G\*\* (\*\*-53.76%\*\*) - ✅ …
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/672#pullrequestreview-5558694431) — truonghoangle (2026-10-17): (No text.)

### Item 673

**[PR #673](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/673) — Perf: improve 3 poly pb files**

Status: merged. Opened: 2026-10-17. Author: oliver-butterley.

Body excerpt: As with all the perf updates, none of the statements of the spec theorems have changed. Note: the helper function \`U16.toBEBytes\_pair\_val\` was already in the code, it has just been moved to a more natural location.

Discussion and review record:

- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/673#pullrequestreview-5558391014) — oliver-butterley (2026-10-17): !radar
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/673#issuecomment-6235792230) — oliver-butterley (2026-10-17): !radar
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/673#issuecomment-6235803197) — baif-radar (2026-10-17): Benchmark results for 8276dbda637708fcd91a0dc70db97cd0f2e7e571 against c6f9bc07684958dec56f4c67e3941e399afe4263 are in. There are significant results. @oliver-butterley \*\*Large changes (2✅, 1🟥)\*\* - 🟥 \`build/module/Spqr.Auxiliary.Aeneas.Scalar//instructions\`: \*\*+2.9G\*\* (\*\*+40.87%\*\*) - ✅ \`build/module/Spqr.Specs.Encoding.Polynomial.PolyDecoder.IntoPb//instructions\`: \*\*-35.0G\*\* (\*\*-54.67%\*\*) - ✅ …
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/673#pullrequestreview-5558697136) — truonghoangle (2026-10-17): (No text.)

### Item 674

**[PR #674](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/674) — Perf: improve 3 lagrange files**

Status: merged. Opened: 2026-10-17. Author: oliver-butterley.

Body excerpt: (No text.)

Discussion and review record:

- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/674#pullrequestreview-5558406079) — oliver-butterley (2026-10-17): !radar
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/674#issuecomment-6235843608) — oliver-butterley (2026-10-17): !radar
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/674#issuecomment-6235853822) — baif-radar (2026-10-17): Benchmark results for 5db5017c1c33d940444a83e82cfd09edba0c7be4 against c6f9bc07684958dec56f4c67e3941e399afe4263 are in. There are significant results. @oliver-butterley \*\*Large changes (3✅)\*\* - ✅ \`build/module/Spqr.Specs.Encoding.Polynomial.Poly.LagrangeInterpolate//instructions\`: \*\*-40.9G\*\* (\*\*-52.50%\*\*) - ✅ \`build/module/Spqr.Specs.Encoding.Polynomial.Poly.LagrangeInterpolateComplete//instructions\`: \*\*-24.9G\*\* …
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/674#pullrequestreview-5558699834) — truonghoangle (2026-10-17): (No text.)

### Item 675

**[PR #675](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/675) — Perf: improve 3 poly arith files**

Status: merged. Opened: 2026-10-17. Author: oliver-butterley.

Body excerpt: (No text.)

Discussion and review record:

- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/675#pullrequestreview-5558413691) — oliver-butterley (2026-10-17): !radar
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/675#issuecomment-6235798070) — oliver-butterley (2026-10-17): !radar
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/675#issuecomment-6235803334) — baif-radar (2026-10-17): Benchmark results for 7fc00b187952bf8c24af3c25f03bc75957815599 against c6f9bc07684958dec56f4c67e3941e399afe4263 are in. There are significant results. @oliver-butterley \*\*Large changes (3✅)\*\* - ✅ \`build/module/Spqr.Specs.Encoding.Polynomial.Poly.AddAssign//instructions\`: \*\*-20.3G\*\* (\*\*-37.36%\*\*) - ✅ \`build/module/Spqr.Specs.Encoding.Polynomial.PolyConst.MultXdiff//instructions\`: \*\*-35.1G\*\* (\*\*-57.69%\*\*) - ✅ …
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/675#pullrequestreview-5558701196) — truonghoangle (2026-10-17): (No text.)

### Item 676

**[Issue #676](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/676) — Lean CI saves the build cache before building the project**

Status: closed. Opened: 2026-10-17. Author: w-woloszyn.

Body excerpt: The Lean workflow uses \`lean-action\` with \`build: false\`, then runs \`lake build\` separately. \`lean-action\` saves \`.lake\` before that step, so the cache does not include the completed Aeneas and SPQR build. Run 39064123457 saves its cache before an 8m45s build. Run 39066114113 restores that same cache but recompiles Aeneas and SPQR. Save \`.lake\` after the build and linter finish so subsequent runs can reuse their …

No recorded comments or reviews.

### Item 677

**[PR #677](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/677) — Fix Lean build caching in CI**

Status: merged. Opened: 2026-10-17. Author: w-woloszyn.

Body excerpt: This PR saves \`.lake\` after the Lean build, lint, and audit succeed. \`lean-action\` currently saves it during setup, before the separate build, so later runs rebuild Aeneas and SPQR despite a cache hit. Use \`actions/cache\` for restore and post-job save, disable \`lean-action\`'s internal GitHub cache, and propagate \`lake build\` failures through \`tee\`. Validated with actionlint and shell checks for build failures and …

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/677#issuecomment-6259193374) — Zhang-Liao (2026-10-19): ~80% of each 2.6 GB cache entry is mathlib's oleans (\`.lake/packages/mathlib/.lake/build\`, ~7 GB uncompressed locally). Those already come from mathlib's own CDN via \`lake exe cache get\`, which \`lean-action\` runs for us (\`use-mathlib-cache: true\`) and which takes about a minute. Only the Spqr, SrcTranslated and Aeneas oleans (~1 GB uncompressed) actually need the GitHub cache. Excluding the mathlib build from the …
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/677#pullrequestreview-5581225985) — Zhang-Liao (2026-10-20): (No text.)
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/677#issuecomment-6287056775) — oliver-butterley (2026-10-20): What's happening with this PR? It seems it is ready and was approved but never got merged? :thinking:
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/677#issuecomment-6287145473) — truonghoangle (2026-10-20): @oliver-butterley it depends on when the author wants to merge it.
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/677#issuecomment-6287170783) — oliver-butterley (2026-10-20): @w-woloszyn? Merge this and then make further improvements in a later PR?
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/677#issuecomment-6287180277) — Zhang-Liao (2026-10-20): @oliver-butterley I am waiting for the author to merge it @w-woloszyn has already made the improvements mentioned by me
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/677#issuecomment-6288829101) — w-woloszyn (2026-10-20): My apologies for the delay, each time I tried to merge I had to update the branch and wait for checks!

### Item 678

**[PR #678](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/678) — Specify and verify : spqr::initial\_state in lib.rs**

Status: merged. Opened: 2026-10-19. Author: truonghoangle.

Body excerpt: This PR specifies and verifies : \`spqr::initial\_state\` in \`lib.rs\` closes #426

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/678#issuecomment-6268363845) — Zhang-Liao (2026-10-19): The V1 postcondition seems too weak to fully characterize initialization. Could we strengthen it to require: - \`vn.direction\` and \`vn.min\_version\` equal the protobuf encodings of the corresponding input parameters; - \`vn.chain\_params = some cp\`, where \`ChainParams.into\_pb params.chain\_params = ok cp\`; - the V1 inner state is \`KeysUnsampled\` for A2B and \`NoHeaderReceived\` for B2A. Currently, incorrect values in these …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/678#issuecomment-6282712220) — truonghoangle (2026-10-20): @Zhang-Liao I fixed it. Thank you for your comments
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/678#discussion_r4337338246) — Zhang-Liao (2026-10-21; Spqr/Specs/Lib/InitialState.lean:90): \*\*AI review (Codex)\*\* \*\*\[P2\] Chain parameters still aren't tied to the input\*\* \`vn.chain\_params ≠ none\` accepts arbitrary \`max\_jump\` and \`max\_ooo\_keys\` values, so incorrect serialized parameters would still satisfy the specification. This leaves the chain-parameter requirement from the earlier review unresolved, despite the documentation claiming that parameters are faithfully transcribed. Please strengthen this …
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/678#pullrequestreview-5600375965) — Zhang-Liao (2026-10-21): \*\*AI review (Codex)\*\* Re-reviewed at \`7f2e8d1a\`. The direction, minimum-version, and direction-specific inner-state requirements from the earlier review are now addressed. One remaining finding is noted inline: chain parameters are still not tied to the input. Validation: both changed Lean modules compile against the local dependencies.
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/678#discussion_r4338193940) — truonghoangle (2026-10-21; Spqr/Specs/Lib/InitialState.lean:90): \*\*Spec change.\*\* The conjunct is now \`\`\`lean ∃ cp, vn.chain\_params = some cp ∧ chain.ChainParams.into\_pb params.chain\_params = ok cp \`\`\` i.e. the stored value must be exactly what the real conversion (\`src/chain.rs:40-53\`, the code \`initial\_state\` actually calls) produces from the input. This rules out both "missing" and "wrong" in one conjunct, and reuses \`into\_pb\` rather than re-encoding the zero-as-default logic …
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/678#pullrequestreview-5601483820) — truonghoangle (2026-10-21): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/678#pullrequestreview-5602749626) — Zhang-Liao (2026-10-21): (No text.)

### Item 679

**[PR #679](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/679) — Update Aeneas to nightly 2026.10.15 cd41995**

Status: merged. Opened: 2026-10-19. Author: oliver-butterley.

Body excerpt: Update Aeneas and mend some proofs which needed adjusting.

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/679#issuecomment-6265523162) — oliver-butterley (2026-10-19): !radar
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/679#issuecomment-6265537888) — baif-radar (2026-10-19): Benchmark results for 95c2f6bd8b12d69fc55f144bf218cf6f2d4f6398 against b17ade9eaa0b657c06bdb502216cb213f4d880be are in. There are significant results. @oliver-butterley \*\*Large changes (10✅, 2🟥)\*\* - 🟥 \`build/module/Spqr.Lint.SpecIndent//instructions\`: \*\*+5.5G\*\* (\*\*+79.43%\*\*) - ✅ \`build/module/Spqr.Math.Gf2Poly.NatRep//instructions\`: \*\*-4.8G\*\* (\*\*-21.63%\*\*) - ✅ …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/679#issuecomment-6265824326) — oliver-butterley (2026-10-19): Note: this PR includes a minor adjustment to Audit.lean because Lean now reports compiler based axioms using a different naming scheme. @astefano
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/679#issuecomment-6265825798) — oliver-butterley (2026-10-19): !radar
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/679#issuecomment-6265834124) — baif-radar (2026-10-19): Benchmark results for 13388896403e0ef8296d1c9938538ecf1a25add8 against b17ade9eaa0b657c06bdb502216cb213f4d880be are in. There are significant results. @oliver-butterley \*\*Large changes (11✅, 3🟥)\*\* - 🟥 \`build/module/Spqr.Crypto.RFC5869//instructions\`: \*\*+433.1M\*\* (\*\*+26.40%\*\*) - 🟥 \`build/module/Spqr.Lint.SpecIndent//instructions\`: \*\*+5.4G\*\* (\*\*+78.45%\*\*) - ✅ \`build/module/Spqr.Math.Gf2Poly.NatRep//instructions\`: …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/679#issuecomment-6266059300) — oliver-butterley (2026-10-19): &gt; Benchmark results for 13388896403e0ef8296d1c9938538ecf1a25add8 against b17ade9eaa0b657c06bdb502216cb213f4d880be are in. There are significant results. @oliver-butterley Overall build times are down. However \`Spqr.Lint.SpecIndent\` is up. However this module needs to be removed soon since the same task can now been done using the upstream linter.
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/679#issuecomment-6267711623) — oliver-butterley (2026-10-19): @copilot resolve the merge conflicts in this pull request
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/679#issuecomment-6267756225) — Copilot (2026-10-19): &gt; @copilot resolve the merge conflicts in this pull request Merged \`main\` and resolved the conflict in \`FromPb.lean\` in merge commit \`94af804\`.
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/679#pullrequestreview-5573996679) — truonghoangle (2026-10-19): (No text.)

### Item 680

**[PR #680](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/680) — Harmonise \`spqr::v1::unchunked::send\_ct::serialize::Ct1Sent::{into\_pb, from\_pb}\` via functional models and prove round trips**

Status: merged. Opened: 2026-10-19. Author: MarkusFerdinandDablander.

Body excerpt: This PR adds \`FunctionalModels.lean\` for the unchunked \`Ct1Sent\` state, proves round trips, and pins the existing \`into\_pb\` and \`from\_pb\` spec theorems to the functional models, following the architecture discussed in #568.

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/680#pullrequestreview-5574770574) — truonghoangle (2026-10-19): (No text.)

### Item 681

**[Issue #681](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/681) — Specify and verify \`call\_once\` in \`decoded\_message\`**

Status: closed. Opened: 2026-10-19. Author: truonghoangle.

Body excerpt: /-- \[spqr::encoding::polynomial::{impl spqr::encoding::Decoder for spqr::encoding::polynomial::PolyDecoder}::decoded\_message::{impl core::ops::function::FnOnce&gt; for spqr::encoding::polynomial::{impl spqr::encoding::Decoder for spqr::encoding::polynomial::PolyDecoder}::decoded\_message::{closure}}::call\_once\]: Source: 'src/encoding/polynomial.rs', lines 942:65-942:73 -/

No recorded comments or reviews.

### Item 682

**[Issue #682](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/682) — Specify and verify \`call\_mut\` in \`decoded\_message\`**

Status: closed. Opened: 2026-10-19. Author: truonghoangle.

Body excerpt: /-- \[spqr::encoding::polynomial::{impl spqr::encoding::Decoder for spqr::encoding::polynomial::PolyDecoder}::decoded\_message::{impl core::ops::function::FnMut&gt; for spqr::encoding::polynomial::{impl spqr::encoding::Decoder for spqr::encoding::polynomial::PolyDecoder}::decoded\_message::{closure}}::call\_mut\]: Source: 'src/encoding/polynomial.rs', lines 942:65-942:73 -/

No recorded comments or reviews.

### Item 683

**[PR #683](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/683) — Specify and verify \`spqr::encoding::polynomial::{impl Decoder for PolyDecoder}::decoded\_message\` in \`polynomial.rs\`**

Status: merged. Opened: 2026-10-19. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::encoding::polynomial::{impl Decoder for PolyDecoder}::decoded\_message\` in \`polynomial.rs\` and its relations of functions closes #681 closes #682 closes #263

Discussion and review record:

- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/683#discussion_r4321338654) — Zhang-Liao (2026-10-20; Spqr/Specs/Encoding/Polynomial/PolyDecoder/DecodedMessage/DecodedMessage.lean:646): The current \`binary\_search\` model always selects the \*\*first\*\* match, which Rust does not guarantee. For example, for points \`\[(0, 10), (0, 20)\]\` compared only by \`x\`, \`lookupY\` returns \`10\`, while Rust may select \`20\`. Rust’s \`SortedSet\` prevents duplicate \`x\` values, but Lean models it as a plain \`Vec\`, without enforcing sortedness or uniqueness. Please make this invariant explicit in the spec: \`\`\`lean -- …
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/683#pullrequestreview-5580618915) — Zhang-Liao (2026-10-20): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/683#discussion_r4322179819) — truonghoangle (2026-10-20; Spqr/Specs/Encoding/Polynomial/PolyDecoder/DecodedMessage/DecodedMessage.lean:646): Thank you for your comments. I fixed it
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/683#pullrequestreview-5581599086) — truonghoangle (2026-10-20): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/683#pullrequestreview-5608726588) — Zhang-Liao (2026-10-22): (No text.)

### Item 684

**[PR #684](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/684) — Specify and verify : \`spqr::v1::unchunked::send\_ct::{spqr::v1::unchunked::send\_ct::NoHeaderReceived}::new\` in 'src/v1/unchunked/send\_ct.rs'**

Status: merged. Opened: 2026-10-19. Author: truonghoangle.

Body excerpt: This PR specifies and verifies : \`spqr::v1::unchunked::send\_ct::{spqr::v1::unchunked::send\_ct::NoHeaderReceived}::new\` in 'src/v1/unchunked/send\_ct.rs' closes #626

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/684#pullrequestreview-5580305464) — Zhang-Liao (2026-10-20): (No text.)

### Item 685

**[Issue #685](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/685) — Verify \`src/v1/unchunked/send\_ek.rs\`**

Status: open. Opened: 2026-10-19. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 686

**[Issue #686](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/686) — specify and verify \`spqr::v1::unchunked::send\_ek::{spqr::v1::unchunked::send\_ek::KeysUnsampled}::new\` in \`src/v1/unchunked/send\_ek.rs\`**

Status: closed. Opened: 2026-10-19. Author: truonghoangle.

Body excerpt: /-- \[spqr::v1::unchunked::send\_ek::{spqr::v1::unchunked::send\_ek::KeysUnsampled}::new\]: Source: 'src/v1/unchunked/send\_ek.rs', lines 76:4-81:5 Visibility: public -/

No recorded comments or reviews.

### Item 687

**[Issue #687](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/687) — specify and verify \`spqr::v1::unchunked::send\_ek::{spqr::v1::unchunked::send\_ek::KeysUnsampled}::send\_header\` in 'src/v1/unchunked/send\_ek.rs'**

Status: closed. Opened: 2026-10-19. Author: truonghoangle.

Body excerpt: /-- \[spqr::v1::unchunked::send\_ek::{spqr::v1::unchunked::send\_ek::KeysUnsampled}::send\_header\]: Source: 'src/v1/unchunked/send\_ek.rs', lines 84:4-100:5 Visibility: public -/

No recorded comments or reviews.

### Item 688

**[Issue #688](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/688) — specify and verify \`spqr::v1::unchunked::send\_ek::{spqr::v1::unchunked::send\_ek::EkSentCt1Received}::recv\_ct2\` in \`src/v1/unchunked/send\_ek.rs\`**

Status: open. Opened: 2026-10-19. Author: truonghoangle.

Body excerpt: /-- \[spqr::v1::unchunked::send\_ek::{spqr::v1::unchunked::send\_ek::EkSentCt1Received}::recv\_ct2\]: Source: 'src/v1/unchunked/send\_ek.rs', lines 139:4-172:5 Visibility: public -/

No recorded comments or reviews.

### Item 689

**[Issue #689](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/689) — Specify and verify \`spqr::v1::unchunked::send\_ek::{spqr::v1::unchunked::send\_ek::EkSent}::recv\_ct1\` in \`src/v1/unchunked/send\_ek.rs\`**

Status: closed. Opened: 2026-10-19. Author: truonghoangle.

Body excerpt: /-- \[spqr::v1::unchunked::send\_ek::{spqr::v1::unchunked::send\_ek::EkSent}::recv\_ct1\]: Source: 'src/v1/unchunked/send\_ek.rs', lines 121:4-133:5 Visibility: public -/

No recorded comments or reviews.

### Item 690

**[Issue #690](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/690) — Specify and verify \`spqr::v1::unchunked::send\_ek::{spqr::v1::unchunked::send\_ek::HeaderSent}::send\_ek\` in 'src/v1/unchunked/send\_ek.rs'**

Status: open. Opened: 2026-10-19. Author: truonghoangle.

Body excerpt: /-- \[spqr::v1::unchunked::send\_ek::{spqr::v1::unchunked::send\_ek::HeaderSent}::send\_ek\]: Source: 'src/v1/unchunked/send\_ek.rs', lines 106:4-115:5 Visibility: public -/

No recorded comments or reviews.

### Item 691

**[PR #691](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/691) — specify and verify : \`spqr::v1::unchunked::send\_ct::{spqr::v1::unchunked::send\_ct::Ct2Sent}::recv\_next\_epoch\` in 'src/v1/unchunked/send\_ct.rs'**

Status: merged. Opened: 2026-10-20. Author: truonghoangle.

Body excerpt: This PR specifies and verifies : \`spqr::v1::unchunked::send\_ct::{spqr::v1::unchunked::send\_ct::Ct2Sent}::recv\_next\_epoch\` in 'src/v1/unchunked/send\_ct.rs' closes #628

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/691#pullrequestreview-5581147841) — Zhang-Liao (2026-10-20): (No text.)

### Item 692

**[PR #692](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/692) — specify and verify \`spqr::v1::unchunked::send\_ek::{spqr::v1::unchunked::send\_ek::KeysUnsampled}::new\` in \`src/v1/unchunked/send\_ek.rs\`**

Status: merged. Opened: 2026-10-20. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::v1::unchunked::send\_ek::{spqr::v1::unchunked::send\_ek::KeysUnsampled}::new\` in \`src/v1/unchunked/send\_ek.rs\` closes #686

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/692#pullrequestreview-5596692372) — MarkusFerdinandDablander (2026-10-21): (No text.)
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/692#issuecomment-6311194711) — MarkusFerdinandDablander (2026-10-21): Well done!

### Item 693

**[Issue #693](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/693) — Verify \`src/v1/chunked/send\_ct.rs\`**

Status: open. Opened: 2026-10-20. Author: truonghoangle.

Body excerpt: (No text.)

No recorded comments or reviews.

### Item 694

**[Issue #694](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/694) — Verify and specify \`spqr::v1::chunked::send\_ct::{spqr::v1::chunked::send\_ct::NoHeaderReceived}::new\` in \`src/v1/chunked/send\_ct.rs\`**

Status: closed. Opened: 2026-10-20. Author: truonghoangle.

Body excerpt: /-- \[spqr::v1::chunked::send\_ct::{spqr::v1::chunked::send\_ct::NoHeaderReceived}::new\]: Source: 'src/v1/chunked/send\_ct.rs', lines 71:4-79:5 Visibility: public -/

No recorded comments or reviews.

### Item 695

**[Issue #695](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/695) — Specify and verify \`spqr::v1::chunked::send\_ct::{spqr::v1::chunked::send\_ct::Ct2Sampled}::epoch\` in \`src/v1/chunked/send\_ct.rs\`**

Status: closed. Opened: 2026-10-20. Author: truonghoangle.

Body excerpt: /-- \[spqr::v1::chunked::send\_ct::{spqr::v1::chunked::send\_ct::Ct2Sampled}::epoch\]: Source: 'src/v1/chunked/send\_ct.rs', lines 303:4-305:5 Visibility: public -/

No recorded comments or reviews.

### Item 696

**[Issue #696](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/696) — Specify and verify \`spqr::v1::chunked::send\_ct::{spqr::v1::chunked::send\_ct::Ct2Sampled}::send\_ct2\_chunk\` in \`src/v1/chunked/send\_ct.rs\`**

Status: open. Opened: 2026-10-20. Author: truonghoangle.

Body excerpt: /-- \[spqr::v1::chunked::send\_ct::{spqr::v1::chunked::send\_ct::Ct2Sampled}::send\_ct2\_chunk\]: Source: 'src/v1/chunked/send\_ct.rs', lines 288:4-295:5 Visibility: public -/

No recorded comments or reviews.

### Item 697

**[Issue #697](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/697) — Specify and verify \`spqr::v1::chunked::send\_ct::{spqr::v1::chunked::send\_ct::Ct1Acknowledged}::epoch\` in \`src/v1/chunked/send\_ct.rs\`**

Status: open. Opened: 2026-10-20. Author: truonghoangle.

Body excerpt: /-- \[spqr::v1::chunked::send\_ct::{spqr::v1::chunked::send\_ct::Ct1Acknowledged}::epoch\]: Source: 'src/v1/chunked/send\_ct.rs', lines 281:4-283:5 Visibility: public -/

No recorded comments or reviews.

### Item 698

**[Issue #698](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/698) — Specify and verify \`spqr::v1::chunked::send\_ct::{spqr::v1::chunked::send\_ct::EkReceivedCt1Sampled}::epoch\` in \`src/v1/chunked/send\_ct.rs\`**

Status: open. Opened: 2026-10-20. Author: truonghoangle.

Body excerpt: /-- \[spqr::v1::chunked::send\_ct::{spqr::v1::chunked::send\_ct::EkReceivedCt1Sampled}::epoch\]: Source: 'src/v1/chunked/send\_ct.rs', lines 245:4-247:5 Visibility: public -/

No recorded comments or reviews.

### Item 699

**[Issue #699](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/699) — Specify and verify \`spqr::v1::chunked::send\_ct::{spqr::v1::chunked::send\_ct::EkReceivedCt1Sampled}::send\_ct1\_chunk\` in \`src/v1/chunked/send\_ct.rs\`**

Status: open. Opened: 2026-10-20. Author: truonghoangle.

Body excerpt: /-- \[spqr::v1::chunked::send\_ct::{spqr::v1::chunked::send\_ct::EkReceivedCt1Sampled}::send\_ct1\_chunk\]: Source: 'src/v1/chunked/send\_ct.rs', lines 226:4-233:5 Visibility: public -/

No recorded comments or reviews.

### Item 700

**[Issue #700](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/700) — Specify and verify \`spqr::v1::chunked::send\_ct::{spqr::v1::chunked::send\_ct::Ct1Sampled}::epoch\` in \`src/v1/chunked/send\_ct.rs\`**

Status: open. Opened: 2026-10-20. Author: truonghoangle.

Body excerpt: /-- \[spqr::v1::chunked::send\_ct::{spqr::v1::chunked::send\_ct::Ct1Sampled}::epoch\]: Source: 'src/v1/chunked/send\_ct.rs', lines 219:4-221:5 Visibility: public -/

No recorded comments or reviews.

### Item 701

**[Issue #701](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/701) — Specify and verify \`spqr::v1::chunked::send\_ct::{spqr::v1::chunked::send\_ct::Ct1Sampled}::send\_ct1\_chunk\` in \`src/v1/chunked/send\_ct.rs\`**

Status: open. Opened: 2026-10-20. Author: truonghoangle.

Body excerpt: /-- \[spqr::v1::chunked::send\_ct::{spqr::v1::chunked::send\_ct::Ct1Sampled}::send\_ct1\_chunk\]: Source: 'src/v1/chunked/send\_ct.rs', lines 202:4-217:5 Visibility: public -/

No recorded comments or reviews.

### Item 702

**[Issue #702](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/702) — Specify and verify \`spqr::v1::unchunked::send\_ct::{spqr::v1::unchunked::send\_ct::HeaderReceived}::send\_ct1\` in \`src/v1/unchunked/send\_ct.rs\`**

Status: open. Opened: 2026-10-20. Author: truonghoangle.

Body excerpt: /-- \[spqr::v1::unchunked::send\_ct::{spqr::v1::unchunked::send\_ct::HeaderReceived}::send\_ct1\]: Source: 'src/v1/unchunked/send\_ct.rs', lines 120:4-148:5 Visibility: public -/

No recorded comments or reviews.

### Item 703

**[Issue #703](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/703) — Specify and verify \`spqr::v1::chunked::send\_ct::{spqr::v1::chunked::send\_ct::HeaderReceived}::send\_ct1\_chunk\` in \`src/v1/chunked/send\_ct.rs\`**

Status: open. Opened: 2026-10-20. Author: truonghoangle.

Body excerpt: /-- \[spqr::v1::chunked::send\_ct::{spqr::v1::chunked::send\_ct::HeaderReceived}::send\_ct1\_chunk\]: Source: 'src/v1/chunked/send\_ct.rs', lines 123:4-142:5 Visibility: public -/

No recorded comments or reviews.

### Item 704

**[Issue #704](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/704) — Specify and verify \`spqr::v1::chunked::send\_ct::{spqr::v1::chunked::send\_ct::NoHeaderReceived}::epoch\` in \`src/v1/chunked/send\_ct.rs\`**

Status: open. Opened: 2026-10-20. Author: truonghoangle.

Body excerpt: /-- \[spqr::v1::chunked::send\_ct::{spqr::v1::chunked::send\_ct::NoHeaderReceived}::epoch\]: Source: 'src/v1/chunked/send\_ct.rs', lines 112:4-114:5 Visibility: public -/

No recorded comments or reviews.

### Item 705

**[Issue #705](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/705) — Specify and verify \`spqr::v1::chunked::send\_ct::{spqr::v1::chunked::send\_ct::Ct2Sampled}::recv\_next\_epoch\` in \`src/v1/chunked/send\_ct.rs\`**

Status: open. Opened: 2026-10-20. Author: truonghoangle.

Body excerpt: /-- \[spqr::v1::chunked::send\_ct::{spqr::v1::chunked::send\_ct::Ct2Sampled}::recv\_next\_epoch\]: Source: 'src/v1/chunked/send\_ct.rs', lines 298:4-301:5 Visibility: public -/

No recorded comments or reviews.

### Item 706

**[Issue #706](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/706) — Specify and verify \`spqr::v1::chunked::send\_ct::send\_ct2\_encoder\` in \`src/v1/chunked/send\_ct.rs\`**

Status: open. Opened: 2026-10-20. Author: truonghoangle.

Body excerpt: /-- \[spqr::v1::chunked::send\_ct::send\_ct2\_encoder\]: Source: 'src/v1/chunked/send\_ct.rs', lines 159:0-163:1 -/

No recorded comments or reviews.

### Item 707

**[Issue #707](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/707) — Specify and verify \`spqr::v1::chunked::send\_ct::{spqr::v1::chunked::send\_ct::Ct1Acknowledged}::recv\_ek\_chunk\` in \`src/v1/chunked/send\_ct.rs\`**

Status: open. Opened: 2026-10-20. Author: truonghoangle.

Body excerpt: /-- \[spqr::v1::chunked::send\_ct::{spqr::v1::chunked::send\_ct::Ct1Acknowledged}::recv\_ek\_chunk\]: Source: 'src/v1/chunked/send\_ct.rs', lines 259:4-279:5 Visibility: public -/

No recorded comments or reviews.

### Item 708

**[Issue #708](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/708) — Specify and verify \`spqr::v1::chunked::send\_ct::{spqr::v1::chunked::send\_ct::EkReceivedCt1Sampled}::recv\_ct1\_ack\` in \`src/v1/chunked/send\_ct.rs\`**

Status: open. Opened: 2026-10-20. Author: truonghoangle.

Body excerpt: /-- \[spqr::v1::chunked::send\_ct::{spqr::v1::chunked::send\_ct::EkReceivedCt1Sampled}::recv\_ct1\_ack\]: Source: 'src/v1/chunked/send\_ct.rs', lines 236:4-243:5 Visibility: public -/

No recorded comments or reviews.

### Item 709

**[Issue #709](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/709) — Specify and verify \`spqr::v1::chunked::send\_ct::{spqr::v1::chunked::send\_ct::Ct1Sampled}::recv\_ek\_chunk\` in \`src/v1/chunked/send\_ct.rs\`**

Status: open. Opened: 2026-10-20. Author: truonghoangle.

Body excerpt: /-- \[spqr::v1::chunked::send\_ct::{spqr::v1::chunked::send\_ct::Ct1Sampled}::recv\_ek\_chunk\]: Source: 'src/v1/chunked/send\_ct.rs', lines 168:4-200:5 Visibility: public -/

No recorded comments or reviews.

### Item 710

**[Issue #710](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/710) — Specify and verify \`spqr::v1::chunked::send\_ct::{spqr::v1::chunked::send\_ct::NoHeaderReceived}::recv\_hdr\_chunk\` in \`src/v1/chunked/send\_ct.rs\`**

Status: open. Opened: 2026-10-20. Author: truonghoangle.

Body excerpt: /-- \[spqr::v1::chunked::send\_ct::{spqr::v1::chunked::send\_ct::NoHeaderReceived}::recv\_hdr\_chunk\]: Source: 'src/v1/chunked/send\_ct.rs', lines 82:4-110:5 Visibility: public -/

No recorded comments or reviews.

### Item 711

**[PR #711](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/711) — Harmonise \`spqr::v1::unchunked::send\_ct::serialize::Ct1SentEkReceived::{into\_pb, from\_pb}\` via functional models and prove round trips**

Status: merged. Opened: 2026-10-20. Author: MarkusFerdinandDablander.

Body excerpt: This PR adds \`FunctionalModels.lean\` for the unchunked \`Ct1SentEkReceived\` state, proves round trips, and pins the existing \`into\_pb\` and \`from\_pb\` spec theorems to the functional models, following the architecture discussed in #568. Closes #588

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/711#pullrequestreview-5585602228) — truonghoangle (2026-10-20): (No text.)

### Item 712

**[PR #712](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/712) — Specify and verify \`spqr::v1::unchunked::send\_ct::{spqr::v1::unchunked::send\_ct::HeaderReceived}::send\_ct1\` in \`src/v1/unchunked/send\_ct.rs\`**

Status: merged. Opened: 2026-10-20. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::v1::unchunked::send\_ct::{spqr::v1::unchunked::send\_ct::HeaderReceived}::send\_ct1\` in \`src/v1/unchunked/send\_ct.rs\` closes #627

Discussion and review record:

- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/712#pullrequestreview-5596505974) — Zhang-Liao (2026-10-21): \*\*AI review\*\* — reviewed commit \`62fdf83aba410211be79b979568bfc896e3af550\`. I found no substantive specification correctness issue. The specification captures the ciphertext, serialized encapsulation state, derived epoch secret, authenticator update, and preserved state fields. There are three guideline issues worth addressing before merging: 1. \*\*File placement:\*\* …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/712#issuecomment-6315362756) — truonghoangle (2026-10-21): ## PR Review Follow-up ### 1. File Placement — Resolved Moved \`SendCt1.lean\` from \`Spqr/Specs/V1/Unchunked/SendCt/Serialize/HeaderReceived/\` to \`Spqr/Specs/V1/Unchunked/SendCt/HeaderReceived/\` to align the spec directory structure with the Rust source location in \`send\_ct.rs\`. ### 2. Missing \`@\[step\]\` Attribute — Resolved Added \`@\[step\]\` to \`send\_ct1\_spec\`. The manual application of \`encaps1\_spec\` within the proof …
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/712#pullrequestreview-5600187014) — Zhang-Liao (2026-10-21): (No text.)

### Item 713

**[PR #713](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/713) — specify and verify \`spqr::v1::unchunked::send\_ek::{spqr::v1::unchunked::send\_ek::KeysUnsampled}::send\_header\` in \`src/v1/unchunked/send\_ek.rs\`**

Status: merged. Opened: 2026-10-21. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::v1::unchunked::send\_ek::{spqr::v1::unchunked::send\_ek::KeysUnsampled}::send\_header\` in \`src/v1/unchunked/send\_ek.rs\` and moved \`new.lean\` from \`Spqr/Specs/V1/Unchunked/SendEk/Serialize/KeysUnsampled/\` to \`Spqr/Specs/V1/Unchunked/SendEk/KeysUnsampled/\` to align the spec directory structure with the Rust source location in send\_ek.rs. closes #687

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/713#pullrequestreview-5608533855) — Zhang-Liao (2026-10-22): (No text.)

### Item 714

**[PR #714](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/714) — Verify and specify \`spqr::v1::chunked::send\_ct::{spqr::v1::chunked::send\_ct::NoHeaderReceived}::new\` in \`src/v1/chunked/send\_ct.rs\`**

Status: merged. Opened: 2026-10-21. Author: truonghoangle.

Body excerpt: This PR verifies and specifies \`spqr::v1::chunked::send\_ct::{spqr::v1::chunked::send\_ct::NoHeaderReceived}::new\` in \`src/v1/chunked/send\_ct.rs\` and change \`opaque\` of \`libcrux\_ml\_kem.mlkem768.incremental.pk1\_len\` by the definition and spec theorem closes #694

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/714#issuecomment-6331000925) — Zhang-Liao (2026-10-22): &gt; \*\*⚠️ AI-generated review (Claude Fable 5.1, run by @liao).\*\* @truonghoangle, please note this review was written by an AI model, not by a human reviewer. Treat it as a checklist, and verify any claim before acting on it. A human sign-off is still required. \*\*Summary:\*\* The spec and proof for \`NoHeaderReceived::new\` are correct and the build is clean. The one thing that needs a maintainer decision is the change of …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/714#issuecomment-6332697952) — truonghoangle (2026-10-22): @Zhang-Liao basis on comments of AI, by change \`pk1\_len\` changed from \`noncomputable opaque\` to a concrete \`def\`, in \`Spqr/Specs/Lib/InitInner.lean \`(init\_inner\_spec\_v1\_b2a and the other B2A spec) and \`Spqr/Specs/Lib/InitialState.lean\` I removed \`h\_pk1 : libcrux\_ml\_kem.mlkem768.incremental.pk1\_len = ok 64#usize\` as a hypothesis.
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/714#pullrequestreview-5610607995) — Zhang-Liao (2026-10-22): (No text.)

### Item 715

**[PR #715](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/715) — Specify and verify \`spqr::v1::unchunked::send\_ct::{spqr::v1::unchunked::send\_ct::Ct1SentEkReceived}::send\_ct2\` in \`src/v1/unchunked/send\_ct.rs\`**

Status: merged. Opened: 2026-10-21. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::v1::unchunked::send\_ct::{spqr::v1::unchunked::send\_ct::Ct1SentEkReceived}::send\_ct2\` in \`src/v1/unchunked/send\_ct.rs\` closes #629

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/715#issuecomment-6330796815) — Zhang-Liao (2026-10-22): &gt; \*\*⚠️ AI-generated review (Claude Fable 5.1, run by @liao).\*\* This is an automated review, not a human sign-off. Please treat it as a checklist for the human reviewer, and verify any claim before acting on it. \*\*Summary:\*\* The spec and proof look correct and the build is clean, but the spec theorem is missing the \`@\[step\]\` attribute. Requesting that one change; everything else below is non-blocking. ### Blocking - …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/715#issuecomment-6332923742) — truonghoangle (2026-10-22): @Zhang-Liao Basis comments of AI, I tagged \`@\[step\]\` to \`send\_ct2\_spec\`.
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/715#pullrequestreview-5610368369) — Zhang-Liao (2026-10-22): (No text.)

### Item 716

**[PR #716](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/716) — specify and verify : \`spqr::v1::unchunked::send\_ct::{spqr::v1::unchunked::send\_ct::Ct1Sent}::recv\_ek\` in \`src/v1/unchunked/send\_ct.rs\`**

Status: merged. Opened: 2026-10-21. Author: truonghoangle.

Body excerpt: This PR specifies and verifies : \`spqr::v1::unchunked::send\_ct::{spqr::v1::unchunked::send\_ct::Ct1Sent}::recv\_ek\` in \`src/v1/unchunked/send\_ct.rs\` closes #630

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/716#pullrequestreview-5608335051) — Zhang-Liao (2026-10-22): (No text.)

### Item 717

**[PR #717](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/717) — Specify and verify \`spqr::v1::unchunked::send\_ct::{spqr::v1::unchunked::send\_ct::NoHeaderReceived}::recv\_header\` in \`src/v1/unchunked/send\_ct.rs\`**

Status: merged. Opened: 2026-10-22. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::v1::unchunked::send\_ct::{spqr::v1::unchunked::send\_ct::NoHeaderReceived}::recv\_header\` in \`src/v1/unchunked/send\_ct.rs\` and changed place of file \`New.lean\` closes #631

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/717#pullrequestreview-5623271694) — Zhang-Liao (2026-10-23): (No text.)

### Item 718

**[PR #718](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/718) — Convert 8 \`decide +kernel\` proofs to \`native\_decide\`**

Status: merged. Opened: 2026-10-22. Author: oliver-butterley.

Body excerpt: Since merging #661 the Radar bench has been failing. This PR converts the 8 \`decide +kernel\` proofs to \`native\_decide\`. This is a temporary solution, the eventual solution is postponed to issue #721.

Discussion and review record:

- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/718#issuecomment-6338514056) — oliver-butterley (2026-10-22): !radar
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/718#issuecomment-6338515995) — baif-radar (2026-10-22): Benchmark results for 9a99c9b07d9f17d0c2fd1a4d078e18f203805645 against 2ab18fd7ed5890c79e80935edcb0ccdae36f446f are in. There are significant results. @oliver-butterley \*\*Large changes (9✅, 3🟥)\*\* - ✅ \`build/module/Spqr.Crypto.Fips203.NTT.InvKernel0//instructions\`: \*\*-79.0G\*\* (\*\*-89.19%\*\*) - ✅ \`build/module/Spqr.Crypto.Fips203.NTT.InvKernel1//instructions\`: \*\*-83.4G\*\* (\*\*-88.16%\*\*) - ✅ …
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/718#issuecomment-6341121076) — oliver-butterley (2026-10-22): Here Radar signals some problems but I believe this is not real, instead it is due to Radar trying to compare the successful build with one that failed.
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/718#pullrequestreview-5614404329) — Kukovec (2026-10-22): (No text.)

### Item 719

**[PR #719](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/719) — specify and verify \`spqr::v1::unchunked::send\_ek::{spqr::v1::unchunked::send\_ek::EkSentCt1Received}::recv\_ct2\` in \`src/v1/unchunked/send\_ek.rs\`**

Status: open. Opened: 2026-10-22. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::v1::unchunked::send\_ek::{spqr::v1::unchunked::send\_ek::EkSentCt1Received}::recv\_ct2\` in \`src/v1/unchunked/send\_ek.rs\` closes #688

Discussion and review record:

- [review DISMISSED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/719#pullrequestreview-5623330319) — Zhang-Liao (2026-10-23): (No text.)
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/719#discussion_r4357028725) — Zhang-Liao (2026-10-23; Spqr/Specs/V1/Unchunked/SendEk/EkSentCt1Received/RecvCt2.lean:14): This import is unused: the file compiles unchanged with this line removed (\`MACSIZE\` is already reachable through \`SrcTranslated.Funs\` / the public \`VerifyCt\` import). Please drop it.
- [inline](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/719#discussion_r4357028731) — Zhang-Liao (2026-10-23; Spqr/Specs/V1/Unchunked/SendEk/EkSentCt1Received/RecvCt2.lean:18): Same here: \`Spqr.Auxiliary.Aeneas.Vec\` is already imported transitively, and the file compiles with this line removed. Please drop it.
- [review COMMENTED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/719#pullrequestreview-5625041526) — Zhang-Liao (2026-10-23): Build, linter, and axiom check all pass; no new axioms beyond those inherited from \`decaps\_spec\`, \`update\_spec\`, \`verify\_ct\_spec\`, and \`hkdf\_to\_vec\_spec\`. One small cleanup below.
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/719#issuecomment-6360523494) — oliver-butterley (2026-10-23): !radar
- [conversation](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/719#issuecomment-6360531195) — baif-radar (2026-10-23): Benchmark results for b5b2c37281cc5da218363eed04f16b0a86f40b34 against fba31c7c1a460628084accb09fd139c05ee28dac are in. No significant results found. @oliver-butterley \*\*Small changes (6🟥)\*\* - 🟥 \`build/module/HeaderLinter.Basic//instructions\`: \*\*+328.4M\*\* (\*\*+5.27%\*\*) - 🟥 \`build/module/Spqr.Auxiliary.Aeneas.Result//instructions\`: \*\*+342.0M\*\* (\*\*+5.37%\*\*) - 🟥 \`build/module/Spqr.Auxiliary.Aeneas.Slice//instructions\`: …

### Item 720

**[PR #720](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/720) — Specify and verify \`spqr::v1::unchunked::send\_ek::{spqr::v1::unchunked::send\_ek::EkSent}::recv\_ct1\` in \`src/v1/unchunked/send\_ek.rs\`**

Status: merged. Opened: 2026-10-22. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::v1::unchunked::send\_ek::{spqr::v1::unchunked::send\_ek::EkSent}::recv\_ct1\` in \`src/v1/unchunked/send\_ek.rs\` closes #689

Discussion and review record:

- [review DISMISSED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/720#pullrequestreview-5623504664) — Zhang-Liao (2026-10-23): (No text.)
- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/720#pullrequestreview-5625399393) — Zhang-Liao (2026-10-23): (No text.)

### Item 721

**[Issue #721](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/721) — Remove 8 \`native\_decide\` proofs**

Status: open. Opened: 2026-10-22. Author: oliver-butterley.

Body excerpt: Previously there were 8 proofs using \`decide +kernel\` but the memory usage due to this caused significant problems. As such they were temporarily swapped for \`native\_decide\` proofs. We need to: - add symbolic proofs of these facts, - \_or\_ decide that we are happy with \`native\_decide\` despite the trust issues, - \_or\_ decide that we won't do the round trip properties which require this.

No recorded comments or reviews.

### Item 722

**[PR #722](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/722) — Specify and verify \`spqr::v1::chunked::send\_ct::{spqr::v1::chunked::send\_ct::Ct2Sampled}::epoch\` in \`src/v1/chunked/send\_ct.rs\`**

Status: merged. Opened: 2026-10-22. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::v1::chunked::send\_ct::{spqr::v1::chunked::send\_ct::Ct2Sampled}::epoch\` in \`src/v1/chunked/send\_ct.rs\` closes #695

Discussion and review record:

- [review APPROVED](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/722#pullrequestreview-5623599103) — Zhang-Liao (2026-10-23): (No text.)

### Item 723

**[PR #723](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/723) — Specify and verify \`spqr::v1::chunked::send\_ct::{spqr::v1::chunked::send\_ct::Ct2Sampled}::send\_ct2\_chunk\` in \`src/v1/chunked/send\_ct.rs\`**

Status: open. Opened: 2026-10-22. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::v1::chunked::send\_ct::{spqr::v1::chunked::send\_ct::Ct2Sampled}::send\_ct2\_chunk\` in \`src/v1/chunked/send\_ct.rs\` closes #696

No recorded comments or reviews.

### Item 724

**[PR #724](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/724) — Specify and verify spqr::v1::chunked::send\_ct::{spqr::v1::chunked::send\_ct::Ct1Acknowledged}::epoch in src/v1/chunked/send\_ct.rs**

Status: open. Opened: 2026-10-22. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::v1::chunked::send\_ct::{spqr::v1::chunked::send\_ct::Ct1Acknowledged}::epoch\` in \`src/v1/chunked/send\_ct.rs\` closes #697

No recorded comments or reviews.

### Item 725

**[PR #725](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/725) — Specify and verify \`spqr::v1::chunked::send\_ct::{spqr::v1::chunked::send\_ct::EkReceivedCt1Sampled}::epoch\` in \`src/v1/chunked/send\_ct.rs\`**

Status: open. Opened: 2026-10-23. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::v1::chunked::send\_ct::{spqr::v1::chunked::send\_ct::EkReceivedCt1Sampled}::epoch\` in \`src/v1/chunked/send\_ct.rs\` closes #698

No recorded comments or reviews.

### Item 726

**[PR #726](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/726) — Specify and verify \`spqr::v1::chunked::send\_ct::{spqr::v1::chunked::send\_ct::Ct1Sampled}::epoch\` in \`src/v1/chunked/send\_ct.rs\`**

Status: open. Opened: 2026-10-23. Author: truonghoangle.

Body excerpt: This PR specifies and verifies \`spqr::v1::chunked::send\_ct::{spqr::v1::chunked::send\_ct::Ct1Sampled}::epoch\` in \`src/v1/chunked/send\_ct.rs\` closes #700

No recorded comments or reviews.

## Commit comments

- [184298665](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/commit/4d9292fc42185838d96c8d2bd7cdfdb2d9b41edd#r184298665) — astefano (2026-05-05): Lables -&gt; Labels
- [184298781](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/commit/4d9292fc42185838d96c8d2bd7cdfdb2d9b41edd#r184298781) — astefano (2026-05-05): what's wrong with markdown headings in PRs?
