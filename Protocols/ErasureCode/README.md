# SPQR erasure-code verification

This directory connects the extracted SPQR polynomial encoder and decoder to a Reed–Solomon model
in Lean. The final theorem, [`concreteSpqrErasureCode_correct`](Correct.lean), applies when
`k ∈ {1, 3, 5, 30, 34, 36}`. For honest chunks at distinct indices, it proves that:

- at least `k` chunks recover the original message;
- fewer than `k` chunks return `none`.

These six values are the point counts supported by the encoder's precomputed polynomial tables.
The broader `concreteSpqrErasureCode` constructor packages encode and decode operations for every
positive `k ≤ 2^16`; `Correct` is a separate property. Its encoder maps extracted construction or
chunk-lookup failures to `default` so that the operation is total.

The theorem is the deterministic extensional fragment of Definition A.6 in
[*How to Compare Bandwidth Constrained Two-Party Secure Messaging Protocols*](https://eprint.iacr.org/2025/2267.pdf).
Recovery from at least `k` honest chunks strengthens the paper's exactly-`k` clause. The result
makes no computability, polynomial-time or PPT, asymptotic-cost, or protocol-security claim.

## How the proof works

1. [`encode_toModel`](Correctness/Encode.lean) proves that the extracted encoder returns the model
   chunk at each index for the six supported table sizes.
2. [`decode_toModel`](Correctness/Decode.lean) starts a fresh decoder, folds over honest chunks at
   distinct indices, and proves that its output equals the model decoder's output.
3. [`modelEC_correct`](Correctness/Params.lean) supplies the Reed–Solomon result. The final theorem
   rewrites both concrete operations to the model and applies that result.

The decoder equation covers this fresh-decoder fold and its output. It does not equate persistent
decoder histories produced by different insertion orders, arbitrary input sets, or streaming
states.

## Assumptions and trust

The extracted `decoded_message` function is opaque. [`Contract.lean`](Contract.lean) states two
assumptions about it and gives their exact hypotheses:

- `decoded_message_spec_short` says that decoding returns `none` when any one of the sixteen stores
  is below its quota. It needs no flag premise.
- `decoded_message_spec_complete` starts with `is_complete = false`. Strictly sorted stores must
  contain enough points on the stated degree-bounded polynomials; decoding then serializes the
  requested evaluations.

The terminal theorem's checked closure contains:

- Lean's standard logical axioms: `propext`, `Classical.choice`, and `Quot.sound`;
- the two decoder contracts and the opaque `decoded_message` definition;
- <code>sorr&#121;Ax</code> from two direct origins: the admitted generated map-iterator `next` in
  [`SrcTranslated/Funs.lean`](../../SrcTranslated/Funs.lean), and
  `Spqr.Aeneas.collect_default_bridge` in
  [`Spqr/Specs/Aeneas/MapCollectBridge.lean`](../../Spqr/Specs/Aeneas/MapCollectBridge.lean);
- the opaque backend type `Aeneas.Std.core.fmt.Formatter`, plus the `RangeFull` extraction
  externals `get_unchecked` and `get_unchecked_mut`;
- two pre-existing encoder native certificates showing that fixed panic strings fit in `U32`:
  `PolyEncoder.chunk_at._native.decide.ax_1` and
  `PolyEncoder.point_at_loop.body._native.decide.ax_1`.

Both decoder contracts remain assumptions. The bridge adds no proof placeholders or uses of
`native_decide`, and a green build cannot validate the assumed contracts. `Contract.lean` also
describes the broader interpolation helper, its machine-size premise, and its helper-only native
certificate, which is outside the terminal theorem's closure and does not discharge either
contract.

## Model provenance

The five files under `Model/` are vendored from the canonical
[`Beneficial-AI-Foundation/secure-messaging`](https://github.com/Beneficial-AI-Foundation/secure-messaging)
repository at immutable commit `2144e3561b3ebf775f973a3c2804a0f8edb77f75`:

- `SecureMessaging/ErasureCode/Defs.lean`
- `SecureMessaging/ErasureCode/ReedSolomon/Construction.lean`
- `SecureMessaging/ErasureCode/ReedSolomon/Correctness.lean`
- `SecureMessaging/ErasureCode/SPQRReedSolomon/Construction.lean`
- `SecureMessaging/ErasureCode/SPQRReedSolomon/Correctness.lean`

Only these local differences are permitted:

1. The header preserves upstream copyright and authorship, names `LICENSE-APACHE`, and records the
   provenance, local adaptation credit, full commit, upstream path, and this README.
2. Imports replace the `SecureMessaging.ErasureCode.*` prefix with
   `Protocols.ErasureCode.Model.*`.

Apart from that import rewrite, every byte from the first import onward matches the pinned source,
including body prose and navigation names. A retained `SecureMessaging.ErasureCode.*` name refers
to the upstream module; its local copy uses the `Protocols.ErasureCode.Model.*` prefix.
