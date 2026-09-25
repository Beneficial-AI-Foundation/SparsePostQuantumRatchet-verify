# SPQR erasure-code verification

In Signal, the public keys and ciphertexts used for post-quantum key agreement are large. To keep
each chat message small, SPQR sends this data in chunks alongside the conversation. Sometimes
some of the chunks do not get to the other end. Nonetheless, we should be able to recover the
whole message once we have enough chunks, without waiting for the particular ones we missed.
[Signal's SPQR post](https://signal.org/blog/spqr/) explains this choice. Here, "message" means
the data we are encoding, such as a public key or a key-agreement ciphertext.

Erasure codes make this possible by adding redundancy: we can produce extra chunks that let us
recover the data even if some chunks are lost. The Reed–Solomon code used here does this through
polynomial interpolation. A line is determined by any two points on it with different x-values.
Likewise, a polynomial of degree less than `k` is determined by its values at any `k` distinct
points. We encode the data as values of a polynomial, send evaluations at different points, and
recover the polynomial once enough arrive. We can then read the original data back from it.
The implementation does this for sixteen polynomials in parallel, packing their evaluations
into each chunk.

## Mapping this to the code

The [Rust encoder and decoder](../../src/encoding/polynomial.rs) are translated into Lean by
Aeneas. `concreteSpqrErasureCode` fills its `encode` and `decode` fields with two wrappers:

- `encodeConcrete` converts the message into bytes, calls `encode_bytes` to prepare the encoder,
  then calls `chunk_at` for a chosen index and reads the returned bytes as a model chunk.
- `decodeConcrete` calls `new` to start an empty decoder, calls `add_chunk` for each received
  chunk, then calls `decoded_message` and reads its result as a model message.

The final `decoded_message` step is opaque in the translation, so its behavior is still assumed,
as described below.

Correctness means that, given enough chunks, decoding recovers exactly the message we encoded.
Here, `k` is the number of 32-byte chunks in the original message, before adding redundancy.
Under the [assumptions below](#assumptions-and-trust), the final theorem,
[`concreteSpqrErasureCode_correct`](Correct.lean), proves that for unmodified chunks from the
same message at distinct indices:

- at least `k` chunks recover the original message;
- fewer than `k` chunks return `none`.

The theorem covers `k ∈ {1, 3, 5, 30, 34, 36}`, the six point counts supported by the encoder's
precomputed polynomial tables. Receiving the same chunk twice does not count as two chunks.

## What we use from functional correctness

The encoder bridge needs two FC results:

- [`encode_bytes_spec`](../../Spqr/Specs/Encoding/Polynomial/PolyEncoder/EncodeBytes.lean)
  proves that preparing the encoder succeeds and stores the original byte pairs in the right
  places. For a message of `32 * k` bytes, each of its sixteen stores holds `k` values.
- [`chunk_at_spec_points`](../../Spqr/Specs/Encoding/Polynomial/PolyEncoder/ChunkAt.lean)
  starts with those stored values. Under its bounds on store lengths and index arithmetic, it
  proves that asking for a chunk succeeds, returns the requested index and 32 bytes, and puts the
  corresponding polynomial evaluation in each byte pair. This covers both reading a stored
  value and computing an extra chunk by interpolation.

The first result connects the stored values to our message; the second connects those values to
the chunk we get back. The mathematical lemmas then identify these polynomials with the model's.

On the decoder side, [`new_spec`](../../Spqr/Specs/Encoding/Polynomial/PolyDecoder/New.lean)
gives us sixteen empty stores, the right number of points needed, and `is_complete = false`.
In [`Decode.lean`](Correctness/Decode.lean), we prove `add_chunk_decoderInv_spec` directly over
the translated `add_chunk` loop. For honest chunks at distinct indices, it shows that stored
points stay sorted, lie on the right polynomials, and reach the required count once enough
chunks arrive.

That proof reuses smaller FC results: `necessary_points_spec` computes each store's quota,
`Pt.Insts.CoreCmpOrd.cmp_spec` orders points by their indices, and `GF16.new_value_spec` preserves
the values read from bytes. It also uses Aeneas' array and iterator results and the sorted-set
model in [`FunsExternal.lean`](../../SrcTranslated/FunsExternal.lean). The final readout uses the
two assumed `decoded_message` contracts below.

## How the proof works

1. [`encode_toModel`](Correctness/Encode.lean) proves that the extracted encoder returns the model
   chunk at each index for the six supported table sizes.
2. [`decode_toModel`](Correctness/Decode.lean) proves that starting a fresh decoder and adding
   honest chunks at distinct indices gives the same output as the model decoder.
3. [`modelEC_correct`](Correctness/Params.lean) proves recovery for the mathematical Reed–Solomon
   model. Since our encode and decode operations agree with that model, the final theorem gives
   us the same recovery guarantee for those operations, subject to the stated assumptions.

The decoder equation covers this fresh-decoder fold and its output. It does not equate persistent
decoder histories produced by different insertion orders, arbitrary input sets, or streaming
states.

The broader `concreteSpqrErasureCode` constructor packages encode and decode operations for every
positive `k ≤ 2^16`; `Correct` is a separate property. Its encoder maps extracted construction or
chunk-lookup failures to `default` so that the operation is total.

The theorem is the deterministic extensional fragment of Definition A.6 in
[*How to Compare Bandwidth Constrained Two-Party Secure Messaging Protocols*](https://eprint.iacr.org/2025/2267.pdf).
Recovery from at least `k` honest chunks strengthens the paper's exactly-`k` clause. The result
makes no computability, polynomial-time or PPT, asymptotic-cost, or protocol-security claim.

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
