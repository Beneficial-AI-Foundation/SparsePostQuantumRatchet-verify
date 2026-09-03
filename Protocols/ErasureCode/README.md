# SPQR erasure-code verification

## What is proved

`concreteSpqrErasureCode_correct` connects the extracted SPQR encoder and decoder to the
Reed–Solomon model in this directory. For an allowed message size `k`, an honest set of encoded
chunks at distinct positions decodes to the original message when it contains at least `k`
chunks, and decoding returns `none` when it contains fewer than `k` chunks.

The proof is split at two correspondence lemmas:

- `encode_toModel` shows that the extracted encoder produces the model's chunk at each index.
- `decode_toModel` shows that the extracted decoder agrees with the model on honest chunk sets.

This is a functional-correctness result. It does not claim security, cover streaming decode, or
define an `ErasureCodePayload` instance.

The theorem requires `k ∈ {1, 3, 5, 30, 34, 36}`. These are the point counts supported by the
precomputed polynomial tables used by the Rust implementation; a theorem for arbitrary `k`
would not describe the shipped code.

## Assumptions and axiom closure

Rust's `decoded_message` function is deliberately opaque to extraction; see
[issue #103](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/103).
`Contract.lean` therefore states two assumptions about that real function:

- `decoded_message_spec_short`: if any one of the 16 point stores is short, decoding returns
  `none`.
- `decoded_message_spec_complete`: complete, sorted stores containing points on suitably
  low-degree polynomials decode to the bytes of those polynomial evaluations.

The checked closure of `concreteSpqrErasureCode_correct` contains:

- `propext`, `Classical.choice`, and `Quot.sound`: Lean's standard logical axioms;
- `decoded_message_spec_short` and `decoded_message_spec_complete`: the two assumptions above;
- `encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.decoded_message`: the extraction
  opaque;
- <code>sorr&#121;Ax</code>: inherited through the pre-existing named assumption
  `Spqr.Aeneas.collect_default_bridge`. Aeneas currently mistranslates the relevant mapped
  iterator ([aeneas#1043](https://github.com/AeneasVerif/aeneas/issues/1043)); project
  [issue #409](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/409)
  tracks removing this assumption;
- `Aeneas.Std.core.fmt.Formatter` and the two `RangeFull.get_unchecked` declarations: opaque
  primitives in the extracted support library;
- `PolyEncoder.chunk_at._native.decide.ax_1` and
  `PolyEncoder.point_at_loop.body._native.decide.ax_1`: pre-existing generated certificates
  that two fixed panic-message strings fit in `U32`.

The bridge adds no proof placeholders or uses of `native_decide`.

To recheck the closure, save the following as `/tmp/ErasureCodeAxioms.lean` and run
`lake env lean /tmp/ErasureCodeAxioms.lean` from the repository root:

```lean
import Protocols

#print axioms Protocols.ErasureCode.concreteSpqrErasureCode_correct
#print axioms Protocols.ErasureCode.encode_toModel
#print axioms Protocols.ErasureCode.decode_toModel
#print axioms Protocols.ErasureCode.decoded_message_spec_short
#print axioms Protocols.ErasureCode.decoded_message_spec_complete
#print axioms spqr.encoding.polynomial.PolyEncoder.chunk_at_spec_points
```

## Model provenance

The five files under `Model/` are non-canonical copies from
`Beneficial-AI-Foundation/secure-messaging` at commit `2144e35`. Their only local differences
are the provenance header and imports rewritten to the `Protocols.ErasureCode.Model` namespace.
The canonical files remain in `secure-messaging`.

To recheck a vendored file, run this in a checkout of `secure-messaging` and compare the output
with the corresponding file under `Protocols/ErasureCode/Model/`, allowing only those two
mechanical differences:

```sh
git show 2144e35:SecureMessaging/ErasureCode/<path>
```
