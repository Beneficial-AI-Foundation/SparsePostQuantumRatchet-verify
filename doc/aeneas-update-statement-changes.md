# Spec statement changes in the Aeneas update (nightly-2026.10.05-557eff8)

Branch `update-to-nightly-2026.10.05-557eff8`, PR #635. Baseline for "before": commit `97924cc`
(the last commit before the regenerated translation).

Every change below was forced: the old statement no longer type-checks against the new Aeneas
`Std` types. Two of them (marked **choice**) could reasonably have been phrased differently and are
worth a second look.

## Theorem statements

| Theorem(s) | File | Before | After | Reason |
|---|---|---|---|---|
| `mac_ct_spec`, `mac_hdr_spec` | `Spqr/Specs/Authenticator/Authenticator/{MacCt,MacHdr}.lean` | `hmac .Sha256 self.mac_key data …` with `data := Slice.make (LABEL ++ to_be_bytes ep ++ ct)` | `hmac .Sha256 self.mac_key.deref data …` with `data := Slice.from (LABEL ++ to_be_bytes ep ++ ct) (by grind)` | `alloc.vec.Vec` is now a structure wrapping a `Slice` and no longer coerces to `Slice`; the generated code itself calls `Vec.deref`. `Slice.make` was a deleted repo shim; the `by grind` only discharges the length bound (a `Prop`), so `data` means the same thing. |
| `verify_ct_spec`, `verify_hdr_spec` | `Spqr/Specs/Authenticator/Authenticator/{VerifyCt,VerifyHdr}.lean` | `result = Ok () ↔ mac_ct self ep ct = ok expected_mac` | `result = Ok () ↔ mac_ct self ep ct = ok { slice := expected_mac }` | `mac_ct` returns a `Vec`, `expected_mac` is a `Slice`. |
| `ChainEpochDirection.new_spec` | `Spqr/Specs/Chain/ChainEpochDirection/New.lean` | `result.next = k` | `result.next.deref = k` | `result.next` is now a `Vec`, `k` a `Slice`. **Choice:** `result.next.val = k.val` is equivalent and matches how `CedForDirection` states its result. It is `@[step]`, so the form affects downstream `step*` proofs (currently only `CedForDirection`, adapted with `simp_all [alloc.vec.Vec.deref, alloc.vec.Vec.val]`). |
| `decode_varint_loop_spec` | `Spqr/Specs/V1/Chunked/States/Serialize/DecodeVarint.lean` | `decode_varint_loop from1 at1 0#u64 0#usize false max_i` | `decode_varint_loop from1 0#u64 0#usize false at1 max_i` | The regenerated `decode_varint_loop` takes its arguments in a different order; only the call was adapted. |
| 8 specs (loop/body/main specs of `from_pb_loop0_loop0`, `from_pb_loop0`, `from_pb`) | `Spqr/Specs/Encoding/Polynomial/PolyDecoder/FromPb.lean` | `match Pt.Insts.CoreCmpOrd.cmp p last with \| ok Ordering.gt => … \| ok Ordering.eq => … \| ok Ordering.lt => …` | `match (Pt.Insts.CoreCmpOrd.cmp p last).match with \| .ok Ordering.gt => … \| .ok Ordering.eq => … \| .ok Ordering.lt => … \| _ => False` | `Result` is now a coinductive interaction tree; `ok` is a definition, not a constructor, so it can't be pattern-matched. `Result.match` is the inductive view Aeneas provides for this. |
| `Pt` `try_from_spec` | `Spqr/Specs/Encoding/Polynomial/Pt/Deserialize.lean` | `(h_clone : ∀ x ∈ s.val, copyInst.cloneInst.clone x = ok x)` | `(_h_clone : …)` (renamed only) | Upstream `TryFromArrayCopySlice.try_from` no longer clones, so the hypothesis is unused (unused-variable warning). **Choice:** delete the hypothesis entirely — a genuine (harmless) weakening of the assumptions. |

## Model definitions (same meaning, new constructor syntax)

These are hand-written spec-model definitions, not theorem statements. Only the way values are
constructed changed (`Slice`, `Vec`, `Array` are now structures built with `.from`):

- `chain.KeyHistory.horizonSlice` (`Spqr/Specs/Chain/KeyHistory/Defs.lean`): `⟨horizonBytes h, _⟩` → `Slice.from (horizonBytes h) _`
- `iterKeyHistory` (`Spqr/Specs/Chain/Defs.lean`): `{ data := ⟨d, h⟩ }` → `{ data := alloc.vec.Vec.from d h }`
- `cedKeyAdvancePost` (`Spqr/Specs/Chain/Chain/Defs.lean`): empty `KeyHistory` `⟨[], _⟩` → `{ data := alloc.vec.Vec.from [] _ }`
- `completePoints` (`Spqr/Math/Poly/Lagrange/CompletePoints.lean`): `⟨list, proof⟩` → `Array.from list (by simp)`
- `Inhabited (Slice U8)` instance (`Spqr/Specs/Encoding/Polynomial/PolyEncoder/EncodeBytesBase.lean`): `⟨⟨[], _⟩⟩` → `⟨Slice.from [] (by simp)⟩`

## Also changed (not statements)

- `Spqr/Auxiliary/Aeneas/Vec.lean`: `alloc.vec.Vec.deref_length` lost its `@[simp]` attribute
  (`runLinter` simpNF: `simp` already proves it); `scalar_tac_simps` and `grind =` kept.
- Deleted repo shims now upstream: `Spqr/Auxiliary/Aeneas/{Array,ArraySlice,Slice}.lean`.
