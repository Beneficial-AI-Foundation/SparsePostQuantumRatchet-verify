# Chain decoder definitions and proof reuse

The chain serialization models use one validity rule for a direction's `next` key: it may be empty, or it must contain exactly 32 bytes. Naming this rule makes the decoder's accepted inputs explicit and lets proofs reuse the same condition at both direction and epoch level. The changes described here concern the training model files and one proof in the test partition.

## New definitions

In `Spqr/Specs/Chain/ChainEpochDirection/FunctionalModels.lean`, within the `spqr.chain.ChainEpochDirection.FunctionalModels` namespace, I added:

```lean
/-- A direction has a decodable next key: either absent or exactly one 32-byte key. -/
abbrev ValidNextKey (next : alloc.vec.Vec U8) : Prop :=
  next.val.isEmpty ∨ next.length = 32

/-- The condition under which serialization and decoding preserve a direction. -/
abbrev ValidDirection (x : chain.ChainEpochDirection) : Prop :=
  ValidNextKey x.next
```

`ValidNextKey` applies to a key vector, so it can be used with the protobuf representation or an in-memory direction. `ValidDirection` expresses the same requirement for a complete in-memory direction. Both are `abbrev` declarations: Lean can reduce them to their right-hand sides during type-class resolution and proof simplification. Neither introduces a new assumption or changes which keys are valid.

## New theorem

I added this theorem in the same training model file:

```lean
/-- A valid key decodes to a direction; an invalid key produces `StateDecode`. -/
theorem fromPb_cases (pb : proto.pq_ratchet.chain.epoch.EpochDirection) :
    (∃ d, fromPb pb = .Ok d) ∨ fromPb pb = .Err .StateDecode := by
  by_cases h : ValidNextKey pb.next
  · exact .inl ⟨{ ctr := pb.ctr, next := pb.next, prev := { data := pb.prev } },
      by simp [fromPb, h]⟩
  · exact .inr (by simp [fromPb, h])
```

The theorem splits on `ValidNextKey`. If the key is valid, it supplies the exact decoded direction. Otherwise, the model returns `StateDecode`. This is a property of the existing decoder model, not an additional constraint on callers.

## Existing definitions and theorem changed

The existing `fromPb` decoder model now names its condition:

```lean
def fromPb (pb : proto.pq_ratchet.chain.epoch.EpochDirection) :
    core.result.Result chain.ChainEpochDirection Error :=
  if ValidNextKey pb.next then
    .Ok { ctr := pb.ctr, next := pb.next, prev := { data := pb.prev } }
  else .Err .StateDecode
```

Previously, its `if` condition was written inline as `pb.next.val.isEmpty ∨ pb.next.length = 32`. Reducing `ValidNextKey` gives precisely that expression, so the decoder's behavior is unchanged.

The existing epoch predicate in `Spqr/Specs/Chain/Chain/FunctionalModels.lean` now composes the direction predicate:

```lean
def epochNextOk (ce : ChainEpoch) : Prop :=
  ChainEpochDirection.FunctionalModels.ValidDirection ce.send ∧
  ChainEpochDirection.FunctionalModels.ValidDirection ce.recv
```

Previously, it contained the empty-or-32-byte condition separately for `send` and `recv`. Its meaning is unchanged. The existing theorem `roundtrip_fromPb_intoPb` also takes `(hx : ValidDirection x)` in place of the same disjunction written inline; its conclusion and proof are unchanged.

## How the test proof became shorter

In `Spqr/Specs/Chain/Chain/FromPb.lean`, the proof of `from_pb.link_from_pb_spec` needs to know that decoding each direction succeeds or returns `StateDecode`. Previously it established that fact locally:

```lean
have hdir : ∀ x, (∃ d, chain.ChainEpochDirection.FunctionalModels.fromPb x = .Ok d) ∨
    chain.ChainEpochDirection.FunctionalModels.fromPb x = .Err .StateDecode := by
  intro x
  rcases h : chain.ChainEpochDirection.FunctionalModels.fromPb x with d | e
  · exact .inl ⟨d, rfl⟩
  · exact .inr (by rw [chain.ChainEpochDirection.FunctionalModels.fromPb_err x e h])
```

It now obtains the same fact from the reusable theorem:

```lean
have hdir := chain.ChainEpochDirection.FunctionalModels.fromPb_cases
```

The rest of `from_pb.link_from_pb_spec` still uses `hdir` for the `send` and `recv` branches. The local setup fell from six lines to one; the case analysis moved into the general decoder model, where other proofs can reuse it. This is a source-code reduction, not a measured proof-time improvement.

## Verification and scope

`lake build` completed successfully with 2,822 jobs after the changes. Only `Spqr/Specs/Chain/Chain/FromPb.lean` changed in the test partition. No other test proof was shortened by this work.
