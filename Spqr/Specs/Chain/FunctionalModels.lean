/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Hoang Le Truong
-/
import SrcTranslated.Types
import Spqr.Specs.Chain.ChainEpochDirection.FunctionalModels

/-!
# Functional models of `spqr::chain::Chain::{into_pb, from_pb}`

Pure, total Lean functions stating what the two Rust serializers compute, written against the
translated data types only, together with the round-trip laws relating them. The spec theorems
in `IntoPb.lean` and `FromPb.lean` pin the extracted, monadic functions to these models. The
nested `ChainEpochDirection` conversions are handled by calling their own functional models.

The iterator pipeline (`into_iter`/`map`/`collect`) in the Rust source is modeled here as a
pure `List.map` over the underlying buffer of the `VecDeque`/`Vec`.

**Source:** "spqr/src/chain.rs"
-/

open Aeneas.Std spqr.chain
namespace spqr.chain.Chain.FunctionalModels

/-- **Functional model of mapping a `ChainEpoch` to a `proto.pq_ratchet.chain.Epoch`**
via `ChainEpochDirection.into_pb` on each of its `send` and `recv` fields. -/
def epochIntoPb (ce : ChainEpoch) : proto.pq_ratchet.chain.Epoch :=
  { send := some (ChainEpochDirection.FunctionalModels.intoPb ce.send),
    recv := some (ChainEpochDirection.FunctionalModels.intoPb ce.recv) }

/-- **Functional model of mapping a `proto.pq_ratchet.chain.Epoch` back to a `ChainEpoch`**
via `ChainEpochDirection.from_pb` on each of its `send` and `recv` fields. Returns
`Err StateDecode` if either field is `none`. -/
def epochFromPb (epoch : proto.pq_ratchet.chain.Epoch) :
    core.result.Result ChainEpoch Error :=
  match epoch.send, epoch.recv with
  | some s, some r =>
    match ChainEpochDirection.FunctionalModels.fromPb s,
          ChainEpochDirection.FunctionalModels.fromPb r with
    | .Ok sd, .Ok rd => .Ok { send := sd, recv := rd }
    | .Err e, _ => .Err e
    | _, .Err e => .Err e
  | none, _ => .Err Error.StateDecode
  | _, none => .Err Error.StateDecode

/-- Helper: traverse a list with a fallible function, collecting into `Ok` or short-circuiting
on the first `Err`. -/
def traverseResult {α β : Type} (f : α → core.result.Result β Error) :
    List α → core.result.Result (List β) Error
  | [] => .Ok []
  | a :: as_ =>
    match f a with
    | .Err e => .Err e
    | .Ok b =>
      match traverseResult f as_ with
      | .Err e => .Err e
      | .Ok bs => .Ok (b :: bs)

/-- `traverseResult` preserves list length on success. -/
theorem traverseResult_length {α₁ β₁ : Type}
    (f : α₁ → core.result.Result β₁ Error)
    (l : List α₁) (l' : List β₁) (h : traverseResult f l = .Ok l') :
    l'.length = l.length := by
  induction l generalizing l' with
  | nil => simp only [traverseResult, core.result.Result.Ok.injEq] at h; subst h; rfl
  | cons a tl ih =>
    simp only [traverseResult] at h
    match hfa : f a with
    | .Err e => exact absurd (hfa ▸ h) nofun
    | .Ok b =>
      simp only [hfa] at h
      match hrest : traverseResult f tl with
      | .Err e => exact absurd (hrest ▸ h) nofun
      | .Ok bs =>
        simp only [hrest, core.result.Result.Ok.injEq] at h
        subst h
        simp only [List.length_cons, ih bs hrest]

/-- **Functional model of `spqr::chain::Chain::into_pb`**
• A pure, total, human-readable function on the translated data types.

Converts a `Chain` to its protobuf form. The `direction` is obtained via `Direction → I32`,
`links` are mapped through `epochIntoPb`, and `params` is wrapped in `some`.

The `direction` field conversion (`Direction → I32`) is kept abstract in this model
because it depends on the `core.convert.IntoFrom.into` instance which is opaque.
We therefore take the converted `I32` as a parameter. -/
def intoPb (self : chain.Chain) (directionI32 : I32) :
    proto.pq_ratchet.Chain :=
  { direction := directionI32,
    current_epoch := self.current_epoch,
    send_epoch := self.send_epoch,
    links := ⟨self.links.buf.val.map epochIntoPb,
              by simp only [List.length_map]; exact self.links.buf.property⟩,
    next_root := self.next_root,
    params := some self.params }

/-- **Functional model of `spqr::chain::Chain::from_pb`**
• A pure, total, human-readable function on the translated data types.

Converts a protobuf `Chain` back into the in-memory form. `direction` is converted via
`try_from`; `links` are mapped through `epochFromPb`; `params` must be `some`.

The `direction` conversion (`I32 → Direction`) is kept abstract: we take the result of
`try_from` as a parameter. -/
def fromPb (pb : proto.pq_ratchet.Chain)
    (dirResult : core.result.Result proto.pq_ratchet.Direction Error) :
    core.result.Result chain.Chain Error :=
  match dirResult with
  | .Err e => .Err e
  | .Ok dir =>
    match h : traverseResult epochFromPb pb.links.val with
    | .Err e => .Err e
    | .Ok epochs =>
      match pb.params with
      | none => .Err Error.StateDecode
      | some params =>
        .Ok { dir := dir,
              current_epoch := pb.current_epoch,
              send_epoch := pb.send_epoch,
              links := { buf := ⟨epochs,
                           traverseResult_length epochFromPb pb.links.val epochs h ▸
                             pb.links.property⟩,
                         head := 0#usize, length := 0#usize },
              next_root := pb.next_root,
              params := params }

/-! ## Epoch-level round-trip properties -/

/-- **Round trip `epochFromPb ∘ epochIntoPb` for `ChainEpoch`** -/
@[simp]
theorem roundtrip_epochFromPb_epochIntoPb (ce : ChainEpoch) :
    epochFromPb (epochIntoPb ce) = .Ok ce := by
  simp [epochFromPb, epochIntoPb, ChainEpochDirection.FunctionalModels.fromPb,
    ChainEpochDirection.FunctionalModels.intoPb]

/-- **Round trip `epochIntoPb ∘ epochFromPb` for `proto.pq_ratchet.chain.Epoch`** -/
theorem roundtrip_epochIntoPb_epochFromPb (epoch : proto.pq_ratchet.chain.Epoch)
    (ce : ChainEpoch) (h : epochFromPb epoch = .Ok ce) :
    epochIntoPb ce = epoch := by
  cases epoch with
  | mk s r =>
    simp only [epochFromPb] at h
    match s, r with
    | some sv, some rv =>
      simp only [ChainEpochDirection.FunctionalModels.fromPb,
        core.result.Result.Ok.injEq] at h
      cases ce with
      | mk cs cr =>
        cases h
        simp only [epochIntoPb, ChainEpochDirection.FunctionalModels.intoPb]
    | none, _ => exact absurd h nofun
    | some _, none => exact absurd h nofun

/-! ## traverseResult round-trip properties -/

/-- `traverseResult` on a mapped list round-trips when `g ∘ f = Ok`. -/
theorem traverseResult_map_roundtrip {α₁ β₁ : Type}
    (f : α₁ → β₁) (g : β₁ → core.result.Result α₁ Error)
    (hgf : ∀ a, g (f a) = .Ok a)
    (l : List α₁) :
    traverseResult g (l.map f) = .Ok l := by
  induction l with
  | nil => simp [traverseResult]
  | cons a tl ih => simp [traverseResult, List.map, hgf, ih]

/-! ## Chain-level round-trip properties -/

/-- **Round trip `fromPb ∘ intoPb` for `spqr::chain::Chain`**

Given a `Chain` value `self` and a direction `dirI32`, converting to protobuf and back
yields `Ok` with a chain whose fields match `self` (the `links` buffer contents are
identical, though VecDeque metadata `head`/`length` are reset to 0). -/
theorem roundtrip_fromPb_intoPb (self : chain.Chain) (dirI32 : I32)
    (dr : core.result.Result proto.pq_ratchet.Direction Error)
    (hDir : dr = .Ok self.dir) :
    fromPb (intoPb self dirI32) dr = .Ok {
      self with
        links := { buf := self.links.buf,
                   head := 0#usize, length := 0#usize } } := by
  subst hDir
  unfold fromPb intoPb
  have htr := traverseResult_map_roundtrip epochIntoPb epochFromPb
    roundtrip_epochFromPb_epochIntoPb self.links.buf.val
  -- Split the outer dirResult match (trivially Ok)
  simp only []
  -- Split the inner `match h : traverseResult ...`
  split
  · next e heq => exact absurd (htr ▸ heq) nofun
  · next l heq =>
      rw [htr] at heq; simp only [core.result.Result.Ok.injEq] at heq; subst heq; rfl

/-- **Round trip `intoPb ∘ fromPb` for `spqr::chain::Chain`**

Given a protobuf `Chain` value `pb` and a direction result, if `fromPb` succeeds with
chain `c`, then `intoPb c dirI32` recovers the scalar fields of `pb`. -/
theorem roundtrip_intoPb_fromPb (pb : proto.pq_ratchet.Chain) (dirI32 : I32)
    (dr : core.result.Result proto.pq_ratchet.Direction Error)
    (c : chain.Chain) (h : fromPb pb dr = .Ok c) :
    intoPb c dirI32 = { pb with direction := (intoPb c dirI32).direction,
                                links := (intoPb c dirI32).links } := by
  unfold fromPb at h
  match hdr : dr with
  | .Err e => simp only at h; exact absurd h nofun
  | .Ok dir =>
    simp only [] at h
    -- Split on the `match h :` inside fromPb
    split at h
    · exact absurd h nofun
    · next epochs heq =>
      match hparams : pb.params with
      | none => exact absurd (hparams ▸ h) nofun
      | some params =>
        simp only [hparams, core.result.Result.Ok.injEq] at h
        subst h
        simp only [intoPb]

end spqr.chain.Chain.FunctionalModels
