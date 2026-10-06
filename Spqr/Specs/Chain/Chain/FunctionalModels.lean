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
translated data types only, together with the round-trip laws relating them.

**Source:** "spqr/src/chain.rs"
-/

open Aeneas.Std spqr.chain
namespace spqr.chain.Chain.FunctionalModels

/-- Functional model of `spqr::chain::ChainEpoch::into_pb`. -/
def epochIntoPb (ce : ChainEpoch) : proto.pq_ratchet.chain.Epoch :=
  { send := some (ChainEpochDirection.FunctionalModels.intoPb ce.send),
    recv := some (ChainEpochDirection.FunctionalModels.intoPb ce.recv) }

/-- Functional model of `spqr::chain::ChainEpoch::from_pb`. -/
def epochFromPb (epoch : proto.pq_ratchet.chain.Epoch) :
    core.result.Result ChainEpoch Error :=
  match epoch.send.map ChainEpochDirection.FunctionalModels.fromPb,
        epoch.recv.map ChainEpochDirection.FunctionalModels.fromPb with
  | some (.Ok sd), some (.Ok rd) => .Ok { send := sd, recv := rd }
  | _, _ => .Err Error.StateDecode

/-- Traverse a list with a fallible function, collecting results or short-circuiting on error. -/
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
        subst h; simp only [List.length_cons, ih bs hrest]

/-- Traverse a `Vec` with a fallible function, preserving the length invariant. -/
def traverseVec {α β : Type} (f : α → core.result.Result β Error) (v : alloc.vec.Vec α) :
    core.result.Result (alloc.vec.Vec β) Error :=
  match h : traverseResult f v.val with
  | .Err e => .Err e
  | .Ok l  => .Ok ⟨l, traverseResult_length f v.val l h ▸ v.property⟩

/-- Extract the logical contents of a `VecDeque` as a plain list. -/
def dequeContents {T A : Type} (d : alloc.collections.vec_deque.VecDeque T A) : List T :=
  (d.buf.val.drop d.head.val).take d.length.val

/-! ## Direction helpers -/

/-- Convert a `Direction` enum to its protobuf `I32` representation. -/
def directionToI32 : proto.pq_ratchet.Direction → I32
  | .A2B => 0#i32
  | .B2A => 1#i32

/-- Parse an `I32` into a `Direction` enum, returning an error on invalid values. -/
def directionFromI32 (i : I32) : core.result.Result proto.pq_ratchet.Direction Error :=
  match i with
  | 0#iscalar => .Ok .A2B
  | 1#iscalar => .Ok .B2A
  | _ => .Err Error.StateDecode

@[simp]
theorem directionFromI32_directionToI32 (d : proto.pq_ratchet.Direction) :
    directionFromI32 (directionToI32 d) = .Ok d := by
  cases d <;> rfl

theorem directionToI32_of_directionFromI32 (i : I32) (d : proto.pq_ratchet.Direction)
    (h : directionFromI32 i = .Ok d) : directionToI32 d = i := by
  unfold directionFromI32 at h
  split at h <;> cases h <;> rfl

/-! ## Functional models -/

/-- **Functional model of `spqr::chain::Chain::into_pb`** -/
def intoPb (self : chain.Chain) : proto.pq_ratchet.Chain :=
  { direction := directionToI32 self.dir,
    current_epoch := self.current_epoch,
    send_epoch := self.send_epoch,
    links := ⟨(dequeContents self.links).map epochIntoPb, by
      simp only [List.length_map, dequeContents, List.length_take, List.length_drop]
      have := self.links.buf.property
      omega⟩,
    next_root := self.next_root,
    params := some self.params }

/-- **Functional model of `spqr::chain::Chain::from_pb`** -/
def fromPb (pb : proto.pq_ratchet.Chain) : core.result.Result chain.Chain Error :=
  match directionFromI32 pb.direction, traverseVec epochFromPb pb.links, pb.params with
  | .Ok dir, .Ok epochs, some params =>
    .Ok { dir := dir,
          current_epoch := pb.current_epoch,
          send_epoch := pb.send_epoch,
          links := { buf := epochs, head := 0#usize,
                     length := Usize.ofNatCore epochs.val.length
                       (by have := epochs.property; scalar_tac) },
          next_root := pb.next_root,
          params := params }
  | _, _, _ => .Err Error.StateDecode


/-! ## Epoch-level round-trip properties -/

@[simp]
theorem roundtrip_epochFromPb_epochIntoPb (ce : ChainEpoch) :
    epochFromPb (epochIntoPb ce) = .Ok ce := by
  simp [epochFromPb, epochIntoPb, ChainEpochDirection.FunctionalModels.fromPb,
    ChainEpochDirection.FunctionalModels.intoPb]

theorem roundtrip_epochIntoPb_epochFromPb (epoch : proto.pq_ratchet.chain.Epoch)
    (ce : ChainEpoch) (h : epochFromPb epoch = .Ok ce) :
    epochIntoPb ce = epoch := by
  cases epoch with
  | mk s r =>
    simp only [epochFromPb] at h
    match s, r with
    | some sv, some rv =>
      simp only [Option.map] at h
      simp only [ChainEpochDirection.FunctionalModels.fromPb,
        core.result.Result.Ok.injEq] at h
      cases ce with
      | mk cs cr =>
        cases h
        simp only [epochIntoPb, ChainEpochDirection.FunctionalModels.intoPb]
    | none, _ => exact absurd h nofun
    | some _, none =>
      simp only [Option.map] at h
      exact absurd h (by
        simp only [ChainEpochDirection.FunctionalModels.fromPb]
        exact nofun)

/-! ## traverseResult round-trip properties -/

theorem traverseResult_map_roundtrip {α₁ β₁ : Type}
    (f : α₁ → β₁) (g : β₁ → core.result.Result α₁ Error)
    (hgf : ∀ a, g (f a) = .Ok a)
    (l : List α₁) :
    traverseResult g (l.map f) = .Ok l := by
  induction l with
  | nil => simp [traverseResult]
  | cons a tl ih => simp [traverseResult, List.map, hgf, ih]

/-! ## Chain-level round-trip properties -/

private theorem dequeContents_full {T A : Type}
    (d : alloc.collections.vec_deque.VecDeque T A)
    (hhead : d.head = 0#usize) (hlen : d.length.val = d.buf.val.length) :
    dequeContents d = d.buf.val := by
  unfold dequeContents
  rw [hhead]; simp [UScalar.ofNatCore_val_eq, hlen]

private theorem traverseVec_map_epochRoundtrip (l : List chain.ChainEpoch)
    (hl : l.length ≤ Aeneas.Std.Usize.max) :
    traverseVec epochFromPb ⟨l.map epochIntoPb, by simp only [List.length_map]; exact hl⟩ =
    .Ok ⟨l, hl⟩ := by
  simp only [traverseVec]
  have h := traverseResult_map_roundtrip epochIntoPb epochFromPb
    roundtrip_epochFromPb_epochIntoPb l
  split
  · rename_i e he; simp [h] at he
  · rename_i l' hl'
    simp only [h, core.result.Result.Ok.injEq] at hl'
    subst hl'
    rfl

theorem roundtrip_fromPb_intoPb (self : chain.Chain)
    (hhead : self.links.head = 0#usize)
    (hlen : self.links.length.val = self.links.buf.val.length) :
    fromPb (intoPb self) = .Ok self := by
  have hdc := dequeContents_full self.links hhead hlen
  simp only [fromPb, intoPb, directionFromI32_directionToI32, hdc,
    traverseVec_map_epochRoundtrip _ self.links.buf.property]
  congr 1
  cases self with
  | mk dir ce se links nr params =>
    cases links with
    | mk buf head len =>
      simp only at hhead hlen hdc ⊢
      subst hhead
      have : Usize.ofNatCore (buf.val.length) (by have := buf.property; scalar_tac) = len := by
        apply UScalar.eq_of_val_eq
        simp [hlen]
      congr 2

private theorem traverseResult_reverse {α₁ β₁ : Type}
    (f : α₁ → β₁) (g : β₁ → core.result.Result α₁ Error)
    (hfg : ∀ b a, g b = .Ok a → f a = b)
    (l : List β₁) (l' : List α₁) (h : traverseResult g l = .Ok l') :
    l'.map f = l := by
  induction l generalizing l' with
  | nil => simp only [traverseResult, core.result.Result.Ok.injEq, List.nil_eq] at h; subst h; rfl
  | cons b tl ih =>
    simp only [traverseResult] at h
    match hgb : g b with
    | .Err e => exact absurd (hgb ▸ h) nofun
    | .Ok a =>
      simp only [hgb] at h
      match hrest : traverseResult g tl with
      | .Err e => exact absurd (hrest ▸ h) nofun
      | .Ok as_ =>
        simp only [hrest, core.result.Result.Ok.injEq] at h
        subst h
        simp only [List.map, hfg b a hgb, ih as_ hrest]

private theorem traverseVec_reverse
    (l : alloc.vec.Vec proto.pq_ratchet.chain.Epoch)
    (l' : alloc.vec.Vec chain.ChainEpoch)
    (h : traverseVec epochFromPb l = .Ok l') :
    l'.val.map epochIntoPb = l.val := by
  unfold traverseVec at h
  split at h
  · exact absurd h nofun
  · rename_i l'' hl''
    cases h
    exact traverseResult_reverse epochIntoPb epochFromPb
      (fun b a ha => roundtrip_epochIntoPb_epochFromPb b a ha) l.val l'' hl''

theorem roundtrip_intoPb_fromPb (pb : proto.pq_ratchet.Chain) (c : chain.Chain)
    (h : fromPb pb = .Ok c) : intoPb c = pb := by
  unfold fromPb at h
  match hdir : directionFromI32 pb.direction,
        hvec : traverseVec epochFromPb pb.links,
        hpar : pb.params with
  | .Ok dir, .Ok epochs, some params =>
    simp only [hdir, hvec, hpar] at h
    cases h
    have hmap := traverseVec_reverse pb.links epochs hvec
    have hlen : (epochs.val.map epochIntoPb).length ≤ Usize.max := by
      rw [hmap]; exact pb.links.property
    simp only [intoPb, directionToI32_of_directionFromI32 _ _ hdir]
    congr 1
    · show ⟨_, _⟩ = pb.links
      have : (Usize.ofNatCore epochs.val.length
        (by have := epochs.property; scalar_tac)).val = epochs.val.length :=
        UScalar.ofNatCore_val_eq ..
      simp only [dequeContents, UScalar.ofNatCore_val_eq, List.drop_zero, this, List.take_length]
      exact Subtype.ext hmap
    · exact hpar.symm
  | .Err _, _, _ => simp only [hdir] at h; exact absurd h nofun
  | _, .Err _, _ => simp only [hdir, hvec] at h; exact absurd h nofun
  | .Ok _, .Ok _, none => simp only [hdir, hvec, hpar] at h; exact absurd h nofun

end spqr.chain.Chain.FunctionalModels
