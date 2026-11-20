/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Lacramioara Astefanoaei
-/
module

public import Spqr.Specs.Braid.StateMachine.Model

/-! # The ML-KEM Braid machine over partially known primitives

A runtime monitor knows the primitives only at the arguments where it saw the code call them.
`OPrims` holds such partial primitives: a primitive learned from calls returns `none` where no
call was seen. `sendO`, `receiveO`, `initAliceO` and `initBobO` compute `send`, `receive`,
`initAlice` and `initBob` of `Model.lean` over `OPrims`, and return `none` when the step needs a
value that the partial primitives do not have.

`Agrees P Q` states that the total primitives `P` extend the partial primitives `Q`. Each
`_sound` theorem states that a result of the partial computation is the result of the total
computation under every `P` that extends `Q`.

**Source**: ML-KEM Braid Rev. 1, §1.2, §2.2–§2.6 -/

@[expose] public section

open Aeneas Aeneas.Std

namespace BraidModel

/-- The primitives of `Prims`, where `nextChunk`, `message`, the KEM, `ekMatches`, `MAC`,
`KDF_AUTH` and `KDF_OK` return `none` at an argument where the value is not known. -/
structure OPrims (Enc Dec Chunk : Type) where
  /-- `Encode(byte_array) → encoder` -/
  encode : Bytes → Enc
  /-- `encoder.next_chunk()`, with the encoder after the call, where known -/
  nextChunk : Enc → Option (Chunk × Enc)
  /-- `Decoder.new(message_size)` -/
  decoderNew : Nat → Dec
  /-- `decoder.add_chunk(chunk)`, with the decoder after the call -/
  addChunk : Dec → Chunk → Dec
  /-- `decoder.message()` (or `none` when there is no message yet), where known -/
  message : Dec → Option (Option Bytes)
  /-- `KeyGen(randomness)`, where known -/
  keyGen : Bytes → Option (Bytes × Bytes × Bytes)
  /-- `Encaps1(ek_header, randomness)`, where known -/
  encaps1 : Bytes → Bytes → Option (Bytes × Bytes × Bytes)
  /-- `Encaps2(encaps_secret, ek_header, ek_vector)`, where known -/
  encaps2 : Bytes → Bytes → Bytes → Option Bytes
  /-- `Decaps(dk, ct1, ct2)`, where known -/
  decaps : Bytes → Bytes → Bytes → Option Bytes
  /-- The integrity check of `ek_vector` against `ek_header`, where known -/
  ekMatches : Bytes → Bytes → Option Bool
  /-- `KEM.HEADER_SIZE` -/
  headerSize : Nat
  /-- `KEM.EK_SIZE` -/
  ekSize : Nat
  /-- `KEM.CT1_SIZE` -/
  ct1Size : Nat
  /-- `KEM.CT2_SIZE` -/
  ct2Size : Nat
  /-- `MAC_SIZE` -/
  macSize : Nat
  /-- `MAC(mac_key, msg)`, where known -/
  mac : Bytes → Bytes → Option Bytes
  /-- `PROTOCOL_INFO` -/
  protocolInfo : Bytes
  /-- `ToBytes(epoch)` -/
  toBytes : Nat → Bytes
  /-- `KDF_AUTH(root_key, update_key, epoch)`, where known -/
  kdfAuth : Bytes → Bytes → Nat → Option Bytes
  /-- `KDF_OK(shared_secret, epoch)`, where known -/
  kdfOk : Bytes → Nat → Option Bytes

variable {Enc Dec Chunk : Type}

/-- `P` extends `Q`: the fields that are total in `Q` are equal, and wherever a field of `Q`
returns `some v`, the field of `P` returns `v`. -/
structure Agrees (P : Prims Enc Dec Chunk) (Q : OPrims Enc Dec Chunk) : Prop where
  encode : P.encode = Q.encode
  nextChunk : ∀ x v, Q.nextChunk x = some v → P.nextChunk x = v
  decoderNew : P.decoderNew = Q.decoderNew
  addChunk : P.addChunk = Q.addChunk
  message : ∀ d v, Q.message d = some v → P.message d = v
  keyGen : ∀ r v, Q.keyGen r = some v → P.keyGen r = v
  encaps1 : ∀ hdr r v, Q.encaps1 hdr r = some v → P.encaps1 hdr r = v
  encaps2 : ∀ es hdr ek v, Q.encaps2 es hdr ek = some v → P.encaps2 es hdr ek = v
  decaps : ∀ dk ct1 ct2 v, Q.decaps dk ct1 ct2 = some v → P.decaps dk ct1 ct2 = v
  ekMatches : ∀ hdr ek v, Q.ekMatches hdr ek = some v → P.ekMatches hdr ek = v
  headerSize : P.headerSize = Q.headerSize
  ekSize : P.ekSize = Q.ekSize
  ct1Size : P.ct1Size = Q.ct1Size
  ct2Size : P.ct2Size = Q.ct2Size
  macSize : P.macSize = Q.macSize
  mac : ∀ k d v, Q.mac k d = some v → P.mac k d = v
  protocolInfo : P.protocolInfo = Q.protocolInfo
  toBytes : P.toBytes = Q.toBytes
  kdfAuth : ∀ rk k e v, Q.kdfAuth rk k e = some v → P.kdfAuth rk k e = v
  kdfOk : ∀ ss e v, Q.kdfOk ss e = some v → P.kdfOk ss e = v

/-- `Auth.update` over `OPrims`. -/
def Auth.updateO (Q : OPrims Enc Dec Chunk) (a : Auth) (epoch : Nat) (key : Bytes) :
    Option Auth := do
  let out ← Q.kdfAuth a.rootKey key epoch
  pure { rootKey := out.take 32, macKey := out.drop 32 }

/-- `Auth.init` over `OPrims`. -/
def Auth.initO (Q : OPrims Enc Dec Chunk) (epoch : Nat) (key : Bytes) : Option Auth :=
  Auth.updateO Q { rootKey := List.replicate 32 0#u8, macKey := [] } epoch key

/-- `Auth.macHdr` over `OPrims`. -/
def Auth.macHdrO (Q : OPrims Enc Dec Chunk) (a : Auth) (epoch : Nat) (hdr : Bytes) :
    Option Bytes :=
  Q.mac a.macKey (Q.protocolInfo ++ ascii ":ekheader" ++ Q.toBytes epoch ++ hdr)

/-- `Auth.macCt` over `OPrims`. -/
def Auth.macCtO (Q : OPrims Enc Dec Chunk) (a : Auth) (epoch : Nat) (ct : Bytes) :
    Option Bytes :=
  Q.mac a.macKey (Q.protocolInfo ++ ascii ":ciphertext" ++ Q.toBytes epoch ++ ct)

/-- `ct2Encoder` over `OPrims`. -/
def ct2EncoderO (Q : OPrims Enc Dec Chunk) (epoch : Nat) (auth : Auth)
    (encapsSecret ct1 hdr ek : Bytes) : Option Enc := do
  let ct2 ← Q.encaps2 encapsSecret hdr ek
  let t ← Auth.macCtO Q auth epoch (ct1 ++ ct2)
  pure (Q.encode (ct2 ++ t))

/-- `send` over `OPrims`. -/
def sendO (Q : OPrims Enc Dec Chunk) (σ : State Enc Dec) (r : Bytes) :
    Option (State Enc Dec × Msg Chunk × Option Key) :=
  match σ with
  | .keysUnsampled e a => do
    let kg ← Q.keyGen r
    let t ← Auth.macHdrO Q a e kg.2.1
    let ce ← Q.nextChunk (Q.encode (kg.2.1 ++ t))
    pure (.keysSampled e a kg.1 kg.2.1 kg.2.2 ce.2, ⟨e, .hdr ce.1⟩, none)
  | .keysSampled e a dk hdr ek enc => do
    let ce ← Q.nextChunk enc
    pure (.keysSampled e a dk hdr ek ce.2, ⟨e, .hdr ce.1⟩, none)
  | .headerSent e a dk d enc => do
    let ce ← Q.nextChunk enc
    pure (.headerSent e a dk d ce.2, ⟨e, .ek ce.1⟩, none)
  | .ct1Received e a dk ct1 enc => do
    let ce ← Q.nextChunk enc
    pure (.ct1Received e a dk ct1 ce.2, ⟨e, .ekCt1Ack ce.1⟩, none)
  | .ekSentCt1Received e a dk ct1 d => pure (.ekSentCt1Received e a dk ct1 d, ⟨e, .ct1Ack⟩, none)
  | .noHeaderReceived e a d => pure (.noHeaderReceived e a d, ⟨e, .none⟩, none)
  | .headerReceived e a hdr d => do
    let x ← Q.encaps1 hdr r
    let ss ← Q.kdfOk x.2.2 e
    let a' ← Auth.updateO Q a e ss
    let ce ← Q.nextChunk (Q.encode x.2.1)
    pure (.ct1Sampled e a' hdr x.1 x.2.1 ce.2 d, ⟨e, .ct1 ce.1⟩, some (e, ss))
  | .ct1Sampled e a hdr es ct1 enc d => do
    let ce ← Q.nextChunk enc
    pure (.ct1Sampled e a hdr es ct1 ce.2 d, ⟨e, .ct1 ce.1⟩, none)
  | .ekReceivedCt1Sampled e a es ct1 hdr ek enc => do
    let ce ← Q.nextChunk enc
    pure (.ekReceivedCt1Sampled e a es ct1 hdr ek ce.2, ⟨e, .ct1 ce.1⟩, none)
  | .ct1Acknowledged e a hdr es ct1 d => pure (.ct1Acknowledged e a hdr es ct1 d, ⟨e, .none⟩, none)
  | .ct2Sampled e a enc => do
    let ce ← Q.nextChunk enc
    pure (.ct2Sampled e a ce.2, ⟨e, .ct2 ce.1⟩, none)

/-- The arms of `receiveEq` over `OPrims` that add an `ek` chunk in `Ct1Sampled` or
`Ct1Acknowledged` and then may reach `Ct2Sampled` (transitions (8), (9) and (11)). With the
decoder `d'` that has the new chunk: no message gives `stay d'`; a message `ek` that matches the
header gives `Ct2Sampled`; any other message is the model's failure. -/
def ekDoneO (Q : OPrims Enc Dec Chunk) (e : Nat) (a : Auth) (hdr es ct1 : Bytes) (d' : Dec)
    (stay : Dec → State Enc Dec) : Option (Option (State Enc Dec × Option Key)) := do
  let msg ← Q.message d'
  match msg with
  | none => pure (some (stay d', none))
  | some ek => do
    let ok ← Q.ekMatches hdr ek
    if ok then do
      let enc ← ct2EncoderO Q e a es ct1 hdr ek
      pure (some (.ct2Sampled e a enc, none))
    else pure none

/-- `receiveEq` over `OPrims`. The outer `none` means that a needed value is unknown; the inner
`none` is the model's failure. -/
def receiveEqO (Q : OPrims Enc Dec Chunk) : State Enc Dec → Payload Chunk →
    Option (Option (State Enc Dec × Option Key))
  | .keysSampled e a dk _ ek _, .ct1 c =>
    pure (some (.headerSent e a dk (Q.addChunk (Q.decoderNew Q.ct1Size) c) (Q.encode ek), none))
  | .headerSent e a dk d enc, .ct1 c => do
    let d' := Q.addChunk d c
    let msg ← Q.message d'
    match msg with
    | some ct1 => pure (some (.ct1Received e a dk ct1 enc, none))
    | none => pure (some (.headerSent e a dk d' enc, none))
  | .ct1Received e a dk ct1 _, .ct2 c =>
    pure (some (.ekSentCt1Received e a dk ct1
      (Q.addChunk (Q.decoderNew (Q.ct2Size + Q.macSize)) c), none))
  | .ekSentCt1Received e a dk ct1 d, .ct2 c => do
    let d' := Q.addChunk d c
    let msg ← Q.message d'
    match msg with
    | none => pure (some (.ekSentCt1Received e a dk ct1 d', none))
    | some m => do
      let ss₀ ← Q.decaps dk ct1 (m.take Q.ct2Size)
      let ss ← Q.kdfOk ss₀ e
      let a' ← Auth.updateO Q a e ss
      let t ← Auth.macCtO Q a' e (ct1 ++ m.take Q.ct2Size)
      if m.drop Q.ct2Size = t then
        pure (some (.noHeaderReceived (e + 1) a' (Q.decoderNew (Q.headerSize + Q.macSize)),
          some (e, ss)))
      else pure none
  | .noHeaderReceived e a d, .hdr c => do
    let d' := Q.addChunk d c
    let msg ← Q.message d'
    match msg with
    | none => pure (some (.noHeaderReceived e a d', none))
    | some m => do
      let t ← Auth.macHdrO Q a e (m.take Q.headerSize)
      if m.drop Q.headerSize = t then
        pure (some (.headerReceived e a (m.take Q.headerSize) (Q.decoderNew Q.ekSize), none))
      else pure none
  | .ct1Sampled e a hdr es ct1 enc d, .ek c => do
    let d' := Q.addChunk d c
    let msg ← Q.message d'
    match msg with
    | none => pure (some (.ct1Sampled e a hdr es ct1 enc d', none))
    | some ek => do
      let ok ← Q.ekMatches hdr ek
      if ok then pure (some (.ekReceivedCt1Sampled e a es ct1 hdr ek enc, none))
      else pure none
  | .ct1Sampled e a hdr es ct1 _ d, .ekCt1Ack c
  | .ct1Acknowledged e a hdr es ct1 d, .ekCt1Ack c
  | .ct1Acknowledged e a hdr es ct1 d, .ek c =>
    ekDoneO Q e a hdr es ct1 (Q.addChunk d c) (.ct1Acknowledged e a hdr es ct1)
  | .ekReceivedCt1Sampled e a es ct1 hdr ek _, .ekCt1Ack _
  | .ekReceivedCt1Sampled e a es ct1 hdr ek _, .ct1Ack => do
    let enc ← ct2EncoderO Q e a es ct1 hdr ek
    pure (some (.ct2Sampled e a enc, none))
  | σ, _ => pure (some (σ, none))

/-- `receive` over `OPrims`, with the outer and inner `none` of `receiveEqO`. -/
def receiveO (Q : OPrims Enc Dec Chunk) (σ : State Enc Dec) (m : Msg Chunk) :
    Option (Option (State Enc Dec × Option Key)) :=
  match σ with
  | .ct2Sampled e a _ =>
    if m.epoch = e + 1 then pure (some (.keysUnsampled (e + 1) a, none))
    else if m.epoch > e then pure none
    else pure (some (σ, none))
  | _ =>
    if m.epoch > σ.epoch then pure none
    else if m.epoch < σ.epoch then pure (some (σ, none))
    else receiveEqO Q σ m.payload

/-- `initAlice` over `OPrims`. -/
def initAliceO (Q : OPrims Enc Dec Chunk) (sharedSecret : Bytes) : Option (State Enc Dec) := do
  let a ← Auth.initO Q 1 sharedSecret
  pure (.keysUnsampled 1 a)

/-- `initBob` over `OPrims`. -/
def initBobO (Q : OPrims Enc Dec Chunk) (sharedSecret : Bytes) : Option (State Enc Dec) := do
  let a ← Auth.initO Q 1 sharedSecret
  pure (.noHeaderReceived 1 a (Q.decoderNew (Q.headerSize + Q.macSize)))

section Soundness

variable {P : Prims Enc Dec Chunk} {Q : OPrims Enc Dec Chunk}

/-- If `Auth.updateO Q a e k` returns `a'`, then every `P` that extends `Q` gives
`Auth.update P a e k = a'`. -/
theorem Auth.updateO_sound (hA : Agrees P Q) {a a' : Auth} {e : Nat} {k : Bytes}
    (h : Auth.updateO Q a e k = some a') : Auth.update P a e k = a' := by
  simp only [Auth.updateO, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨out, hout, rfl⟩ := h
  simp only [Auth.update, hA.kdfAuth _ _ _ _ hout]

/-- If `Auth.initO Q e k` returns `a`, then every `P` that extends `Q` gives
`Auth.init P e k = a`. -/
theorem Auth.initO_sound (hA : Agrees P Q) {a : Auth} {e : Nat} {k : Bytes}
    (h : Auth.initO Q e k = some a) : Auth.init P e k = a :=
  Auth.updateO_sound hA h

/-- If `Auth.macHdrO Q a e hdr` returns `t`, then every `P` that extends `Q` gives
`Auth.macHdr P a e hdr = t`. -/
theorem Auth.macHdrO_sound (hA : Agrees P Q) {a : Auth} {e : Nat} {hdr t : Bytes}
    (h : Auth.macHdrO Q a e hdr = some t) : Auth.macHdr P a e hdr = t := by
  simp only [Auth.macHdrO] at h
  simp only [Auth.macHdr, hA.protocolInfo, hA.toBytes, hA.mac _ _ _ h]

/-- If `Auth.macCtO Q a e ct` returns `t`, then every `P` that extends `Q` gives
`Auth.macCt P a e ct = t`. -/
theorem Auth.macCtO_sound (hA : Agrees P Q) {a : Auth} {e : Nat} {ct t : Bytes}
    (h : Auth.macCtO Q a e ct = some t) : Auth.macCt P a e ct = t := by
  simp only [Auth.macCtO] at h
  simp only [Auth.macCt, hA.protocolInfo, hA.toBytes, hA.mac _ _ _ h]

/-- If `ct2EncoderO Q e a es ct1 hdr ek` returns `enc`, then every `P` that extends `Q` gives
`ct2Encoder P e a es ct1 hdr ek = enc`. -/
theorem ct2EncoderO_sound (hA : Agrees P Q) {e : Nat} {a : Auth} {es ct1 hdr ek : Bytes}
    {enc : Enc} (h : ct2EncoderO Q e a es ct1 hdr ek = some enc) :
    ct2Encoder P e a es ct1 hdr ek = enc := by
  simp only [ct2EncoderO, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨ct2, h2, t, ht, rfl⟩ := h
  simp only [ct2Encoder, hA.encaps2 _ _ _ _ h2, Auth.macCtO_sound hA ht, hA.encode]

/-- If `sendO Q σ r` returns `x`, then every `P` that extends `Q` gives `send P σ r = x`. -/
theorem sendO_sound (hA : Agrees P Q) {σ : State Enc Dec} {r : Bytes}
    {x : State Enc Dec × Msg Chunk × Option Key} (h : sendO Q σ r = some x) :
    send P σ r = x := by
  cases σ <;> simp only [sendO, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  case keysUnsampled e a =>
    obtain ⟨⟨dk, hdr, ek⟩, hkg, t, ht, ⟨c, enc⟩, hce, rfl⟩ := h
    simp only [send, hA.keyGen _ _ hkg, Auth.macHdrO_sound hA ht, hA.encode,
      hA.nextChunk _ _ hce]
  case headerReceived e a hdr d =>
    obtain ⟨⟨es, ct1, ss₀⟩, hx, ss, hss, a', ha', ⟨c, enc⟩, hce, rfl⟩ := h
    simp only [send, hA.encaps1 _ _ _ hx, hA.kdfOk _ _ _ hss, Auth.updateO_sound hA ha',
      hA.encode, hA.nextChunk _ _ hce]
  all_goals first
    | (subst h; rfl)
    | (obtain ⟨⟨c, enc⟩, hce, rfl⟩ := h; simp only [send, hA.nextChunk _ _ hce])

/-- If `ekDoneO Q e a hdr es ct1 d' stay` returns `x`, then for every `P` that extends `Q`, the
same computation over `P`, as in the corresponding arms of `receiveEq P`, gives `x`. -/
theorem ekDoneO_sound (hA : Agrees P Q) {e : Nat} {a : Auth} {hdr es ct1 : Bytes} {d' : Dec}
    {stay : Dec → State Enc Dec} {x : Option (State Enc Dec × Option Key)}
    (h : ekDoneO Q e a hdr es ct1 d' stay = some x) :
    (match P.message d' with
      | none => some (stay d', none)
      | some ek =>
        if P.ekMatches hdr ek then some (.ct2Sampled e a (ct2Encoder P e a es ct1 hdr ek), none)
        else none) = x := by
  simp only [ekDoneO, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨msg, hmsg, h⟩ := h
  rw [hA.message _ _ hmsg]
  cases msg with
  | none => simpa only [Option.pure_def, Option.some.injEq] using h
  | some ek =>
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨ok, hok, h⟩ := h
    simp only [hA.ekMatches _ _ _ hok]
    cases ok with
    | false =>
      simpa only [Bool.false_eq_true, ↓reduceIte, Option.pure_def, Option.some.injEq] using h
    | true =>
      simp only [↓reduceIte, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h ⊢
      obtain ⟨enc, henc, rfl⟩ := h
      rw [ct2EncoderO_sound hA henc]

/-- If `receiveEqO Q σ p` returns `some x`, then every `P` that extends `Q` gives
`receiveEq P σ p = x`. -/
theorem receiveEqO_sound (hA : Agrees P Q) {σ : State Enc Dec} {p : Payload Chunk}
    {x : Option (State Enc Dec × Option Key)} (h : receiveEqO Q σ p = some x) :
    receiveEq P σ p = x := by
  cases σ <;> cases p <;>
    simp only [receiveEqO, receiveEq, Option.pure_def, Option.some.injEq, hA.addChunk,
      hA.decoderNew, hA.encode, hA.ct1Size, hA.ct2Size, hA.macSize, hA.headerSize,
      hA.ekSize] at h ⊢
  case headerSent.ct1 e a dk d enc c =>
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨msg, hmsg, h⟩ := h
    rw [hA.message _ _ hmsg]
    cases msg <;> simpa only [Option.pure_def, Option.some.injEq] using h
  case ekSentCt1Received.ct2 e a dk ct1 d c =>
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨msg, hmsg, h⟩ := h
    rw [hA.message _ _ hmsg]
    cases msg with
    | none => simpa only [Option.pure_def, Option.some.injEq] using h
    | some m =>
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨ss₀, hss₀, ss, hss, a', ha', t, ht, h⟩ := h
      simp only [hA.decaps _ _ _ _ hss₀, hA.kdfOk _ _ _ hss, Auth.updateO_sound hA ha',
        Auth.macCtO_sound hA ht]
      split_ifs at h ⊢ <;> simpa only [Option.pure_def, Option.some.injEq] using h
  case noHeaderReceived.hdr e a d c =>
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨msg, hmsg, h⟩ := h
    rw [hA.message _ _ hmsg]
    cases msg with
    | none => simpa only [Option.pure_def, Option.some.injEq] using h
    | some m =>
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨t, ht, h⟩ := h
      simp only [Auth.macHdrO_sound hA ht]
      split_ifs at h ⊢ <;> simpa only [Option.pure_def, Option.some.injEq] using h
  case ct1Sampled.ek e a hdr es ct1 enc d c =>
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨msg, hmsg, h⟩ := h
    rw [hA.message _ _ hmsg]
    cases msg with
    | none => simpa only [Option.pure_def, Option.some.injEq] using h
    | some ek =>
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨ok, hok, h⟩ := h
      simp only [hA.ekMatches _ _ _ hok]
      cases ok <;> simpa only [Bool.false_eq_true, ↓reduceIte, Option.pure_def,
        Option.some.injEq] using h
  case ct1Sampled.ekCt1Ack | ct1Acknowledged.ekCt1Ack | ct1Acknowledged.ek =>
    exact ekDoneO_sound hA h
  case ekReceivedCt1Sampled.ekCt1Ack | ekReceivedCt1Sampled.ct1Ack =>
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨enc, henc, rfl⟩ := h
    rw [ct2EncoderO_sound hA henc]
  all_goals exact h

/-- If `receiveO Q σ m` returns `some x`, then every `P` that extends `Q` gives
`receive P σ m = x`. -/
theorem receiveO_sound (hA : Agrees P Q) {σ : State Enc Dec} {m : Msg Chunk}
    {x : Option (State Enc Dec × Option Key)} (h : receiveO Q σ m = some x) :
    receive P σ m = x := by
  by_cases hc : ∃ e a enc, σ = .ct2Sampled e a enc
  · obtain ⟨e, a, enc, rfl⟩ := hc
    simp only [receiveO, receive, Option.pure_def] at h ⊢
    by_cases h1 : m.epoch = e + 1
    · simpa only [h1, ↓reduceIte, Option.some.injEq] using h
    · by_cases h2 : m.epoch > e
      · simpa only [h1, h2, ↓reduceIte, Option.some.injEq] using h
      · simpa only [h1, h2, ↓reduceIte, Option.some.injEq] using h
  · have hr : receive P σ m = if m.epoch > σ.epoch then none
        else if m.epoch < σ.epoch then some (σ, none) else receiveEq P σ m.payload := by
      cases σ <;> first | rfl | exact absurd ⟨_, _, _, rfl⟩ hc
    have hrO : receiveO Q σ m = if m.epoch > σ.epoch then some none
        else if m.epoch < σ.epoch then some (some (σ, none)) else receiveEqO Q σ m.payload := by
      cases σ <;> first | rfl | exact absurd ⟨_, _, _, rfl⟩ hc
    rw [hrO] at h
    rw [hr]
    by_cases h1 : m.epoch > σ.epoch
    · simpa only [h1, ↓reduceIte, Option.some.injEq] using h
    · by_cases h2 : m.epoch < σ.epoch
      · simpa only [h1, h2, ↓reduceIte, Option.some.injEq] using h
      · simp only [h1, h2, ↓reduceIte] at h ⊢
        exact receiveEqO_sound hA h

/-- If `initAliceO Q ss` returns `σ`, then every `P` that extends `Q` gives
`initAlice P ss = σ`. -/
theorem initAliceO_sound (hA : Agrees P Q) {ss : Bytes} {σ : State Enc Dec}
    (h : initAliceO Q ss = some σ) : initAlice P ss = σ := by
  simp only [initAliceO, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨a, ha, rfl⟩ := h
  simp only [initAlice, Auth.initO_sound hA ha]

/-- If `initBobO Q ss` returns `σ`, then every `P` that extends `Q` gives
`initBob P ss = σ`. -/
theorem initBobO_sound (hA : Agrees P Q) {ss : Bytes} {σ : State Enc Dec}
    (h : initBobO Q ss = some σ) : initBob P ss = σ := by
  simp only [initBobO, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨a, ha, rfl⟩ := h
  simp only [initBob, Auth.initO_sound hA ha, hA.decoderNew, hA.headerSize, hA.macSize]

end Soundness

end BraidModel
