/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Lacramioara Astefanoaei
-/
module

public import Aeneas
public meta import Spqr.Auxiliary.SpecTags
public import Spqr.Specs.Braid.Deviations

/-! # An abstract ML-KEM Braid machine

The state machine of [ML-KEM Braid] §2.5 and §2.6, written over the values each state holds.
The primitives are parameters (`Prims`): the incremental KEM of §1.2, and the erasure code,
`MAC`, `PROTOCOL_INFO`, `ToBytes`, `KDF_AUTH` and `KDF_OK` of §2.2. The authenticator of §2.4 is
built from them. Where the code differs from §2.5 (`Deviation`, `Deviations.lean`), the machine
follows the code, and the arm names the deviation.

`send` takes the randomness that §1.2 gives `KeyGen` and `Encaps1`. `receive` returns `none` for
a failure of §2.5 (`FAIL` in `VfyHdr` or `VfyCt`, the `ek` integrity error) and for a message
from a later epoch. `Step` is one step of one party, and `Run` is a sequence of steps.

**Source**: ML-KEM Braid Rev. 1, §1.2, §2.2–§2.6 -/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace Braid

/-- A byte string. The model gives bytes no structure beyond concatenation and splitting. -/
abbrev Bytes := List Std.U8

/-- The bytes of an ASCII string, for the labels of §2.4. -/
def ascii (s : String) : Bytes := s.toList.map (fun c => ⟨BitVec.ofNat 8 c.toNat⟩)

/-- The primitives that ML-KEM Braid takes as parameters: the erasure code of §2.2, the
incremental KEM of §1.2 with its constants, and `MAC`, `PROTOCOL_INFO`, `ToBytes`, `KDF_AUTH`
and `KDF_OK` of §2.2. `Enc`, `Dec` and `Chunk` are the types of encoders, decoders and
codewords. `message d` is `d.message()` when `d.has_message()` holds, and `none` otherwise. -/
structure Prims (Enc Dec Chunk : Type) where
  /-- `Encode(byte_array) → encoder` -/
  encode : Bytes → Enc
  /-- `encoder.next_chunk()`, with the encoder after the call -/
  nextChunk : Enc → Chunk × Enc
  /-- `Decoder.new(message_size)` -/
  decoderNew : Nat → Dec
  /-- `decoder.add_chunk(chunk)`, with the decoder after the call -/
  addChunk : Dec → Chunk → Dec
  /-- `decoder.message()` when `decoder.has_message()` holds, and `none` otherwise -/
  message : Dec → Option Bytes
  /-- `KeyGen(randomness) → (dk, ek_header, ek_vector)` -/
  keyGen : Bytes → Bytes × Bytes × Bytes
  /-- `Encaps1(ek_header, randomness) → (encaps_secret, ct1, shared_secret)` -/
  encaps1 : Bytes → Bytes → Bytes × Bytes × Bytes
  /-- `Encaps2(encaps_secret, ek_header, ek_vector) → ct2` -/
  encaps2 : Bytes → Bytes → Bytes → Bytes
  /-- `Decaps(dk, ct1, ct2) → shared_secret` -/
  decaps : Bytes → Bytes → Bytes → Bytes
  /-- The integrity check of `ek_vector` against `ek_header`. In §1.2.1 and §2.5 it is
  `SHA3-256(ek_seed || ek_vector) = hek`. -/
  ekMatches : Bytes → Bytes → Bool
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
  /-- `MAC(mac_key, msg)` -/
  mac : Bytes → Bytes → Bytes
  /-- `PROTOCOL_INFO` -/
  protocolInfo : Bytes
  /-- `ToBytes(epoch)` -/
  toBytes : Nat → Bytes
  /-- `KDF_AUTH(root_key, update_key, epoch)`, 64 bytes. -/
  kdfAuth : Bytes → Bytes → Nat → Bytes
  /-- `KDF_OK(shared_secret, epoch)`, 32 bytes. -/
  kdfOk : Bytes → Nat → Bytes

variable {Enc Dec Chunk : Type}

/-- The Ratcheted Authenticator state of §2.4. -/
structure Auth where
  /-- `root_key` -/
  rootKey : Bytes
  /-- `mac_key` -/
  macKey : Bytes

/-- `Authenticator.Update` (§2.4): the 64 bytes of `KDF_AUTH` are the new `root_key` and
`mac_key`. -/
def Auth.update (P : Prims Enc Dec Chunk) (a : Auth) (epoch : Nat) (key : Bytes) : Auth :=
  let out := P.kdfAuth a.rootKey key epoch
  { rootKey := out.take 32, macKey := out.drop 32 }

/-- `Authenticator.Init` (§2.4): a zero `root_key`, then `Update`. -/
def Auth.init (P : Prims Enc Dec Chunk) (epoch : Nat) (key : Bytes) : Auth :=
  Auth.update P { rootKey := List.replicate 32 0#u8, macKey := [] } epoch key

/-- `Authenticator.MacHdr` (§2.4). -/
def Auth.macHdr (P : Prims Enc Dec Chunk) (a : Auth) (epoch : Nat) (hdr : Bytes) : Bytes :=
  P.mac a.macKey (P.protocolInfo ++ ascii ":ekheader" ++ P.toBytes epoch ++ hdr)

/-- `Authenticator.MacCt` (§2.4). -/
def Auth.macCt (P : Prims Enc Dec Chunk) (a : Auth) (epoch : Nat) (ct : Bytes) : Bytes :=
  P.mac a.macKey (P.protocolInfo ++ ascii ":ciphertext" ++ P.toBytes epoch ++ ct)

/-- The eleven states of §2.5 with the variables each one holds. `hdr` is the §1.2
`ek_header`, which for ML-KEM is `ek_seed || hek`. -/
inductive State (Enc Dec : Type) where
  | keysUnsampled (epoch : Nat) (auth : Auth)
  | keysSampled (epoch : Nat) (auth : Auth) (dk hdr ek : Bytes) (headerEncoder : Enc)
  | headerSent (epoch : Nat) (auth : Auth) (dk : Bytes) (ct1Decoder : Dec) (ekEncoder : Enc)
  | ct1Received (epoch : Nat) (auth : Auth) (dk ct1 : Bytes) (ekEncoder : Enc)
  | ekSentCt1Received (epoch : Nat) (auth : Auth) (dk ct1 : Bytes) (ct2Decoder : Dec)
  | noHeaderReceived (epoch : Nat) (auth : Auth) (headerDecoder : Dec)
  | headerReceived (epoch : Nat) (auth : Auth) (hdr : Bytes) (ekDecoder : Dec)
  | ct1Sampled (epoch : Nat) (auth : Auth) (hdr encapsSecret ct1 : Bytes) (ct1Encoder : Enc)
      (ekDecoder : Dec)
  | ekReceivedCt1Sampled (epoch : Nat) (auth : Auth) (encapsSecret ct1 hdr ek : Bytes)
      (ct1Encoder : Enc)
  | ct1Acknowledged (epoch : Nat) (auth : Auth) (hdr encapsSecret ct1 : Bytes) (ekDecoder : Dec)
  | ct2Sampled (epoch : Nat) (auth : Auth) (ct2Encoder : Enc)

/-- The epoch every state holds. -/
def State.epoch : State Enc Dec → Nat
  | .keysUnsampled e .. | .keysSampled e .. | .headerSent e .. | .ct1Received e ..
  | .ekSentCt1Received e .. | .noHeaderReceived e .. | .headerReceived e ..
  | .ct1Sampled e .. | .ekReceivedCt1Sampled e .. | .ct1Acknowledged e .. | .ct2Sampled e .. => e

/-- The message types of §2.3. `ct1Ack` has no payload. -/
inductive Payload (Chunk : Type) where
  | none
  | hdr (c : Chunk)
  | ek (c : Chunk)
  | ekCt1Ack (c : Chunk)
  | ct1Ack
  | ct1 (c : Chunk)
  | ct2 (c : Chunk)

/-- A message of §2.3. -/
structure Msg (Chunk : Type) where
  /-- The epoch being negotiated. -/
  epoch : Nat
  /-- The message type and its chunk. -/
  payload : Payload Chunk

/-- An output key `(epoch, shared_secret)`. -/
abbrev Key := Nat × Bytes

/-- The `ct2` encoder of transitions (9), (11) and (12): `Encode(ct2 || mac)` with
`ct2 = KEM.Encaps2(encaps_secret, ek_header, ek_vector)` and `mac = MacCt(epoch, ct1 || ct2)`. -/
def ct2Encoder (P : Prims Enc Dec Chunk) (epoch : Nat) (auth : Auth)
    (encapsSecret ct1 hdr ek : Bytes) : Enc :=
  let ct2 := P.encaps2 encapsSecret hdr ek
  P.encode (ct2 ++ Auth.macCt P auth epoch (ct1 ++ ct2))

/-- `Send()` of §2.5 with `Deviation.ct1AckAccepted` applied. `r` is the randomness that
`KeyGen` (transition (1)) and `Encaps1` (transition (7)) take in §1.2; the other states ignore
it. The result is the new state, the message and the output key. -/
@[braid_deviation Deviation.ct1AckAccepted]
def send (P : Prims Enc Dec Chunk) (σ : State Enc Dec) (r : Bytes) :
    State Enc Dec × Msg Chunk × Option Key :=
  match σ with
  | .keysUnsampled e a =>
    let (dk, hdr, ek) := P.keyGen r
    let (c, enc) := P.nextChunk (P.encode (hdr ++ Auth.macHdr P a e hdr))
    (.keysSampled e a dk hdr ek enc, ⟨e, .hdr c⟩, none)                              -- (1)
  | .keysSampled e a dk hdr ek enc =>
    let (c, enc') := P.nextChunk enc
    (.keysSampled e a dk hdr ek enc', ⟨e, .hdr c⟩, none)
  | .headerSent e a dk d enc =>
    let (c, enc') := P.nextChunk enc
    (.headerSent e a dk d enc', ⟨e, .ek c⟩, none)
  | .ct1Received e a dk ct1 enc =>
    let (c, enc') := P.nextChunk enc
    (.ct1Received e a dk ct1 enc', ⟨e, .ekCt1Ack c⟩, none)
  | .ekSentCt1Received e a dk ct1 d =>
    -- Deviation.ct1AckAccepted: §2.5 sends a message of type `None`.
    (.ekSentCt1Received e a dk ct1 d, ⟨e, .ct1Ack⟩, none)
  | .noHeaderReceived e a d => (.noHeaderReceived e a d, ⟨e, .none⟩, none)
  | .headerReceived e a hdr d =>
    let (es, ct1, ss₀) := P.encaps1 hdr r
    let ss := P.kdfOk ss₀ e
    let a' := Auth.update P a e ss
    let (c, enc) := P.nextChunk (P.encode ct1)
    (.ct1Sampled e a' hdr es ct1 enc d, ⟨e, .ct1 c⟩, some (e, ss))                   -- (7)
  | .ct1Sampled e a hdr es ct1 enc d =>
    let (c, enc') := P.nextChunk enc
    (.ct1Sampled e a hdr es ct1 enc' d, ⟨e, .ct1 c⟩, none)
  | .ekReceivedCt1Sampled e a es ct1 hdr ek enc =>
    let (c, enc') := P.nextChunk enc
    (.ekReceivedCt1Sampled e a es ct1 hdr ek enc', ⟨e, .ct1 c⟩, none)
  | .ct1Acknowledged e a hdr es ct1 d => (.ct1Acknowledged e a hdr es ct1 d, ⟨e, .none⟩, none)
  | .ct2Sampled e a enc =>
    let (c, enc') := P.nextChunk enc
    (.ct2Sampled e a enc', ⟨e, .ct2 c⟩, none)

/-- `Receive()` of §2.5 for a message from the state's own epoch, with `Deviation.ct1AckAccepted`
and `Deviation.lateEkChunk` applied. `none` is a failure of §2.5 (`FAIL` in `VfyHdr` / `VfyCt`, or
the `ek` integrity error). A message the state does not act on leaves it unchanged. -/
@[braid_deviation Deviation.ct1AckAccepted Deviation.lateEkChunk]
def receiveEq (P : Prims Enc Dec Chunk) : State Enc Dec → Payload Chunk →
    Option (State Enc Dec × Option Key)
  | .keysSampled e a dk _ ek _, .ct1 c =>
    some (.headerSent e a dk (P.addChunk (P.decoderNew P.ct1Size) c) (P.encode ek), none) -- (2)
  | .headerSent e a dk d enc, .ct1 c =>
    let d' := P.addChunk d c
    match P.message d' with
    | some ct1 => some (.ct1Received e a dk ct1 enc, none)                               -- (3)
    | none => some (.headerSent e a dk d' enc, none)
  | .ct1Received e a dk ct1 _, .ct2 c =>
    some (.ekSentCt1Received e a dk ct1
      (P.addChunk (P.decoderNew (P.ct2Size + P.macSize)) c), none)                        -- (4)
  | .ekSentCt1Received e a dk ct1 d, .ct2 c =>
    let d' := P.addChunk d c
    match P.message d' with
    | none => some (.ekSentCt1Received e a dk ct1 d', none)
    | some m =>
      let ct2 := m.take P.ct2Size
      let ss := P.kdfOk (P.decaps dk ct1 ct2) e
      let a' := Auth.update P a e ss
      if m.drop P.ct2Size = Auth.macCt P a' e (ct1 ++ ct2) then
        some (.noHeaderReceived (e + 1) a' (P.decoderNew (P.headerSize + P.macSize)),
          some (e, ss))                                                                   -- (5)
      else none
  | .noHeaderReceived e a d, .hdr c =>
    let d' := P.addChunk d c
    match P.message d' with
    | none => some (.noHeaderReceived e a d', none)
    | some m =>
      let hdr := m.take P.headerSize
      if m.drop P.headerSize = Auth.macHdr P a e hdr then
        some (.headerReceived e a hdr (P.decoderNew P.ekSize), none)                      -- (6)
      else none
  | .ct1Sampled e a hdr es ct1 enc d, .ek c =>
    let d' := P.addChunk d c
    match P.message d' with
    | none => some (.ct1Sampled e a hdr es ct1 enc d', none)
    | some ek =>
      if P.ekMatches hdr ek then some (.ekReceivedCt1Sampled e a es ct1 hdr ek enc, none) -- (10)
      else none
  | .ct1Sampled e a hdr es ct1 _ d, .ekCt1Ack c =>
    let d' := P.addChunk d c
    match P.message d' with
    | none => some (.ct1Acknowledged e a hdr es ct1 d', none)                             -- (8)
    | some ek =>
      if P.ekMatches hdr ek then
        some (.ct2Sampled e a (ct2Encoder P e a es ct1 hdr ek), none)                     -- (9)
      else none
  | .ekReceivedCt1Sampled e a es ct1 hdr ek _, .ekCt1Ack _ =>
    some (.ct2Sampled e a (ct2Encoder P e a es ct1 hdr ek), none)                         -- (12)
  | .ekReceivedCt1Sampled e a es ct1 hdr ek _, .ct1Ack =>
    -- Deviation.ct1AckAccepted: §2.5 acts only on `EkCt1Ack` here.
    some (.ct2Sampled e a (ct2Encoder P e a es ct1 hdr ek), none)                         -- (12)
  | .ct1Acknowledged e a hdr es ct1 d, .ekCt1Ack c =>
    let d' := P.addChunk d c
    match P.message d' with
    | none => some (.ct1Acknowledged e a hdr es ct1 d', none)
    | some ek =>
      if P.ekMatches hdr ek then
        some (.ct2Sampled e a (ct2Encoder P e a es ct1 hdr ek), none)                     -- (11)
      else none
  | .ct1Acknowledged e a hdr es ct1 d, .ek c =>
    -- Deviation.lateEkChunk: §2.5 acts only on `EkCt1Ack` here.
    let d' := P.addChunk d c
    match P.message d' with
    | none => some (.ct1Acknowledged e a hdr es ct1 d', none)
    | some ek =>
      if P.ekMatches hdr ek then
        some (.ct2Sampled e a (ct2Encoder P e a es ct1 hdr ek), none)                     -- (11)
      else none
  | σ, _ => some (σ, none)

/-- `Receive()` of §2.5 with `Deviation.futureEpochError` applied: a message from a later epoch is
a failure, except in `Ct2Sampled` at `epoch + 1` (transition (13)). A message from an earlier
epoch leaves the state unchanged. -/
@[braid_deviation Deviation.futureEpochError]
def receive (P : Prims Enc Dec Chunk) (σ : State Enc Dec) (m : Msg Chunk) :
    Option (State Enc Dec × Option Key) :=
  match σ with
  | .ct2Sampled e a _ =>
    if m.epoch = e + 1 then some (.keysUnsampled (e + 1) a, none)                         -- (13)
    else if m.epoch > e then none
    else some (σ, none)
  | _ =>
    if m.epoch > σ.epoch then none
    else if m.epoch < σ.epoch then some (σ, none)
    else receiveEq P σ m.payload

/-- `InitAlice` (§2.6). -/
def initAlice (P : Prims Enc Dec Chunk) (sharedSecret : Bytes) : State Enc Dec :=
  .keysUnsampled 1 (Auth.init P 1 sharedSecret)

/-- `InitBob` (§2.6). -/
def initBob (P : Prims Enc Dec Chunk) (sharedSecret : Bytes) : State Enc Dec :=
  .noHeaderReceived 1 (Auth.init P 1 sharedSecret) (P.decoderNew (P.headerSize + P.macSize))

/-- One step of one party: a `Send()` with some randomness, or a `Receive()` of some message
that does not fail. -/
inductive Step (P : Prims Enc Dec Chunk) : State Enc Dec → State Enc Dec → Option Key → Prop
  | send (σ : State Enc Dec) (r : Bytes) : Step P σ (send P σ r).1 (send P σ r).2.2
  | recv (σ σ' : State Enc Dec) (m : Msg Chunk) (k : Option Key) :
      receive P σ m = some (σ', k) → Step P σ σ' k

/-- A run of one party from `σ` to `σ'` that emits the keys `ks`, in order. -/
inductive Run (P : Prims Enc Dec Chunk) : State Enc Dec → State Enc Dec → List Key → Prop
  | nil (σ : State Enc Dec) : Run P σ σ []
  | cons {σ σ₁ σ₂ : State Enc Dec} {k : Option Key} {ks : List Key} :
      Step P σ σ₁ k → Run P σ₁ σ₂ ks → Run P σ σ₂ (k.toList ++ ks)

end Braid
