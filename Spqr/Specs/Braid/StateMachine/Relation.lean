/-
Copyright (c) 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Lacramioara Astefanoaei
-/
module

public import SrcTranslated.Funs
public import SrcTranslated.FunsExternal
public import Spqr.Crypto.Hkdf
public import Spqr.Specs.Authenticator.Authenticator.Update
public import Spqr.Specs.V1.Unchunked.SendCt.HeaderReceived.SendCt1
public import Spqr.Specs.Braid.StateMachine.Model

/-! # The relation between the chunked `States` machine and the abstract ML-KEM Braid machine

The refinement theorems of `Refinement.lean` are stated with the definitions of this module:

* `CodeAgrees P`: each primitive of `P : CodePrims` returns what the code's function returns
  wherever that function succeeds;
* `absAuth`, `absMsg` and `absKey`: the model's authenticator, message and key for the code's;
* `Refines s σ`: a code state `s` and a machine state `σ` are the same state with equal values,
  and `s` has the sizes of the last section.

## The sizes in `Refines`

`util::compare` loops over the length of its first argument only, and `verify_hdr` and
`verify_ct` pass the received MAC as that argument, so a short received MAC is compared as a
prefix. The HMAC contract `hmac_sha256_tag32_spec` gives a 32-byte tag only for keys and data of
at most `U32.max` bytes. Without sizes, `recv_refines` is false: a `ct2` decoder of 65 points
gives a 130-byte message with a 2-byte MAC, which the code can accept and the machine rejects.

`Refines` therefore requires the sizes that the code's constructors give: 480 points for the
`ct1` decoder, 960 bytes for a received `ct1`, 80 points for the `ct2` decoder, 48 points for the
header decoder, and a 32-byte MAC key in `NoHeaderReceived`. `init_refines`, `send_refines` and
`recv_refines` establish each size where the state is built, so every state reached from
`init_a` or `init_b` has them. A state restored from bytes is not covered.

**Source**: ML-KEM Braid Rev. 1, §1.2, §2.2–§2.6; spqr/src/v1/chunked/states.rs:56-533 -/

@[expose] public section

open Aeneas Aeneas.Std Result spqr

namespace spqr.v1.chunked.states

open Braid

/-- The primitives of the code: encoders, decoders and codewords are `PolyEncoder`,
`PolyDecoder` and `encoding.Chunk`. -/
abbrev CodePrims := Prims encoding.polynomial.PolyEncoder encoding.polynomial.PolyDecoder
  encoding.Chunk

/-- `P` agrees with the code: each primitive returns what the code's function returns wherever
that function succeeds. `KDF_AUTH` and `KDF_OK` are the code's HKDF calls, with salt
`[0u8; 32]`; for `KDF_AUTH` the key is `root_key ‖ update_key`. `PROTOCOL_INFO` is the code's
label `Signal_PQCKA_V1_MLKEM768`. The `ek` check is the code's `ek_matches_header`, which calls
libcrux `validate_pk_bytes`: it hashes `ek_vector ‖ ek_seed`, not `ek_seed ‖ ek_vector` as in
§2.5, and also checks the input lengths and that `ek_vector` is a canonical encoding. Every
output of the code's `generate` and `encaps1` is an output of `KeyGen` and `Encaps1` for some
randomness. -/
structure CodeAgrees (P : CodePrims) : Prop where
  encode : ∀ (msg : Slice Std.U8) (e : encoding.polynomial.PolyEncoder),
    encoding.polynomial.PolyEncoder.Insts.SpqrEncodingEncoder.encode_bytes msg = ok (.Ok e) →
    P.encode msg.val = e
  nextChunk : ∀ (e e' : encoding.polynomial.PolyEncoder) (c : encoding.Chunk),
    encoding.polynomial.PolyEncoder.Insts.SpqrEncodingEncoder.next_chunk e = ok (c, e') →
    P.nextChunk e = (c, e')
  decoderNew : ∀ (n : Std.Usize) (d : encoding.polynomial.PolyDecoder),
    encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.new n = ok (.Ok d) →
    P.decoderNew n.val = d
  addChunk : ∀ (d d' : encoding.polynomial.PolyDecoder) (c : encoding.Chunk),
    encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk d c = ok d' →
    P.addChunk d c = d'
  message : ∀ (d : encoding.polynomial.PolyDecoder) (m : Option (alloc.vec.Vec Std.U8)),
    encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.decoded_message d = ok m →
    P.message d = m.map (·.val)
  keyGen : ∀ {R : Type} (i₁ : rand_1.rng.Rng R) (i₂ : rand_core_1.CryptoRng R) (rng rng' : R)
    (k : incremental_mlkem768.Keys),
    incremental_mlkem768.generate i₁ i₂ rng = ok (k, rng') →
    ∃ r, P.keyGen r = (k.dk.val, k.hdr.val, k.ek.val)
  encaps1 : ∀ {R : Type} (i₁ : rand_1.rng.Rng R) (i₂ : rand_core_1.CryptoRng R) (rng rng' : R)
    (hdr ct1 es ss : alloc.vec.Vec Std.U8),
    incremental_mlkem768.encaps1 i₁ i₂ hdr rng = ok ((ct1, es, ss), rng') →
    ∃ r, P.encaps1 hdr.val r = (es.val, ct1.val, ss.val)
  encaps2 : ∀ (ek es ct2 : alloc.vec.Vec Std.U8) (hdr : Bytes),
    incremental_mlkem768.encaps2 ek es = ok ct2 → P.encaps2 es.val hdr ek.val = ct2.val
  decaps : ∀ (dk ct1 ct2 ss : alloc.vec.Vec Std.U8),
    incremental_mlkem768.decaps dk ct1 ct2 = ok ss → P.decaps dk.val ct1.val ct2.val = ss.val
  ekMatches : ∀ (ek hdr : alloc.vec.Vec Std.U8) (b : Bool),
    incremental_mlkem768.ek_matches_header ek hdr = ok b → P.ekMatches hdr.val ek.val = b
  headerSize : ∀ n, incremental_mlkem768.HEADER_SIZE = ok n → P.headerSize = n.val
  ekSize : ∀ n, incremental_mlkem768.ENCAPSULATION_KEY_SIZE = ok n → P.ekSize = n.val
  ct1Size : ∀ n, incremental_mlkem768.CIPHERTEXT1_SIZE = ok n → P.ct1Size = n.val
  ct2Size : ∀ n, incremental_mlkem768.CIPHERTEXT2_SIZE = ok n → P.ct2Size = n.val
  macSize : P.macSize = authenticator.Authenticator.MACSIZE.val
  mac : ∀ (key data : Slice Std.U8) (t : alloc.vec.Vec Std.U8),
    libcrux_hmac.hmac .Sha256 key data (some 32#usize) = ok t → P.mac key.val data.val = t.val
  protocolInfo : P.protocolInfo = ascii "Signal_PQCKA_V1_MLKEM768"
  toBytes : ∀ ep : Std.U64, P.toBytes ep.val = (core.num.U64.to_be_bytes ep).val
  kdfAuth : ∀ (rootKey key : Bytes) (ep : Std.U64),
    P.kdfAuth rootKey key ep.val = crypto.hkdf (List.replicate 32 0#u8) (rootKey ++ key)
      (authenticator.Authenticator.updateLabel ++ (core.num.U64.to_be_bytes ep).val) 64
  kdfOk : ∀ (ss : Bytes) (ep : Std.U64),
    P.kdfOk ss ep.val = crypto.hkdf (List.replicate 32 0#u8) ss
      (Spqr.V1.Unchunked.SendCt.sckaKeyLabel ++ (core.num.U64.to_be_bytes ep).val) 32

/-- The model's authenticator for the code's. -/
def absAuth (a : authenticator.Authenticator) : Auth := ⟨a.root_key.val, a.mac_key.val⟩

/-- The model's message for the code's. `Ct1Ack false` is not an acknowledgement: it maps to a
`None` payload. -/
def absMsg (m : Message) : Msg encoding.Chunk :=
  ⟨m.epoch.val, match m.payload with
    | .None => .none
    | .Hdr c => .hdr c
    | .Ek c => .ek c
    | .EkCt1Ack c => .ekCt1Ack c
    | .Ct1Ack true => .ct1Ack
    | .Ct1Ack false => .none
    | .Ct1 c => .ct1 c
    | .Ct2 c => .ct2 c⟩

/-- The model's key for the code's. -/
def absKey (k : EpochSecret) : Key := (k.epoch.val, k.secret.val)

/-- `Refines s σ`: `s` and `σ` are the same §2.5 state with equal epoch, authenticator, byte
values, encoders and decoders. The model's `ek_header` in `KeysSampled` and
`EkReceivedCt1Sampled` is free: the code does not keep it there. `s` also has these sizes: the
`ct1` decoder needs 480 points, a received `ct1` has 960 bytes, the `ct2` decoder needs 80
points, the header decoder needs 48 points, and the MAC key of `NoHeaderReceived` has 32
bytes. -/
def Refines : States →
    State encoding.polynomial.PolyEncoder encoding.polynomial.PolyDecoder → Prop
  | .KeysUnsampled s, .keysUnsampled e a =>
    s.uc.epoch.val = e ∧ absAuth s.uc.auth = a
  | .KeysSampled s, .keysSampled e a dk _ ek enc =>
    s.uc.epoch.val = e ∧ absAuth s.uc.auth = a ∧ s.uc.dk.val = dk ∧ s.uc.ek.val = ek ∧
      s.sending_hdr = enc
  | .HeaderSent s, .headerSent e a dk d enc =>
    s.uc.epoch.val = e ∧ absAuth s.uc.auth = a ∧ s.uc.dk.val = dk ∧ s.receiving_ct1 = d ∧
      s.sending_ek = enc ∧ s.receiving_ct1.pts_needed.val = 480
  | .Ct1Received s, .ct1Received e a dk ct1 enc =>
    s.uc.epoch.val = e ∧ absAuth s.uc.auth = a ∧ s.uc.dk.val = dk ∧ s.uc.ct1.val = ct1 ∧
      s.sending_ek = enc ∧ s.uc.ct1.length = 960
  | .EkSentCt1Received s, .ekSentCt1Received e a dk ct1 d =>
    s.uc.epoch.val = e ∧ absAuth s.uc.auth = a ∧ s.uc.dk.val = dk ∧ s.uc.ct1.val = ct1 ∧
      s.receiving_ct2 = d ∧ s.uc.ct1.length = 960 ∧ s.receiving_ct2.pts_needed.val = 80
  | .NoHeaderReceived s, .noHeaderReceived e a d =>
    s.uc.epoch.val = e ∧ absAuth s.uc.auth = a ∧ s.receiving_hdr = d ∧
      s.uc.auth.mac_key.length = 32 ∧ s.receiving_hdr.pts_needed.val = 48
  | .HeaderReceived s, .headerReceived e a hdr d =>
    s.uc.epoch.val = e ∧ absAuth s.uc.auth = a ∧ s.uc.hdr.val = hdr ∧ s.receiving_ek = d
  | .Ct1Sampled s, .ct1Sampled e a hdr es ct1 enc d =>
    s.uc.epoch.val = e ∧ absAuth s.uc.auth = a ∧ s.uc.hdr.val = hdr ∧ s.uc.es.val = es ∧
      s.uc.ct1.val = ct1 ∧ s.sending_ct1 = enc ∧ s.receiving_ek = d
  | .EkReceivedCt1Sampled s, .ekReceivedCt1Sampled e a es ct1 _ ek enc =>
    s.uc.epoch.val = e ∧ absAuth s.uc.auth = a ∧ s.uc.es.val = es ∧ s.uc.ct1.val = ct1 ∧
      s.uc.ek.val = ek ∧ s.sending_ct1 = enc
  | .Ct1Acknowledged s, .ct1Acknowledged e a hdr es ct1 d =>
    s.uc.epoch.val = e ∧ absAuth s.uc.auth = a ∧ s.uc.hdr.val = hdr ∧ s.uc.es.val = es ∧
      s.uc.ct1.val = ct1 ∧ s.receiving_ek = d
  | .Ct2Sampled s, .ct2Sampled e a enc =>
    s.uc.epoch.val = e ∧ absAuth s.uc.auth = a ∧ s.sending_ct2 = enc
  | _, _ => False

end spqr.v1.chunked.states
