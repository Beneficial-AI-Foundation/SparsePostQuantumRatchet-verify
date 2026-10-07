# Proposal: compositional specs for the "group C" `= ok` statements

**Context.** Aeneas `nightly-2026.10.07` removed `WP.spec_imp_exists`/`exists_imp_spec`
(aeneas#1384). We re-prove them in `Spqr/Auxiliary/Aeneas/SpecImpExists.lean` as a temporary shim.
Groups A/B (proofs only) are being migrated now. Group C is different: the `= ok` equation is part
of a **statement**, so migrating means restating specs. This document proposes the new statements
for review before anything is written.

**Principle.** A spec should say what the result *is*, through a pure model, rather than "the result
equals what this other computation returns":

```lean
-- equational style (to remove)
f x ⦃ r => g y = ok r ⦄
-- compositional style
f x ⦃ r => r.val = model y ⦄     -- and separately: g y ⦃ r => r.val = model y ⦄
```

Two specs that agree on `model` compose by `step`, with no equations between computations. This
is the same pattern `hkdf_to_slice_spec` already uses (`out.val = hkdf …`).

---

## C1. HMAC / authenticator chain

**Today**
- `libcrux_hmac.hmac_sha256_tag32_spec` (axiom in `SrcTranslated/FunsExternal.lean`) only states
  `r.length = 32`.
- So `mac_ct_spec`/`mac_hdr_spec` describe the tag's value indirectly:
  `hmac .Sha256 self.mac_key.deref data (some MACSIZE) = ok result`. They need `refl_of%`
  (`SpecRefl.lean`) to produce that equation.
- `verify_ct_spec`/`verify_hdr_spec` state `result = Ok () ↔ mac_ct self ep ct = ok { slice := expected_mac }`.
  The `{ slice := … }` was itself a forced change in the last Aeneas update.

**Proposed**

1. **Byte-level model.** `Spqr/Crypto/Hkdf.lean` already has the opaque primitive
   `crypto.HMAC_SHA256 (key data : List UInt8) : {l // l.length = 32}`. Add a byte-level wrapper next
   to `hkdf`:
   ```lean
   /-- HMAC-SHA256 over Aeneas bytes. -/
   noncomputable def hmacSha256 (key data : List U8) : List U8 := …  -- via HMAC_SHA256, mapping U8 ↔ UInt8
   theorem hmacSha256_length (key data : List U8) : (hmacSha256 key data).length = 32
   ```
2. **Strengthen the trusted axiom** and move it out of `FunsExternal.lean`. It must live in `Spqr/`,
   because `Spqr/Crypto` imports `SrcTranslated`. Proposed location `Spqr/Specs/Libcrux/Hmac.lean`,
   next to how `hkdf_to_slice_spec` is placed:
   ```lean
   @[step]
   axiom libcrux_hmac.hmac_sha256_spec (key data : Slice U8)
       (hkey : key.length ≤ U32.max) (hdata : data.length ≤ U32.max) :
       libcrux_hmac.hmac .Sha256 key data (some 32#usize)
         ⦃ (r : alloc.vec.Vec U8) => r.val = hmacSha256 key.val data.val ⦄
   ```
   This is the same trust level as the HKDF axiom: we trust that libcrux (HACL\*-verified) computes
   HMAC-SHA256. It subsumes the current length-only axiom, since length follows from
   `hmacSha256_length`.
3. **Restate the authenticator specs:**
   ```lean
   theorem mac_ct_spec … :
       mac_ct self ep ct ⦃ (result : alloc.vec.Vec U8) =>
         result.val = hmacSha256 self.mac_key.val (MAC_CT_LABEL ++ to_be_bytes ep ++ ct.val) ⦄
   theorem verify_ct_spec … (h_mac : expected_mac.length = MACSIZE.val) :
       verify_ct self ep ct expected_mac ⦃ (result : core.result.Result Unit Error) =>
         result = Ok () ↔
           expected_mac.val = hmacSha256 self.mac_key.val (MAC_CT_LABEL ++ to_be_bytes ep ++ ct.val) ⦄
   ```
   `mac_hdr_spec`/`verify_hdr_spec` follow the same pattern. `result.length = MACSIZE` becomes a
   corollary (or stays as an extra conjunct if callers use it).

**Effects**
- `SpecRefl.lean` (`spec_refl`, `refl_of%`) is no longer needed: its only users are these four files.
- The `.deref` and `{ slice := … }` forms in these statements disappear. Statements become about byte
  lists only.
- This is a strictly stronger, more useful spec: callers learn what the tag *is*.

**Questions for you**
- (a) OK to strengthen the HMAC trust assumption from "length 32" to "is HMAC-SHA256"? It matches
  the HKDF axiom.
- (b) Name and location of the model (`crypto.hmacSha256` in `Hkdf.lean`, or a new `Spqr/Crypto/Hmac.lean`)?
- (c) Keep a `result.length = 32` conjunct in `mac_*_spec` for convenience, or derive it?

---

## C2. Sorted insertion: `sortedInsert`, `SortedSet.push`, `Pt` comparison

**Today**
- `Ord` comparison is a computation: `cmpOrdInst.cmp a b : Result Ordering`.
- `SortedSet.push_spec_gt/eq/lt` (`FunsExternal.lean`) take `hcmp : cmpOrdInst.cmp x last = ok .gt`.
- `push_spec_lt` additionally takes `hsorted : sortedInsert cmpOrdInst s.val x 0 = ok (idx, opt, newList)`.
- `sortedInsert_spec` takes `h : sortedInsert … = ok (idx, opt, newList)` and characterizes `newList`.
- To discharge those premises, `PolyDecoder/FromPb.lean` proves `cmp_eq : Pt.cmp a b = ok (compare …)`
  and `sortedInsert_always_ok : ∃ idx opt newList, sortedInsert … = ok (…)`. `AddChunk.lean`
  reuses both.
- The 8 `from_pb` specs match on `(Pt.Insts.CoreCmpOrd.cmp p last).match` with `| _ => False`,
  another forced change from the last update.

**Proposed**

1. **Pure comparator.** Generic lemmas get a pure comparison function plus a spec tying the `Ord`
   instance to it:
   ```lean
   /-- `cmpOrdInst.cmp` never fails and agrees with the pure `cmp`. -/
   def Ord.IsPure (cmpOrdInst : core.cmp.Ord T) (cmp : T → T → Ordering) : Prop :=
     ∀ a b, cmpOrdInst.cmp a b ⦃ o => o = cmp a b ⦄
   ```
   For `Pt`, this is exactly the existing `Pt.Insts.CoreCmpOrd.cmp_spec`, with
   `cmp a b = compare a.x.value.val b.x.value.val`.
2. **Pure model of insertion**, mirroring `sortedInsert` line by line:
   ```lean
   def sortedInsertModel (cmp : T → T → Ordering) : List T → T → Nat → Nat × Option T × List T
   ```
   The current `∃ k, idx = i + k ∧ …take/drop…` characterization becomes a pure lemma about
   `sortedInsertModel`.
3. **Restate the external specs:**
   ```lean
   theorem sortedInsert_spec (h : Ord.IsPure cmpOrdInst cmp) :
       sortedInsert cmpOrdInst list x i ⦃ r => r = sortedInsertModel cmp list x i ⦄
   theorem push_spec_lt … (h : Ord.IsPure cmpOrdInst cmp) (hcmp : cmp x last = .lt) :
       push cmpOrdInst s x ⦃ ((n, o), s') =>
         (n.val, o, s'.val) = sortedInsertModel cmp s.val x 0 ⦄
   ```
   `push_spec_gt/eq` similarly take `hcmp : cmp x last = .gt/.eq`. Ideally a single
   `push_spec (h : Ord.IsPure …)` covers all four branches with
   `match s.val.getLast?, … cmp x last`, so `step*` needs no branch-picking. That fixes the
   "`step*` picks the generic `push_spec`" problem seen in `AddChunk`.
4. **`from_pb` statements** (`PolyDecoder/FromPb.lean`): `match (Pt.cmp p last).match with … | _ => False`
   becomes `match compare p.x.value.val last.x.value.val with …`, with no failure branch.
   `cmp_eq` and `sortedInsert_always_ok` are deleted.

**Effects**
- No `= ok` premises remain anywhere in the sorted-set API.
- The `.match`/`False` workaround in the `from_pb` specs goes away.
- Statements change in `FunsExternal.lean` (5 push/insert specs), `PolyDecoder/FromPb.lean` (8 specs
  plus helpers) and `PolyDecoder/AddChunk.lean` (helpers).
- Note that `sorted_vec` is an external crate we model by hand. `sortedInsertModel` describes our
  model, which approximates `SortedVec::replace` (binary search) by a linear scan, as today.

**Questions for you**
- (d) OK to introduce `Ord.IsPure`, or would you rather specialise everything to `Pt` (simpler,
  less reusable)?
- (e) One combined `push_spec`, or keep the four branch specs (`empty/gt/eq/lt`)?

---

## C3. `chain_from_version_negotiation_spec`

**Today.** The statement uses equation premises and an equation conclusion:
`try_from vn.direction = ok (.Ok dir) → vn.chain_params = some params → Chain.new … = ok result`.
Its proof deliberately avoids `step*` through `Chain.new`, to keep that equation.

**Proposed.** Use the pure models that already exist:
- `Direction.try_from_spec` already states `result = match value with | 0 => .Ok .A2B | 1 => .Ok .B2A | _ => .Err value`.
- `Chain.new_spec` already has a full postcondition.

So:
```lean
/-- The postcondition of `Chain.new_spec`, named so other specs can refer to it. -/
def Chain.NewPost (initial_key : List U8) (dir) (params) (r : Result Chain Error) : Prop := …
theorem chain_from_version_negotiation_spec vn :
    chain_from_version_negotiation vn ⦃ result =>
      match directionOfI32 vn.direction, vn.chain_params with
      | none, _ => result = .Err .StateDecode
      | some _, none => result = .Err .ChainNotAvailable
      | some dir, some params => Chain.NewPost vn.auth_key.val dir params result ⦄
```
Here `directionOfI32` is the pure function behind `try_from_spec`. Nothing else names this theorem,
so the change is local; it is `@[step]`, so callers see it through `step*`.

**Question for you**
- (f) Is naming `Chain.NewPost` (and using it in `new_spec` itself) acceptable? The alternative is
  inlining `new_spec`'s full postcondition into this statement.

---

## C4. Small, no public statement change

- `Lib/SecretOutput/Eq.lean`: the private helper `allM_zip_u8_post : ∃ b, List.allM … = ok b ∧ …`
  becomes `List.allM … ⦃ b => b = true ↔ xs = ys ⦄`, proved by induction with `spec_bind`. This
  removes the `exists_imp_spec` use; public `eq_spec` is unchanged.
- `SpecRefl.lean`: deleted after C1.
- `SpecImpExists.lean` (the shim): deleted once groups A/B and C1–C4 are done. The build then
  prevents regressions.

## C5. Pure-result helper lemmas stated as equations

Found while migrating groups A/B. Each states a computation's result as an equation, and each
proof needs an `= ok` fact from a scalar addition or clone:

- `core.array.from_fn_loop_replicate_default` (`SrcTranslated/FunsExternal.lean`):
  `from_fn_loop fnMutInst () i n = ok (List.replicate n default)`.
- `core.array.from_fn_loop_const` (same file): `from_fn_loop fnMutInst f i n = ok (List.replicate n v)`.
- `Slice.concatListAux_shared_id_spec` (`Spqr/Specs/Aeneas/SliceConcatListAux.lean`):
  `Slice.concatListAux … l = ok ((l.map (·.val)).flatten)`.

- Enumerate-iterator step helpers: `EnumerateSliceIter_next_post` (`Poly/AddAssign.lean`) and
  `EnumerateSliceIter_next_Pt_post`/`_some` (`Poly/FromCompletePoints.lean`), stated as
  `IteratorEnumerate.next … = ok (opt, iter')`. They are built on
  `usize_checked_add_one_val : ∃ y, x + 1#usize = ok y ∧ …`.
- Iterator-to-list equation lemmas: `iterToList_enum_map_acc` (`PolyEncoder/PointAt.lean`) and
  `iterToList_trans` (`ConstPolysToPolys/SliceIterMapCollect.lean`), stated as
  `∃ L, iterToList … = .ok … ∧ …`. Their proofs rewrite with `count + 1 = ok y` / `call_mut … = ok r`.

**Proposed:** restate each as a spec: `from_fn_loop … ⦃ r => r = List.replicate n … ⦄`, and
similarly for the others. Proofs go by induction with `spec_bind`. Their callers use them through
`step`/`spec_mono` instead of `rw`, so a few call sites change, but there is no change in meaning.

## Suggested order

1. C4 (trivial).
2. C3 (local).
3. C1 (needs your decision (a)).
4. C2 (largest; touches the hand-written `FunsExternal` models).
5. Delete the shim.

Each step is its own small PR with a full build.
