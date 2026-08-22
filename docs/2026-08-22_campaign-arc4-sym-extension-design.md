# Arc 4 / A4-U2 — the handler-fragment Sym extension: design (v1)

Campaign lane `campaign-arc4`, 2026-08-22, [AGENT] throughout (§5
tooling latitude; nothing here touches a statement's meaning). Follows
the accepted pilot verdict
(`docs/2026-08-22_campaign-arc4-pilot-verdict.md` §5.1) and the
seam-design amendment re-basing layer (B) on evaluator transport.
Primary sources read for this design: `Sym/{Domain,Mirror,Drift,
DriftOps,DriftApply,Walk,Refine}.lean` at this tip (8,193 lines), the
quit catalog (Mirror.lean §"quit catalog as code"), the refinement
template (`Refine.lean`), and the machine's normalizer/store path
(`GoLean/GoCore/Ops.lean:873-977`, `Machine.lean` store spine).

## 0. Boundaries (restated as binding, none relaxed here)

- **Sym stays outside every statement closure.** The statement-TCB
  walker's third refusal class bans the whole `GoLean.Sym` prefix
  from designated statements; nothing in this extension may weaken
  that, and no extension artifact becomes statement vocabulary.
- **Refinement theorems in the default build** (kit doctrine): every
  new evaluator capability ships in the same commits as its
  refinement/commutation coverage in the always-built modules.
- **Existing Sym lemmas are additive-extend-only**: the shipped
  theorem STATEMENTS (`symEvalWindow_refines`, `symEvalWindow_refines'`,
  `stepFnS_sound`, `stepFn'_concrete_agrees`) keep their exact forms;
  new capability arrives via (a) trailing default-`[]` parameters
  that leave existing call sites elaborating unchanged, and (b)
  NEW-named theorems for the conditioned forms. Where a fueled
  match-style helper cannot take a trailing parameter, the
  parameterized core gets a NEW name and the old name becomes its
  `[]`-instance, with the handful of internal proof references
  patched (internal only — no shipped statement changes).

## 1. Where the five classes actually sit (contact-grounded)

The mirror already carries the FULL Config/Cont/Value grammar
(structs, funcVals, syncData, mapIterK, sortSlice arms included). The
pilot's five ingredient classes decompose against the quit catalog as:

| class | quit site today | what is missing |
|---|---|---|
| 1. struct stores at defined types | Q4: `normalizeValueForTyFuel'`'s `.defined` arm quits — store-time normalization needs the TYPE TABLE | the Q4a "conditioned-facts-as-inputs" lever (recorded at OQ6 as the v2 plan): a table input |
| 2. call entry (fid, closure call-value, interface dispatch) | Q4: `enterFrame` consults funcs/methods/methodSets (+ defaultValue/normalize at param and result types) | the same lever, widened to the full table pack |
| 3. sequential sync-ops | Q7: all sync arms quit | mirror `applySyncOp`'s sequential success path + the `.opDone` marker emission (mirror `Config` already has `.opDone`) |
| 4. sortSlice | Q9 — **only on SYMBOLIC elements** | **NOTHING for the census path**: the `sortSlice` arm already loads, sorts and stores CONCRETE int elements (Mirror.lean, `.sortSlice` arm); Visit's ids are concrete node IDs. Documented, to be witnessed, not built |
| 5. pointer-valued map range | Q3 (the pick consumes a choice — FORCED) + a KIT shape gap (`MapMem` is uint64-key/value-shaped; `trk.Progress` is `map[uint64]*Progress`) | nothing in the MIRROR (its `mapIterK` is `Value D`-generic); a kit lift + the §4 choice-point story |

## 2. Class 1 — struct-store normalization (SLICE 1, implemented)

**Representation.** The evaluator gains a TYPE-TABLE INPUT
`T : TypeEnv`, dflt `[]`, threaded: `stepFn' s c (T := [])` →
`storeTarget'`/`storeLoc'`/`applyStmtOp'`-store-arms →
`normalizeValueForTyFuelT T` (new-named core; old
`normalizeValueForTyFuel'` = its `[]`-instance). New arms mirror the
machine's `.defined` dispatch verbatim (`Ops.lean:958-966`): alias /
defined re-target, struct via new `normalizeFieldsWith'` /
`normalizeStructValueWith'` (+ the `emptyStructAssignable` check);
`interfaceDef`/`unsupported`/unknown stay quits. Struct FIELD payloads
are already `Value D` — a symbolic int field normalizes to
`D.norm kind t` (the `SymInt.norm` constructor, already in the term
grammar), so value-symbolic/shape-concrete structs normalize without
quitting.

**Refinement-theorem shape** (matches the template exactly, one added
premise):

```
def SubTable (T U : TypeEnv) : Prop :=
  ∀ id d, TypeEnv.lookup T id = some d → TypeEnv.lookup U id = some d

theorem symEvalWindowT_refines' (hn : (symEvalWindow budget S C T).1 = n)
    (ρ σ ch) (hsub : SubTable T σ.types) :
    stepFnIter n (γS ρ σ S) (γC ρ C) ch
      = .ok (γC ρ (…).2.2, γS ρ σ (…).2.1, ch)
```

`SubTable [] U` holds vacuously, so the shipped unconditioned
theorems are the degenerate instance and keep their exact statements
(the master walk `stepFn'_conc` is generalized IN PLACE with the
`hsub` premise; the old-form corollaries re-derive at `T = []`).
Sub-table (not table equality) is deliberate: a window emitted at the
pin's table transports into any run state whose types EXTEND it.

**Cost, estimated then measured**: est. mirror ~80 lines + drift
~150–250 + threading ~25 sites. **MEASURED at slice-1 end**: the
delegation design ELIMINATED the threading entirely — ZERO edits to
existing Sym modules; one new module `Sym/TableExt.lean`, 652 lines
total (defs ~210, conc lemmas ~330, step/window/refinement ~110),
elaborating in 2.4 s. The re-measure
(`Specs/Raft/HandlerEqSym.lean`, 157 lines incl. witness +
projection readouts, 7.3 s): the pilot leaf's 14-step body span —
ten hand-chained windows with four conditioned facts in
`HandlerEq.lean` (~105 lines of span proof + the 25-line
`storeTarget_field` lemma + per-instance `hset`/`hnorm`
hypotheses) — became ONE transported window: a 3-line step-count
`rfl` + a 6-line refinement application over a ~55-line reusable
fixture (embedding + symbolic struct + state/config). The store's
whole-struct re-normalization, the pilot's measured cost center, is
COMPUTED by the evaluator. Honest scope delta, per §5: the Sym span
is address-concrete and fixes the non-scalar fields (γ-quantified
over the five scalars); the hand span quantified over the whole
field array and the cell address. Two operational gotchas recorded:
(i) the kit guide §5 REVERSAL reproduced exactly — with
`set_option smartUnfolding false` the module DNF'd (>8·10⁶
heartbeats, 671 s partial); at default options, 7.3 s; (ii) γ-image
projection equalities at a concrete valuation reduce by
`decide +kernel` (seconds), while both elaborator-whnf `rfl` and
plain `decide` fail (the default-transparency instance gets stuck) —
each `decide +kernel` `#eval`-checked first per the standing rule.

**Routing note**: the pilot ledger's "normality preservation under
`StructFields.set`" plain-kit lemma becomes unnecessary for
transported windows (the evaluator computes the normalization
outright); the ledger row stays PARKED for hand-walk consumers rather
than built speculatively.

## 3. Classes 2–4 (designed, not in slice 1)

**Class 2 — call entry (the scaling payoff).** Widen the input to a
pack `SymTables` (types, funcs, methods, methodSets; each dflt empty)
with per-component sub-table/sub-array agreement premises shaped like
`SubTable` (for funcs: every successful `findFunctionIn?` on the
input agrees with `σ.functions`). Mirror `enterFrame'`:
find → `dynamicDispatch'` (methodInfo + methodSets + the pointer-box
deref) → `bindParams'`/`allocDecls'` (needs class 1's normalize and a
`defaultValue'` defined-arm at `T`). The `callValArgsK` completion
resolves a `funcVal` callee to its fid and enters the SAME mirror
`enterFrame'` — so fid calls, closures, and interface dispatch are
ONE lever, not three. Refinement: template + the pack premise. Est.
400–700 new lines (the largest class); the payoff is windows that
cross whole call trees, collapsing the pilot's per-callee split —
the multiplier the NO-GO verdict priced.

**Class 3 — sequential sync-ops.** Mirror `applySyncOp`'s SUCCESS
path over the (already concrete) `syncData` payloads, emitting the
`.opDone` marker exactly as the machine; blocked shapes remain quits
(a blocked mutex inside a sequential window is the deadlock terminal
— no window wants it). The sync apply consumes no choices
(StepFn.lean's arm), so the `ch`-unchanged theorem form is untouched.
Est. 100–200 lines. **Salvage check (coordinator-directed), result
NEGATIVE**: the parked `channel-logic` branch was searched read-only
(`git grep` over its `proofs/*` for SyncOp/applySyncOp/mutex) — its
DM layers (`ChanDM`, `LawsDM`) are CHANNEL-op WP laws predating the
W3.2 sync-op machinery entirely; zero sync-op forms exist there.
Nothing taken; nothing cited.

**Class 4 — sortSlice.** Already proceeds at concrete elements
(loads → `sortLe` → stores; Q9 only when an element payload does not
close). The census path sorts concrete node ids. Deliverable is a
WITNESS window over a Visit-shaped fragment when class 2 makes the
surrounding steps transportable — no evaluator work.

## 4. Class 5 and THE CHOICE-POINT STORY

Handlers consume draws (pilot measurement: 4 per `becomeFollower` —
the D-11 jitter pick, three `Visit` mapIter picks). Two designs were
considered:

- **(i) Thread a pick prefix as evaluator input** — refinement shape
  `stepFnIter n … (pre ++ ch) = .ok (…, ch)`. REJECTED as the
  default: it changes the theorem template's `ch`-unchanged form, and
  it yields one window PER PICK SEQUENCE (3 picks over 3 keys = 6
  orders per Visit; every enclosing composition multiplies), i.e. it
  re-imports the very explosion the sort canonicalizes away.
- **(ii) Q3 stays a WINDOW BOUNDARY; choice quantification lives at
  the composition layer.** ADOPTED. Windows transport the
  straight-line segments BETWEEN consumption points; each pick is
  crossed by the kit's pick step (`MapMem.stepFn_pick_bind`, lifted
  value-generic — the class-5 KIT half) under the §16
  conservation-invariant schema. The pilot's
  choice-independent-projection pattern generalizes as: per range
  loop, a conservation invariant ("the accumulator holds a
  permutation of consumed keys ++ remaining") quantifies over ALL
  pick orders; the canonicalization step (Visit: `slices.Sort`)
  collapses the per-order states to ONE post-state; the next window
  resumes from the collapsed state. One window after the sort — not
  six. Where a pick lands in the post-state without canonicalization
  (the jitter: `randomizedElectionTimeout = 10 + pick`), the handler
  equation carries the choice-dependent field EXISTENTIALLY and the
  projection (`absRaftNode`) never reads it — exactly the pilot's
  GAP-V1-5 scoping, now a design rule: **latitude-bearing fields stay
  unprojected, so handler equations stay choice-prefix-quantified
  with choice-independent conclusions.**

Class 5's kit half (value-generic pick/snapshot forms for
`map[uint64]*T`) goes to the promotion ledger as a PLAIN KIT lift —
the mirror needs nothing (its map machinery is `Value D`-generic;
symbolic KEYS stay Q8, and the census path has concrete keys).

## 5. The address-concreteness caveat (stated, not hidden)

Mirror heaps are concrete-keyed (Q2): transported windows are
VALUE-symbolic but ADDRESS-concrete. The pilot's hand span was
address-generic (`∀ a`); a Sym-driven span pins the layout and
γ-quantifies the payloads. Consequences and mitigations: per-layout
window emission is a closed evaluator run (machine work, no hand
labor — acceptable for the twin's finitely many node layouts), and
the recorded v2 lever (D-relative addressing, Q2's catalog entry)
would restore address genericity if layouts proliferate. Handler
equations composed from Sym windows therefore state their layout as
part of the WF pack; `absRaftNode`'s address argument absorbs it.

## 6. Slice ladder for A4-U2+

- **Slice 1 (this unit): class 1 end-to-end** — the `T` input, the
  defined/struct normalize arms, the generalized master walk +
  `symEvalWindowT_refines'`, a discharge witness on the pilot's
  leaf-store fragment, and the re-measured `alt_call_span`
  (Sym-driven; before/after line count = the value measurement).
- Slice 2: class 3 (sync-ops) — small, independent.
- Slice 3: class 2 (call entry) — the big one; after it, re-measure a
  MULTI-callee fragment (`reset`'s straight-line prefix) as one
  window.
- Slice 4: class 5 kit half + the first choice-crossing composition
  (Intn's pick), witnessing §4(ii) end to end.
- Kill-points: any slice whose drift generalization forces a
  NON-additive change to a shipped Sym statement stops and reports;
  class 2 stops if `enterFrame'` mirroring demands table shapes the
  sub-table premises cannot express.
