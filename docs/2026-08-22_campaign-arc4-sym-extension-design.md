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

## 7. A4-U5 — the allocation-symbolic re-base (2026-08-24, [AGENT]; the campaign watch-list's top classic-ward item)

**LINEAGE: separation-logic locality — the frame rule and the
renaming/relocation lemma of O'Hearn–Reynolds–Yang local reasoning
(O'Hearn–Reynolds–Yang, "Local Reasoning about Programs that Alter
Data Structures", CSL 2001; the frame property / safety monotonicity
semantics of Yang–O'Hearn, "A Semantic Basis for Local Reasoning",
FoSSaCS 2002; support/equivariance in the nominal reading).** In this
repo the classic is already mechanized as the EXECUTABLE FRAME
THEOREM layer (`proofs/GoLeanProofs/Frame/`: `FrameSim`, `stepFn_sim`,
`stepFnIter_sim`, `execStmtLoop_ren`, `frameSim_seed`/`rebaseSimT`;
design of record `docs/2026-08-13_executable-frame-theorem.md`), whose
own recorded lineage is the allocator-independence quotient
(`Frame/AllocIndep.lean` — user direction 2026-08-13). Secondary
lineage, unchanged: the windows feeding the equations remain symbolic
execution via conservative extension (§0–§4 above). Nothing in this
section is a new trick — it is the composition of two landed classics.

### 7.1 The problem being retired (the stupid-trick risk, named)

Every handler equation shipped through U4 is stated at the γ-image of
a PINNED fixture: footprint cells at `Loc.base 0..k` in one arbitrary
construction order. The real twin's becomeFollower raft cell sits at
base 389 (probe2, U1) — the pinned layout is not even the run's. The
addresses are an ACCIDENTAL feature of the proof: nothing in Go, the
machine, or the handler assigns base 0 to the raft cell, and Go
promises NO address determinism at all (AllocIndep's charter). Scaling
waves 2–3 on the concrete-address pattern would bake the accident into
~20 more theorems and every layer-(C) consumer — the campaign log's
flagged "stupid trick" risk, verbatim.

### 7.2 The re-based equation form

The equation quantifies over the handler's FOOTPRINT PLACEMENT: an
arbitrary conforming relocation `r` of the fixture's cells plus an
arbitrary disjoint framed remainder `fr`, both carried by ONE premise
— `FrameSim r na₀ na fr (γS ρ σ S0) σF` ("σF owns the fixture's
ownership shape at addresses `r(0..k)`, with `fr` untouched beside
it"). Conclusion: the run from the call configuration AT `r 0`
returns in the same step count with the SAME choice-stream behavior,
the final state again `FrameSim`-related to the fixture's post-image
(the footprint transformed, the frame preserved — the frame rule's
conclusion shape), and the `absRaftNode` projection AT `r 0` stepping
by the spec function. The concrete-fixture theorem is re-derived as
the corollary at the identity seed (`frameSim_seed`, `ρT T 0` = the
zero shift) — which is the machine-checked proof that the symbolic
form STRICTLY generalizes the shipped one.

### 7.3 The composition answer (the dispatch's contact question)

Does the kit's frame machinery compose with the TableExt window
transport, or does the transport need a frame-aware variant? **IT
COMPOSES — at the machine level, POST-transport, with ZERO Sym
changes.** The transported span (`bpc_span` etc.) is already a
machine-level `stepFnIter` fact at the pinned placement, ∀σ over the
table-carrier; `stepFnIter_sim` (Frame/Transfer.lean) is stated at
exactly that level, so the relocation+frame lift is one `ExSim.ok_inv`
application on the span's conclusion. The mirror's concrete-keyed
heaps (Q2) never enter: Sym emits the window at the canonical
placement, the frame theorem transports the RESULT. Consequences:

- **No frame-aware `symEvalWindowT` variant is needed.** The §5
  D-relative-addressing v2 lever stays parked — it is the deeper fix
  for layout-SHAPE symbolism (per-layout window emission), not needed
  for allocation-symbolism.
- The zero-edits property holds a FIFTH time: no existing Sym or
  Frame line changes; the lift is one new target-layer module.
- The one genuinely new obligation is PROJECTION RENAME-INVARIANCE:
  `absRaftNode` (a chain of heap lookups + scalar field reads) commutes
  with `renameCell`/`renameLoc` under `FrameSim` — `absRaftNode_ren`,
  proved once, serving every handler equation's pre/post readout.
- **Naming-collision flag (from contact, for the reuse survey):** the
  kit's `wp_frame_*` family (`Laws/Call.lean`, `Laws/Unwind.lean`) is
  Go CALL-frame machinery (function frame entry/return/defer laws) —
  NOT the separation-logic frame rule. The SL-frame content of this
  repo lives in `Frame/` (`FrameSim` + the `_sim`/`_ren` theorems).
  The dispatch's "wp_frame family" question resolves to: call-frame
  laws are orthogonal to allocation-symbolism; the Frame/ layer is
  the machinery that composes.

### 7.3b The Iris-preference ladder applied ([USER] directive, mid-unit)

Priority order per the directive — (1) iris-lean as-is, (2)
Iris-compatible extension, (3) reused Iris-literature ideas, (4) new
machinery with an explicit no-analog note. Applied from contact with
the pinned `deps/iris-lean` checkout:

1. **iris-lean as-is — checked, does not fit THIS layer.** iris-lean
   carries the genuine frame rule (`wp_frame_l`/`wp_frame_r`,
   `Iris/ProgramLogic/WeakestPre.lean:492-504`; the ProofMode `Frame`
   class, `ProofMode/Classes.lean:189`) — but over `IProp GF` WP for
   a `Language`-instance (HeapLang is the worked instance); GoCore is
   not one. Two structural mismatches, not taste: (a) the handler
   equations are EXACT-FUEL, EXACT-CHOICE-STREAM `stepFnIter`
   equalities — step-indexed Iris WP does not express "returns in
   exactly 152 steps consuming exactly this prefix" without
   time-credit-style bookkeeping; (b) constitution §3.2 keeps Iris
   out of statement-adjacent closures, and the layer-(B) equations
   feed layer-(C)'s first-order round induction directly.
2. **Iris-compatible extension — the recorded convergence (not
   re-based now):** a GoCore state interpretation in iris-lean's
   ProgramLogic would make the `FrameSim` premise the model-level
   satisfaction of `([∗] i, (r i) ↦ cᵢ) ∗ R` — the footprint as an
   iterated points-to at symbolic addresses, `fr` as the framed `R`.
   The alloc equation is then the adequacy-level shadow of an Iris
   triple; re-basing becomes mechanical when the iris-lean refresh
   arc lands a GoCore instance. This is the route the ladder prefers
   long-term; it is gated on the pin-refresh + reuse-survey backlog,
   not on anything in this unit.
3. **Reused ideas — what this slice actually is:** operational
   locality — the renaming lemma + frame property of Yang–O'Hearn's
   "Semantic Basis for Local Reasoning" — which is ALSO exactly the
   physical-heap locality that Iris's own heap adequacy rests on.
   The exact-step form's Iris-literature analog is time
   credits/receipts (Mével–Jourdan–Pottier); the choice-prefix
   quantification's nearest Iris concept is prophecy-style oracle
   reasoning. Both noted for the survey.
4. **New machinery — none.** No new logic, no new trick:
   `absRaftNode_ren` is a congruence lemma over landed machinery.

**Convergence notes for the parallel reuse survey** (per the
directive, even though no re-base happens here): (i) `FrameSim` ≈
big-sep points-to + frame at the model level (item 2 above); (ii)
`fr_avoid`/`frame_pres` = the frame `R` surviving the run — the frame
rule's conclusion; (iii) the equations' conditioned side conditions
(`hvote` range facts) = pure `⌜φ⌝` embeddings; (iv) the kit
`wp_frame_*` naming collision (§7.3 flag) should not be counted as
Iris-frame coverage in the survey.

### 7.4 What stays concrete (the honest boundary, stated not hidden)

1. **Footprint layout SHAPE**: ownership is expressed as
   `FrameSim`-relatedness to the pinned-layout γ-image — `r` relocates
   cells, it never reshapes the footprint (which cells exist, their
   field structure, their inter-pointer wiring are the fixture's).
   Genuine shape-symbolism is the §5 v2 lever, not this slice.
2. **The fresh region is canonical-sequential from `na`**
   (`ShiftSpec`): the machine has ONE allocator; arbitrariness of the
   handler's OWN allocations is exactly AllocIndep's quotient (apply
   the theorem again at the exit state if a consumer needs a shifted
   continuation).
3. **Tables** stay `Agrees`-pinned (unchanged from U2).
4. **The §3.3 witness discharges at the identity seed** (every premise
   concretely instantiated, `FrameSim` included). A NON-identity
   concrete instance at the raft fixture needs a generic relocation
   seed builder (`frameSim_relocate : ShiftSpec r na₀ na → … →
   FrameSim r na₀ na [] σ (rename-image of σ)`), which the Frame layer
   does not yet provide (its non-identity instances are built
   incrementally by `rebaseSimT` in the sort examples). PROMOTION
   LEDGER row — two named consumers: shifted witnesses for every
   handler's alloc equation, and the layer-(C) composition that must
   transport leaf-fixture equations to the twin's REAL layout
   (base 389 et al.). Non-identity liveness of `FrameSim` itself is
   already kit-witnessed (`swapShift_spec`, the rebase chains).
