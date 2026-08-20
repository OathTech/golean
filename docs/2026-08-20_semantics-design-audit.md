# The semantics design audit — W3.2 slice 0 (2026-08-20)

**Charter:** `docs/2026-08-20_w32-re-envelope-charter.md` §Slice 0. The
user directive this executes: the semantics should be *"nice as well as
faithful … an operational semantics to be proud of … a trust surface
humans will eventually want to read."* This is a DESIGN audit by a
PL-theorist persona, not a bug hunt (the differential owns bugs).

**Ground truth:** branch `w32-re-envelope` @ `f78138d7`, tree clean.
Every `file:line` below is against that commit. Files read in full:
`GoLean/GoCore/{Syntax,Machine,StepFn,Ops,Multi,Race}.lean` (9,664
lines), plus the doctrine inputs (essence-of-Go, nondeterminism
doctrine, reshape note §1). No code was changed by this slice; the
output is this note plus the graded refactor queue (§8), consumed
during slice 1 after the G0 review.

**Verdict in one paragraph.** The machine's skeleton is genuinely good:
one plan/shift/apply schema instantiated five times, envelope statements
in situ at every live choice site, fail-closed discipline that is
legible arm by arm, and an unwinding design that derives Go's chained
abort output from one rule. The wince points are not rot but growth
scars, and they cluster in exactly three places: (1) the **choice-site
mechanics** are a doc-maintained list with per-site bespoke consumption
policies rather than a code-resident enumeration — the thing slice 1's
`Choices` reshape must fix anyway; (2) the **continuation type** has
outgrown its algebra — 30 constructors, five hand-written full walks,
two frames with 10–11 positional fields, and a delete-prune whose
legality is narrated rather than named; (3) the **pool/detector seam**
reconstructs what a step did (partner-diffing, stream-replication)
instead of being told — three copies of the consumption logic that must
agree by review. All three sit inside slice 1's blast radius, which is
why the queue's top items ride the wedge surgery rather than preceding
it as separate reshapes.

---

## 1. Rule uniformity

**Verdict: strong skeleton, four legible deviations.**

The machine's core discipline — classify the construct into a head plus
an operand plan, evaluate operands left-to-right under one generic
frame, apply the head in one step — is instantiated uniformly five
times: `strictPlan`/`applyStrictOp` (Machine.lean:142/262),
`stmtPlan`/`applyStmtOp` (709/911), `chanPlan`/`applyChanOp`
(1271/2303), `syncPlan`/`applySyncOp` (1340/2428),
`selectOperands`/`applySelect` (1399/2712). The relation's rule
quadruples (`*First`/`*Shift`/`*Apply`/`*ApplyPanic`) are predictable
from the schema; a reader who has seen one family can read the others.
This is the file's greatest design asset and the opsem write-up's
natural spine. Deviations:

- **U-1 — the apply-result grading is real but unnamed.** The five
  applies return four different shapes: value×state (`applyStrictOp`),
  state×choices (`applyStmtOp`), config×state (`applyChanOp`,
  `applySyncOp` — these also TAKE `env`/`k`, i.e. they build
  continuations), config×state×choices (`applySelect`). Each choice is
  individually justified (a channel op's outcome IS a configuration:
  proceed/panic/block/delivery-entry), but the grading — *value < state
  < configuration, ± stream* — is nowhere stated as the design rule it
  is. Better shape: not unification (the grades are semantic), but one
  paragraph at the `StrictOp` section head naming the grading and which
  family sits where, so the signature zoo reads as a ladder instead of
  drift. Cost: docs only.
- **U-2 — `stepFn` bypasses `chanPlan` for send/close but consults it
  for recv.** StepFn.lean:194-197 hand-inlines the send/close plans
  (`.chanStK (.send elem) [] [value]`) while :201 dispatches recv
  through `chanPlan` with a named scrutinee; the relation's
  `chanStFirst` (Machine.lean:3321) uses `chanPlan` uniformly for all
  three. Both sides are equal, but the executable and the relation
  dispatch the same family by different routes, and a reader must check
  the equality by hand. Better shape: route all three stepFn arms
  through `chanPlan` (the `syncStmt` arm at :267 is the model).
- **U-3 — the spine-riding assignment family has no plan function.**
  `assign`/`assignMany`/`mapLookup`/`typeAssert` each get a bespoke
  entry rule (`assignFirst`, `assignManyFirst`, `mapLookupFirst`,
  `typeAssertFirst`, Machine.lean:3409-3427) and a bespoke stepFn arm
  (StepFn.lean:138-150, 228-262), all constructing the same
  `.tgtOpK sh [] ops [] rest ROP rhs [] (.seqn #[]) env k` literal with
  different `RhsOp`/rhs payloads. Every OTHER statement family got a
  classifier; this one is the residue of three migrations (BUG-025/034/
  037). Better shape: `spinePlan : Stmt → Option (List (TargetShape ×
  List Expr) × RhsOp × List Expr)` + one `spineFirst` rule — four rules
  become one, and the stepFn arms become one schema instance.
- **U-4 — one rule carries an environment-equality premise.**
  `initialization` (Machine.lean:2819, executable StepFn.lean:129-137)
  requires the enclosing `seq`'s env to EQUAL the current env
  (`if kenv = env`), a decidable-equality test on whole environments —
  the only rule in the machine whose premise compares environments. It
  is the artifact of `seqCont`'s splice plus in-sequence declaration,
  and it is defensive (the frontend only emits initializations inside
  statement lists), but neither the rule nor the arm says "defensive;
  unreachable from lowered Go". Better shape: say exactly that in the
  docstring, or eliminate the shape by letting a declaration consume its
  OWN sequence tail (a head-form rule needing no equality). The
  `seqCont` splice condition (`env' = env`, Machine.lean:1863) is the
  same O(env) equality in a smart constructor — worth one line noting
  it is a canonicalization, not semantics.

## 2. Construct orthogonality

**Verdict: mostly one-place-per-feature; two genuine smears, one
recorded hazard that could be made impossible.**

- **O-1 — delete-prune makes map deletion non-local.** `mapDelete`/
  `clearMap`'s semantics now includes rewriting OTHER statements'
  continuation frames: `contAfterStmtOp` (Machine.lean:2183) →
  `pruneIterFramesKey`/`pruneIterFramesAll` (2088/2131), two more full
  continuation walks. A delete is a state update PLUS a global
  continuation transformation, because `mapIterK.produced`/`start` are
  *derived data cached in the continuation* and the prune is the cache
  invalidation protocol. The legality argument (the sets are
  per-goroutine; keys compare at the frame's own type; the walk crosses
  frames) is narrated in docstrings, not named as an invariant. Two
  better shapes, at very different cost:
  1. **Name the invariant** (cheap): a stated `IterFramesConsistent`
     property — every in-flight `mapIterK`'s `produced` ⊆ keys this
     frame has bound, and `start` = range-start keys minus keys since
     deleted from this map — with the prune as its preservation step.
     Makes the operation's legality a lemma target instead of prose.
  2. **Entry-identity stamps** (the principled alternative): give map
     entries a creation stamp in the cell itself; `produced`/`start`
     record `(key, stamp)` pairs. Delete-then-recreate then yields a
     NEW stamp *definitionally* — the I-1 adopted reading becomes
     representation, the prune disappears, delete is local again, and
     **E9's cross-goroutine residual vanishes by construction** (stamps
     live in the shared heap, not in any one goroutine's continuation).
     Cost is real: the `mapData` cell shape changes, every map op and
     `valueEq`-on-maps and footprint arm touches, metatheory-level.
     Recorded here as the *widen branch's best implementation* for
     slice 4's E9 ruling, not as a slice-1 item.
- **O-2 — the detector's parallel dispatch.** `stepAccesses`
  (Race.lean:922) and `raceUpdate` (Multi.lean:1138) are a second,
  read-only interpreter keyed on configuration shapes, mirroring
  `stepFn`/`stepThread`'s dispatch; `wokenPartner` (Multi.lean:986)
  recovers the pairing partner by DIFFING pre/post pools, and the
  select-commit arm REPLICATES the step's stream consumption
  (Multi.lean:1241-1271, three consumption re-derivations that must
  stay in lockstep with `stepMulti`/`arrivalPlan`/`applySelect` by
  review alone). The footprint-table-not-autologging decision itself is
  right and well-argued (Race.lean:26-53); the smear is that the
  *classification* of what a pool step did is computed twice. Better
  shape: the step returns a **step event** (queue item Q2, §8) and the
  detector folds events. This is the one refactor that deletes code
  from three files at once.
- **O-3 — the spawn nil-interface hazard can be made impossible.**
  `spawnStep` (Multi.lean:289) routes EVERY `enterFrame` `.panic` to a
  child abort, correct only because the frontend hoists the
  nil-interface-dispatch check before `go` — a machine-correctness
  contingent on a frontend invariant, recorded as a standing hazard in
  its own docstring ("any future lowering that leaks the nil-interface
  class through a spawn would be misrouted … keep the hoist, or split
  the classes upstream"). The two classes are indistinguishable because
  `enterFrame` collapses both into one `.panic msg` with an identical
  message. Better shape: `enterFrame` returns a structured entry-panic
  class (`nilInterfaceDispatch | nilPointerBox`), `spawnStep` routes on
  it, the hazard becomes a type error. Witness-level cost
  (`enterFrameStep`/`enterFrameDeferPanicking` + a handful of rules).
- Honest negative: the interface/dispatch machinery, the panic chain,
  channels, sync, and the wide ops each live in one place with their
  probes attached. The E6 hoist-refusal smell the charter names is
  real only at O-3's site and at `contHeadLabel`'s label-placement
  contract (Machine.lean:1867-1874) — and the latter fails closed
  (`labeled continue escaped its label`) if the placement invariant
  ever breaks, which is the right failure.

## 3. Choice-site / envelope legibility from the rules

**Verdict: envelope STATEMENTS are exemplary; consumption MECHANICS are
not readable as a system. This is the audit's top finding and it is
slice-1 work.**

The good half first, plainly: every live site carries its spec-quoted
envelope at the consuming definition — `Cont.mapIterK`'s docstring
(Machine.lean:1742-1770), `appendSpillUpper` (Ops.lean:1926-1949),
`applySelect` (Machine.lean:2625-2661), `applySyncOp` (2366-2388),
`runnableIdxs` (Multi.lean:213-216), `arrivalPlan`/L4
(Multi.lean:504-513), the L5 window (Multi.lean:1391-1414). Requirement
1 of the nondeterminism doctrine is visibly met *in the code*. A reader
CAN find every latitude point — by grepping for `Choices`.

What a reader CANNOT do is predict the consumption discipline from any
one convention:

- **C-1 — per-site bespoke width-1 policies, each load-bearing in a
  different direction.** `mapIterNext` consumes even at width 1
  (StepFn.lean:617-618, the inventory's §9 flag 5); `applySelect`
  consumes only at ≥2 ready and singleton-readiness NON-consumption is
  itself load-bearing (Machine.lean:2630-2633 says so); L4 and L1
  special-case the singleton candidate/runnable list to avoid the pop
  (Multi.lean:887-897, 931-937); the append spill consumes whenever it
  spills, with the canonical member produced by offset arithmetic
  (`newLen + ((growth − newLen + extra) % width)`, Machine.lean:945-948)
  rather than by slot ordering. Five sites, three policies, one
  arithmetic trick — all correct, none inferable from the others.
- **C-2 — the canonical-member convention is real but implicit.** Every
  site arranges slot 0 = the canonical/default member (first candidate
  in cell order with stop LAST; growth-formula point via the offset;
  exit-now = 0 at L5). This is a genuinely principled cross-site
  convention — and it exists only as per-site comments.
- **C-3 — the site census is doc-resident, synced by audits.** The
  canonical list lives in the nondeterminism doctrine's preamble and
  the latitude inventory's §0 table, "brought current at F16" — i.e.
  the enumeration is maintained by periodic human sweeps, and
  `Choices.consume` (State.lean:156) is an anonymous `List Nat` pop
  that carries no site identity. The fairness non-preclusion constraint
  (charter §Hard constraints: scheduling picks identifiable, the
  schedulable set recoverable, `Fair : Choices → Prop` definable) is
  not satisfiable over anonymous pops without re-deriving which pop was
  which — exactly the reconstruction `raceUpdate` already has to do.

**Better shape (queue Q1):** a `ChoiceSite` enumeration (one
constructor per census row: `mapIter`, `appendSpill`, `l2Entry`,
`l2Arrival`, `l4Waiter`, `l1Sched`, `l5ExitWindow`, plus slice 1's new
points) and one consumption combinator
`Choices.consumeAt (site : ChoiceSite) (bound : Nat)` whose policy
(consume-at-1 or not; canonical slot) is a per-site declaration in ONE
table. Then: the census IS a datatype (exhaustiveness-checked, F16-style
sweeps retired); the width-1 nuances are declared, not discovered; and
a labeled consumption trace is exactly the carrier a future
`Fair : Choices → Prop` quantifies over. Since slice 1 reshapes
`Choices` anyway, doing that reshape untagged and re-tagging later
would be two reshapes — this rides the wedge surgery or it costs
double.

Also here: **C-4 — the L2 site is consumed in two code paths** with a
prose bound-equality argument (`applySelect`'s cell path vs
`arrivalPlan`'s `.multi`, Multi.lean:686-695: "its bound then equals
the waiter-extended one by construction"), and replayed in a third
(`raceUpdate`). One semantic site, three textual consumers. Q1+Q2
together collapse this to one.

## 4. Continuation-algebra principledness

**Verdict: the frames are individually well-designed; the TYPE has no
algebra. The five hand-written walks and the two positional-soup frames
are the cost, and they grow with every feature.**

- **K-1 — five full walks over 30 constructors, four of which differ
  only at 2–4 frames.** `panicPassthrough` (Machine.lean:1902),
  `recoverThroughWrappers` (1945), `recoverResult` (2012),
  `pruneIterFramesKey` (2088), `pruneIterFramesAll` (2131), plus the
  partial `pushDefer` (1887). Each treats all "glue" frames identically
  and acts at frames/markers/iteration frames. `recoverResult` and
  `recoverThroughWrappers` are ~65-line near-duplicates. Adding one
  `Cont` constructor today means editing 5–7 functions plus
  `stepAccesses` plus the relation. Better shape, two rungs:
  1. (Cheap, rides anything) a frame-classification + generic rebuild
     combinator — `Cont.rebuild (act : Cont → Option (Option Cont))`
     or a `mapGlue` traversal defined once, with the five walks as
     instances; the classification (`glue | frame | marker | iter |
     stop`) becomes a named function instead of `panicPassthrough`'s
     implicit `none`-arms.
  2. (Deep, NOT this arc) `Cont` as `List Frame` — the classic CEK
     spine-as-list, under which pushDefer is "find first frame",
     unwinding is "dropWhile glue", prune is "map". Every rule and
     proof moves; recorded as the shape a future ground-up cleanup
     would take, graded out of this arc's budget.
- **K-2 — `mapIterK` (10 fields) and `tgtOpK` (11 fields) are
  positional soups.** Machine.lean:1771-1773, 1812-1815. `mapIterK`
  carries 5 static fields recoverable from the originating `mapRange`
  (keyVar/valVar/keyTy/valTy/body), 3 dynamic ones (base/produced/
  start), plus env/k; every walk arm spells
  `.mapIterK a b c d e f g h i k`. `tgtOpK` interleaves four jobs
  (current-target operands, resolved refs, pending targets, RHS/values
  carriage). Better shape: bundle — `RangeSpec` (static) + `IterState`
  (dynamic) making `mapIterK spec st env k`; a `SpineState` for
  `tgtOpK`. The prune becomes a function `IterState → IterState`
  applied through one field instead of a 10-argument constructor
  rebuild; the charter's "just grew three fields" question gets the
  structural answer (the growth was fine; the FLATNESS is the debt).
  Mechanical but wide; the parametric mirror + kit pins make the cost
  estimable, and slice 4 respins `mapIterK` again regardless — bundle
  first, so the re-proof wave lands on the bundled shape once.
- **K-3 — the prune's legality should be an invariant, not a
  narrative.** See O-1.1; the existing `MultiWf`/`itersNormalized`
  carrier (Multi.lean:1590) covers typing, not the produced/start
  semantics.
- **K-4 — `contAfterStmtOp` patches a dead case.** Its docstring
  (Machine.lean:2174-2181) explains why the NULLARY wide-statement rule
  doesn't thread the prune — but no statement classifies to an empty
  plan at all (every `stmtPlan` arm emits ≥ 1 operand;
  `proofs/GoLeanProofs/Laws/Init.lean:71` already refutes the case by
  `simp [stmtPlan]`). See D-1.

## 5. Naming

**Verdict: consistently good at the rule level; a handful of confusable
or under-descriptive names.**

- **N-1 — `Stmt.label` vs `Stmt.labeled`** (Syntax.lean:318/303): an
  inert marker vs the semantic label scope, one character apart. Rename
  the inert one (`.inertLabel` / `.marker`) or fold it out at the
  frontend.
- **N-2 — `newValue`** says nothing about allocation (`new(T)`
  semantics). `allocValue` would read.
- **N-3 — `tgtOpK`** names phase-1 target operands but carries the
  whole assignment pipeline; if Q3's `SpineState` lands, `spineK` (or
  `assignK`) is the honest name.
- **N-4** — the relation's rule names (`callArgsDoneEnter`,
  `panicResumeMerge`, `breakToLabelMatch`) are exemplary: verb-object,
  predictable, and the write-up can use them as rule labels verbatim.
  The K-suffix convention for frames and the `apply*`/`*Plan` pairing
  are uniform. Honest negative: no systemic naming debt.

## 6. Dead generality

**Verdict: very little — three concrete items, one of them a whole dead
rule.**

- **G-1 — `stmtOpNullary` is dead** (rule Machine.lean:3000-3003, arm
  StepFn.lean:278-280): no `Stmt` classifies to an empty operand plan
  (every `stmtPlan` arm includes its target or base). The proof layer
  already knows (`Laws/Init.lean:71` discharges the case by
  contradiction), and `contAfterStmtOp`'s docstring spends a paragraph
  on the dead rule's non-threading (K-4). It exists by symmetry with
  the genuinely-live `evalStrictNullary` (floatLit/defaultValue/nil are
  nullary strict forms). Delete rule + arm; witness-level (one mirror
  arm and one refuted proof case vanish).
- **G-2 — `applyStmtOpCore`'s `_nt` parameter is unused**
  (Machine.lean:747). Drop it or say why it is kept.
- **G-3 — `(Nat × PairTarget)` carries a dead 0 for chan-op arrivals**
  (Multi.lean:432-464: "for chan-op arrivals the first component is 0
  and unused"). Representation slack; a select-arrival-only clause
  index would be honest. Low priority.
- Also noted, below the bar for the queue: the targetless-frame-with-
  pinned-results shape is representable but stuck-closed at two
  duplicate arms (StepFn.lean:553-559 = 674-680 — see G-4);
  `recvStores`' `_ => []` arm silently under-delivers on impossible
  counts (it fails closed two steps later at storeK's arity check —
  acceptable, but a direct refusal would be cleaner).
- **G-4 — ~40 lines of verbatim duplication between `.next` and
  `.returning` frame handling** in stepFn (552-570 vs 673-691, and the
  defer-drain 573-592 vs 694-713), plus the relation's Fall/Return rule
  twins. The twins are forced in the relation (rules have no helpers),
  but the executable side can share one `frameExitStep`/`frameDrainStep`
  helper in the `enterFrameStep` mold ("kept as ONE helper so each call
  site remains a single fun_cases branch" — the precedent is already in
  the file, StepFn.lean:44-54). Similarly the
  `.panicking [⟨runtimeErrorValue msg, false⟩] k` chain-singleton
  appears at ~15 sites; a `panicStep k msg` smart constructor is free
  readability.

## 7. Granularity as a design property; the op-taxonomy

**Verdict: the taxonomy is principled-with-a-residue; the granularity
ledger should live in the code; two charter-named suspects are cleared.**

- **T-1 — the three-way stmtOp/strictOp/spine split, read honestly.**
  The principled axes are (i) what the apply produces (U-1's grading)
  and (ii) fused vs phase-split granularity. The historical part is
  that `stmtPlan`'s membership is the residue of three migrations
  (assign, assignMany, mapLookup/typeAssert all LEFT it for the spine
  when their per-store phase-2 semantics stopped being expressible as
  one fused apply). What remains is coherent: allocations
  (`newValue`/`make*`), map mutation (`mapAssign`/`mapDelete`/
  `clearMap`), and the bulk-cell loops (`append`/`copy`/`clear`/
  `sortSlice`) — i.e. exactly the class whose granularity-ledger
  entries exist. The split is defensible **once stated as**: "fused
  apply = ops whose intermediate states Go itself never exposes
  (allocation, map-object mutation) or whose coarseness is a recorded
  ledger debt (the bulk loops)". `mapAssign` staying fused while
  `assign` went to the spine is right (map objects are ONE location for
  race purposes — gc/TSan's own classification, Race.lean:353-356) but
  is the sentence a reader most needs and does not find.
- **T-2 — put the ledger in the code.** The granularity ledger lives in
  a 2026-07-23 design note §1 plus scattered comments; slice 5 re-audits
  it. Better shape: a `StmtOp.granularity` function (or a per-
  constructor docstring block with a fixed vocabulary:
  `single-write / multi-write-one-cell / multi-cell`) making the ledger
  code-resident, exhaustive by constructor, and greppable — the U-5
  wide-op re-audit in slice 5 then has a checklist generated from the
  type. Cost ≈ zero, proof blast radius none.
- **T-3 — `addrOfDeref` is NOT a wart (charter suspect, cleared).** The
  address-former family is `ref`/`fieldAddr`/`indexAddr`/`addrOfDeref`,
  each carrying its operand's panic at formation — which IS the spec's
  compositional rule ("if the evaluation of x would cause a run-time
  panic, then the evaluation of &x does too"). `addrOfDeref` is the one
  member where naive composition (deref-then-address) would fabricate a
  race-visible read gc never performs, hence the fused form; its
  no-footprint decision is recorded in Race.lean's inventory
  (:191-199). The generalization question has a positive answer: the
  address-of-panicking-lvalue story is already compositional through
  the family. Owed: one sentence at `StrictOp.addrOfDeref` naming it
  the fourth address-former, so the family reads as a family.
- **T-4 — the 19-arm fix round landed uniformly (charter suspect,
  cleared).** Sampled against the triage L-ids: L1's rune conversions
  are two appended strict ops with plan arms, footprint rows, and the
  R3 cap-envelope statement carried in situ (Machine.lean:565-604,
  Race.lean:149-152); L5/L6's pointer-to-array index landed as
  read-position siblings of BUG-038's write-path arms with the
  asymmetry documented (Machine.lean:417-430 — only array pointees in
  read position, and WHY); L10's go-nil fatal rerouted `spawnStep`'s
  arm to the existing `GoError.fatal` class with the expired-reason
  note (Multi.lean:304-311). These are patterned landings, not special
  cases.
- **T-5 — the terminal taxonomy splits one Go-observable class across
  two carriers.** A recoverable panic is in-model (`.panicking` →
  `.panicked`, a Config terminal with rules); the UNRECOVERABLE fatals
  (`sync: unlock of unlocked mutex`, `go of nil func value`) are
  `GoError.fatal` throws — relation-silent, no configuration, despite
  being differentially-compared Go behavior (exit 2 + fixed text). The
  current line is "GoError = anything with no successor configuration";
  the nicer line for a written semantics is "Config terminals = program
  outcomes; GoError = diagnostics + resource bounds". Better shape: a
  `.fataled msg` terminal Config in `panicked`'s mold, rules stepping
  to it, driver classification unchanged. Witness-level; makes the
  opsem write-up's outcome grammar one sentence. (Deadlock is rightly
  NOT a per-goroutine terminal — it is a global property the driver
  owns.)
- **T-6 — the boundary set is legible; slice 1 should keep it so.**
  `Config.atBoundary` (Multi.lean:229-257) is one predicate = the
  registry definition, and the `.spawned` marker (BUG-040) is the
  existing precedent for a post-op boundary as a first-class
  configuration. The C3 de-fuse will generalize exactly that move
  (post-op points as marker configs or as boundary-classified
  post-apply shapes); the G1 design note should treat `.spawned` as the
  mold rather than inventing a second mechanism, and Q1's site tags
  give the new points names on arrival.

---

## 8. THE REFACTOR QUEUE

Grades: **(a)** proof blast radius — `none` / `witness` (designated
witnesses, kit pins, mirror arms re-derive) / `metatheory`
(`MultiSound`/`MultiStreams`/step_det-class statements move);
**(b)** relation to slice 1 — `RIDES` (consumed during the wedge
surgery; the same files/proofs are in its re-proof wave, so the item
costs its grade once), `PRECEDES` (cheaper done first, not required),
`DEFER` (any later slice / recorded out);
**(c)** reader payoff.

| # | Item | (a) blast | (b) slice-1 | (c) payoff |
|---|------|-----------|-------------|------------|
| **Q1** | **Tagged choice sites**: `ChoiceSite` enum + `Choices.consumeAt site bound`; per-site policy (width-1 behavior, canonical slot) declared in one table; census becomes a datatype (§3 C-1..C-4) | metatheory-lite — every consume site + the oblivious/kit lemmas mentioning `consume`; but the `Choices` reshape is slice-1 work regardless | **RIDES — effectively blocks**: doing the reshape untagged and re-tagging later is two reshapes; fairness non-preclusion (identifiable picks) is chartered | High — latitude legible from the rules; F16-style doc sweeps retired |
| **Q2** | **Step-event channel**: `stepThread`/`stepMulti` return a `StepEvent` (who ran, site consumed, clause committed, partner paired); `raceUpdate` folds events; deletes `wokenPartner` diffing + the consumption replication (§2 O-2, §3 C-4) | metatheory — Multi/Race + MultiSound/MultiStreams; all restated by slice 1's widening anyway | **RIDES**: the boundary widening rewrites `stepThread`/`raceUpdate` classification regardless; without this, slice 1 adds a fourth copy of the consumption logic | High — one honest channel instead of three lock-stepped reconstructions |
| **Q3** | **Frame-payload bundling**: `RangeSpec`+`IterState` for `mapIterK`, `SpineState` for `tgtOpK` (§4 K-2); prune becomes `IterState → IterState` | witness — wide but mechanical; mirror + kit pins make it estimable | **PRECEDES**: not needed by the wedge, but slice 4 respins `mapIterK` again — bundle before the re-proof wave so it lands once | High — the positional soups in five walks vanish |
| **Q4** | **Generic `Cont` traversal**: frame classification + one rebuild combinator; five walks become instances; `recoverResult`/`recoverThroughWrappers` dedup (§4 K-1 rung 1) | witness — walk lemmas restate over the combinator | PRECEDES/DEFER — natural companion of Q3; nothing in slice 1 needs it | High for maintainers; medium for the write-up |
| **Q5** | **Dead-code and dedup sweep**: delete `stmtOpNullary` (+arm), drop `_nt`, `panicStep` helper, shared frame-exit/drain helpers for the `.next`/`.returning` twins (§6 G-1,2,4) | witness/none | DEFER — rides any core-touching slice | Medium — honest shrinkage |
| **Q6** | **Signal unification**: `breaking/continuing/returning/breakingTo/continuingTo` → one `Config.signal sg k` + per-frame signal table; ~40 control-transfer rules become a legible frame×signal matrix (the Perennial exception-monad presentation, arrived at from the machine side) | metatheory — rules + Surface outcome classification re-derived | DEFER past slice 1 — **decide at G0 whether it lands before S6a**: the write-up renders a 5×8 table instead of 40 rules if it does | Highest per-rule payoff in the file |
| **Q7** | **Structured `enterFrame` panic classes** (nil-interface vs nil-pointer-box); `spawnStep` routes on the class; the recorded hoist hazard becomes impossible (§2 O-3) | witness | DEFER (cheap; any slice touching spawn — slice 1 touches spawn boundaries, so opportunistic) | Medium — a standing hazard deleted |
| **Q8** | **`.fataled` terminal Config** — fatal in-model like `.panicked` (§7 T-5) | witness | DEFER | Medium — clean outcome grammar for S6a |
| **Q9** | **`spinePlan` classifier + uniform `chanPlan` use in stepFn** (§1 U-2, U-3) | witness — positional case tags shift; mirror re-derives | DEFER | Medium — four bespoke entries become one schema |
| **Q10** | **Granularity-in-code**: `StmtOp.granularity` / fixed-vocabulary ledger blocks per constructor (§7 T-2) | none | PRECEDES slice 5 (feeds the U-5 re-audit) | Medium-high — the ledger becomes exhaustive by type |
| **Q11** | **Map entry-identity stamps** — the principled alternative to delete-prune; discharges E9 definitionally (§2 O-1.2) | metatheory-heavy — heap value shape, all map ops, `valueEq`, footprints | DEFER to **slice 4** — this is the "widen" branch's best implementation; the E9 ruling should weigh it against justify-and-guard | High conceptually; cost is the question |

Deferred-past-this-arc items are recorded with reasons inline (Q6 if
G0 rules it out of S6a's path; K-1 rung 2 — `Cont` as `List Frame` —
is recorded in §4 as out of budget entirely). Everything else is either
consumed in slice 1 (Q1, Q2, opportunistically Q7), staged immediately
before it (Q3, optionally Q4), or owned by a named later slice (Q10 →
slice 5, Q11 → slice 4, Q5/Q8/Q9 → any touching slice, S6a-gated Q6).

## 9. What is already good — said plainly

These are findings, not politeness; they are the evidence base for the
opsem write-up's structure (S6a):

1. **The plan/shift/apply schema** — one uniform evaluation discipline,
   five instances, shared VERBATIM between rule premises and `stepFn`.
   "One semantics, instantiated twice" is not a slogan here; it is the
   file layout. The write-up's rule families fall out of it.
2. **Envelope statements in situ** — every live choice site quotes its
   governing spec sentence at the consuming definition, with evidence
   class and transfer caveats. The doctrine's requirement 1 is met in
   code, not in a companion doc.
3. **Fail-closed is legible arm by arm** — malformed shapes carry their
   reason; relation silence and executable errors mirror each other;
   defensive arms say they are defensive (`applySelect`'s `.inr`
   mirror, Machine.lean:2683-2688, is the model of the form).
4. **Panic-as-unwinding is principled** — the chain + `panicResumeK`
   marker design derives Go's chained abort output and the
   exactly-one-non-wrapper-frame recover rule from gc's own stated
   runtime rules, with probe receipts; `panicResumeMerge` producing
   `panic: first ⏎ panic: second` from ONE rule is the kind of thing a
   PL reader enjoys.
5. **The arrival/pairing design is argued, not asserted** — the hchan
   invariants (i)–(iv) (Multi.lean:49-69) read as a proof sketch
   against chan.go, and `applyPairing` refuses `.internal` on invariant
   breach rather than "helpfully" recovering.
6. **The race footprint discipline** — a curated per-shape table argued
   against gc's compiled accesses, with an exhaustive call-site
   inventory and honest O/U ledgers (Race.lean:26-259). Unusual and
   excellent. (Tooling wish, not a machine finding: a lint that checks
   the inventory rows against actual `loadLoc`/`storeLoc` call sites
   would make the lockstep obligation mechanical.)
7. **Provenance density** — nearly every arm carries its probe/pin/BUG
   id. As a trust surface for human readers this is a strength; the
   write-up is the compression layer, not a replacement.
8. **Charter suspects cleared**: `addrOfDeref` is a coherent member of
   the address-former family (T-3); the 19-arm fixes landed uniformly
   (T-4); `mapIterK`'s growth is fine in substance — the flatness, not
   the fields, is the debt (K-2); `Config.atBoundary` + `.spawned` is
   the right mold for slice 1's widening (T-6).

## 10. Gate record

Docs-only slice: `scripts/ci` with `GOLEAN_ALLOW_NO_DIFF=1` (visible
note; no runtime change owes a differential), `GOLEAN_MEM_MAX=24G`
(parallel-lane cap budget; raft-w4 lane concurrent). Result recorded in
`docs/w32-log.md` at the slice-0 checkpoint.

**G0 (user gate):** this queue awaits Mike's review — mark what rides
slice 1 (Q1/Q2 recommended, Q3 staged before, Q7 opportunistic), what
is owned by later slices (Q10→5, Q11→4), and whether Q6 lands before
S6a. No code moves until then.
