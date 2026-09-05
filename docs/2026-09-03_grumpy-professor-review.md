# The grumpy professor's design review of the semantic core (2026-09-03)

Status: REVIEW, docs only. Reviewed tree: `main` @ `b5abacc1`
(2026-09-03). Written in worktree `grumpy-professor`, branch of the
same name. Nothing under `GoLean/`, `tools/`, `scripts/`, `Corpus/` or
`baselines/` is touched by this lane.

Provenance. Every judgment in this document is [AGENT] unless marked
[USER]. The lane's brief is Mike's, dated 2026-09-03, held by this
worker BY RELAY from the [AGENT] coordinator (not firsthand); the
relayed wording: «The grumpy professor admires the Cerberus C
semantics very much, and the grumpy professor knows everything there
is to know about semantic modelling of real programming languages. The
grumpy professor's job is to find ways that our semantics isn't 'nice'
- special cases, unclear reasoning, things that will bite us when it
comes time to build on top of the semantics. The grumpy professor
proposes ways to make the semantics nicer without changing the
semantic effect of anything - their job is purely to make a semantics
that the heroes of PL theory would admire as pure, clean,
well-structured, and above all, useful.» A mid-lane emphasis, also
relayed: the primary material is the Lean definitions, definition by
definition; the docs are background.

What was read, in full: `GoLean/GoCore/{Value,Syntax,State,Ops,
Machine,StepFn,Multi,Race}.lean` (the executable core and the
`Step`/`StepM` relations, 12 415 lines), the headers and declaration
lists of `StateWf`, `MachineSound`, `MultiSound`, `MultiWfSound`,
`MultiStreams`, `NPDRF`, `EnumSpec`, `EnumDedupCheck`, `StateEqb`,
`SyntaxEqb`, `MachineEqb`; the decoder `GoLean/NativeToIR.lean`
(header, key sets, the `$`-temp emissions) and the consumption
accountant in `GoLean/CLI.lean` (`stepNeeds`/`stepNeedsSeq`). The two
earlier design audits (`docs/2026-08-20_semantics-design-audit.md`,
`docs/2026-08-21_semantics-design-audit-2.md`) were read afterwards so
that this review does not re-discover their queue; where a finding
below overlaps a queued item (Q1–Q11, N-1–N-6) the overlap is cited and
the new evidence or the new angle is stated. No Cerberus checkout is
readable on this machine (`/home/dev/projects/cerberus-lean` does not
exist; `deps/` has no Cerberus); §4 draws on the reviewer's knowledge
of Cerberus (Memarian et al., POPL 2019; the Core language and the
`Mem` interface).

"Building on top" below means the downstream reasoning repo that will
consume this one as a pinned dependency (CLAUDE.md): iris-lean
`Language` instances, the WP calculus, per-field points-to (G-REPR),
the NPDRF mover route, the `Fair` hypothesis over the choice tape.

Line numbers are those of `b5abacc1`.

---

## 1. What is already nice (be fair)

Findings, not politeness. These are the parts a PL theorist would
recognize immediately and would not want touched.

1. **The core is total and the totality is real.** No `partial` in
   `GoLean/GoCore/`; the fuel families are structural on the fuel
   (Ops.lean:1060 `normalizeValueForTyFuel`, :1435 `defaultValueFuel`,
   :1662 `valueEqFuel`, :306 `tySizeAlignFuel`), the list helpers are
   parameterized rather than mutually recursive (Ops.lean:1001
   `normalizeListWith` — the "de-WF recipe"), and the reason for every
   choice is written next to it. `loadLoc`/`storeLoc` are structural on
   `Loc` (Ops.lean:1219/1241). This is exactly the discipline that
   makes `decide`/kernel evaluation of the machine possible, and the
   repo proves it does (`StateWf` is `Decidable`; `allStreamsOk`).

2. **One nondeterminism combinator, one census.** `Choices :=
   List Nat` (State.lean:149) with the single consumption point
   `Choices.consumeAt site bound` (State.lean:263), the exhaustive
   `ChoiceSite` enumeration (State.lean:207 — nine constructors, every
   consumption in the core tagged; the grep of `consumeAt`/`consumeAtE`
   in Machine/StepFn/Multi finds exactly seven call sites, one per site
   except `l1Sched`/`postOp`/`backEdge` which share the boundary
   consultation at Multi.lean:1391), the per-site policy table
   (`ChoiceSite.policy`, State.lean:238) and the labeled pick record
   (`PickRecord`, State.lean:308). The relation quantifies the stream
   (`Step.stmtOpApply`, Machine.lean:3224; `Step.selectApply`,
   :3566); the executable instantiates it. The "empty stream is the
   canonical member" convention (slot 0) is declared per site, not
   discovered. This is a cleaner scheduler-oracle design than
   Cerberus' `nd` + driver, because the tape is a first-class object a
   fairness predicate can quantify over.

3. **Nondeterminism is reified, never baked in.** Map iteration order,
   append spill capacity, select pick, waiter pick, scheduler pick,
   exit window: each is a site with an envelope statement at the
   consuming definition (`Cont.mapIterK`'s docstring, Machine.lean
   :1826–1886; `appendSpillUpper`, Ops.lean:2106; `applySelect`,
   Machine.lean:2907; `runnableIdxs`, Multi.lean:245; `Config.opDone`,
   Machine.lean:2370–2415). The pinned deterministic points (E2/E5/E10/
   R1/R16) are marked PINNED LATITUDE in situ with a transfer caveat.
   No evaluator recursion hides a choice; `applyStmtOpCore`
   (Machine.lean:775) is choices-free BY CONSTRUCTION and
   `applyStmtOp` (:986) is the only wide-op arm that touches the
   stream.

4. **Refusals are first-class and cause-naming.** `GoError.unsupported`
   / `.stuck` / `.internal` carry a message that names the cause at
   the point of failure; no arm absorbs. The wire decoder's exact-key
   discipline (NativeToIR.lean:52ff) refuses unknown keys. `Ty.eqb`
   and `GoValue.eqb` fail CLOSED (`false`) on fuel exhaustion and the
   eqb tower's soundness is one-directional by design
   (StateEqb.lean header). The method-set record contract
   (Ops.lean:865–920) turns "absence of information" into a refusal
   rather than an answer. This is the right instinct and it is applied
   consistently.

5. **Plan/shift/apply as one evaluation discipline.** `strictPlan`
   (Machine.lean:142) + `Cont.strictK` + `applyStrictOp` (:279);
   `stmtPlan` (:737) + `stmtOpK` + `applyStmtOp`; `chanPlan` (:1371)
   + `chanStK` + `applyChanOp` (:2462); `syncPlan` (:1440) + `syncStK`
   + `applySyncOp` (:2589); `targetPlan` (:1276) + `tgtOpK` +
   `storeTarget` (:1316). The rules are generic over the op tables and
   the executable shares the tables verbatim, so `stepFn_sound` /
   `step_complete` (MachineSound.lean:44/367) are case analyses, not
   simulations. The three disjointness lemmas (`stmtPlan_of_chanPlan`
   :1385, `stmtPlan_of_syncPlan` :1470, `chanPlan_of_syncPlan` :1476)
   are exactly the right small theorems to have.

6. **Panic as unwinding, not teleport.** `.panicking chain k`
   (Machine.lean:2330ff) strips frames one step at a time; defers run
   above a `panicResumeK` marker; `recover` is a deterministic
   function of the continuation (`recoverResult`, :2127); a new panic
   merges behind a suspended chain (`Step.panicResumeMerge`). The
   design gives Go's chained abort output for free and keeps
   `Progress` meaningful ("no UNRECOVERED panic"). This is better than
   most formal Go semantics manage.

7. **The pool is additive over the sequential machine.** `MultiConfig`
   (Multi.lean:119) is an append-only array of `Config`s over one
   shared `ExecState`; `execProg_single_eq_execStmt` (MultiSound) says
   a one-thread pool IS the sequential machine; the detector is inert
   on one goroutine by construction (`raceUpdate`'s first branch,
   Multi.lean:1627). Channels hold no waiter queues; parked goroutines
   are configurations (D7). The hchan-invariant analogue is stated and
   asserted (`applyPairing`'s `.internal` arms, Multi.lean:1114ff).

8. **The differential discipline is the lower bound and says so.**
   Every fixture is a differential row first; observed ∈ modeled is
   the only claim the oracle is allowed to make; refusals never count
   as passes (AGENTS.md). The two prior design audits with their
   refactor queue and gate records are themselves evidence of a
   healthy process.

9. **`EnumSpec.lean` is the best 64 lines in the core** (the second
   audit said so first; this reviewer agrees): `Obs`, `obsOf?`,
   `SlowObs` state what a certified membership row means without any
   enumeration machinery in sight. It is also, as §2 U1 says, where
   the outcome-grammar debt becomes a statement-level cost.

The rest of this document is about what stands between these good
bones and a semantics the downstream repo can pin without paying for
our history on every lemma.

---

## 2. The un-nice list, ranked by how hard it bites the downstream consumer

Ranking criterion: how many downstream lemmas grow a case split, a
side condition, or a hand-threaded invariant because of it. Ties
broken by how much the item will resist change once the reasoning
repo pins us.

### U1. The outcome grammar is a bag, and program panics live in two carriers

**Where.** `GoError` (Value.lean:169–217): `panic msg | unsupported |
stuck | internal | fuelOut | deadlock | raceDetected | fatal msg`.
`Config.panicking`/`Config.panicked` (Machine.lean:2330ff).
`runConfig` (StepFn.lean:780) re-throws `.panicked msg` as
`GoError.panic msg`. The `.error (.panic msg) => .ok (.panicking …)`
conversion appears at 14 sites in StepFn.lean, 24 in Machine.lean
(the relation's twin rules), 3 in Multi.lean (grep
`\.panicking \[⟨runtimeErrorValue`).

**What it is.** One inductive mixes four different kinds of thing:
(i) Go program behaviours that are terminals of a run — `deadlock`,
`fatal`, `raceDetected`, and `panic` as reported by the driver;
(ii) a MODEL artifact — `fuelOut`; (iii) three refusal classes —
`unsupported`/`stuck`/`internal`; (iv) `panic` as an *intermediate*
signal from a helper (`valueAsLoc` Ops.lean:1625, `indexOutOfRangePanic`
:130, `checkKeyHashable` :1880 …) that the step function must catch
and turn into a `.panicking` configuration. So a Go panic is
represented (a) as an `Except` error inside helpers, (b) as a
`Config` while unwinding, (c) as a `Config.panicked msg` terminal,
(d) as a `GoError.panic msg` driver result. `fatal` and `deadlock`
are `Except`-only terminals with no configuration form
(`Step.syncStApply`'s comment, Machine.lean:3664: "FATAL outcomes …
are RELATION-SILENT"), which is why `Obs` (EnumSpec.lean) cannot say
"fatal" (the second audit's W-1/Q8).

**How it bites.**
- The relation has ~17 twin rules that exist only to catch the
  helper-level `.panic`: `strictApply`/`strictApplyPanic`,
  `evalStrictNullary`/`Panic`, `stmtOpApply`/`stmtOpApplyPanic`,
  `stmtOpTargetPanic`, `chanStApply`/`Panic`, `selectApply`/`Panic`,
  `syncStApply`/`Panic`, `rhsStores`/`rhsStoresPanic`,
  `storeStep`/`storeStepPanic`, `callImmediate`/`Panic`,
  `callArgsDoneEnter`/`Panic`, `callValCalleeEnter`/`Panic`,
  `callValArgsEnter`/`Panic`, `frameDeferFall`/`Return`/
  `panicFrameDefer` + their `EnterPanic` twins
  (Machine.lean:2941–3692). Every downstream rule-indexed lemma (a
  `wp` law per rule, a `step_det` case, an adequacy case) is written
  twice.
- An adequacy statement for the downstream repo must first define
  "which `GoError`s are Go behaviours" by hand; the type does not say.
  A `Language` instance needs `to_val : Config → Option Val`; here a
  terminal is either a `Config` (`.next .stop`, `.panicked`) or an
  `Except` error (`fatal`, `deadlock`), so `to_val` cannot be a
  projection.
- `StepEvent`/`raceUpdate` must probe the *post*-configuration to
  learn whether an op proceeded (the ten `some (.opDone _ _)` matches,
  Multi.lean:1679–1802; the second audit's W-2/N-1) because the apply
  did not return an outcome datum.

### U2. Map iteration is implemented by rewriting other goroutines' continuations

*[LANDED / RETIRED 2026-09-03 — B1 (§3) landed on branch
`hygiene-b1-stamps` @ `f6152a6c`: every definition named in this
section is DELETED and the `mapIterK` frame carries entry-id sets. The
twelve `file:line` cites below are HISTORICAL (tree `b5abacc1`); they
no longer resolve.]*

**Where.** `pruneIterFramesKey` (Machine.lean:2205), `pruneIterFramesAll`
(:2248), `contAfterStmtOp` (:2303), `removeKeyList` (:2181),
`keyInKeyList`/`keyInKeys` (:1088/:1098), `mandatoryInList` (:1167);
the pool half `mapPrunePlan` (Multi.lean:628), `Config.mapContM`
(:640), `foreignPruneError` (:669), `pruneForeignOne/List` (:683/:692),
`pruneForeign` (:710); the extra premise on `StepM.thread`
(Multi.lean:1984ff). The `mapIterK` frame carries `produced : Array
GoValue` and `start : Array GoValue` (Machine.lean:1826–1886).

**What it is.** The iteration state is a *set of keys*, so a delete
must be propagated to every in-flight frame over the same map — in
the deleting goroutine by walking its own continuation, and in every
OTHER goroutine by walking theirs at the pool level. Key membership is
Go map-key equality, so the walk is `Except`-monadic (`valueEq` can
refuse). The module docstring (Multi.lean:560–626) records the cost
(O(threads × continuation depth) per delete; a two-ranger shape did not
enumerate within 10 minutes) and the thread-locality problem
(NPDRF.lean obstruction 7: a `thread` step is no longer thread-local;
the rewrite appears in no footprint).

**How it bites.**
- The mover route (NPDRF) needs "a thread step changes only that
  thread's configuration and the shared state". `StepM.thread` now has
  a premise `pruneForeign σ' i c c' (…) = .ok ts'` that rewrites the
  whole pool. Every commutation lemma over `StepM.thread` grows a side
  condition, argued in prose ("consulted only at that frame's next
  pick, which loads the cell, which conflicts …"), which is precisely
  the kind of argument a proof assistant should not be asked to take
  on faith.
- Five full `Cont` walks exist because of this design (see U3), and
  `Config.mapContM` is a sixth over `Config`.
- The `mapIterK` frame's dynamic state is key-valued, so the
  well-formedness carrier had to grow a typing component
  (`itersNormalized`) that is now VACUOUS (`Cont.itersNormalized_true`,
  StateWf.lean:550) but still threaded through `MachineWf`/`MultiWf`
  (StateWf.lean:577, Multi.lean:2057).

The second audit's Q11 (entry-identity stamps) is the principled fix;
§3 B1 argues it is also strictly semantics-preserving and deletes all
of the above.

### U3. `Cont` has no algebra; `Config` mixes control, status and annotation

**Where.** `Cont` (Machine.lean:1728–1976, 30 constructors);
`Config` (:2330–2433, 16 constructors). The full `Cont` walks:
`panicPassthrough` (:2017), `recoverThroughWrappers` (:2060),
`recoverResult` (:2127), `pruneIterFramesKey` (:2205),
`pruneIterFramesAll` (:2248), `Cont.locSup` (StateWf.lean:336),
`Cont.itersNormalized` (StateWf.lean:484), `Cont.eqbF` (MachineEqb),
plus the partial `pushDefer` (:2002) and the shape table
`stepAccesses` (Race.lean:1290ff). Terminal shapes (`.next .stop`,
`.returning .stop`, `.breaking .stop`, `.continuing .stop`,
`.panicked _`) are enumerated as patterns in `threadDone`
(Multi.lean:148), `Config.atBoundary` (:257), `mainOutcome?` (:1828),
`execStmtLoop` (StepFn.lean:828), `Config.terminal` (Machine.lean:3717),
and again in MachineSound/MultiSound.

**What it is.** Two related things. (a) The continuation type is a
flat 30-constructor inductive in which ~24 constructors are "glue"
(they forward every walk to their tail) and ~6 are "load-bearing"
(`frame`, `panicResumeK`, `mapIterK`, `labelK`, `breakableK`, `stop`),
but the type does not say which is which; each walk re-derives the
classification by listing all 30. `tgtOpK` has eleven positional
fields, `mapIterK` ten. (b) `Config` puts in one type: control modes
(`exec/evalE/retV/next`), five control-transfer signals
(`breaking/continuing/returning/breakingTo/continuingTo`), the
unwinding mode, one terminal (`panicked`), four parked shapes
(`blockedSend/Recv/Select/Sync`), and a scheduling ANNOTATION
(`opDone (sched : ChoiceSite) (inner : Config)` — a configuration
wrapping a configuration; the type admits `opDone (opDone …)` though
no emitter produces it).

**How it bites.**
- Adding one frame today means editing 9 places (the walks above plus
  the relation plus `stepFn`). The second audit's W-3 measured the
  eqb tower as the sixth walk; `andSplit11` (MachineEqb.lean) exists
  because `tgtOpK` has eleven fields.
- The downstream `Language` instance wants `of_val`/`to_val` and a
  notion of "stuck vs. value vs. reducible". Here "value" is a pattern
  over two constructors (`.next .stop`), "parked" is four
  constructors, and "annotation" is a wrapper that must be looked
  through (`opDoneInner`, `Config.mapContM`'s recursive arm,
  `Config.itersNormalized_opDone`).
- `frame` (Machine.lean:1751) does three jobs: call frame with
  targets/results, defer-drain host, and BARRIER (`.frame [] [] [] []
  k` is spelled at ≥ 8 sites: spawn, defer drain ×3, panic drain,
  driver ×3). The `wrapper : Bool := false` field is placed AFTER `k`
  so that existing construction sites keep compiling — the type's
  field order records history, not meaning.
- The five signals produce ~40 control-transfer rules
  (`seqBreak/seqContinue/seqReturn`, `loopBreak/…`, `breakable*`,
  `label*`, `breakTo*`, `continueTo*`) that are a frame×signal table
  written out longhand (the first audit's Q6). The `.next`/`.returning`
  frame-exit twins (`frameReturn`/`frameFall`,
  `frameReturnTargets`/`frameFallTargets`, `frameDeferFall`/`Return`,
  `frameDeferNilFall`/`Return`, `frameDeferFallEnterPanic`/
  `ReturnEnterPanic`; StepFn.lean:552–575 vs 673–696 are verbatim
  twins) exist because `returning` at a frame means exactly `next` at
  a frame.

### U4. Frontend artifacts inside the core, and String-keyed runtime name resolution

**Where.**
- `Expr.locLit (l : Loc)` (Syntax.lean:131): program text carries heap
  addresses (globals resolved by the frontend to `Loc.base ⟨i⟩`). Consequence:
  `Expr.locSup`/`Stmt.locSup`/`Func.locSup` (StateWf.lean:150/202/282)
  and `StateWf` covering *stored function bodies* ("found by the
  `Syntax.lean` scan", StateWf header).
- `Scope := List (String × Loc)` (State.lean:10); `LocalEnv.lookup env
  id` is a `String` comparison chain on every `.var`/`.ref`
  evaluation (StepFn.lean `evalE (.var id)`); `seqCont` tests
  `env' = env` on whole environments to decide splicing
  (Machine.lean:1977); `stepFn`'s `.initialization` arm requires the
  continuation to be `.seq rest kenv k'` with `kenv = env` else
  `.internal` (StepFn.lean:129–137).
- `$`-named temporaries (`$rcoll`, `$ridx`, `$rfirst`, `$forFirst`,
  `$cr{i}`, `$ret{i}`, `$blank{i}`, `$ta`, `$mlv`; NativeToIR.lean
  passim) reach the core as `String`s; the reserved-prefix argument is
  a comment (Syntax.lean:476–495).
- `Func.wrapper : Bool` (Syntax.lean:409) marks a *frontend-synthesized*
  frame so that `recoverResult` can imitate gc's `abi.FuncIDWrapper`
  walk; `Race.lean:610 wrapperForwardArg` recognizes the DECODER'S
  exact emission shape ("`.block #[] #[.seqn [init, call], .seqn
  [assign, ret]]`") to narrow a footprint — the detector's verdict
  depends on how the frontend spells a wrapper (recorded in its
  docstring as "RESIDUAL COUPLING").
- `MethodSetRecord`/`MethodSetCoverage` (Syntax.lean:424–439) — "how
  much of a type's method set the WIRE records" — is a wire-contract
  fact stored in `Program` and `ExecState`.
- Five `unsupported (feature : String)` constructors INSIDE the IR:
  `TypeDef.unsupported` (Syntax.lean:71), `Expr.unsupported` (:183),
  `Assignee.unsupported` (:198), `Stmt.unsupported` (:375),
  `Ty.unsupported` (Value.lean:311). The machine has arms for them
  that throw. `TypeDef.unsupported` also serves as the "opaque
  imported type" marker (Ops.lean:909 docstring's history).
- `IntKind.unbounded (name : String)` (Value.lean:16) is a runtime
  value kind for untyped constants; `intKindBitWidth` refuses it,
  `IntKind.compatibleResult` (Value.lean:150) exists to adopt it.
- String sentinels: `runtimeErrorTypeId := ⟨"$runtime.Error"⟩`
  (Syntax.lean:486), `isEmptyInterfaceName` accepting `"any"` OR the
  legacy `"empty_interface"` (Ops.lean:680), `emptyStructAssignable`
  keying on `.key == "struct{}"` (Ops.lean:1032), `syncWord` building
  a `TypeId ⟨"sync.Mutex"⟩` (Race.lean:1221).

**How it bites.** Renaming lemmas. Any downstream statement of the
form "this program with these variable names satisfies this spec"
must carry α-equivalence over `String`s, and the machine's own
behaviour depends on name equality in two places (`seqCont`,
`initialization`) that a bijective renaming preserves but a proof
must SHOW it preserves. `locLit` forces the well-formedness invariant
onto program text: `StateWf` is about the heap AND the function
table, so every theorem that would like to say "the program is a
constant" must instead carry `Func.locSup f ≤ nextAddr`. The detector
coupling means a `-race` verdict can flip under a semantics-preserving
frontend change (the F7 incident recorded at Race.lean:600ff is
exactly that, once already).

### U5. The memory model is not a module

**Where.** `Heap := List (Loc × HeapCell)` (State.lean:27) keyed by
FULL `Loc` though only `.base` keys are ever stored; `Heap.set` on a
missing key APPENDS a cell (State.lean:99–105), so `storeLoc` at an
unallocated `.base` materializes an untyped cell (Ops.lean:1241ff —
the "fail-open aliasing" the decoder's `globaladdr` bound check and
the driver's `StateWf` assert exist to prevent, NativeToIR.lean:28–40,
StepFn.lean:961ff). `HeapCell.declaredTy : Option Ty` (State.lean:22)
selects between TWO store disciplines: `normalizeValueForTy` for
typed cells and `coerceStoredValue` (Ops.lean:155) for untyped ones;
the untyped cells are exactly the `mapData`/`chanData` payload cells
(`s.alloc (.mapData #[])`, Machine.lean:851; `.chanData`, :881).
`GoValue.mapData`/`.chanData` (Value.lean:632/640) are "values no
expression may produce" living in the value type. The access
footprint is a TABLE over configuration shapes (`stepAccesses`,
Race.lean:1290; `strictOpAccesses` :503; `stmtOpAccesses` :695) whose
agreement with what `loadLoc`/`storeLoc` actually touch is argued by a
300-line prose inventory (Race.lean:1–318) and a "lockstep
obligation"; the overlap relation `locPrefix` (Race.lean:356) lives in
the detector module, not with load/store. `syncWord` (Race.lean:1221)
manufactures PHANTOM `Loc`s (`.field loc ⟨"sync.Mutex"⟩ "state"`)
that never exist in the heap so the data shadow can key on them.

**How it bites.**
- G-REPR (per-field points-to, the downstream plan's "big design
  unit") wants: a store, an allocation discipline, a load/store
  interface, and a frame lemma "store at `l` is invisible to loads at
  `m` when `l`,`m` do not overlap". Today the frame lemma is
  `storeLoc_root_frame`/`loadLoc_after_disjoint_store` (NPDRF.lean)
  for the cross-root case only; the same-root path-level half is
  "obstruction 6". With paths-into-tree-values as the representation,
  the path-level frame lemma requires reasoning about `StructFields.set`
  and `arraySet` commuting — implementation detail of the value
  encoding leaking into the memory logic.
- `HeapCell.declaredTy = none` is a second, weaker normalizer with
  its own arms and its own congruence lemma
  (`coerceStoredValue_congr`, MachineSound.lean:1393, 160 lines).
- Every value-level function (`valueEq`, `normalize`, `eqb`,
  `locSup`, `isNormal`, `Repr`) has arms for `mapData`/`chanData` it
  never legitimately meets.
- The detector's soundness against the machine's real accesses is not
  a theorem; it is a table plus an inventory. For NPDRF, "footprint"
  should be definitional.

### U6. The apply position is an encoding every consumer must know

**Where.** Every plan/shift/apply frame fuses "last operand arrives"
with "apply": `.retV v (.strictK op done [] env k)`, `.retV v
(.stmtOpK op nt done [] env k)`, `.retV v (.chanStK op done [] env k)`,
`.retV v (.selectOpsK … done [] env k)`, `.retV v (.syncStK op done []
env k)`, `.retV v (.rhsK rop refs done [] …)`, `.retV v (.tgtOpK sh
ops [] …)`. The operand list is reconstructed as `(v :: done).reverse`
in: `stepFn` (7 arms), the relation (≥ 10 rules), `stepAccesses`
(Race.lean:1290ff, 4 arms), `mapPrunePlan` (Multi.lean:628),
`selectApplyPlan` (:552), `chanApplyChan` (:1453), `arrivalCases`
(:1062), `raceChanEntryReads` (:1600), `raceUpdate`'s `.privateStep`
arm, `Config.atBoundary` (:257), `stepNeeds`/`stepNeedsSeq`
(CLI.lean:986/1095). Meanwhile the CALL frames accumulate in order
with append: `callArgsK … (vals ++ [v])`, `callValArgsK`, `deferArgsK`,
`goArgsK` (Machine.lean:3001ff).

**What it is.** Two accumulator conventions in one file (`v :: done`
then `.reverse`, versus `vals ++ [v]`), and a "the apply is the last
shift" convention that means there is no configuration one can point
at and say "this is the apply of op X to operands vs" — one must
pattern-match `retV v (xK … [] …)` and recompute.

**How it bites.** Every downstream bind/plug lemma over a frame
(`wp_plug_bind`-class) has to normalize `List.reverse` goals and
carry `done.reverse ++ [v]` rewriting; the pool's four extraction
functions (`spawnPlan`, `selectApplyPlan`, `mapPrunePlan`,
`chanApplyChan`) are four ways to spell "is this an apply position and
of what". The choice-consumption accountant in CLI.lean (U10) is a
fifth. A single `Config.applyPos : Config → Option (ApplyHead × List
GoValue × LocalEnv × Cont)` would be one lemma target instead of five.

### U7. gc layout pins are tangled into evaluation

**Where.** `IntKind.bits? .int => some 64` (Value.lean:46);
`maxAllocBytes := 2^48`, `chanHeaderBytes := 112`,
`intExclusiveUpperBound := 2^63` (Ops.lean:245/254/259);
`tySizeAlignFuel` (Ops.lean:306 — go/types `gcSizes` transcribed arm
for arm, including the zero-size-final-field rule and the `sync`
struct sizes); consumed inside `applyStmtOpCore`'s `makeSlice`/
`makeChan` arms and `applyStmtOp`'s `appendSlice` spill arm
(Machine.lean:775ff, :986ff).

**What it is.** A platform (word size, address-space bits, runtime
header sizes, struct layout) hard-wired as constants in the semantic
core, with transfer caveats in docstrings. These are exactly the
IMPLEMENTATION-DEFINED quantities Cerberus keeps behind
`Impl`/`Mem` parameters.

**How it bites.** Every theorem about `make`/`append`/`chan` is
implicitly `gc linux/amd64` and cannot say so in its statement; the
R1/R16 re-envelope (documented as "XIMPL-gated") would have to REWRITE
`applyStmtOpCore` rather than instantiate a parameter; a downstream
"portable" theorem that does not depend on the pins cannot express
that independence.

### U8. Channel-object semantics are smeared across two modules

**Where.** FIFO dequeue `buf.eraseIdx! 0` appears in `applyChanOp`
(Machine.lean:2462ff), `commitClause` (:2759ff), `resumeThread`
(Multi.lean:427ff), and three arms of `applyPairing` (:1114ff);
`.opDone .postOp` is spelled at 22 sites in Machine.lean and 20 in
Multi.lean; `applyChanOp`/`applySyncOp` return a `Config` and know
about `enterRecvTargets`, `.opDone`, `.blockedSend …` — the op
semantics constructs continuations; `resumeRecvDelivery`/
`selectRecvDelivery` (Multi.lean:381/393) are two more deliver
variants; the readiness predicate exists as `clauseReady`
(Machine.lean:1523) AND `wakeReady` (Multi.lean:172) AND
`selectArrivalCases`' waiter-extended readiness (:984).

**What it is.** There is no `Chan` object with `trySend/tryRecv/close`
and a derived `handoff`/`headAndRefill`; each caller re-implements
the queue semantics against the raw `chanData` triple.

**How it bites.** The parked channel-logic (~14.5k lines of WP laws
on the park branch, per memory) needs ONE `Chan.step` to state its
laws about; today every law has five realizations to cover. The
hchan invariant (i)–(iv) (Multi.lean:35–70) is prose across two files.
A change to buffered-channel semantics (say, modelling the Go 1.22+
`synctest` bubble, or a different fairness pin) touches six functions.

### U9. Fourteen fuel towers where structure would do, and the sealing dance they force

**Where.** Ops.lean: `Ty.eqbFuel` (Value.lean:344), `GoValue.eqbFuel`
(Value.lean:703), `resolveDefinedAliasesFuel` (:540),
`canonicalTyFuel` (:561), `Ty.mentionsUnsupportedFuel` (:593),
`tyUncomparableFuel` (:641), `goTypeNameForMessageFuel` (:686),
`normalizeValueForTyFuel` (:1060), `isNormalForTyFuel` (:1158),
`convertValueToTyFuel` (:1271), `defaultValueFuel` (:1435),
`buildStructValueFuel` (:1487), `valueEqFuel` (:1662),
`tySizeAlignFuel` (:306); `typeResolutionFuel := 1024` (:29);
`attribute [irreducible]` on the wrappers with post-seal pins
(Ops.lean:2217ff).

**What it is.** The ONE genuine source of non-structurality is
`Ty.defined name` — a type refers to another by NAME through
`TypeEnv`, and Lean cannot see that Go's type declarations are
acyclic through struct/array. Everything else is collateral: the
value-directed functions (`normalize`, `valueEq`, `isNormal`,
`coerce`) recurse on a VALUE that shrinks and would be structural if
the type lookup were not in the way; `eqbFuel`s exist because the
nested inductives make the derived `BEq` opaque.

**How it bites.** Every unfolding lemma carries `typeResolutionFuel`;
proof sites need `simp [wrapper, fuelFn, typeResolutionFuel]` and the
elaborator dives into `1024` towers unless the wrappers are sealed
(Ops.lean:2205–2216); the docstring at Ops.lean:8–28 records measured
"budget shifts" (a `.defined` chain of 1023 vs 1024 links) as
fail-closed differences nobody wants to think about. The downstream
kit will inherit "the value is normalized at fuel 1024" as a
hypothesis shape on every points-to law.

### U10. Consumption accounting is mirrored by hand, three times, outside the machine

**Where.** `CLI.stepNeeds` (CLI.lean:986, 110 lines) and
`stepNeedsSeq` (:1095) re-derive, shape by shape, WHETHER the next
step consumes and with what bound — calling the machine's own analysis
functions but re-implementing the dispatch ladder (`atBoundary` →
menu → blocked → opDone → spawn → `arrivalCases` → per-shape). A third
mirror lives in `ChoiceTrace.lean` (its docstring says so: "the
site-tagged mirror here must agree with `CLI.stepNeeds`"). `Config.
atBoundary` (Multi.lean:257), `Config.boundarySite` (:1337) and the
`.opDone` emission sites are three more places that must agree on
"where the machine consults the scheduler".

**What it is.** The census is a datatype (good), but the WIDTH of a
consultation is not exposed by the machine; it is recomputed by
consumers. `StepEvent.picks` (Multi.lean:831) carries pool-layer picks
only, by recorded scope decision (the `stepFn` reshape was out of
budget).

**How it bites.** The `Fair : Choices → Prop` hypothesis will be
stated over `PickRecord`s; the enumerator's completeness ("every
consumption is branched") is only as good as the hand mirror. A
future consumer that needs "the labeled sequential trace" (the
recorded reopen trigger) will have to reshape `stepFn` anyway.

### U11. Statement-level special cases and stale shapes

- `Stmt.initialization` (Syntax.lean:248) is a statement whose
  semantics depends on the SHAPE of its continuation: it rewrites the
  enclosing `seq` frame's environment (`Step.initialization`,
  Machine.lean:3021; `stepFn` StepFn.lean:129–137 with the
  `kenv = env` test and an `.internal` otherwise). The header of
  Machine.lean records the consequence: "a bare `.initialization` NOT
  directly under a statement sequence is stuck".
- `Assignee` has TWO classifiers: `assigneeExpr` (Machine.lean:81;
  `none` for `.mapElem`) used by `stmtPlan`, and `targetPlan` (:1276;
  handles `.mapElem`) used by the spine. `Assignee.mapElem`'s
  docstring (Syntax.lean:189–197) still says "Only the channel-receive
  delivery path consumes it", which has been false since BUG-025/037
  routed `assign`/`assignMany`/call write-back through `targetPlan`.
- `Stmt.label` vs `Stmt.labeled` (Syntax.lean:318/303) — the first
  audit's N-1, still open.
- `ExecOutcome` (State.lean:57) has four constructors; three are dead
  for programs (`runProgramPoolM` throws `.internal` on them,
  Multi.lean:1934ff). `GoValue.unit` (Value.lean:606) is produced by no
  arm (grep: only eqb/locSup/eqbSound mention it).
- `Expr.length/capacity (typ : Option Ty)` (Syntax.lean:160–161)
  exists for ONE arm (`some (.pointer (.array n _)) => n`,
  Machine.lean:475/505): a type-static length go/types constant-folds
  anyway.
- `Expr.eqCmp/neqCmp (typ : Ty)` are type-directed while
  `lessCmp/atMostCmp/…` are value-directed (`valueLess`, Ops.lean:1905
  dispatches on value shape): two comparison disciplines.
- `Stmt.newValue (typ : Option Ty := none)` (Syntax.lean:251) lets a
  `new(T)` cell be UNTYPED if a caller passes `none`; the decoder
  happens to pass `some` (NativeToIR.lean:861). The `Option` is a hole
  shaped like the frontend's history.

### U12. The refusal taxonomy has no stated rule

`stuck`, `internal`, `unsupported` are used for overlapping causes:
`bindParams` says `.stuck "extra argument value"` (Machine.lean:647ff)
while `stepFn` says `.internal "malformed assignment target plan"`
(StepFn.lean) for the same class (frontend-contract violation);
`runProgramSetupM` says `.stuck "GoCore function not found"` for a
missing subject (a driver-input error); `wakeReady` documents an
"ABSORBING DEFAULT, named" (Multi.lean:225) that reads a malformed
cell as "not ready". `markInitPhase` (StepFn.lean:922) and
`foreignPruneError` (Multi.lean:669) exist to PREFIX messages so that
triage can tell phases apart — string surgery standing in for
structure. Downstream, nobody can state "the machine never returns
`.internal` on a well-formed program" because `.internal` has no
definition.

### U13. Docstring-as-ledger inside the trusted core

Measured comment/docstring share of lines: Machine.lean 40 %,
Multi.lean 47 %, Race.lean 65 %, Syntax.lean 57 %, Ops.lean 32 %.
Single docstrings: `Cont.mapIterK` ~60 lines (Machine.lean:1826–1886);
`applySyncOp` ~70 lines (:2589ff); `Config.opDone` ~45 lines;
Race.lean's module preamble 318 lines including a call-site inventory,
a probe ledger and a countersign record; `applyStmtOp`'s appendSlice
arm carries a 25-line R16 residual analysis inline. The content is
valuable — but bug ids, probe ids, audit round numbers, and
"the docstring used to claim X" corrections are HISTORY, and history
inside a trusted definition is noise a reviewer must read past to
check the definition. The envelope statements (one paragraph each) are
the part that belongs in situ.

### U14. The Prop-level relation is interleaved with the executable core

`inductive Step` occupies Machine.lean:2941–3692 (≈ 750 lines, 155
rules) plus `Steps`, `Config.terminal`; `StepE`/`StepM`/`schedPick`/
`MultiWf` sit in Multi.lean:1951–2066. Known and owed (the split
plan). The point for THIS review: extract AFTER U1/U6 are fixed, or
the extracted relation carries the twin rules and the reverse
encoding into the downstream repo permanently.

---

## 3. Proposals — semantics-preserving refactors, ranked by value/cost

Conventions. "Preserving" means: for every `Program`, every `Choices`
stream and every fuel, `runProgramPoolM`/`runProgramM` return the same
`Except GoError Result` (same constructor, same message, same
readout), and `Choices` consumption is identical (same sites, same
bounds, same order) unless a bijection is argued. Where a proposal
preserves behaviour only up to heap isomorphism or fuel accounting it
is SAID. For each: change / why nicer / cost / preservation argument /
downstream lemmas simplified. Overlaps with the earlier audits' queue
are cited.

### 3(a). Cheap and local

_A1 status (2026-09-04, design-hygiene arc step (ii)): LANDED `dfa68802` (branch `hygiene-a-series`, 2026-09-04) — flat names kept as `@[match_pattern]` views; design note §A1._

**A1. Split `GoError` into three types (the type change only; the
monad change is B2).**
Change: `Refusal := unsupported msg | stuck msg | internal msg`;
`Terminal := panicked msg | fatal msg | deadlock | raceDetected`;
`Budget := fuelOut`; `Stop := refusal Refusal | terminal Terminal |
budget`. `GoError` becomes an abbreviation-compatible view (or is
deleted once callers move). `GoError.status`/`.message` become
projections per class.
Why nicer: "which stops are Go behaviours" is a TYPE, not a comment;
`Obs` can be `ok | terminal Terminal` and W-1/Q8 (fatal un-statable)
dissolves; `foreignPruneError`/`markInitPhase` operate on `Refusal`
only, by type.
Cost: mechanical; every `throw (.stuck …)` site (hundreds) becomes
`throw (.refusal (.stuck …))` or keeps a helper. Proof churn:
`GoError.isPanic`-style discriminators in MachineSound.
Preservation: a bijection on constructors; `GoError.status` strings
unchanged, so the CLI observation is byte-identical.
Downstream: adequacy statements quantify `Terminal`, not "the subset
of GoError I mean".

_A2 status (2026-09-04, design-hygiene arc step (ii)): LANDED `7cba41cd` — `nextAddr` a derived def; BUG-085's `.internal` refusal kept (recorded deviation); design note §A2._

**A2. Dense heap: `Heap := Array HeapCell`, addresses are indices.**
Change: `Heap.lookup (.base ⟨i⟩) = heap[i]?`; `Heap.set` out of range
is `stuck` (fail closed BY TYPE), never an append; `ExecState.alloc`
is `push`; `nextAddr` becomes `heap.size` (delete the field).
`StateWf`'s `Heap.locSup ≤ nextAddr` becomes "every `.addr` in a cell
value is `< heap.size`" — half the carriers disappear from the
invariant (keys cannot dangle).
Why nicer: the fail-open materialization at Ops.lean:1241ff
(`| none => return { state with heap := Heap.set … }`) becomes
unrepresentable; the two external nets (decoder gid bound, driver
`StateWf` assert) become defense in depth rather than the only
defense. `Heap.lookup_set_ne`, `Heap.set_locSup`, `alloc_shape`
(StateWf/MachineSound) become array lemmas from core.
Cost: small; `Heap` is an `abbrev` with five functions. Proof churn:
the heap lemmas in StateWf.lean:791–840 and `storeLoc_shape`.
Preservation: on `StateWf` states the two representations are in
bijection (`List (Loc × HeapCell)` with distinct `.base` keys all
`< nextAddr` ↔ `Array HeapCell` of length `nextAddr`); every corpus
run starts from a seeded `StateWf` state (asserted at
`runProgramSetupM`) and `Step.preserves_wf` keeps it there, so no run
observes the difference. The differential is the regression.
Downstream: G-REPR's "re-keyed heap" gets a dense address space for
free; `Loc.rootBase < size` is the whole ownership story.

_A3 status (2026-09-04, design-hygiene arc step (ii)): LANDED `6973354b` — plus one root write path `ExecState.updateCell`; `coerceStoredValue` deleted; `newValue typ : Ty`; design note §A3._

**A3. Move `mapData`/`chanData` out of `GoValue` into the cell.**
Change: `HeapCell.content := value (declaredTy : Ty) (v : GoValue) |
mapPayload (entries) | chanPayload (buf cap closed)`; delete
`GoValue.mapData`/`.chanData`; `mapEntries`/`chanCell` read the
payload constructors; `HeapCell.declaredTy : Option Ty` becomes
`Ty` (always present on value cells) and `coerceStoredValue`
(Ops.lean:155–197) is deleted with its 160-line congruence lemma.
`syncData` STAYS a `GoValue` (sync structs are copyable values —
correct as is).
Why nicer: "a value no expression may produce" is enforced by the
type; `valueEq`/`normalize`/`eqb`/`locSup`/`isNormal` each lose two
arms; one store discipline.
Cost: small-medium; `.alloc` gains a content argument; `storeLoc`'s
`.base` arm matches on content. Proof churn: `coerceStoredValue_*`
lemmas deleted, `loadLoc_locSup` restated.
Preservation: payload cells are only ever written whole
(`storeLoc s baseLoc (.mapData …)`/`(.chanData …)` at Machine.lean
:258ff, :851ff, :2462ff and Multi.lean), never through a path, and
`coerceStoredValue`'s catch-all `| _, value => return value` is the
identity on them; typed cells already normalize. Extensional equality
of `loadLoc`/`storeLoc` on all reachable states.
Downstream: points-to for maps/chans is a distinct predicate by
construction (`l ↦ₘ entries`), which is what a channel logic wants.

_A4 status (2026-09-04, design-hygiene arc step (ii)): LANDED `bcdf04c1` — no wire change (the wire already carried `globaladdr gid`; the twin pin pins emitted bytes); the program-text `locSup` deletion is OWED to wave (iii); design note §A4._

**A4. `Expr.global (gid : Nat)` replacing `Expr.locLit`.**
Change: the frontend emits `gid`; the core evaluates `.global gid` to
`.addr (.base ⟨gid⟩)` after checking `gid < σ.globalCount` (a new
`ExecState` field set by `seedGlobals`), else `stuck`. `Expr.locLit`
is deleted; `Expr.locSup`/`Stmt.locSup`/`Func.locSup` (StateWf.lean
:150–290) and the "stored function bodies" clause of `StateWf` go
with it.
Why nicer: program text is address-free again — a `Program` is a
constant; `StateWf` is about the heap.
Cost: small; one decoder arm, one evaluator arm, one relation rule.
Preservation: the decoder's `globaladdr` arm already refuses `gid ≥
globals.size`, and the driver seeds cell `i` at `.base ⟨i⟩`
(StepFn.lean:902ff asserts it), so `.global gid` and `.locLit (.base
⟨gid⟩)` evaluate identically on every accepted program.
Downstream: no `Func.locSup` hypothesis on any program-level theorem;
the split plan's "GoCore extraction" carries less.

_A5 status (2026-09-04, design-hygiene arc step (ii)): LANDED `48d9aba8` — record + `gcAmd64` + single instantiation `platform`; `tySizeAlignFuel` parametric; no `ExecState.platform` field yet (→ B7); design note §A5._

**A5. A `Platform` record, instantiated once.**
Change: `structure Platform where intBits : Nat; maxAllocBytes : Nat;
chanHeaderBytes : Nat; sizes : Ty → TypeEnv → Except Refusal (Nat ×
Nat)`; `def gcAmd64 : Platform`; `IntKind.bits?` takes the platform
for `.int/.uint`; `applyStmtOpCore`/`applyStmtOp` read it from a new
`ExecState.platform` field (or a section variable). Envelope prose
for R1/R16 moves to `gcAmd64`'s docstring.
Why nicer: the pins are one named object; theorems can be stated
`∀ p : Platform` where they are platform-free, and `gcAmd64` where not.
Cost: small; four constants and one function move; every
`IntKind.normalize` call site for `.int` needs the width — make
`IntKind.int (bits)` carry it at lowering, or thread `Platform`.
Preservation: at `gcAmd64` every arm computes the same numbers.
Downstream: re-envelope of R1/R16 is instantiation, not surgery.

_A6 status (2026-09-04, design-hygiene arc step (ii)): LANDED `367dab2f` — footprint keeps `AccessKind × Loc` (recorded deviation); first gate RED (dedup-engine merge rate), fixed by a canonical sorted shadow; design note §A6._

**A6. A `ShadowKey` type instead of phantom `Loc`s.**
Change: `inductive ShadowKey | data (l : Loc) | syncWord (l : Loc)
(k : SyncKind) (w : SyncWordName) | chanObj (l : Loc)`; `SyncWordName
:= state | sema | w | readerCount | done | m` (an enum, not
`String`); `RaceState.shadow : List (ShadowKey × ShadowCell)`;
`overlap : ShadowKey → ShadowKey → Bool` with `data`/`data` via
`locOverlap`, `syncWord`/`syncWord` by equality, `data l`/`syncWord m
_ _` iff `locPrefix l m` (a whole-struct copy covers the words) and
`chanObj` exact. `chanObj` folds into the same shadow (deleting
`RaceState.chanObj` and `chanObjAccess`'s separate cell logic).
Why nicer: `Loc` means "memory path" again; the union rule
(Race.lean:1221) becomes a table over an enum; the two
"keying" disciplines (path overlap vs exact) are one function with two
arms instead of two shadows.
Cost: small; Race.lean only; `syncEntryKinds`/`syncReleaseTailKinds`
change their `at_` helper.
Preservation: verdict-for-verdict — the conflict test is a pure
function of (kind, key, clock) and the key encodings are in bijection
with the phantom paths.

_A7 status (2026-09-04, design-hygiene arc step (ii)): SKIPPED — folded into wave (iii)/B3, whose `Cont` classification is this accessor; measured ~85 pattern sites incl. 24 in proofs (design note §A7)._
_A7 status (2026-09-04, wave (iii)): the ACCESSOR half LANDED with B3 (`cd2a3474`) — `Config.applyPos : Config → Option (ApplyHead × List GoValue × LocalEnv × Cont)`, additive, consumed by ONE consumer (B8's `seqConsumption`) with the inversion lemmas `applyPos_stmt/_select/_sync`; NOT "spelled once" (audit fix F3 correction): the raw `(v :: done).reverse` spelling stays at 64 sites (35 executable / 29 proof) and `applyPos` ADDED 8 spellings + 3 encoding theorems — the flip's true cost is ≈110 sites + 3 restatements, recorded for B4/C3; the accumulator flip and the `applyOperands` spelling NOT done (wave-(iii) note §B3)._

**A7. One accumulator convention and one apply-position accessor.**
Change: pick `done : List GoValue` reversed (the majority) for the
call frames too (`callArgsK`, `callValArgsK`, `deferArgsK`,
`goArgsK`); define `Cont.operands : Cont → Option (List GoValue)` and
`Config.applyPos : Config → Option ApplyPos` (a small sum:
`strict op vs | stmtOp op nt vs | chanOp op vs env k | selectOp … |
syncOp op vs env k | rhs rop refs vs … | target sh vs …`), used by
`stepAccesses`, `atBoundary`, `mapPrunePlan`, `selectApplyPlan`,
`chanApplyChan`, `arrivalCases`, `raceChanEntryReads`, `stepNeeds`.
Why nicer: `(v :: done).reverse` is spelled once; "is this an apply
position" is one function with one inversion lemma
(`applyPos_some_shape`, replacing `mapPrunePlan_some_shape` and its
siblings).
Cost: small-medium; positional case tags in MachineSound shift (the
`fun_cases` proofs are positional — the second audit's recorded
fragility).
Preservation: the accumulator flip is a representation change
inside frames never observed (frames are not values); the accessor is
definitional.
Downstream: bind/plug lemmas over frames normalize one shape.

_A8 status (2026-09-04, design-hygiene arc step (ii)): LANDED `7ff80223` (in part) — renames (`Stop`, `inertLabel`, `allocNew`, `opaqueDecl`), `_nt` drop, `stmtOpNullary` deleted; NOT done with reasons: `GoValue.unit` (not dead — the atomic store result), `ExecOutcome` (→ B4), `itersNormalized` (→ (iii)), `length/capacity typ` (frontend); design note §A8._

**A8. Dead-generality sweep** (extends the queue's Q5).
Delete: `GoValue.unit`; `ExecOutcome.returned/broke/continued`
(`execStmt` returns `ExecState`; `mainOutcome?` returns `Option
ExecState`); `Config.itersNormalized` and its conjunct in
`MachineWf`/`MultiWf` (vacuous by `Cont.itersNormalized_true`);
`Step.stmtOpNullary` + `stepFn`'s nullary arm (no `stmtPlan` arm emits
an empty operand list); `applyStmtOpCore`'s `_nt`; `Stmt.newValue`'s
`Option` on `typ` (make it `Ty`); `Expr.length/capacity`'s `typ`
(constant-fold at the frontend — go/types already does for arrays;
for `*[n]T` emit `intLit n`). Rename `Stmt.label` → `.inertLabel`
(or drop it at the frontend), `Stmt.newValue` → `.allocNew`,
`TypeDef.unsupported` → `.opaque (reason)` where it marks imported
types by design, `GoError` → `Stop` (with A1).
Preservation: each deletion is of an unreachable arm or an
unproducible value; the renames are α.

_A9 status (2026-09-04, design-hygiene arc step (ii)): LANDED `80b4ed89` — rule on `Refusal`; five `.internal` → `.stuck` re-tags; `Refusal.at`/driver error type deferred (→ B2/B7); design note §A9._

**A9. State the refusal rule in one place and apply it.**
Docstring on `Refusal` (three sentences): `unsupported` = a Go
construct/behaviour not modeled, reachable from a well-typed Go
program (the fail-closed frontier); `stuck` = the machine received a
program outside the lowering contract (ill-typed operand, malformed
plan, arity) — a FRONTEND bug; `internal` = a machine invariant broke
between two of its own definitions (unreachable if the machine is
correct). Then re-tag the ~15 mismatched sites (`bindParams`'s arity
→ `stuck` is right; `stepFn`'s "malformed assignment target plan" →
`stuck`; `runProgramSetupM`'s missing subject → a driver error type,
not a machine refusal). Delete `markInitPhase`/`foreignPruneError`
in favour of a `Refusal.at (phase : Phase) (goroutine : Option Nat)`
structured context.
Preservation: refusal messages change (they are diagnostics, not
observations; the harness compares `status`, which is unchanged
within class — VERIFY against `scripts/coverage`'s status grammar
before landing; if `error` vs `stuck` is compared, keep the class
map). Downstream: "on a well-formed program the machine never
returns `.internal`" becomes a stateable (if unproved) property.

_A10 status (2026-09-04, design-hygiene arc step (ii)): LANDED `884e5226` — 19 history blocks moved to `docs/2026-09-04_core-docstring-ledger.md`; Race.lean 68.4%→66.4%, Machine.lean 43.8%→43.6% comment lines — the ≤35%/≤25% targets are NOT met: what remains is envelope statements and design rationale, which this item keeps by its own rule; design note §A10._

**A10. Docstring diet.**
Keep in situ: the envelope statement (≤ 12 lines) and the transfer
caveat. Move to `docs/` (with a stable anchor id the docstring cites,
e.g. `[E9]`, `[R16]`, `[BUG-045]`): probe ids, audit round history,
"this docstring used to say", cost measurements, countersign records.
Target: Machine.lean ≤ 25 % comment lines, Race.lean ≤ 35 %. Not a
semantics change; a reviewability change. Do it in the same commit
series as A1–A9 so the moved prose is re-read once.

### 3(b). A medium arc

**B1. Entry-identity stamps for maps (the queue's Q11) — delete the
prune.**
LANDED 2026-09-03 — design-hygiene arc slice 1, branch
`hygiene-b1-stamps`, landing commit `f6152a6c` (also recorded in
`docs/2026-09-03_design-hygiene-arc.md`'s landing table; design note
`docs/2026-09-03_hygiene-b1-stamps-design.md`). As proposed, with two
recorded deviations: the id counter is PER MAP (kept `StateWf`
field-free), and the `mandatoryRemains` test became pure `Bool` (so
`Step.mapIterNext` lost its success premise). The bisimulation's
"subtlety to prove" pointed at ±0; the other direction — NaN, where
`valueEq` is IRREFLEXIVE — is where the key-set frame was actually
wrong (BUG-088, fixed by construction; `maps/nan-key-range`).
Change: `mapPayload` (or `GoValue.mapData` if A3 is not taken) becomes
`entries : Array (Nat × GoValue × GoValue)` plus `nextId : Nat`.
`mapAssignValue` on an ABSENT key pushes `(nextId, k, v)` and bumps;
on a PRESENT key it `set!`s the same id (`entries.set! i (id, key,
value)` — the E10 always-replace pin unchanged). `mapDelete`/`clearMap`
just erase. `Cont.mapIterK` carries `produced : List Nat` and `start :
List Nat` (ids). `mapIterCandidates` = live entries whose id ∉
produced; `mapIterMandatoryRemains` = some candidate id ∈ start.
DELETE: `pruneIterFramesKey`, `pruneIterFramesAll`, `removeKeyList`,
`contAfterStmtOp`, `keyInKeyList`/`keyInKeys` (the `Except`-monadic
`valueEq` walks), `mandatoryInList`'s `valueEq`, `Config.mapContM`,
`mapPrunePlan`, `foreignPruneError`, `pruneForeignOne/List`,
`pruneForeign`, the `pruneForeign` premise of `StepM.thread`, and
`Step.stmtOpApply`'s `contAfterStmtOp` premise.
Why nicer: a delete is a heap write and nothing else; a `thread` step
is thread-local again (NPDRF obstruction 7 closes by construction);
key membership is `Nat` equality (no `Except`, no fuel); the two
"iteration sets" have a definition a reader can hold in one line;
O(threads × depth) per delete becomes O(1).
Cost: medium. `GoValue.eqbFuel`/`locSup`/`Repr` for the payload;
`mapEntryIndex?`, `mapEntries`, `mapLookupValue`, `mapRangeStartSets`,
`mapIterLiveEntries` change shape; `stmtOpAccesses`/`stepAccesses`
unchanged (the map cell is one location either way). Proof churn:
`filterCandidateList_sup`, `mapIterCandidates_normalized`,
`stepFn_mapIter_*`, `bindIterVars_wf` restated over ids; MultiSound's
`pruneForeign_*` lemmas deleted.
Preservation (bisimulation sketch). Relate a key-frame `(base,
producedK, startK)` to an id-frame `(base, producedI, startI)` under
the invariant `I`: for the live entry table `E`, `producedK ≈ { k |
∃ id, (id,k,_) ∈ E ∧ id ∈ producedI }` and `startK ≈ { k | ∃ id,
(id,k,_) ∈ E ∧ id ∈ startI }` (sets under `valueEq` at `keyTy`), and
`producedI ⊆ ids ever allocated`, `startI = ids live at range start`.
`I` is established at `mapRangeStart` (producedI = [], startI = live
ids ↔ startK = live keys). `I` is preserved by: `mapAssign` on an
absent key (fresh id ∉ producedI ∪ startI ↔ new key ∉ producedK ∪
startK — the created-entry clause); `mapAssign` on a present key
(same id, same key — both sides unchanged); `mapDelete k` (the key's
id leaves `E` so it drops out of BOTH id-sets' image, exactly what the
key-prune removes from `producedK`/`startK` — and it does so in EVERY
frame over that base in EVERY goroutine, which is precisely what
`pruneForeign` achieves by walking; a later re-creation gets a fresh
id, which is exactly the key-prune's "re-created key is a NEW entry");
`clearMap` (all ids leave — the `pruneIterFramesAll` case); every
other step (frames and tables untouched). Under `I`, the candidate
LIST is the same list in cell order (live entries filtered by
`∉ produced`, and the key-side filter `keyInKeys produced k` agrees
with the id-side `id ∈ producedI` by `I`), so the pick WIDTH and the
picked entry at every slot coincide — the choice tape is consumed
identically (no bijection needed; it is the identity). `bindIterVars`
receives the same `(key, value)`. The stop-slot legality
(`mandatoryRemains`) agrees for the same reason. One subtlety to
prove, not assume: `producedK`'s key-set semantics under a
`valueEq`-equal-but-`eqb`-distinct key (float `±0`, interface boxes):
the key-side prune removes ALL `valueEq`-equal keys
(`removeKeyList`), and a `mapAssign` on a `valueEq`-equal key hits the
same entry (`mapEntryIndex?` uses `valueEq`), so the id-side "same
entry" and the key-side "equal key" coincide. The differential is the
regression; the `maps/cross-goroutine-delete-*` membership rows are
the pins.
Downstream: `mapIterK` is a frame over `Nat` sets; the channel-logic
and map laws need no prune lemma; NPDRF's mover kit loses a side
condition.

**B2. The `Result` monad through the helpers; rule twins halved.**
Change: `inductive Result (α) | ok (a : α) | panic (msg : String)`;
helpers that can panic return `Except Refusal (Result α)` (or a
`ResultT`), so `.panic` is never an `Except` error. One function
`deliver : Result GoValue → Cont → Config` (`ok v ↦ .retV v k`,
`panic m ↦ .panicking [⟨runtimeErrorValue m, false⟩] k`) and
`deliverS : Result ExecState → …`. Each apply rule becomes ONE rule
with conclusion `deliver r k`: `strictApply : applyStrictOp s op vs =
.ok r → Step (.retV v (.strictK …)) s (deliver r.1 k) r.2`. Same for
`enterFrame` (returns `Result (Func × …)`), `storeTarget`,
`applyRhsOp`, `applyChanOp`, `applySyncOp`, `applySelect`. The 17
`*Panic` twin rules and the 41 conversion sites disappear;
`enterFrameStep`/`enterFrameDeferPanicking` (StepFn.lean:55/70)
collapse into `deliver`.
Why nicer: one panic representation on the helper side, one on the
control side, one function between them; the relation shrinks by
~17 rules and reads as "apply, then deliver".
Cost: medium; signature churn through Ops.lean (every `panic "…"`
site becomes `pure (.panic "…")` or a `raise` helper in the `ResultT`
monad — mechanical). Proof churn: `fun_cases` positional tags shift;
`exceptCong`-family lemmas restated over the nested monad.
Preservation: `deliver` is exactly what every conversion site does
today (all 41 build `[⟨runtimeErrorValue msg, false⟩]`); helper-level
`.panic` carried the same message. Extensional equality of `stepFn`.
Downstream: half the rule-indexed lemmas; `Progress`-class statements
quantify `Result`.

_B2 status (2026-09-04, design-hygiene arc step (iii)): LANDED `91c57c9e` (branch `hygiene-wave3`) — `Result` at the APPLY BOUNDARY (`toResult` once, `deliver` once; the helper-internal monad route measured and deferred, cost-driven), the 17 twins deleted (159 → 142 rules), `enterFramePick` the one entry funnel (replaces `enterFrameStep`/`enterFrameDeferPanicking` and `spawnStep`'s copy), `Obs := ok | terminal Terminal` (A1's owed payoff — fatal/deadlock statable; engine + checker still refuse them), driver readout `Result` → `Readout`; design note `docs/2026-09-04_hygiene-wave3-design.md` §B2._

**B3. `Cont` classification + generic rebuild (Q4) and field bundling
(Q3).**
Change: `inductive FrameClass | glue | callFrame | resumeMarker |
iterFrame | labelScope | breakScope | stop`; `Cont.tail : Cont →
Option Cont` (every constructor but `stop`); `Cont.withTail : Cont →
Cont → Cont`; `Cont.foldGlue`/`Cont.rebuild (f : Cont → Option (Option
Cont))`. `panicPassthrough` = "if class = glue then tail";
`pushDefer` = "rebuild, acting at the first callFrame";
`recoverThroughWrappers`/`recoverResult` = one walk with a wrapper
flag; `Cont.locSup` = fold over own-payload sups. Bundle
`mapIterK`'s ten fields into `RangeSpec` (static) + `IterState`
(dynamic) and `tgtOpK`'s eleven into `SpineState`; `frame`'s six into
`FrameSpec` with `Cont.barrier k := .frame FrameSpec.barrier k`.
Why nicer: the walks are instances; a new frame is one constructor
plus one `tail`/`withTail` arm plus a class; the eqb tower and
`locSup` become folds.
Cost: medium (wide but mechanical; the second audit's grade). The
positional `fun_cases` proofs are the main churn — do it together
with B2 so the re-proof wave lands once.
Preservation: definitional — each walk's instance is proved equal to
today's definition by `cases k <;> rfl` (30 cases, once).
Downstream: `Cont` has an algebra (`tail`, `withTail`, the class
lemmas); "unwinding strips glue" is a lemma, not 24 rules.

_B3 status (2026-09-04, design-hygiene arc step (iii)): LANDED `cd2a3474` — `Cont.tail`/`withTail`, `FrameClass`/`Cont.class`, ONE well-founded `Cont.rebuild`; `pushDefer`/`recoverThroughWrappers`/`recoverResult` as instances (each proved EQUAL to its 30-arm predecessor before the swap — evidence `b3-prototype/`), `panicPassthrough` = glue → tail, the generic `Cont.rebuild_locSup` replacing three walk inductions, `Config.isTerminal` (threadDone, atBoundary), plus A7's additive `Config.applyPos`; NOT done with reasons: `Cont.eqbF` restructure, field bundling, the accumulator flip, `itersNormalized` deletion (owed); design note §B3._

**B4. Signal unification (Q6) and a thread-level `Status`.**
Change: `inductive Signal | brk | cont | ret | brkTo L | contTo L`;
`Config.signal (sg : Signal) (k : Cont)` replaces five constructors;
one rule `signalStrip : k.class = glue → Step (.signal sg k) …
(.signal sg k.tail)` plus a frame×signal table (`loop`: brk→next,
cont→re-test, ret→pass, brkTo/contTo→match label; `breakableK`:
brk→next, else pass; `labelK`: brkTo L=name→next, else pass;
`frame`: ret→exit, others→stuck; `mapIterK`: as loop). Separately,
at the POOL level: `inductive Status | running (c : Config) | parked
(p : Park) | done (t : Terminal)` with `Park := send … | recv … |
select … | sync …` and `Terminal := normal | panicked msg`; `threads
: Array Status`. `threadDone`, `isBlockedConfig`, `Config.terminal`,
`mainOutcome?`, `execStmtLoop`'s terminal match, and `atBoundary`'s
five terminal arms become projections of `Status`.
Why nicer: ~40 control rules become a 5×7 table; "value/parked/
reducible" is a type; `Config` has 6 constructors (`exec/evalE/retV/
next/signal/panicking`) — and, if C5 is taken, no `opDone`.
Cost: medium-high (metatheory: MultiSound/MultiStreams statements
move). The document half (a table presentation) is free.
Preservation: the signal rules are in one-to-one correspondence with
today's (a `Signal`-indexed family of the same conclusions);
`Status` is a re-packaging of the four parked shapes and five terminal
patterns with an obvious retraction to `Config`.
Downstream: the `Language` instance's `to_val` is `Status.done?`.

_B4 status (2026-09-05, C-arc step 2, lane `c-arc-b4`): LANDED `40fd1903` + `165822ef` — `Signal`, `Config.signal`, the table `signalStep`/`signalRefusal`, rules `signalStmt`/`signal` (32 → 2; the four frame-exit `ret` twins stay as rules, the executable shares `stepFrameExit`); `.panicked` deleted (the abort is `.panicking chain .stop`, `Config.abort?`, rendered by the drivers/pool via `abortMsg`); ONE terminal; `ExecOutcome` deleted; `Thread | running c boundary | aborted msg` with the `Status`/`Done` VIEW (`Thread.status`, agreement theorems) — NOT the stored `Array Status` with `parked (p : Park)`: the consumer's `Expr` is `Config`, so parked shapes stay configurations and `Park` as a type is OWED (design note §2/§7)._

**B5. A `Chan` module.**
Change: `GoLean/GoCore/Chan.lean`: `structure ChanState (buf cap
closed)`; `trySend : ChanState → v → SendOutcome (enqueued st | full |
closedPanic)`; `tryRecv : ChanState → RecvOutcome (got v st ok | empty
| drained zero)`; `close : ChanState → Option ChanState`; `handoff`
(empty-buffer direct) and `headRefill` (full-buffer receive against a
parked sender) as functions on `ChanState × v`; `ready : Dir →
ChanState → Bool` (ONE readiness predicate, used by `clauseReady`,
`wakeReady`, `selectArrivalCases`). `applyChanOp`, `commitClause`,
`resumeThread`, `applyPairing` call these and do only the
control-side plumbing. Plus `Config.completed (c : Config) := .opDone
.postOp c` as the one wrap site (the queue's N-4).
Why nicer: FIFO in one place; the hchan invariants become lemmas about
`ChanState` functions; readiness has one definition.
Cost: medium; Machine.lean/Multi.lean channel arms rewritten as calls.
Preservation: each caller's inlined queue code is replaced by a call
whose body is that code; equational lemmas `applyChanOp_eq` etc. by
`rfl`/`simp`.
Downstream: the channel WP laws are stated about `Chan.*` and lifted
once through the control plumbing.

**B6. Frontend-resolved locals: `VarId := Nat`.**
Change: the decoder numbers every local (including `$`-temps) per
function; `Scope := List (VarId × Loc)`; `Expr.var/ref (id : VarId)`;
`Param.id : VarId` (name kept in a side table for diagnostics only,
like `GlobalDef.name`). `LocalEnv.lookup` compares `Nat`.
Why nicer: no `String` in the dynamics; α-equivalence is trivial;
the reserved-prefix argument for `$` disappears (there are no names to
collide); `seqCont`'s and `initialization`'s env-equality tests become
`Nat`-list equality (and go away entirely under C4).
Cost: medium (frontend + decoder + core signatures; the eqb tower).
Preservation: a bijective renaming; `LocalEnv.lookup` commutes with
the renaming by induction.
Downstream: specs mention variables by `VarId`; the Sym/Rename walks
that existed on the park branch shrink to nothing.

**B7. Split `ExecState` into `ProgramCtx` (static) and `Store`
(dynamic).**
Change: `structure ProgramCtx where types functions methods methodSets
platform`; `structure Store where heap (dense) …`; `ExecState := Store`
and `ProgramCtx` a parameter of the machine (a `variable` or an
explicit argument). `valueEq`/`normalize`/`defaultValue` take
`ProgramCtx` (they already only read `types` — `isNormalForTy` says
so).
Why nicer: "no step changes the program" is by type; the `htypes :
σ₂.types = σ₁.types` hypothesis on `storeLoc_congr`,
`normalizeValueForTy_congr`, `structTagCompatible_congr` (MachineSound
:853–1360) disappears; `StateWf` is about `Store` only.
Cost: medium (signature churn everywhere; mechanical).
Preservation: a record re-packaging; `ExecState` today is literally
the product.

**B8. Consumption widths from the machine itself.**
Change: `stepFn` returns the labeled pick (`Choices.consumeAtE` at
the three apply-layer sites) so `StepEvent.picks` is complete; then
`stepNeeds`/`stepNeedsSeq` (CLI.lean) and ChoiceTrace's mirror are
replaced by a dry run: `stepMulti m [sentinel]` and read the
`PickRecord`'s bound. The State.lean docstring's demand for "an
accountant arm" per site becomes a theorem obligation
(`consumeAtE` is the only consumer) rather than three hand mirrors.
Why nicer: one consumption truth; `Fair` quantifies the machine's own
records.
Cost: medium — the recorded `stepFn` 3-tuple → 4-tuple reshape
("hundreds of pinned equations"). Bundle with B2/B3's re-proof wave.
Preservation: `consumeAtE` projects onto `consumeAt`
(`Choices.consumeAtE_fst_snd`, State.lean:326) — same picks, same
stream.

_B8 status (2026-09-04, design-hygiene arc step (iii)): LANDED `2e69fde0` — NOT the `stepFn` 4-tuple reshape (recorded deferral; "hundreds of pinned equations") but the machine's OWN consumption projection `seqConsumption`/`poolConsumption` with the theorem `stepFn_consumption_none`/`_some` (the old `stepFn_oblivious` DERIVED); `CLI.stepNeeds`/`stepNeedsSeq` and the tracer's `seqSite`/`poolSite` are projections (the three hand mirrors gone); the NEW tracer reproduced the OLD tracer's 23665 per-consumption records byte for byte; the theorem's `some` half's FIRST DRAFT carried a "post-pop delivered panic undoes the pop" disjunct — the consumption-accounting finding (filed on this branch during B8, refuted by lemma in the fix round, never numbered on main) — a PROOF ARTIFACT, refuted by lemma in the audit fix round (`applyTryLock_noPanic`; `Config.appendTargetLocal` + `storeLoc_base_noPanic`; `appendSpill?` mirrors every pre-consult test) and RETIRED; the theorem now states the single pop conclusion under the frontend's hoisting contract; the checker's fragment flags untouched (widening = drift); design note §B8._

### 3(c). The big reshaping — only worth doing before the reasoning repo pins us

**C1. A memory module with an access trace.**
Change: `GoLean/GoCore/Mem.lean` exporting `Mem.alloc`, `Mem.load (l :
Loc) : MemM GoValue`, `Mem.store`, and `Mem.peek` (metadata reads gc
does not instrument: bounds, lengths, type tags), where `MemM := Store
→ Except Refusal (α × Store × List Access)` — every user-visible
load/store EMITS its access at the call site. `stepFn`'s footprint is
then `(stepFn …).accesses` DEFINITIONALLY; `stepAccesses`,
`strictOpAccesses`, `stmtOpAccesses`, `storeTargetAccess`,
`dispatchAccesses`, `projChainTarget` and the 318-line inventory are
deleted; `raceUpdate` folds the emitted list. The O1 narrowing
(`projChainTarget`) is reproduced by having `evalVar`/`deref` under an
immediate projection frame call `Mem.load` at the projected path (the
CEK already knows the continuation at that point — the narrowing
becomes a choice of WHICH path to load, made where the load happens);
the wrapper-hop narrowing (`dispatchAccesses`) becomes "the wrapper's
body loads what it loads", with no shape recognition at all.
Why nicer: the detector is exactly layered over a trace (the memory
model separation Cerberus got right); the "lockstep obligation" is
gone; NPDRF's footprints are what the step did, not a table beside it;
the frontend-shape coupling in Race.lean (U4) dissolves.
Cost: high — `Ops.lean`/`Machine.lean` helpers move into `MemM`;
every `loadLoc`/`storeLoc` call site classified as `load/store/peek`
(the inventory ALREADY does this classification, in prose — it becomes
code). Proof churn: the `_locSup`/`_wf` families restate over `MemM`.
Preservation: (i) the state/value component of every helper is
unchanged (the trace is a writer effect); (ii) the emitted trace at
each step equals today's `stepAccesses` — provable per arm as
`accesses (stepFn s c ch) = stepAccesses s c` for the current table,
which also AUDITS the table once and for all (any disagreement is a
detector bug found, not a semantics change). The racy corpus lane is
the regression.
Downstream: the NPDRF reduction's mover lemmas quantify emitted
accesses; the DRF hypothesis is stated over traces.

**C2. A well-founded type environment; the fuel towers become
structural.**
Change: the frontend emits `typeDefs` in dependency order with
aliases INLINED (`.alias` is identity-erasing by definition —
Syntax.lean:66 says so) and `.defined`-over-`.defined` flattened to
its underlying; `TypeEnv := Array TypeDef` indexed by `TypeIdx : Nat`
with the INVARIANT that a struct/array/defined body refers only to
SMALLER indices (pointer/slice/map/chan/func/interface are leaves for
every type-directed recursion — Go forbids `type T struct{ x T }`
and permits recursion only through those). Then
`defaultValue`/`tySizeAlign`/`canonicalTy`/`tyUncomparable` recurse by
well-founded recursion on `TypeIdx` that the KERNEL can reduce
(`Nat.rec` on the index, or `Fin`-indexed structural descent), and
`normalize`/`valueEq`/`isNormal`/`convert` recurse structurally on the
VALUE with the type looked up (no fuel). `typeResolutionFuel`, the
fourteen `*Fuel` functions, the `irreducible` sealing and the
post-seal pins go.
Why nicer: no budgets, no "1023 vs 1024" caveats, no elaborator
dance; kernel reducibility for free; `Ty.eqb` structural (nested
`List Ty` in `funcType` still needs a hand-written `BEq`, but no fuel).
Cost: high (frontend emission order + every type-directed function
+ the `_locSup`/`_congr` families). Note: `TypeId` keys remain for
diagnostics and interface identity; the INDEX is the recursion
measure.
Preservation: on every well-typed program the fuel never runs out
(depth ≪ 1024), so every fuel function equals its structural
counterpart; the refusals at exhaustion are unreachable today and
unrepresentable afterwards.
Downstream: `normalizeValueForTy` is a structural function the kit
can `simp` without a budget hypothesis; `isNormalForTy_sound`'s
1024-fuel statement becomes a plain equation.

**C3. `Cont` as `List Frame` (K-1 rung 2).**
Change: `inductive Frame` (the 29 non-`stop` constructors minus
their `k` field); `Cont := List Frame`; `Config := Mode × List Frame`
with `Mode := exec stmt env | evalE e env | retV v | next | signal sg
| panicking chain`. Unwinding is `dropWhile isGlue`; `pushDefer` is
"map at the first callFrame"; the recover walk is a fold; `locSup` is
`supBy Frame.locSup`; `eqb` is list equality of frame equality; the
iris-lean `Language` instance's `fill K e` is `++`.
Why nicer: the continuation is a monoid; every "context" lemma
(`wp_bind`) is about list append.
Cost: very high — every rule and proof moves (the first audit graded
it out of budget). Worth it ONLY if done before the downstream repo
pins the `Cont` shape; after that it is a breaking change for them.
Preservation: the isomorphism `Cont ≅ List Frame` is a bijection
(`toList`/`ofList`, `k.tail ≅ tail`), and every rule transports.

**C4. Block-scoped allocation — delete `Stmt.initialization`.**
Change: the frontend already knows every local of a block (go/types);
lower `x := e` inside a block as a `.block` declaration plus
`.assign`, so all locals of a block are allocated at block entry
(`allocDecls`, Machine.lean:637 — already exists) and `seq` frames
have a FIXED environment. Delete `Stmt.initialization`,
`Step.initialization`, the `kenv = env` arm, and `seqCont`'s
splice-equality test (splice unconditionally, or never — with fixed
envs both are fine).
Why nicer: the environment is a property of the frame, not something
statements rewrite; a declaration is not a statement whose meaning
depends on its continuation.
Cost: medium in code, but SEMANTICS-PRESERVING ONLY UP TO HEAP
ISOMORPHISM: allocation ORDER changes (all of a block's locals are
allocated at entry, not at their declaration), so `Loc.base` ids
differ from today's. Nothing in the observation channel exposes
addresses (pointer `==` is preserved by any bijective renaming;
`%p`-style printing is not in the channel; map iteration order is
cell-insertion order, not address order; race keys are renamed
uniformly), and Go itself forbids use-before-declaration, so the
zero-valued-but-undeclared cells are unobservable. But the dedup
certificates and any pinned `repr` of states change, and NPDRF's
obstruction 1 (allocator interleaving) says the reasoning repo must
work up to heap isomorphism anyway. Flagged, not hidden: this changes
`nextAddr` trajectories; the differential (observations) is the
regression; the golden `repr` pins are not.
Downstream: `env` is per-frame data; the "scope = continuation
extent" story becomes literally true.

**C5. `.opDone` out of `Config` into the thread `Status`.**
Change: with B4's `Status`, `.opDone sched inner` becomes `running
(c) (boundary : Option ChoiceSite)` — a per-thread phase flag the
pool consults, not a control constructor. `Config.mapContM`'s
recursive arm, `opDoneInner`, `Config.itersNormalized_opDone`,
`Config.boundarySite`'s `.opDone` arm, and `raceUpdate`'s
`some (.opDone _ _)` probes (replaced by N-1's outcome class in the
event) go.
Why nicer: a scheduling annotation is not control.
Cost: medium. PRESERVING MODULO FUEL ACCOUNTING: today the marker
strip is one `stepFn` step on BOTH drivers (StepFn.lean:769) so that
`execProg_single_eq_execStmt` holds step-for-step; removing the strip
step changes the step count, hence the exact fuel at which a run
reports `fuelOut`. Fuel is a model artifact, and `fuelOut` is not a
Go observation — but the harness's fuel-out rows and `execStmt_mono`-
class lemmas are stated at exact fuels. Either keep the strip as a
no-op step of the flag (then nothing changes and the win is only
representational), or accept the fuel shift and re-pin. Flagged.

_C5 status (2026-09-05, C-arc step 2, lane `c-arc-b4`, gate G-C5 RULED [USER] 2026-09-04 as recommended, relayed): LANDED `165822ef` — `Thread.running`'s `boundary : Option ChoiceSite`, set by ONE rule (`Thread.afterStep`/`Config.afterStepFlag`/`Config.registryCommits`); the strip is a POOL step (`StepM.strip`) so no baseline fuel moves; `Step.opDoneStrip` gone; `execProg_single_eq_execStmt` restated at `fuel + seqOpCount …`; `raceUpdate`'s 12 probes read the flag; the marker's clamp retired (its reason expired at G-U). Design note §3._

### Ranking by value/cost

| Rank | Item | Value (downstream) | Cost | Preservation |
|---|---|---|---|---|
| 1 | B1 stamps (Q11) | Very high: thread-locality restored; 12 defs and 1 premise deleted | M | exact (identity on tape) |
| 2 | A1+B2 outcome grammar / `Result` monad | Very high: rule count −17, one panic carrier, `Obs.fatal` statable | S+M | exact |
| 3 | A2+A3 dense heap, payloads out of `GoValue` | High: fail-closed by type, one store discipline, G-REPR base | S | exact on wf states |
| 4 | B3 `Cont` algebra + bundling (Q3/Q4) | High: 6 walks → 1 combinator; new frame = 3 edits | M | definitional |
| 5 | A4 `Expr.global` | High per unit cost: program text address-free | S | exact |
| 6 | C1 memory module + trace | Very high for NPDRF/detector trust | H | trace-equality audit |
| 7 | B4 signals + `Status` (Q6) | High: `Language` instance shape; 40 rules → table | M-H | exact |
| 8 | A7 apply-position accessor | Medium-high: one shape for bind/plug lemmas | S-M | definitional |
| 9 | B5 `Chan` module | High for the channel logic | M | equational |
| 10 | A5 `Platform` | Medium: portability stated, not commented | S | exact at gcAmd64 |
| 11 | B6 `VarId` | Medium: α-equivalence trivial | M | bijective renaming |
| 12 | B7 `ProgramCtx`/`Store` | Medium: `htypes` hypotheses vanish | M | re-packaging |
| 13 | C2 well-founded `TypeEnv` | Medium-high: no fuel anywhere | H | exact (fuel unreachable) |
| 14 | A6 `ShadowKey` | Medium: `Loc` means one thing | S | verdict-identical |
| 15 | B8 widths from the machine | Medium: `Fair` over real records | M | projection lemma |
| 16 | A8/A9/A10 sweep, refusal rule, docstring diet | Reviewability | S | α / diagnostics |
| 17 | C3 `List Frame` | High but only pre-pin | VH | isomorphism |
| 18 | C4 block-scoped allocation | Medium | M | up to heap iso (flagged) |
| 19 | C5 `.opDone` out of `Config` | Medium | M | modulo fuel (flagged) |

Suggested sequencing: A-items in one series (each a small commit with
the full differential); then B1 alone (its own re-proof wave); then
B2+B3+B8 as ONE re-proof wave (they all shift the positional
`fun_cases` tags — pay once); then B4/B5/B6/B7 in any order; C1/C2
only if the downstream pin date allows; C3–C5 by [USER] decision.

### Not mine to propose, but note (would change semantics or its accounting)

- **`ChoiceSite.policy.consumeAtOne` uniformization.** `mapIter`
  pops even at width 1 (State.lean:239, "memo §5 ruling Q3"); every
  other site does not. Making the rule uniform ("consume iff bound ≥
  2") leaves the SET of behaviours unchanged but changes which stream
  realizes which member — every fixed-stream baseline would re-pin.
  A bijection on streams exists (drop the width-1 mapIter picks) but
  the baselines are stream-indexed. [USER] call.
- **Promotion in the core instead of frontend wrappers.** Modelling
  embedded-field method promotion natively (method-set lookup through
  `FieldDef.embedded`) would delete `Func.wrapper`, the wrapper
  transparency in `recoverResult`, `wrapperForwardArg`/`recvFieldChain`
  and the D2 wire contract's "full method set incl. promoted". It is
  behaviour-preserving in intent but changes the frontend contract and
  the detector's hop-path narrowing argument (gc's autogenerated
  wrapper loads only the hop; a native model must reproduce that
  footprint deliberately). A frontier decision, not a refactor.
- **E-class evaluation-order pins realized by frontend ANF** (E12/E13
  are "structural (frontend ANF)"): the core cannot state them because
  the frontend has already sequenced the operands. A core that
  admitted unsequenced operand evaluation (a Cerberus `unseq`) would be
  a semantics WIDENING — the doctrine's business, not this review's.
- **`Stmt.mapRange` as the only primitive range**: fine; but range
  over integers/slices/strings desugared at the frontend means the
  core's `while` sees `$ridx`/`$rlen` temps and the RACE FOOTPRINT of
  a range-over-slice is the desugar's footprint. If gc's instrumented
  footprint for `for i, v := range s` ever differs from the desugar's
  (it reads the header once; the desugar reads `$rcoll` per iteration
  — currently a whole-cell read of a slice HEADER, race-equivalent),
  that is a fidelity question, not a niceness one.
- **`GoValue.eqb` used as eface identity** in `renderPanicHead`
  (Machine.lean:1690): structural equality stands in for gc's
  pointer-identity collapse and fails closed on the ambiguous case.
  Modelling boxing identity would be a semantics addition.

---

## 4. Comparison to Cerberus, where it illuminates

Cerberus (Memarian, Gomes, Davis, Kell, Richardson, Watson, Sewell;
POPL 2019 and its Core language) is the right yardstick for a
"weakest machine the standard permits" project, and the doctrine
already cites it. Four things it got right that this core lacks, and
three that do not transfer.

**What transfers.**

1. **The memory model is a module behind an interface.** Cerberus'
   `Mem` signature (allocate, kill, load, store, pointer arithmetic,
   provenance operations) has several instantiations (concrete,
   symbolic, PNVI variants) and the dynamics of Core never look
   inside. Here the store is an association list of tree-shaped
   values with paths into them (U5); load/store are structural on the
   path but the OVERLAP relation the detector needs is defined in a
   different module (Race.lean:356), the frame lemma for same-root
   paths is an open obstruction (NPDRF.lean), and the footprint is a
   table beside the semantics rather than an effect of it. Proposals
   A2/A3/C1 are the transfer: dense addresses, payload cells typed as
   such, and access as an EFFECT of `load`/`store`. Cerberus also
   shows the payoff: the same Core ran under three memory models
   because the dynamics never depended on the representation. A
   per-field points-to logic downstream is exactly a fourth "memory
   model instantiation" — the interface is what makes it cheap.

2. **Undefined/implementation-defined behaviour is a CONSTRUCTOR with
   a catalogue, and implementation-defined quantities are PARAMETERS
   (`Impl`).** Cerberus' `undef UB_xxx` names the standard's UB
   clause; `Impl` supplies sizes, alignments, integer widths. Here the
   refusal constructors carry a `String` (U12) and the
   implementation-defined quantities are constants in `Ops.lean` (U7).
   Go has almost no UB, so the catalogue is small — but it EXISTS:
   the fail-closed frontier (`unsupported`) is a catalogue of "the
   standard permits several things here and we model none/one", and
   the `PINNED LATITUDE` docstrings ARE `Impl` parameters written as
   comments. A1/A5/A9 make them types and a record.

3. **One small Core, one big elaboration, and the elaboration IS the
   semantics of the surface constructs.** Cerberus' Core has a handful
   of forms (`pure`, `memop`, `let`, `if`, `case`, `unseq`, `nd`,
   `bound`, `save/run`, procedure call); everything else — every C
   operator's promotion rules, every implicit conversion, `switch`,
   loops — is elaborated. The elaboration is INSPECTABLE (Cerberus
   prints Core) and the Core dynamics are ~one page. Here the IR has
   ~55 `Expr` constructors and ~40 `Stmt` constructors, and the
   statement layer contains what Cerberus would call builtins or
   library (`appendSlice`, `copySlice`, `sortSlice`, `clearSlice`,
   `clearMap`, `mapLookup`, `typeAssert` as statements). The
   plan/shift/apply schema (§1 item 5) is this core's Core: `StrictOp`
   and `StmtOp` ARE the builtin table. The un-nice part is that the
   BOUNDARY is not drawn: some desugaring happens at the frontend
   (ranges, `for`, `+=`, method promotion, ANF hoisting), some at the
   decoder (`$`-temps, comma-ok temps), some in the machine
   (`Assignee` desugaring, `seqCont` splicing, `initialization`
   frame rewriting). Cerberus' discipline — the elaborator produces
   Core that needs NO further desugaring, and Core has no
   "unsupported" node — is the cure for U4 and U11: delete the five
   `unsupported` IR constructors (the decoder refuses; nothing
   changes for accepted programs), resolve names to `VarId` (B6),
   allocate at block entry (C4), and the machine's statement layer
   becomes a Core.

4. **Nondeterminism is a Core construct, explored by a driver.**
   Cerberus' `nd` (and `unseq` for unsequenced evaluation) puts every
   non-determinism in the term, and the "exhaustive" and "random"
   drivers are separate from the semantics. GoLean's choice tape is
   the same separation done BETTER for a fairness story (the tape is
   data one can quantify over, the sites are tagged), and worse in one
   respect: the WIDTH of a consultation is not part of the site's
   interface (U10) — a Cerberus `nd` lists its alternatives. B8 (the
   machine emits `PickRecord`s with bounds everywhere) closes the gap.

**What does not transfer.**

1. **Go has no UB in C's sense; racy programs are BOUNDED.** Cerberus
   spends most of its complexity on pointer provenance and on making
   UB explicit because C programs routinely live on the edge of it.
   Go's memory model says racy programs may crash or corrupt but stays
   within the language's type safety envelope, and this project's
   doctrine REFUSES below the DRF line (`raceDetected`). So the
   detector, not a provenance model, is the right instrument — and the
   right place to spend effort is making the detector's footprint
   definitional (C1), not building provenance.

2. **Goroutines and channels are primitive; Cerberus' concurrency is
   bolted on.** Cerberus' C11 concurrency went through a separate
   `cmm` executable memory model and `par`; GoLean's registry
   (channels, sync, select, spawn) is the language. There is no
   Cerberus template for "channel as a synchronization object with
   FIFO + rendezvous + HB edges" — the closest analogue is Cerberus'
   own lesson that the OBJECT model (there: memory objects) wants its
   own module with an interface (B5).

3. **Cerberus validates by symbolic execution and a test suite;
   GoLean validates by differential testing against a pinned oracle
   and REFUSES what it cannot compare.** This is a genuine
   methodological advance for a language with a single dominant
   implementation and a compatibility promise, and nothing in
   Cerberus does it. The consequence for niceness: every refactor
   above has a mechanical regression (the full `--diff`) that Cerberus
   never had — which is why this review can propose representation
   changes (A2, A3, B1, B6) with a straight face.

One more Cerberus lesson, stated because it is the cheapest to take:
**Cerberus' Core is PRINTABLE and the paper's semantics IS the
printed Core.** The opsem write-up this project owes (S6a) will be
easier to write, and to check against the code, once the rules are
~130 instead of 155 (B2), the signals are a table (B4), and the
docstrings say what a rule MEANS rather than when it was last
corrected (A10).

---

## 5. If you only do three things

For the coordinator and Mike. Each is semantics-preserving, each has
the full differential as its regression, and each removes a whole
class of downstream pain rather than an instance.

**1. Entry-identity stamps for maps (B1 — the queue's Q11).**
Give every map entry a fresh `Nat` id; make `mapIterK`'s `produced`
and `start` sets of ids. Delete `pruneIterFramesKey`,
`pruneIterFramesAll`, `contAfterStmtOp`, `removeKeyList`,
`keyInKeys`, `Config.mapContM`, `pruneForeign*`, `foreignPruneError`,
the `pruneForeign` premise on `StepM.thread`, and the O(threads ×
depth) walk per delete. A thread step becomes thread-local again
(NPDRF obstruction 7 closes by construction), key membership becomes
`Nat` equality instead of an `Except`-monadic `valueEq` walk, and the
choice tape is consumed IDENTICALLY (same candidates in cell order,
same widths, same stop slot — §3 B1 has the bisimulation). This is
the single largest simplification available for the cost, and it
removes the one place where the semantics rewrites other goroutines'
continuations.

**2. One outcome grammar (A1 + B2).**
Split `GoError` into `Refusal` / `Terminal` / `Budget`, make the
helpers return `Result α := ok α | panic msg` instead of throwing
`.panic`, and add ONE `deliver : Result → Cont → Config`. The 17
`*Panic` twin rules and the 41 hand-written `.error (.panic msg) =>
.ok (.panicking …)` conversions disappear; `fatal` becomes statable in
`Obs` (closing the second audit's W-1/Q8); the downstream adequacy
statement quantifies a `Terminal` type instead of "the subset of
`GoError` I mean". Do it BEFORE the `Step` relation is extracted to
the reasoning side, or the twins travel with it.

**3. The memory representation, in two cheap moves (A2 + A3), with
C1 as the arc that follows if the pin date allows.**
Make the heap a dense `Array HeapCell` (addresses are indices;
storing past the end is `stuck` by type, not a materialized cell) and
move `mapData`/`chanData` out of `GoValue` into a typed cell payload
(one store discipline; `coerceStoredValue` and its 160-line congruence
lemma deleted). Both are exact on well-formed states, which every run
starts in and stays in. They are the foundation the downstream
per-field points-to (G-REPR) will otherwise have to build for itself
on top of an association list of trees — and they set up C1, the
memory module whose `load`/`store` EMIT their accesses, which turns
the race detector's 318-line prose inventory into a theorem
(`accesses (stepFn …) = stepAccesses …`) and makes NPDRF's footprints
definitional.

Everything else in §3 is worth doing; these three change what the
downstream repo has to prove ABOUT us rather than how pleasant our
file is to read.

---

### Appendix: counts used above (all at `b5abacc1`)

- `Cont`: 30 constructors (Machine.lean:1728–1976, 249 lines incl.
  docstrings). `Config`: 16 (Machine.lean:2330–2433).
- `Step`: 155 rules (Machine.lean:2941–3692).
- Full `Cont` walks in the core: `panicPassthrough`,
  `recoverThroughWrappers`, `recoverResult`, `pruneIterFramesKey`,
  `pruneIterFramesAll`, `Cont.locSup`, `Cont.itersNormalized`,
  `Cont.eqbF`; partial: `pushDefer`, `stepAccesses`.
- `Choices.consumeAt`/`consumeAtE` call sites in Machine/StepFn/Multi:
  7 (StepFn.lean:621 mapIter; Machine.lean:1046 appendSpill, :2922
  l2Entry; Multi.lean:1087 l2Arrival, :1273 l4Waiter, :1391 the
  boundary site {l1Sched, postOp, backEdge}, :1893 l5ExitWindow).
- `.panicking [⟨runtimeErrorValue …` conversion sites: StepFn 14,
  Machine 24, Multi 3.
- `.opDone .postOp` emission sites: Machine 22, Multi 20.
- `eraseIdx! 0` (FIFO dequeue): Machine 2, Multi 4.
- Terminal-shape pattern `.returning .stop` enumerated at: Multi.lean
  :150, :272, :1831; StepFn.lean:833; MachineSound.lean:706, :2714,
  :3198; NPDRF.lean:247.
- Comment/docstring share: Machine 40 %, Multi 47 %, Race 65 %,
  Syntax 57 %, Ops 32 %, StepFn 29 %, State 36 %, Value 32 %.
- Fuel families in Ops/Value: 14 (listed in U9); `typeResolutionFuel
  = 1024`; wrappers sealed `irreducible` at Ops.lean:2217.
- `stepNeeds` (CLI.lean:986–1094): 108 lines mirroring the machine's
  consumption ladder; `stepNeedsSeq` (:1095–1123): 28.
