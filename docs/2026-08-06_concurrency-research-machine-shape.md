# Concurrency research: machine shape, metatheory, statement idiom (2026-08-06)

Research note — a DESIGN SPACE map, not a decision record. Decisions belong to
the user. `[FACT]` entries carry `file:line` citations against the current
tree (worktree of `main` @ a38e086); `[OPTION]`/`[ANALYSIS]` are the mapped
choices and my cost/benefit reads. Binding prior doctrine that constrains
everything here: `docs/2026-08-04_nondeterminism-doctrine.md` (esp. its
"Inputs to the concurrency arc" section — DRF-SC fail-closed races, `go run
-race` second oracle, litmus corpus, fairness quantifier decided in the design
note); `docs/2026-07-22_f4-concurrency-model.md` (memory-op granularity, SC,
sync-primitive ladder, R4/R5 staging); `docs/2026-08-03_sem-adequacy-arc.md`
§Goal + decision 5 (fork/join specs stay pre/post over `sem`; differential
weakens to membership).

---

## 0. Ground truth: the sequential machine as it stands

- [FACT] The machine is a CEK machine over `(Config, ExecState)`:
  `Config ::= exec | evalE | retV | next | breaking | continuing | returning |
  breakingTo | continuingTo | panicking | panicked`
  (`GoLean/GoCore/Machine.lean:1381-1406`), continuations `Cont` with ~27
  constructors (`Machine.lean:1079-1191`). The environment is in the control
  (`env`-in-config); `ExecState` is `{types, functions, methods, heap,
  nextAddr}` only (`GoLean/GoCore/State.lean:35-41`). ALL mutable data —
  including every local variable — lives in heap cells (`bindParams`/
  `allocDecls` allocate cells, `Machine.lean:481-498`); the env maps names to
  `Loc`s.
- [FACT] `stepFn : ExecState → Config → Choices → Except GoError (Config ×
  ExecState × Choices)` (`GoLean/GoCore/StepFn.lean:81`) is total,
  deterministic given the stream, and fails closed
  (`.stuck`/`.unsupported`/`.internal`) everywhere the relation is silent.
  Terminal configs throw, so `stepFnIter` prefixes are genuine run prefixes
  (`StepFn.lean:603-617`).
- [FACT] The `Choices` stream (`State.lean:130-147`) is consumed at exactly
  TWO sites: the `mapIterK` pick (`StepFn.lean:439`) and the `appendSlice`
  spill capacity (`Machine.lean:839-840`); `applyStmtOpCore` is choices-free
  by construction (`Machine.lean:619-626`). Note for later:
  `Choices.consume` POPS the head even at bound 1 (`State.lean:143-147` —
  `c :: rest => (c % b, rest)` with `b = max 1 bound`). Any new
  "pick among 1" site that calls `consume` will consume stream elements and
  desynchronize every existing adversarial-stream corpus run.
- [FACT] Correspondence kit: `stepFn_sound` (`MachineSound.lean:44`),
  `step_complete` (∃-stream realization, `:289`), `step_det` over
  `Config.choiceFree` (`proofs/GoLeanProofs/Inversions.lean:24-45`),
  `stepFn_oblivious` (non-consuming arms succeed identically under every
  stream, `MachineSound.lean:2377-2392`), `step_complete_any_wf` (`:2156`),
  `execStmtLoop_ok_or_fuelOut` (`:2179`), and the ∀-streams kernel checker
  `allStreamsOk` (`:2293`) + `execStmtLoop_ok_of_allStreamsOk` (`:2740`),
  which branches ONLY at nonempty `mapIterK` picks and fails closed at any
  `appendSlice` apply position (`consumesAppendSlice`, `:2274`).
- [FACT] The invariant: `StateWf σ := ExecState.locSup σ ≤ σ.nextAddr`;
  `ConfigWf bound c`; `MachineWf σ c := StateWf ∧ ConfigWf ∧
  Config.itersNormalized` (`GoLean/GoCore/StateWf.lean:415-435`), decidable,
  preserved per step (`Step.preserves_wf`, `MachineSound.lean:601`;
  `stepFn_preserves_wf` `:609`).
- [FACT] Statement idiom (`proofs/GoLeanProofs/Surface.lean`): `InitialSplit`
  (`:139`), `GoTriple` (`:209`), `Terminates` (∃N ∀fuel≥N ∀ch, `:347`),
  `TerminatesNormally` (`:361`), `ProgressExec` (`:383`), `ReachableExec`
  (`:260`), `GoInvariant` (`:299`), `GoSpec` (`:453`), `GoSpecT` (`:503`),
  `GoFuncSpec` (`:488`). All quantify `execStmt` runs over ALL choice
  streams; the relation (`Step`/`Steps`) is proof infrastructure, banned from
  designated statement closures (statement-TCB gate).
- [FACT] The Iris seat already has the fork-shaped hole: `GoPrimStep (c, s)
  [] (c', s', [])` — the third component is `List Config` forked threads,
  currently always `[]` (`proofs/GoLeanProofs/Lang.lean:36-41`). iris-lean's
  `Language.primStep` is `Expr × State → Obs → Expr × State × List Expr →
  Prop` (`deps/iris-lean/Iris/Iris/ProgramLogic/Language.lean:57`) and its
  generic thread-pool `Step` is the `t₁ ++ e :: t₂` congruence rule
  (`Language.lean:114-131`). The roadmap anticipates exactly this: "forked
  goroutines are the `List Expr` component of the step relation"
  (`docs/roadmap.md:55`).
- [FACT] Memory ops have a two-function chokepoint: every heap access in
  Machine/StepFn routes through `loadLoc`/`storeLoc`
  (`GoLean/GoCore/Ops.lean:934,956`) plus `ExecState.alloc`
  (`State.lean:153`); no other caller of `Heap.lookup`/`Heap.set` exists in
  the step layer (verified by grep). This matters for race detection (§4).
- [FACT] Channels/goroutines are entirely absent today: no `chan` in
  `Value.lean`/`Syntax.lean`/`NativeToIR.lean` (grep-clean); all 38 channel
  corpus cases FAIL at `frontend-export` (`baselines/native-full.tsv:84-121`)
  — expected coverage gaps.

---

## 1. Multi-goroutine configuration: the machine-shape options

### Option A — ThreadPool machine, fine-grained (pick at every step)

Shape: a new top layer, leaving `Config`/`ExecState` untouched:

```
structure MultiConfig where
  threads : Array Config        -- index 0 = main
  shared  : ExecState           -- one heap, one allocator
  chans   : <see §2>            -- if not folded into the heap
stepMulti : MultiConfig → Choices → Except GoError (MultiConfig × Choices)
```

One `stepMulti` step = (i) compute the runnable set (not terminal, not
blocked); (ii) if `|runnable| > 1`, consume ONE scheduler choice; (iii) run
`stepFn shared threads[i] choices` for the picked thread; (iv) a `go`-spawn
step appends a fresh `Config` to `threads`.

- [ANALYSIS] **Totality/determinism-given-stream**: preserved trivially —
  `stepMulti` is a total function of `(MultiConfig, Choices)`; the doctrine's
  "one mechanism" rule holds (scheduler picks join map-pick and spill-cap in
  the ONE stream). Executability — the differential trust root — is intact.
- [ANALYSIS] **Correspondence kit**: `step_det` stays PER-THREAD exactly as
  is (a picked thread's step from a choice-free `Config` is unique);
  the new nondeterminism is confined to the pick site, mirroring
  `mapIterNext`. `stepFn_oblivious` is reusable verbatim (the picked thread's
  step is the same `stepFn`). Soundness/completeness against the Prop level
  is a thin wrapper IF the relation stays per-thread (below).
- [ANALYSIS] **The relation**: keep `Step` per-thread and extend its type
  with a spawn component — `Step : Config → ExecState → Config → ExecState →
  List Config → Prop` (or a twin `StepF` to avoid touching ~140 existing
  rule constructors; every existing rule spawns `[]`). Then iris-lean's
  GENERIC thread-pool `Step` (`Language.lean:114`) provides interleaving for
  free on the proof side, and `stepMulti` is the executable instantiation of
  that generic pool step. This is the GooseLang architecture exactly
  (`deps/perennial/src/goose_lang/lang.v:234` `Fork (e : expr)`; `:1344`
  `Fork e => ret ([], Val #(), [e])` — fork is a base step whose `efs`
  carries the new thread; the pool is the language interface's business).
  It is also the charter's option (c); executable-side, (a) and (c) are the
  same machine — the distinction is only where the pool lives in the
  Prop layer, and per-thread-relation + generic pool is strictly less new
  proof surface.
- [ANALYSIS] **`allStreamsOk` explosion**: today the checker branches only at
  map picks (`MachineSound.lean:2293`). Under Option A it must branch over
  the runnable set at EVERY step: `|runnable|^steps` paths. For a fork/join
  toy (main + 1 goroutine, ~20 steps interleaved) that is ~2^20 ≈ 10^6 kernel
  branches — marginal; for anything real, hopeless. Kernel-discharged
  `Terminates` survives only for tiny pinned programs; real concurrent
  termination proofs move to Iris (§5) or to a partial-order-reduced checker
  (a research project of its own — flag, don't promise).
- [ANALYSIS] **StateWf**: extends componentwise — `MultiWf m := StateWf
  m.shared ∧ ∀ i, ConfigWf m.shared.nextAddr m.threads[i] ∧
  itersNormalized …` plus channel-state boundedness (§2). All existing
  `locSup` machinery (`StateWf.lean:66-358`) reuses as-is because `Config`
  is unchanged; the checker stays decidable (finite array). Preservation is
  the existing `Step.preserves_wf` for the picked thread + a frame lemma
  "other threads' `ConfigWf` survives a foreign step" (their configs are
  untouched; `nextAddr` only grows — `ConfigWf.mono`, `StateWf.lean:442`).
- [ANALYSIS] **Cost center**: the fuel/step count multiplies; every existing
  granularity coarseness (§3) becomes semantically load-bearing.

### Option B — coarse interleaving: pick only at communication/blocking points

The scheduler consumes a choice only when the running thread reaches a
"yield point" (channel op, `go`, select, block, termination); between yield
points a thread runs a maximal sequential burst.

- [ANALYSIS] **Pro**: exploration and kernel checking become tractable
  (branch count ~ #comm-ops, not #steps); fuel stays near-sequential;
  `allStreamsOk` survives in recognizable form; sequential conservation is
  immediate (a single thread has no yield points → the burst IS the
  sequential run).
- [ANALYSIS] **Con — and it is BUG-002's exact class**: coarse scheduling is
  observationally complete for Go only under a REDUCTION theorem ("for
  race-free programs, every fine-grained SC execution is equivalent to a
  yield-point-scheduled one" — Lipton movers over HB-ordered accesses). That
  theorem is true under DRF but is real metatheory nobody has built here; and
  it is FALSE for racy programs — which is tolerable only because races fail
  closed (§4), i.e. Option B is sound ONLY IF race detection is airtight at
  access granularity. Baking B in as the ground truth without the reduction
  argument written down is precisely "atomicity decomposition unobservable
  sequentially, bites under concurrency" (granularity ledger,
  `docs/2026-07-23_reshape-r1r2-machine-design.md:121-163`). The F4 decision
  of record is fine-grained memory-op steps
  (`docs/2026-07-22_f4-concurrency-model.md` §1, user direction) — B as
  ground truth would reverse a recorded user decision.
- [ANALYSIS] **B as an optimization layer over A** is the defensible hybrid:
  A is the semantics; a coarse explorer is a testing/proof accelerator whose
  soundness is the (later) reduction theorem, or which is used only in the
  membership lane where under-exploration is conservative. Flag as staging,
  not semantics.

### Option C — GooseLang-literal: expression-level fork, pool in the logic only

Make `Config` itself the "thread" and never define an executable pool —
concurrency exists only in the Iris generic layer, execution stays
single-threaded.

- [ANALYSIS] Rejected by the project's own doctrine: the interpreter is the
  statement language and the differential trust root (sem-adequacy decisions
  1-2); a concurrency story with no executable multi-thread machine cannot be
  differentially tested against `go run` at all, and fork/join `GoSpec`s
  (§5) would have no interpreter-level notion to be stated in. Perennial can
  live logic-only because their statements ARE Iris triples; ours are not.

### Recommendation-shaped summary (still the user's call)

Option A (executable ThreadPool; per-thread relation with spawn component;
one Choices stream; scheduler choice consumed only when `|runnable| > 1`)
dominates on: doctrine fit, Iris fit (the `List Config` slot already exists,
`Lang.lean:36-41`), StateWf reuse, sequential conservation (§7), and honest
granularity. Its cost — kernel-checker explosion — is real but is a cost of
the DOMAIN (schedule quantification), not of the shape; B only hides it
behind an unproven reduction theorem.

---

## 2. Channels: primitive machine objects vs modeled-over-heap

### The prior art, both directions

- [FACT] Perennial-new models channels as a verified Go LIBRARY: `chan.v`
  delegates every op to `channel.Channel[T]` methods
  (`Receive`/`Send`/`TrySend`/`TryReceive`/`Close`/`Len`/`Cap`), i.e. Go
  model code over mutex+heap, and `select` is "shuffle the non-default
  clauses, try in order, else default / retry"
  (`deps/perennial/new/golang/defn/chan.v:8-63,96-118`; model code at
  `deps/perennial/new/code/github_com/mit_pdos/perennial/goose/model/channel.v`).
  GooseLang's PRIMITIVES are only load/store/CAS/fork; channels are not
  machine objects.
- [FACT] Our maps set the in-repo precedent for the other route: a `MapValue
  {base : Option Loc}` reference value over a `.mapData` heap cell
  (`GoLean/GoCore/Value.lean:350,465-466`), nil = `base none`, ops as
  machine steps.

### Option P — primitive channel objects (machine steps)

- [ANALYSIS] For an EXECUTABLE, differentially-tested, kernel-evaluable
  machine this is close to forced, for four independent reasons:
  1. A library model needs `sync.Mutex` + spin/park loops FIRST — inverting
     the F4 ladder (`f4-concurrency-model.md` §6 puts channels at rung 3,
     but a channel LIBRARY would put mutex at rung 0 of the channel slice)
     and making every channel op a nondeterministic multi-step spin whose
     fuel is schedule-dependent — ∀-stream `Terminates` via kernel
     evaluation dies immediately, and strict-lane determinism dies with it.
  2. Fault identity: `close(nil)`, double-close, send-on-closed panic
     messages and the deadlock fatal must match `go run` verbatim (the
     runner compares fault IDENTITY); primitive steps pin these directly.
  3. Our TCB philosophy inverts Perennial's: their model code is NOT trusted
     (it is verified against GooseLang); our interpreter IS the trusted
     statement language, so "channels as library" would still sit inside the
     trust surface — the TCB-size argument for the library route evaporates.
  4. The 38-case corpus is single-goroutine deterministic (§6) — primitive
     buffered ops give a strict-lane slice with zero scheduler machinery.
- [ANALYSIS] The honest cost: the machine grows a new stateful object kind
  with its own wf, its own envelope decisions (waiter order, select pick),
  and its own granularity entries — all trusted, all needing the
  differential + review (nondet doctrine: the too-wide direction has no
  oracle).

### Option L — library/modeled-over-heap

- [ANALYSIS] Pro: smallest machine delta (only mutex+park primitives);
  maximal proof reuse from Perennial's channel proofs shape; one fewer
  primitive envelope surface. Con: everything in P's list above; plus the
  differential would compare a spin-loop artifact against `go run`'s runtime
  scheduler — even MEMBERSHIP-lane comparison gets murky (len/cap
  observations mid-spin). Not viable as the first concurrency slice; could
  become the modeling route for `sync.Mutex`/`WaitGroup` LATER (over
  channels or over atomics), which is a separate decision.

### Where channel state lives (under Option P)

- [OPTION] P1 — heap-cell channels, the map precedent: `GoValue.chan
  (value : ChanValue)` with `ChanValue {base : Option Loc, dir?}`, and a new
  cell payload `GoValue.chanData {buf : Array GoValue, cap : Nat, closed :
  Bool}` at the base loc. nil channel = `base none` (matches
  `channels/nil-values`: len/cap 0, `== nil` true). Pros: `Heap`,
  `locSup`/`StateWf`, `heapletOf`, gen_heap wiring, `valueEq` (reference
  equality via base loc, like maps) all reuse verbatim; `len(ch)`/`cap(ch)`
  are `lengthOf`/`capacityOf` arms; the Surface `pointsTo` idiom covers
  channel state for free (a chan cell is a heap cell — specs can say
  `ℓ ↦ chanData …`). Cons: `chanData` is a value no expression may produce
  (same as `mapData` — precedent handles it).
- [OPTION] P2 — separate `chans : List (ChanId × ChannelState)` table in
  `ExecState`, `GoValue.chanRef (id : Option ChanId)`. Pros: channel state
  can hold things that are NOT `GoValue`s (waiter queues of thread ids)
  without polluting the heap; no fake value constructor. Cons: a second
  allocator + a second wf carrier + a second heaplet story (Surface's
  `Heaplet` is base-addressed heap only, `Surface.lean:39-49` — specs about
  channel contents would need a new assertion form); `InitialSplit`, the
  Iris `StateInterp`, and the comparator statement-TCB all grow.
- [ANALYSIS] The deciding question is whether WAITER QUEUES must live in the
  channel. They need not: a blocked thread can be represented by its own
  Config (new configurations `.blockedSend chv v k`, `.blockedRecv chv
  targets k`, `.blockedSelect …` — Config-level, NOT Cont-level, which
  matters because Cont has ~8 total-match consumers of ~27 arms each
  (`panicPassthrough`, `recoverResult`, `recoverThroughWrappers`,
  `Cont.locSup`, `Cont.itersNormalized`, `pushDefer`, …,
  `Machine.lean:1221-1374`) while Config matchers are few). Rendezvous then
  = a `stepMulti` rule that pairs the picked runnable sender with a chosen
  blocked receiver by SCANNING `threads` for matching blocked configs — no
  sendq/recvq state at all. FIFO wake order (gc's realized policy; the spec
  is silent) then either (i) an envelope: partner choice is a Choices site
  bounded by #matching waiters — spec-honest, membership-lane for gc's
  FIFO point; or (ii) a singleton narrowing: lowest thread index = oldest
  blocked? FALSE in general (indices don't order blocking times) — real
  FIFO needs a per-channel arrival counter, i.e. some queue state after
  all. Under the nondet doctrine the envelope route (i) is the honest
  default and needs no queue; record it as an envelope statement at the
  pairing rule. This tilts the state question toward P1 (heap-cell), since
  the only argument for a separate table was non-value waiter data.
- [ANALYSIS] Rendezvous atomicity: unbuffered send/receive as ONE machine
  step pairing sender+receiver (value teleports sender→receiver targets,
  both threads unblock) is faithful — Go's own rendezvous is one
  synchronization (send HB receive); there is no observable intermediate.
  Buffered send = enqueue step; buffered receive = dequeue step; both are
  single-cell RMWs of the chanData cell — same atomicity class as
  `mapAssign` (§3), justified here because Go channel ops genuinely ARE
  atomic (that's their point). Close = set closed flag (+ panic rules:
  double-close, close(nil), send-on-closed — all pinned by the corpus).
  Receive-on-closed-drained = zero value + ok=false, no block.
- [ANALYSIS] `select` as a machine step: readiness of a clause is a pure
  function of (chanData cell, clause kind) — buffered-not-full / has-queued
  or matching-blocked-partner / closed. Machine shape: after the
  operand-evaluation frames complete (channel operands and send RHS
  evaluated once, in source order, on entry — Go spec, pinned by
  `channels/select-deterministic/{channel-operands-eval-order,
  send-rhs-eval-unselected,recv-chan-panic-before-default,
  send-rhs-panic-before-default}`), a single `selectReady` step computes the
  ready set: if nonempty, consume a choice bounded by its size (envelope =
  "any ready case", per doctrine §3 possibilistic — "uniform pseudo-random"
  enters as "any"); if empty and a default exists, take default
  (deterministic, NO choice consumed — the single-goroutine corpus stays
  strict-lane); if empty and no default, the thread blocks
  (`.blockedSelect` carrying the evaluated clauses). The receive-case LHS
  is evaluated only AFTER selection (pinned by
  `unselected-receive-lhs-not-eval`, `selected-receive-lhs-eval`) — so the
  selected case's body config is `exec`/`evalE` continuation-plumbing, not
  part of the select step. Nested selects need no special handling (each is
  its own statement); nil-channel clauses are never ready
  (`select-nil-default`, `nil-and-ready-*`).
- [ANALYSIS] Deadlock: when NO thread is runnable and ≥1 is blocked,
  `stepMulti` steps to a terminal `deadlocked` multi-config rendered as
  Go's `fatal error: all goroutines are asleep - deadlock!` — an
  unrecoverable fatal per the fault-model taxonomy
  (`f4-concurrency-model.md` §5), fault-identity-compared. A blocking op in
  a single-threaded program hits this immediately (differentially testable
  TODAY-style: deterministic). Note: Go's detector is conservative (misses
  deadlocks when any thread is in a syscall etc.) — ours is exact for the
  modeled fragment; that asymmetry needs an envelope note only if we admit
  externs that Go counts as "not asleep".

---

## 3. The granularity ledger revisited (BUG-002's class)

- [FACT] The recorded ledger (`2026-07-23_reshape-r1r2-machine-design.md:
  121-163`): `appendSlice` (both paths — in-place store loop over the
  shared backing cell; spill fresh-build), `copySlice`, `clearSlice`,
  `sortSlice` — single-cell multi-write loops in ONE apply step; frame-drain
  `enterFrame` allocations; panic-chain ops (continuation-local, declared
  interleaving-irrelevant). All flagged "re-audit at R4 before any
  concurrency claim".
- [ANALYSIS] Fresh enumeration of every ONE-step construct whose interior
  touches state a second goroutine could reach (now that shared state =
  the entire heap, since globals are heap cells `Loc.base ⟨0..n⟩`
  (`StepFn.lean:645-663`) and ALL locals are heap cells reachable by any
  goroutine that receives their address):
  1. The four ledger loops above (unchanged, now live).
  2. `mapAssign`/`mapDelete`/`mapLookup`/`clearMap`/`mapGet`: whole-map RMW
     or read in one step (`Machine.lean:672-731`). Go gives maps NO
     atomicity — concurrent map access is a runtime FATAL ("concurrent map
     read and map write"), not a panic. Our one-step atomicity is
     over-atomic vs gc, but race detection (§4) at access granularity
     flags concurrent map access before the difference is observable; if
     we additionally want gc's fatal-error identity for map races, the map
     cell access can carry a dedicated check. Either way: SAFE only
     jointly with fail-closed races — record as a ledger disposition, not
     a silent assumption.
  3. Frame exit: `loadMany results` + `storeMany targets` in ONE step
     (`StepFn.lean:402-405,479-482`; rules `frameReturn`/`frameFall`,
     `Machine.lean:1790-1797`). Multi-assignment `applyStmtOp .assignMany`:
     N stores in one step (`Machine.lean:629-631`). Both write potentially
     shared cells (globals as call targets / assignees). gc compiles these
     as separate word stores — non-atomic. Under DRF the writes are
     HB-isolated so coarseness is unobservable (reduction argument below);
     under a race, detection fires first. Ledger entries.
  4. `storeLoc` on interior paths (`.field`/`.index` locs): a single-field
     write is implemented as an RMW of the WHOLE base cell
     (`Ops.lean:956-966` recursing through the path). Two goroutines
     writing DISJOINT fields of one struct are race-FREE in Go, and our
     cell-RMW steps serialize them correctly under SC — each step reads
     the current cell — so no lost update and no false semantic
     divergence. The hazard is only in race DETECTION granularity: if
     conflicts are tracked per base CELL, disjoint-field writers look like
     a write-write race → false positive (fail-closed on a correct
     program; incompleteness, loud not wrong — but raft shares structs, so
     precision matters). Track accesses at full `Loc` path granularity
     (§4), not root-cell granularity.
  5. Multi-word plain stores generally (struct/array assignment, interface
     values, slice headers, strings): one `storeLoc` step here, several
     machine words in gc — Go's memory model gives racy multiword access
     torn values ("multiword races can corrupt", F4 §1). We CANNOT model
     tearing (our values are structured); the only honest posture is the
     DRF-SC one: claim SC-equivalence for race-free programs only, make
     races fail closed. This is already the recorded decision (nondet
     doctrine, F4 §1) — the new part is stating the argument shape:

  **The DRF-SC argument shape** (what the eventual claim must say):
  (i) our machine realizes all interleavings of MACHINE STEPS (∀-stream);
  (ii) if no interleaving reports a race at ACCESS granularity (each
  `loadLoc`/`storeLoc`/alloc inside every step recorded individually with
  its full `Loc` path), then the program is DRF in Go's sense on the modeled
  footprint; (iii) for DRF programs, Go guarantees SC at access
  granularity; (iv) every access-granular SC execution is observationally
  equivalent to some step-granular execution of ours, because each coarse
  step's interior accesses have no concurrent conflicting access (by DRF)
  and hence commute adjacent (Lipton movers) — so our step-interleaving set
  is complete up to observation. (i)-(iii) are definitions/spec; (iv) is
  the reduction lemma — the one genuinely new metatheory obligation, and it
  is per-coarse-construct (exactly the ledger's re-audit list, now with a
  proof obligation attached instead of prose). Until (iv) is built, any
  concurrency soundness claim must carry it as a stated assumption. Note
  the direction: our steps being COARSER means we might miss gc behaviors
  (too-narrow, the soundness-relevant direction per the doctrine) — (iv) is
  precisely the argument that DRF makes the missed interleavings
  observation-equivalent to kept ones.

  6. Non-entries, verified: expression temps and operand lists live in
     continuations (per-thread by construction) — BUG-002's root stays
     fixed; frontend-synthesized temps (`$c*`, `$ts*`, `$lvp*`, `$res*`,
     `$pc*`, `tools/nativefrontend/emit.go:1176-1470,2385-2949`) are
     function-local cells whose addresses never escape the lowering —
     private, so their multi-step lowerings (compound assign = read step +
     write step; multi-assign lvalue-pointer prelude) are FINER than or
     equal to gc's decomposition, which is the safe direction (matches
     Go's own non-atomicity). `$pkginit` runs to completion before the
     subject single-threaded (`StepFn.lean:685-731`) — EXCEPT that Go
     permits `go` inside init (spawned goroutines may run concurrently
     with the rest of init); slice 1 should fail closed on `go` during the
     init phase and record it.
  7. The allocator: `nextAddr` is shared state mutated by nearly every
     step (param binding, literals building structs, spills). Under
     ThreadPool, allocation order becomes schedule-dependent → heap
     ADDRESSES become schedule-dependent → any observation leaking
     addresses (none today — addresses aren't printable) stays fine, but
     `InitialSplit`-style concrete-seed reasoning and `allStreamsOk`
     state-equality caching would see exploding distinct states. Not a
     correctness issue; a proof-ergonomics fact worth recording early.

---

## 4. Race detection in the machine

- [FACT] The doctrine requires races FAIL CLOSED — "an error, not an
  interleaving"; `go run -race` is the designated second oracle
  (`2026-08-04_nondeterminism-doctrine.md:103-112`).

- [OPTION] (a) **Dynamic in-machine detection** — happens-before via vector
  clocks (FastTrack-style, simplified): per-thread clock; per-`Loc`-path
  shadow (last-write epoch, read set/epoch); HB edges from the sync
  primitives we model — `go` spawn (parent→child), channel send→matching
  receive, close→receive-of-closed, buffered k-th receive→(k+cap)-th send,
  (later) mutex unlock→lock, atomic ops. A step that performs an access
  conflicting (write-write or read-write, same `Loc` path, neither HB the
  other) with a recorded access → `GoError.raceDetected` (new constructor;
  a fatal, fault-identity-matched against `go run -race`'s nonzero exit —
  message matching is NOT feasible verbatim; compare the CLASS).
  - [ANALYSIS] Cost/benefit: state grows a shadow map (a second heap-shaped
    carrier — wf extension is mechanical `locSup` reuse; determinism given
    stream unaffected since detection is a pure function of the trace;
    `stepFn` totality unaffected). The instrumentation point is the
    chokepoint fact from §0: wrap `loadLoc`/`storeLoc` (and alloc) in
    recording variants inside `stepMulti`'s picked-thread execution —
    crucially this records the INTERIOR accesses of coarse steps
    individually, which is what makes detection granularity finer than
    step granularity and lets the ledger's coarse steps stand (§3's
    reduction argument needs exactly this). Metatheory cost: the shadow
    state must be provably observation-inert for race-free runs (a
    congruence: `stepMulti` with and without shadow agree on the
    projection) — mechanical but wide. THE key limitation, stated
    honestly: dynamic detection is per-RUN; "no run under any stream
    reports a race" is a ∀-schedule fact that testing samples and only
    proofs certify. Which is fine — see the synergy note below.
  - [ANALYSIS] Precision decision inside (a): track full `Loc` paths
    (field/index) to avoid false positives on disjoint struct fields
    sharing a cell (§3.4). Go's race detector granularity is byte-range;
    ours would be path-shaped — strictly finer than cell, incomparable to
    bytes in weird aliasing corners (a slice element vs the whole-array
    write: `.index base i` vs `.base` — path-prefix conflict must count as
    a conflict; define conflict = one path is a prefix of the other).
- [OPTION] (b) **No in-machine detection; races surface as exploration
  divergence** (a racy strict case fails `nondet` variance).
  - [ANALYSIS] Fails the doctrine on its face: detection by luck, not fail
    closed — a race whose interleavings the sampled streams never split is
    a hidden wrong answer; and even when caught, it classifies as
    "variance", not "race", corrupting triage. Also useless for the
    membership lane (any observed value is "in the set"). Only virtue:
    zero machine cost. Not honest as the primary mechanism; fine as a
    bonus signal.
- [OPTION] (c) **Static refusal of shared-memory patterns** (only
  channel-confined data crosses goroutines; reject programs where a
  non-channel-communicated cell is touched by two goroutines — an
  escape-analysis-shaped frontend check).
  - [ANALYSIS] Too broad for the stated target: F4 §1 records the user's
    direction that channel-confinement-only concurrency is REJECTED
    ("mutexes, atomics, lock-free — the actually interesting code"), and
    even raft's `node.go` shares memory under mutexes. Also unsound as
    stated (aliasing makes the static check either unsound or wildly
    over-restrictive). Could serve as a SLICE-1 stopgap (channels-only
    fragment where the check is trivially "no shared access at all"), but
    then it's a fragment gate, not race detection.
- [ANALYSIS] **The synergy that makes (a) the honest answer**: dynamic
  detection gives the EXECUTABLE fail-closed behavior + the `-race`
  differential lane (testable boundary); Iris CSL proofs (§5) certify
  ∀-schedule race-freedom STRUCTURALLY (points-to ownership: a proof that
  types-checks in CSL cannot have a data race on plain cells — that is what
  separation is). So: machine detects per-run (fail closed, differential);
  proofs discharge the ∀-schedule quantifier; the DRF-SC reduction (§3)
  connects both to gc executions. Each leg does the job the other can't.

---

## 5. Statement idiom: how Terminates/ProgressExec/GoSpec extend

- [FACT] The posture is decided: fork/join specs are pre/post state
  statements over `sem` — "single-threaded pre-state in, forked execution,
  join, results read off" (`2026-08-03_sem-adequacy-arc.md:9-24,59-64`);
  Iris is proof machinery, never a statement dependency
  (`2026-08-01_tcb-and-layering-doctrine.md`, statement-TCB gate).

- [ANALYSIS] The natural extension keeps every notion's SHAPE and swaps the
  carrier: `execStmt` → `execProg` (fuel-iterated `stepMulti` from
  `MultiConfig ⟨#[.exec prog env .stop], σ₀, …⟩`), with completion =
  MAIN thread terminal. Go semantics forces a decision here: **when main
  returns, the program exits — other goroutines are killed mid-flight** (Go
  spec, "Program execution"). Options: (i) model that faithfully — the
  multi-run's `.ok` terminal is "main reached its terminal", final state =
  shared heap at that instant (killed goroutines' partial effects
  included); (ii) require join-before-return in specs (the fork/JOIN idiom
  means well-written subjects join anyway, making (i) vs (ii)
  indistinguishable on the programs we care about). (i) is the faithful
  semantics; (ii) is a spec-side discipline, not a machine rule. Take (i)
  in the machine, let specs impose (ii).

- [ANALYSIS] Sketch of a concurrent `GoSpec` (the fork/join form):

  ```
  GoSpecC types funcs methods env₀ P prog Q :=
    ∀ hp na hP F, InitialSplit P hp na hP F funcs env₀ prog →     -- unchanged, single-threaded pre
      (∀ fuel ch σf ch',                                          -- GoTripleC half
        execProg fuel env₀ ⟨seed⟩ ch prog = .ok (.mainNormal σf, ch') →
        ∃ hQ, disj ∧ hQ.sub (heapletOf σf.heap) ∧ F.sub … ∧ sat hQ Q)
    ∧ (∀ fuel ch, ok-or-fuelOut)                                  -- ProgressExecC: never stuck,
                                                                  -- never panicked, never DEADLOCKED,
                                                                  -- never raceDetected
  ```

  Everything is still interpreter-level pre/post over states; `∀ ch` now
  quantifies schedules AND latitude in the one stream. The pre stays a
  single-threaded `InitialSplit` (main is the only thread at t=0 — exactly
  the user's stated scope). `ProgressExecC`'s success pin is
  `.mainNormal` (the multi analogue of the `.normal` pin, audit
  2026-08-04); its exclusions GROW: deadlock and race are new fail-closed
  terminals that a proven spec forbids — i.e. **a proven concurrent GoSpec
  implies deadlock-freedom and race-freedom on every modeled schedule**,
  which is the right headline strength and is exactly what the Iris proof
  route can discharge (races structurally; deadlock via the usual CSL
  obligations — note Iris WP does NOT give deadlock-freedom for free with
  blocking constructs modeled as blocked configs rather than spinning: a
  blocked thread with no partner is a stuck-shaped config, and pool
  progress only needs SOME thread to step, so pool-progress ≠ per-thread
  liveness. The `.mainNormal`-pinned ProgressExecC (main completes) is what
  forces global liveness through fuel — see the fairness flag below).

- [ANALYSIS] **Termination and the fairness problem (flag, per doctrine —
  the decision belongs to the arc's design note)**: `TerminatesC := ∃N
  ∀fuel≥N ∀ch, execProg … = .ok` is FALSE for virtually every interesting
  concurrent program under UNRESTRICTED streams — an adversarial stream can
  starve main forever by always picking a spinning/looping sibling (even a
  TERMINATING sibling can only delay main finitely — the killer is any
  nonterminating or unboundedly-running goroutine; and with
  exit-on-main-return, a deliberately diverging worker is LEGAL Go that
  terminates under every fair schedule and diverges under unfair ones).
  Candidate quantifier repairs, all with costs:
  (i) restrict to programs whose every goroutine terminates (∀-stream
  uniform bound then exists — finite total work) — sound, simple, excludes
  server-loop shapes; probably sufficient for fork/join specs and for
  raft's testable core;
  (ii) bounded fairness: quantify streams where every runnable thread is
  picked within k choices (k a statement parameter) — honest, keeps the ∃N
  uniform-in-fuel form (N depends on k), but puts a fairness predicate
  into the statement TCB;
  (iii) count fuel in MAIN-steps only and quantify fair streams — cleaner
  reading, same TCB cost as (ii).
  The doctrine already flagged this exact trap
  (`2026-08-04_nondeterminism-doctrine.md:114-118`). For slice 1
  (channels-only, single-goroutine — §6) NONE of this arises; for the first
  fork/join slice, (i) is the cheapest honest scope.
- [ANALYSIS] `GoInvariant`/`ReachableExec` extend verbatim with
  `stepMultiIter` (`ReachableExecC := ∃ n ch ch', stepMultiIter n m₀ ch =
  .ok (m, ch')`) — and become MORE valuable: invariance over reachable
  multi-configs is the natural home of protocol invariants
  (Verdi-style reading already recorded, `Surface.lean:290-298`).
- [ANALYSIS] **Statement TCB impact**: the base-definition set grows by
  `MultiConfig`, `stepMulti`/`execProg`, the terminal classification
  (`mainNormal`/`deadlocked`/`raceDetected`), and (if (ii)/(iii)) the
  fairness predicate. Each is first-order and interpreter-level — the gate's
  philosophy survives — but the comparator-judge Challenge and the
  designated-statement closure walk must add them; a Comparator landmark is
  mandatory the moment a designated statement changes shape (standing
  rule). The sequential notions and all 33 designated statements are
  UNTOUCHED if the multi layer is additive (§7).
- [FACT] **Iris readiness** (`deps/iris-lean`): the concurrent stack exists
  end to end — `Language` with `List Expr` efs + thread-pool `Step`/`NSteps`
  (`ProgramLogic/Language.lean:57,114-138`), WP with `forkPost` and per-fork
  `[∗list]` obligations (`ProgramLogic/WeakestPre.lean:52-53,79`),
  thread-pool adequacy `wp_strong_adequacy_gen` over `wptp`
  (`ProgramLogic/Adequacy.lean:26,174`), invariants
  (`Instances/Lib/Invariants.lean:37,103` — `own_inv`, `own_inv_acc` with
  masks), WSat, NaInvariants, ghost names (`GName`), and a worked
  HeapLang `Fork` + `Spawn`/`join` library with `joinHandle` ghost-state
  spec (`HeapLang/Lib/Spawn.lean:22-45`) as the pattern for our
  channel-based join specs. What I could NOT verify from reading: maturity/
  ergonomics of the ghost-state algebra layer for the custom RAs channel
  specs traditionally use (Perennial's channel proofs lean on bespoke
  protocols); budget for discovering gaps there. The seat is ready: our
  `GoPrimStep` already carries the `List Config` slot (`Lang.lean:36-41`)
  — the fork rule is a one-constructor change + re-derivation of the
  `IrisGS` instance over the pool.

---

## 6. Wire/frontend surface and the slice-1 scoping fact

- [FACT] The 38 channel cases (`baselines/native-full.tsv:84-121`; sources
  under `Corpus/coverage/exec/channels/`) are ALL single-goroutine and
  deterministic — not one contains a `go` statement or a blocking
  operation. Read in full, they pin: buffered FIFO send/receive + len/cap
  (`buffered-basic`, `make-edge/*` — 10 sub-cases incl. eval-order of
  channel/value operands via side-effect marks); close semantics
  (double-close panic, close(nil) panic, close-send-only, close does not
  drain, receive-from-closed comma-ok, drained zero+false); nil channels
  (len/cap 0, ==nil, close panic); directional types incl.
  `make(<-chan int, 2)` (len/cap only — a channel nothing can send on);
  `range` over a closed buffered channel; and 13 `select` cases — ALL with
  either a `default` or exactly one ready case, so the pick is
  deterministic: readiness (buffered full/empty, closed, nil), default
  fallthrough, entry-time evaluation of channel operands and send RHS in
  source order (panic-before-default cases), selected-only LHS evaluation,
  send-on-closed panic inside select. The negative lane
  (`Corpus/coverage/negative/compile/channels/`, 14 cases) pins
  direction/type errors (send on receive-only, close receive-only,
  multiple defaults, non-communication clauses, arity, element type) —
  compile-stage, so `go/types` in the frontend carries them.
- [ANALYSIS] Consequence — **a channels-only, zero-scheduler slice 1 is
  available**: `ChanValue`+`chanData` (§2 P1), make/send/receive/close/
  len/cap/range/select as machine steps, blocking = immediate
  single-thread deadlock fatal (differentially testable, deterministic!),
  NO `stepMulti`, NO scheduler choice site, NO fairness question. It flips
  all 38 cases from `frontend-export` to live differential coverage under
  the STRICT lane (everything is deterministic — even select, given the
  corpus's ≤1-ready construction; a multi-ready select would consume a
  choice and belongs to the membership lane, with new cases written for
  it). Guardrails-first is already satisfied — the corpus predates the
  machinery, per the standing rule. Goroutines (`stepMulti`, spawn,
  rendezvous, deadlock detection, race detection) are slice 2+, with their
  OWN guardrail suites owed first (deterministic-output concurrent cases +
  `-race` lane + litmus shapes, F4 §4).
- [ANALYSIS] Lowering shapes (mostly direct, mirroring existing patterns):
  - `Ty.chan (dir : ChanDir) (elem : Ty)` — direction is a TYPE fact
    (frontend-checked; the machine can carry it for fail-closed defense or
    drop it — the negative cases are compile-stage, so `go/types` already
    rejects them; carrying dir in `ChanValue` costs little and lets the
    machine fail closed if the frontend leaks).
  - Stmts: `makeChan (target) (elem) (cap : Option Expr)` (shape of
    `makeSlice`, `Syntax.lean:191`); `chanSend (ch value : Expr)` (evaluate
    ch then value — order pinned by `ordinary-send-eval-order`);
    `chanRecv (targets : Array Assignee) (ch : Expr)` covering plain,
    1-target, and comma-ok forms (shape of `mapLookup`,
    `Syntax.lean:194`); `closeChan (ch : Expr)`; `goStmt (callee : Expr)
    (args : Array Expr)` — callee and args evaluated in the SPAWNING
    goroutine (Go spec), which is EXACTLY `deferCall`'s existing eval-now
    machinery (`deferCalleeK`/`deferArgsK`, `Machine.lean:1105-1112`) with
    "spawn a Config" in place of "push onto the frame chain" — the defer
    frames are the implementation template, including the nil-callee
    panics-at-invocation rule (in the CHILD, at its first step);
    `selectStmt (clauses : Array SelectClause) (default? : Option Stmt)`
    with `SelectClause ::= send (ch val : Expr) (body) | recv (targets)
    (ch : Expr) (body)`.
  - Exprs: receive-in-expression-position lowers frontend-side to a
    `chanRecv` into a `$c`-style temp (the existing effectful-expr temp
    mechanism, `tools/nativefrontend/emit.go:1470`), so NO new Expr
    constructor is needed; `length`/`capacity` gain chan arms
    (`Machine.lean:391-424`).
  - `range ch`: a dedicated iteration frame in the `mapIterK` mold but
    NON-snapshot (receive until closed-and-drained — pinned by
    `range-closed`); do not reuse the snapshot machinery.
  - New Cont frames (`chanSendK`, `chanRecvK`, `closeK`, `selectK`, range
    frame, go-callee/args frames if not reusing defer's): each addition
    costs an arm in the ~8 total Cont matchers (§2) — mechanical, wide,
    and it shifts `fun_cases` positional numbering in the correspondence
    proofs (the docstrings warn about exactly this,
    `StepFn.lean:47-53`); budget proof-repair time accordingly, or land
    new constructors at the END and audit which matchers are
    position-sensitive.
  - Fail-closed in slice 1: `goStmt` (until slice 2), `sync.*`
    (extern-policy: `Mutex`/`WaitGroup`/`atomic` all `.unsupported` at the
    boundary — rungs 2/4 of the F4 ladder; whether `WaitGroup` is later
    MODELED over channels or made primitive is a rung-4 decision, not
    slice 1), select-with->1-ready (either fail closed or consume-choice +
    membership-lane — the former is safer for slice 1 since no corpus case
    needs it), `go` during `$pkginit` (§3.6).

---

## 7. Sequential conservation — the theorem we owe

- [ANALYSIS] Two distinct obligations, one cheap and one structural:
  1. **Empirical**: the ~1027-case corpus (`baselines/native-full.tsv`,
     1038 lines incl. header) runs identically — the standing zero-drift
     gate. Any shape that leaves `Config`/`ExecState`/`stepFn` untouched
     gets this by construction (the sequential driver `runProgramM` never
     constructs a `MultiConfig`).
  2. **Metatheory**: `stepMulti` restricted to one thread ≃ `stepFn`. Under
     Option A with the two design details flagged above — (α) scheduler
     choice consumed ONLY when `|runnable| > 1` (never `consume … 1`, which
     pops — §0), and (β) `Config`/`ExecState` types unchanged, the multi
     layer purely additive — the theorem is one `simp`-grade unfolding:
     `stepMulti ⟨#[c], σ⟩ ch = (stepFn σ c ch).map (wrap)` definitionally,
     lifted to `execProg fuel ⟨#[.exec prog env .stop], σ⟩ ch =
     (execStmtLoop fuel σ (.exec prog env .stop) ch).map (…)` by induction
     on fuel. Call it `execProg_single_eq_execStmt` — it is ALSO the
     transfer lemma that lets sequential `GoSpec`s be read as concurrent
     `GoSpecC`s of single-threaded programs (the existing 33 designated
     statements never need restating).
  - Caveats that would break definitionality, to be avoided or priced:
    new `GoValue`/`Ty` constructors (chan) touch `valueEq`/`normalize`/
    `defaultValue` fuel towers — sequential programs never reach the new
    arms, but the DEFINITIONS change, so "≃" is still `rfl`-grade while
    kernel-reduction COSTS may shift (the de-WF lessons, sem-adequacy build
    log); new Cont/Config constructors renumber `fun_cases` (§6); if
    channels live in a separate `chans` table (P2), `ExecState` itself
    changes and every existing concrete-seed `decide` re-elaborates —
    another point for P1.
  - Under Option B, conservation is equally trivial (no yield points
    single-threaded). Under any shape that RESHAPES `Config` (e.g. moving
    env or locals), conservation becomes a simulation proof — weeks, and
    the strongest single argument for the additive-layer discipline.

---

## 8. The questions only the user can decide

1. **Machine shape**: ratify Option A (executable ThreadPool over unchanged
   `Config`/`ExecState`; per-thread relation gains a spawn component; Iris
   pool via the generic `Language` step) — or direct otherwise. (§1)
2. **Channel state representation**: P1 heap-cell (`chanData`, map
   precedent — my read: dominant once waiter queues are dropped for
   blocked-configs) vs P2 separate table. (§2)
3. **Waiter-wake and select envelopes**: partner/case choice = "any
   matching/ready" Choices envelope (spec-honest; gc's FIFO/pseudo-random
   as membership points) vs FIFO singleton narrowing (needs per-channel
   arrival counters). Nondet doctrine requires the envelope statements
   either way. (§2)
4. **Race detection**: commit to in-machine HB/vector-clock detection at
   `Loc`-path granularity with a `raceDetected` fatal (+ `-race`
   differential lane), accepting the shadow-state cost — the only option I
   can argue delivers fail-closed honestly. (§4)
5. **The DRF-SC reduction lemma**: accept it as the recorded proof
   obligation attached to every granularity-ledger entry (replacing the
   prose "re-audit at R4"), and whether concurrency claims may ship with it
   as a stated assumption initially. (§3)
6. **Fairness quantifier** for concurrent termination: scope (i)
   (all-goroutines-terminate) first vs bounded-fairness (ii)/(iii) in the
   statement TCB. Doctrine says this is decided in the design note, not
   discovered as an unprovable theorem. (§5)
7. **Main-exit semantics**: ratify exit-kills-goroutines in the machine
   with join-discipline pushed to specs. (§5)
8. **Slice 1 scope**: channels-only/zero-scheduler (flip the 38 cases,
   strict lane, blocking = deadlock fatal) before any `go` machinery — and
   the guardrail suites owed before slice 2 (deterministic concurrent
   cases, `-race` lane, litmus shapes). (§6)
9. **Statement-TCB growth + Comparator landmark**: sign off that
   `MultiConfig`/`execProg`/terminal classes (+ fairness predicate if any)
   enter the base-definition set, with the judge run at the first
   designated concurrent statement. (§5)

## 9. What this note could not verify

- iris-lean ghost-state ergonomics for channel-protocol RAs (surface exists;
  depth unprobed — no build was run against it). (§5)
- gc's exact waiter-wake observability (whether ANY conforming-program
  observation distinguishes FIFO from other wake orders without already
  being schedule-dependent) — needs Go probes before the envelope statement
  is written. (§2)
- The reduction lemma's actual difficulty on `appendSlice`-in-place (the
  one coarse step whose interior both reads and writes a shared cell across
  many indices) — sketched, not attempted. (§3)
- Whether `select`'s "uniform pseudo-random" has any spec-visible
  consequence beyond "any" (doctrine says no — possibilistic only; a probe
  of starvation-sensitive programs would still be prudent before the
  envelope statement ships). (§2)
