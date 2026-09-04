# The reasoning surface: consumer interface spec + the C-arc plan (2026-09-04)

Status: PLAN, docs only. Second grumpy-professor pass. Written in
worktree `professor-2` (branch of the same name) off `main` @
`aceb0dcb`. Nothing under `GoLean/`, `tools/`, `scripts/`, `Corpus/`,
`baselines/` is touched by this lane. Every `file:line` below is at
`aceb0dcb` unless marked PARK (park branch `park/reasoning-2026-08-31`
@ `7440bf70`), IRIS (`deps/iris-lean` @ `e7a0a438`), CEDAR
(`deps/cedar-spec/cedar-lean`), or CERB (the sibling project
`/home/dev/projects/cerberus-lean-proj`, read for its lessons only).

Provenance. Every judgment here is [AGENT] unless marked [USER]. The
mandate is Mike's, 2026-09-04, held BY RELAY from the [AGENT]
coordinator, not firsthand (U0-incident convention: citation, never
bare assertion): «One question is whether we need to do any major
architectural reworking to fix any tech debt that might have built
up. The professor audit yesterday pointed to some things that seemed
potentially valuable but too disruptive. But I think we should try to
do the disruptive thing if it'll result in a more useful reasoning
surface». The earlier ratification of the C-items IN PRINCIPLE is
also relayed [USER] 2026-09-03 («eventually we will want to do the
bigger breaking changes as well … we can schedule those later or
now», `docs/2026-09-03_design-hygiene-arc.md`). This document answers
the relayed question with a specification of the surface (§1), a
measurement of the distance (§2), a plan with gates (§3), the
interactions with the other live lines (§4) and a sequence (§5).

What was read for this pass, in full: `GoLean/GoCore/{State,Platform,
EnumSpec,NPDRF}.lean`; `Machine.lean`'s `Cont`, `Config`, the walks,
`Step`/`Steps`/`Config.terminal`, `enterFrame`; `StepFn.lean`'s
`stepFn` head, the drivers and the `.initialization`/`.opDone` arms;
`Multi.lean`'s `MultiConfig`, `StepEvent`, `StepE`/`StepM`/`MultiWf`,
`execProgLoop`/`runProgramPoolM`, `raceUpdate` head; `Race.lean`'s
key types and `stepAccesses`/`dispatchAccesses`; `Ops.lean`'s
`loadLoc`/`storeLoc`/`nilValueMethodText?`; `Value.lean`'s stop
grammar; `Syntax.lean`'s `Func`/`Program`/`MethodSetRecord`;
`CLI.lean` `stepNeeds`; `ChoiceTrace.lean`'s header; the first
review, the arc plan, the A-series and B1 design notes, the wave-(iii)
HANDOFF + `Proto.lean` (its `Cont.tail/withTail/rebuild` prototype
compiles); the revival guide; the cedar census; the stdlib boundary
design; the doctrine's fairness paragraph. Six file:line censuses
were delegated and their cites are used below (control layer;
memory/type/proof counts; the park branch's actual consumption of
`GoCore`; the other lines + Cedar's `Spec/`; iris-lean's `Language`
classes; cerberus-lean-proj's design history). The wave-(iii) lane
(B2/B3/B8 + A7) is IN FLIGHT on `hygiene-wave3` (no commits yet at
`aceb0dcb`; its decisions are in the HANDOFF); nothing below
duplicates it — where this plan depends on its output it says so and
takes the HANDOFF's decisions as given.

---

## 0. The answer, before the argument

Yes: do the disruptive things, in a particular order, BEFORE the
reasoning repo pins us, and pin a DOCUMENT (this one's §1), not a
tree. Three facts drive that answer.

1. **The park branch is already broken against main, and not by
   accident.** The parked Iris layer's store law `wp_store_step`
   (PARK `proofs/GoLeanProofs/Lifting.lean:38-49`) is stated over
   `Heap.set`, which A2 deleted (there is no `Heap.set` on main; the
   one root write is `ExecState.updateCell`, State.lean:453); its
   examples unfold `coerceStoredValue` at 131 sites (PARK
   `Examples/MatMul.lean:71-72`, `Examples/Kadane.lean:799`), deleted
   by A3; `typeResolutionFuel` is a `simp only` target at 335 sites
   (PARK `Examples/Fib.lean:589,663,875-877`). None of that was a
   theorem about Go; all of it was a theorem about our
   representation. A pin of the tree would have frozen exactly those
   accidents. The consumer that comes back must import a SURFACE whose
   every name is a semantic commitment, and the surface must be
   written down first so that a refactor which preserves §1 is by
   definition not a breaking change.

2. **What the consumer actually needed was narrow.** The census of
   the park's import graph (PARK, §2/§4 of the delegated survey) is
   unambiguous: the Iris layer used `Config`/`ExecState`/`Cont`/`Loc`/
   `GoValue`/`HeapCell`, the relation `Step` (+ `Steps`, `StepE`,
   `StepM` and five `Multi.lean` helpers), three heap operations
   (`Heap.lookup`, the store, `alloc`), two continuation walks
   (`recoverThroughWrappers`, `panicPassthrough`), the four bridges
   (`stepFn_sound`, `step_complete`, `stepFnIter_sound`,
   `execStmt_sound_normal`), `Step.preserves_wf`, the `*_congr` frame
   family, and the predicates `StateWf`/`MachineWf`/`Func.locSup`.
   `stepFn`, `Choices`, fuel and `allStreamsOk` were DELIBERATELY
   absent from every WP law and every adequacy statement (they enter
   only at the Surface/kernel-replay boundary). That is the right
   shape and it is small: §1 is a cleaned-up statement of it.

3. **Every item the first review graded "very high value / only
   pre-pin" is cheaper now than it was, because the A-series and B1
   removed the parts that made them expensive**, and wave (iii) will
   remove more (the `Cont` algebra in `Proto.lean` already proves the
   30-case walk equivalences with one uniform script). C3 in
   particular (`Cont := List Frame`) can be done by the SAME
   `@[match_pattern]`-view trick A1 used for `Stop` (Value.lean:
   255-261), which turns "every rule and proof moves" into "every
   `induction k` moves" — §3.C3 has the measured count.

The un-answer, equally plainly: three semantics-adjacent items the
[USER] asked to be weighed are NOT hygiene and are graded here as
frontier decisions with their re-pin costs (§3.P native promotion —
recommended, after C1; §3.U `consumeAtOne` uniformization —
recommended, small, after wave (iii); the three standing exclusions
`unseq`/range-desugar footprint/eface identity — still excluded, §3.X).

---

## 1. The consumer interface — the target

This section is the pin. It is written as Lean signatures with a
one-paragraph contract each. The signatures are UNELABORATED SKETCHES
(no `lake` was run against them); names are proposals; the contracts
are the commitments. The module the reasoning repo imports is ONE
file, `GoLean/Interface.lean` (proposed), that re-exports exactly the
names below and nothing else; the reasoning repo's `Audit.lean`-class
deletion test (PARK `proofs/Audit.lean:130-560`, the statement-TCB
walk) is the enforcement: a designated theorem whose statement closure
reaches a `GoCore` constant NOT listed here is a build failure on
their side. Cedar's `Spec/` is the yardstick for size: six types + two
functions, ~250 lines, no theorems (CEDAR `Cedar/Spec.lean:19-30`);
what follows is larger because Go is larger, but the discipline is
the same — the interface exports DEFINITIONS and a short list of
BRIDGE THEOREMS, never proof devices.

Conventions. `ProgramCtx` (B7) is a section variable everywhere it
appears; `Refusal`/`Terminal`/`Stop` are A1's (Value.lean:199/213/
240). Where a name below does not yet exist the §2 gap item that
produces it is cited in brackets.

### 1.1 The program and its values

```lean
-- Syntax.lean / Value.lean, after B6 and I1 (§3)
structure Program where
  typeDefs   : Array TypeDef          -- indexed by TypeIdx (C2); dependency-ordered
  funcs      : Array Func             -- indexed by FuncId
  methods    : Array MethodInfo
  globals    : Array GlobalDef        -- cell i ↦ Loc.base ⟨i⟩ (A4)
  platform   : Platform               -- 1.11

structure Func where
  id : FuncId; args results : Array Param; body : Stmt; variadic : Bool
  -- NO `wrapper` field (§3.P); NO `methodSets` (internal to ProgramCtx)

inductive Expr  -- 57 constructors; NO `unsupported` (I1)
inductive Stmt  -- 39 constructors; NO `unsupported`, NO `initialization` (C4)
inductive Ty    -- NO `unsupported`; `.defined (idx : TypeIdx)` (C2)
inductive GoValue -- Go values only: no payload constructors (A3, done)
inductive Loc | base (a : Addr) | field (base : Loc) (tid : TypeId) (f : FieldName) | index (base : Loc) (i : Int)
abbrev VarId := Nat  -- B6
```

Contract. A `Program` is a CONSTANT of the semantics: no step reads
anything but it and the store, no step writes it (B7 makes this a
type fact). It contains no addresses (A4, done), no refusal markers
(the decoder refuses; an accepted program has no `unsupported` node —
I1 deletes the five constructors Syntax.lean:187/202/413 and
Value.lean:484 and `TypeDef.opaqueDecl` Syntax.lean:74 becomes an
import-boundary fact of `ProgramCtx`, not of the IR), no frontend
provenance (`wrapper`, `$`-temps as `String`s: B6 numbers locals; the
diagnostics side table keeps names). The consumer states specs over
`Program`s it constructs or decodes; it never needs a well-formedness
hypothesis on program TEXT (the last one, `Func.locSup`, is
identically zero since A4 and is owed for deletion — A-series note
§A4).

### 1.2 The store and the memory interface (C1)

```lean
-- GoLean/GoCore/Mem.lean (C1)
inductive HeapCell | value (ty : Ty) (v : GoValue) | mapPayload … | chanPayload …   -- A3, done
structure Store where heap : Array HeapCell                                        -- B7 (dense, A2 done)
def Store.nextAddr (σ : Store) : Nat := σ.heap.size

inductive AccessKind | read | write | atomicRead | atomicWrite      -- Race.lean:385, exists
structure Access where kind : AccessKind; loc : Loc                 -- = RaceAccess, Race.lean:464
abbrev Trace := List Access

/-- The memory monad: state + refusal + the ACCESS TRACE as a writer effect. -/
abbrev MemM (α) := Store → Except Refusal (α × Store × Trace)

def Mem.alloc  : HeapCell → MemM Loc                -- push; emits []  (allocation is not an access)
def Mem.load   : Loc → MemM GoValue                 -- emits [⟨.read, l⟩]
def Mem.store  : Loc → GoValue → MemM Unit          -- normalize at the cell's declared Ty; emits [⟨.write, l⟩]
def Mem.peek   : Loc → MemM GoValue                 -- metadata read gc does not instrument; emits []
def Mem.loadAtomic / Mem.storeAtomic                -- emit the atomic kinds
def Mem.mapPayload / Mem.setMapPayload / Mem.chanPayload / Mem.setChanPayload   -- whole-cell, emit as today's stmtOpAccesses say

def Loc.overlap : Loc → Loc → Bool  -- = locOverlap (Race.lean:308), moved next to load/store
```

Contract. Every user-visible memory operation the machine performs
goes through `Mem.*` and EMITS its access at the call site; the
footprint of a step is DEFINITIONALLY the trace its `MemM`
computation produced. `peek` exists because gc's instrumentation
does not record bounds/length/type-tag reads (Race.lean's inventory
classifies them today in prose); its uses are enumerated and each is
argued against the compiled access set, once, in `Mem.lean`'s
docstring. The two frame lemmas the consumer wants are stated ON THIS
INTERFACE and proved once:

```lean
theorem Mem.load_after_disjoint_store {l m v} (h : ¬ Loc.overlap l m) :
    (do Mem.store l v; Mem.load m) ≈ₛ (do let r ← Mem.load m; Mem.store l v; pure r)   -- same value, same store
theorem Mem.store_store_disjoint {l m v w} (h : ¬ Loc.overlap l m) :
    (do Mem.store l v; Mem.store m w) ≈ₛ (do Mem.store m w; Mem.store l v)
```

(`≈ₛ` = equal value and store, traces permuted.) These are NPDRF
obstruction 6's "same-root path-level half" (NPDRF.lean, obstruction
6) — today only the cross-root case is proved (`storeLoc_root_frame`,
`loadLoc_after_disjoint_store`, NPDRF.lean). With paths still living
inside tree-shaped values the proof goes through `StructFields.set`
(State.lean:167) and `arraySet` (Ops.lean:151) commuting at distinct
field/index — implementation detail, but proved ONCE behind the
interface, never again by a consumer. G-REPR (the park's "big design
unit", PARK `docs/2026-08-28_iris-corpus-plan.md:391-467`, route (b)
"re-key the ghost heap at `(base, path)`") is then a ghost-state
construction over `Mem` with these two lemmas as its only semantic
input — which is exactly how heaplang's `pointsTo` (IRIS
`Iris/BI/Lib/GenHeap.lean:83`) relates to heaplang's `loadS`/`storeS`
(IRIS `Iris/HeapLang/Semantics.lean:355-361`).

The detector is a FOLD over the trace: `RaceState.step : RaceState →
StepEvent → Trace → Except Refusal RaceState` (today `raceUpdate`,
Multi.lean:1492, which instead PROBES the post-configuration at 12
`some (.opDone _ _)` sites, Multi.lean:1544-1745). Exported to the
consumer: the fold and `Terminal.raceDetected`'s meaning as a
proposition over traces (`RacyFine`, NPDRF.lean, restated over emitted
traces instead of `stepAccesses`). NOT exported: `stepAccesses`,
`strictOpAccesses`, `stmtOpAccesses`, `dispatchAccesses`,
`projChainTarget`, `wrapperForwardArg`, `recvFieldChain`
(Race.lean:503-695) — deleted by C1.

### 1.3 The machine: frames, continuation, configuration, status

```lean
-- Machine.lean after B3 (algebra) and C3 (List Frame), B4 (Status)
inductive Frame     -- today's 30 non-`stop` Cont constructors minus their `k` field
abbrev Cont := List Frame                         -- C3; `fill K e = K ++ …`
inductive FrameClass | stmtGlue | exprGlue | callFrame | resumeMarker  -- B3 (Proto.lean)
def Frame.class : Frame → FrameClass

inductive Mode                                     -- C3's control modes
  | exec (s : Stmt) (env : LocalEnv) | evalE (e : Expr) (env : LocalEnv) | retV (v : GoValue)
  | next | signal (sg : Signal) | panicking (chain : List PanicEntry)
inductive Signal | brk | cont | ret | brkTo (l : Label) | contTo (l : Label)    -- B4
structure Config where mode : Mode; k : Cont

inductive Park | send … | recv … | select … | sync …                             -- B4
inductive Status | running (c : Config) (boundary : Option ChoiceSite) | parked (p : Park) | done (t : Done)  -- B4 + C5
inductive Done | normal | panicked (msg : String)
structure Pool where threads : Array Status; shared : Store; cur : Nat
```

Contract. A configuration is a MODE and a LIST OF FRAMES; the list is
the evaluation context and appending is context composition, so
iris-lean's `EctxLanguage` (IRIS `Iris/ProgramLogic/EctxLanguage.lean:
150-172`: `fill`, `fill_empty`, `fill_comp`, `fill_inj`, `fill_val`,
`step_by_val`) is instantiable with `fill K c := ⟨c.mode, c.k ++ K⟩`
— PROVIDED the two obstacles the park recorded are removed: (i) the
`hdrain` premise of `wp_plug_bind` (PARK `Laws/Bind.lean:26-34,
170-186`: the two-step panic abort `.panicking → .panicked → stuck`
makes `Language.Context.primStep_fill` FALSE for a context whose
drain sticks before the canonical render) — removed by B4's `Status`,
which makes "panicked" a THREAD status the pool observes, not a
configuration the sequential relation gets stuck on; (ii) labelled
`break`/`continue` and `return`, which are non-local control — kept
as `Signal` modes that step frame by frame (B4's table), so they DO
respect `fill` (a signal at `k ++ K` strips `k`'s glue exactly as at
`k`; cerberus-lean's `Erun` jump that discards its frame — CERB
`cerberus-heaplang/CerberusHeapLang/Lang.lean:94-100`, "Deliberately
ABSENT: a `Language.Context` instance … the engine's `Erun` discards
the frame (step_ctx's Erun arm, Core_reduction.lean:484)" — is the
shape we do NOT have and must not acquire — `goto` FR-11/FR-20 must lower to
signals, never to a frame-discarding jump). Terminal shapes are a
`Status`, never a pattern over `Cont` (today enumerated at Multi.lean:
148/259/1770, StepFn.lean:886-889, MachineSound.lean, NPDRF.lean:247).
`opDone` is a per-thread `boundary` flag (C5), never a configuration
wrapping a configuration (Machine.lean:2469).

### 1.4 The step relation family and its quantifier structure

```lean
-- the relation is CHOICE-FREE: nondeterminism is rule multiplicity (demonic)
inductive Step  : Config → Store → Config → Store → Prop            -- Machine.lean:3297, ~130 rules after B2/B4
inductive StepE : Config → Store → Config → Store → List Config → Prop   -- Multi.lean:1893 (spawn component)
inductive StepM : Pool → Pool → Prop                                -- Multi.lean:1928 (thread/pair/pickPair/pickCommit/wake)
inductive Steps / StepsM                                            -- rtc

-- the executable instantiates it against a stream, emitting its labeled picks (B8)
def stepFn  : Config → Store → Choices → Except Stop (Config × Store × Choices)               -- StepFn.lean:103
def stepPool : Pool → Choices → Except Stop (Pool × Choices × StepEvent)                       -- Multi.lean:1239 `stepMulti`
structure StepEvent where who : Nat; action : StepAction; picks : List PickRecord; trace : Trace; out : List OutEvent  -- 1.6/§4.1

theorem stepFn_sound    : stepFn c σ ch = .ok (c', σ', ch') → Step c σ c' σ'                  -- MachineSound.lean:44
theorem step_complete   : Step c σ c' σ' → ∃ ch ch', stepFn c σ ch = .ok (c', σ', ch')        -- MachineSound.lean:393
theorem stepPool_sound / stepM_complete                                                        -- MultiSound.lean:884/1059
theorem step_det_of_choiceFree : seqConsumption σ c = none → Step c σ c₁ σ₁ → Step c σ c₂ σ₂ → c₁ = c₂ ∧ σ₁ = σ₂   -- NEW (B8's theorem, §2 G12)
```

Contract. `Step` quantifies NOTHING over choices: where Go admits
several behaviours the relation has several derivations. `Choices`
and `stepFn` are the EXECUTABLE tier and are exported only through
the two bridge theorems (soundness: every executable step is a
relation step; completeness: every relation step is realized by some
stream). The park used exactly this (PARK `Lang.lean:36-41`,
`GoPrimStep … | step : Step c s c' s' → …`, observations `[]`, forks
`[]`; `LangC.lean:68` lifts `StepE`). What the park lacked and this
interface adds: DETERMINISM WHERE THE MACHINE CONSUMES NOTHING
(`step_det_of_choiceFree`) — the census found no `stepFn_det`/
`step_det` anywhere (MachineSound.lean has prose references only,
Machine.lean:1430/1547); the park's store laws each carry a hand-proved
`∀ c' s', Step c₀ σ₁ c' s' → …` determinism premise (PARK
`Lifting.lean:38-49`). B8's `seqConsumption`/`stepFn_consumption`
(HANDOFF) is the machine-side fact this derives from: `none ⇒ ch' = ch
∧ stream-oblivious`, hence unique successor by `stepFn_sound`/
`step_complete`. This single lemma is what a SEQUENTIAL refinement
(cedar-go, §4.5) needs to turn "some run reaches r" into "every run
reaches r".

### 1.5 Terminals, observations, readouts, outcomes

```lean
inductive Refusal | unsupported (feature : String) | stuck (msg : String) | internal (msg : String)   -- Value.lean:199, done
inductive Terminal | panic (msg : String) | fatal (msg : String) | deadlock | raceDetected            -- Value.lean:213, done
structure Readout where values : Array GoValue; stderr : ByteArray; stdout : ByteArray             -- rename of `Result` State.lean:93 (name clash with B2's `Result α`, HANDOFF) + §4.1
inductive Obs | ok (r : Readout) | terminal (t : Terminal)                                          -- EnumSpec.lean, B2 wires it (HANDOFF)
inductive Outcome | obs (o : Obs) | fuelOut | refusal (r : Refusal)

def run (P : Program) (entry : FuncId) (args : Array GoValue) (fuel : Nat) (ch : Choices) : Outcome    -- = runProgramPoolM, Multi.lean:1876
def SlowObs (P entry args) (o : Obs) : Prop := ∃ fuel ch, run P entry args fuel ch = .obs o           -- EnumSpec.lean, exists
theorem run_mono : run P e a fuel ch = .obs o → fuel ≤ fuel' → run P e a fuel' ch = .obs o           -- execProgLoop_mono-class
theorem run_refusal_free : Accepted P → run P e a fuel ch ≠ .refusal r                                -- NEW, §1.9
```

Contract. A run ENDS in exactly one of: an observation (Go behaviour
— the differential compares these), `fuelOut` (a model artifact — the
budget, never Go), or a refusal (the machine declined — a frontier or
a bug, never Go). The consumer's adequacy statements quantify
`Terminal`/`Obs`, never "the subset of `Stop` I mean" (review U1;
A1 delivered the types, B2 wires `Obs`). `fatal` IS an observation
(EnumSpec.lean's structural exclusion is retired by B2 — HANDOFF).
`fuelOut` is a first-class, TRANSPARENT constructor and fuel is a
PARAMETER of `run`, monotone (`run_mono`) — cerberus-lean learned this
the hard way: an opaque exhaustion sentinel made every `∀ fuel`
statement unprovable and forced them to author a second trusted
driver (CERB `refined-cerberus/docs/DECISIONS.md:630-645`, [USER
there]: «There should not be any reason for the driver to not be the
actual, genuine, legitimate, original … one»; and `:1787-1800`: «the
semantics [should] take fuel as a parameter … the executable
interpreter [can] pick 10^8»). We already have that shape
(`execProgLoop`, Multi.lean:1819; `execStmt_mono`, MachineSound.lean:
750); the interface commits to it and to ONE driver (`run`), not
four (`runProgramM`/`runProgramPoolM`/`execStmt`/`runConfig`).

### 1.6 The small-step/big-step correspondence

```lean
theorem run_ok_iff_stepsM : run P e a fuel ch = .obs (.ok r) ↔
    ∃ m, StepsM (init P e a) m ∧ mainDone m ∧ readout m = r ∧ stepCount ≤ fuel        -- shape; the ≤ is the fuel side
theorem run_terminal_iff : run P e a fuel ch = .obs (.terminal t) ↔ ∃ m, StepsM (init P e a) m ∧ poolTerminal m = some t
theorem execProg_single_eq_execStmt : … -- MultiSound.lean:583 (the one-thread pool IS the sequential machine); kept
```

Contract. Whatever a consumer proves by induction on `StepsM` (or on
`Steps` for sequential programs, via `execProg_single_eq_execStmt`)
transfers to the driver's verdict, and conversely; the driver is a
DEFINED function of the relation plus fuel plus the stream, not a
second semantics. The park's G-EXIT (PARK plan `:541-580`: "the last
step — setup + `$pkginit` + entry wiring — is unproved as a chain";
adequacy landed on `execStmt`, the designated sentences on
`runProgramM`) is exactly the absence of this pair of lemmas on the
semantics side. It is our lemma to prove, once, because `init P e a`
(today `runProgramSetupM`, StepFn.lean:1015, with its `StateWf`
assert at :1028) is ours.

### 1.7 The frame algebra and the bind lemma

```lean
def Config.fill (K : Cont) (c : Config) : Config := ⟨c.mode, c.k ++ K⟩       -- C3
theorem step_fill    : Step c σ c' σ' → Step (c.fill K) σ (c'.fill K) σ'      -- Language.Context.primStep_fill
theorem step_fill_inv : ¬ c.isVal → Step (c.fill K) σ c₂ σ' → ∃ c', c₂ = c'.fill K ∧ Step c σ c' σ'
theorem fill_val      : (c.fill K).toVal = some v → K = [] ∧ c.toVal = some v
instance : EctxLanguage Config Cont Store Obs Val                              -- IRIS EctxLanguage.lean:150-172
```

Contract. Under C3 + B4 these are the iris-lean `Language.Context`
laws (IRIS `Language.lean:271-280`) and `wp_bind` comes from iris-lean
for free; the park's standalone `wp_plug_bind` with its `mapIterFree`
/`recoverThroughWrappers k' = none`/`hdrain` premises (PARK
`Laws/Bind.lean:170-186`) and its σ-conditioned owed variant (the
revival guide's "named owed row") are retired. The one honest caveat:
`recover` reads the continuation (`recoverResult`, Machine.lean:2325)
— a `recover()` under `k ++ K` may find its `panicResumeK` in `K`. So
`step_fill_inv` holds for every rule EXCEPT the recover rule at a
`k` with no `resumeMarker`, and the instance carries `¬ c.k.hasMarker
→ …` there, or — cleaner — `recover` is modelled as an OPERATION on
the frame stack whose result is a pure function of `c.k ++ K` and the
lemma is stated as "fill commutes with `recoverResult` when `k`
contains a marker or when `K` contains none". Either way it is ONE
side condition on ONE rule, stated here, instead of a premise on every
bind. `Val` is `Unit` and `toVal ⟨.next, []⟩ = some ()` (PARK
`Lang.lean:25`, kept: results live in the store at pinned locations).

### 1.8 The consumption projection and the fairness slot (B8)

```lean
structure PickRecord where site : ChoiceSite; bound : Nat; pick : Nat   -- State.lean:386, exists
def seqConsumption  : Store → Config → Option (ChoiceSite × Nat)          -- B8 (HANDOFF)
def poolConsumption : Pool → List PickRecord → Option (ChoiceSite × Nat)  -- B8
theorem stepFn_consumption : …  -- none ⇒ oblivious; some (s,b) ⇒ ch' = (consumeAt s b ch).2 ∧ pick-determined   (B8)
theorem picks_complete : stepPool m ch = .ok (m', ch', ev) → ev.picks = the labeled consumptions of this step, in order   (B8)
theorem sched_pick_menu : ⟨.l1Sched | .postOp | .backEdge, b, p⟩ ∈ ev.picks → b = (schedSlots …).length ∧ ev.who = (schedSlots …)[p]

abbrev Run := Nat → Option (Pool × StepEvent)          -- a driver run, unrolled
def SchedSites : List ChoiceSite := [.l1Sched, .l5ExitWindow, .postOp, .backEdge]   -- State.lean:276-278, exists in prose
-- `Fair : Run → Prop` is DEFINED DOWNSTREAM (doctrine, [USER] 2026-09-02); the interface exports the vocabulary it is stated in.
```

Contract. The machine's OWN labeled picks are complete and
menu-anchored: every consumption a step makes appears in the event
with its site and bound, and a scheduling pick's bound is the runnable
menu's length and its slot names the goroutine that ran. `Fair` —
"every goroutine runnable at infinitely many scheduling picks is
picked at infinitely many" — is the reasoning side's to define and
assume (doctrine `docs/2026-08-11_essence-of-go-doctrine.md:37-68`,
[USER] verbatim: «the semantics should admit unfair schedules …
Fairness is an assumption about the sequences that are chosen»);
what we owe is that it is STATABLE over `StepEvent.picks` without a
mirror. Today the width of a consultation is recomputed by three
hand mirrors (`CLI.stepNeeds` CLI.lean:970-1113, `stepNeedsSeq`
:1118-1162, `ChoiceTrace.seqSite/poolSite` ChoiceTrace.lean:416/469,
whose header :47-57 states the agreement obligation) — B8 replaces
them; nothing here is new beyond B8's recorded design.

### 1.9 Well-formedness: what the consumer carries, what becomes type

```lean
def StateWf (σ : Store) : Prop := ∀ cell ∈ σ.heap, cell.locSup ≤ σ.heap.size     -- StateWf.lean:595, simplified (no function-body clause)
def ConfigWf (bound : Nat) (c : Config) : Prop := c.locSup ≤ bound                   -- StateWf.lean:599
def MachineWf (σ : Store) (c : Config) : Prop := StateWf σ ∧ ConfigWf σ.nextAddr c    -- StateWf.lean:605 MINUS `itersNormalized`
theorem step_preserves_wf : Step c σ c' σ' → MachineWf σ c → MachineWf σ' c'          -- StateWf.lean:6658
theorem stepM_preserves_wf : StepM m m' → PoolWf m → PoolWf m'                        -- MultiWfSound.lean:1260 (`stepMulti_wf`), restated over StepM
def Accepted (P : Program) : Prop  -- decoder-side: no refusal marker, method sets complete, typeDefs well-founded (C2)
theorem run_refusal_free : Accepted P → StateWf (init P e a).shared → run P e a fuel ch ≠ .refusal r   -- the "never .internal on wf input" claim, made a THEOREM TARGET
```

Contract. ONE dynamic invariant (no dangling address in any cell or
frame), decidable, preserved by every relation step; the consumer
carries it as the park carried `HeapWf` (PARK `HeapBridge.lean:
115-120`, the single adequacy side condition, `Adequacy.lean:83`).
Which of today's conjuncts become TYPE-LEVEL: (a) heap keys — already
(dense heap: a key IS an index, A2); (b) `Config.itersNormalized` —
vacuous (`Cont.itersNormalized_true`, StateWf.lean:578) and still
threaded through `MachineWf` and `MultiWf` (113 mentions in StateWf,
103 in MultiWfSound) — DELETE, owed since A8; (c) the "stored function
bodies" clause (`ExecState.locSup` = `max (Heap.locSup) (funcListSup
…)`, StateWf.lean:491) — identically zero since A4; DELETE with B7
(the program leaves the state). What stays a PREDICATE, deliberately:
address boundedness of VALUES — making `Addr` a `Fin heap.size` would
make `GoValue` depend on the store, which is the wrong dependency; the
predicate is cheap and preserved. `Accepted` is the decoder's
contract stated as a Prop the consumer can `decide`; `run_refusal_free`
is the theorem A9 made statable (Value.lean:184-197, the refusal rule:
`.internal` is "unreachable if the machine is correct") — it will not
be proved soon, but it is the interface's promise and every
`.internal` arm is a proof obligation against it, not a shrug.

### 1.10 The pool: what the concurrent consumer sees

`Pool`, `StepM`, `StepE`, `Status`, the five helpers `StepM` mentions
(`arrivalCases` Multi.lean:933, `applyPairing` :985, `commitClause`
Machine.lean:3115, `resumeThread` Multi.lean:484, `spawnPlan` :328 —
the park's `LangD.lean:82` used exactly these), `schedPick` :1903 and
`runnableIdxs` :247, `RaceState.step` (1.2), `RacyFine`, and the two
mover lemmas of 1.2. NOT `raceUpdate`'s shape probes, NOT
`arrivalCases`' internals beyond its result type, NOT `MultiWf`'s
`itersNormalized` conjunct (Multi.lean:1998-2002).

### 1.11 The platform parameter

```lean
structure Platform where intBits wordBytes maxAlign maxAllocBytes chanHeaderBytes : Nat   -- Platform.lean:28, exists
def gcAmd64 : Platform                                                                    -- Platform.lean:82
-- the machine is parametric: `Program.platform` (1.1) / `ProgramCtx.platform` (B7); `platform := gcAmd64` (Platform.lean:88) is the DRIVER's default, not the core's constant
```

Contract. A theorem that does not depend on the layout pins can say
so (`∀ p`); one that does names `gcAmd64`. Today only `tySizeAlignFuel`
(Ops.lean:227) and `IntKind.bitsAt` (Value.lean:38) take the record;
`IntKind.bits?` (Value.lean:53), `maxAllocBytes`/`chanHeaderBytes`/
`intExclusiveUpperBound` (Ops.lean:174-180) and `tySizeBytes`
(Ops.lean:266) read the global (A-series note §A5 records the
deferral to B7). B7 threads it.

### 1.12 Deliberately NOT exported

`stepFn`'s body (only its two bridge theorems), `Choices.consume/
consumeAt/consumeAtE/policy` (only `PickRecord` and the two B8
projections), the four drivers other than `run`, `fuel` anywhere but
`run`'s parameter, `ExecOutcome` (State.lean:101 — three of four
constructors dead for programs, A-series §A8 deferred it to B4),
`allStreamsOk`/`allStreamsOkPool` and the enumeration engine
(`EnumDedup*`, MultiStreams.lean — the park's grandfathered tier the
revival guide records as banned for new members), `ChoiceTrace`,
`NativeToIR` and the wire, `Func.wrapper` and `MethodSetRecord`
(internal to `ProgramCtx`, §3.P), the `stepAccesses` table family
(1.2), `.opDone` (1.3), `Stmt.initialization` (C4), the `*Fuel`
functions and `typeResolutionFuel` (C2 deletes them), `seqCont`
(Machine.lean:2172 — its env-equality splice is an implementation of
`.seq` sequencing that C4 makes unconditional), `StateEqb`/`MachineEqb`
(decidability instruments), the `$`-named temporaries (B6 makes them
`VarId`s; the wire may keep names as diagnostics).

### 1.13 The pin

When the reasoning repo pins this one, the pin is a SHA whose
`GoLean/Interface.lean` matches §1.1-1.11 name for name and whose
`docs/` carries this document with a "PINNED @ <sha>" line. A later
refactor that preserves §1 is not a breaking change for the consumer
even if it moves every line of `Machine.lean`; a change to §1 is a
pin move with a written reason, like the oracle pin. That is the
whole point of writing §1 before doing §3.

### 1.14 The customer, concretely: the iris-lean instantiation

iris-lean (`deps/iris-lean` @ `e7a0a438`, the park's pin — PARK
`proofs/lakefile.toml`) is THE consumer §1 is specified for. Its
classes, cited so the fit can be checked line by line, and what our
instance is.

**The classes.**
- `class Language (Expr) (State Obs Val : outParam) extends PrimStep Expr
  State (List Obs), ToVal Expr Val where val_stuck : (e, σ) -<obs>-> (e',
  σ', eₜ) → toVal e = none` — IRIS `Iris/ProgramLogic/Language.lean:
  109-113`; `PrimStep.primStep : Expr × State → Obs → Expr × State × List
  Expr → Prop` :67-69 (the `List Expr` is the FORK list; `Language`
  instantiates the observation slot at `List Obs`, so a step emits a
  LIST of observations — heaplang uses it for prophecy resolution,
  `Iris/HeapLang/Semantics.lean:386-391`); `ToVal` :34-41.
- `class Language.Context (K : Expr → Expr)` — `toVal_eq_none_fill`,
  `primStep_fill`, `primStep_fill_inv` — :271-280 (the bind law's
  premise; the park says it is FALSE for us today, PARK `Laws/Bind.lean:
  22-25`).
- `class EctxLanguage (Expr) (Ectx State Obs Val : outParam) extends
  BaseStep, ToVal, EvContext` with `fill_val`, `step_by_val`,
  `val_stuck`, `base_ctx_step_val` — IRIS `EctxLanguage.lean:150-172`;
  `EvContext.fill/fill_empty/fill_comp/fill_inj` :40-45; the item
  version `EctxItemLanguage` with `Ectx := List EctxItem`, `fill K e :=
  K.foldl (fun x y => fillItem y x) e`, `comp x y := y ++ x` —
  `EctxiLanguage.lean:19-34, 53, 56-63` (a list of frames IS its
  evaluation context; C3 makes ours the same type).
- `class StateInterp (State) (Obs) (GF) where stateInterp : State → Nat →
  List Obs → Nat → IProp GF` — `WeakestPre.lean:35-40` (state, step
  count, PRIOR OBSERVATIONS, threads spawned); `class IrisGS_gen …
  extends StateInterp` with `numLatersPerStep`, `forkPost`,
  `stateInterp_mono` :45-59; `wp.pre` :73-83 (the `primStep` premise at
  :80), `wp_unfold` :127-131.
- `structure adequate (s) (e1) (σ1) (φ : Val → State → Prop)` with
  `adequate_result` (every thread-pool trace reaching a value satisfies
  φ) and `adequate_not_stuck` (every reachable thread `NotStuck` when
  `s = .NotStuck`) — `Adequacy.lean:237-243`; `wp_strong_adequacy_gen`
  :174-192, `wp_adequacy_gen` :302-311; the total variant `twp_total`
  (`TotalAdequacy.lean:200-214`).
- heaplang as the template: `State := {heap : ExtTreeMap Loc (Option
  Val); usedProphId}` `Semantics.lean:88-90`; `loadS`/`storeS` :355-361;
  `genHeapInterp`/`pointsTo l dq v := heapName ↪◯MAP[l]{dq} v`
  `Iris/BI/Lib/GenHeap.lean:79-86`; `HeapLangGS` (NOT an instance, "to
  avoid diamonds with IrisGS_gen") and `HeapLangState.stateInterp σ _ κs
  _ := genHeapInterp σ.heap ∗ prophMapInterp κs σ.usedProphId`
  `PrimitiveLaws.lean:60-70`; `heap_adequacy … : adequate .NotStuck e σ
  (fun v _ => φ v)` :131-134.

**Our instance (the design the interface must admit).**

```lean
-- downstream, over GoLean.Interface; nothing here is built in this repo
inductive Event | pick (r : PickRecord) | access (a : Access) | out (o : OutEvent)   -- ONE observation type
abbrev Obs := Event
-- (sequential) Expr := Config, State := Store, Val := Unit
def primStepSeq : Config × Store → List Event → Config × Store × List Config → Prop :=
  fun (c, σ) evs (c', σ', efs) => StepE c σ c' σ' efs ∧ evs = eventsOf c σ c'   -- picks/accesses/out of THAT step
instance : Language Config Store Event Unit   -- val_stuck: no rule from ⟨.next, []⟩ (today PARK Lang.lean:46 proves it by `cases`)
instance : EctxLanguage Config Cont Store Event Unit   -- C3 + B4: fill K c := ⟨c.mode, c.k ++ K⟩ (§1.7)
-- (concurrent) the park's LangD shape: a per-thread relation whose pairing/wake rules ∃-quantify the partner
--   (PARK LangD.lean:25-36, :82); StepM is the refinement target via a simulation (PARK stepM_erasedD :487).
```

Four consequences the interface is shaped by:

1. **The choice tape is demonic nondeterminism in `primStep`, and the
   PICKS are observations.** `Step` has several derivations where Go
   has several behaviours (§1.4); the executable's `PickRecord`s (B8)
   are emitted as `Event.pick` in the step's observation list. So a
   thread-pool trace `NSteps n ([c], σ) obs ρ` (IRIS `Language.lean:
   148-154`) CARRIES the labeled schedule in `obs`, and `Fair` is a
   predicate on `obs` — `Fair : List Event → Prop` (or on the infinite
   trace), "every goroutine runnable at infinitely many `pick` events
   at a `SchedSites` site is the `who` of infinitely many" — an
   IRIS-LEVEL HYPOTHESIS on the trace, exactly the doctrine's «fairness
   is a hypothesis on the chosen choice sequence, stated where it is
   used» ([USER] 2026-09-02, relayed via the doctrine). `sched_pick_menu`
   (§1.8) is what makes it well-defined (a pick names its goroutine).
   Partial adequacy (`adequate`) is fairness-free; liveness under `Fair`
   is a trace-indexed corollary the downstream states over `NSteps`,
   not something the machine enforces.
2. **The state interpretation is heap + race shadow, and the shadow is
   a FOLD OF THE OBSERVATIONS, not ghost state.** `stateInterp σ _ κs _
   := genHeapInterp (Store.toKeyMap σ) ∗ ⌜RaceState.ofEvents κs = some r⌝`
   — because `StateInterp` receives the prior observation list (the
   slot heaplang uses for prophecies), and the detector (§1.2) is
   definitionally a fold over emitted accesses and picks. `Terminal.
   raceDetected` is then `RaceState.ofEvents κs = none` — a pure fact
   about the trace prefix, provable or refutable by computation. This
   is why C1 must make the footprint an EMISSION: a table beside the
   semantics cannot be folded from `κs`.
3. **Points-to is keyed like the detector: `ShadowKey`, not `Loc`.** The
   ghost heap's key type is `ShadowKey` (Race.lean:336: `data l |
   syncWord l kind word | chanObj l`, A6 — done) restricted to LEAF
   paths plus sync words: `Store.toKeyMap σ : ExtTreeMap ShadowKey Cell`
   decomposes each value cell into its scalar leaves (`data (l.field
   …)`, `data (l.index …)`), each `sync` value into its words (`syncWord
   l .mutex .state`, `.sema`, …), each payload cell into `chanObj l` /
   `data l`. Then `l ↦ v` for a leaf, `l ↦ₘ μ` for a mutex as the
   conjunction of its word assertions, `own_struct`/`own_slice`/`own_map`
   as iterated conjunctions (G-REPR route (b), PARK plan `:391-467`),
   and the frame rule is `ShadowKey.overlap k₁ k₂ = false → keys
   disjoint` — the SAME overlap table the detector uses (Race.lean:354),
   so "these two accesses cannot race" and "these two points-to are
   separate" are one fact. `Mem.load_after_disjoint_store`/
   `store_store_disjoint` (§1.2) are the semantic input; `genHeap_update`
   at a leaf key rewrites exactly one leaf of one cell. Per-word sync
   keying is what lets a `Mutex` inside a struct be owned separately
   from its neighbouring fields — precisely the case the detector's
   A6 table was built for (a whole-struct copy covers the words; a
   sibling field's access overlaps none).
4. **Adequacy shape.** `go_adequacy : StateWf σ → (∀ [GoGS GF], ⊢ WP c
   {{ _, ⌜φ⌝ }}) → adequate .NotStuck c σ (fun _ σ' => φ σ')`, then
   through §1.6 `run_ok_iff_stepsM` to `∀ fuel ch, run P e a fuel ch ∈
   {.obs (.ok r) | φ r} ∪ {.fuelOut}` (the park's `go_adequacy`, PARK
   `Adequacy.lean:83`, carried `HeapWf σ` plus three pin equalities
   `GoCoreGS.prog GF = σ.functions/methods/types` — B7 makes those a
   single `ProgramCtx` section variable). `NotStuck` under the LangD
   widening: a parked goroutine is REDUCIBLE (∃ partner), so deadlock
   is not "stuck" in Iris's sense and deadlock-freedom is a `Fair`-
   conditioned liveness statement, not adequacy; a `Refusal` IS stuck
   (no rule) — so `adequate .NotStuck` is exactly `run_refusal_free`
   (§1.9) for the fragment the WP covers. That is the sentence the
   interface should be able to state and the downstream should be
   able to prove.

---

## 2. Gap analysis: the current core against §1, item by item

Each item: what a consumer proof fights through TODAY, with the
cite; which §3 item closes it. Counts are from the delegated censuses
at `aceb0dcb`. Items are ordered by §1 section, not by pain.

**G1. `Cont` is a 31-constructor flat inductive with no algebra**
(Machine.lean:1918-2166; 30 carry a `k : Cont` tail, `stop` :1919).
`fill` does not exist; the park's `plugC` is proof-layer (PARK
`Frame/Plug.lean`) and its bind lemma is standalone with three
premises (PARK `Laws/Bind.lean:170-186`; `:22-25`: "the unconditional
`Language.Context` shape is FALSE here"). The walks: `pushDefer`
:2197, `panicPassthrough` :2212, `recoverThroughWrappers` :2256,
`recoverResult` :2325 (30 arms each), `Cont.locSup` StateWf.lean:360
(1151 `locSup` mentions in that file), `Cont.itersNormalized`
StateWf.lean:511, `Cont.eqbF` (MachineEqb). Consumer cost: every
`cases k`/`induction k` is 31 cases; `.seq` alone appears 3091 times
in the park's proofs, `.strictK` 867, `.frame` 416. → B3 (in flight)
gives `tail`/`withTail`/`rebuild`; C3 gives the list.

**G2. `Config` mixes control, five signals, one terminal, four parked
shapes, and a scheduling annotation** (Machine.lean:2384-2479, 16
constructors; `opDone (sched) (inner : Config)` :2469). Terminal
shapes are enumerated as patterns at Multi.lean:148 (`threadDone`),
:259 (`atBoundary`), :1770 (`mainOutcome?`), StepFn.lean:886-889
(`execStmtLoop`), Machine.lean:4099 (`Config.terminal`, only `.next
.stop` and `.panicked`), NPDRF.lean:247. `toVal` cannot be a
projection: a terminal is either a `Config` (`.next .stop`,
`.panicked`) or an `Except` error (`fatal`, `deadlock` are
relation-silent — Machine.lean's `syncStApply` comment, review U1).
→ B2 (terminals as `Terminal`), B4 (`Signal`, `Status`), C5
(`opDone` out).

**G3. The panic twins.** 158 `Step` rules (Machine.lean:3297-4075), 17
of them `*Panic` twins (:3327, 3347, 3573, 3581, 3819, 3825, 3829,
3833, 3857, 3862, 3867, 3892, 3932, 3970, 3997, 4042, 4070); the
`.panicking [⟨runtimeErrorValue …` conversion spelled 15× in StepFn,
25× in Machine, 3× in Multi (HANDOFF counts). Every rule-indexed
consumer lemma is written twice. → B2 (in flight; ONE `deliver`).

**G4. The footprint is a table beside the semantics, argued by a
253-line prose inventory.** Race.lean:3-255 is docstring; the table
is `stepAccesses` :1531 (17 arms over `Config` SHAPES),
`strictOpAccesses` :503, `stmtOpAccesses` :695, `storeTargetAccess`
:1515, `dispatchAccesses` :641, `deferEntryAccesses` :686,
`projChainTarget` :571. Its agreement with what `loadLoc` (Ops.lean:
1140) and `storeLoc` (:1172) touch is a "lockstep obligation" — a
theorem nobody has. `RacyFine` (NPDRF.lean) and the detector share
the table, which NPDRF obstruction 5 records as "cancels a shared
under-approximation" but does not make either right. The detector
learns whether an op proceeded by probing the POST-configuration
(`raceUpdate` Multi.lean:1492; 12 `some (.opDone _ _)` matches
:1544-1745). → C1.

**G5. The frontend's shape is inside the detector's verdict.**
`wrapperForwardArg` (Race.lean:610) recognizes the decoder's EXACT
emission (`synthesizePromotionWrappers`, `tools/nativefrontend/emit.go:
5467`, `"wrapper": true` :5726) to narrow a footprint to the promotion
hop; `recvFieldChain` :600; `dispatchAccesses` :641 branches on
`target.wrapper`. `Func.wrapper` (Syntax.lean:468) is consumed by
`recoverResult` (Machine.lean:2326/2330), `recoverThroughWrappers`
(:2259), `nilValueMethodText?` (Ops.lean:2103 — `if target.wrapper
then none`), `dispatchAccesses`, and propagated at seven frame-entry
sites (Machine.lean:3543, 3550, 3652, 3664, 3715, 3720, 3777). The park
had to `rw [show …Func.wrapper = false from rfl]` at every call-chain
example (PARK `Specs/Callchain.lean:438,468,592`). → §3.P (native
promotion) deletes the field; C1 makes the hop narrowing fall out of
the trace (the wrapper's body — or, natively, the projection chain —
loads what it loads).

**G6. The memory frame lemma is cross-root only.** `storeLoc_root_frame`
/`loadLoc_after_disjoint_store` (NPDRF.lean) are gated on `Loc.rootBase
m ≠ Loc.rootBase l`; the same-root path-level half (distinct fields/
indices of one cell — which `locOverlap` Race.lean:308 rightly calls
independent) is NPDRF obstruction 6, unproved in any form; store/store
commutation is unproved. The park's heap RA is base-address whole-cell
(PARK `HeapBridge.lean:33-47`: `heapToMap_cons_field`/`_index` DROP
field and index keys), so G-REPR had nothing to stand on. A2/A3 are
done (dense heap State.lean:68; payload cells :30-63; one root write
path `updateCell` :453). → C1 states and proves the two lemmas of
§1.2 behind `Mem`.

**G7. Fourteen fuel towers and a sealing dance.** Ops.lean: 12 `*Fuel`
functions (:227, 461, 482, 514, 562, 607, 981, 1079, 1199, 1363, 1415,
1590), `typeResolutionFuel := 1024` :29; Value.lean: `Ty.eqbFuel` :513,
`GoValue.eqbFuel` :862 with `tyEqFuel`/`valueEqbFuel` = 1024 (:496/
:835); the five wrappers sealed `attribute [irreducible]` at Ops.lean:
2229-2230 with post-seal pins :2237-2252. Proof-side: 77 `Fuel`
mentions in StateWf.lean, 43 in MachineSound.lean;
`isNormalForTyFuel_sound` (StateWf.lean:1387) is a ∀-fuel statement
whose wrapper form `isNormalForTy_sound` :1475 is what consumers use;
the park unfolded `typeResolutionFuel` at 335 sites. The ONE genuine
non-structurality is `Ty.defined name` through `TypeEnv := List
(TypeId × TypeDef)` (State.lean:69, `TypeEnv.lookup` :153 a `String`-
keyed chain). → C2.

**G8. Locals are `String`-keyed at run time.** `Scope := List (String ×
Loc)` State.lean:10, `LocalEnv.lookup` :119 (a `==` chain on every
`.var`/`.ref`), `Param.id : String` Syntax.lean:11, `Expr.var (id :
String)` :78, `Expr.ref` :121; `seqCont` decides splicing by
whole-environment equality `env' = env` (Machine.lean:2173);
`stepFn`'s `.initialization` arm requires `kenv = env` else
`.internal` (StepFn.lean:150-158); 30+ `$`-prefixed temporaries reach
the core as strings (NativeToIR.lean:640-1788: `$lit`, `$ta`, `$taok`,
`$cr{i}`, `$cv{i}`, `$maplit`, `$rrecv`, `$rok`, `$rcoll`, `$ridx`,
`$rlen`, `$rfirst`, `$roff`, `$rnext`, `$ret{i}`, `$ca0`, `$mlv`,
`$mlok`, `$blank{i}`, `$forFirst`, `$stub{i}`) with the reserved-prefix
argument a comment (Syntax.lean:535-544). Consumer cost: α-renaming
lemmas on every spec that names a variable (the park's `Frame/Rename.
lean`, `RenameId.lean`). → B6 (+ C4 deletes the two env-equality
tests).

**G9. A statement whose meaning depends on its continuation.**
`Stmt.initialization` (Syntax.lean:286) rewrites the enclosing `.seq`
frame's environment (`Step.initialization`; StepFn.lean:150-158) and is
`stuck` anywhere else; `Stmt.block (decls) (stmts)` :277 already
allocates declared locals at entry (`allocDecls`, Machine.lean:639).
Two allocation disciplines for one concept. → C4.

**G10. The program is inside the state.** `ExecState` (State.lean:76)
carries `types`, `functions`, `methods`, `methodSets` beside `heap`;
`StateWf` (StateWf.lean:595) is `ExecState.locSup σ ≤ σ.nextAddr`
where `ExecState.locSup := max (Heap.locSup) (funcListSup σ.functions
…)` (:491) — a program-text clause that is identically zero since A4
and still costs a `by decide` at every example (PARK `Examples/
BinSearch.lean:1478` etc.). Every congruence lemma carries `htypes :
σ₂.types = σ₁.types` (`normalizeValueForTy_congr` MachineSound.lean:
1453, `storeLoc_congr` :1611; 18 `_congr` declarations in that file).
`step_preserves_wf_loc` (StateWf.lean:5769) must conclude `σ'.types =
σ.types` because nothing else says the program is constant. → B7.

**G11. `MethodSetRecord` and `MethodSetCoverage` are wire facts stored
in the semantics** (Syntax.lean:483-498; `Program.methodSets` :524;
`ExecState.methodSets` State.lean:85; the decode contract NativeToIR.
lean:1861-1893). They exist so the machine can REFUSE rather than
answer from absence (BUG-053) — right instinct, wrong layer: they are
an `Accepted P` fact (§1.9), i.e. a decoder-side obligation, not a
runtime table a consumer must carry in its state interpretation (PARK
`FastEval/Ops.lean:31` mirrors the field; `Frame/TypeCongr.lean:177`
needs `dynamicMethodSetRecorded_congr`). → B7 puts them in
`ProgramCtx`; §3.P shrinks what they must say (no promoted entries).

**G12. No determinism lemma; five obliviousness hypotheses instead.**
`stepFn_oblivious` (MachineSound.lean:2889) carries `hmi` (not a
`mapIterK` shape), `hnc`/`hns`/`hnv`/`hnt` (`consumesAppendSlice`,
`consumesSelect`, `consumesNilValueMethod`, `consumesTryLock`) — one
per consuming site, hand-maintained, and it speaks of `stepFn`, not
`Step`. No `step_det`. → B8's `seqConsumption` + `stepFn_consumption`
(HANDOFF) then §1.4's `step_det_of_choiceFree` (a 20-line corollary
once B8 lands; §3.I3).

**G13. Consumption widths are mirrored three times outside the
machine.** CLI.lean:970-1113 (`stepNeeds`, 144 lines re-implementing
the `stepMulti` dispatch ladder), :1118-1162 (`stepNeedsSeq`),
ChoiceTrace.lean:416/469 (`seqSite`/`poolSite`; header :47-57: "the
site-tagged mirror here must agree with `CLI.stepNeeds` on every
bound"); `StepEvent.picks` (Multi.lean:705) carries POOL-layer picks
only. → B8 (in flight).

**G14. `Obs` cannot say `fatal`, and the readout type is misnamed.**
EnumSpec.lean `Obs := ok | panic | race` (its docstring calls the
fatal exclusion "a CAPABILITY bound"); `obsOf?` maps `.error _ =>
none` for fatal/deadlock. `Result` (State.lean:93) is the READOUT and
clashes with B2's `Result α` (HANDOFF names the clash; proposes
`Readout`). → B2 (in flight) wires `Obs := ok | terminal`; the rename
is §3.I2.

**G15. The platform is a global constant read by the core.**
Platform.lean:88 `def platform : Platform := gcAmd64`; readers Value.
lean:53, Ops.lean:174/177/180/267; only two functions take the record
(Ops.lean:227, Value.lean:38). Theorems are at `platform`, not `∀ p`
(A-series §A5 says so). → B7.

**G16. `.opDone` is control.** Machine.lean:2469; 39 mentions in
Machine.lean, 54 in Multi.lean; `opDoneInner` Multi.lean:140;
`boundarySite` :1201; the strip is a `stepFn` step (StepFn.lean:823)
and a relation rule (`Step.opDoneStrip`); the park needed
`wpC_opDone_strip`/`wpD_opDone_strip` (PARK `LangC.lean:170`,
`LangD.lean:863`) to reason past it. → B4 + C5.

**G17. Vacuous invariant conjuncts still threaded.** `Config.
itersNormalized` (StateWf.lean:549; `_true` :578/585) in `MachineWf`
:605 and `MultiWf` Multi.lean:1998-2002 — 113 + 103 mentions;
`ExecOutcome`'s three dead constructors (State.lean:101-105;
constructed only at StepFn.lean:886-889 and Multi.lean:1772-1775).
→ B3/B4 (owed since A8).

**G18. Refusal markers inside the IR.** `Expr.unsupported` Syntax.lean:
187, `Assignee.unsupported` :202, `Stmt.unsupported` :413,
`Ty.unsupported` Value.lean:484, `TypeDef.opaqueDecl` :74;
`Ty.mentionsUnsupported` (Ops.lean:539) exists to scan for them at
run time. The decoder already refuses unknown keys (NativeToIR.lean:
52ff); a consumer's `Program` should not be able to spell "I don't
know". → §3.I1.

Not a gap (recorded so nobody "fixes" it): the relation being
choice-free (§1.4) is right; `Choices := List Nat` staying writable by
hand is right; `Terminal` as a Go behaviour type is right and done;
the dense heap and payload cells are done; the eqb tower's
one-directional soundness is right for a decidability instrument.

---

## 3. The C-arc plan

### 3.0 Dependency order (what must land first)

```
wave (iii) B2 + B3 + B8 (+A7)  ── in flight; every C-item assumes it
   │
   ├── U  consumeAtOne uniformization  (needs B8's single consumption truth; its own re-pin)
   │
   ├── B7 ProgramCtx/Store split  ──► C1 Mem module + trace  ──► P native promotion
   │                                     │                          (needs C1: the hop footprint is the trace)
   │                                     └──► (I4 RacyFine over traces; detector fold)
   ├── B4 Signal + Status  ──► C5 .opDone out of Config
   │        │
   │        └── (with B3) ──► C3 Cont := List Frame  ──► I5 EctxLanguage instance sketch (interface module)
   ├── B6 VarId  ──► C4 block-scoped allocation
   ├── C2 well-founded TypeEnv   (independent; frontend emission order; twin pin move)
   └── B5 Chan module            (independent; pre-pin nice-to-have for the parked channel logic)
                                                 │
                                    I  GoLean/Interface.lean + §1.4/1.6/1.9 bridge theorems
                                                 │
                                    assessment re-run  ──►  pin offer
```

Reading the graph: B7 is the hinge nobody scheduled — C1's `MemM` is a
state monad over `Store`, and threading `Platform` and deleting the
`htypes` hypotheses both want the program out of the state first. B4
is the second hinge: C5 is trivial after it and C3 is clean after it
(signals as modes). C2 is the one big item with no dependency and a
FRONTEND half, so it runs in a parallel lane. Wave (iii)'s decisions
are taken as given: `Result` at the apply boundary, `deliver`,
`Cont.tail/withTail/rebuild/class`, `applyPos`, `seqConsumption`, NO
`stepFn` 4-tuple reshape (HANDOFF).

Every item below follows the arc plan's six invariants
(`docs/2026-09-03_design-hygiene-arc.md`, "Invariants of every
slice"): full `scripts/capped scripts/ci --diff` at ZERO drift (a
changed row is a STOP, not a re-pin), whole-corpus labeled-consumption
trace at ZERO delta (`scripts/choice-trace-corpus`), proofs move
arm-for-arm, records in step, adversarial audit, [USER] gate before
merge. Where an item is preserving only up to an isomorphism or a
re-pin it SAYS so and stops at the gate.

"Session" below = one worker lane of the kind that landed B1 or the
A-series: a branch-complete slice with its gate and audit-ask,
roughly one agent-day. Estimates are [AGENT] guesses anchored to the
measured counts; the A-series (9 items, one session) and B1 (one
session + one fix round) are the calibration points.

### 3.C1 — the memory module with an access trace

**Change.** `GoLean/GoCore/Mem.lean` per §1.2: `MemM`, `Mem.alloc/
load/store/peek/…`, `Loc.overlap` moved beside them. `loadLoc`/
`storeLoc` (Ops.lean:1140/1172) become `Mem.load`/`Mem.store`'s
bodies; the 13 load + 26 store call sites in Machine.lean (census list:
loads :204,228,383,438,448,485,513,670,1025,1048,1562,3086,3301; stores
:676,857,895,927,957,1003,1034,1052,1055,1084,1088,1130,1367,2703,2711,
2722,2731,2740,2746,2754,2794,2822,2830,2844,3001,3031), 1 in StepFn
(:317), 2+4 in Multi (:195,1730; :523,527,532,537), and the map/chan
payload sites are each classified `load`/`store`/`peek`/`atomic` —
the classification Race.lean's inventory ALREADY makes in prose,
turned into the choice of which `Mem.*` to call. `stepFn` returns its
trace (the HANDOFF declined a 4-tuple reshape for B8; C1 needs the
trace out — carry it in the `MemM` result and have the drivers thread
it, or make `stepFn : … → Except Stop ((Config × ExecState × Choices)
× Trace)` — the reshape is paid ONCE here and B8's `StepEvent.picks`
rides the same event). `raceUpdate` becomes a fold over `ev.trace`;
`stepAccesses` and its six helpers and the 253-line inventory are
deleted; the O1 narrowing (`projChainTarget`: `evalVar`/`deref` under
an immediate projection frame load the PROJECTED path) is reproduced
by having those two rules call `Mem.load` at the projected path —
the CEK already has the continuation in hand at that point, so this is
a choice of WHICH path to load made WHERE the load happens.

**Order.** After wave (iii) and B7 (`MemM` over `Store`). Before P.

**Preservation.** (i) State/value component of every helper unchanged
— the trace is a writer effect; extensional equality of `stepFn`'s
first three components is by `rfl`/`simp` per arm. (ii) The emitted
trace at each step EQUALS today's `stepAccesses σ c` — provable per
arm as `theorem accesses_eq_stepAccesses : (stepFn σ c ch).trace =
stepAccesses σ c` for the retiring table; this theorem is the AUDIT of
the table. Any arm where it fails is a detector bug found (recorded as
a BUG with a red-first row, referred to the [USER]) — never absorbed
as "preservation". Gates: `ci --diff` zero drift (the detector's
verdicts are observations: `raceDetected` rows); `scripts/detector-
soundness` re-run over the racy corpus (its four-cell matrix must be
unchanged except for HOLE→agree if the audit found a bug); choice
trace zero delta (loads/stores consume nothing).

**Proof-wave cost.** The `_locSup`/`_wf` families restate over `MemM`
(StateWf.lean's `loadLoc`/`storeLoc` mentions: 17/45; MachineSound 13/
12; `storeLoc_congr`-class 18 `_congr` lemmas gain a trace component
they ignore); `NPDRF.lean`'s two movers move to `Mem.lean` and gain
the path-level siblings (§1.2 — NEW proofs through `StructFields.set`/
`arraySet`, ~300 lines); `RacyFine` restated over traces (I4).
Estimate: 4-6 sessions (2 for the module + call-site classification, 1
for the audit theorem, 1-2 for the proof restatements, 1 for the
path-level movers).

**Risk — where a semantic change could hide.** (a) A `peek`/`load`
misclassification changes a race verdict, not a value — the audit
theorem catches every case the old table covered and NOTHING it did
not (obstruction 5's residual: an access the table omitted stays
omitted unless C1's author adds it deliberately; each added access is
a disclosed narrowing, filed). (b) Trace ORDER within a step matters
to no consumer (the detector folds a set), but `accesses_eq_
stepAccesses` should be stated up to permutation to avoid pinning an
accident. (c) The `Mem.store` normalization at the declared type is
unchanged (A3's one discipline) — no value change possible.

**Design gate G-C1 (to the [USER]).** «Adopt `Mem` with an emitted
access trace as THE definition of a step's footprint; retire the
`stepAccesses` table once `accesses_eq_stepAccesses` is proved arm by
arm; any arm where the theorem fails is filed as a detector BUG (red-
first row, referred), never absorbed.» Recommendation: YES. This is
the single item that turns the detector's 253-line prose obligation
into a theorem and gives G-REPR its two frame lemmas.

### 3.C2 — a well-founded `TypeEnv`; the fuel towers become structural

**Change.** The frontend emits `typeDefs` in DEPENDENCY ORDER, aliases
inlined (`.alias` is identity-erasing by definition, Syntax.lean:50),
`.defined`-over-`.defined` flattened; `TypeEnv := Array TypeDef`
indexed by `TypeIdx : Nat` with the INVARIANT that a struct/array/
defined body refers only to SMALLER indices (pointer/slice/map/chan/
func/interface are leaves for every type-directed recursion — Go
forbids `type T struct{ x T }` and permits recursion only through
those). `Ty.defined (idx : TypeIdx)`; `TypeId` keys stay for
diagnostics and interface identity. Then `defaultValue`/`tySizeAlign`/
`canonicalTy`/`tyUncomparable`/`goTypeNameForMessage` recurse by
well-founded recursion on the index (kernel-reducible via `Nat.rec`
or a `Fin`-indexed descent), and `normalize`/`valueEq`/`isNormal`/
`convert`/`buildStruct` recurse structurally on the VALUE with the
type looked up; `Ty.eqb`/`GoValue.eqb` structural (nested `List Ty`
in `funcType` keeps a hand-written `BEq`, no fuel). `typeResolutionFuel`,
the 14 `*Fuel` functions, the `irreducible` seal and its pins go.
`Accepted P` (§1.9) gains the well-foundedness clause, DECIDED at
decode.

**Order.** Independent of the other C-items; frontend half + core
half in one lane (the twin pin moves because the wire's typeDef
ORDER changes — `scripts/check-frontend-pins`, the raft twin wire,
byte-for-byte). Can run in parallel with C1.

**Preservation.** Exact: on every accepted program the fuel never
runs out (depth ≪ 1024), so each fuel function equals its structural
counterpart on every reachable call — the refusals at exhaustion
(`Ops.lean:14-28`'s "1023 vs 1024" caveats) are unreachable today and
unrepresentable afterwards. Gates: `ci --diff` zero drift; choice
trace zero delta (types consume nothing); twin pin re-pinned with the
written reason "typeDefs dependency-ordered". One NEW row class: a
program whose typeDefs are NOT well-founded must be refused at the
decoder (fail closed), pinned as a `stuck`/`unsupported` row.

**Proof-wave cost.** Every lemma that unfolds a `*Fuel` function
restates: StateWf 77 `Fuel` mentions, MachineSound 43; `isNormalForTy
Fuel_sound` (StateWf.lean:1387) becomes `isNormalForTy_sound` directly;
`normalizeValueForTyFuel_congr` (MachineSound.lean:1311) and the
`normalizeListWith_congr` family restate structurally (shorter). The
frontend: an emission-order pass over go/types' type graph (SCC +
topological order; struct/array edges only) — ~200 Go lines + tests.
Estimate: 4-5 sessions (1 frontend, 2 core, 1-2 proofs).

**Risk.** (a) Interface identity: `Ty.defined` by INDEX means two
programs' `.defined 3` are different types — fine, a `Program` is a
constant; but the decoder must reject duplicate `TypeId`s (it does:
FR-19 is the whole-export kill for duplicate local `TypeId`s). (b)
Struct tag compatibility (`structTagCompatible`, Ops.lean) compares
by `TypeId`; unchanged. (c) Recursive types THROUGH pointers/slices/
maps (`type L struct{ next *L }`) must be leaves of the size/default
recursion — they are today (fuel never enters a pointer's pointee for
size); the invariant must say so or the topological order fails on
the cycle — the emitter must break cycles at pointer/slice/map/chan/
func/interface edges only, and REFUSE any other cycle.

**Design gate G-C2.** «Frontend emits typeDefs in dependency order
with aliases inlined (twin pin moves); `TypeEnv` becomes index-keyed
and well-founded by an `Accepted` clause decided at decode; the 14
fuel towers, `typeResolutionFuel` and the `irreducible` seal are
deleted.» Recommendation: YES; it is the item the reflect gate G6
will otherwise re-pay (§4.4), and every downstream points-to law
inherits "normalized at fuel 1024" until it lands.

### 3.C3 — `Cont := List Frame`, via `@[match_pattern]` views

**Change.** `inductive Frame` = the 30 non-`stop` constructors with
their `k` field deleted (Machine.lean:1922-2166; after B3's bundling,
fewer fields per frame). `abbrev Cont := List Frame`. THE TRICK, which
A1 already used for `Stop` (Value.lean:255-261): keep the 31
constructor NAMES as `@[match_pattern] abbrev`s —

```lean
@[match_pattern] abbrev Cont.stop : Cont := []
@[match_pattern] abbrev Cont.seq (rest : List Stmt) (env : LocalEnv) (k : Cont) : Cont := Frame.seq rest env :: k
… (30 of these)
```

— so every existing PATTERN and TERM `.seq rest env k`, `.frame t te
r ds k w`, `.stop` in `stepFn`, the 158 rules, `stepAccesses` (until
C1 deletes it), `atBoundary`, the plan extractors, elaborates
UNCHANGED as a pattern on `List.cons (Frame.seq …) k`. `Cont.tail =
List.tail?`, `withTail = fun k t => k.head?.map (· :: t)`, `class =
head class`, `rebuild` = `List` recursion; `pushDefer` = "map at the
first `callFrame`", unwinding = `dropWhile isGlue`, `locSup = supBy
Frame.locSup`, `eqb` = list equality; `fill K c := ⟨mode, k ++ K⟩`.
`Config := Mode × Cont` (§1.3) is the same slice.

**Order.** After B3 (its `tail`/`withTail`/`rebuild` API is what makes
the walks representation-independent — `Proto.lean`'s `rebuild_locSup`
generic lemma already replaces the per-walk inductions) and after B4
(signals as modes; otherwise `Config`'s five signal constructors each
carry a `Cont` and the mode/stack split is half done). Pre-pin ONLY
(the arc plan's stated condition).

**Preservation.** Definitional: `Cont ≅ List Frame` is a bijection
(`toList`/`ofList`, `k.tail ≅ tail?`); every rule's conclusion is the
same TERM under the views; `stepFn` is unchanged text. Gates: `ci
--diff` zero drift; choice trace zero delta; `StateEqb`/`MachineEqb`
decidability unchanged in verdict (list equality of frame equality).

**Proof-wave cost — the honest count.** What does NOT move: pattern
matches (views). What MOVES: every `induction k`/`cases k` on `Cont`
— they become `induction k` on a list + `cases f` on the head frame.
Census: StateWf.lean 1151 `locSup` mentions across 207 theorems (the
`Cont.locSup` inductions are the bulk — but B3's `rebuild_locSup`
collapses the five walk lemmas at :4361-4465 into one, HANDOFF);
MachineSound.lean's two `fun_cases` proofs (`stepFn_sound` :44,
`stepFn_oblivious` :2889, 75 positional `case caseN` tags) do NOT
change shape — `fun_cases stepFn` splits on `stepFn`'s match, which
is unchanged under views; MultiWfSound 145 `locSup` mentions;
MachineEqb's `Cont.eqbF` becomes `List.beq` + `Frame.eqbF` (andSplit11
goes with B3). The `Cont.sizeOf_tail_lt`-style termination arguments
become `List.length`. Estimate: 3-4 sessions (1 for the type + views +
walks-as-list-functions, 2-3 for the induction re-proofs). The first
review's "very high" grade assumed patterns move; with views they do
not, and the grade drops to "high, mechanical".

**Risk.** (a) `@[match_pattern]` on an `abbrev` that unfolds to
`List.cons` is exactly A1's precedent — verified compiling there; the
one place it can bite is `fun_cases`/`split` generating goals in the
UNFOLDED form (`Frame.seq _ _ :: k`) that `simp [Cont.seq]` must
re-fold — a `@[simp]` lemma per view, 31 lines. (b) The `wrapper :
Bool := false` default argument on `frame` (Machine.lean:1941-1943)
cannot be a default on a view — §3.P deletes the field; do P's field
deletion FIRST or spell `false` at the ≥ 8 barrier sites (`Cont.
barrier k` per B3's `FrameSpec.barrier`). (c) No semantic change is
possible here: nothing evaluates differently on a list than on a
spine.

**Design gate G-C3.** «`Cont := List Frame` with `@[match_pattern]`
views for the 31 constructor names; `Config := Mode × Cont`; `fill` is
append; done before the pin, never after.» Recommendation: YES, third
in order (after C1 and B4), because it is what makes §1.7 an
`EctxLanguage` instance instead of a bespoke bind lemma with three
premises.

### 3.C4 — block-scoped allocation; delete `Stmt.initialization`

**Change.** The frontend already knows every local of a block (go/
types); lower `x := e` inside a block as a `.block` declaration plus
`.assign` so all locals of a block are allocated at BLOCK ENTRY
(`allocDecls`, Machine.lean:639, already exists) and `.seq` frames
have a FIXED environment. Delete `Stmt.initialization` (Syntax.lean:
286), `Step.initialization`, `stepFn`'s arm (StepFn.lean:150-158) and
`seqCont`'s splice test (Machine.lean:2173 — splice unconditionally;
with fixed envs both choices are equivalent). With B6, "declared
locals of a block" is a `List (VarId × Ty)`.

**Order.** After B6 (numbering locals per block makes the declaration
list a frontend artifact of the same pass). Pre-pin preferred (so the
consumer never sees `initialization`); could be post-pin since it
does not change §1 — but §1.1 says `Stmt` has 39 constructors, and a
pin that says 40 is a different pin.

**Preservation — UP TO HEAP ISOMORPHISM, flagged.** Allocation ORDER
changes (a block's locals are allocated at entry, not at their
declaration), so `Loc.base` ids differ from today's. Nothing in the
observation channel exposes addresses: pointer `==` is preserved by
any bijective renaming; `%p` printing is not modeled (and slice 3
REFUSES address kinds by name, §4.1); map iteration order is
cell-insertion order not address order; race keys rename uniformly;
Go forbids use-before-declaration so the zero-valued-but-undeclared
cells are unobservable — EXCEPT one class to probe deliberately:
`goto` backward into a block (FR-11's "fresh cell per execution")
and closures capturing a loop variable (Go 1.22 per-iteration
semantics) — a block-entry allocation must still allocate per
ITERATION, i.e. the loop body is a block entered per iteration; the
frontend's current desugar already does this (`$forFirst`,
NativeToIR.lean:1608-1623) and the differential's closure rows are
the regression. What DOES change: dedup certificates (`EnumDedupCheck`
keys on state repr), `Tests/GoCoreEval.lean`-class `repr` pins, any
baseline that records a `Loc` (the observation JSON does not: A3's
docstring, State.lean:47). NPDRF obstruction 1 says the reasoning
side must work up to heap isomorphism anyway. Gates: `ci --diff` on
OBSERVATIONS zero drift (this is the invariant-2 STOP condition — a
changed observation means the probe above found something); choice
trace zero delta (allocation consumes nothing); certificates re-pinned
with the written reason; the frontend twin pin moves (the wire loses
`initialization` nodes).

**Proof-wave cost.** Small in the core (one constructor, two rules, one
arm, one `if`); medium in the proof layer that speaks of `.seq`'s env
(StateWf's `seqCont_locSup`; MachineSound's `seqCont` cases). Estimate:
2 sessions + the re-pin ceremony.

**Risk.** The closure/loop-variable class above; and one MORE, subtle:
`defer` and `recover` see the frame's environment through `tenv`
(Machine.lean:1941) — allocation at block entry does not change which
cells they see, only WHEN those cells came to exist; a deferred
closure reading a variable declared AFTER the `defer` statement but in
the same block is ill-typed Go, so unreachable. State it in the
design note; probe it.

**Design gate G-C4.** «Block-scoped allocation: `Stmt.initialization`
deleted, locals allocated at block entry; PRESERVING UP TO HEAP
ISOMORPHISM ONLY — observations unchanged (gate), `Loc` trajectories
and therefore dedup certificates and `repr` pins change and are
re-pinned with this reason; the closure-per-iteration and
backward-`goto` classes are probed before landing.» Recommendation:
YES, pre-pin, as the last C-item before the interface module; the
re-pin is of instruments, not of observations.

### 3.C5 — `.opDone` out of `Config`, into the thread `Status`

**Change.** With B4's `Status`, `.opDone sched inner` (Machine.lean:
2469) becomes `Status.running c (boundary : Option ChoiceSite)` — a
per-thread phase flag the pool consults (`boundarySite` Multi.lean:
1201 reads the flag; `atBoundary` :259 is `boundary.isSome ∨ shape`);
`opDoneInner` :140, `Config.itersNormalized_opDone`, `Config.locSup`'s
`.opDone` arm (StateWf.lean:463), the 12 `raceUpdate` probes (replaced
by the event's outcome class, which B2's `Result` at the apply
boundary now exposes — `StepAction` Multi.lean:675 already carries
`opDoneStrip`/`privateStep`; it gains the completed op's identity)
all go.

**Order.** After B4. Small.

**Preservation — the fuel question, answered.** Today the strip is ONE
`stepFn` step on both drivers (StepFn.lean:823; `Step.opDoneStrip`)
so `execProg_single_eq_execStmt` (MultiSound.lean:583) holds
step-for-step. Two options the first review left open: (a) keep a
no-op step that clears the flag → fuel identical, `fuelOut` rows
identical, the win is representational only; (b) drop the step → the
exact fuel at which a run reports `fuelOut` shifts by the number of
completed registry ops, and `execStmt_mono`-class statements are
untouched (monotone in fuel) but every fuel-out ROW in the baselines
and every pinned `Terminates`-class fuel witness re-pins. Recommendation:
(a) — the flag-clear stays a pool step (`stepThread` at a flagged
thread clears it and reports `opDoneStrip`), NOT a `Config` step; the
SEQUENTIAL relation loses `Step.opDoneStrip` (a `Step` on a `Config`
no longer needs it) and the sequential driver never sees the flag —
so `execProg_single_eq_execStmt` needs its statement adjusted: the
one-thread pool takes one extra step per completed op relative to
`execStmt`. That is a fuel shift IN THE THEOREM, not in the baselines
(the differential engine runs the pool driver — `runProgramPoolIntsM`,
the one ChoiceTrace.lean's header names — whose step count is
unchanged; VERIFY before landing that no baseline lane runs the
sequential driver, and if one does, keep the no-op step there too).
Preserving exactly on every baseline; the theorem is restated with
`fuel + opCount`. Gates: `ci --diff` zero drift (incl. fuel-out rows);
choice trace zero delta (`postOp` consults unchanged — same slots,
same bounds).

**Proof-wave cost.** `MultiSound`'s `stepMulti_sound`/`stepM_complete`
(:884/:1059) restate over `Status`; `execProgLoop_single` restated
with the count. 1 session.

**Design gate G-C5.** «`.opDone` becomes a per-thread `boundary` flag;
the strip stays a POOL step (no baseline fuel shift); the sequential
relation drops `Step.opDoneStrip`; `execProg_single_eq_execStmt` is
restated with the op count.» Recommendation: YES, bundled with B4's
landing.

### 3.P — native method promotion (a frontier decision, weighed)

**What it is.** Today the frontend synthesizes one forwarding method
per promoted method (`synthesizePromotionWrappers`, emit.go:5467;
`"wrapper": true` :5726), the wire's D2 contract says a type's method
set is "full, promoted methods included" (`docs/2026-08-10_method-set-
record-contract.md:76`), and the core carries `Func.wrapper` for
`recoverResult`'s gc-`FuncIDWrapper` imitation (Machine.lean:2326/
2330), `dispatchAccesses`' hop narrowing (Race.lean:641-685 via
`wrapperForwardArg`/`recvFieldChain` :600-640), and `nilValueMethodText?`'s
family test (Ops.lean:2103). Native promotion: the frontend emits NO
wrappers; a selector `x.M` on a struct with embedded fields is
resolved BY THE CORE through `FieldDef.embedded` (Syntax.lean:15) to
a receiver path `x.E1.E2` and the concrete method; interface dispatch
(`dynamicDispatch?`, Ops.lean:2129) walks the same chain.

**Behaviour-preserving in intent; three places it must reproduce
deliberately.** (1) The race footprint: gc's autogenerated wrapper
loads only the hop path (S3 convergence, Race.lean:641's docstring);
natively, evaluating the receiver `x.E1.E2` as a projection chain
under C1 loads the projected path — the narrowing FALLS OUT of the
trace, which is why P comes after C1; without C1 it would need a new
special case in the table. (2) `recover`: gc skips wrapper frames
("exactly one non-wrapper frame between gopanic and gorecover"); with
no synthesized frame at all, the real method frame is the one recover
finds — the same result as skipping, and `recoverThroughWrappers`
loses its `true` arm. (3) `nilValueMethodText` (BUG-087, [USER] ruled
demonic width 2): the family test says a PROMOTED wrapper target is
NOT in the family (`if target.wrapper then none` — probed: promoted
value methods on a nil box give the plain nil-deref text). Natively
the same fact must be decided from the resolved hop chain: a method
reached through ≥ 1 embedding hop is outside the family. That is one
line, but it is a SEMANTIC test that today rides on a frontend flag —
write it as a lemma target: `nilValueMethodText?` agrees before/after
on every corpus entry (the differential's BUG-087 rows are the pin).

**Cost.** Frontend: delete the synthesizer, emit `embedded` faithfully
(already on the wire); method-set records shrink to declared methods
(the D2 contract changes: "full" means declared; promotion is the
core's). Core: a `resolveSelector` in Ops (method lookup through
embedding depth, with Go's depth/ambiguity rules — the frontend's
static delegation already computes depth, so ambiguity is a
decode-time refusal), `dynamicDispatch?` gains the chain; `Func.wrapper`
and the four consumers deleted. Twin pin moves (wire loses wrappers).
Detector-soundness lane re-run (the hop-path rows are exactly its
`over-refusal`/`agree` cells). Estimate: 3-4 sessions after C1.

**Design gate G-P.** «Model embedded-field method promotion natively:
the frontend stops synthesizing wrappers (D2 contract: method sets
record DECLARED methods), the core resolves selectors and interface
dispatch through the embedding chain; `Func.wrapper` and its four
consumers are deleted; the hop-path footprint is the trace (requires
C1); twin pin moves; the BUG-087 family test becomes chain-depth ≥ 1
and is pinned by the existing rows.» Recommendation: YES, after C1;
it is a frontier decision (the contract moves) but the machine's
behaviour set is meant to be unchanged and the differential says
whether it is.

### 3.U — `consumeAtOne` uniformization (accounting change, weighed)

**What it is.** `ChoiceSite.policy` (State.lean:312-334): `mapIter`
pops even at width 1 (the done-check pick; "memo §5 ruling Q3"),
`appendSpill`/`l2Entry`/`l2Arrival` are `true` but vacuous (never
consulted at width 1 by construction), every other site is `false`.
Uniform rule: consume iff bound ≥ 2; the `SitePolicy.consumeAtOne`
field is deleted.

**What changes.** The SET of behaviours: unchanged (a width-1 consult
has one member either way). The stream REALIZATION: every range-over-
map's final done-check (and every single-candidate pick) stops popping,
so every later consumption in that run reads an EARLIER stream entry;
under a fixed stream a different member may be realized. Bijection on
streams: delete the width-1 `mapIter` draws from the old stream to get
the new one — total and stream-length-decreasing; the choice-trace
tool (B8's `PickRecord` dump, HANDOFF's B8-PREP) certifies it: the new
trace must equal the old trace with `⟨.mapIter, 1, _⟩` records removed.
Re-pin: every stream-indexed baseline row (the strict lane's fixed
8-10-entry streams; ChoiceTrace's B4 finding says most rows exhaust
them anyway, in which case pick 0 = canonical member and NOTHING
changes) — expected drift: a handful of rows whose fixed stream
crosses a range-over-map; each re-pinned member must be shown IN the
membership set (the membership lane's certified sets are stream-
independent and must be identical — that is the gate that says the
behaviour set did not move). `Choices.consumeAt_mapIter` (State.lean:
352) and the `mapIter` arm of `stepFn_oblivious`'s `hmi` (MachineSound.
lean:2889) simplify.

**Cost.** 1 session + the re-pin. **Design gate G-U.** «Uniform
consumption rule (pop iff bound ≥ 2); `consumeAtOne` deleted;
behaviour sets certified identical by the membership lane; realized
members under fixed streams re-pinned with the choice-trace bijection
as evidence.» Recommendation: YES, right after wave (iii) lands
(B8's trace is the certificate) — it removes a per-site policy table
from the interface's consumption story (§1.8 then says "a consult
pops iff it has a choice", full stop).

### 3.X — still excluded, and why

- **`unseq` (unsequenced operand evaluation).** A semantics WIDENING:
  E12/E13 are pinned as "structural (frontend ANF)" and the core
  cannot state them; admitting a Cerberus-style `unseq` would add
  behaviours. cerberus-lean MEASURED its unsequenced nodes before
  deciding how to reason about them (CERB `refined-cerberus/docs/
  2026-08-30_eunseq-census.md:11,109-120`: 98 `Eunseq` nodes in 23
  files, 201 arms, 94 binary, all inside an `Ebound` at a sequencing
  head; `:252`: 24 whose join is consumed by a store) — a census, not a
  ruling; the analogous measurement here would be a latitude-inventory
  row counting where Go's order is open and our ANF pins it. Go's spec
  DOES leave operand order open in places and we have chosen to pin it
  at the frontend. Reopening that is the doctrine's business (a
  latitude-inventory row), not this plan's.
- **Range-desugar footprint.** `for i, v := range s` lowers to a
  `while` over `$rcoll`/`$ridx`/`$rlen` (NativeToIR.lean:1224-1307);
  its race footprint is the desugar's (a whole-cell read of the slice
  HEADER per iteration) — race-equivalent to gc's one header read as
  far as anyone has probed. A FIDELITY question for the detector-
  soundness lane (`scripts/detector-soundness`), not an interface one;
  C1 makes the footprint definitional, which is what a future probe
  needs. Excluded here.
- **eface identity.** `renderPanicHead` uses `GoValue.eqb` as boxing
  identity and fails closed on the ambiguous case (review §3). A
  semantics ADDITION (modelling gc's pointer-identity collapse); it
  becomes live only if reflect/`fmt` land (G6, §4.4). Excluded.

### 3.I — small interface-closing items (no gate; ride the nearest wave)

- **I1** Delete the five refusal markers from the IR (Syntax.lean:187/
  202/413, Value.lean:484; `TypeDef.opaqueDecl` :74 → a `ProgramCtx`
  fact); `Ty.mentionsUnsupported` (Ops.lean:539) goes. Decoder refuses
  instead. Rides B7. Exact (accepted programs have no such node).
- **I2** `Result` → `Readout` (State.lean:93); `ExecOutcome` → deleted
  with B4. Rides wave (iii)/B4.
- **I3** `step_det_of_choiceFree` (§1.4) from B8's `stepFn_consumption`.
  Rides B8's landing or the first slice after.
- **I4** `RacyFine`/`footprintsConflict` (NPDRF.lean) restated over
  emitted traces; the detector as a fold. Rides C1.
- **I5** `GoLean/Interface.lean`: the re-export module; the §1.4/1.6/
  1.9 bridge theorems stated (proved where cheap: `run_ok_iff_stepsM`
  is `execProgLoop`'s definition unrolled + `stepMulti_sound`/
  `stepM_complete`; `run_refusal_free` STATED as the target, unproved,
  labelled); the `EctxLanguage` instance SKETCHED (not built — iris-
  lean is not a dependency of this repo and must not become one; the
  instance lives downstream, the LAWS it needs — `step_fill`,
  `step_fill_inv`, `fill_val` — live here). 2 sessions, last.

---

## 4. Interaction with the other lines

### 4.1 Stdlib slice 3: `print`/`println` and the stderr observable

The design of record (`docs/2026-09-03_stdlib-boundary-design.md:
816-825`) puts two append-only byte buffers in `ExecState` and bumps
the observation schema to `golean-observation-v2` with REQUIRED
`stdout`/`stderr` fields; `print` is ONE machine step (gc's
`printlock`); cross-goroutine interleaving is L1 latitude enumerated
by the membership lane (:837-843); address-bearing kinds refuse by
name (:848-871). Two of those four are interface decisions.

**Where the bytes live.** Not in `Store` (§1.2). A byte buffer in the
memory state is a field every frame lemma must say it does not touch,
and `Mem`'s two frame lemmas would carry a "stdout unchanged"
conjunct forever. iris-lean's `Language` already has the slot this
belongs in — the per-step OBSERVATION (`PrimStep : Expr × State → List
Obs → …`, IRIS `Language.lean:67-69,109-113`; heaplang uses it for
prophecy resolution, `Semantics.lean:386-391`). So: `StepEvent` gains
`out : List OutEvent` with `OutEvent := ⟨fd : Fd, bytes : ByteArray⟩`
(§1.4's sketch already shows it), `print` emits one event, and the
DRIVER folds events into `Readout.stderr/stdout` (§1.5). The
observation JSON is byte-identical to the design's (the fold is
concatenation in step order, which IS the interleaving the membership
lane enumerates); the difference is representational and it is the
difference between "output is a trace of the run" and "output is a
heap cell". For the consumer: a spec about printed output is a
statement about the event trace, exactly parallel to a spec about the
access trace — one vocabulary, two event kinds.

**Whether `Obs` gains output.** `Obs.ok (r : Readout)` carries it
(§1.5); `Obs.terminal t` does not — Go's `fatal error` and panic
output go to stderr too, and gc prints them AFTER the program's own
stderr; the design's oracle capture (fd 1/fd 2 separately, :826-836)
will record them. Decision needed: does a `.terminal` observation
carry the stderr prefix printed before the terminal? Recommendation:
YES (`Obs.terminal (t) (stderr : ByteArray)`), else a program that
prints then panics has an unstated observable. This is a schema-v2
question the slice must settle; flagged here because §1.5's `Obs` is
in the pin.

**Design gate G-OUT.** «Program output is a per-step EVENT (`StepEvent.
out`), folded by the driver into `Readout`, not a `Store` field;
`Obs.terminal` carries the stderr prefix.» Recommendation: event
trace. Cost: neutral to slice 3 (the design's machine-side buffers
become the driver's fold; same tests, same schema).

**The float-bits primitive** (`math.Float64bits`/`Float64frombits`-
class; ledger FR-21 item, register `docs/stdlib-admission-register.md:
218-222`, [USER]-gated, cap 2, currently 0/2). For the interface: a
pure `StrictOp` over `FloatBits.lean`'s kernel — no state, no trace,
kernel-reducible (FloatBits.lean:1-16 says so). One constructor in an
op table the consumer does not enumerate; NO interface change. The
condition the auditor attached (NaN payload exactness) is a fidelity
row, not a surface question.

### 4.2 The frontier fixes

FR-1/2/3/4/6/7/11/12/16/17/18/19/20/22/23/24 are frontend-only (ledger
§4): each moves the twin pin, none touches §1 — EXCEPT that FR-11/FR-20
(`goto`) must lower to `Signal` modes (`brkTo`/`contTo`-class, B4),
never to a frame-discarding jump (§1.3's cerberus lesson: a jump that
drops its context falsifies `fill`). Three are NOT frontend-only and
each meets the C-arc: **FR-10** (array-pointer views over slice
storage) adds a `Loc` shape or a view value — land it AFTER C1 or it
is baked into `Mem` twice; **FR-13** (structural `TypeId`s for
anonymous structs) is a type-identity design — land it WITH C2, whose
index-keyed `TypeEnv` is where structural identity would be decided;
**FR-15** (complex) adds a `GoValue` constructor and kernel ops — no
interface impact beyond the value type, last as the ledger says.

### 4.3 The reflect gate G6

RULED [USER] 2026-09-03 (relayed, `docs/2026-09-03_stdlib-boundary-
design.md:954-966`): commission a design memo for a "modeled,
layout-free `reflect` subset as a machine facility", after the first
two stdlib slices. What such a subset DEMANDS of §1, so the memo does
not discover it late: (a) run-time type descriptors as VALUES —
`GoValue.typeDesc (t : Ty)` or a `TypeIdx` — so `reflect.TypeOf` is
a projection of an interface box's dynamic type (already carried:
`GoValue.interface dynTy inner`); (b) the type table READABLE by the
program: `ProgramCtx.types` (B7) is exactly that — `NumField`/
`Field(i)`/`Kind`/`Elem` are lookups by field ORDER, never by offset,
which is what "layout-free" means and why `Platform` stays out of it;
(c) `DeepEqual` and `fmt`'s reflective walk are TYPE-DIRECTED
recursions over values — precisely the family C2 makes structural
(under fuel they would be fourteen more towers); (d) `errors.Is/As`
via reflectlite need (a) + assignability, which `Ty.eqb` and
`structTagCompatible` already decide. Consequence for sequencing: C2
BEFORE the G6 memo lands, or the memo designs against fuel.
Consequence for §1: `Ty` and `TypeIdx` become program-visible values —
a §1.1 fact worth recording now so the pin admits it.

### 4.4 The cedar-go refinement: what the first downstream proof needs

The target (`docs/2026-09-03_cedar-go-coverage-census.md` §5/§7; CEDAR
`Spec/`): `isAuthorized : Request → Entities → Policies → Response`
(CEDAR `Authorizer.lean:56-63`, 8 lines) over `evaluate : Expr →
Request → Entities → Result Value` (`Evaluator.lean:98`), with
`is_authorized_congr_evaluate` (CEDAR `Thm/Authorization/Authorizer.
lean:96-98`: per-policy `evaluate` agreement gives `isAuthorized`
agreement) as the hinge. cedar-go's authorizer is sequential, map-
heavy, closure-light, `go`-free (census :279-280). The statement shape
a refinement wants, in §1's vocabulary:

```lean
theorem cedarGo_refines (P := cedarProgram) :
  ∀ (req : Request) (es : Entities) (ps : Policies) fuel ch,
    Accepted P →
    (run P main (encode req es ps) fuel ch = .obs (.ok r) → decode r = some (isAuthorized req es ps)) ∧
    (run P main (encode req es ps) fuel ch ≠ .obs (.terminal t)) ∧
    (run P main (encode req es ps) fuel ch ≠ .refusal _)
theorem cedarGo_total : ∃ fuel, ∀ ch, run P main (encode …) fuel ch ≠ .fuelOut
```

with `decode` quotienting `determiningPolicies`/`erroringPolicies` to
SETS (census :579-585: `order_and_dup_independent` does not transfer
as stated because the Go side's `Reasons`/`Errors` are map-ordered
— E9 latitude; the `∀ ch` is what makes the set quotient necessary and
sufficient). What the proof consumes from §1, concretely and in the
order it will hit them:

1. **`run_ok_iff_stepsM` + `execProg_single_eq_execStmt`** (§1.6) to
   reason by `Steps` on a one-goroutine program — G-EXIT closed on our
   side.
2. **`step_det_of_choiceFree`** (§1.4) for every step that is not a
   map iteration — the whole program is deterministic except at
   `mapIter` picks, so "some run" becomes "every run" everywhere else,
   and the map picks are exactly where the set quotient enters
   (G-MAPITER's `Perm`-of-draws law, PARK plan :506-540, stated over
   B1's entry ids — `mapIterK` frames over `Nat` sets are what makes
   that law provable).
3. **`fill`/`step_fill_inv`** (§1.7) — `Evaler.Eval(env)` is an
   interface-dispatched recursive walk over 50 node kinds (census
   :576-578); the per-node correspondence is a `wp_bind` per call, and
   50 × 3-premise `wp_plug_bind`s is the difference between a summer
   and a decade. C3 + B4.
4. **`Mem.load_after_disjoint_store`** (§1.2) under G-REPR's
   `own_struct`/`own_map` — `types.Set` is `map[uint64]Value` with
   linear probing (census :586-596) and `Record` wraps `map[String]
   Value`; the abstraction function to Cedar's canonical `Set`/`Map`
   (CEDAR `Thm/Data/List/Canonical.lean`) is the refinement's real
   work and it is a points-to argument per map cell. C1.
5. **`Accepted P` decidable and `run_refusal_free` stated** (§1.9) —
   the refinement's first conjunct is vacuous unless refusal-freedom
   is at least a named target; today "the machine never returns
   `.internal` on wf input" is a docstring (Value.lean:184-197).
6. **The program must EXPORT first.** Today 5/34 census cases lower
   (census :661-663, unchanged across three re-measurements);
   blockers FR-12 (range-over-func, incl. `authorize.go:38`), FR-23,
   `errors.Join` (29 decls), and the JSON codec (38 decls, reflect-
   bound → G6). No lemma in §1 helps until the frontier moves; the
   refinement is the SECOND thing after export, not the first.

What cedar-go does NOT need and this plan therefore does not hurry:
`Fair` (sequential), the channel module B5, `StepM`'s pairing rules,
`Platform` parametricity (the authorizer's `int` arithmetic is
`int64`-shaped by construction; a `∀ p` theorem is a bonus).

---

## 5. Sequencing, sizes, and the two calendar points

### 5.1 The order and the sizes

| # | Item | Depends on | Sessions | Preservation | Gate to [USER] |
|---|---|---|---|---|---|
| 0 | wave (iii) B2 + B3 + B8 (+A7) | — | 3-4 (in flight) | exact | — (ratified arc) |
| 1 | U `consumeAtOne` uniform | B8 | 1 + re-pin | behaviour set exact; realization re-pins | G-U |
| 2 | B4 `Signal` + `Status` (+I2) | (iii) | 2 | exact | — |
| 3 | C5 `.opDone` → flag | B4 | 1 | exact on baselines; theorem restated | G-C5 |
| 4 | B7 `ProgramCtx`/`Store` (+I1, Platform threading) | (iii) | 2 | re-packaging | — |
| 5 | C1 `Mem` + trace (+I3, I4) | B7 | 4-6 | trace-equality audit | G-C1 |
| 6 | C2 well-founded `TypeEnv` | — (parallel lane from 2) | 4-5 | exact; twin pin | G-C2 |
| 7 | B6 `VarId` | (iii) (parallel lane) | 2-3 | bijective renaming; twin pin | — |
| 8 | P native promotion | C1 | 3-4 | intent-exact; twin pin; detector re-run | G-P |
| 9 | C3 `List Frame` via views | B3, B4, P (wrapper field gone) | 3-4 | definitional | G-C3 |
| 10 | C4 block-scoped allocation | B6 | 2 + re-pin | up to heap iso | G-C4 |
| 11 | B5 `Chan` module | — (optional, any time) | 1-2 | equational | — |
| 12 | I5 `Interface.lean` + bridge theorems | all above | 2 | — | — |
| 13 | assessment re-run | 12 | 1-2 | — | — |
| 14 | pin offer | 13 | — | — | G-PIN |

Critical path: (iii) → B7 → C1 → P → C3 → I5 → assessment → pin ≈ 17-22
sessions; with C2 and B6/C4 in parallel lanes and merge trains the
whole table is ≈ 28-38 sessions of work at 1-3 concurrent lanes. That
is a quarter's worth at one lane and six-to-eight weeks at three; it
is also the LAST time this reshaping is cheap — after the pin every
item here is a coordinated two-repo change.

### 5.2 Where the assessment re-run belongs

After item 12 and before the pin. Reason: the fidelity assessment
(`docs/2026-08-31_fidelity-assessment-plan.md`, lanes A-E; decisions
`docs/assessment/decisions-2026-08-31.md`) graded C1-C4 (feature
totality, lower bound, upper bound, apparatus) against a tree whose
refusal grammar, memory representation, detector footprint and
consumption accounting will all have been rewritten. Every slice's own
gate is zero-drift, so the EXPECTED result is "unchanged" — and that
is precisely the claim a re-run exists to certify rather than assume:
the lower-bound lane against the pinned oracle (unchanged by
construction), the upper-bound lane's latitude census against the
NEW consumption story (U changes the site table; B8 changes how widths
are stated), the apparatus lane against the retired mirrors (D-10's
`stepNeeds` finding closes), the detector-soundness leg against the
trace (C1). One thing the re-run must ADD: the `Accepted`/
`run_refusal_free` frontier as a graded item — "how many corpus rows
reach `.internal`" is a number the assessment can now derive from a
type.

### 5.3 Where the pin belongs

Offer the pin when: (a) `GoLean/Interface.lean` exists and matches §1
name for name; (b) items 0-10 have landed (C4's heap-iso re-pin done —
a pin that predates C4 forces the downstream to absorb an allocation-
order change later; NPDRF obstruction 1 says they must tolerate heap
iso anyway, but "must tolerate" and "were handed a moving target"
are different sentences); (c) the assessment re-run is green; (d)
this document carries "PINNED @ <sha>". B5 (Chan) may follow the pin
— it changes no §1 name. P must precede it (it deletes `Func.wrapper`
from `Func`, §1.1). Everything after the pin is a two-repo change and
is scheduled as such.

### 5.4 The design gates, collected (verbatim, for the [USER])

**Ruling record, 2026-09-04.** [AGENT] record; the [USER] quote was
received by the [AGENT] coordinator and RELAYED to the recording
worker, so it is cited as relayed, not firsthand (U0-incident
convention). Presented with this section's nine gates, each carrying
a recommendation, Mike replied, verbatim as relayed: «Great, this
sounds good - let's move ahead with the plan. Our top level goal
here is (1) to be a highly accurate go semantics, and (2) to support
reasoning about go using an iris-lean layer (which we won't build,
that's a customer)» — read by the coordinator as: all nine gates
(G-U, G-C5, G-C1, G-C2, G-P, G-C3, G-C4, G-OUT, G-PIN) RULED as
recommended below, plus the two top-level goals stated (carried
forward into `CLAUDE.md`). Earlier the same day, the standing
direction that frames the C-arc's move from deferred-in-principle
to scheduled (`docs/2026-09-03_design-hygiene-arc.md` (v)): «I think
we should try to do the disruptive thing if it'll result in a more
useful reasoning surface».

- **G-U.** «Uniform consumption rule (pop iff bound ≥ 2); `consumeAtOne`
  deleted; behaviour sets certified identical by the membership lane;
  realized members under fixed streams re-pinned with the choice-trace
  bijection as evidence.» Rec: YES, first after wave (iii). RULED
  [USER] 2026-09-04 — as recommended (relayed).
- **G-C5.** «`.opDone` becomes a per-thread `boundary` flag; the strip
  stays a POOL step (no baseline fuel shift); the sequential relation
  drops `Step.opDoneStrip`; `execProg_single_eq_execStmt` is restated
  with the op count.» Rec: YES, with B4. RULED [USER] 2026-09-04 — as
  recommended (relayed).
- **G-C1.** «Adopt `Mem` with an emitted access trace as THE definition
  of a step's footprint; retire the `stepAccesses` table once
  `accesses_eq_stepAccesses` is proved arm by arm; any arm where the
  theorem fails is filed as a detector BUG (red-first row, referred),
  never absorbed.» Rec: YES. RULED [USER] 2026-09-04 — as recommended
  (relayed).
- **G-C2.** «Frontend emits typeDefs in dependency order with aliases
  inlined (twin pin moves); `TypeEnv` becomes index-keyed and
  well-founded by an `Accepted` clause decided at decode; the 14 fuel
  towers, `typeResolutionFuel` and the `irreducible` seal are
  deleted.» Rec: YES, parallel lane. RULED [USER] 2026-09-04 — as
  recommended (relayed).
- **G-P.** «Model embedded-field method promotion natively: the frontend
  stops synthesizing wrappers (D2 contract: method sets record DECLARED
  methods), the core resolves selectors and interface dispatch through
  the embedding chain; `Func.wrapper` and its four consumers are
  deleted; the hop-path footprint is the trace (requires C1); twin pin
  moves; the BUG-087 family test becomes chain-depth ≥ 1 and is pinned
  by the existing rows.» Rec: YES, after C1. RULED [USER] 2026-09-04 —
  as recommended (relayed).
- **G-C3.** «`Cont := List Frame` with `@[match_pattern]` views for the
  31 constructor names; `Config := Mode × Cont`; `fill` is append; done
  before the pin, never after.» Rec: YES, after B4 and P. RULED [USER]
  2026-09-04 — as recommended (relayed).
- **G-C4.** «Block-scoped allocation: `Stmt.initialization` deleted,
  locals allocated at block entry; PRESERVING UP TO HEAP ISOMORPHISM
  ONLY — observations unchanged (gate), `Loc` trajectories and
  therefore dedup certificates and `repr` pins change and are
  re-pinned with this reason; the closure-per-iteration and
  backward-`goto` classes are probed before landing.» Rec: YES, last
  C-item before the interface module. RULED [USER] 2026-09-04 — as
  recommended (relayed).
- **G-OUT.** «Program output is a per-step EVENT (`StepEvent.out`),
  folded by the driver into `Readout`, not a `Store` field;
  `Obs.terminal` carries the stderr prefix.» Rec: event trace; decide
  before slice 3 lands. RULED [USER] 2026-09-04 — as recommended
  (relayed): per-step event.
- **G-PIN.** «The reasoning repo pins a SHA whose `GoLean/Interface.
  lean` matches this document's §1; a refactor preserving §1 is not a
  breaking change; a change to §1 is a pin move with a written
  reason.» Rec: offer after §5.3's four conditions. RULED [USER]
  2026-09-04 — as recommended (relayed).

### 5.5 What the grumpy professor will not pretend

- The session counts are guesses anchored to two data points. The
  first review graded C3 "very high"; this one grades it "high,
  mechanical" on the strength of one compiling prototype and one
  precedent (A1's views). If the views bite in `fun_cases`, C3 costs
  double and the order still holds.
- `run_refusal_free` is stated as a target and will stay unproved for
  a long time. It is in the interface because a promise you cannot
  yet keep is still better than a promise you did not write down; the
  reasoning side should treat it as an assumption with a name.
- Nothing here makes cedar-go export. The frontier work (FR-12,
  FR-23, `errors.Join`, the codec/G6) is a separate line with its own
  ledger; this plan only guarantees that when it does export, the
  proof does not have to fight the representation.
- cerberus-lean-proj's most useful lesson is the one that costs
  nothing: their [USER]'s «I feel like abstractions should do some work for us …
  How much does this actually buy us?» (CERB `refined-
  cerberus/docs/DECISIONS.md:372-378`, the 2026-09-02 "PARAMETRIC
  INTERFACES NOT ADOPTED" ruling; KOI B9) led them to DEFER a parametric memory interface and prove rules
  directly against the step relation. §1.2's `Mem` is not that
  abstraction — it is not a typeclass, has one instance, and exists
  to make the TRACE definitional, not to admit a second memory model.
  If it ever grows a second instance, someone should ask their
  question again.

---

## 6. Lessons from cerberus-lean / refined-cerberus, pitfall by pitfall

Read-only, from `/home/dev/projects/cerberus-lean-proj/` (CERB; nothing
there was modified). The sibling project instantiated an Iris-style
separation logic over the Lem→Lean port of Cerberus Core and has been
audited five times in a week (skeptical re-audit 2026-09-01, audit
response 2026-09-02, shareable-main review 2026-09-03, Reynolds/O'Hearn
audit 2026-09-04, fuel-parameter review 2026-09-04). Each row: the
pitfall as THEY hit it (their cite), our exposure TODAY (our
file:line), the item here that closes it. "✓" = we already stand on
the right side; the row is kept so nobody moves us off it.

| # | Pitfall (as they hit it) | Their record (CERB) | Our exposure today (`aceb0dcb`) | Fixing item |
|---|---|---|---|---|
| L1 | Fuel exhaustion as an OPAQUE sentinel: no `∀ fuel` statement can classify an out-of-fuel run; a package-defined driver was built, then ruled out — «We should not be writing our own trusted driver code» | `docs/2026-09-02_request-cerberus-lean-fuel-exhaustion-outcome.md:32-58`; `docs/DECISIONS.md:630-645, 649-660, 1787-1800` | ✓ `Stop.fuelOut` is a transparent constructor (Value.lean:240-246); fuel is a parameter of `execProgLoop` (Multi.lean:1819) and `run_mono`-class lemmas exist (`execStmt_mono` MachineSound.lean:750). Exposure: FOUR drivers (StepFn.lean:834/882/903, Multi.lean:1876) | §1.5 one `run`; §1.6 `run_ok_iff_stepsM` |
| L2 | Fuelled HELPERS whose exhaustion is the return type's `Inhabited` default — the run CONTINUES with a wrong value; their rule: every fuel'd function must be (A) structural, (B) absorbing-typed exhaustion, or (C) gate-checked unreachable | `docs/2026-09-04_review-of-fuel-parameter-design.md:57-100`; `DECISIONS.md:2118-2126`; KOI A5 (61 `panic!` arms read as defaults) | Our 14 fuel towers fail CLOSED (a `Refusal`, never a default — Ops.lean:14-28), i.e. already (B); but `typeResolutionFuel` (Ops.lean:29) is in every unfolding and 31 `set!`/`eraseIdx!` sites (Ops.lean:157,1454,2163; Machine.lean:274,980,2592,3139; Multi.lean:497,1023,1042,1065; …) are kernel-default-on-OOB ops guarded by convention, not by type | C2 (rule A: structural); the `!`-ops → `Array.set` under a bounds proof as A2's `updateCell` does (ride B5/C1); keep the ci escape-hatch scan |
| L3 | A hand-written MIRROR relation beside the engine (1,943-line `Step`, 4,943-line one-directional `Soundness`): "a certified package projection of a selected Core", not "over Cerberus Core" | `docs/2026-09-01_cerberus-heaplang-skeptical-re-audit.md:298-322` (R-03); ARCHITECTURE glossary "the mirror … a proof device with no semantic authority" | ✓ two-sided: `stepFn_sound` (MachineSound.lean:44) AND `step_complete` (:393), `stepMulti_sound`/`stepM_complete` (MultiSound.lean:884/1059). Exposure: the relation is INTERLEAVED with the executable (review U14) and carries the 17 twins | B2 (twins); keep BOTH directions in §1.4; extraction after B2/B4, never before |
| L4 | `Language.Context` is FALSE because a jump discards its frame (`Erun`): no `EctxLanguage`, bind proved by hand | `cerberus-heaplang/CerberusHeapLang/Lang.lean:94-100`; `DECISIONS.md:360-371` (parametric spike: "control mixin not an `EctxLanguage` instance because `Erun` discards its context") | Same disease, different cause: the two-step panic abort makes `primStep_fill` false, hence the park's `hdrain` premise (PARK `Laws/Bind.lean:22-34`); `goto` (FR-11/FR-20) could ADD their cause if lowered as a frame-discarding jump | B4 `Status` (panicked is a thread status) + C3 (`fill` is append); §4.2: `goto` lowers to `Signal` |
| L5 | `toVal` is CONTROL-dependent: "a value at a non-empty stack is a RETURN redex (`toValRt = none` at `κ ≠ []`)"; congruence guards `toVal e1 = none` on every sequencing lift | `DECISIONS.md:1277-1284, 1326-1330` | ✓ `toVal ⟨.next, []⟩ = some ()`, `retV` never at the empty stack (PARK `Lang.lean:20-25`); exposure: terminal shapes are enumerated at six sites (§2 G2) | B4 `Status.done`; §1.7 keeps `Val := Unit` |
| L6 | The memory invariant lives INSIDE the state interpretation (`MemWF`, ten engine-cited fields, a field of `CohG`; `Coh` = per-cell coherence + pairwise disjointness) and every op has its preservation theorem | `cerberus-heaplang/ARCHITECTURE.md:411-430`; `Heap.lean:386-389` | ✓ one predicate `StateWf` (StateWf.lean:595) preserved by `step_preserves_wf` (:6658); the park put `HeapWf` in `stateInterp` (PARK `Adequacy.lean:105-108`). Exposure: two VACUOUS conjuncts still threaded (`itersNormalized` 113+103 mentions; function-body `locSup`) | §1.9; B3/B7 delete the conjuncts |
| L7 | Points-to granularity chosen for the logic, not the machine: a typed VIEW = metadata + byte range (`pointsToView`), fractional/split laws proved with NO client (R-06) | `Heap.lean:2714-2720`; re-audit `:399-410` | The park's ghost heap was WHOLE-CELL, dropping field/index keys (PARK `HeapBridge.lean:33-47`) — no per-field frame at all (G-REPR open) | C1 + §1.14(3): keys = `ShadowKey` leaves + sync words, the detector's own overlap table; build split laws only when a corpus member needs them |
| L8 | The allocation rule unreachable from adequacy; allocating examples proved by concrete traces that BYPASS the logic (R-01/R-02, both Critical) | re-audit `:170-297` | Park: alloc laws hardcoded per cell count (`wp_alloc_step₂/₃/₄`, PARK `Lifting.lean:170-312`); every example discharged `funcListSup … ≤ 0` by `decide` (PARK `Examples/BinSearch.lean:1478`) | C1 `Mem.alloc` (one rule); A4-owed `locSup` deletion (B7); §1.6 so examples exit through `run`, not a replay |
| L9 | The capability manifest validates DECLARATIONS, not use; broad constructors hide NO-RULE variants (15 of them: locking store, union-member pointer, zero-size create, `free(NULL)`, …) | R/O'H audit `:133-145` (Finding 1); ARCHITECTURE §6 NO-RULE table | Our NO-RULE variants are the five `unsupported` IR constructors (§2 G18) and every `.stuck` arm; nothing states which `Accepted` programs the relation is total on | I1 (no refusal markers in the IR); §1.9 `Accepted` + `run_refusal_free` as the NAMED target; the downstream's statement-TCB deletion test (PARK `Audit.lean:130-560`) as the enforcement |
| L10 | The client abstraction boundary is not ENFORCED (readouts cross it; the boundary check is text-based and per-module allowlisted) | R/O'H audit `:205-215` (Finding 2); KOI C11-C12 | The park's veneer ban / A-TRIP was a lint over a scope file (revival guide: "the scope config is young") | §1.13: `GoLean/Interface.lean` is the boundary and the kernel-level deletion test is the check — a constant outside the interface in a designated statement's closure is a build failure |
| L11 | Judgments fixed to one profile/mask (`SemTriple` at `spikeCtx`; statement logic hard-wired to `⊤`) — less general than the prose | R/O'H audit `:263-272` (Finding 3); re-audit `:452-465` (R-09) | Park adequacy pinned `functions/methods/types` by THREE equalities (PARK `Adequacy.lean:83`); theorems stated at `platform` not `∀ p` (A-series §A5) | B7: `ProgramCtx` (incl. `Platform`) as ONE section variable |
| L12 | Two separately proved bridges for the same engine round feed adequacy and the rule layer — "not a soundness hole" but duplication and drift risk | R/O'H audit `:303-330`; KOI B12 | Several bridges: `stepFn_sound`/`step_complete`, `execProg_single_eq_execStmt` (MultiSound.lean:583), `execProgLoop_ok_of_allStreamsOkPool` (MultiStreams.lean:801), `checkCert_slowObs` (EnumDedupSound) | §1.6: ONE `run_ok_iff_stepsM` derived from the pool bridges; enumeration soundness stays engine-side, off the interface (§1.12) |
| L13 | Parametric semantics interfaces DEFERRED — «abstractions should do some work for us … How much does this actually buy us?»; rules proved directly against `Step` and the memory state | `DECISIONS.md:372-378`; KOI B9; ARCHITECTURE §6 | `Mem` (§1.2) is not a typeclass and has one instance; it exists for the TRACE, not for a second memory model | §5.5's standing question: a second `Mem` instance needs a customer first |
| L14 | «NO BORING LOGIC; A PROJECTION THEOREM ONLY» — a semantic separation logic beside Iris was REJECTED as a second logic; the semantics exports "just memory + pure properties" | `DECISIONS.md:446-454` | ✓ this repo makes no verification claims (CLAUDE.md); the interface exports definitions and bridge theorems, never proof rules | §1 by construction; I5 SKETCHES the `EctxLanguage` laws, does not build the instance |
| L15 | Re-pin drift: the pinned semantics fell ≥ 34 commits behind its mainline; the re-pin is a 2.5-4 worker-day arc with exported-text changes | KOI A4, A6; `docs/2026-09-03_repin-scout*.md` | We are the pinned side; the park already drifted (§0 item 1: `Heap.set`, `coerceStoredValue`, `typeResolutionFuel`) | §1.13: pin the DOCUMENT; a §1-preserving refactor is not a pin move |

Two things they did RIGHT that §1 copies without apology: every
exported statement carries a `file:line` into the pinned semantics and
"a disagreement between any definition here and the engine is a defect
here" (ARCHITECTURE §1 — our version: a disagreement between §1 and
`Interface.lean` is a defect in the tree, not the document); and the
trust base is stated as a LIST (kernel + trio; iris-lean as definitions
only; the pinned semantics as a policy sampled by differential
validation — ARCHITECTURE §3 `:432-440`), which is CLAUDE.md's "trusted
surface" paragraph in another dialect.

Provenance note on this section: the CERB citations in §1.3, §1.5, §3.X
and §5.5 were written before the delegated cerberus survey returned and
were VERIFIED against the files afterwards; three were corrected in the
follow-up commit (the `Erun` cite `Lang.lean:28-35` → `:94-100`; the
`Eunseq` census claim "no store ever an arm" → the measured `:252`
figure; the "abstractions should do some work" ruling `:360-371` →
`:372-378`). [AGENT]
