# The GoLean master plan v2 — what is missing for RefinedC-like reasoning over a faithful Go semantics, and what is at hand (2026-09-07)

Status: PLAN OF RECORD for the reasoning-surface line (it supersedes the
named parts of the 2026-09-05 plan listed in §0.5 and nothing else), docs
only. [AGENT]-authored (lane `master-plan-0907`, worktree off `main` @
`da0a9c2c`, 2026-09-07); [USER]-commissioned (§0.1). Every number names
the command or `file:line` it came from; every status is one of the six
words of §0.3; every decision cited carries [USER]/[AGENT] provenance,
and [USER] quotes are cited AS RELAYED by the [AGENT] coordinator (the
U0-incident convention) unless a tracked record shows otherwise. This
repo makes NO verification claims about Go programs (`CLAUDE.md`, "What
this repo is"); nothing here is one, and nothing here builds the
reasoning layer — it says what that layer needs FROM this repo and what
of the old attempts can be adapted.

---

## 0. Purpose, commission, vocabulary, snapshot

### 0.1 The commission

[USER] Mike, 2026-09-07, verbatim as relayed by the [AGENT] coordinator
(cited as relayed, not firsthand): «Do we have an up-to-date 'master
plan' which lays out exactly what is missing, and what will be needed
for some 'refinedC' like reasoning vs. golean, while making it a
faithful Go semantics? Can you put that together, along with a log of
what we have at hand (eg. on branches) that might be adapted.»

The same day, on the external prover track this document's §4.4 serves
([USER] Mike, 2026-09-07, verbatim as relayed by the [AGENT] coordinator
— cite as relayed): «I've been experimenting with running a codex agent
in parallel. This tends to work well on highly ambitious work that is
resistent to goal-drift. Eg. deep theorems with clear specs. Ideally this
would be separated from the main line work». This document is the
tracked home of both quotes.

Three readers: (a) the [USER]; (b) future review and prover agents,
including an external Codex agent given deep, drift-resistant theorem
work (§4.4 names those items with exact acceptance criteria); (c) the
next independent whole-project review (§5.2 is its brief). Everything
is written to be CHECKED: statuses carry their pointer, numbers their
derivation, assets their `branch:path`.

### 0.2 How to read this document

- §1 says what a RefinedC-like layer over GoLean IS and what it needs
  from GoLean, in layers (the "Caesium role"), and what a faithful
  semantics forbids of that layering.
- §2 is the checklist of what is MISSING, one row per item, with the
  statement owed, its dependency, size, owner class and evidence.
- §3 is the asset log: every branch and parked artifact surveyed
  (read-only, via `git show`/`git log`/`git diff --stat`), classified
  ADAPTABLE / DEAD / SUPERSEDED with the concrete thing to lift.
- §4 is the layering and sequencing: the dependency graph from GoLean
  exports to a RefinedGo, the critical paths to a SEQUENTIAL and to a
  CONCURRENT pin offer, the recommended next wave, calendar points, and
  the [USER] decisions pending.
- §5 is provenance, maintenance and the review brief.

The tracked documents this plan indexes (read them, not this summary,
when the two disagree — and file the disagreement): the 2026-09-05 plan
`docs/2026-09-05_master-plan.md` (v1; packages B–I and §4 broader goals
remain its; §7 = the gate audit's dispositions; §7.8 = the sprint
landing); the independent gate audit `docs/2026-09-05_project-gate-audit.md`
(F1–F13, Gates A–D); the reasoning-surface plan
`docs/2026-09-04_reasoning-surface-plan.md` (RSP; §1 the interface as
sketched, §1.6/§1.7 REJECTED AS SKETCHED, §1.14 the iris-lean
instantiation, §6 the cerberus-lean pitfall table); the Gate A1 contract
`docs/2026-09-05_gate-a1-contract.md`; the A2 customer
`docs/2026-09-05_iris-customer-design.md`; the typed-consumer sprint
charter, handoff and landing plan (`docs/2026-09-05_typed-consumer-sprint-charter.md`,
`docs/2026-09-05_typed-consumer-sprint-handoff.md`,
`docs/2026-09-07_typed-sprint-landing-plan.md`) and the five landing
notes `docs/2026-09-07_land-*.md`; the revival guide
`docs/2026-08-31_reasoning-revival-guide.md`; the split plan
`docs/2026-08-31_repo-split-plan.md` (+ its 2026-09-05 addendum);
`docs/ARCHIVE.md`; the doctrine `docs/2026-08-11_essence-of-go-doctrine.md`;
the latitude census `docs/2026-08-11_latitude-inventory.md`;
`docs/BUGS.md`; `docs/language-coverage-ledger.md`; `GoLean/Interface.lean`;
`GoLean/GoCore/NPDRF.lean`; `spikes/gate-a1/`, `spikes/iris-customer/`,
`spikes/i1-declarations/`. The architecture rules are `AGENTS.md`
(moving to `docs/architecture-rules.md` by the parallel lane
`agents-alias-0907`; cite as "the architecture rules").

### 0.3 Status vocabulary (exact; used for every item below)

| word | meaning | must carry |
|---|---|---|
| LANDED | on `main` at or before `da0a9c2c` | the commit SHA |
| IN FLIGHT | exists on a branch, not on main (branch-complete, under review, or abandoned mid-work — the row says which) | the branch name and tip |
| RULED | a [USER] decision exists and is recorded | the record pointer (file §/line) |
| PROPOSED | an [AGENT] recommendation with no [USER] ruling | "[AGENT]" and the decision the [USER] would make |
| OWED | a recorded debt from a landed step (no new decision needed) | the note that recorded it |
| PENDING [USER] | cannot proceed without a named [USER] decision (v1 wrote BLOCKED-ON-USER for this) | the decision, stated |

For §3's assets a second, orthogonal vocabulary: ADAPTABLE (statements,
lemma shapes, tactics, corpus or design reusable with renaming over the
current core), DEAD (built over deleted or restructured definitions —
named), SUPERSEDED (its job is done differently on main — by what),
UNKNOWN (could not be classified read-only — why).

### 0.4 The snapshot this document describes (`main` @ `da0a9c2c`, 2026-09-07)

Every figure re-derived in this lane's worktree at that tip unless
marked "(not re-derived)".

- `git log -1 --format='%h %ad %s' main` → `da0a9c2c 2026-09-07 L6
  land/sprint-records: record the gate at the clean committed tip
  0c9c6d6a (scripts/ci --diff PASS, 3654/3654 zero drift on main
  29f77b43) …`.
- Baseline tally: `awk -F'\t' '!/^#/ && $1!="result"{c[$1]++} END{for(k
  in c) print k, c[k]}' baselines/native-full.tsv` → **PASS 3403, FAIL
  251** (3654). By stage (same file, `$1" "$3`): PASS `-` 3139,
  confluent 89, membership 140, racy 35; FAIL frontend-export 197,
  lean-observation 32, differential 10, go-observation 10, confluent 1,
  `lean-observation|differential` 1 (the single [USER]-ruled alternation
  row). Negative lane (`baselines/negative-full.tsv`, same awk): 394 PASS
  / 0 FAIL.
- Gate: the L6 note (`docs/2026-09-07_land-sprint-records.md:121-143`)
  records `scripts/capped scripts/ci --diff` at the clean committed tip
  `0c9c6d6a`: `RESULT: PASS`, `ok baseline diff FULL (3654/3654, no
  regression)`, `git_dirty false`, `jobs 8`. `da0a9c2c` is the
  records-only commit that recorded that tail. This lane's own gate at
  its tip is §5.1.
- Unpushed: `git rev-list --count origin/main..main` → **2**
  (`0c9c6d6a`, `da0a9c2c`; `origin/main` = `29f77b43`). Push is a
  separate [USER] sign-off, not this lane's.
- Oracle pin `baselines/go-oracle-pin` = `go1.26.5`; twin wire pin
  `sha256sum baselines/pins/twin-chdriver.wire.json` = `758110a3f5a212b8…`
  (unchanged since e13-b, v1 §0.2).
- Bugs: `grep -c '^## BUG-' docs/BUGS.md` = 107; `grep -c '^- Status:
  open'` = 17; `fixed` = 90 (the only two status words the gate accepts;
  BUG-001..107 contiguous). The 17 open, by class: §2.3.
- The core: `ls GoLean/GoCore/*.lean | wc -l` = 88 modules; `cat
  GoLean/GoCore/*.lean | wc -l` = 45,018 lines; `find GoLean -name
  '*.lean' | xargs cat | wc -l` = 50,363; `Tests/` 39,661. Of the 88
  modules, 57 were added by landing chunk L1 (the typed layer — v1
  §7.8.2's breakdown: Boolean profile 12; recovery static 7,
  storage/setup 13, control/preservation/progress 15, pool/choices 4;
  generic abort observer 4; `Declaration`, `PanicText`; per
  `docs/2026-09-07_land-typed-core-proofs.md`).
- The relation: `inductive Step` at `GoLean/GoCore/Machine.lean:4149`
  has **112** constructors (`sed -n '4150,4842p' … | grep -c -E
  '^\s*\| [a-zA-Z_]'`; the next top-level declaration is at :4843);
  `Config` (:2830) 10 constructors; `StepE` (`Multi.lean:2371`) 2,
  `StepM` (:2406) 7, `StepMFine` (`NPDRF.lean:192`) 7 (same awk per
  block). The park survey's alternate count of 114 used
  `awk '/^inductive Step /,/^end /'` over the whole file and is the
  wider range's artifact; the two agree on the structure.
- The tape: `inductive ChoiceSite` (`GoLean/GoCore/State.lean:339-351`)
  has **13** constructors — `mapIter appendSpill l2Entry l2Arrival
  l4Waiter l1Sched l5ExitWindow postOp backEdge nilValueMethodText
  tryLock unseqPanic repanicCollapse` (several per line; a per-line
  grep undercounts to 9 — do not use one). The inventory's §0 mirror
  lists the same 13 (`docs/2026-08-11_latitude-inventory.md:118-131`);
  reconciler C12 checks it.
- `GoLean/Interface.lean`: 185 lines, 18 `import` lines, **zero
  definitions of its own** — a re-export facade whose body is one
  docstring stating what the imported modules prove and do not prove
  (§2.1 item 5 quotes it).
- Spikes (outside the default build and `scripts/ci`'s dependency
  graph): `spikes/gate-a1/` (8 modules), `spikes/iris-customer/` (24
  modules), `spikes/i1-declarations/` (1); iris-lean pinned in both Iris
  spikes at `e7a0a43814c4f1154ca0c8049883ca56c2288b86` (the park's pin;
  `spikes/iris-customer/lakefile.toml:13-16`), Lean 4.32.2.

### 0.5 Relation to the 2026-09-05 plan (v1): what v2 supersedes

v1 (`docs/2026-09-05_master-plan.md`) stays the index for packages
B–I (§3.B language frontier, §3.C stdlib boundary, §3.D latitude, §3.E
apparatus, §3.F frontend trust, §3.G bug backlog, §3.H downstream
subjects, §3.I process) and for §4 (broader goals not yet decomposed)
UNLESS a row here restates an item — then this document's row is the
current status and v1's is history. v1 §1.7's E-table is read through
v1 §7.3's qualification table (the gate audit's F1), unchanged here.

v2 SUPERSEDES, exactly:

- **v1 §3.A** (reasoning surface / the C-arc): its status table (rows
  4–14) and work items 1–10 are replaced by §2.1–§2.2 and §4.1–§4.3
  here. The C-arc gates (G-U, G-C5, G-C1, G-C2, G-P, G-C3, G-C4, G-OUT,
  G-PIN) remain RULED [USER] 2026-09-04 (RSP §5.4; confirmed 2026-09-05);
  this document changes no ruling, only what is claimed to follow from
  each (in particular, C3 yields a representation change, not an
  `EctxLanguage` instance — F3, already recorded in RSP §5.4's addendum).
- **v1 §5.1–§5.4** (dependency graph, recommended next wave, calendar
  points, decisions): replaced by §4 here. v1 §7.4's "revised next wave"
  table (items (1)–(6)) is folded into §4.3 and superseded by it; its
  Gates A–D framing is KEPT as the frame.
- **RSP §5.1's C-arc sequence** (which v1 §6.2 named authoritative) is
  superseded by §4.1 here ONLY in what it says about I5 and the pin (I5
  is the OUTPUT of Gate A, sized after it — already RSP §5.4's
  2026-09-05 addendum); the B7 → C1 → P → C3 order stands.
- **v1 §6.2's sentence "This document supersedes nothing"** does not
  describe v2: v2 supersedes the items above and nothing else.

Not superseded and still binding: the charter (`CLAUDE.md`), the
architecture rules, the doctrine, the F10 ruling (the relation and the
coherence proofs live HERE; Iris resources, WP rules, program proofs,
tactics and ghost state are the customer's), the split plan's 2026-09-05
addendum (extraction WITHDRAWN), and every [USER] ruling recorded in
`docs/2026-08-31_qrow-rulings.md`, `docs/assessment/decisions-2026-08-31.md`
and the design notes' §0s.

---

## 1. The target, precisely: a RefinedC-like layer for Go over GoLean

### 1.1 What RefinedC is and how its layers stack

Stated from the author's knowledge of the published work; the local
RefinedC pin the A2 note recorded (`25f706d417df2b18b23c5cbadde46468c1b1262c`,
`docs/2026-09-05_iris-customer-design.md` "Reference decisions") was not
re-read for this document.

**RefinedC** — Sammler, Lepigre, Krebbers, Memarian, Dreyer, Garg,
*RefinedC: Automating the Foundational Verification of C Code with
Refined Ownership Types*, PLDI 2021. Four layers, bottom-up:

1. **Caesium** — an operational semantics of (a large fragment of) C in
   Coq: expressions and statements, a byte-level memory model with
   allocation identities, small-step reduction with evaluation contexts,
   and an Iris `language` instance (with evaluation contexts, so Iris's
   generic `wp_bind` applies). Caesium is the ground truth every proof
   is about; nothing above it is trusted.
2. **Iris** — the separation logic instantiated over Caesium: `wp`,
   adequacy, ghost state (`gen_heap`-style points-to over Caesium's
   memory), invariants.
3. **The RefinedC type system** — types are Iris predicates on values;
   *refinement* types are indexed by mathematical values (`n @ int i32`:
   "an `i32` whose value is the integer `n`"), *ownership* types describe
   the heap (`&own`, `&shr`, `&frac`, `struct`, `array`, `optional`,
   `uninit`, …). Typing judgments for expressions, places and statements
   are separation-logic lemmas proved against Caesium's step rules and
   Iris's `wp`; function specifications are TYPE ANNOTATIONS written in
   C comments (`[[rc::parameters]]`, `[[rc::args]]`, `[[rc::returns]]`,
   `[[rc::requires]]`, `[[rc::ensures]]`) and parsed by a Cerberus-based
   frontend that also translates the C to Caesium.
4. **Lithium** — a goal-directed, deterministic (no-backtracking)
   proof-search engine — "a separation logic programming language" —
   whose programs are the typing rules; it interprets each typing
   judgment as a goal, applies rules by syntactic head, and hands
   arithmetic side conditions to solvers. Because Lithium runs inside
   Coq and every step is a lemma application, the result is
   **foundational**: the trusted base is Coq plus Caesium plus the
   statement of the theorem, never the automation.

The same recipe was re-run over a second language semantics in
**RefinedRust** (Gäher, Sammler, Jung, Krebbers, Dreyer, PLDI 2024:
refinement types for Rust over the Radium semantics, same Lithium
engine) — evidence that the recipe transfers when the semantics has the
right shape, and that the shape requirements are the interesting part.

What the recipe needs from the semantics, abstracted: (i) an Iris
`Language` instance whose steps are the semantics' steps (no second
evaluator); (ii) a memory whose ownership can be sliced (points-to at
the granularity the program's aliasing needs, with frame); (iii) a bind
rule, so sub-expressions are typed compositionally; (iv) a notion of
well-formed input so that "no rule applies" means a genuine type error,
not a semantics refusal; (v) adequacy connecting `wp` to the executable
verdict; and (vi) a stable pin, because the type system's soundness
proofs are stated against the semantics' definitions by name.

### 1.2 The Go analogue: what the "Caesium role" (GoLean) must export

GoLean plays Caesium. The F10 ruling ([USER] 2026-09-05, relayed;
`CLAUDE.md` "What this repo is") fixes the boundary: the transition
relation, its observations, the invariants stating its domain, and the
executable↔relation coherence proofs live HERE, co-designed with the
interpreter; Iris resources, WP rules, program proofs, tactics and
consumer ghost state are downstream. The thin customer adapter (an
iris-lean `Language` instance + toy facts) is an in-repo SPIKE outside
the default build. Item by item, what the layer above needs, what exists
at `da0a9c2c`, and what is owed (the owed items are §2's rows).

#### 1.2.1 The language instance (expr / val / state / step)

- **Exists.** `spikes/gate-a1/GateA1/Language.lean:24-28`: `instance :
  Language Config ExecState Empty Unit` with `PrimStep := Prim`, `Prim.step
  : Step c s c' s' → Prim (c, s) [] (c', s', [])` — the Prop-level
  sequential relation `Step` (`Machine.lean:4149`, 112 rules) IS the
  primitive step; values are `Unit` at `.next .stop` (results live in the
  store, RSP §1.7's `Val := Unit` decision, park lineage); no forks, no
  observations. `val_stuck` proved by `cases`. The executable tier enters
  only through `stepFn_sound` (`MachineSound.lean:172`) and
  `step_complete` (:506) — `pure_of_stepFn` (`Language.lean:33-46`)
  derives Iris pure steps from stream-oblivious executable steps.
- **The pool.** `StepM` (`Multi.lean:2406`, 7 rules) with `StepE`
  (:2371) for spawn; `stepMulti_sound`/`stepM_complete`
  (`MultiSound.lean:1172/1316`); the singleton-pool ≡ sequential machine
  bridge `execProg_single_eq_execStmt` (:812). No `Language` instance
  over the pool exists on main; the park's `LangC`/`LangD` attempts are
  §3's assets.
- **Owed.** After B7 the instance's `State` is `Store` (heap only) and
  the program is a section variable `ProgramCtx` (the B7 design,
  `docs/2026-09-06_b7-context-store-design.md`, "Concrete target API");
  the customer's `ContextEq` pin of five immutable `ExecState` fields
  (`spikes/iris-customer/README.md`, "Boundaries") disappears into the
  type. Observations as `Event := pick | access | out` in the step's
  observation list (RSP §1.14) need C1's emitted trace (1.2.2) and B8's
  `StepEvent.picks` (LANDED, G-U `e58eff5e`).

#### 1.2.2 The memory interface: points-to and frame (C1's `Mem` + trace)

- **Exists.** The dense heap `Heap := Array HeapCell` (A2), payload
  cells (A3), one root write `ExecState.updateCell`; the A2 customer's
  `Heap`/`Ghost` modules put an Iris `gen_heap` over it at WHOLE ROOT-CELL
  granularity (`spikes/iris-customer/GoLeanIris/{Heap,Ghost,Lifting}.lean`;
  README "Ownership is at whole root-cell granularity. Field/index paths
  live inside a cell"). The cross-root frame lemmas `storeLoc_root_frame`
  (`NPDRF.lean:465`) and `loadLoc_after_disjoint_store` (:511) are
  proved.
- **Missing.** Path-level (same-root, disjoint field/index) frame —
  NPDRF obstruction 6, unproved in any form; store/store commutation
  unproved. The sprint's C1 handoff records a pitfall a naive statement
  would hit: «raw StateWf bounds do not establish sibling path frames
  (byte array `[256,0]`, writing index 1 normalizes index 0)»
  (`docs/2026-09-06_typed-sprint-pause-state.md:261-263`) — normalization
  at the cell's declared type is a same-cell effect, so the frame lemma
  must be stated at the normalized-value level or over typed cells, not
  raw bytes. The footprint is a TABLE beside the semantics
  (`Race.lean:1532 stepAccesses`, 17 arms over `Config` shapes) whose
  agreement with `loadLoc`/`storeLoc` is a "lockstep obligation" nobody
  has (RSP §2 G4); C1 (RULED G-C1) makes the footprint an EMISSION so the
  detector is a fold over the trace and points-to can be keyed like the
  detector (`ShadowKey`, `Race.lean:336`; RSP §1.14 (3)).
- **What a RefinedGo needs from it.** `own_struct`/`own_slice`/`own_map`
  as iterated conjunctions over leaf keys; the frame rule as
  `ShadowKey.overlap = false → disjoint`; the two `Mem` lemmas of RSP
  §1.2 as the ONLY semantic input to the ghost-heap construction (G-REPR
  route (b), the park's "big design unit").

#### 1.2.3 Bind/frame laws, or an honest admissible-context class (F3)

- **The fact.** `recoverResult` reads the continuation: appending a
  frame below an ordinary frame changes both the value `recover()`
  returns and the continuation (gate audit F3, reproduced as
  kernel-checked counterexamples in `spikes/gate-a1/GateA1/Counterexamples.lean`
  and the Iris-free `Tests/InterfaceContract.lean`). So `fill K` is not
  a `Language.Context` for the pinned iris-lean, and `Cont := List
  Frame` (C3, RULED) will not make it one. The park's `wp_plug_bind`
  (§3) proved bind with three premises; its `hdrain` premise is FALSE
  at drain sites with ≥ 2 live defers (revival guide, "Named owed row").
- **Exists.** The route the audit allowed and the sprint took: a plain
  `Language` without `EctxLanguage`, with continuation-EXPLICIT rules —
  `pure_recover (env) (k) : PurePrimStep (Config.evalE .recoverCall env
  k) (.retV (recoverResult k).1 (recoverResult k).2)` and `wp_recover`
  (`spikes/gate-a1/GateA1/Language.lean:53-75`); the A2 customer's
  `wp_call`/`wp_frame_result`/`wp_store_cell`/`wp_initialize` and the
  `Call`/`Unwind`/`Return`/`Shared*` rules (L1) all carry `k`. This is
  correct and honest (auditor B, v1 §7.8.5: «made irrelevant by
  parameterising every rule on `k`. That is the correct design»). It is
  also exactly what a Lithium-style engine does NOT want: RefinedC types
  sub-expressions through a generic bind.
- **Owed (statement, not yet proposed anywhere as a definition).** An
  `Admissible : Cont → Prop` class of contexts (candidate: no
  `panicResumeK`/resume marker in the appended tail, so `recoverResult
  (k ++ K) = recoverResult k`; the exact class is the spike's to find)
  with `step_fill_adm : Admissible K → Step c σ c' σ' → Step (fill K c) σ
  (fill K c') σ'` and its inverse, PROVED for every rule; OR a
  customer-side bind lemma with the class as premise (the park's shape,
  premises re-derived, not ported). Either way the LAWS are GoLean's to
  state and prove (F10: coherence laws live here); the WP-level bind is
  the customer's. Worked examples the audit demands before any claim:
  nested defer/recover, labelled control flow, frame-local allocation.

#### 1.2.4 Typed admission (F5)

- **Exists.** Two profiles with sound-AND-complete checkers over
  independently defined judgments, preservation over the Prop-level
  relation, progress, and driver theorems: Boolean
  (`GoLean/GoCore/BooleanTyping.lean:336 TypedBooleanAdmission`, `:392
  checkTypedBoolean_iff`; `BooleanPreservation.lean Inv.step`;
  `BooleanSafety.lean Inv.reachable_progress`; `BooleanPool.lean:175
  runProgramPool_no_refusal`) and Recovery (`RecoveryAdmission.lean:83/
  166 checkRecovery_iff`; `RecoveryInvariant.lean Inv.step`;
  `RecoveryTerminal.lean Inv.run_classified` with FOUR disjuncts and
  `*_refusal_named` — the only refusal an admitted recovery program
  reaches is the NAMED invalid-UTF-8-first-line abort, D5). Landed L1
  `f70ea4bf` + L3 `a6a068ce`/`25c665b7`/`29f77b43`. Also the A3a
  syntactic checker `Admission.lean:125 checkBoolean_iff`.
- **Missing.** The machine-wide programme the audit named: `WireWellFormed`
  (decoding yields the structural invariants), `ProgramWellTyped`
  (heap/operand types, signatures, method metadata, normalization —
  `StateWf` is `ExecState.locSup σ ≤ σ.nextAddr` only, `StateWf.lean:645-646`,
  and `decide (StateWf illTyped) = true` still holds at this tip), valid
  entry/arguments, a feature/extern support contract, preservation on
  the WHOLE machine, and the strongest refusal-free result those premises
  justify. The Boolean grammar has no calls, loops or ints; the recovery
  grammar adds direct/closure calls, defers, string panic, recover
  (`docs/2026-09-07_land-typed-core-proofs.md` states both exactly).
  Refusal markers still live INSIDE the IR (`Syntax.lean:304/319/530`,
  `Value.lean:585 Ty.unsupported`, `Syntax.lean:76 TypeDef.opaqueDecl`) —
  I1's job; the declaration wire (L1b) did not land (§2.6).
- **Why a RefinedGo needs this first.** In RefinedC "no typing rule
  applies" is a type error because Caesium is total on well-formed
  programs. Here a `Refusal` is a stuck non-value in the Iris instance
  (`spikes/gate-a1/GateA1/Language.lean:5-8`), so every `NotStuck` proof
  must exclude refusals — i.e. carry the admission predicate. Typed
  admission is the type system's DOMAIN, not an optional extra.

#### 1.2.5 Latitude: streams, membership, what the logic may assume

- **The design (RULED by the doctrine, [USER] 2026-08-12; `Step` is
  choice-free).** Nondeterminism is rule multiplicity in `Step`/`StepM`
  (demonic); the executable realizes ONE derivation per stream `ch :
  Choices` and emits its labelled picks (`PickRecord`, `StepEvent.picks`;
  consumption rule "pop iff bound ≥ 2" at every site, G-U LANDED
  `e58eff5e`). Thirteen sites (§0.4). `Fair` is a DOWNSTREAM hypothesis
  over streams/traces, never a machine filter ([USER] 2026-09-02, the
  doctrine's "Scheduling and fairness" paragraph; `docs/2026-08-11_essence-of-go-doctrine.md:37-59`);
  no `Fair` predicate exists on any branch (`:156-165`).
- **What the layer may assume.** Exactly the relation. A RefinedGo
  typing rule is sound only if it holds for EVERY `Step` derivation:
  no rule may assume a map-iteration order (E9 → specs quotiented to
  sets, as the cedar refinement target already does, v1 §3.H), a
  `[]byte(s)` capacity (R3), a scheduler choice, or a panic-order
  realization gc happens to make (E3/E4, E13's `unseqPanic`). Where the
  logic wants a fixed stream (a deterministic run), it quantifies `∀ ch`
  (the typed theorems do) or uses `step_det_of_choiceFree` (RSP §1.4 —
  still NOT on main; a 20-line corollary of B8's `seqConsumption`
  promised at G12, unproved).
- **Membership as the assumption surface.** The corpus's membership
  rows (`members=`, 140 PASS at stage membership) are the differential
  EVIDENCE that gc's realizations ∈ the modeled set; they certify the
  lower bound, never the width (doctrine `:22-25`). For the customer
  they are the SPECIFICATION of what may be assumed: a spec stronger
  than the set is a spec about gc, not about Go. The latitude census's
  (b)/(b-n) pins (24 rows, §2.3) are places where the machine is
  deliberately NARROWER than Go; a consumer theorem that relies on one
  inherits a re-envelope obligation and must say so (the F1 release
  predicate 3, v1 §7.3).
- **Two-outcome demonstrations that exist.** Untyped:
  `Tests/InterfaceContract.lean:183 two_choice_pool_bridge` (the
  `.unseqPanic` site under `[0]`/`[1]`). Typed: the recovery profile's
  abort draws `repanicCollapse` (`Tests/RecoveryTerminal.lean
  equal_repanic_two_members_at_frontier`, L3) — the first TYPED
  two-outcome driver demonstration; every other typed step is
  choice-free (`Control.no_seq_consumption`).

#### 1.2.6 Observations: readout, output, terminals, panics

- **Exists.** `Refusal | unsupported | stuck | internal` and `Terminal |
  panic | fatal | deadlock | raceDetected` (`Value.lean:199-`, A1); output
  as a per-step EVENT (`StepEvent.out`, G-OUT RULED and LANDED
  2026-09-04) folded by the driver; the whole-program observation
  bridge `Pool.observation_iff` (`ProgramTrace.lean:75`, ∃ fuel ch on
  both sides; refusal and exhaustion are NOT observations); the abort
  observer (`runConfigWithAbort`, `*_erasure`, `*_witness`, L3) whose
  record carries the payload's FIRST LINE (`stringFirstLine?`) and the
  `repanicCollapse` member; the same-run crash channel on the oracle
  side (L4) with authenticated abort classification (D4 RATIFIED by the
  L4 merge sign-off, relayed).
- **Scope, stated.** The observation contract compares the abort
  message's first line; the TAIL is unmodelled and unobserved on both
  sides by record (FR-32, `docs/language-coverage-ledger.md` §8w; v1
  §7.8.6 item 3). An invalid-UTF-8 first line is REFUSED by name (D5(i),
  RULED at round 24). `EnumSpec`'s `Obs` is still output-free (TODO.md
  G-OUT owed). A terminal `panic` is a Go OBSERVATION in the driver but
  a stuck non-value in the bare `Language` (1.2.4).
- **What a RefinedGo needs.** Panics as observations the postcondition
  can name (a RefinedGo "may panic with payload p" type), the readout
  through owned result cells (A2's `Readout`), output as a trace
  predicate. All three exist at the driver level; the Iris-level `Obs`
  type (RSP §1.14's `Event`) is not instantiated.

#### 1.2.7 Concurrency: scheduler reduction and go_mem (F4)

- **Exists.** Registry-point scheduling (`schedPick` at designated
  boundaries; C5's per-thread `boundary` flag); the full-interleaving
  relation `StepMFine` (`NPDRF.lean:192`) with `stepM_le_stepMFine`
  PROVED (:327 — coarse ⊆ fine); `RacyFine` (:418) over the shared
  footprint; the segment-level happens-before detector (`Race.lean`,
  four access kinds since BUG-080) following go_mem exactly where TSan
  and go_mem disagree (Q-U4RESIDUAL option (A), [USER] 2026-09-02; the
  UNION rule, BUG-084 designed reds); the detector campaign (364 in-scope
  rows × 10 `-race` runs, HOLE 0 — `docs/2026-09-02_detector-soundness.md`).
- **Missing (F4).** `NPDRFReduction` (`NPDRF.lean:438`) is a DRAFT
  `def`, REFUTABLE AS WRITTEN (obstruction 4: main-exit discards other
  goroutines mid-flight, so `ReachesMFine → ReachesM` fails on race-free
  programs); its weakening is a reviewed decision that has not been
  made; nothing may cite it. The movers are cross-root only. HOLE 0 is a
  sampled result, not go_mem exactness. BUG-002 (expression-step
  atomicity coarser than Go) is a LATENT Prop-level unsoundness for
  concurrent programs; U2 (`len`/`cap` on channels record nothing) and
  BUG-041 (over-refusal on dynamic-index reads) are open detector rows.
  No reference step/event model at Go's access granularity exists — the
  audit's first ask.
- **What a concurrent RefinedGo needs.** A per-thread `Language` (the
  park's `LangD` shape: pairing/wake rules ∃-quantify the partner) or a
  pool-level instance; the DRF-SC transfer stated as an explicit
  ASSUMPTION until the reduction is proved for the observable
  projection; race-freedom as a typing consequence (the detector's fold
  over the trace, RSP §1.14 (2)). Until F4 closes, a concurrent pin is a
  knowingly conditional contract (Gate D).

#### 1.2.8 The pin ceremony

G-PIN is RULED ([USER] 2026-09-04, RSP §5.4: the customer pins a SHA
whose `GoLean/Interface.lean` matches the interface document name for
name; a §1-preserving refactor is not a pin move). Its CRITERIA are to
be REVISED to Gate D's exit — sequential and concurrent pins offered
SEPARATELY, each recording source/profile/toolchain fingerprints, exact
observation equivalence, supported domains, proved bridges, remaining
assumptions, live consumer tests and fresh certification (gate audit
Gate D; RSP §5.4 2026-09-05 addendum). The revised criteria are OWED by
the Gate A spike and are a [USER] decision when posed (PENDING). Today
no interface document has its final shape; `Interface.lean` is
"experimental" by its own docstring; no pin is offered.

**Today vs owed, in one table** (statuses per §0.3; rows detailed in §2):

| export | today (LANDED) | owed |
|---|---|---|
| language instance | bare sequential `Language` over `Step` (spike) | pool instance; `Store`/`ProgramCtx` after B7; `Event` observations after C1 |
| memory + frame | dense heap; whole-cell gen_heap (spike); cross-root movers | C1 `Mem` + trace; path-level frame; `ShadowKey` points-to |
| bind | continuation-explicit rules (spike/L1) | admissible context class + laws, or bind-lemma premises |
| typed admission | Boolean + Recovery profiles, sound/complete, preserved | `WireWellFormed`/`ProgramWellTyped`/entry/support; machine-wide preservation; I1 |
| latitude | choice-free relation; 13 sites; picks labelled; two two-outcome demos | `step_det_of_choiceFree`; `Event.pick` in the instance |
| observations | driver-level bridges (∃ fuel ch both sides); abort observer; first-line scope | Iris-level `Obs`; FR-32 tail; `EnumSpec.Obs` output |
| concurrency | `StepM`/`StepMFine`; coarse ⊆ fine; detector; HOLE 0 sampled | reduction statement repair + proof or explicit assumption; reference event model; BUG-002 |
| pin | G-PIN ruled; criteria to be revised | Gate D criteria (PENDING [USER]); interface document with final shape |

### 1.3 What the customer builds (and this repo does not)

Per the F10 ruling and the charter, the following are the customer's
(the iris-lean layer, "which we won't build, that's a customer" — [USER]
2026-09-04, relayed), and this document plans none of it beyond the
thin adapter spike:

- **The type system.** Refinement types over `GoValue` (`n @ int64`,
  `s @ string`, `b @ bool`, …); ownership types for Go's aggregates —
  `own_struct` (fields as leaf points-to), `own_slice ptr len cap`
  (ownership of the backing array's window; aliasing between slices of
  one array is Go's central ownership problem), `own_map` (a finite map
  with iteration-order latitude, so specs quotient to sets), pointers
  (`&own`, shared/fractional after `sync`), interface values (dynamic
  type + payload; typed nils), function values and closures (captured
  cells), channels (protocol types — Actris-style, or the park's
  `channel-logic` material, §3), goroutines (fork + join ghost state),
  `defer`/`recover` (continuation-sensitive rules; the panic chain as a
  resource or as a mode of the postcondition). Each is a family of
  Iris lemmas proved against `Step`/`StepM` through the interface.
- **The automation.** A Lithium-like goal-directed engine in Lean
  (tactic + `DiscrTree` of registered typing rules; the park's `go_walk`
  is the precedent, §3). Foundational: every step a lemma application;
  side conditions to `omega`/`decide`/`simp`.
- **Program proofs.** The corpus members (the park's 25-member gallery
  as a re-target), the cedar-go refinement (`cedarGo_refines`, v1 §3.H),
  raft components — each consuming ONLY the interface (the statement-TCB
  deletion test, RSP §1.13; not met today — the A2 customer «still uses
  machine internals and unfolds operations», `spikes/iris-customer/README.md`).
- **Their own gates.** Axiom audits, the designated-theorem list, the
  judge/comparator apparatus (all parked, §3), a re-pin runbook.

What this repo DOES owe the customer beyond definitions and bridge
theorems: the coherence laws (1.2.3), the domain predicates (1.2.4), the
frame lemmas (1.2.2), the reduction or its explicit assumption (1.2.7),
and a pin whose meaning is written down.

### 1.4 What "faithful" forbids, and what it requires of the logic

The semantics is «the weakest machine Go permits, all latitude
included» (`CLAUDE.md`); differential testing is the LOWER bound;
spec/docs/corpus argue the upper (doctrine). Consequences for the
layering, each with the rule it comes from:

**Forbidden.**
- **gc-pinning latitude and presenting it as fidelity** — «no record may
  present gc-conformance at a latitude point as correctness»
  (doctrine `:99-107`). For the logic: no typing rule or program proof
  may assume a (b)-pinned realization without naming the pin and its
  re-envelope obligation.
- **Shims and compensating behaviour** — «fix and go red rather than
  preserve wrong or over-wide behaviour; no compensating shim bodies»
  ([USER] 2026-09-03, memory `break-incorrect-behaviour`; applied in
  `docs/2026-09-05_fr19-bug097-design.md`). For the logic: a rule that
  is provable only because the machine is WRONG in a convenient way is a
  bug report, not a lemma (the sprint's `string-member` lane was retired
  on exactly this: five of nine PASS rows demonstrably divergent from gc,
  auditor A R1).
- **A second semantics.** No proof-side evaluator with semantic
  authority (cerberus-lean pitfall L3, RSP §6; the park's `Sym` mirror
  is the acceptable form — it REFINES `stepFn` by theorem and quits
  rather than diverges). The driver `run` is a defined function of the
  relation + fuel + stream, not a second semantics (RSP §1.6's contract
  sentence, which the F2 correction keeps).
- **Hiding a semantic choice in evaluator recursion** (`CLAUDE.md`
  doctrine; A-R2 at the landing: the `[recovered, repanicked]` collapse
  was a hard-coded member until L3 put it on the tape).

**Required of the logic.**
- **Quantification over streams.** Adequacy and refinement statements
  range over `∀ ch` (or over the relation's derivations); a fixed-stream
  statement is a statement about one run and must say so
  (`Interface.lean`'s docstring does; the F2 correction separates the
  two bridge shapes).
- **Membership as the assumption surface** (1.2.5).
- **Refusals as visible reds, never absorbed.** `Refusal` is stuck in
  the instance; refusal-freedom is a THEOREM conditioned on admission
  (`*_refusal_named`), never an axiom; an `unsupported`/`stuck` outcome
  never counts as a pass (`CLAUDE.md`).
- **The allocation-succeeding rider** ([USER] 2026-08-31, fidelity
  decision 5(a); doctrine register #7): every consumer-facing claim is
  scoped to allocation-succeeding runs; the heap is unbounded here.
- **Pointer equality is the only address observation** (doctrine
  register #6): any customer construct that would observe addresses
  (`%p`, ordering, `unsafe` round-trips) re-opens the allocator-quotient
  entry whose theorem lives only on the park branch.
- **Exact scope on every theorem** — fuel, stream, profile, terminal
  policy, output scope (first line), platform (`gcAmd64` vs `∀ p`) —
  the charter's honest-measurement rule applied to statements.

---

## 2. Exactly what is missing — the checklist

### 2.0 Derivation and columns

Derived from: the gate audit's E1–E13 qualification table and Gates
A–D (`docs/2026-09-05_project-gate-audit.md`; v1 §7.3/§7.4); RSP §1's
items against what landed (v1 §7.8.5's F2/F3/F5 answer table, auditor B
verbatim, and "what the landed tree realizes"); the sprint outcome
(handoff, "Required outcomes — FINAL status"; v1 §7.8.6 owed chunks);
the C-arc gates (RSP §5.4); TODO.md's C-arc section; `docs/BUGS.md` at
the tip. Columns: **owed** = the statement/definition/artifact that
would close the row; **dep** = what must land first; **size** = S/M/L/XL
([AGENT] guesses; where v1 gave sessions they are quoted as
REFACTORING estimates only — v1 §7.4 withdrew them as assurance
estimates); **who** = mainline (a worker lane under the merge protocol)
/ Codex (deep theorem work with a fixed statement, §4.4) / customer
(downstream) / design (a note before any lane); **status** per §0.3.

### 2.1 Contract items (Gate A)

| # | item | owed | dep | size | who | status | evidence |
|---|---|---|---|---|---|---|---|
| A1 | **F2 — the driver↔relation bridges, relation→driver direction** | `∀` labelled `StepsM` trace reaching an observation, `∃ ch fuel, run … = .obs o` (the converse of `Trace.erase`), for the Prop-level `Step`/`StepM`, with initialization, terminal priority, main-exit, output and fuel accounted; a TYPED two-choice bridge | none for the statement; B7 for a stable state type | M | Codex (after B7's representation settles — "after pinning" in the brief's sense) | **PARTIAL — the driver-side bridges are LANDED** (`GoLean/GoCore/Trace.lean:16 iter_iff_trace`, `:54 run_ok_iff`; `PoolTrace.lean:71 run_iff`; `ProgramTrace.lean:26 program_run_iff`, `:53 exists_program_run_iff`, `:75 observation_iff`, all `4919b05a`); `two_choice_pool_bridge` `Tests/InterfaceContract.lean:183`. The relation→driver direction is OWED: «`Trace.erase` yields unlabelled `Steps`; no converse to erasure is supplied» (`Interface.lean` docstring); `ProgramRun`/`Pool.Run` are mirrors of the DRIVER, not `Machine.Step` (auditor B) | v1 §7.8.5; `docs/2026-09-05_gate-a1-contract.md` "Sequential prefixes" |
| A2 | **F3 — the admissible context class and its laws** | `def Admissible (K : Cont) : Prop`; `step_fill_adm`, `step_fill_inv_adm`, `fill_val` under `Admissible`, proved for all 112 rules; the recover counterexample as the first negative test; worked examples (nested defer/recover, labelled control, frame-local allocation) | none for truth (statable over today's `Cont`); C3 for ergonomics | M–L | design (the class) + Codex (the laws) | **OWED; no definition proposed in any tracked file.** The bare-`Language` route is LANDED (spike) and honest; `EctxLanguage` is not claimed anywhere (`spikes/gate-a1/README.md`, `spikes/iris-customer/README.md:85`) | gate audit F3; RSP §1.7 annotation; v1 §7.8.5 |
| A3 | **F5 — typed admission beyond two profiles** | `WireWellFormed` (decoder yields it), `ProgramWellTyped` (heap/operand types, signatures, method metadata, normalization), valid entry/arguments, a support contract (feature/extern/profile, incl. reachable quarantined declarations), `Inv.step` preservation on the WHOLE machine for the named profile, `run_refusal_free` (or `*_refusal_named`) for it | the profile NAMED (PENDING [USER], F1 predicate 2); I1 (refusal markers out of the IR); B7 | XL | design (the type system) + Codex (preservation) | **PARTIAL** — Boolean and Recovery profiles LANDED (L1 `f70ea4bf`, L3); `StateWf illTyped` still decides `true`; `Accepted P` as one Prop still OWED (v1 §3.A "Owed"); allocation normalization and the C2 bound theorem OWED | v1 §7.8.5 F5 row; `docs/2026-09-05_gate-a1-contract.md` "Proposed interface and admission boundary" table |
| A4 | **`step_det_of_choiceFree`** (RSP §1.4) | `seqConsumption σ c = none → Step c σ c₁ σ₁ → Step c σ c₂ σ₂ → c₁ = c₂ ∧ σ₁ = σ₂` | B8 (LANDED) | S | Codex | **OWED, not on main** (`git grep step_det GoLean/` → nothing) — the sequential refinement's "some run → every run" lemma | RSP §2 G12, §3.I3 |
| A5 | **`GoLean/Interface.lean`'s honest state** | an interface DOCUMENT with a final §1 shape (the pin's referent), `Interface.lean` re-exporting exactly its names | A1–A4, B7, C1 | — | mainline | **EXPERIMENTAL facade.** 18 imports, no definitions; its docstring: «These are correspondence theorems about the current machine. They do not establish Go frontend correctness, termination, refusal freedom, scheduler completeness, generic context laws or Iris adequacy» and «The underlying `GoCore` and `GoCore.Machine` types remain representation dependent. This facade is experimental: B7, C1 and the composition work may change that representation». Gate C's "no unfolding of internals" exit is NOT met (`spikes/iris-customer/README.md:101`) | `GoLean/Interface.lean`; `docs/2026-09-05_semantic-interface-design.md` "Remaining representation dependencies" |
| A6 | **The observation contract's scope** | FR-32: compare the whole abort message region (gc's `printindented` TAB-after-LF un-wrapped; machine renders the full payload) at L4's byte view; the Iris-level `Obs`/`Event` type; `EnumSpec.Obs` carrying output | L4 harness (LANDED); C1 for `Event.access` | M | mainline | **OWED** (v1 §7.8.6 item 3; TODO.md G-OUT owed). First-line scope is LANDED and stated (L3); D5(i) RULED | `docs/2026-09-07_land-panic-text-tape.md`; ledger §8w |
| A7 | **The type-descriptor decision** (F11) | `typeDesc` over `Ty` vs `TypeIdx`: a small type/descriptor algebra covering builtin, unnamed composite, recursive, defined and interface types; addressability tests | C2 (LANDED) | S–M | design | **PENDING [USER]** (the HOLD on G6 T1 is [AGENT]-proposed; T1 is RULED, so the hold needs confirmation) | v1 §7.2 F11; §7.4 item (4) |
| A8 | **Gate D pin criteria** | the revised G-PIN criteria: sequential and concurrent offers separate, each with fingerprints, exact observation equivalence, supported domains, proved bridges, remaining assumptions, live consumer tests, fresh certification | A1–A3 for the sequential offer | S (to write) | design → PENDING [USER] | **OWED by the Gate A spike; PENDING [USER] when posed** | gate audit Gate D; RSP §5.4 addendum |

### 2.2 Representation items (the C-arc; every gate RULED, RSP §5.4)

| # | item | owed | dep | size | who | status | evidence |
|---|---|---|---|---|---|---|---|
| R1 | **B7 `ProgramCtx`/`Store`** | `ProgramCtx {program, platform}` immutable; `Store {heap}`; `stepFn ctx s c ch`, `Step ctx`, drivers threaded; `htypes` hypotheses deleted; `Platform` threaded (A5's deferral, `Platform.lean:17-21`); zero baseline drift; whole-corpus trace byte-identical; both customers rebuilt | wave (iii) (LANDED) | 2 sessions (v1, refactoring) — the sprint's attempt suggests more | mainline | **design LANDED** (`docs/2026-09-06_b7-context-store-design.md`, L1); **implementation IN FLIGHT on `typed-context-store` @ `ca1e01d5`** — unreviewed by the landing; its V1 kernel-sharing completeness claim WITHDRAWN, V2 uncommitted (`docs/2026-09-06_typed-sprint-pause-state.md:132-138`); `grep ProgramCtx GoLean/` on main → one deferral comment | v1 §7.8.4 O4; §3 asset T1 |
| R2 | **C1 `Mem` + emitted access trace (G-C1)** | `Mem.alloc/load/store/peek/…` emitting `Access`; `accesses_eq_stepAccesses` arm by arm (any failing arm a red-first detector BUG); `stepAccesses` retired; `RacyFine`/`footprintsConflict` over traces; `Mem.load_after_disjoint_store`, `Mem.store_store_disjoint` at PATH level (the sibling-normalization pitfall stated); detector re-run HOLE 0 | B7 | 4–6 sessions (v1, refactoring) | mainline (+ Codex for the two frame lemmas once `Mem` exists) | **RULED [USER] 2026-09-04; NOT STARTED.** The sprint's handoff is a tracked DRAFT with root corrections owed (`docs/2026-09-06_c1-contract-handoff.md`; pause-state `:254-267`) | RSP §3.C1; v1 §3.A item 2 |
| R3 | **P native method promotion (G-P)** | frontend stops synthesizing wrappers; core resolves selectors through the embedding chain; `Func.wrapper` + four consumers deleted; twin pin moves; BUG-087 family → chain-depth ≥ 1 | C1 | 3–4 sessions (v1) | mainline | RULED; NOT STARTED | RSP §3.P |
| R4 | **C3 `Cont := List Frame` (G-C3)** | `Config := Mode × Cont`, `fill` is append, `@[match_pattern]` views; definitional preservation; the `.probeK` traveller arms become explicit (owed since e13-b) | B4 (LANDED), P | 3–4 sessions, double if views bite (v1 §5.5) | mainline | RULED as a REPRESENTATION change; the `EctxLanguage` claim WITHDRAWN (F3). NOT STARTED | RSP §3.C3; §5.4 addendum |
| R5 | **C4 block-scoped allocation (G-C4)** | `Stmt.initialization` deleted; preserving up to heap isomorphism; re-pin with reason | B6 | 2 sessions + re-pin | mainline | RULED; NOT STARTED | RSP §3.C4 |
| R6 | **B6 `VarId := Nat`** | no `String` scope keys in the core; twin pin moves | — | 2–3 sessions | mainline | PROPOSED; NOT STARTED (its wave slot is a coordinator/[USER] call, v1 §7.4) | RSP §2 G8 |
| R7 | **I1 — refusal markers out of the IR; the declaration wire** | delete `Expr/Assignee/Stmt.unsupported` (`Syntax.lean:304/319/530`), `Ty.unsupported` (`Value.lean:585`), `TypeDef.opaqueDecl` (`Syntax.lean:76`) → `ProgramCtx` facts; the declaration wire (`declaration.go`, `NativeDeclaration`/`StrictJsonParse`, `scripts/check-declarations` with A-R11/A-R12 fixed) | B7 | M | mainline | **PARTIAL** — `GoLean/GoCore/Declaration.lean` + `spikes/i1-declarations/` LANDED (L1); the wire (plan L1b, 16 of 19 paths) OWED; runtime V2 IN FLIGHT on `typed-i1-envelope` @ `3d49e9e9` / `typed-i1-declarations` @ `380753b9` | v1 §7.8.3, §7.8.6 item 7 |
| R8 | **Owed small items from landed C-arc steps** | `Park` as a type (~150 sites, 14 files); bound-irrelevance theorem (`types.WellFounded → i < b → i < b' → defaultValueAt types b i = defaultValueAt types b' i`); `Accepted P` as one Prop; `itersNormalized` deletion (216 refs); program-text `locSup` deletion; `EnumSpec.Obs` output; `canonicalSlot0` docstring for `repanicCollapse` (still "under BUG-087's ruling") | — | S each | mainline (bound-irrelevance: Codex) | OWED | v1 §3.A "Owed"; v1 §7.8.6 item 5 |
| R9 | **B5 `Chan` module** | equational module; may follow the pin | — | 1–2 sessions | mainline | PROPOSED, optional | RSP §5.1 row 11 |

**Addendum 2026-09-08 ([AGENT], `land/i1-declarations`) — R7/L1b.**
The declaration producer, strict byte parser, decoder and dedicated CI gate
are implemented on this branch, with A-R11 fixture-pin enforcement, A-R12
query isolation and the named-constraint refusal correction. The full
3,654-row differential and 394-row negative baselines match on the frozen
candidate. This is branch implementation, pending committed-tip certification,
the mandatory audit ask and explicit merge sign-off; no main-side LANDED
status is claimed. Production I1 integration and refusal-marker removal still
depend on B7. Scope and fresh evidence:
[landing record](2026-09-08_i1-declaration-landing.md).

**Completion addendum 2026-09-08 ([AGENT], `land/i1-declarations`).**
Clean implementation commit `3e393be5` passed `scripts/capped scripts/ci
--slow`, actual exit 0: 3,654 executable rows and 394 negative rows match
the baselines, and fresh slow enumeration reproduces the certified set and
wire exactly. The mandatory independent-audit ask is posed, its disposition
pending; explicit merge sign-off is still required. L1b is branch-complete,
with a documentation-only completion record following the validated source.
The R7 main status and remaining production I1 scope do not change until
their respective landings.

**Review addendum 2026-09-08 ([AGENT], `land/i1-declarations`).**
The coordinator's independent review of `8b4a1aec` returned FIX-FIRST.
[USER] then authorized fixes and a pause for a second review. The
[review response](2026-09-08_i1-review-response.md) records R1–R7/R11 fixes
and R8–R10 scope/accounting/remaining pin-policy limitations. This supersedes
the pending first-audit disposition above; L1b remains unmerged, with fresh
correction gates and the second review owed before sign-off.

**Correction completion addendum 2026-09-08 ([AGENT], `land/i1-declarations`).**
Fixes at `061904f0` passed the candidate and clean committed-source full
`--diff` gates, actual exit 0, with 3,654 executable and 394 negative rows
matching their baselines. The linked review response records each disposition
and the evidence. The branch is paused for the user-directed second review;
L1b is still unmerged and production I1 remains outstanding.

**Second-review addendum 2026-09-08 ([AGENT], `land/i1-declarations`).**
The [coordinator's second review](evidence/2026-09-08_i1-declarations/coordinator-review-update.md)
at `4eb2ab1c` is MERGE-CLEAN, with R1–R7/R11 independently closed and a
clean full `--diff` gate PASS (3,654 executable / 394 negative rows,
no baseline regression). [USER] authorized fixing its remaining minor
issue and landing on main. Its sole required change, N5, is the owed row
below; the existing pin is unchanged. R7's production scope still includes
declaration-set/nominal-inventory closure and source provenance. Review N1
adds a named residual there: the decoder accepts distinct-package private
fields such as `struct{ p.t; q.t }`, matching `go/types` identity but wider
than checked source; resolve that acceptance boundary before a production
consumer. This records a follow-up, not source-validity certification.

| # | item | owed | dep | size | who | status | evidence |
|---|---|---|---|---|---|---|---|
| R10 | **Declaration fixture re-pin authorization guard** | gate changes to `Tests/declaration-fixture/SHA256SUMS` on an explicit re-pin record with written reason, fresh fixture output and review of the changed identity matrix; reject an unrecorded producer-plus-pin change in a negative control | L1b; define the re-pin record contract | S | mainline, W3 follow-up before the first declaration fixture re-pin | **OWED** — the current byte check detects producer drift but has no dedicated authorization guard | second review N5 / first review R10; `Tests/declaration-fixture/README.md`; [review response](2026-09-08_i1-review-response.md) |

**Landing addendum 2026-09-08 ([AGENT]) — R7/L1b.**
[USER] signed off the N5 fix and merge; main fast-forwarded from `ae9c8079`
to `960ee230`. **L1b is LANDED**: the separate declaration type producer,
strict parser/decoder and gate, including the reviewed corrections.
R7 overall remains **PARTIAL**: production I1 integration, declaration-set
closure and refusal-marker removal are outstanding. R10 remains **OWED**.
The [landing record](2026-09-08_i1-declaration-landing.md) binds the reviews,
unchanged runtime's clean full gate and fresh documentation checks to source.

### 2.3 Fidelity families, identity, open bugs (Gate B)

| # | item | owed | dep | size | who | status | evidence |
|---|---|---|---|---|---|---|---|
| B1 | **F6 — the evaluation-order family model** | a design note specifying expression evaluation as a dependency/ordering relation over value production, effects and failure; a bounded prototype (calls, receives, short-circuit, multiassign, mutation, multiple panics); generated interaction tests; ONE translation certificate; BUG-101's value axis and BUG-104 decided INSIDE it | none | L | design → mainline | **OWED (v1 §7.4 item (5a)); not started.** BUG-101 (2 rows) and BUG-104 (5 rows) open red-first; the E2/E12 value-axis gate is to be posed WITH the note | gate audit F6; v1 §3.D items 2–3 |
| B2 | **F7 — semantic identity metadata** | opaque/interned IDs with package/scope/instantiation structure; display separate; `keyPathHazard` and `TypeId.unqualified` parsing retired; C6 revisited (not ratified as-is); module-aware source manifest | none | M–L | design → mainline (frontend) | **OWED (v1 §7.4 item (5b)); not started.** FR-31/BUG-098 repaired on `fix/package-method-identity` (2026-09-09 [AGENT], awaiting review); broader identity design and C6 narrowing PENDING [USER] with the note | gate audit F7; v1 §3.B items 17–18 |
| B3 | **Open bugs at the tip — 17** (`awk '/^## BUG-/{h=$0} /^- Status: open/{print h}' docs/BUGS.md`) | each: a plan and a lane or queue slot; wrong answers → zero within the named profile | per bug | — | mainline | see the table below | `docs/BUGS.md` |

The 17 open entries by class (class = the heading's bracketed tag where
present, else [ANALYST]; line = entry start at `da0a9c2c`):

| BUG | line | class | area | one line | plan / slot |
|---|---|---|---|---|---|
| 002 | 3039 | latent Prop-level unsoundness | concurrency (Q-ATOMICITY) | expression-step atomicity coarser than Go | the F4 reference-granularity model (§2.5) |
| 004 | 2740 | rendering (2 (c)-pins + 3 D5 reds) | observer-terminal | boxing identity / defined-type payload rendering; invalid-UTF-8 first lines red by name | D5(ii) byte channel = its own arc; R-1 pin |
| 008 | 2452 | refusal of legal Go | frontend (wire identity) | imported named types have no wire TypeDef | FR-9 (raft path) |
| 041 | 981 | over-refusal (NARROWED) | detector | whole-cell reads for dynamic-index array reads | Q-RACEPATH residual; C1 |
| 061 | 37 | init-order latitude (L-011) | frontend | `staticinit` pruning under-approximates gc's; 11/26 flavours | **PENDING [USER]** L-011 ruling |
| 065 | 3693 | apparatus budget | enumerator | `worker-pool/sum` exceeds the dedup budget | reduction/DPOR lane |
| 090 | 5495 | PERFORMANCE | interpreter | assoc-list heap cost (A2 landed dense heap; re-measure OWED) | hygiene follow-up |
| 093 | 5633 | coverage | stdlib + float formatting | `print` residuals (float/complex, zero-operand, `$pkginit`) | FR-29 |
| 094 | 5680 | latitude (R7) | FloatBits | `Float64bits` of canonical NaN refuses | R7 re-envelope; §4.4 FloatBits item |
| 098 | BUGS.md entry | **FIXED on branch, awaiting review** (2026-09-09 [AGENT]) | frontend + decoder + core identity | I1 package/name identity through matching and distinct promoted function ids | FR-31; `docs/2026-09-08_method-identity-design.md`; broader B2 remains owed |
| 099 | 5991 | wrong-answer (observed) | interpreter/terminal | one synthetic `$runtime.Error` type for every recovered runtime error | **unowned** (Gate B: "give BUG-099 a concrete owner") |
| 100 | 6040 | designed (c)-pin | frontend | C6: function-local type as generic TYPE argument | ratification PENDING [USER] with B2's note |
| 101 | 6064 | wrong-answer at a forced VALUE point (red-first, 2 rows) | frontend + core eval order | E13 probe discards the early value | inside B1 |
| 102 | 6137 | designed reds (6 rows) | frontend | E13 (b) boundary refusals | retire as probes widen |
| 104 | 6273 | wrong-answer, lower-bound violation (red-first, 5 rows) | frontend eval order | compound-target temp panics before RHS events | `safeExpr`-style decomposition; inside B1 |
| 106 | 6386 | apparatus (terminal classification) | observer | fatal during panic unwinding cannot be authenticated | owed with the fd-channel chunk |
| 107 | 6451 | apparatus (terminal classification) | observer | pre-`main` abort has no crash-channel acknowledgement (4 rows) | **PENDING [USER]** option (a)/(b)/(c) |

Wrong answers OPEN (F1's predicate 2 counts these): BUG-099, BUG-101,
BUG-104. BUG-098 is fixed on `fix/package-method-identity`, awaiting the
user’s adversarial review (2026-09-09 [AGENT]); no merge is claimed. The untriaged ratchet
(`scripts/check-bugs.sh`) is a separate counter that stays 0/0 for
wrong-answer; its blind spot (a guard moves a row out of its filter) is
v1 §2.6/§3.G; the guarded-wrong-answer marker is PENDING [USER].

Latitude pins that a consumer theorem inherits (the (b)/(b-n) rows of
`docs/2026-08-11_latitude-inventory.md` §10, 24 in all): (b) to gc's
realization 14 — C9, E10, E11, E12, R1, R8, R9, R10, R11, R12, R15, R16,
R17, E7 (E7 known ≠ gc); (b) to OUR point 3 — E2 value axis (BUG-101),
E3, E4; (b-n) narrowed 7 — C7, E8, R3 (gc known outside), R4, R5, R7
(BUG-094), R13. The honesty-critical list (§10): E2, E3, E5 (gc
DEVIATION L-016), E7, R3, BUG-104. §10's REFUSED count reads 6 where §5's
own arithmetic gives 7 — a records nit to fix at the next census sweep.

### 2.4 Apparatus and utility (Gates B–C)

| # | item | owed | dep | size | who | status | evidence |
|---|---|---|---|---|---|---|---|
| P1 | **F8 — certificate provenance** | bind slow-tier `CERTIFIED-CACHED` sets to a semantic-source/build fingerprint (Lean toolchain, observation schema, checker/enumerator version) beyond wire hash + row params; stale certification = release-blocking; merge protocol 5a's trigger set widens at landing | none | S–M | mainline | **DONE ON BRANCH; awaiting the user’s independent review** ([AGENT] 2026-09-09, `fix/certificate-provenance`, implementation `7d60c8bf`). Full clean `ci --slow` PASS: 3665 native / 394 negative rows unchanged, same six-member set, 68 provenance controls. Shared source/build/claim identity, compiled executable stamp, both consumers, deliberate refresh, C9 and broadened 5a. [Handoff and measured cost](2026-09-09_certificate-provenance-completion.md) | gate audit F8; v1 §7.4 item (3) |
| P2 | **F9 — the frontend negative leg** | a rejection leg that runs the native frontend/decoder on the negative corpus and distinguishes type error / unsupported valid syntax / parser failure / infrastructure failure; malformed-wire tests; the decoder's `resultTypes[i]?.getD .int` fallback (`GoLean/NativeToIR.lean:1507,1584`) replaced by required metadata | none | M | mainline | **NOT STARTED**; 394 negative PASS means the ORACLE rejects the fixtures | gate audit F9; v1 §7.4 item (3) |
| P3 | **G6 tiers** | T1 `reflectlite` facility (HELD on A7); T2 read-full (after P); G6-4 `fmt` source-through (after T2 + G7; G7 blocked on the primitive cap 2/2, PENDING [USER]); T3 write+construct; G6-5 `encoding/json` | A7; P; G7 cap | 20–27 sessions total (G6 memo) | mainline | RULED G6-1…G6-5 ([USER] 2026-09-05); T1 HOLD PROPOSED [AGENT], PENDING [USER] | v1 §3.C items 2–6 |
| P4 | **F12 — one end-to-end workload** | the smallest genuine cedar functional driver (path: FR-31 fix → T1 + narrowed slice 4 → FR-12 for `Authorize`) OR a raft component (W4 stage 2: needs [USER] restart + FR-9 + E7's re-envelope); normal, error and boundary paths; a consumer proof through the public interface | B2 (FR-31), P3 (T1), FR-12 | L | mainline + customer | **PENDING [USER]** (workload choice; raft restart is a [USER] call — «we're not running Raft right now», 2026-09-03). No cedar driver has reached MATCH (v1 §2.5) | gate audit Gate C; v1 §3.H |
| P5 | **Sequential frontier (E9)** | 33 FR rows, 21 open at v1 (ledger §4); FR-15 complex LAST | — | per row | mainline | v1 §3.B stands | ledger §4/§5 |
| P6 | **Stdlib boundary (E10)** | six `fmt` shims retire via G6-4 | P3 | — | mainline | v1 §3.C stands | register |

### 2.5 Concurrency (Gate D)

| # | item | owed | dep | size | who | status | evidence |
|---|---|---|---|---|---|---|---|
| D1 | **F4 — the NPDRF reduction: statement repair, then proof or explicit assumption** | (i) a REVIEWED weakening of `NPDRFReduction` (`NPDRF.lean:438`) that survives obstruction 4 (post-state scoped to main-reachable locations, or main's readout only), stated as a theorem TARGET; (ii) the reference step/event model at Go's access granularity, distinct from the scheduler; (iii) the proof for the observable projection, or the reduction exposed as an explicit transfer assumption of the concurrent pin | C1 (trace as footprint); BUG-002's granularity decision | XL | Codex (statement repair FIRST, as its own reviewed deliverable; then the proof) | **DRAFT, REFUTABLE AS WRITTEN; nothing may cite it.** `stepM_le_stepMFine` PROVED (:327); movers cross-root only (:465/:511) | `NPDRF.lean` header obstructions 1–7; gate audit F4 |
| D2 | **go_mem HB detector soundness/completeness** | w.r.t. the reference event model of D1(ii): every go_mem race in scope is detected (completeness) and every detection is a go_mem race or a recorded designed divergence (soundness); U2 (`len`/`cap` on channels) closed or ruled; BUG-041's over-refusal scoped | D1(ii); C1 | L–XL | Codex | **MEASURED, NOT PROVED**: 364 rows, HOLE 0 (sampled); BUG-084's UNION rule is a designed divergence from `-race` | `docs/2026-09-02_detector-soundness.md`; `Race.lean` header |
| D3 | **BUG-002 expression-step atomicity** | the small-step expression machine or a granularity ruling (Q-ATOMICITY) | — | L | design → PENDING [USER] | open, latent; 0 rows | `docs/BUGS.md:3039` |
| D4 | **Concurrent `Language` instance** | a per-thread instance (park `LangD` shape) or a pool instance, with `StepM` as the simulation target; `Fair` stated over `Event.pick` downstream | B7, C1, D1 | L | customer (adapter spike here) | NOT STARTED on main; §3 assets | RSP §1.14 |
| D5 | **Open Q-rows** | Q-ATOMIC wave 2 (`atomic.Value/Bool/Pointer`, 1 red), Q-SELSEL (2 reds), Q-COND (3), Q-INITSPAWN (1), Q-GOEXIT (1); T-8: 16 strict rows not confluence-certifiable at registry granularity (`depth=N`) | — | per row | mainline | v1 §3.D stands | ledger §6/§7 |

### 2.6 Owed small chunks from the 2026-09-07 landing (each its own gate and audit ask)

From v1 §7.8.6 and the L4 note §9, none scheduled: (1)
`land/observer-fd-channel` — the runner-owned crash channel as an
inherited descriptor (= BUG-107 option (c) if ruled); (2)
`land/observer-gate-scripts` — the two Python gate scripts re-cut for
the R6-uniform contract (~900 lines of shell glue currently uncovered);
(3) FR-32 (§2.1 A6); (4) the `canonicalSlot0` docstring (§2.2 R8); (5)
the opt-in spike gate re-run `spikes/iris-customer/check` at the merged
tip after L3's `Terminal.lean` restatement; (6) the I1 declaration wire
(§2.2 R7); (7) `uintptr` (L5) — HELD on D1; (8) the 32 unlanded sprint
design/contract notes (four are cited by `Interface.lean`'s docstring
and do not exist on main: `docs/2026-09-06_boolean-program-contract.md`,
`recovery-static-claims.md`, `recovery-entry-contract.md`,
`recovery-control-contract.md` — a dangling-citation records nit until
the chunk lands); (9) `tools/check-recovery-fixture-controls.py`; (10)
NEW, this document (§3.1 T8): `land/typed-test-gates` — four declared
`Tests.*` modules (`Tests.BooleanTyping`, `Tests.BooleanTypingAudit`,
`Tests.BooleanInvariant`, `Tests.BooleanSafetyAudit`; libraries
`BooleanTypingTests`, `BooleanRuntimeTests`) are built by no `scripts/ci`
step — land the sprint's `scripts/check-boolean-{typing,runtime}` (and
the sibling steps so every declared test library has a named step).

**Addendum 2026-09-08 ([AGENT], `land/typed-test-gates`) — T8/W3/N6.**
[USER] authorized the typed-gate completion with no `GoLean/` edits, no
`Tests` theorem statement changes, worktree-local scratch removed on success,
compiled private-axiom/proof-hole controls, and bidirectional ownership/build
coverage. Seven gate families are restored against landed main `dc83782d`;
all 35 Lean test modules now have library ownership, and all 14 libraries
are assigned to 13 executed named CI steps. There are no exceptions.
The initial focused gates pass; full validation and cost measurement are in
progress. This is **IN FLIGHT**, not LANDED. N6's implementation is authorized;
the measured CI cost and adversarial review remain the user's acceptance
decisions. [Charter](2026-09-08_typed-test-gates-charter.md) and
[implementation record](2026-09-08_typed-test-gates-landing.md).

**Completion addendum 2026-09-08 ([AGENT], `land/typed-test-gates`).**
T8's implementation is **BRANCH COMPLETE**, unmerged, at `76f81a7d`.
The clean capped full `--diff` gate passed, actual exit 0: all 3,654
executable and 394 negative baseline rows match, 207 eval checks pass,
54 compiled audit negatives pass, and executed coverage accounts for every
Tests module and declared library without exceptions. The 18 coverage and
five scratch controls pass, including an actual compiler control against a
bare library build with empty `defaultFacets`; the runner explicitly requests
`:leanArts`. No `GoLean/`, `Tests/`, production frontend or baseline changes.
Seven new steps plus coverage actions took 267.380 seconds; total full CI
took 911.316 seconds with a warm cache and fresh poison compilation. Slow
certification is cached. Only records follow the validated implementation.
The linked landing record supplies source-bound evidence, per-step costs
and the mandatory review ask. The user owns the adversarial review and N6's
cost acceptance; T8 is not marked LANDED and no merge or push is authorized.

**Review addendum 2026-09-08 ([AGENT], `land/typed-test-gates`) — T8/W3/N6.**
The adversarial review of tip `35fab3e3` ([AGENT] coordinator's Opus auditor,
relayed) returned MERGE-CLEAN with small fixes; [USER] pre-authorized «land
with small fixes» (relayed). The fixes — receipt command provenance in
`tools/ci_libraries.py` `run_step` (behaviour unchanged; `verify` untouched)
and records — and every residual the review named are in the landing note's
["Residual gaps (rowed)"](2026-09-08_typed-test-gates-landing.md). T8 (§3.1),
W3 (§4.3) and N6 (§4.6) now read **LANDED (round 28, 2026-09-08 — pending
merge)**; the train supplies the merge hash. The measured cost as the
reviewer measured it (seven steps 272.98 s of a 920.06 s tip gate, ≈ +42 %
over the derived main-equivalent ≈ 646.7 s; the author's 266.96/911.32
reproduces within 2 %; no paired main run) is accepted by the [USER] at the
merge sign-off. The addenda above stay as written (BRANCH COMPLETE at
`76f81a7d`). The residuals are ONE combined owed row:

| # | item | owed | dep | size | who | status | evidence |
|---|---|---|---|---|---|---|---|
| T8.1 | **typed-gate coverage residuals** (R1 receipt check-command enforcement; R2 `Tests/` escape-hatch scan + `StringPanicMembers` audit; R4 fixture tools on the `--slow` path; R3 timings pruning; R7 scratch retrofit of the three incumbent audits) | R1: a per-step `check` field in `scripts/ci-libraries.json` compared against the receipt's `command` in `verify`, with a negative control (a bare `library_step` for a step that declares a check must fail); R2: add `Tests` to the three escape-hatch `find` sets (`scripts/ci:239/:284/:310`; the reviewer verified zero hits today) and give `Tests/StringPanicMembers.lean` an importing audit — a gate WIDENING, PENDING [USER]; R4: run the full (non-`--lean-only`) `scripts/check-boolean-typing`/`scripts/check-recovery-typing` on the `--slow` path with receipts; R3: a header note or keep-last-N pruning at `verify` for `artifacts/ci-library-timings/`; R7: `typed_audit.scratch()`/`link_package()` onto `scripts/check-interface.py`, `tools/admission-check.py audit` and `tools/recovery-terminal-audit.py` (≈ 1.6 GB of scratch per gate run today, measured by the reviewer; the seven new gates leak zero) | T8 merged | S (R1, R3, R4 each ≤ a session; R7 S–M; R2 a ruling plus minutes) | mainline, W3 follow-up; one lane, PROPOSED [AGENT] name `land/typed-gate-residuals`, its own gate and audit ask; queue slot (PROPOSED [AGENT], coordinator's order): the next W3 chunk after the T8 merge | **OWED** — none started; R2's widening PENDING [USER] | 2026-09-08 review R1/R2/R3/R4/R7 (relayed); [landing note](2026-09-08_typed-test-gates-landing.md) "Residual gaps (rowed)" |

### 2.7 Tally by status

Rows in §2.1–§2.5 (31 rows; §2.3's per-bug and §2.6's per-chunk lists
counted separately): LANDED-in-full 0; PARTIAL (landed piece + owed
remainder) 5 (A1, A3, R7, and the two-profile halves of A5/D2 counted
with their rows); OWED 12 (A2, A4, A6, A8, R8, B1, B2, D1, D2, P1, P2,
plus A5's document); RULED-not-started 5 (R2, R3, R4, R5, P3's tiers);
PROPOSED-not-started 2 (R6, R9); PENDING [USER] 5 (A7, A8's criteria,
P4, D3, B3's BUG-061/100/107); IN FLIGHT on a branch 2 (R1, R7's wire).
Open bugs 17 (3 open wrong answers + 1 guarded). Owed small chunks 10
(nine carried from the landing + T8, new here).

---

## 3. The asset log — what is at hand, and what of it can be adapted

### 3.0 How the survey was done, and the one structural fact

Read-only, via `git show <branch>:<path>`, `git log`, `git ls-tree -r`,
`git diff --stat <merge-base>..<branch>`, `git merge-base [--is-ancestor]`,
from this lane's worktree; no branch was checked out, no worktree
entered, no `lake`/`lean` run. Every ADAPTABLE/DEAD verdict below is a
STATEMENT-AND-DEPENDENCY judgment from source reading, not a build
result — nothing on the park is expected to compile against main
unmodified (the surveyors say so; §3.4).

**The structural fact that reorganizes the log:** `park/reasoning-2026-08-31`
(= `7440bf70`, 2026-08-29) **is an ancestor of `main`** (`git
merge-base --is-ancestor park/reasoning-2026-08-31 main` → exit 0;
`git rev-list --count park/reasoning-2026-08-31..main` = 318). The split
then DELETED the reasoning tree from main in one commit (`git diff
--numstat 7440bf70..main | awk '$3~/^proofs\//{p+=$2} END{print p}'` →
195,031 lines of `proofs/` removed; 156 docs). So every parked asset is
a DELETION on main with exactly one address, `7440bf70:<path>`; the
branches `g-bind`, `a-trip`, `u0-iris-refresh`, `w1-prover`, `w0-reset`,
`campaign-arc2/-arc3/-arc4/-arc4b/-arc4c`, `foundation`,
`proof-automation` are ALL ancestors of main too (merged before the
split) and resolve to the same address. Only seven pre-split refs carry
Lean or docs NOT in main's history: `channel-logic` (+ `-s4`),
`wp-design`, `raft-proof-campaign`/`design-pass`, `campaign-arc4d`,
`campaign-ce`, `campaign-wave-a`, `w3-init`, `w3-m`. Post-split: the 32
`typed-*` branches (none an ancestor — L1–L6 landed by path-selection
squash from `typed-consumer-sprint` @ `7edc298f`), `review/project-audit-20260905`
(an ancestor — LANDED), and the two `storage-maintenance-*` branches
(not reviewed). Of 108 branches matching the survey filter, 101 are
ancestors of main.

**Volume at `7440bf70`** (`git ls-tree -r --name-only … | grep '\.lean$'`
+ a `git show | wc -l` loop): 425 `.lean` files, 304,864 lines; `proofs/`
193,834 — `Examples/` 107,592 (132 files), `Specs/` 25,044 (59),
`Frame/` 15,507 (29), `Sym/` 11,765 (16), `Laws/` 6,502 (12), `Audit/`
4,023 (31) + `Audit.lean` 2,098, `Tactics/` 603, the WP core
(`Lang`/`Ghost`/`HeapBridge`/`Lifting`/`Adequacy`/`TotalWp`) ≈1,700;
5,102 `theorem`/`lemma` declarations; **0 `sorry` outside
`Challenge.lean`** (whose bodies are `sorry` by design — the judge
re-proves them); 51 designated theorems (`proofs/Audit.lean:293-460`),
180 `#print axioms` pins; `compat/verdi` 38,972 (35 files), `compat/gobra`
1,131 (8). Liftable INFRASTRUCTURE ≈ 11k lines (WP core + Laws +
Tactics); the rest is per-program content.

**The core moved hard underneath it** (`git diff --stat 7440bf70..main --
GoLean/GoCore/` → 87 files, +22,646/−6,892): `Machine.lean` 3,602 →
4,870 lines; `Step` ≈155 → 112 constructors (54 removed — the
`break*`/`continue*`/`label*` families and `*EnterPanic` twins, replaced
by B4's `Signal` modes and B2's one `deliver`; 11 added — `atomicSt*`,
`evalGlobal`, `inertLabel`, e13-b's probe rules); `Heap` from an
association list to `Array HeapCell` (A2); `nextAddr` derived;
`HeapCell.chanData` → `chanPayload (buf) (capacity) (closed)`. Names the
park's proofs depended on that are GONE on main (`git grep <name> main
-- GoLean/`): `Heap.set` (only `Heap.set_locSup` remains),
`coerceStoredValue` (a `simp` target at 131 park sites → 0 hits), `HeapWf`
(0 hits — the park's adequacy side condition), `pruneIterFramesKey`
(retired 2026-09-02/03); `typeResolutionFuel` (a `simp only` target at
335 park sites) survives at 2 sites. MOVED, not gone: `step_complete` →
`MachineSound.lean:506` (the surveyor's "→ `BooleanPreservation.lean`"
is a second, profile-local statement); `seqCont` → `BooleanControl.lean`.
**The pin and toolchain already match**: the park's `proofs/lakefile.toml`
requires iris-lean `e7a0a43814c4f1154ca0c8049883ca56c2288b86` on Lean
4.32.2 — identical to `spikes/iris-customer/lakefile.toml:13-16` and
`lean-toolchain`. Re-lifting is a rebase-onto-a-moved-core problem, not
a port (exception: `channel-logic` predates U0 — iris `3877dbe…`, Lean
4.31.0). `raftsubject/` has ZERO drift since the campaign base `66d62eac`
(`git diff --stat 66d62eac..main -- raftsubject/` → empty): the raft
subject the campaign proved things about is byte-identical.

### 3.1 The asset table

Columns: asset · where (`<ref>:<path>`) · size (lines; `+/−` vs
merge-base where a branch) · built over (core era) · class (§0.3's
second vocabulary) · the concrete artifact to lift · pitfalls recorded
in-tree. "park" = `7440bf70` (= `park/reasoning-2026-08-31`).

| # | asset | where | size | built over | class | lift | pitfalls |
|---|---|---|---|---|---|---|---|
| 1 | Sequential Iris `Language` instance | park`:proofs/GoLeanProofs/Lang.lean` | 61 | assoc-list heap, 155-rule `Step` | **SUPERSEDED** by `spikes/gate-a1/GateA1/Language.lean` (which names it as lineage) | the design decisions already carried over: `Val := Unit` at `.next .stop`, `PrimStep := Step`, no forks | `val_stuck` by `cases` over every `Step` rule — churns on each added rule (→ §4.4 item 5) |
| 2 | Ghost state, heap bridge, adequacy, total WP | park`:…/Ghost.lean` 86, `HeapBridge.lean` 324, `Adequacy.lean` 354, `TotalWp.lean` 207, `Specs/TotalPins.lean` 464 | 1,435 | assoc heap; `HeapWf`; pins `prog`/`methods`/`types` by three equalities | **ADAPTABLE (design) / DEAD (bodies)** — A2's `Heap`/`Ghost`/`Adequacy` on main redo the first two over the dense heap at whole-cell | the 7-slot functor bundle `GoCoreS` mirroring HeapLang's; the `TotalWp` instance (upstream iris-lean's first inhabitant) and `go_total_adequacy`'s shape (`StronglyNormalizing Language.ErasedStep`) | `HeapWf σ` + three pin equalities as adequacy preconditions — B7's `ProgramCtx` is the fix (RSP L11); `allStreamsOk` enumeration BANNED for new `Terminates` members (corpus plan A1) |
| 3 | WP law family + lifting | park`:…/Laws/` (12 files) 6,502 + `Lifting.lean` 625 | 7,127 | 155-rule `Step` incl. the 54 deleted control rules | **ADAPTABLE (statements) / DEAD (bodies)**; `Unwind.lean` 929 + `Control.lean` 305 worst hit (built on the deleted rules) | statement shapes: `Call.lean` (≈25 laws), `Eval.lean` (28 step laws), `Loop.lean:83` (Goose `wp_forBreak_cond` shape, Löb-proved, `I : Bool → IProp`), `Range`, `Values`, `StmtOps`; `Lifting.wp_store_step` as the one gen_heap step-plus-ghost-update engine | every law is stated over park constructors; A2's `Lifting`/`Rules` (main) already re-derived the store/load/init/recover subset over the dense heap |
| 4 | The bind rule | park`:…/Laws/Bind.lean:170` `wp_plug_bind`/`wp_bind_plug`; `Frame/Plug*.lean` (8 files) ≈3,000 | ≈3,260 | `plugC`, `hasBarrierC`, `mapIterFree`, `recoverThroughWrappers`, `pruneIterFramesKey` | **SUPERSEDED as a route** (F3 → continuation-explicit rules) / **ADAPTABLE as the premise census** for §2.1 A2 | the three premises are the first candidate for `Admissible`: `mapIterFree k'` (guarded the map-delete prune crossing call frames — `pruneIterFramesKey` is GONE, so this premise may now be discharge-free; unverified), `recoverThroughWrappers k' = none` (the recover side condition — exactly F3's), `hdrain` (FALSE at ≥ 2 live defers; a σ-conditioned restatement is the named owed row) | the in-tree refutation of `Language.Context` is the F3 counterexample class, recorded 2026-08-29: `primStep_fill_inv` fails for `K = plugC env' k'` at `e = .returning .stop` with a poppable `.frame` |
| 5 | Executable frame theorem (SL locality) | park`:…/Frame/` 29 files | 15,507 | `Machine`, `StepFn`, `State` at park | **ADAPTABLE (statement shapes) / DEAD (bodies)** | `Sim`/`StepSim`/`Transfer` (16/12 consumers), `Rename`/`RenameId` (α-renaming — B6 makes it unnecessary), `Threshold`/`rebaseSimT`, `AllocIndep.allocatorIndependence` (**doctrine register #6's theorem lives ONLY here**; main maintains its CONDITION, pointer-equality-only observation), `NoPanic`, `HeapOps`, `StrictOps` 2,003 | `FrameSimS` is COPY-THREADED (`ShapeStrict.lean` = 2,013-line mechanical copy of `StrictOps.lean`, SCAFFOLD); re-opens if any address-exposing observation is added |
| 6 | `Sym` — the symbolic mirror evaluator | park`:…/Sym/` 16 files | 11,765 | `stepFn` transcribed arm-for-arm | **ADAPTABLE, high value** (route B: mirror lives proof-side, outside the statement TCB) | `Refine.lean` `symEvalWindow_refines` (∀ρ ∀σ ∀ch, `ch` unchanged — the three fidelity quantifiers), `Drift.lean` (the drift theorem, a DEFAULT BUILD TARGET: a computing arm diverging from `stepFn` fails the build), `Domain.lean` `ScalarDom`, `Walk`, `TableExt` (`stepFnT`, type-table input), `Crossing.lean` (King-1976 path conditions as window splits — blocker (K)) | a SECOND full transcription of the machine (re-pays drift cost on every core change); quit-on-`none` (payload-consulting sites quit; a quit shortens the window, never unsound); `PickTransport` DUPLICATE + ORPHAN (mechanism registry #1); its design note exists ONLY on `wp-design` |
| 7 | `go_walk` — goal-directed automation | park`:…/Tactics/GoWalk.lean` | 603 | `Lean` + `Iris.ProofMode` + `Iris.ProgramLogic.WeakestPre`; **zero GoCore imports** | **ADAPTABLE, highest leverage** — the Lithium precedent at algorithm level | `go_walk`, `go_walk n`, `go_walk with [h]`, `go_walk_step law`; `@[go_walk_law]` attribute + `DiscrTree` of law conclusions; the modality dance; disclosed stops (no law / non-`rfl` side condition / nondeterministic branch / unresolvable split) | invariant-carrying rules (`wp_while_inv`, `wp_map_iter_inv`) DELIBERATELY unregistered — their `I` is a `∀`-obligation no goal determines (Lithium's own hard class); a law with a variable statement matches everything (hence the bound); the n=1 `CommittedIndex` walk cost ~2,800 hand tactic lines before it |
| 8 | Kit / brick-wp library + guide | park`:…/StepKit.lean` 881, `SliceMem` 1,430, `MapMem` 1,076, `MapLoops` 1,237, `MapPerm` 932, `StringMem` 190, `SliceWalk` 1,000, `FuelMeasure` 774, `CondFor` 755, `EntryEq` 471, `Lens.lean` 794, `RunGlue` 494; `docs/kit-guide.md` 825; `proofs/Audit/Kit.lean` 780 | ≈11,600 | `MachineSound`, `applyStrictOp`, `storeTarget`, `Heap.lookup` | **ADAPTABLE (patterns, guide, discipline) / DEAD (bodies)** | `StepKit`'s five placement-generic rules; the guide's situation index; `Lens.lean` = the Perennial `Access`/`AccessStrict` field-lens port (first-order, Iris-free); `MapPerm`'s permutation-family threading (never canonicalizes — the (M) blocker's design); the axiom-pin-per-kit-addition rule | the STORM rule: state a step over an abstract `σ`, pin the result type at concrete sites; kit names may never appear in a headline statement's closure |
| 9 | Surface layer (Iris-free spec vocabulary) | park`:…/Surface.lean` 723, `SurfaceBridge` 304, `SurfaceExit` 208 | 1,235 | `MachineSound`, `MultiSound`, `execStmt` | **ADAPTABLE** — the assertion-shaped half `Interface.lean` (trace-shaped) lacks | `Heaplet`, deep-embedded `HProp` + satisfaction, `GoTriple` over `execStmt`, `GoSpec`/`GoFuncSpec`, `goSpec_of_wp` (the collapse from WP to an Iris-free sentence) | structural rule D1: Iris-free by ci lint; a general module may not import `Specs/*`; the 51 designated theorems are STATED here |
| 10 | Concurrent instances | park`:…/LangC.lean` 449, `LangD.lean` 1,144 | 1,593 | `Multi.lean` at park (+1,413 lines on main since) | **UNKNOWN** (needs a constructor-level diff of `StepM`) / **ADAPTABLE (design)** | `LangC`: thread-pool `Language` + fork rule + closed adequacy over a spawning program; `LangD`: per-thread `StepDC` with ∃-quantified partner in `pairArrive`/`pairRelease`/`selCommit`/`wake`, `stepM_erasedD` simulation | `LangC` CANNOT express `StepM`'s pairing (two threads in one step vs one-thread-per-step); `LangD`'s envelope is deliberately WIDER (any delivered value) — sound for simulation only; a WP against it must absorb "a parked receiver may release with ANY value" → the channel-logic finding (row 11) |
| 11 | channel-logic | `channel-logic` @ `f49752a6` (+14,542/−26 over `ba6398ab` 2026-08-11, 34 commits); `channel-logic-s4` @ `9fbf674d` (+16,847/−84, 40); 13 files / 10,605 lines absent from park (`ChanD`, `ChanDM`, `ChanDMRes`, `LangDM`, `LawsDM`, `Specs/Chan{Transfer,Rendezvous,RendezvousVal,DSP,CloseProbe,VacuityWarning}`, `SeqWalkDM`, `SpawnNoopProgress`) | ≈14.5k | pre-U0 core (iris `3877dbe`, Lean 4.31.0); `HeapCell.chanData`; `Heap.set` | **ADAPTABLE (statements: the resource algebra shape) / DEAD (assertions and proofs)** | `ChanDMRes.chanInv (a) (cap) (Ψ) := ∃ buf, ([∗list] v ∈ buf, Ψ v) ∗ a ↦ chanCell` (transcribes 1:1 to `chanPayload`), the 8 send/recv laws, `goTripleC_of_wpDM`; s4's NPDRF material: `stepM_iff_fine_bs`/`stepsM_iff_fine_bs` and the three `*_refuted` theorems | the informal theorem: over `LangD`/`StepDC` **no WP can pin a delivered value** (∃-partner) — fix = the cell-mediated carrier `LangDM` (Perennial is cell-mediated BY CONSTRUCTION); `NPDRFClassReductionRooted` was REFUTED post-park — never cite as proved; the permanent VACUITY warning («A channel triple ALONE certifies nothing about communication, liveness, or deadlock» — a `GoTripleC` proved for a `.deadlock` program); park ruling: resume only after the W3.2 re-envelope; memory: salvage `-s4`, never merge as-is; the caption-sweep lesson (a "module-wide scan" missed negated phrasings) |
| 12 | wp-design | `wp-design` @ `c3dc3986` (+1,153 docs, 6 commits over `04fec3c1` 2026-08-16) | 1,153 | — (docs only) | **ADAPTABLE (design)** | the WP-arc charter; `docs/2026-08-16_symbolic-domain-design.md` (the `Sym` design of record — ONLY copy on any branch); OQ1–OQ6 DISCHARGED 2026-08-18; the compute-and-emit principle («the interpreter is the decision procedure. Any search component must be finite-table, probe- or evaluation-grounded, and fail-closed … No open simp sets, no backtracking search, no unbounded defeq») | OQ3's amendment (the charter's literal `stepFn' @ GoValue = stepFn` → the embedding form) was recorded as an integration TODO and never done |
| 13 | a-trip / u0-iris-refresh / w1-prover / w3-init / w3-m | ancestors (address `7440bf70`) except `w3-init` @ `0087b48a` (+1,813, 1 commit over `fe4e42a3` 2026-08-27) and `w3-m` @ `7468a9d4` (+2,320, 2 over `ce05ecd1`) | — | park core | a-trip **ADAPTABLE, no equivalent on main**; u0 **SUPERSEDED**; w1/w3 **ADAPTABLE (forms) / DEAD (proofs)** | `7440bf70:scripts/WpVeneerClosure.lean` (363) + `wp-veneer-lint` + `wp-lint-scope.txt` — the proof-TERM tripwire banning tier-3 proofs from reaching `stepFn`/`execStmt`/`allStreamsOk` except through Laws/lifting/adequacy (the Audit gate polices STATEMENT closures only; «a veneer would be a cost INLIER»; negative twins cannot catch it); the five judgment forms `CallSpec`/`StmtSpec`/`CallSpecR`/`CallSpecRD`/`CallSpecRN` (Hoare triples over `stepFnIter` with the tape as an explicit demonic parameter, `ch' <:+ ch`); u0's ADOPT/KEEP reuse table | A-TRIP's first in-build enrollment FAILED on scope gaps («the scope config is young»); `CallSpecV` (function-value call) named, never built — blocks every closure call site |
| 14 | raft-proof-campaign / design-pass | `raft-proof-campaign` @ `17197113` (+445,212/−16 over `66d62eac` 2026-08-24, 262 commits; 153 touch `docs/raft-campaign-log.md`); `design-pass` @ `24212862` (219) | 3,799-line log + 27 design docs | park core | **ADAPTABLE (records)** | the campaign log (the [AGENT]/[USER] provenance trail; the OUTSIDER LEGITIMACY REVIEW — «genuine Iris», MINOR REVISIONS; the 892-proof-lines-per-32-Go-lines economics finding); the blocker taxonomy — **(M)** map-order (association order persists into built maps; ≥10⁴ leaves never re-converge), **(K)** the data-branch crossing kit, the **segment-walk NO-GO** (2.22 s/step, 157 MB/step at 19k cells ⇒ 440–800 CPU-h; monolithic `rfl` ≥ 3.1 TB), **F1 SEVERE** (`logBridge`/`commitTie` tie a frozen carrier to the advancing one); `docs/2026-08-24_campaign-iris-reuse-map.md` (ADOPT Perennial `Access`/`AccessStrict`, goose proofgen per-field instances — 76 for `raftpb`, ~1,400 for the Goose corpus — upstream `TotalWeakestPre`/`TotalAdequacy`, `AddModal`/`ElimAcc`, `iinv`; REJECT rebasing `Sym`/`FastEval` onto Iris and Perennial's axiomatize-the-data-layer strategy; KEEP `go_walk`); the iris-corpus plan revision 1 (`design-pass:docs/2026-08-28_iris-corpus-plan.md`, 1,104 lines — the park carries the landed 1,105-line copy at `7440bf70:docs/2026-08-28_iris-corpus-plan.md`; **not on main**) | the reuse map's own caveat: «no local checkout of RefinedC/Lithium or Diaframe existed — I make no claims about them beyond naming them as unchecked»; the corpus plan's ruling that RefinedC/Lithium is «EXPLICITLY the road not taken for now … revisit only if the tactic route measurably stalls» (§3.3); N-1 approval claimed by merged commit `05e81b70` («[USER]-approved 2026-08-28») while `design-pass`'s tip still reads «awaiting [USER] adjudication at gate N-1» — unresolved (§4.6 N8) |
| 15 | campaign-arc4d / campaign-ce / campaign-wave-a / arc2–4c | `campaign-arc4d` @ `7fa0e04d` (+16,281, 17 over `eee6b43b` 2026-08-26); `campaign-ce` @ `a1d70861` (+1,996/−36, 4 over `c4986b29`); `campaign-wave-a` @ `b3c329c8` (+554/−86, 3); arc2/3/4/4b/4c ancestors | — | park core | arc4d **ADAPTABLE (schema) / DEAD (spans)**; ce **ADAPTABLE (statement)**; wave-a **ADAPTABLE**; arc3 **ADAPTABLE** (Verdi side); arc2, arc4b, arc4c **DEAD** | arc4d: `Sym/UtoaForKit.lean`'s `CondFor` (Floyd/Hoare loop-invariant schema for plain `for`); ce: `SpanIso`/`SpanIsoAt` (the canonicalizer-free relational face of choice-erasure); wave-a: `Lens.lean`; arc3: `7440bf70:compat/verdi/` election safety, log matching, leader completeness, state-machine safety (2,615 decls, zero hatches) | arc4d's spans are fuel-literal (`m ≤ 5200`) over the old machine; ce's gate theorem `cequiv_iff_spanIso` NEVER proved; wave-a's `round_induction` «couples nothing»; arc2's segment walk refuted; arc4c's `ChoiceCanon` (616) DELETED by [USER] ruling 2026-08-28 («choice-invariance will just roll up into the reasoning layer, eg. when we have a points-to we don't care about choices outside the footprint») |
| 16 | Program proofs — gallery | park`:…/Examples/` 132 files; `Examples/Targets.lean` 1,015; `docs/verified-examples.md` 4,419 | 107,592 | park core (`coerceStoredValue`, `typeResolutionFuel` unfolded at hundreds of sites) | **ADAPTABLE as a CORPUS + statement layer / DEAD (bodies)** | the 25 members (`SliceQueue` 8,343, `SliceStack` 6,830, `Stein/Run` 4,487, `WordFreq/Count` 3,164, `BinSearch` 3,045, `RunLength`, `DedupAdjacent`, `MatMul`, `Kadane`, `Sieve`, `MinMax`, `FibMemo`, `Reverse`, `WordCount`, `DotProduct`, `Fib`, `Histogram`, `TwoSum`, `InsertionSort`, `BubbleSort`, `SelectionSort`, `Gcd`, `PowMod`, `StringReverse`, `ArrayPalindrome`) as RE-TARGETS for a RefinedGo; the gallery's byte-checked Go quotes (`scripts/render-gallery`) | economics: 892 proof lines per 32 Go lines with G-AUTO unbuilt; R1 residual: ~35 theorems on the banned `allStreamsOk` tier, 4 designated |
| 17 | Program proofs — raft / quorum / goose | park`:…/Specs/` 59 files: `GoldenQuorum*` (5 files ≈7,000), `Specs/Raft/` 16 (`DriverNet` 1,384, `AbsTwinCheckerRead` 1,004, `NativeEtcdDischarge`, `AbsStateV2`, `NativeS1/S23Chain`), `ImportedGoose*` 11, `GooseParity*` 7, `Callchain` + `CallchainSentences` (C-05), `Statements.lean` 391 (DEF-ONLY) | 25,044 | park core; `raftsubject/` (zero drift) | **ADAPTABLE (statements + the raft corpus) / DEAD (bodies)** | landed raft proofs: `SetLogger`, `NewMemoryStorage`, `MemoryStorage.ApplySnapshot`/`firstIndex`/`lastIndex`/`FirstIndex`, `Config.validate` (∀ id ∈ {1,2,3}), `tracker.MakeProgressTracker`, `newLogWithSize`, `unstable.maybeFirstIndex`/`maybeLastIndex`/`maybeTerm`, `quorum.JointConfig.IDs` (full permutation family), `raft.becomeFollower` (+ the W2 plug-rule gate at the verbatim `stepCandidate→becomeFollower` site), `zeroTermOnOutOfBounds`, `raftLog.firstIndex`/`lastIndex`, `softState`/`hardState`, `MustSync`; parked: the confchange `Clone`/`symdiff`/`Restore`/`Simple`/`switchToConfig` chain, `newRaft`, `NewRawNode`, `Ready`/`acceptReady`/`Advance` | the F4 incident (2026-08-07): importing a targets module dragged nine `decide +kernel` proofs into the trusted closure → DEF-ONLY statement modules, ci step 1c3 |
| 18 | `FastEval` compiled replay | park`:…/FastEval/` 12 + `FastReplay.lean` 288 | 5,598 | `stepFn` (proof-side `stepFast`) | **UNKNOWN** | `FastEval/Transfer.lean` (the pinned transfer theorem `stepFast` → `runProgramM`) | a second transcription; not a default target; the reuse map REJECTS rebasing it onto Iris |
| 19 | Judge / audit apparatus | park`:proofs/Audit.lean` 2,098, `Audit/` 4,023, `Challenge.lean` 461, `Solution.lean` 432; `scripts/comparator-judge`, `comparator-setup`, `judge-config.json`, `wp-veneer-lint` + `WpVeneerClosure.lean`, `proof-lint`, `proof-costs`, `render-gallery`, `check-golden` | ≈8,000 | the whole park tree | **ADAPTABLE — the DESIGN is the asset** (the customer's gates) | the 51-name designated list + statement-TCB closure gate; 180 `#guard_msgs #print axioms` pins; the Challenge/Solution kernel-replay judge (re-elaborate, export, replay sandboxed; statement identity + axiom allowlist); A-TRIP; `proof-costs` report-only by doctrine («DO NOT HARDEN THIS INTO A GATE») | the designated-list parser broke on a square bracket inside a comment (2026-08-27) — the "no square brackets in that comment" convention is load-bearing; the judge cannot run from a lane worktree and needs `deps/{comparator,lean4export,landrun}` (never modified; binary build has needed the [USER]) |
| 20 | `compat/` + the two 2026-08-09 arc notes | park`:compat/verdi/` 38,972 (35), `compat/gobra/` 1,131 (8); park`:docs/2026-08-09_verdi-compat-layer.md`, `…_gobra-lean-backend.md`, `…_verdi-p1-lane.md` — **on the park branch, NOT on main** (`git ls-tree --name-only main docs/ \| grep 2026-08-09` → only `sync-package-design`, `spec-parity-arc-charter`) | 40,103 | own lakefiles/toolchains | **UNKNOWN / exploratory** (lower bar by charter) | Verdi note §4d (a theorem's robustness to model extension depends on what its STATEMENT mentions — make the durable top theorem client-observable linearizability), §4e (the Go-level theorem is refinement RELATIVE TO A DRIVER CONTRACT at the `Ready`/`Advance` boundary — «genuinely new spec-writing; audit it like a law statement»; quantifying over literal Go client contexts DEFERRED), §8b (the parallel-lane seam: lane owns `compat/**`, mainline owns ALL of GoCore; coordination points are explicit merge-window slices), §9 ([USER] 2026-08-11: certificate transfer from a frozen upstream proof REJECTED — «A living development must OWN its proofs»); Gobra §10a–d (the 60 GB `decide +kernel` on a FALSE Bool; silent VACUITY via an unscoped total environment — `requires 0 < b` read as `0 < 0`; `decreases` parsed then dropped; «the first fix closed the instance that was reported, not the class») | Gobra §7: «an automation engine of RefinedC/Lithium class does not exist in Lean and would have to be built» — the ring-2 predicate generator per Go type is the other long pole |

**Post-split (typed-*) assets — all over merge-base `47195683` (2026-09-05); none an ancestor of main:**

| # | asset | where | size (`+/−` non-evidence) | class | lift | pitfalls / blocker |
|---|---|---|---|---|---|---|
| T1 | **B7 `ProgramCtx`/`Store` prototype** | `typed-context-store` @ `ca1e01d5` (+21,220/−368, 80 commits) | — | **IN FLIGHT — and the B7 implementation is NOT COMMITTED** | the only unique tracked file: `typed-context-store:spikes/iris-customer/GoLeanIris/IndependentB7Review.lean` (51 lines; five theorems `primitive_exact_context`, `fractional_read_with_frame`, `full_alias_ownership_exclusive`, `both_customers_original_choices`, `uncaught_remains_panic`) — usable as B7's ACCEPTANCE TESTS; the design note is on main | `git grep ProgramCtx typed-context-store -- GoLean/` → only the `Platform.lean` deferral comment; `typed-context-store:TODO.md:87` `- [ ] B7` unchecked; vs main the branch is a REGRESSION on `GoLean/GoCore/` (17 files, +144/−1,387 — it predates L3's modules); the review file references `ProgramCtx`/`ContextExpr`/`Prim ctx` which exist on NO branch — it was written against the sprint worktree's UNCOMMITTED tree. The real B7 work exists only as an uncommitted working tree in `.claude/worktrees/typed-context-store` (pause-state, second-hand: «270 runtime/reference/test jobs PASS», customer 321/gate PASS; the V1 kernel-sharing completeness claim WITHDRAWN, V2 uncommitted, the 4,356-root diagnostic FAILED). **If that worktree is cleaned, the work is gone** — §4.6 N1 |
| T2 | B7 review branches | `typed-b7-{kernel,customer,original}-review` @ `3107e248`/`0f5ae41f`/`2831473d` | — | **SUPERSEDED** (conclusions on main via the pause-state record) | nothing unique (customer-review carries the same `IndependentB7Review.lean` blob) | added NO review document; their only doc delta on the B7 note REMOVES main's R20 correction («the host-capability decision remains OPEN and [USER]-owned») |
| T3 | **I1 declaration wire** | `typed-i1-envelope` @ `3d49e9e9` (+21,470/−368, 86); `typed-i1-json` = `typed-i1-envelope-review` (one commit `7ac3eb46`, two names); `typed-i1-declarations` @ `380753b9` (+7,538/−67, 36) ⊂ envelope | — | **OWED chunk L1b (HELD until its own gate)** | `GoLean/{NativeDeclaration,StrictJsonParse}.lean`, `Tests/{DeclarationWire,DeclarationAudit,StrictJsonParse}.lean`, `tools/nativefrontend/declaration{,_test,_fixture_test}.go`, `scripts/check-declarations`, `tools/{declaration-audit.py,check-declaration-wire.lean}`, `docs/2026-09-06_i1-{declaration-wire,positive-declarations,json-boundary}.md`; the design: an ADDITIVE positive-declaration channel reading exact `go/types` facts (closed basic types incl. `complex128`, nominal keys with ordered type args — `iter.Seq[int]` needs no opaque TypeDef — byte-exact struct tags, canonically ordered method sets); `StrictJsonParse` refuses duplicate keys and unpaired surrogates BEFORE insertion (`Lean.Json` collapses duplicates and substitutes U+FFFD) | touches trusted surface #1 → 5a; A-R11 (`check-declarations` prints sha256 and never compares), A-R12 (`declaration.go:100` poisons the executable emit's `badLocalTypes`; a nil-package object must refuse); «NativeToIR accepts the new root declarations but ignores their content»; runtime V2 UNCOMMITTED; its full CI exited 1 before the pause. Land only with `check-frontend-pins` unchanged and the certified set byte-identical |
| T4 | **`uintptr` identity (L5)** | `typed-uintptr-identity` @ `5f185fb3` (+17,097/−343, 64) | — | **HELD — PENDING [USER] D1** | `IntKind.uintptr` (`Value.lean` +4: `bitsAt = 8 * p.wordBytes`, unsigned), `NativeToIR.lean:252` `"uintptr" => pure .uintptr` (was `.uint64`), `asAtomicOp?` to five kinds, `Corpus/coverage/exec/ints/uintptr-identity/`, `docs/2026-09-06_uintptr-identity-repair.md` («Go 8 versus Lean 15: cross-type assertions in both directions and a `M(uintptr)` method falsely matching `M(uint64)`»); isolated validation exit 0 (3,635 = 3,390/245; 394 negative; certified set unchanged) | overrides the standing latitude pin R1 («observations of it refused») and w7 J-8 («record it there rather than "fix" it») without citing either (B-R13); `NativeToIR.lean` → 5a; takes BUG number **108** if (b) is ruled (107 is L4's) |
| T5 | **byte-store spike (BUG-090)** | `typed-byte-store-consume-review` @ `631b883f` (+22,132/−368, 81) — tip of `typed-byte-store-{proof,review,exec,consume-review}`; `typed-byte-runtime` @ `35aee5d3` (+28,937/−398, 88) | 13 files | **PROTOTYPE — the cleanest liftable unlanded artifact** (own lakefile, outside every gate, no trusted-surface delta) | `spikes/byte-store/`: `storeByteElement_eq_storeLoc … (hc : Heap.lookup … = some (.value (.array n (.int .uint8)) (.array values))) (hn : BackingNormal n values)`, `consumeByteElement_eq_storeLoc`, the subtype-threaded `consumeCertifiedByteElement_eq_storeLoc`; `docs/2026-09-06_byte-store-{proof,executable}-findings.md` | its own README: «the unchecked branch does **not** refine `storeLoc` on arbitrary non-normal backing arrays … Production integration would therefore need a sound certificate boundary or a fallback»; `typed-byte-runtime`'s `ByteArrayStore` (574 lines) + `Machine.applyStmtOp_byteAppend_exact` are UNCOMMITTED — only evidence is committed, which is exactly what may not land; BUG-090's 2 MiB case still times out |
| T6 | string-members lane | `typed-string-members` @ `819182b5` (+25,356/−342, 72) | — | **RETIRED** (D2, RULED round 24) | nothing — do not revive | A-R1 BLOCKER: 5 of 9 PASS rows divergent from gc; the `Controls` role is covered by L4's `panic-controls` under L3's renderer |
| T7 | landed-by-squash lanes | `typed-recovery-terminal`, `typed-r1-production-review`, `typed-panic-rendering` (→ L3); `typed-abort-observation-review`, `typed-shared-customer(-review)`, `typed-recovery(-runtime/-setup)`, `typed-boolean`, `typed-contract-review` (→ L1); `typed-observer-{classification,controls}` (→ L2/L4); `typed-preflight`, `typed-consumer-charter` | — | **SUPERSEDED-BY L1/L2/L3/L4/L6** | nothing beyond the owed gate scripts (T8) | — |
| T8 | **NEW FINDING (this survey; scope corrected and verified here): four `Tests.*` modules on main are built by no `scripts/ci` step** | main `lakefile.toml:31-57` declares seven `lean_lib`s (`BooleanTypingTests`, `BooleanRuntimeTests`, `RecoveryTypingTests`, `RecoveryStorageTests`, `RecoverySetupTests`, `RecoveryControlTests`, `AbortObservationTests`; 18 globbed modules) that no ci step names. `scripts/ci` builds `golean` (which DOES include all 57 typed `GoCore` modules — `GoLean.lean:5 import GoLean.Interface`), `InterfaceTests` (`check-interface`), `AdmissionTests` (`check-admission`), `RecoveryTerminalTests` (`check-recovery-terminal`), `TestsData`, and the `gocore-eval-tests` executable (root `Tests.GoCoreEval`). The `import Tests.*` closure of those targets' 12 root modules reaches **26 of the 31** `Tests/*.lean` (computed by a Python fixpoint in this lane; a first shell attempt under-reached and was discarded) — so 14 of the 18 declared modules ARE built transitively (e.g. `Tests.RecoveryTyping` via `Tests/RecoveryTerminal.lean:2`). UNREACHED: `Tests.BooleanTyping`, `Tests.BooleanTypingAudit` (lib `BooleanTypingTests`), `Tests.BooleanInvariant`, `Tests.BooleanSafetyAudit` (lib `BooleanRuntimeTests`) | 4 of 31 `Tests/*.lean` (2 libs) | **LANDED (round 28, 2026-09-08 — pending merge)** — branch `land/typed-test-gates`; review MERGE-CLEAN with small fixes; residuals = §2.6 row T8.1 | the sprint's `scripts/check-{boolean-typing,boolean-runtime}` + `tools/{boolean-typing,boolean-runtime}-audit.py` + `tools/check-boolean-typing-artifact.lean` (and, for hygiene, the other five `check-*`/`*-audit.py` pairs so each declared lib has a named step), all at `typed-consumer-sprint:` and absent from main | L1's note §4.4 routed the gate scripts to "L2 (tooling)"; L2's note §2 routed `check-declarations` back to "L1"; neither landed the rest. Effect: the typed layer's DEFINITIONS and THEOREMS are gated by the core build, and most of its regressions ride the three landed steps; the Boolean profile's TYPING regression (`old_unbound_rejected`, the A3a counterexample), its axiom AUDIT, and the Boolean invariant/safety audit are declared but not built. A gate WIDENING (adds build minutes), never a weakening — §4.6 N6 |
| T9 | `typed-consumer-sprint` archive | @ `7edc298f` (96 commits; +30,425/−400 non-evidence) | 81 paths owed (51 code + 30 docs) | **ARCHIVE** (retained unmodified, `docs/ARCHIVE.md`) | the owed paths above and the 32 design/contract notes | the 2,159-file / 114 MB payload NEVER lands ([USER] 2026-09-07, relayed) |
| T10 | `review/project-audit-20260905` | @ `75dcb6d1` | 0 ahead | **LANDED** (ancestor; content = `docs/2026-09-05_project-gate-audit.md` + its evidence dir) | nothing | retire the branch pointer once `docs/ARCHIVE.md` names it (N7) |
| T11 | `storage-maintenance-20260906` / `-main-20260906` | @ `0560484e` (100 ahead; 2,551 files) / `521f4eca` (3 ahead) | — | **NOT REVIEWED (note only)** | — | landing plan §5: out of scope; both carry an `AGENTS.md` standing-deletion assertion rejected on the global no-standing-permission rule |
| T12 | housekeeping | `spec-parity-s1..s6` (stale slices of the MERGED `spec-parity`; `-s6` +18,268 over `2927085f`), `prep/observer-terminal-harness` (behind main), `typed-i1-json` = `typed-i1-envelope-review` | — | **SUPERSEDED** | nothing | delete candidates — a destructive records action → N7 |

**Addendum 2026-09-08 ([AGENT], `land/i1-declarations`) — T3.**
The L1b declaration boundary is assembled from fifteen selected committed
source/doc blobs at `typed-i1-json` @ `7ac3eb46`, with repairs and controls;
the core declaration module already on main is unchanged. No whole branch
or dirty prototype overlay is merged. The four selected design notes carry
historical headers. See the [source selection and validation
record](2026-09-08_i1-declaration-landing.md); production I1 remains outstanding.

**Landing addendum 2026-09-08 ([AGENT]) — T3.**
The L1b selection and review corrections are **LANDED** at `960ee230`;
§2.2's landing addendum and its evidence supersede the earlier branch status.
The remainder of the prototype is still outside this landing.

### 3.2 What to lift, concretely — by layer of the target (§1.2)

- **Language instance (1.2.1).** Nothing from the park; `spikes/gate-a1`
  is the live successor. From `LangD` take the DESIGN of the per-thread
  decomposition and the simulation target `stepM_erasedD`; from
  `channel-logic` take the theorem that the ∃-partner envelope cannot
  pin delivered values and its fix (cell-mediated carrier) — this decides
  the concurrent instance's shape before any code.
- **Memory + frame (1.2.2).** From `Frame/AllocIndep.lean` the statement
  of `allocatorIndependence` (the doctrine's register #6 theorem — the
  only copy); from `Lens.lean` (wave-a / kit) the Perennial `Access`
  field-lens shape for per-field points-to; from the corpus plan's
  G-REPR the route-(b) ruling (re-key at `(base, path)`) and the
  PRE-REGISTERED discriminating test (write one field under a sibling
  field's frame — «a candidate that cannot state and prove this is a
  reader-predicate in costume»); from the C1 handoff the
  sibling-normalization pitfall. A2's `Heap`/`Ghost` on main are the
  starting code.
- **Bind (1.2.3).** From `Laws/Bind.lean:170` the three premises as the
  first candidate `Admissible` class (check whether `mapIterFree` is now
  vacuous); from the corpus plan A5 the recorded fact that the
  `Context`-instance route is unavailable and the inverse decomposition
  is a NEW obligation.
- **Typed admission (1.2.4).** From `w1-prover`/`w3-init` the five
  judgment FORMS (Hoare triples with the tape as an explicit demonic
  parameter) as the shape of profile-level specs; from refined-cerberus
  the `fn_params`-shaped procedure-spec judgment (§3.3, the one design
  bug worth pre-empting) and the fail-closed partial classifier pattern
  (statement-view design). The A3 lineage on main (`Admission.lean`,
  `BooleanTyping.lean`, `RecoveryAdmission.lean`) is the code precedent.
- **Latitude (1.2.5).** From `campaign-ce` the `SpanIso` statement
  (choice-erasure as a relation, canonicalizer-free); from `w3-m` the
  `MapPerm` permutation-family design (never canonicalize — the quotient
  lives in the spec vocabulary); the [USER] ruling that killed
  `ChoiceCanon` («choice-invariance will just roll up into the reasoning
  layer»). These say how a RefinedGo states map-order-independent specs
  without a canonical order in the semantics.
- **Observations (1.2.6).** From `Surface.lean` the Iris-free `GoTriple`/
  `GoSpec`/`GoFuncSpec` vocabulary and `goSpec_of_wp` (the collapse) —
  the assertion-shaped half `Interface.lean` lacks; from the Verdi note
  §4e the "refinement relative to a driver contract" framing for
  library-boundary subjects.
- **Concurrency (1.2.7).** From `channel-logic-s4` the NPDRF refutations
  and `stepM_iff_fine_bs` (the s4 `NPDRF.lean` at 1,774 lines is AHEAD
  of main's 517 — the statement material, not the proofs); from
  `LangC` the fork rule; from the detector-soundness note the eight
  cell classes and the per-run claim's exact scope.
- **Automation (1.3).** `Tactics/GoWalk.lean` whole (603 lines, zero
  GoCore imports) — the algorithm-level Lithium precedent; the
  wp-design compute-and-emit principle; the reuse map's ADOPT list
  (`AddModal`/`ElimAcc` retiring the 393-site modality dance; `iinv`);
  `Sym`'s drift-theorem-as-build-target pattern for any evaluator the
  automation grows.
- **Gates (1.3, the customer's).** The judge/audit design whole (row 19)
  + A-TRIP (row 13): designated list, statement-TCB closure,
  kernel-replay judge, proof-term veneer tripwire, `proof-costs`
  report-only. Main has re-derived the axiom-audit half (the spikes'
  poisoned-import fixtures, `Tests/InterfaceAudit.lean`); it has NO
  veneer tripwire and NO designated list — both come due when the first
  designated theorem is stated downstream.

### 3.3 The external pitfall reference (cerberus-lean-proj / refined-cerberus)

`/home/dev/projects/cerberus-lean-proj` is readable; `refined-cerberus/`
is a subdirectory (own repo; `CLAUDE.md`, `docs/DECISIONS.md` 3,787
lines, `ARCHITECTURE.md` 1,074; six audit generations in a week). RSP §6's
15-row table (L1–L15) stands and is not repeated; read it first. What
this survey ADDS, each with its path (line numbers as read 2026-09-07;
the files are append-heavy — re-grep before quoting elsewhere):

1. **The referent rule** — `refined-cerberus/CLAUDE.md:95-102`: «The
   referent of every export is the genuine semantics: no hand-written
   definition (driver loop, discharge, scheduler) may appear in the
   statement of an exported theorem; proof devices … live in proofs
   only. A semantics-side limitation that blocks such a statement is
   REQUESTED from the [semantics] team … never worked around». GoLean's
   analogue: `run` = the shipped `runProgramPoolOutM`, never a second
   driver (RSP L1; A2's `execProgLoop_single`/`execProgLoopOut_snd`
   transfer already obeys it).
2. **Trust architecture in one sentence** — `refined-cerberus/CLAUDE.md:10-19`:
   the operational semantics is the ONLY trusted semantics; «no layer
   counts as capability until its downward theorem into the engine
   exists — the adequacy spine is load-bearing from the first rung».
3. **`EctxLanguage` failed for the same reason** — `docs/DECISIONS.md:360-388`
   (`Erun` discards its context; parametric interfaces «DEFERRED POSSIBLY
   PERMANENTLY»). GoLean: `recoverResult` reads the continuation (F3).
4. **The global environment belongs in the `Language` instance, not in
   a premise** — `docs/DECISIONS.md:310-340` (rejected: pinning
   `fmapEmpty` by a `M.tagDefs = …` premise — «a representation
   accident»). GoLean: B7's `ProgramCtx` as a section variable replaces
   A2's five `ContextEq` equalities.
5. **Masks hard-coded at ⊤ is a real ceiling for a RefinedC layer** —
   `ARCHITECTURE.md:233-241`; R/O audit `docs/2026-09-04_reynolds-ohearn-separation-logic-audit.md:263-301`;
   `KNOWN-OPEN-ITEMS.md:53` (B11). And the mask-placement gotcha in
   iris-lean's `wp.pre` vs `wps.pre` (`DECISIONS.md:598-602`) — solved
   there by a mask-generic `AtomicStep` spec lifted three ways
   (`ARCHITECTURE.md:256-264`) — the one genuinely reusable structure.
6. **A projection theorem, not a second logic** — `DECISIONS.md:447-467`
   (Iris triples project to plain memory/pure statements; iris-lean is
   proof machinery, not TCB) = RSP L14 = `Surface.lean`'s `goSpec_of_wp`.
7. **The recurring failure mode across six audits: claims run ahead of
   proof flow; instruments check NAMES, not DEPENDENCY EDGES** —
   `DECISIONS.md:251-264` (root cause R-04); R-01 the allocation rule
   unreachable from adequacy (every launcher initialized the cursor map
   empty) `docs/2026-09-01_cerberus-heaplang-skeptical-re-audit.md:170-242`;
   R-02 "production" examples bypassing the logic by hand-unfolding
   engine traces (`:244-296`); R-03 the 1,943-line hand-written mirror
   never bridged (`:298-341`); R-04 the capability gate validating that
   a theorem EXISTS, not that a consumer depends on it (`:343-376`);
   def-level `sorry` passing every gate (`docs/2026-08-31_heaplang-merge-audit.md:160-173`;
   `DECISIONS.md:687-696` — a planted `private theorem plant : True := by
   sorry` passed because sweeps skipped `isInternalDetail`); the
   normative architecture doc itself overclaiming (`…audit-response-re-review.md:284-311`);
   an audit transcript that did not reproduce (`:336-351`); 117 `panic!`
   arms read by the kernel as `Inhabited` defaults, invisible to axiom
   sweeps (`ARCHITECTURE.md:604-629`). GoLean has hit four of these
   independently (A1 R1's in-module audit gap; the poison fixtures; Gobra
   §10b/§10d's vacuity; the referent rule) and has two still ahead: the
   fragment/NO-RULE residual as a first-class tracked artifact, and the
   procedure-spec judgment shape (item 12).
8. **Gate overcorrection is itself a pitfall** — `DECISIONS.md:265-283`:
   «we want to build speedbumps» (= memory `gates-are-speedbumps`).
   Fresh-eyes reviewers, never same-reviewer delta convergence
   (`:510-523`); charter defects blocked four Codex runs — «CHARTER
   DEFECTS of the orchestrator, not work failures» (`:3573-3586`); a
   launch text is handed over only after the worktree contains every
   file it names (`:3695-3709`) — directly relevant to §4.4.
9. **The fragment as a first-class artifact** — `Frag`, a 35-constructor
   fail-closed syntactic predicate «declared as exactly what the mirror
   covers» (`ARCHITECTURE.md:105-122`), with a tabulated NO-RULE list of
   24 in-fragment engine-accepted shapes with no proof rule
   (`:981-995`) that the capability manifest nonetheless reported as "0
   red"; mirror-completeness as a standing per-arc obligation
   (`DECISIONS.md:748-777`, `:816-827`: «a carefully characterized
   boundary that is fail-closed outside the boundary»). GoLean's
   `Admission`/`BooleanTyping`/`RecoveryAdmission` profiles are this
   shape; what is missing is the NO-RULE table for the machine-wide
   profile (§2.1 A3).
10. **The referent dialect** — `docs/2026-09-04_emitted-core-dialect-design.md:21-26`
    («the RAW elaborated Core, not the sequentialised one»); the gap
    measurement (`…gap-measurement.md:108-117`) showed even trivial
    programs need constructs the trigger note undercounted by three.
    GoLean's analogue is the wire's positive declarations (I1) and the
    lower-diagnose census: the profile must be measured against real
    programs, not asserted.
11. **Latitude reification retrofits can invalidate laws proved
    earlier** — `DECISIONS.md:3053-3070`: adding the fresh-symbol supply
    (`Step.neg_bound` drawing from `Ctl.sup`) retroactively made an
    already-designed frame rule UNSOUND («SOUNDNESS CATCH before landing:
    the E4-era `wps_bound`/`wpt_bound` would have been UNSOUND at the E5
    fragment», `:3063-3067`). GoLean: any frame/bind law proved before a
    re-envelope (E7, R3, E3/E4, BUG-101's value axis) must be re-checked
    when the site lands — the tape is part of the semantic contract (C1
    handoff). Also: `Eunseq` mirrored as the driver executes it, with a
    SHARED-READS/DISJOINT-WRITES rule whose side condition «literally
    mirrors the engine's own join-time race criterion» (`:158-182`,
    `:2839-2900`) — the F6 family model has a precedent.
12. **The procedure-spec shape bug** — `docs/2026-09-04_refinedc-layer-design-2.md:149-176`:
    `ProcSpec := sym → List value → IProp × (value → IProp)` cannot state
    a spec whose logical variable is not determined by the argument
    values («`reverse(p)` … cannot be stated»); the fix is the
    `fn_params`-shaped `Σ (A : Type)` judgment. Cheap to get right in the
    interface document now, a rewrite of the customer's base later.
13. **RefinedC/Lithium scope rulings there** — `DECISIONS.md:882-900`
    («we only want to adopt refinedC inasmuch as it supports our goal of
    agent-driven formal verification for very large bits of software»);
    `refinedc-layer-design-2.md:30-32` («RefinedC's DESIGN IS A
    TIEBREAKER, NOT A CONSTRAINT»); the adopted slice (`:69-76`: types as
    spec vocabulary, the syntax-directed judgment over `wps`,
    `fn_params`-shaped procedure specs, «a Lean 4 goal-directed executor
    implementing Lithium's ALGORITHM … not Caesium, not their memory
    model, frontend, concurrency»); Lithium «algorithm yes, engine no»
    (`:708-726`: Ltac2, the `i2p` instance encoding and evar-sharing are
    not reusable; Lean 4 `MetaM` replaces them). Prerequisite they found:
    the fuel restatement must land BEFORE the layer, or its base is
    rewritten twice (`:242-248`).
14. **Pinning discipline (they are the consumer; we would be the
    pinned)** — one-way Lake pin (`docs/2026-08-29_rules-of-engagement.md:40-56`);
    read-only re-pin SCOUTS before every pin move (`docs/2026-09-03_repin-scout.md`,
    `repin-scout-2.md:38-39`: exported statements whose text must change
    — 1); divergences FILED as dated request notes, never patched
    (`docs/2026-09-03_upstream-note-dynamic-addrs.md:37-60`); an upstream
    defect register separate from own open items (`KNOWN-OPEN-ITEMS.md:27`
    §A); staged re-pins, «each re-pin is one audit range»
    (`docs/2026-09-04_response-concurrency-S1-interface-review.md:123-129`);
    error constructors must carry kernel-transparent data, never free
    text (`:58-69`) — GoLean's `Refusal.unsupported (feature : String)`
    is free text; a RefinedGo that wants to REASON about refusals will
    ask for a structured constructor. The one theorem they insisted the
    semantics team prove: sequential/SC driver agreement on `Epar`-free
    programs (`:87-104`) — the analogue is our `execProg_single_eq_execStmt`
    (LANDED) and the single-goroutine face of D1.

### 3.4 What the survey could not determine (stated, not hidden)

- Whether ANY parked or unlanded module compiles against `main`: no
  build was run (by the brief). Expectation from the drift figures:
  essentially none unmodified; the statements transcribe.
- `LangC`/`LangD`/`FastEval`: UNKNOWN pending a constructor-level diff of
  `StepM` (park vs main) — not done.
- Whether `wp_plug_bind`'s `mapIterFree` premise is now vacuous: needs
  the rule restated and re-proved.
- The size, state and buildability of the UNCOMMITTED B7, I1-V2 and
  `ByteArrayStore` working trees (`.claude/worktrees/typed-{context-store,
  i1-envelope,byte-runtime}`): not entered; the only evidence is the
  pause-state's second-hand numbers.
- The `design-pass` N-1 approval contradiction (§3.1 row 14).
- The exact park `Step` count (≈155) is bracketed by `sed`; the corpus
  plan independently says 155.
- Whether the seven proof-gate scripts' omission (T8) was a deliberate
  exclusion: no tracked record dispositions them; classified as an
  unrecorded gap.
- RefinedC/Lithium/Diaframe/RefinedRust applicability: NO local checkout
  was evaluated by any in-repo document (the reuse map says so); §1.1 is
  from the author's knowledge; the corpus plan's "road not taken" is the
  only in-repo position, and refined-cerberus's slice rulings (§3.3 item
  13) the only sibling position.

---

## 4. Layering and sequencing

### 4.1 The dependency graph — from GoLean exports to a RefinedGo

```
THIS REPO (exports; §2 row ids)                          DOWNSTREAM (customer; in-repo only as the spike)
─────────────────────────────────────────────            ──────────────────────────────────────────────
R1 B7 ProgramCtx/Store ─┬─► R2 C1 Mem + trace ─┬─► R3 P ─► R4 C3 List Frame (ergonomics; RULED before the pin)
                        │                      ├─► path-level frame lemmas ─────────► points-to at ShadowKey leaves; own_struct/own_slice/own_map
                        │                      ├─► detector = fold over trace; RacyFine over traces ─► race-freedom as a typing consequence
                        │                      └─► Event.access ──────────────────────► Iris Obs := Event (picks ∪ accesses ∪ out)
                        └─► Store as Iris State; ProgramCtx section variable ────────► Language instance v2 (adapter re-cut; A2 rebuilt)
A2 Admissible class + step_fill_adm/inv ─────────────────────────────────────────────► customer bind lemma ─► Lithium-style engine (go_walk lineage)
A3 WireWellFormed / ProgramWellTyped / entry / support; Inv.step machine-wide ───────► NotStuck domain; typing-rule premises; refusal-freedom
A4 step_det_of_choiceFree ───────────────────────────────────────────────────────────► sequential refinement ("some run → every run"; cedarGo_refines)
A1 F2 relation→driver bridge ────────────────────────────────────────────────────────► adequacy through `run`, ∀ ch
A6 observation contract (FR-32; Iris-level Obs) ─────────────────────────────────────► panic/output postconditions
B1 F6 eval-order model · B2 F7 identity · BUG-099/101/104 ───────────────────────► "zero known wrong answers in the profile" (Gate B)
A7 typeDesc algebra ─► P3 G6 T1 ─► T2 (after P) ─► G6-4 fmt (needs G7) ─► T3 ─► G6-5 json ─► P4 cedar driver (Gate C)
P1 F8 · P2 F9 ───────────────────────────────────────────────────────────────────────► Gate C evidence
A8 Gate D SEQUENTIAL criteria (PENDING [USER]) ═════════════════════════════════════► SEQUENTIAL PIN OFFER
D1 reduction repair → proof | explicit assumption · D1(ii) reference event model · D2 detector sound/complete · D3 BUG-002 · D4 concurrent instance (LangD shape; cell-mediated) ═► CONCURRENT PIN OFFER
```

What the graph says that v1 §5.1 did not: the contract items (A1–A4)
are NOT downstream of C3 — they are statable and provable over today's
representation and RULED to be REGRESSION TESTS across B7/C1/C3 (Gate A1
contract, "Consequences" 1); C3's place is ergonomics before the pin,
not the source of any law.

### 4.2 The two critical paths

**(i) To a SEQUENTIAL pin offer** (Gate D, first release):

1. **Name the profile** (PENDING [USER]; §4.6 N5 proposes one). Nothing
   below can be stated exactly without it.
2. **B7** (R1) — the hinge: `Store` as the Iris state, `ProgramCtx` as
   the section variable; every later statement changes shape if it
   lands later. Salvage-or-restart decision N1 first.
3. **C1** (R2) — `Mem` + trace; the two path-level frame lemmas; the
   detector as a fold (needed even sequentially: the singleton pool runs
   `raceUpdate`, F2).
4. **Gate A proper** — A2 (class + laws), A4, A1 (relation→driver), A6's
   Iris-level `Obs`; the adapter re-cut over B7/C1 and A2 rebuilt as the
   live test (its five `IndependentB7Review` theorems as acceptance).
5. **F5 for the named profile** (A3) — the long pole; XL; Codex-suitable
   once the type system is designed.
6. **Gate B** for the profile — BUG-104 fix lane, BUG-099 owned,
   BUG-101 decided inside the F6 note, F7's identity metadata if the
   profile includes multi-package code.
7. **P, C3, C4** as RULED (representation; C3 «before the pin, never
   after»; C4 «last C-item before the interface module») — sequenced
   before the pin by their rulings, not on the contract's truth path.
8. **A8** — the Gate D sequential criteria written and ruled; the
   interface DOCUMENT with its final shape; `Interface.lean` re-exporting
   exactly its names; the open-ended assessment re-run; the pin offer.

**(ii) To a CONCURRENT pin offer**, additionally: D1's statement repair
(a reviewed decision — decision 1's "NPDRF proof investment" comes due
here, not at G-PIN as v1 §5.4 placed it), D1(ii)'s reference event model
at Go's access granularity, D2's detector soundness/completeness over
C1's trace (with U2/BUG-041 scoped), D3's BUG-002 granularity ruling,
D4's concurrent instance (per-thread, cell-mediated — the channel-logic
finding), the relevant Q-rows (Q-SELSEL, Q-COND, Q-GOEXIT for a profile
that uses them), and — if the reduction is not proved — the DRF-SC
transfer stated as an explicit assumption of the pin (Gate D allows a
knowingly conditional contract; it is a different release from a
trustworthy Go-transfer guarantee).

Not on either path: G6 beyond what the workload needs; FR rows outside
the profile; the raft twin (a wire pin); the legs' cadence.

### 4.3 The recommended next wave ([AGENT]; consistent with the coordinator's, as relayed)

Each item is a lane with its own gate and audit ask; none is launched by
this document; the order within the wave is a coordinator call.

| # | lane | what | exit |
|---|---|---|---|
| W1 | **Gate A bridge spike** | A2's `Admissible` class DEFINED (starting from `Bind.lean:170`'s three premises; check `mapIterFree` against main) and `step_fill_adm`/`step_fill_inv_adm` PROVED over the 112 rules, the recover counterexample as the first negative test, nested defer/recover + labelled control + frame-local allocation as worked examples; A4 `step_det_of_choiceFree`; the STATEMENT of A1's relation→driver bridge fixed (proof deferred to after B7 if the state type would move under it) | theorems compile in the core build; `Tests/InterfaceContract.lean` gains the class's negative and positive regressions; `Interface.lean`'s docstring updated; no `EctxLanguage` claimed |
| W2 | **B7** | N1 decided; then the design note's target API implemented at ZERO baseline drift and byte-identical whole-corpus consumption trace; both spike gates green; T1's five review theorems proved against the landed API | `grep ProgramCtx GoLean/` is the API, not a comment; `htypes` hypotheses gone; `Platform` threaded; both customers rebuilt |
| W3 | **Owed small chunks** (§2.6 + T8) | `land/typed-test-gates` (N6) — **LANDED (round 28, 2026-09-08 — pending merge)**, the I1 wire (L1b, with A-R11/A-R12), `observer-gate-scripts`, `observer-fd-channel` (if BUG-107 (c)), the spike gate re-run, the `canonicalSlot0` docstring, the 32 sprint notes (records) | each its own gate; 5a where `NativeToIR.lean` moves |
| W4 | **Fix lane** (v1 §7.4 item (3), retained) | **FR-31/BUG-098 DONE on branch, awaiting review** (2026-09-09 [AGENT]; I1 member identity + matching + distinct promoted targets, three reds green, fresh Cedar census); BUG-104 `safeExpr`-style decomposition; the decoder `.getD .int` fallback (`NativeToIR.lean:1507,1584`); F8's certificate fingerprint | the 3 + 5 rows PASS; the BUG-098 guard retires; cedar `all` revives; stale certification is release-blocking |
| W5 | **Design notes before lanes** | F6 (with BUG-101's value axis decided inside), F7 (with C6 revisited), A7 the type-descriptor algebra, the profile-naming proposal (N5), the D1 statement-repair note (§4.4 item 1, deliverable 1) | each a note + a posed [USER] gate; no lane launches on a note that has not been ruled |
| W6 | **Codex deep theorems** (§4.4) | the items whose statements are FIXED now: A4, R8's bound-irrelevance, C2's bound theorem, §4.4 items 4 and 5; after C1: the `Mem` frame lemmas, D2; after D1's ruling: the reduction proof | per-item criteria in §4.4 |
| HOLD | G6 T1 (pending A7 — PENDING [USER] confirmation); raft W4 stage 2 (PENDING [USER]); P/C3/C4 (after C1); B6 (coordinator/[USER] slot); B5 (any time) | | |

**Addendum 2026-09-08 ([AGENT], `land/i1-declarations`) — W3.**
[USER] authorized the I1 declaration-boundary chunk in this session; the
[charter](2026-09-08_i1-declaration-landing-charter.md) records the firsthand
instruction. L1b is implemented on its worktree branch with a green full
candidate gate; final certification and review disposition are recorded in
the linked landing note. No other W3 chunk or production I1 work is included.

**Landing addendum 2026-09-08 ([AGENT]) — W3.**
The I1 declaration-boundary chunk L1b is **LANDED** at `960ee230` after
two independent reviews and explicit [USER] sign-off (see §2.2). The other
W3 chunks retain their statuses; R10 is the newly queued fixture-pin follow-up.

### 4.4 The Codex-suitable deep-theorem list — statements and acceptance criteria

The track exists by [USER] direction (§0.1's second quote: deep theorems
with clear specs, resistant to goal-drift, separated from the mainline).
Discipline for any external prover agent (drift-resistant by
construction; the discipline itself is PROPOSED [AGENT] — the
coordinator's reading, relayed: «exact theorem statements, additive
modules only, no edits to mainline-owned definitions, kernel-checked
acceptance, own branch, ordinary audit+train; write a one-page spec per
item before handing it over» — and a [USER] decision, N2): the STATEMENT
is fixed in the brief by definition names + `file:line` at a named main
SHA, and may not be weakened; ADDITIVE modules only (new files beside the
core, never edits to mainline-owned definitions); work in its own
worktree/branch off `main`; NO edits to the trusted surface (`GoLean/GoCore/StepFn.lean`,
the `Step`/`StepM` rules in `Machine.lean`/`Multi.lean`, `NativeToIR.lean`,
`tools/nativefrontend/`, `scripts/`, `baselines/`) unless the item says
so — a counterexample to a statement is a BUG entry or a finding, never
a definition edit; no `sorry`/axioms/`native_decide`; gate =
`scripts/capped scripts/ci --diff` green (docs-only or proof-only
changes still run it) + the audit ask; a statement it cannot prove is
reported with the blocking lemma or counterexample. The brief is handed
over only after the worktree contains every file it names (§3.3 item 8).

| # | theorem / deliverable | statement (fixed) | acceptance criterion | deps |
|---|---|---|---|---|
| 1 | **NPDRF reduction — STATEMENT REPAIR FIRST** | (a) `theorem npdrf_draft_refuted` — a kernel-checked refutation of `NPDRFReduction` (`GoLean/GoCore/NPDRF.lean:438`) on the obstruction-4 program (main spawns two sync-free goroutines and returns), as a regression in `Tests/`; (b) `def NPDRFReductionV2 : Prop` beside the draft, scoped to the OBSERVABLE PROJECTION (`Pool.Observation` of `ProgramTrace.lean` — readout + terminal + output, not the whole pool), with obstructions 1, 5, 6 restated against it; (c) a design note posing the weakening as the [USER] gate (decision 1) | (a) compiles and is cited from the NPDRF header; (b) is REVIEWED (audit ask) and RULED a target before any proof; nothing cites V2 as proved; (d) SECOND deliverable, after the ruling: the proof, or its reduction to named mover lemmas (C1's path-level frame) with each remaining obstruction a named hypothesis | (a)–(c) none; (d) C1 |
| 2 | **go_mem HB detector soundness/completeness** | `def GoMemRace : Trace → Prop` — go_mem's happens-before over the memory model's synchronization rules (spec pin go1.26.5, `docs/spec-sources.md`) on C1's emitted trace; `theorem detector_sound : RaceState.fold tr = .refused → GoMemRace tr` and `theorem detector_complete : GoMemRace tr → RaceState.fold tr = .refused` for the in-scope kinds (data, mutex, RWMutex, chan send/recv/close, WaitGroup, atomics per `Race.lean`'s inventory), with U2 and BUG-041 as EXPLICIT exclusions and BUG-084's UNION rule as a NAMED widening | both directions for the supported kinds; a table mapping each go_mem synchronization rule to the lemma that realizes it; `scripts/detector-soundness --select in-scope` still HOLE 0 | C1 (before C1 the statement is over `stepAccesses` and is about the TABLE — obstruction 5) |
| 3 | **Checker fragment widening** | `checkCert_slowObs` (`GoLean/GoCore/EnumDedupSound.lean:915`) restated over `Pool.Observation` INCLUDING the output prefix and terminal (today the engine refuses output-bearing execution rather than certify it — gate audit "Scope and evidence") | the widened theorem; the engine REFUSES BY NAME outside the widened fragment; `scripts/ci --slow` at the tip: certified set identical or a FINDING (never a re-pin) | none |
| 4 | **`FloatBits` vs IEEE 754** | a Lean specification of IEEE-754 binary64/binary32 round-to-nearest-even (`roundRNE : ℚ → Bits` for finite results; overflow/underflow/subnormal per the standard; NaN/∞/signed-zero policy STATED per latitude rows R4 per-op rounding and R7 canonical NaN) and `theorem FloatBits.add_spec : finite a → finite b → add a b = roundRNE (toRat a + toRat b)` (likewise `sub`, `mul`, `div`, `sqrt`, the int↔float conversions) against `GoLean/GoCore/FloatBits.lean`'s definitions UNCHANGED | the theorems for the five basic ops + conversions; `Tests/FloatVectors.lean` (33,004 hardware-oracle vectors, seed 20260805; regenerated by `scripts/ci`'s derived-artifacts step) unchanged; a counterexample = a BUG entry (BUG-094's canonical-NaN refusal is a LATITUDE row, not a target) | none |
| 5 | **Named-cases refactor of `MachineSound`** | `stepFn_sound` (`MachineSound.lean:172`), `step_complete` (:506), `stepMulti_sound`/`stepM_complete` (`MultiSound.lean:1172/1316`) re-proved with NAMED cases (or a per-constructor lemma table) so that adding a `Step` rule adds exactly one obligation — the `.probeK` traveller-arm debt (v1 §3.A "Owed") is the motivating instance («every added arm shifts `MachineSound`'s positional case tags; three theorems broke») | `git diff` shows NO statement change; the proofs compile; a documented scratch experiment (not landed) adds a dummy rule and breaks exactly one new obligation; `Machine.lean`/`StepFn.lean` untouched (the coherence proof is editable, the interpreter is not) | **after B7** (the coordinator's sequencing, relayed: B7 restates every `MachineSound` theorem over `ProgramCtx`/`Store`; refactoring the cases before it would be redone). Note this item EDITS `MachineSound.lean`, an existing module — an exception to "additive only" that the brief must grant explicitly |
| 6 | **Typed admission for the named profile** (§2.1 A3) | in order: `WireWellFormed` + the decoder theorem; `ProgramWellTyped` + `Inv.step` preservation over ALL 112 rules restricted to the profile; progress; `run_refusal_named` for the profile | the typed-contract review's anti-tautology rules (`docs/2026-09-05_typed-contract-design-review.md`: the invariant is not "reachability"; refusal is not a fourth success class; bounds are not circular); checker soundness AND completeness as the two profiles have; the NO-RULE table (§3.3 item 9) published with the profile | N5 (profile named); the type-system design note; I1; B7 |
| 7 | **F2 relation→driver bridge, after B7** (§2.1 A1) | `∀` labelled `StepsM` trace (picks + accesses + out) from `init P e a` reaching a `Pool.Observation` o, `∃ ch fuel, run P e a fuel ch = .obs o` — with the composition argument for per-step stream witnesses (the audit's explicit warning), initialization, terminal priority, main-exit and output accounted; the TYPED two-choice bridge on `Tests/RecoveryTyping.lean`'s `repanicProgram` as the regression | proved for `StepM` including `StepM.abort`'s pick; `Interface.lean`'s «no converse to erasure is supplied» sentence DELETED as a consequence, not edited | B7 (state type), C1 (`Event.access`) |
| S | small, statements fixed now | A4 `step_det_of_choiceFree` (RSP §1.4 shape); R8's bound-irrelevance (`types.WellFounded → i < b → i < b' → defaultValueAt types b i = defaultValueAt types b' i`); C2's bound theorem (`c-arc-c2` §8); after C1: `Mem.load_after_disjoint_store`, `Mem.store_store_disjoint` at PATH level (the sibling-normalization pitfall in the statement) | compile; `Tests/` regressions; no statement drift | B8 (landed); C2 (landed); C1 |

### 4.5 Calendar points

- **Now, before any storage maintenance touches `.claude/worktrees/typed-*`:**
  N1 (salvage the uncommitted B7 / I1-V2 / `ByteArrayStore` trees to
  branches, or accept their loss). The disk-growth review
  (`docs/2026-09-06_disk-growth-review.md`, untracked in the primary
  checkout) proposes cleanup manifests; those trees are in its blast
  radius.
- **Step 5a** at the first train touching `wire.go`/`NativeToIR.lean`:
  the I1 wire (L1b), FR-31, B6, P, `uintptr` (b) all will.
- **Decay reviews:** D-002 (fmt shims) 2026-10-31; D-001 2026-11-30.
- **go1.27 pin move:** when it ships (runbook OWED, v1 §4 item 7).
- **Assessment re-run:** open-ended, after Gate A's statements exist and
  B7/C1 land — not "after I5" (v1 §5.3 superseded).
- **Next independent whole-project review:** at the sequential pin
  offer (v1 §4 item 12's proposal); §5.2 is its brief.

### 4.6 Decisions the [USER] must make

Carried (each already posed in a tracked record; none presumed):

| decision | default in force | where posed |
|---|---|---|
| **D1** `uintptr`: (a) record per w7 J-8 / latitude R1, red-first rows, observations stay refused; (b) fix with records amended, third-lane review, real full + `--slow` | HELD, nothing built | landing plan §2.5/§4; §3.1 T4 |
| **BUG-107** option: (a) keep the four pre-`main` rows red; (b) named exception from raw bytes (auditor recommends against); (c) variable-initializer hook over the fd-passed channel (RECOMMENDED [AGENT]) | (a) | `docs/BUGS.md:6451-6547`; L4 note §3 |
| **D3** coverage worker count (no verbatim "2 workers" ruling exists in any tracked file) | ≤ nproc/2, recorded per run | landing plan §4 |
| **D6** record K4 («merges to main are always user-approved…») in `CLAUDE.md`? | not landed | landing plan §4 |
| **D7** the evidence caps (256 KiB / 4 MiB / no archives / no source copies) | in force as proposed (gate-enforced) | `scripts/check-evidence-size` header |
| E2/E12 value-axis gate (BUG-101) — now posed WITH the F6 note (W5) | (b) pin, red rows | v1 §3.D item 2 |
| C6 §5.1-item-1 narrowing — now posed WITH the F7 note (revisit, not ratify as-is) | narrowing in force as [AGENT] | v1 §3.B item 18 |
| G7 primitive-cap re-ratification (`os.Exit`, `os.Stdout/Stderr`); overlay-import cap 8; G3 anchor widening | caps as coded | v1 §3.C items 7, 11 |
| periodic legs cadence (gotest / grossmith / sweep / 386 / P4) or "on demand" | on demand de facto | v1 §3.E item 2 |
| baseline-header narrative out of the header; the guarded-wrong-answer marker | header as is; prose only | v1 §3.I item 1; §3.G |
| BUG-061 / L-011 `callinit` init order: envelope or permanent pin | red-first pin | v1 §3.G |
| restart raft W4 stage 2 | parked («we're not running Raft right now», 2026-09-03) | v1 §3.H |
| `nonterm=` under `engine=dedup` (OQ5); second toolchain install (machine-global) | — | `TODO.md:352-358`; `oracle-legs.md:102-110` |
| migration-stage decisions (repo name, dependency mechanism, history strategy, `raft-proof-campaign` disposition) | — | split plan "Deferred" — come due at the sequential pin |
| NPDRF proof investment (fidelity decision 1) — now framed as the §4.4 item 1 statement-repair ruling | draft uncited | `docs/assessment/decisions-2026-08-31.md` |
| F1 predicate 2: NAME the supported profile | none named | v1 §7.3 |
| Gate D's revised G-PIN criteria (A8) | G-PIN's original four conditions, known-insufficient | RSP §5.4 addendum |
| the HOLD on G6 T1 pending the type-descriptor algebra (A7) | hold in force as [AGENT] | v1 §7.4 item (4) |
| disk-growth review: one cleanup manifest + a narrow lifecycle policy | nothing authorized | `docs/2026-09-06_disk-growth-review.md` (untracked) |

New, raised by this document (PROPOSED [AGENT]; each a [USER] call):

| # | decision | [AGENT] recommendation |
|---|---|---|
| **N1** | B7: resume from the UNCOMMITTED `typed-context-store` working tree (first action: commit it to a branch, records-only, so it exists) or restart from the design note; and whether the I1-V2 and `ByteArrayStore` trees are committed for the record before any storage maintenance | commit all three to branches now (a records action; touches other lanes' worktrees, hence the ask); then restart B7 from the design note using the committed tree as a quarry and `IndependentB7Review.lean` as acceptance |
| **N2** | Codex engagement: which of §4.4's items, in what order, under the discipline stated there (one-page spec per item, handed over only when the worktree contains every file it names); who reviews (fresh eyes, never the author) | item 4 (FloatBits — statement fixed, no deps, purely additive) and the S items first, then 1(a)–(c) (the statement repair, additive beside the draft); item 5 after B7; items 2, 6, 7 after their deps |
| **N3** | Whether the in-repo spike may grow toward a RefinedGo PROTOTYPE (types-as-Iris-predicates over `GoValue` + a `go_walk`-lineage engine over the A2 customer's rules) as the «thin enough customer layer» test, or whether the reasoning repo is created now | grow the spike ONE step (a refinement type for `bool`/`int64` + one ownership type for a struct, typed through a bind-free rule set over the Boolean and recovery profiles) — the smallest test of whether the interface fits a RefinedC-shaped customer; the repo decision stays at the pin |
| **N4** | Is A1's relation→driver direction REQUIRED for the sequential pin, or may the sequential pin ship with the driver-side bridges + the `∀ ch` typed theorems and the converse as a NAMED assumption? | required for the pin; permitted as a named assumption for a labelled experimental snapshot before it |
| **N5** | The first named profile (F1 predicate 2; A3's domain). Proposal **SEQ-1**: single goroutine (no `go`, channels, `sync`, atomics), allocation-succeeding runs, `gcAmd64`, no `unsafe`/`reflect`/cgo/complex/`goto`, source-through stdlib only (no shims), panics observed at the first line, membership rows' sets as the only latitude assumptions | ratify or edit; every §2 row then says whether it is inside SEQ-1 |
| **N6** | `land/typed-test-gates` (T8): land the sprint's proof-gate scripts and audit tools so the four unbuilt `Tests.*` modules (`BooleanTyping`, `BooleanTypingAudit`, `BooleanInvariant`, `BooleanSafetyAudit`) run in `scripts/ci`, and every declared test library has a named step (a WIDENING; adds build minutes) | adopt — **LANDED (round 28, 2026-09-08 — pending merge)**: adopted by [USER] authorization 2026-09-08 (§2.6 addenda); residuals = §2.6 row T8.1 |
| **N7** | Retire stale refs: `spec-parity-s1..s6`, the duplicate name `typed-i1-json`/`typed-i1-envelope-review`, the `review/project-audit-20260905` pointer (after `docs/ARCHIVE.md` names it), `prep/observer-terminal-harness` | retire (deletion is destructive — [USER] only) |
| **N8** | The iris-corpus plan's N-1 approval: confirmed as `05e81b70` claims («[USER]-approved 2026-08-28»), or still awaiting as `design-pass`'s tip says? | a one-line provenance clarification in `docs/ARCHIVE.md`'s park entry |

---

## 5. Provenance and maintenance

### 5.1 Landing record

- Written in worktree `.claude/worktrees/master-plan-0907`, branch
  `master-plan-0907`, off `main` @ `da0a9c2c`, 2026-09-07, [AGENT] author
  under the [USER] commission of §0.1 (relayed). Records-only change
  set: this file; a one-line dated pointer at the top of
  `docs/2026-09-05_master-plan.md` stating what v2 supersedes.
  `docs/ARCHIVE.md` indexes branches and snapshot refs only (checked:
  no live plans) — no entry added. `CLAUDE.md`/`AGENTS.md` NOT touched
  (the parallel lane `agents-alias-0907` owns them; the pointer to v2
  from the charter is that lane's or the train's to add).
- Five read-only surveys were delegated (the park branch; the pre-split
  feature branches; the `typed-*`/review/storage branches; the
  cerberus-lean reference + the main-side design notes; the fidelity
  state — bugs/latitude/ledger/doctrine) and their numbers re-derived or
  spot-checked here where cited; where a survey's figure was corrected
  (the `Step` count's range artifact, the "ungated modules" scope, the
  2026-08-09 notes' location, the corpus plan's location) the corrected
  figure and its command are what appear above.
- Numbers this lane could NOT derive: whether any parked module compiles
  (no build run, by the brief); the uncommitted worktrees' contents
  (not entered); the park's exact `Step` count (≈155, bracketed);
  session sizes anywhere ([AGENT] guesses, v1's quoted as refactoring
  estimates only); the RefinedC/RefinedRust facts of §1.1 (author's
  knowledge, no local artifact re-read).
- Gate at the committed tip: recorded in the addendum below once run
  (`scripts/capped scripts/ci --diff`; `scripts/check-evidence-size`;
  `python3 tools/reconcile-records` — 2 findings, 0 HIGH, before this
  document: C13 1 site, C5 FR-7 `=`).

### 5.2 Brief for the next independent review

In a fresh worktree off `main` with `scripts/setup-deps --from <sibling>`:

1. **Re-derive the snapshot** (§0.4): the awk tally; `git log -1 main`;
   `git rev-list --count origin/main..main`; the `ChoiceSite` and `Step`
   counts with the commands given (not a per-line grep for the former).
2. **Run the gate** (`scripts/capped scripts/ci --diff`, TMPDIR inside
   the worktree); read every step and the `RESULT` line; confirm
   `git_dirty=false`.
3. **Test §2's statuses**: for every LANDED pointer, `git show`/open the
   `file:line` and confirm the theorem name and statement shape; for
   every OWED item, `git grep` that the named definition does NOT exist
   on main (e.g. `git grep -n 'Admissible\|step_fill_adm\|step_det_of_choiceFree\|WireWellFormed\|ProgramWellTyped\|NPDRFReductionV2' GoLean/` → nothing);
   for every RULED item open the record pointer and find the relayed
   [USER] quote; for every PROPOSED item confirm no ruling is claimed.
4. **Test T8** (the unbuilt test modules): re-run the `import Tests.*`
   closure from the ci-built targets' roots (expect 26 of 31 reached);
   confirm no `scripts/ci` step names `BooleanTypingTests` or
   `BooleanRuntimeTests`; then `scripts/capped lake build
   BooleanTypingTests BooleanRuntimeTests` and report whether the four
   modules build at the tip (this lane did not build them).
5. **Test §3's structural fact**: `git merge-base --is-ancestor
   park/reasoning-2026-08-31 main`; the seven non-ancestor pre-split
   refs; `git grep -c 'Heap\.set\b\|coerceStoredValue\|HeapWf\|pruneIterFramesKey' main -- GoLean/`.
6. **Probe the honesty-critical surfaces**: `decide (StateWf illTyped)`
   still `true` (F5); `recoverResult` under an appended `panicResumeK`
   (F3) via `Tests/InterfaceContract.lean`; `NPDRFReduction` uncited
   (`git grep -n NPDRFReduction GoLean/ Tests/` → the def and its
   header only).
7. **Report** with the same discipline: every claim with its command or
   `file:line`; every disagreement with this document as a numbered
   finding; no verification claims.

### 5.3 How this document is amended

Dated addenda at the end of the affected section, never silent edits;
[USER]/[AGENT] provenance on each; a status word changes only with its
evidence pointer; a number changes only with its derivation re-run and
re-stated. When a landing note and this document disagree, the landing
note wins and the disagreement is an addendum here. When v1 and v2
disagree on a §0.5-superseded item, v2 wins; on anything else, v1 wins
and the disagreement is filed.

**Addendum 2026-09-07 ([AGENT], lane `master-plan-0907`) — the gate.**
`TMPDIR=$PWD/.tmp/ci GOLEAN_COVERAGE_JOBS=12 scripts/capped scripts/ci
--diff` was started at the committed tip `3b56809a` (this file + the v1
pointer over `main` @ `da0a9c2c`); while it ran, this file received the
docs-only edits recorded in the follow-up commit (§0.1's second [USER]
quote, §4.4's discipline paragraph and item-5 sequencing, N2, the §0.4
L1 breakdown), so the gate CERTIFIED THE WORKTREE STATE, NOT A COMMIT —
its own words, verbatim: `note baseline diff FULL (3654/3654, no
regression) but recorded on a DIRTY tree (git_dirty=true) — certifies
that worktree state, not a commit`. The tree it certified differs from
`3b56809a` only in this document's prose. Tail, verbatim where quoted:
`RESULT: PASS`, `exit=0`; 27 steps `ok`, 0 `FAIL`; `differential
coverage summary: cases=3654 pass=3403 fail=251 export_status=0`;
`baseline diff FULL (3654/3654, no regression)` (dirty note above);
negative baseline diff matched (394); `check-frontend-pins: ok
[hidden-dep-order]`, `ok [twin-wire] — fresh emit = pinned wire
(758110a3f5a2…)`, `ok [stdlib-pin] — 61 lowered stdlib source files
match`; `check-stdlib-register: ok`; interpreter eval tests `ok:207
fail:0`; semantic-interface, admission and recovery-terminal negative
audits all rejected their poisoned controls by name; `reconciler: 2
finding(s), 0 HIGH — report-only` (C13, C5 — unchanged from main);
`jobs 12`. Log: the lane's `.tmp/ci-diff.log` (untracked). A clean-tip
re-run is the coordinator's/train's call: the merge train re-gates a
docs-only branch at the merged tip in any case.


### FR-31 audit follow-ups (2026-09-09)

[AGENT] The independent audit of `fix/package-method-identity` found no
remaining gc mismatch in its adversarial source constructions. FR-31's
bounded audit fixes and re-review remain on that branch; this is not a
mainline landing claim. The following pre-existing or broader obligations
remain owned by their roadmap lanes rather than blocking that increment:

| Finding | Owner / next check |
| --- | --- |
| Blank-identifier method target collisions currently reach the decoder's duplicate-target refusal | B2/F7: define non-callable declaration identity and add a source regression before changing admission |
| Twin `raft.DefaultLogger` wrapper references absent `log.Logger.output` body | Raft restart / imported-method coverage: establish the reachable demand and close or refuse the missing body; keep the current twin pin |
| `anonIfaceKey` still spells package-qualified members in the separate TypeId grammar | B2/F7 TypeId design: consume the member record without introducing another classifier |
| Hand-built core programs are not checked for exported-name iff empty-package agreement | B2 + admission boundary: state the core-domain invariant and preserve decoder/consumer separation |

Promotion depth/ambiguity remains package-scoped under G-P. An eventual
FR-31 landing still owes merge protocol 5a (`ci --slow`) at the merged tip;
these follow-ups do not waive any gate or authorize merge/push.
