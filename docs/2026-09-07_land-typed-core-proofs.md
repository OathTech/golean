# Landing chunk L1 — `land/typed-core-proofs`: the additive typed-contract layer of the typed-consumer sprint

[AGENT] landing worker, 2026-09-07. Source: branch `typed-consumer-sprint`
at `7edc298f` (96 commits over main `47195683`). Built on current main by
PATH SELECTION (`git checkout typed-consumer-sprint -- <paths>`), never by
merge, and squashed into ONE landing commit (disclosed in §8).

Ruling context ([USER] Mike, 2026-09-07, relayed by the [AGENT] coordinator
in the landing brief — cite as relayed): land the sprint in reviewable
chunks; evidence bundles do NOT land; fix the issues where appropriate,
«eg. the choice tape stuff». This chunk is the ADDITIVE layer only: NO
behavioural change to the shipped machine. Every excluded hunk is named in
§4 with its destination chunk.

Inputs read before selecting paths: `CLAUDE.md`, `AGENTS.md`, both landing
audits (`.tmp/landing-review/auditor-A.md`, `auditor-B.md` in the sprint
worktree — untracked review artifacts, quoted where load-bearing), the
sprint charter §2–§3 and the three design notes landed here.

## 1. Contents

### 1.1 Semantic-core modules (57, all new, verbatim from `7edc298f`)

| Family | Modules |
|---|---|
| Boolean profile (12) | `BooleanTyping`, `BooleanStore`, `BooleanSetup`, `BooleanInitialization`, `BooleanControlTyping`, `BooleanControl`, `BooleanInvariant`, `BooleanPreservation`, `BooleanProgress`, `BooleanSafety`, `BooleanProgram`, `BooleanPool` |
| Recovery profile, static (7) | `RecoveryTypingCore`, `RecoveryExpressions`, `RecoveryCalls`, `RecoveryStatements`, `RecoveryGraph`, `RecoveryDiagnostics`, `RecoveryAdmission` |
| Recovery profile, storage/setup (13) | `RecoveryStore`, `RecoveryEnvironment`, `RecoveryAllocation`, `RecoveryOperators`, `RecoveryContext`, `RecoveryControlTyping`, `RecoverySetupShape`, `RecoveryInitialization`, `RecoveryResultRoots`, `RecoverySetup`, `RecoverySetupWf`, `RecoverySetupReadout`, `RecoveryCallEntry` |
| Recovery profile, control/preservation/progress (15) | `RecoveryDelivery`, `RecoveryControlData`, `RecoveryControl`, `RecoveryControlMono`, `RecoveryWalk`, `RecoveryExpressionProgress`, `RecoveryControlHelpers`, `RecoveryCallControl`, `RecoveryValueBasic`, `RecoveryValueCalls`, `RecoveryStatementProgress`, `RecoveryFrameProgress`, `RecoveryPanicProgress`, `RecoveryInvariant`, `RecoverySuccessfulRuns` |
| Recovery profile, pool/choices (4) | `RecoveryCallLayout`, `RecoverySingleton`, `RecoveryPool`, `RecoveryChoices` |
| Generic abort observer (4) | `AbortObservation`, `RecoveryPoolObservation`, `RecoveryProgramObservation`, `RecoveryObservation` |
| Consumer-free helpers (2) | `Declaration` (positive closed Go declaration identities + `LawfulBEq`), `PanicText` (total constructive text helpers: `firstLine`, `escapeAllBytes`, `decodeEscapedBytes`, round-trip/injectivity — [the `escapeAllBytes`/`decodeEscapedBytes` half was DELETED by landing chunk L3, 2026-09-07, landing decision D5: the escape form is never a member; `firstLine`/`firstLine_bytes`/`lfPrefix_valid` remain — noted at L3's audit fix round, L3]) |

All 57 are under `GoLean/GoCore/`; none is `partial`; none imports
`EnumDedup`, `NativeToIR` or `CLI`.

### 1.2 Tests (20 modules + 2 native fixtures, verbatim)

`Tests/{AbortObservation, AbortObservationAudit, BooleanInvariant,
BooleanProgram, BooleanRuntime, BooleanSafetyAudit, BooleanTyping,
BooleanTypingAudit, BooleanTypingFixture, RecoveryA2Artifact,
RecoveryControlAudit, RecoveryDiagnosticControls, RecoveryInvariant,
RecoverySetup, RecoverySetupAudit, RecoveryStorage, RecoveryStorageAudit,
RecoveryTyping, RecoveryTypingAudit, RecoveryTypingFixture}.lean`;
`Tests/boolean-typing-fixture/{main.go,manifest.tsv}`;
`Tests/recovery-typing-fixture/{main.go,manifest.tsv}`. The fixture
manifests are NOT scanned by `scripts/coverage-manifest` (only `Corpus/` is),
so they add no baseline rows; they are run by hand in §7.

### 1.3 Restated files (edited relative to the branch; every edit listed)

- `GoLean/Interface.lean` — imports `StringPanic` and
  `RecoveryPoolObservationTyped` REPLACED by `RecoveryChoices` and
  `RecoveryObservation` (so `RecoverySingleton`/`RecoveryPool`/
  `RecoveryChoices`/`RecoveryObservation` stay in the default build); the
  two docstring paragraphs claiming the recovery terminal classification
  and `*_no_refusal` REPLACED by a paragraph stating they are NOT in this
  tree and why (§5); a paragraph added stating both profiles are
  CHOICE-FREE (auditor B R2 fix; §2); a pointer to this note for the
  profile domains. No theorem text changed.
- `Tests/InterfaceAudit.lean` — module and export lists trimmed of the
  deferred modules/theorems (§5), `Tests.AbortObservationAudit` and
  `GoLean.GoCore.PanicText` imported, `RecoveryObservation`'s two theorems
  added to the export list, the constructive-axiom check kept for the
  three `PanicText` helpers only. The branch's broadened axiom sweep (all
  `GoLean.*`/`Tests.*` constants) and its `NativeToIR`/`CLI` import ban
  are KEPT.
- `GoLean/GoCore.lean` — `+import GoLean.GoCore.Declaration`,
  `+import GoLean.GoCore.PanicText` (the branch reached them only through
  excluded files; without this they would be orphaned). Every one of the
  57 modules is now in the default-build import closure (checked
  mechanically from the sources).
- `lakefile.toml` — seven new `lean_lib` test targets (`BooleanTypingTests`,
  `BooleanRuntimeTests`, `RecoveryTypingTests`, `RecoveryStorageTests`,
  `RecoverySetupTests`, `RecoveryControlTests`, `AbortObservationTests`);
  `InterfaceTests` gains `Tests.BooleanRuntime`, `Tests.BooleanProgram`.
  `defaultTargets = ["golean"]` UNCHANGED; the `GoLean` lib UNCHANGED; no
  `[[require]]`; the branch's `DeclarationTests` and `RecoveryTerminalTests`
  libs NOT taken (§5). Verified: `spikes/` stay outside the default build
  and outside `scripts/ci`'s dependency graph (no root target names them;
  Iris is required only in the spikes' own lakefiles).

### 1.4 Spikes (outside the default build; opt-in gates)

- `spikes/iris-customer` — the sprint delta MINUS `GoLeanIris/Terminal.lean`
  (it consumes the deferred `runProgramPoolWithAbort_typed`,
  `runProgramPool_no_refusal` and `stringPanicHead`). Consequent trims:
  `GoLeanIris.lean` drops `import GoLeanIris.Terminal`; `GoLeanIris/Audit.lean`
  drops the `Terminal` module, the two deferred core modules and the seven
  `Terminal` exports; `check` and `gate_checks.py` drop the same names and
  the call to `tools/check-recovery-fixture-controls.py` (in `tools/**`,
  excluded — its check is reproduced by hand in §7). The 18 other changed
  spike files land verbatim (shared-recovery customer, reusable
  `wp_call`/`wp_frame_result`/`wp_store_cell`/`wp_initialize` rules,
  ownership tests, two-artifact `check_artifact.lean`).
- `spikes/i1-declarations/{Prototype.lean,README.md}` — verbatim.
- `spikes/gate-a1/GateA1/Audit.lean` — the sprint's 7-line strengthening
  (axiom sweep over all `GateA1`/`GoLean`/`Tests` constants). Not in the
  brief's list; taken because the iris spike gate builds on gate-a1 and the
  sprint validated the pair together.

### 1.5 Documents

`docs/2026-09-05_typed-contract-design-review.md`,
`docs/2026-09-06_recovery-static-design.md`,
`docs/2026-09-06_b7-context-store-design.md` — verbatim (sealed review/design
artifacts are not edited here; their dangling links are listed in §9), and
this note. The evidence directory
`docs/evidence/2026-09-07_land-typed-core-proofs/` carries ONLY the gate tail
(§7).

## 2. The F2 / F3 / F5 answer table — auditor B, VERBATIM

The following table is copied unchanged from
`.tmp/landing-review/auditor-B.md` §1 (auditor B, 2026-09-07, over tip
`7edc298f`). Nothing in this chunk claims more than it; §2.1 records what
this chunk's SUBSET of the branch changes about it.

| Finding | What the branch actually proves | Domain / premises | Verdict |
|---|---|---|---|
| **F2** driver↔relation bridge | *Nothing new.* The stream-quantified bridge is **pre-existing on `main`**: `GoLean/GoCore/PoolTrace.lean:71 run_iff`, `GoLean/GoCore/ProgramTrace.lean:26 program_run_iff`, `:53 exists_program_run_iff`, `:75 observation_iff` (`∃ fuel ch` on **both** sides), with the two-outcome example at `Tests/InterfaceContract.lean:164–185` (`two_choice_pool_bridge`). The branch adds `Tests/InterfaceContract.lean` +1 line. | The branch's *typed* readouts (`BooleanPool.lean:161`, `RecoveryTerminal.lean:83`) are `∀ fuel, ∀ ch` but over profiles with **no choice sites**: `Control.no_spawn/no_select/no_seq_consumption`, `Inv.run_choices : chf = ch`, `Choices.consumeAtE … = (0, ch, [])`. | **Partially answered, but not by this branch, and not for the typed profile.** The `∀ ch` quantifier on the typed theorems is *vacuously uniform* — the profiles are deterministic. The reverse direction (relation → driver) for the true Prop-level relation is still absent: `Trace.erase` gives `Steps`, and `GoLean/Interface.lean` states "no converse to erasure is supplied". `ProgramRun`/`Pool.Run` are *mirrors of the driver*, not `Machine.Step`. See R2. |
| **F3** context laws / `EctxLanguage` | The branch does **not** attempt `step_fill`. It **sidesteps legitimately**: `spikes/gate-a1/GateA1/Language.lean:28` gives a plain `instance : Language Config ExecState Empty Unit` (PrimStep = `Step`), and the recover rule keeps the continuation explicit in **both** parameters and postcondition — `pure_recover (env) (k) : PurePrimStep (Config.evalE .recoverCall env k) (.retV (recoverResult k).1 (recoverResult k).2)` (`:53`), `wp_recover` (`:64`). Header, `:6`: "This has no `EctxLanguage` instance". This file is **also pre-existing on `main`**; the branch adds the customer proofs above it. | Sequential, `Unit` terminal, empty observations, uncaught panic is stuck. | **Answered, honestly, by the "basic `Language` without `EctxLanguage`" route the audit itself allowed.** It is **not** an `EctxLanguage` instance and does not claim to be. `spikes/iris-customer/README.md:85` repeats "There is no unconditional `EctxLanguage` or continuation-transport law." **Reviewer's counterexample reproduced UNCHANGED on the branch** (I re-ran `docs/evidence/2026-09-05_project-gate-audit/ContractProbes.lean` at the tip): `recoverResult bareFrame = nil`, `recoverResult panicFrame = interface (defined 1) (string "audit")`. It is neither excluded by admission nor side-conditioned — it is *made irrelevant* by parameterising every rule on `k`. That is the correct design, and the sprint says so. |
| **F5** typed admission / refusal freedom | **Real and substantial.** Two independently defined judgments with total checkers and soundness **and** completeness: `GoLean/GoCore/BooleanTyping.lean:336 TypedBooleanAdmission`, `:379 checkTypedBoolean`, `:392 checkTypedBoolean_iff`; `GoLean/GoCore/RecoveryAdmission.lean:83 RecoveryAdmission`, `:155 checkRecovery`, `:166 checkRecovery_iff`. All-successor preservation over the **Prop-level relation**: `BooleanPreservation.lean:150 Inv.step (hstep : Step c s c' t) : Inv … t c'` and `RecoveryInvariant.lean:43` (same shape); progress `BooleanSafety.lean:16 Inv.reachable_progress`, `RecoveryInvariant.lean:70` (normal terminal ∨ nonempty abort ∨ legal successor). Driver refusal-freedom, universally quantified over fuel and stream: `BooleanPool.lean:175 runProgramPool_no_refusal`, `RecoveryTerminal.lean:99/107`. | `TypedBooleanAdmission = BooleanAdmission ∧ ProgramTyped p`, checked over **every** function in the program (`ProgramTyped`, `:331`). Boolean profile grammar is `var/boolLit/not/and/or` + `seqn/block/initialization/assign(var)/ifThenElse/return` — **no calls, no loops**. Recovery profile adds direct/closure calls, defers, string panic, recover, finite call-graph certificate. | **Answered *within two deliberately tiny profiles*, and stated as such.** The reviewer's ill-typed cell is now excluded — I proved `¬ BooleanRuntime.BoolHeap illTyped` at the tip (`BooleanStore.lean:15` requires `.value .bool (.bool b)`). **But `StateWf` itself is unchanged**: `decide (StateWf illTyped)` still returns `true` at the tip. The exclusion is profile-local, not machine-wide, and F5's general `Accepted`/`WireWellFormed`/`ProgramWellTyped` programme is untouched. |

### 2.1 What this chunk realizes of that table (no stronger claim)

- **F2: NOT answered.** Both profiles are choice-free; the `∀ ch` on every
  landed theorem is uniform by vacuity. The `Interface.lean` docstring now
  says so (auditor B R2 fix). The only two-outcome bridge remains the
  untyped pre-existing `two_choice_pool_bridge`. F2 stays OPEN for the typed
  contract in the master plan's §7 table (the records chunk owns that
  update).
- **F3: answered via a basic `Language` WITHOUT `EctxLanguage`**, on
  pre-existing `spikes/gate-a1` code; this chunk adds the customer proofs
  above it (`Call`, `Unwind`, `Return`, `Shared*`). No `step_fill`, no
  continuation-transport law, none claimed.
- **F5: answered within two tiny profiles; the general `Accepted` /
  `WireWellFormed` / `ProgramWellTyped` programme is UNTOUCHED.** The table's
  recovery-side refusal-freedom entries (`RecoveryTerminal.lean:99/107`) are
  NOT in this chunk (§5); the Boolean one (`BooleanPool.lean:175`) is.
  `StateWf illTyped` still decides `true` on this tip (the machine is
  unchanged); `¬ BoolHeap illTyped` is re-proved in §7.

## 3. The profiles' domains (what each admission judgment admits)

Both are opt-in. Neither is invoked by the frontend, the CLI or any driver.
Both check EVERY function of the program, not only the entry
(`ProgramTyped`). Both keep A3a's `BooleanAdmission` (`checkBoolean`) as a
separate, weaker predicate — `Tests/BooleanTyping.lean` keeps the
A3a-accepted unbound program side by side with its rejection here.

### 3.1 `BooleanTyping.TypedBooleanAdmission p name args`

`= BooleanAdmission p name args ∧ ProgramTyped p`, where for every `f`:
`BoolParams f.args ∧ BoolParams f.results ∧ SignatureDistinct f ∧
StmtTyped (initialContext f) f.body ∧ ReturnPolicy f`.

- Context: `List (List String)` (scope stack); `Bound` = any scope,
  `Fresh` = not in the innermost scope; `.block` pushes a scope,
  `.seqn` EXPORTS its declarations (`afterStmt` threading — review R1).
- Expressions: `var` (bound), `boolLit`, `not`, `and`, `or`. Nothing else.
- Statements: `seqn`, `block ps ss` (Boolean, distinct params),
  `initialization p` (Boolean, fresh, and ONLY as a statement-list element:
  `inSequence = true`), `assign (.var x) e`, `ifThenElse e t f` (arms
  export no declarations), `returnStmt`. Nothing else — no calls, no loops,
  no pointers, no strings, no panics.
- `ReturnPolicy f := f.results.size = 0 ∨ Returns f.body` (structural
  terminating-statement discipline; NOT definite assignment). Zero-initialized
  locals/results are admitted.
- Entry: A3a's `Entry` (Boolean external arguments at the declared arity).

### 3.2 `RecoveryTyping.RecoveryAdmission p name args`

`= IndexStructure p ∧ Entry p name args ∧ ProgramTyped p`, where
`ProgramTyped p := p.globals.size = 0 ∧ p.methods.size = 0 ∧ (∀ f, FunctionTyped p.funcs f) ∧ FiniteCalls p.funcs`
and `FunctionTyped fs f := FunctionFlags f ∧ ParameterTypes f.args ∧ StorageParams f.results ∧ SignatureDistinct f ∧ Statement fs false (initialContext f) f.body ∧ ReturnPolicy f`.

- Value sorts (`TypeClass`): `.bool ↦ boolean`; `.pointer .bool ↦ root`
  (a LIVE Boolean root cell — refinement carried by checked call arguments,
  not by the Go type); `.interface id ↦ payload` for the machine's
  empty-interface name only; `.string ↦ string` (transient literals only).
- Context: `List (List (String × Ty))`, first-match lookup; `.seqn`
  exports, `.block` restores; branch arms export zero declarations.
- Expressions: `var`, `boolLit`, `stringLit` (ANY `GoString`: no UTF-8,
  newline or control-byte restriction), `nil` (untyped or at an admitted
  empty-interface type), `not/and/or`, `ref x` (x Boolean), `deref e .bool`
  (e a root), `toInterface target .string e` (target empty-interface, e a
  string), `recoverCall` (payload), `eqCmp/neqCmp` at Boolean type or at
  empty-interface type against nil.
- Targets: `var` (first match, sort-agreeing), `addr e` (e a root; writes a
  Boolean).
- Statements: `seqn`, `block` (Boolean/payload params, distinct),
  `initialization` (Boolean or payload; root-typed locals EXCLUDED because
  their zero value is nil), `assign`, `ifThenElse`, `call targets fid args`
  (actual `FuncId` lookup; exact argument and result-target arities),
  `callValue targets (.funcVal fid caps) args` (literal closure only; captures
  are roots matching the callee's parameter prefix), `deferCall (.funcVal fid caps) args`
  (same check; results deliberately discarded), `panicStmt (toInterface target .string e)`
  (explicit string boxing only — `panic(true)`, `panic(nil)` and rethrow of a
  recovered payload are OUT), `returnStmt`.
- `Returns` additionally counts `panicStmt` as terminating.
- `FunctionFlags`: not the package initializer, not variadic, not a wrapper.
- `FiniteCalls`: an inductive `CallDepth` certificate (bounded by the
  function-table size) over direct, closure and defer edges — no recursion
  (`admitted_no_cycle`), independent of table order and of execution fuel.
- Excluded structurally: loops, globals/package init, methods, general
  interface operations, pointer arithmetic/non-root paths, concurrency,
  runtime-generated error payloads, arbitrary higher-order dispatch.

### 3.3 What the landed runtime theorems say about these domains

Boolean: `setup_typed_exact` (actual `runProgramSetupM` succeeds, canonical
env/heap, distinct result pins, `MachineWf`, typed storage), `Inv.step`
(preservation for EVERY relational successor), `Inv.reachable_progress`
(normal terminal or a legal successor — no abort disjunct in this profile),
`Inv.run_readout`, and the shipped-driver theorems `runProgramPool_typed`
(typed readout at the declared arity with empty output, or explicit fuel
exhaustion with empty output) and `runProgramPool_no_refusal`.

Recovery: `setup_typed_wf`/`setup_inv` (actual setup establishes the
structural invariant), `Inv.step` (every relational successor),
`Inv.reachable_progress` (normal terminal ∨ NONEMPTY SEMANTIC ABORT ∨ legal
successor), `Inv.run_readout`, `Inv.run_choices`, `Inv.reachable_silent`,
call/defer entry and direct/indirect recovery control contracts,
`Inv.pool_eq_runConfig`, `runProgramPool_eq_sequential`, `Inv.loop_all_choices`,
plus the generic observer (`*_erasure`, `*_witness`, `Inv.observation_complete`).
The abort disjunct is a SHAPE (a nonempty typed panic chain), NOT a rendered
terminal: whether the shipped machine renders that chain or refuses is the
deferred question of §5.

No termination bound, no sufficient-fuel bound, no Iris resource, no
`NotStuck` for uncaught panic, no frontend correctness, no general
`Accepted` guarantee is provided by either profile.

## 4. Exclusions, with destinations

Chunk names as given by the coordinator: L3 = rendering/choice tape, L4 =
observer/terminal classification, L5 = uintptr; "L2 (tooling)" = the
gate-tooling chunk (`scripts/ci` steps, `scripts/check-*`, `tools/*`);
"records" = the docs/records chunk (auditor B group 10).

### 4.1 `GoLean/GoCore/Machine.lean` — every hunk main..`7edc298f`

| # | Lines (tip) | Hunk | Destination | Why excluded here |
|---|---|---|---|---|
| M1 | 2 | `+import GoLean.GoCore.PanicText` | L3 | only consumer is the renderer change |
| M2 | 2061–2098 | `asciiString?` DELETED; `utf8StringAux?`/`utf8String?` (strict constructive UTF-8), `firstPanicLine?`, `renderStringMember` (TOTAL: escapes invalid UTF-8 as `"\xHH…"`) ADDED | L3 | A-R3: the valid-UTF-8/first-line half is a K3 fidelity fix with strict-lane gc evidence; the invalid-UTF-8 half emits a rendering gc never prints — a [USER] decision (B-R3) |
| M3 | 2131–2134 | `renderPanicPayload`: runtime-error arm `asciiString?`→`utf8String?`; string arm `asciiString?`→`some (renderStringMember s)`; docstring | L3 | same object as M2 |
| M4 | 2178–2207 | `renderPanicHead`: unconditional ` [recovered]` for string payloads even when `rest` head equals the value (was `none`, BUG-004); `.bind firstPanicLine?`; docstring cites R-1 | L3 | A-R2: a latitude choice baked into evaluator recursion (`AGENTS.md` merge invariant; «the choice tape stuff»); must be a tape draw or the restored refusal |

### 4.2 `GoLean/GoCore/Ops.lean` — one hunk

| # | Lines | Hunk | Destination |
|---|---|---|---|
| O1 | 1027–1031 | docstring only: drops the sentence "the same constraint the abort renderer records at `asciiString?`" | L3 (the sentence is still TRUE on this tip because `asciiString?` still exists) |

### 4.3 `GoLean/CLI.lean` — three hunks

| # | Lines | Hunk | Destination |
|---|---|---|---|
| C1 | 2 | `+import GoLean.GoCore.RecoveryProgramObservation` | L3 |
| C2 | 35 | usage line for `native-json-string-run` | L3 |
| C3 | 508–573, 1671 | `abortHeadJson`, `abortChainJson`, `runNativeJsonStringRun` (schema `golean-string-abort-witness-v1`; `--require-recovery-profile`) and its dispatch arm | L3 (the R-1 string-member lane's machine-side apparatus; consumed by `tools/string_member_runner.py`) |

Note: the module C1 imports (`RecoveryProgramObservation`) DOES land here;
only the CLI command is deferred. `StepFn.lean`, `Multi.lean`,
`NativeToIR.lean`, `MachineSound.lean` are byte-identical to main on the
sprint tip; nothing to exclude.

### 4.4 Other excluded families

| Family | Destination |
|---|---|
| `GoLean/GoCore/{StringPanic, RecoveryTerminal, RecoveryPoolObservationTyped}.lean`, `Tests/{PanicRendering, StringPanicMembers, RecoveryTerminal, RecoveryTerminalAudit}.lean`, the `Tests/InterfaceContract.lean` delta (`import Tests.PanicRendering`), `spikes/iris-customer/GoLeanIris/Terminal.lean`, lakefile `RecoveryTerminalTests` | L3 — see §5 for the named dependency |
| `GoLean/{NativeDeclaration, StrictJsonParse}.lean`, `Tests/{DeclarationWire, StrictJsonParse, DeclarationAudit}.lean`, lakefile `DeclarationTests` | L2 (tooling) — the Lean half of the I1 declaration wire; its test needs the excluded Go emitter `tools/nativefrontend/declaration.go` and `scripts/check-declarations`, so it cannot run green here |
| `tools/**` (coverageharness observer, `declaration.go`, `*-audit.py`, `string_member*.py`, …) | L2 / L4 / L3 per file |
| `scripts/**` (+94-line `ci`, `check-*`, `diff-coverage` rework) | L2 (tooling) / L4 |
| `baselines/**` (four re-pins, `string-members/` pins) | L3 / L4 / L5, each with its own full run |
| `Corpus/**` (37 new rows) | L3 / L4 |
| `docs/evidence/**` (2,159 files, 734,510 lines) | NOT landing (ruling); the archive branch keeps it |
| `docs/BUGS.md` (BUG-105/106), `docs/language-coverage-ledger.md` | L3 / L4 (they record the renderer/observer flips) |
| `docs/2026-09-05_master-plan.md` (+21), `AGENTS.md` (+7), `CLAUDE.md` (+10, auditor B R4) | records |
| The other 40 sprint docs, incl. the four contract notes `Interface.lean` still cites (`boolean-program-contract`, `recovery-static-claims`, `recovery-entry-contract`, `recovery-control-contract`) and the sprint charter | records |

## 5. The dependency check — outcome per module

Method: every included module was built on top of the UNCHANGED main core
(`Machine.lean`, `Ops.lean`, `StepFn.lean`, `Multi.lean`, `MachineSound.lean`
byte-identical to `47195683`). A module that only builds because of an
excluded hunk is classified (a) pure helper → hunk moved here, or
(b) dependent on the baked-in latitude choice (A-R2) or the total renderer
(A-R3) → restated if small and honest, else deferred with the dependency
named.

| Module(s) | Outcome | Dependency named |
|---|---|---|
| 12 Boolean modules | LANDED verbatim; build on unchanged core | — |
| 42 Recovery modules listed in §1.1 | LANDED verbatim; build on unchanged core. `RecoveryPool.lean`'s header states it "preserves renderer refusals as well as successes, so it does not depend on a renderer totality claim"; `RecoveryInvariant.reachable_progress`'s abort disjunct is a chain SHAPE | — |
| `AbortObservation`, `RecoveryPoolObservation`, `RecoveryProgramObservation`, `RecoveryObservation` | LANDED verbatim; the instrumented drivers pattern-match `stepFn`'s `.error (.panic _)` and `abortMsg`'s `.ok`/`.error` generically; erasure/witness/completeness hold on the unchanged machine | — |
| `PanicText` | LANDED verbatim (class (a): pure total text helpers, `decide +kernel` over `Fin 256`, constructive — pinned to `propext`/`Quot.sound` by the audit). It has NO consumer on this tip; it is the helper L3's renderer will consume. Landing the DEFINITION of the contested `"\xHH"` escape member commits the machine to nothing: nothing here calls it | — |
| `Declaration` | LANDED verbatim (class (a): declaration identity types + `equality_exact`/`LawfulBEq`); consumer-free here (its decoder is L2) | — |
| `StringPanic` | DEFERRED to L3 (class (b)). `abortMsg_string_total : ∃ msg, abortMsg s first rest = .ok msg` for EVERY string payload is FALSE on main (`asciiString?` refuses `≥ 0x80`/LF); `renderPanicHead_string` gives `some (… ++ " [recovered]")` where main gives `none` for an equal-value repanic (A-R2) | `Machine.renderStringMember` totality (A-R3) + the unconditional string `[recovered]` arm of `renderPanicHead` (A-R2), i.e. hunks M2–M4 |
| `RecoveryTerminal` | DEFERRED to L3 (class (b)). `Inv.run_classified`/`runProgram_typed`/`runProgramPool_typed`/`*_no_refusal` are proved through `runConfig_string_abort`/`stepFn_string_abort` from `StringPanic`. The honest restatement over main adds a fourth disjunct — "an abort configuration whose string payload the renderer REFUSES" — which negates the theorems' names and content; that is not a small restatement, and its final shape depends on the pending [USER] decision (tape draw vs restored refusal vs total renderer) | same as `StringPanic` |
| `RecoveryPoolObservationTyped` | DEFERRED to L3 (class (b)); every theorem states its member as `stringPanicHead record.bytes record.recovered` via `abortMsg_string` | same |
| `Tests/RecoveryTerminal(+Audit)`, `Tests/PanicRendering`, `Tests/StringPanicMembers`, `Tests/InterfaceContract` delta, spike `Terminal.lean` | DEFERRED to L3 with their modules | same |
| `GoLean/Interface.lean`, `Tests/InterfaceAudit.lean`, spike `Audit.lean`/`check`/`gate_checks.py`/`GoLeanIris.lean` | RESTATED (edits itemized in §1.3/§1.4) — list/import trims plus honest prose; no theorem changed | — |

No behavioural hunk was imported to make a proof go through (class (a)
was never needed for a machine file).

## 6. O1–O5 status after this chunk

- **O1 (typed Boolean contract): realized here** — judgment + checker with
  `checkTypedBoolean_iff`; the A3a unbound counterexample REJECTED
  (`old_unbound_rejected`) beside its A3a acceptance; setup/preservation/
  progress/readout and the shipped-driver classification; Go-differential
  rows for the native fixture (§7).
- **O2 (typed recovery customer): partially realized here** — admission
  (`checkRecovery_iff`, both A2 entries and the second fixture admitted),
  setup, all-successor preservation, terminal-aware progress at the SHAPE
  level, control contracts, singleton-pool correspondence, the generic
  observer, and the Iris customer's reusable rules + shared-capture fixture
  proofs. NOT here: the terminal classification / refusal-freedom for the
  recovery profile and the customer's `Terminal.lean` (L3, §5). The spike
  README's own statement stands: the customer "still uses machine internals
  and unfolds operations" — Gate C's exit criterion is NOT discharged.
- **O3 (evidence that can challenge the contract): partially realized
  here** — the positive/negative admission tests, semantic counterexamples,
  dependency audits (`*Audit.run`) and the two native fixtures land; the
  sprint's `scripts/check-*` gate steps and `tools/*-audit.py` (L2), the
  Go differential rows in `Corpus/` (L3/L4) and the independent review
  records (records chunk) do not.
- **O4 (B7 + I1): UNIMPLEMENTED.** `docs/2026-09-06_b7-context-store-design.md`
  is a design; `grep ProgramCtx GoLean/` finds one deferred-work comment.
  The I1 spike and `Declaration.lean` are prototypes, not an admission
  boundary.
- **O5 (a branch ready for the closing decision): PENDING** — this is one
  of several landing chunks; the closing packet is the records chunk's.

## 7. Verification at the committed tip

Host: linux/amd64, 32 cores, 125 GiB, load ≈ 3 at run time (no other heavy
lane active). Toolchain: `go version go1.26.5 linux/amd64` (= `baselines/go-oracle-pin`),
Lean per `lean-toolchain`. All Lean/Lake via `scripts/capped`. The ci gate
and the spike gates ran under the sprint's recorded envelope
`GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3 GOLEAN_COVERAGE_JOBS=2` (main's last
full pin, BUG-103, used `jobs 8`; the tighter setting is the [USER]-relayed
lane-coordination limit auditor A cites — applied here as the safe reading).
The build-time comparison in §7.1 used the default cap and thread count so
that main and tip are measured alike.

### 7.1 Build wall time, main vs tip (same worktree, same cap, cold `.lake`)

| Build | main `47195683` | this tip | delta |
|---|---|---|---|
| `scripts/capped lake build` (default target `golean`), cold | 109.05 s wall, 76 jobs | 117.17 s wall, 186 jobs (+ 6.19 s for the `GoCore.lean` wiring rebuild, 190 jobs) | +8.1 s (+7 %) |
| `lake build GoLean.Interface InterfaceTests AdmissionTests` (+ the 7 new test libs on tip), incremental after the above | 31.66 s, 28 jobs | 40.70 s, 111 jobs | +9.0 s |

The default target reaches every landed module because `GoLean.lean`
imports `GoLean.Interface` (and `GoCore.lean` now imports the two helpers).

### 7.2 Escape hatches and totality (source scans over this tree)

- `grep -rn 'sorry\|native_decide\|axiom' GoLean/` — prose only (the same
  comment hits as main; no new hits).
- `grep -rn 'partial' GoLean/GoCore/` — none.
- `PanicText.lean` uses `decide +kernel` twice over `Fin 256` — kernel, not
  native; permitted by doctrine and by `scripts/ci`'s addendum scan.

### 7.3 Axioms (`#print axioms`, `.tmp/land/probe/axioms.log`)

| Theorem | Axioms |
|---|---|
| `BooleanTyping.checkTypedBoolean_iff` | `[propext, Quot.sound]` |
| `RecoveryTyping.checkRecovery_iff` | `[propext, Quot.sound]` |
| `BooleanRuntime.runProgramPool_no_refusal` | `[propext, Classical.choice, Quot.sound]` |
| `RecoveryRuntime.Inv.reachable_progress` | `[propext, Classical.choice, Quot.sound]` |
| `RecoveryRuntime.Inv.observation_complete` | `[propext, Classical.choice, Quot.sound]` |
| (also) `BooleanRuntime.Inv.step`, `RecoveryRuntime.Inv.step` | `[propext, Classical.choice, Quot.sound]` |

`stepFn_sound` and `step_complete` (`MachineSound.lean`, byte-identical to
main) `#check` to exactly main's statements:
`stepFn s c ch = .ok (c', s', ch') → Step c s c' s'` and
`Step c s c' s' → ∃ ch ch', stepFn s c ch = .ok (c', s', ch')`.

### 7.4 Non-vacuity (`.tmp/land/probe/nonvacuity.log`, all by `#eval`/kernel)

- Admitted sets inhabited by the NATIVE fixtures: `checkTypedBoolean nativeFixture`
  at `Argument #[true]`, `Argument #[false]`, `Shadow`, `Branches`, `Zero` →
  `Except.ok ()` (5/5); `checkRecovery a2Program` at `Recovered`, `Normal`,
  `Uncaught` → `ok` (3/3); `checkRecovery nativeRecovery` at `Shared #[true]`,
  `Shared #[false]`, `Outside`, `Reversed #[true]`, `DirectRecoveryControl #[true]`
  → `ok` (5/5).
- Named refusals: the A3a-accepted unbound program → `.error (.scopedBody ⟨"F"⟩)`
  (`old_unbound_rejected`); `Shared #[.int 1]` → `.error (.boundary .initialArgumentTypes)`;
  a missing entry → `.error (.boundary (.missingEntry "NoSuchFunction"))`.
- The gate audit's F5 cell: `StateWf illTyped` still holds (machine unchanged)
  and `¬ BooleanRuntime.BoolHeap illTyped` is proved in three lines.
- The SHIPPED drivers on the native recovery fixture: `Shared #[true]` → `false`,
  `Shared #[false]` → `true` (input-dependent), `Reversed #[true]` → `true`
  (defer-order-dependent), `Outside` → `true`; A2 `Uncaught` →
  `.error (.panic "customer panic")` and the generic observer returns the
  record `⟨"customer panic", recovered := false, []⟩` for it and `none` for
  the normal `Shared` run.
- Fresh native emission (`go run ./tools/nativefrontend`) of
  `Tests/boolean-typing-fixture`, `Tests/recovery-typing-fixture` and
  `spikes/iris-customer/fixtures/recovery`, lowered by the unchanged
  `NativeToIR.decodeProgram`, equals the pinned proof artifacts
  `nativeFixture` (4 funcs), `nativeRecovery` (16), `a2Program` (5) by `reprStr`
  (`.tmp/land/probe/compare-artifacts.log`; wire sha256
  `dbf75176…`, `e9ce5629…`, `5a421bbd…`).
- Go-vs-Lean differential on the two fixture manifests (`scripts/diff-coverage`,
  main's runner, 2 jobs): recovery 5/5 PASS, boolean 3/3 PASS. The five
  control observations are exactly the table the excluded
  `tools/check-recovery-fixture-controls.py` pins: `shared-false → true`,
  `shared-true → false`, `outside → true`, `reversed-true → true`,
  `direct-true → true`.

### 7.5 Tests and audits (all exit 0)

`lake build` of all seven new test libs + `InterfaceTests` + `AdmissionTests`
succeeds (111 jobs). The eight post-import audits, each run from a fresh
harness (`import Tests.X` / `#eval X.run`): `BooleanTypingAudit` (12 exports,
3,276 constants), `BooleanSafetyAudit` (44 / 14,821), `RecoveryTypingAudit`
(46 / 10,868), `RecoveryStorageAudit` (32 / 6,778), `RecoverySetupAudit`
(37 / 11,230), `RecoveryControlAudit` (124 / 13,813), `AbortObservationAudit`
(43 / 14,518), `InterfaceAudit` (111 exports / 15,114 constants) — every
constant on the classical trio only.

### 7.6 Gate: `scripts/capped scripts/ci --diff` at the clean committed tip

Run at `bfcd3d77d9b0b2fae58ca182bed56966aa1cc5f5` (= `refs/snapshots/land-typed-core-gated`;
the final landing commit differs from it ONLY by
`docs/evidence/2026-09-07_land-typed-core-proofs/` and §7.6–§7.7 of this
note — a documentation-only amend, the practice of the 2026-09-05
semantic-interface landing). Envelope `GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3
GOLEAN_COVERAGE_JOBS=2`. Full log: `docs/evidence/2026-09-07_land-typed-core-proofs/ci-diff.log`.
Verbatim lines:

```
  ok   core build (warning-free)
  ok   semantic interface (bridges, counterexamples, compiled audit negatives)
  ok   admission checker proofs and post-import audit
  ok   eval tests (202 ok)
differential coverage summary: cases=3598 pass=3353 fail=245 export_status=0
  ok   negative baseline diff (no regression)
  ok   baseline diff FULL (3598/3598, no regression)
  note reconciler: 3 finding(s), 0 HIGH — report-only (details: tools/reconcile-records)
RESULT: PASS
WALL 2265.30 s
```

`git_dirty`: the run's records (`full.meta.tsv`, `negative.meta.tsv` in the
evidence dir) carry `git_commit bfcd3d77…`, `git_dirty false`, `jobs 2`; the
ci prints its DIRTY demotion note only when `git_dirty=true`, and none was
printed. Baseline drift: ZERO — 3598 = 3353 PASS / 245 FAIL is exactly
`baselines/native-full.tsv`'s current pin, the negative corpus matched its
394 rows, no row moved, no re-pin owed (the machine is unchanged). The run
is FULL (every row re-run; tier=slow rows verified against their cached
certified records, as `--diff` does), not cached. `scripts/ci --slow` is
NOT owed: `tools/nativefrontend/wire.go` and `GoLean/NativeToIR.lean` are
untouched.

### 7.7 Opt-in spike gates (outside the default build; same tree)

```
Gate A1: 12 required exports present; 14864 constants' axiom dependencies checked (classical trio only)
Gate A1: PASS
WALL 17.80 s
Iris customer: 136 required exports present; 15212 constants' axiom dependencies checked (classical trio only)
Iris customer: both complete fresh native artifacts match the proved programs
differential coverage summary: cases=5 pass=5 fail=0 export_status=0
Iris customer: PASS
WALL 134.27 s
```

Both under `GOLEAN_MEM_MAX=16G LEAN_NUM_THREADS=3 GOLEAN_COVERAGE_JOBS=2`;
Iris dependencies at the pinned revisions (`iris e7a0a438`, `batteries 023ce7d6`,
`Qq 38d591e7`; `gate_checks.py dependencies` verified them clean), seeded
from a sibling worktree's checkout because this host has no GitHub access —
no clean network bootstrap is claimed. The iris gate compiled the trimmed
customer (25 compiled poison controls rejected by name: 4 core modules,
17 customer helpers, trailing/aggregate/sorry) — so the `Terminal.lean`
removal left a coherent spike.

## 8. Provenance

- **Derived from** (sprint commits whose content lands here, by path
  selection; authorship is theirs, the squash is mine): Boolean —
  `c7a439f7`, `f251abcb`, `354ef7f2`, `8717b974`, `26f0dc09`; recovery
  static — `e8a665e9`, `77f154e0`; recovery storage/setup/control —
  `4f7aedef`, `123fd48e`, `63769964`, `30b09c08`, `f160d7ca`, `b3d6fa6e`;
  abort observer — `04109912`, `414a2abe`; shared Iris customer —
  `10cd6e8f`, `658fe3eb`, `b34cee67`; I1 spike/declaration identity —
  `8ea5a74b`, `0ff12435`; design notes — `d3ffb32b`, `ce896516`,
  `71183a62` (contract review), `e8a665e9` (recovery static design),
  `45ff4ae2` (B7 design); facade/audit integration — `a392fab0`,
  `29092c26`, `7edc298f` (the tip, whose `Interface.lean`/`InterfaceAudit.lean`
  were the base for the restatement). The full 96-commit history stays on
  `typed-consumer-sprint`.
- **Squash disclosed:** one commit, built by `git checkout typed-consumer-sprint -- <105 paths>`
  plus the six restated files and `GoLean/GoCore.lean`. `git log` will not
  show the sprint's per-lane history for these paths.
- **Approval chain, as relayed:** the sprint's K1–K5 defaults were approved
  by [USER] Mike on 2026-09-05 («Agree with all 5»; K4 clarified: «merges
  *to main* are always user-approved. Feature branches can be merged to by
  agents, when standign approval is given by the user»), recorded verbatim
  by the [AGENT] coordinator in `docs/2026-09-05_typed-consumer-sprint-charter.md`
  §2 (on branch `typed-consumer-sprint`; that charter lands with the records
  chunk) — cite as relayed. The 2026-09-07 chunked-landing ruling is quoted
  at the top of this note, also as relayed. This chunk does NOT merge to
  main and does NOT push; both remain [USER] sign-offs.
- **Provenance of the deferred [USER] decisions this chunk steps around:**
  A-R2/A-R3 (renderer, `[recovered]` collapse), B-R3 (R-1 scope), B-R13
  (uintptr latitude), B-R14 (terminal-classification policy) — none is
  decided or pre-empted here.

## 9. Known dangling references in landed text (deliberately not edited)

- `docs/2026-09-05_typed-contract-design-review.md`: its 2026-09-06
  corrigendum links `2026-09-06_panic-rendering-repair.md` (L3) and
  `evidence/2026-09-05_typed-contract-design-review/README.md` (evidence,
  not landing); it links the sprint charter (records). Auditor B R21 (the
  in-place corrigendum) is a records-chunk item; the artifact is landed as
  sealed.
- `docs/2026-09-06_b7-context-store-design.md`: links the charter (records),
  `evidence/2026-09-06_b7-design/source-inventory.json` and
  `evidence/2026-09-06_typed-preflight/README.md` (evidence, not landing);
  its `:135` "host-capability ruling" phrase is auditor B R20 (the decision
  is OPEN and [USER]-owned — master plan `:1402`); records chunk.
- `GoLean/Interface.lean` docstrings cite the four contract notes named in
  §4.4 (records chunk); the domains are stated in §3 above meanwhile.
