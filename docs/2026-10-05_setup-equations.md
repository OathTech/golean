# The setup equations G-R1–G-R4 (lane `core/setup-equations-1005`)

[AGENT worker, lane `core/setup-equations-1005`] 2026-10-05. Authority: [USER] Mike 2026-10-05 «(1) Go ahead»
(relayed by the [AGENT] coordinator; scheduled after train r66, main `7a0a1568`). The request, verbatim:
`docs/2026-10-05_note-from-logic-team-setup-equations.md` (the golean-logic coordinator, «with Mike's approval»);
the requesters' design (read-only): golean-logic branch `design/globals-init-1005`,
`docs/2026-10-05_globals-init-design.md` §3.1, §5–§6, §9. The [AGENT] coordinator's committed reply: additive only
— new names, the existing pinned statements unchanged, the old `{}`-store forms kept as corollaries — and G-R4's
exact statement goes to the logic team for review BEFORE it is proved. This note is that delivery.

## 1. What landed (phase 1: G-R1–G-R3 proved; phase 2: G-R4 stated; phase 3: G-R4 approved and proved, with the logic team's answers (a)–(d))

| File | Content |
|---|---|
| `GoLean/GoCore/SetupStatement.lean` (new) | the `def <name>_stmt : Prop` of G-R1–G-R4 (the `ExecutionStatement`/`PoolStatement` grain); the one new definition `zeroCell`; `rfl` controls after `#eval` (§5). Phase 3: G-R4 restated WITHOUT the no-blocked premise; the four `runInitConfig_*_iff_stmt` corollaries; the wrapper pair `runPkgInitM_some_stmt` / `runPkgInitM_ok_iff_stmt`; a `runPkgInitM` control |
| `GoLean/GoCore/SetupSound.lean` (new) | `theorem <name> : <name>_stmt` for the nine statements of G-R1–G-R3; `example`s re-deriving the `{}`-store statements of `Equations.lean` from the general forms. Phase 3: G-R4 proved (induction on the fuel through `runInitConfig_unfold`, the twin of `execStmtLoop_unfold`), the four corollaries (the equation + `Prefix.lean`'s sequential statement), the wrapper pair |
| `GoLean/GoCore/BridgeSet.lean` | RE-PIN 12: rows 1–511 byte-identical; rows 512–520 ADDED (the nine, written out); import of `SetupSound`. RE-PIN 13: rows 1–520 byte-identical; rows 521–527 ADDED (G-R4, its four corollaries, the wrapper pair) |
| `Tests/GoCoreAudit.lean` | the two modules in `requiredModules`; the nine theorems in `exports`; phase 3: the seven more |
| `GoLean.lean` | the two modules enrolled in the default build |
| `scripts/mem-callsites.tsv` | two rows (the raw call-site inventory, `scripts/check-mem-callsites`): `SetupSound.lean seedStep alloc` — a PROOF DEVICE, `seedGlobals`' loop body restated verbatim so the loop can be characterized by induction, never executed by a run; `SetupStatement.lean seedGlobals_cell_stmt Heap.lookup` — NO EXECUTION, the Prop statement's cell reader (the precedent of the `program_bridge_stmt`/`program_prefix_stmt` rows) |

Unchanged: `stepFn`, every driver and setup function (`seedGlobals`, `runPkgInitM`, `runInitConfig`,
`runProgramSetupM`), the frontend, `Corpus/`, baselines, and every previously pinned statement — rows 397
(`runProgramSetup_noInit`) and 399–402 (`setup_lookup_arg`, `setup_lookup_result`, `setup_resultLocs`,
`setup_heap_size`) keep their statements AND proofs (`Equations.lean` is not touched; its client
`Tests/EquationClient.lean` needs no new pin). No `sorry`, `native_decide`, axiom or `partial`; the core audit's
machine check covers both new modules.

Why a module pair and not «beside the existing setup lemmas»: the brief asks for `_stmt` + pin. A `_stmt`-typed
theorem inside the namespace `GoLean.GoCore.Equations` would be enrolled by the equation client's EXHAUSTIVE
namespace check, whose pin comparison is Expr-equality — the only pin that passes for such a theorem is the bare
constant `<name>_stmt`, which would silently weaken the client's drift check for exactly these statements. The
`_stmt` grain (statement module + proof module, written-out pins in `BridgeSet.lean`) is the one `ExecutionStatement`
/`Prefix` and `PoolStatement`/`PoolSound` already use, so the new theorems follow it in their own namespaces.

## 2. The statements, one by one (names = BridgeSet rows)

Notation: `⟨program⟩ : ProgramCtx`; `entrySlot s i = .base ⟨s.heap.size + i⟩` (`Machine.lean`).

### G-R2 — seeding (rows 512–515)

`zeroCell ctx g := (HeapCell.value g.typ ·) <$> defaultValue ctx g.typ` — the global's zero value at its declared
type.

* **512 `seedGlobals_cells`** — `seedGlobals ctx {} globals = (fun cells => { heap := cells.toArray }) <$>
  globals.toList.mapM (zeroCell ctx)`. One `Except` equation: the heap IS the zero cells in order (global `i` at
  `.base ⟨i⟩`); a global whose zero value is refused refuses seeding with that refusal, in order. The in-loop
  address check (`loc != .base ⟨i⟩`) never fires from the fresh store — part of what the equation says.
* **513 `seedGlobals_cell`** — the pointwise reading: `seedGlobals ctx {} globals = .ok s₀ → ∀ i < globals.size,
  ∃ z, defaultValue ctx globals[i].typ = .ok z ∧ Heap.lookup s₀.heap (.base ⟨i⟩) = some (.value globals[i].typ z)`.
* **514 `seedGlobals_heap_size`** — `s₀.heap.size = globals.size` (the base of the design's §3.3 conjunct).
* **515 `seedGlobals_wf`** — `seedGlobals ctx {} globals = .ok s₀ → StateWf ctx s₀`, UNCONDITIONAL.

Deviation from the request's wording, and why. The request says «the normalized zero cells». The cell in the
statement is `.value g.typ z` with `z` the zero value itself — no normalizer appears — because the zero value is
already normal at its type: `defaultValue_isNormal`/`defaultValue_normalize` (`MachineSound.lean`) are theorems,
so `Store.alloc`'s normalization at seeding returns the zero value unchanged. The design's own cell
(`.value g.typ (zero g.typ)`, §3.1) is this one. `seedGlobals_wf` is stronger than the design expected (§6's
`SeedPlan` planned to DECIDE «default normalizes to itself and contains no location» per program): both are
theorems for every type (`defaultValue_locSup`, `defaultValue_isNormal`), so `SeedPlan` reduces to «`seedGlobals`
succeeds», and G-R1 carries no `StateWf` premise.

### G-R1 — the general setup equation (row 516)

**516 `runProgramSetup_init`** — mirroring `runProgramSetup_noInit` with the two program-level premises
(`globals = #[]`, no `$pkginit`) replaced by the phases' RESULTS:

```
findFunctionIn? program.funcs ⟨name⟩ = some func → func.args.size = args.size →
program.typeDefs.hasReservedPrefix = true →
seedGlobals ⟨program⟩ {} program.globals = .ok s₀ →
runPkgInitM ⟨program⟩ fuel s₀ choices = .ok (s₁, choices₁) →
bindParams ⟨program⟩ [] s₁ func.args.toList args.toList = .ok (env, s₂) →
allocDecls ⟨program⟩ env s₂ func.results.toList = .ok (frameEnv, s₃) →
pinResultLocs frameEnv func.results.toList = .ok resultLocs →
runProgramSetupM fuel program name args choices
  = .ok (⟨program⟩, .exec func.body frameEnv (.frame [] [] [] [] .stop func.id), s₃, resultLocs, choices₁)
```

Deviation: the request lists «seeding, StateWf, runPkgInitM and the entry bind as one rewrite». The `StateWf`
check IS in the rewrite — discharged internally by `seedGlobals_wf`, so it is not a premise (one fewer obligation
for the client). `runProgramSetup_noInit` is this at `seedGlobals_nil` + `runPkgInitM_none` (an `example` in
`SetupSound.lean` re-derives its exact statement).

### G-R3 — the entry layout from a pre-bind store (rows 517–520)

The four `{}`-store lemmas of `Equations.lean` with `{}` replaced by an arbitrary `s₁` (the post-init store), the
environment `[]` as in the seam, the same `namesDistinct` premise:

* **517 `setup_lookup_arg_from`** — `LocalEnv.lookup frameEnv func.args[i].id = some (entrySlot s₁ i)`.
* **518 `setup_lookup_result_from`** — `LocalEnv.lookup frameEnv func.results[j].id = some (entrySlot s₁ (func.args.size + j))`.
* **519 `setup_resultLocs_from`** — `resultLocs = (List.range func.results.size).map (fun j => entrySlot s₁ (func.args.size + j))`.
* **520 `setup_heap_size_from`** — `s₃.heap.size = s₁.heap.size + func.args.size + func.results.size`.

No deviation. Each `{}` lemma's statement is re-derived as an `example` in `SetupSound.lean` by `simpa [entrySlot]`
(`entrySlot {} i = .base ⟨0 + i⟩`). The names carry `_from` («from the store `s₁`»); the old names stay on the `{}`
forms.

## 3. G-R4 — reviewed, approved, proved (phase 3)

### 3.1 The review and the logic team's answers (verbatim, with provenance)

Phase 2 sent the statement below WITH a second premise (no blocked configuration reached) and four points for the
requesters (the dispensability of that premise; the guard's spelling; whether to pin the `run_*_iff`-style
corollaries; whether a `runPkgInitM`/`markInitPhase` wrapper equation is wanted). The reply — the golean-logic
coordinator, 2026-10-05, by cross-session message, relayed by the [AGENT] coordinator; cite as relayed — verbatim:

> «G-R1–G-R3 look exactly right, and both deviations are improvements … On G-R4, approved as stated with these
> answers: (a) DROP the no-blocked premise. If it's dispensable (stepFn throws on a blocked config so no Prefix
> passes one, and both loops give .deadlock), the theorem is stronger and cleaner without it; our init-mode adequacy
> wouldn't have to discharge it. (b) Keep `initPrintRefusal? c' = none` — it's the guard runInitConfig actually uses
> … Keep the `n ≤ fuel` bound as you found it must be. (c) Yes, please pin the run_ok_iff-style corollaries for
> runInitConfig (ok / panic / fuelOut / deadlock characterizations via Prefix/Finish, under the no-print premise) —
> our init-prefix adequacy theorem composes with the existing Prefix/Finish statements through them. (d) Yes, please
> add the runPkgInitM / markInitPhase wrapper equation relating runPkgInitM to runInitConfig on the init
> configuration — G-R1's premise is stated over runPkgInitM's result, so we need that link to reach runInitConfig
> and then (via G-R4) execStmtLoop. No other changes. Prove as above; we'll consume them at the next (additive)
> re-pin.»

Phase 3's instruction ([AGENT] coordinator, 2026-10-05): prove G-R4 with the four answers applied, on the same
branch by added commits (an auditor reads `36e0b302`), with the standing rule «if dropping the premise turns out
false, STOP and report the counterexample». It did not: the proof went through without it (§3.2).

### 3.2 What changed, and the final G-R4 statement (row 521)

Answer (a) applied — the second premise is gone; nothing else in the text changed (answer (b)):

```lean
def runInitConfig_eq_execStmtLoop_stmt : Prop :=
  ∀ {ctx : ProgramCtx} {fuel : Nat} {σ : Store} {c : Config} {ch : Choices},
    (∀ (n : Nat) (σ' : Store) (c' : Config) (ch' : Choices) (ls : List StepLabel),
      Prefix ctx n σ c ch ls σ' c' ch' → n ≤ fuel → initPrintRefusal? c' = none) →
    runInitConfig ctx fuel σ c ch = execStmtLoop ctx fuel σ c ch
```

PROVED (`SetupSound.lean`, `runInitConfig_eq_execStmtLoop`), by the argument of the review: `runInitConfig` and
`execStmtLoop` (`StepFn.lean`) have the same five zero-cost arms — `.next .stop ↦ .ok (σ, ch)`, the four blocked
shapes `↦ .error .deadlock` — and differ in exactly one place: in the default arm, `runInitConfig` consults
`initPrintRefusal? c` and throws before the fuel match; after that both do `0 ↦ .fuelOut` and `fuel+1 ↦ stepFn ctx
σ c ch >>= recurse`. The proof is the induction on `fuel`, generalizing `σ c ch`, through the init loop's one-layer
unfolding `runInitConfig_unfold` (the twin of `MachineSound.lean`'s `execStmtLoop_unfold`) and its two
consequences `runInitConfig_blocked` / `runInitConfig_nonZero` (the twins of `Prefix.lean`'s): at a zero-cost
configuration both sides agree outright; otherwise the premise at `n = 0` (`Prefix.done`) silences the guard, both
loops fall to the same fuel match, and on a successful step the premise transfers to the successor through
`Prefix.step`. The bound stays `n ≤ fuel` (at `n < fuel` the statement is false: fuel 0 at a print position is
`.error (refusal)` vs `.error .fuelOut` — checked by `#eval`).

### 3.3 The corollaries (answer (c); rows 522–525)

`ExecutionStatement.lean`'s `run_ok_iff` / `run_panic_iff` / `run_deadlock_iff` / `run_fuelOut_iff` (rows 44–47)
for `runInitConfig`, each with the no-print premise prepended and the SAME right-hand side (`Prefix`, `Finish`,
`ZeroCost`), so the init-prefix adequacy composes with the existing `Prefix`/`Finish` statements through them:

* **522 `runInitConfig_ok_iff`** — `runInitConfig ctx fuel s c ch = .ok (sf, chf) ↔ ∃ n, n ≤ fuel ∧ ∃ ls, Prefix ctx n
  s c ch ls sf (.next .stop) chf`.
* **523 `runInitConfig_panic_iff`** — `… = .error (.terminal (.panic t)) ↔ ∃ n ls sf cf chf ch'' rec, n + 1 ≤ fuel ∧
  Prefix ctx n s c ch ls sf cf chf ∧ Finish ctx sf cf chf rec (.aborted t sf ch'') 1`.
* **524 `runInitConfig_deadlock_iff`** — `… = .error (.terminal .deadlock) ↔ ∃ n, n ≤ fuel ∧ ∃ ls sf cf chf, Prefix …
  ∧ Finish ctx sf cf chf [] (.deadlock sf chf) 0`.
* **525 `runInitConfig_fuelOut_iff`** — `… = .error .fuelOut ↔ ∃ ls sf cf chf, Prefix ctx fuel s c ch ls sf cf chf ∧
  ¬ ZeroCost cf`.

Each proof is G-R4's rewrite followed by the sequential statement. (The refusal/`fatal` endings are not
characterized by `iff` for the sequential loop either; nothing was asked for them.)

### 3.4 The wrapper (answer (d); rows 526–527)

The twin of `Equations.lean`'s `runPkgInitM_none` (row 396), for `$pkginit` PRESENT — nullary and resultless, the
design's `Definition ctx hI [] [] Dinit`:

* **526 `runPkgInitM_some`** — `findFunctionIn? ctx.functions pkgInitFuncId = some initF → initF.args.size = 0 →
  initF.results.size = 0 → runPkgInitM ctx fuel s ch = (runInitConfig ctx fuel s (.exec initF.body [] (.frame [] []
  [] [] .stop initF.id)) ch).mapError markInitPhase`. `markInitPhase` prefixes `stuck`/`unsupported`/`internal` with
  `package init:` and passes `fuelOut` and the terminals unmarked.
* **527 `runPkgInitM_ok_iff`** — the SUCCESS link G-R1's premise composes with: `runPkgInitM ctx fuel s ch = .ok (s₁,
  ch₁) ↔ runInitConfig ctx fuel s (.exec initF.body [] (.frame [] [] [] [] .stop initF.id)) ch = .ok (s₁, ch₁)`.

The chain the logic team asked for is now pinned end to end: G-R1's premise `runPkgInitM ⟨program⟩ fuel s₀ choices =
.ok (s₁, choices₁)` → (527) `runInitConfig` on the init configuration → (521, under no-print) `execStmtLoop` → (522,
or row 3 `run_ok_iff`) a `Prefix` of length `n ≤ fuel` from `(s₀, cI, choices)` to `(s₁, .next .stop, choices₁)`.
`ctx.functions ⟨program⟩` is `program.funcs` by `rfl` (as `runProgramSetup_noInit`'s proof already uses).

## 4. The `{}`-store corollaries

The brief asked that the existing `{}` lemmas be kept and, if natural, re-derived as corollaries. They are kept
UNCHANGED in `Equations.lean` (statements and proofs; re-deriving them in place would invert the module dependency
— `Equations.lean` would have to import the new proofs). The derivability is shown instead by five `example`s at the
end of `SetupSound.lean`, each stating the pinned `{}` form verbatim and closing by the general one:
`runProgramSetup_noInit`'s statement from `runProgramSetup_init` + `seedGlobals_nil` + `runPkgInitM_none`; the four
`setup_*` statements from the `_from` forms by `simpa [entrySlot]`.

## 5. Controls (`#eval` first — the #eval-first rule — then `rfl`)

`SetupStatement.lean`, section `Controls`. The program `initControl`: `var g int; func init() { g = 7 }; func F()
(z int) { z = g }`.

* Seeding: `seedGlobals ⟨initControl⟩ {} initControl.globals = .ok { heap := #[.value .int (.int 0 .int)] }`.
* The run: `runProgramM 12 initControl "F" #[] = .ok { values := #[.int 7 .int] }` (fuel 12 the least that
  completes; `set_option maxRecDepth 8192 in` for this one reduction — the elaborator's default depth, not the
  kernel, is what the bare `rfl` exhausted).
* G-R4 positive, at the init configuration `runPkgInitM` builds: the two loops AGREE at fuel 10 (the body's step
  count; both `.ok ({ heap := #[.value .int (.int 7 .int)] }, [])`), at fuel 9 (both `.fuelOut`) and at 0.
* G-R4 negative — the no-print premise is load-bearing: at `printPosition` (a `println(1)` apply position)
  `runInitConfig … 4 {} … = .error (refusal …)` (the init-phase text, pinned byte-for-byte on `initPrintRefusal?`)
  while `execStmtLoop … 4 {} … = .ok ({}, [])`.
* The wrapper (phase 3): `runPkgInitM ⟨initControl⟩ 10 {seeded} [] = runInitConfig ⟨initControl⟩ 10 {seeded}
  initControlConfig []`, both `.ok ({ heap := #[.value .int (.int 7 .int)] }, [])`.

## 6. For the train (records, not this lane's to write)

* Post-offer changelog row (`docs/changelog/20d3946d-WINDOW.md`), draft: «additive, no existing statement or
  behaviour changed: the setup equations G-R1–G-R4 (the logic team's 2026-10-05 request; G-R4 approved 2026-10-05
  with answers (a)–(d), relayed) — new modules `GoLean/GoCore/SetupStatement.lean` (statements) and
  `GoLean/GoCore/SetupSound.lean` (proofs); BridgeSet RE-PIN 12, rows 512–520 (`seedGlobals_cells`, `_cell`,
  `_heap_size`, `_wf`; `runProgramSetup_init`; `setup_lookup_arg_from`, `_result_from`, `setup_resultLocs_from`,
  `setup_heap_size_from`) and RE-PIN 13, rows 521–527 (`runInitConfig_eq_execStmtLoop` — no blocked premise;
  `runInitConfig_ok_iff`/`_panic_iff`/`_deadlock_iff`/`_fuelOut_iff`; `runPkgInitM_some`, `runPkgInitM_ok_iff`);
  rows 1–511 and 397, 399–402 unchanged; two NO-EXECUTION rows in `scripts/mem-callsites.tsv`. [USER] Mike
  2026-10-05 «(1) Go ahead», relayed; the logic team's approval of G-R4 relayed by the [AGENT] coordinator.»
* Certificate provenance: STALE on this branch (it touches `GoLean/`); the train's step 5a refreshes it.
* The G-R4 relay is CLOSED (approved and proved, §3); the logic team consumes rows 512–527 at the next additive
  re-pin.

## 7. Gate tails (worktree `.claude/worktrees/setup-eqs`, branch `core/setup-equations-1005`, all under the box lock)

* `scripts/capped lake build GoLean` — `Build completed successfully (64 jobs).` EXIT=0, warning-free (the two new
  modules and the re-pinned `BridgeSet` built warning-free in their explicit-target builds; one linter round trimmed
  unused `simp` arguments).
* `scripts/check-core-audit` — `Core totality audit: 61 GoLean modules in the closure (52 under GoLean.GoCore), all
  on disk; 554 required theorems present; 20511 declarations across all imported local modules; classical trio
  only` · `Core totality audit gate: PASS` EXIT=0.
* `scripts/check-equations` — `Equation gate: PASS (client PASS, exhaustive enrollment, the Lean-level no-unfold
  check over the closure up to the published API, the import whitelist, the regex pre-filter, 12 self-tests)`
  EXIT=0.
* `scripts/check-pool-spec` — `ok [frozen] both files and 48 statements match docs/specs/pool-relation/FROZEN.sha256`
  · `ok [discharge] LANDED=M1 … all 9 statements of M1..M1 discharged` EXIT=0.
* `scripts/check-mem-callsites` — `Memory-module raw call-site inventory: PASS (74 (file, declaration, raw-op)
  rows, all inventoried with reasons)` EXIT=0 (after the two rows of §1 — the first fast `scripts/ci` named them:
  `NEW GoLean/GoCore/SetupSound.lean seedStep alloc 1`, `NEW GoLean/GoCore/SetupStatement.lean seedGlobals_cell_stmt
  Heap.lookup 1`).
* `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci` (fast, first run) — `RESULT: FAIL`, 523 s: the inventory rows above,
  and `FAIL baseline diff (NO recorded differential run …)` / `FAIL negative baseline diff (NO recorded negative run
  …)` — a FRESH worktree has no per-checkout `artifacts/coverage/latest.tsv`; resolved by running the differential
  here rather than by `GOLEAN_ALLOW_NO_DIFF`.
* `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff` — `RESULT: FAIL`, `CI total wall seconds: 964`. Every step
  `ok` (core build warning-free; core totality audit; semantic equations; pool spec; frontend pins; eval tests 298
  ok; `differential run completed`; `negative run completed`; `no regression: 394 case(s) run in
  negative-latest.tsv match baselines/negative-full.tsv`) EXCEPT the two lines of ONE cause, the expected 5a-class
  STALE certificate on a branch that touches `GoLean/`:
  `FAIL certificate provenance` (`certification: STALE certification: changed dependency build/files/GoLean.lean`)
  and its echo `FAIL baseline diff (DRIFT — see above)`: `DRIFT vs baselines/native-full.tsv (3884 case(s) run):
  imported-goose/channel/google-search baseline[PASS/membership] -> now[FAIL/membership]` with detail
  `certification: STALE certification: changed dependency build/files/GoLean.lean` — the tier=slow case judged from
  its cached certified record, which `GoLean.lean`'s change invalidates (the `baselines/native-full.tsv` header
  records this exact item on every GoLean-touching train: «the 5a-class item … not re-pinned here»). NOT re-pinned
  here; the train's step 5a (`scripts/ci --slow`, candidate installed as the round's records commit) refreshes it.
  No other row moved. The negative record notes `git_dirty=true` (run before this commit).

**Phase 3 (G-R4 proved; the same gates, same lock, re-run at the phase-3 tree):**

* `scripts/capped lake build GoLean` — `Build completed successfully` EXIT=0, 0 warnings.
* `scripts/check-core-audit` — `Core totality audit: 61 GoLean modules in the closure (52 under GoLean.GoCore), all
  on disk; 561 required theorems present; 20563 declarations across all imported local modules; classical trio
  only` · PASS (554 → 561: the seven new required theorems).
* `scripts/check-equations` — `Equation gate: PASS (… 12 self-tests)`.
* `scripts/check-pool-spec` — `ok [discharge] LANDED=M1 … all 9 statements of M1..M1 discharged` · PASS.
* `scripts/check-mem-callsites` — `PASS (74 (file, declaration, raw-op) rows, all inventoried with reasons)` (no
  new raw sites: the phase-3 proofs touch no memory operation).
* `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci` (fast) — `RESULT: FAIL`, 513 s, on exactly the same two lines of
  the one expected cause: `FAIL certificate provenance` (`certification: STALE certification: changed dependency
  build/files/GoLean.lean`) and its echo `FAIL baseline diff (DRIFT — see above)` — `DRIFT vs
  baselines/native-full.tsv (3884 case(s) run): imported-goose/channel/google-search baseline[PASS/membership] ->
  now[FAIL/membership]` (judged from this worktree's phase-2 `--diff` record; the fast gate re-runs no Go). Every
  other step `ok`. Not re-pinned; the train's 5a refreshes it.
