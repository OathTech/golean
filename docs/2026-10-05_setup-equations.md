# The setup equations G-R1–G-R4 (lane `core/setup-equations-1005`)

[AGENT worker, lane `core/setup-equations-1005`] 2026-10-05. Authority: [USER] Mike 2026-10-05 «(1) Go ahead»
(relayed by the [AGENT] coordinator; scheduled after train r66, main `7a0a1568`). The request, verbatim:
`docs/2026-10-05_note-from-logic-team-setup-equations.md` (the golean-logic coordinator, «with Mike's approval»);
the requesters' design (read-only): golean-logic branch `design/globals-init-1005`,
`docs/2026-10-05_globals-init-design.md` §3.1, §5–§6, §9. The [AGENT] coordinator's committed reply: additive only
— new names, the existing pinned statements unchanged, the old `{}`-store forms kept as corollaries — and G-R4's
exact statement goes to the logic team for review BEFORE it is proved. This note is that delivery.

## 1. What landed (phase 1: G-R1–G-R3 proved; phase 2: G-R4 stated)

| File | Content |
|---|---|
| `GoLean/GoCore/SetupStatement.lean` (new) | the `def <name>_stmt : Prop` of G-R1–G-R4 (the `ExecutionStatement`/`PoolStatement` grain); the one new definition `zeroCell`; `rfl` controls after `#eval` (§5) |
| `GoLean/GoCore/SetupSound.lean` (new) | `theorem <name> : <name>_stmt` for the nine statements of G-R1–G-R3; `example`s re-deriving the `{}`-store statements of `Equations.lean` from the general forms |
| `GoLean/GoCore/BridgeSet.lean` | RE-PIN 12: rows 1–511 byte-identical; rows 512–520 ADDED (the nine, written out); import of `SetupSound` |
| `Tests/GoCoreAudit.lean` | the two modules in `requiredModules`; the nine theorems in `exports` |
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

## 3. G-R4 statement for the logic team's review

STATED, NOT PROVED (`GoLean/GoCore/SetupStatement.lean`, `runInitConfig_eq_execStmtLoop_stmt`; it elaborates; not
pinned in `BridgeSet.lean` until proved). The exact Lean text:

```lean
def runInitConfig_eq_execStmtLoop_stmt : Prop :=
  ∀ {ctx : ProgramCtx} {fuel : Nat} {σ : Store} {c : Config} {ch : Choices},
    (∀ (n : Nat) (σ' : Store) (c' : Config) (ch' : Choices) (ls : List StepLabel),
      Prefix ctx n σ c ch ls σ' c' ch' → n ≤ fuel → initPrintRefusal? c' = none) →
    (∀ (n : Nat) (σ' : Store) (c' : Config) (ch' : Choices) (ls : List StepLabel),
      Prefix ctx n σ c ch ls σ' c' ch' → n ≤ fuel → ¬ Blocked c') →
    runInitConfig ctx fuel σ c ch = execStmtLoop ctx fuel σ c ch
```

(`Prefix`, `Blocked` from `ExecutionStatement.lean`; `initPrintRefusal?`, `runInitConfig`, `execStmtLoop` from
`StepFn.lean`.) Instantiated at `runPkgInitM`'s own call — `σ := s₀` (the seeded store), `c := .exec initF.body []
(.frame [] [] [] [] .stop initF.id)` — it turns the init phase into an `execStmtLoop` run, so every pinned
`execStmtLoop` bridge (rows 3, 5, 500–501 and `Prefix.lean`'s classification) applies to it; `markInitPhase` then
only re-labels diagnostic errors.

**Truth argument (one paragraph).** `runInitConfig` and `execStmtLoop` (`StepFn.lean`) have the same five
zero-cost arms — `.next .stop ↦ .ok (σ, ch)`, the four blocked shapes `↦ .error .deadlock` — and differ in exactly
one place: in the default arm, `runInitConfig` consults `initPrintRefusal? c` (= `some e` iff `printOut? c = some
_`) and throws `e` before the fuel match; after that both do `0 ↦ .fuelOut` and `fuel+1 ↦ stepFn ctx σ c ch >>=
recurse`. Induction on `fuel`, generalizing `σ c ch`: at a zero-cost arm both sides agree outright; in the default
arm the first premise at `n = 0` (`Prefix.done`) gives `initPrintRefusal? c = none`, so `runInitConfig` falls
through to the same fuel match; at `fuel = 0` both are `.fuelOut`; at `fuel + 1` both call the same `stepFn` — on
`.error e` both are `.error e`; on `.ok (c', σ', ch', l)` both recurse, and both premises transfer to
`(σ', c', ch')` at bound `fuel` through `Prefix.step` (a prefix of length `n` from the successor is a prefix of
length `n + 1 ≤ fuel + 1` from the start). The bound is `n ≤ fuel`, not `n < fuel`: the configuration reached at
step `fuel` IS inspected by the guard before the fuel-out, so the premise must cover it (at `n < fuel` the
statement is FALSE: fuel 0 at a print position gives `.error (refusal)` vs `.error .fuelOut`). ∎

**Points for the requesters.**

1. *The blocked premise is dispensable.* Both loops classify a blocked configuration as `.deadlock` before any
   guard, and `stepFn` itself throws `.deadlock` on one (`StepFn.lean:1054`), so no `Prefix` passes through a
   blocked configuration; the equation holds without the second premise. It is kept as the request names it
   («when no print or blocked configuration is reached», design §5.5). Say whether to keep it (it costs the client
   one discharge, which `NotStuck` in `init` mode gives anyway) or drop it (the stronger, premise-lean form; the
   proof is the same).
2. *The guard's spelling.* The no-print premise is `initPrintRefusal? c' = none`, the loop's own guard and the
   design's §5.2 side condition on `Prim.step`. `printOut? c' = none` is equivalent (`initPrintRefusal?` reads
   nothing else) and is the form the design's generic liftings carry; either can be the pinned spelling.
3. *The quantifier shape* follows rows 500–501 (`∀ n σ' c' ch' ls, Prefix ctx n σ c ch ls σ' c' ch' → n ≤ fuel →
   …`). A `Finish`-side corollary (`runInitConfig … = .ok (sf, chf) ↔ ∃ n ≤ fuel, Trace …`, the `run_ok_iff` twin)
   follows from this equation and row 3; say if it should be pinned as well.
4. The statement is silent on `markInitPhase`: `runPkgInitM` wraps `runInitConfig`'s error with it (`fuelOut`,
   `panic` unmarked; `stuck`/`unsupported`/`internal` get the `package init:` prefix). If the logic needs the
   wrapper as a rewrite too (`runPkgInitM` with `$pkginit` present, in terms of `runInitConfig`), name it; it is a
   one-line equation we can add to the same lane.

Once the text is confirmed (or amended), the proof is the induction above, in `SetupSound.lean`, and the row is
pinned at 521.

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

## 6. For the train (records, not this lane's to write)

* Post-offer changelog row (`docs/changelog/20d3946d-WINDOW.md`), draft: «additive, no existing statement or
  behaviour changed: the setup equations G-R1–G-R3 (the logic team's 2026-10-05 request) — new modules
  `GoLean/GoCore/SetupStatement.lean` (statements; G-R4 stated only, out for review) and
  `GoLean/GoCore/SetupSound.lean` (proofs); BridgeSet RE-PIN 12, rows 512–520 (`seedGlobals_cells`, `_cell`,
  `_heap_size`, `_wf`; `runProgramSetup_init`; `setup_lookup_arg_from`, `_result_from`, `setup_resultLocs_from`,
  `setup_heap_size_from`); rows 397, 399–402 unchanged. [USER] Mike 2026-10-05 «(1) Go ahead», relayed.»
* Certificate provenance: STALE on this branch (it touches `GoLean/`); the train's step 5a refreshes it.
* The G-R4 relay: §3 above, to the logic team; the proof lands in a follow-up on their confirmation.

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
