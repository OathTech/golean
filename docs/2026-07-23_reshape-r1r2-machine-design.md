# Reshape R1+R2: the fine-grained machine — design of record (2026-07-23)

Step-0 note for the reshape arc (branch `reshape-smallstep`), executing
`docs/2026-07-22_f4-concurrency-model.md` §7 stages R1–R2 (and sequencing
R3). The F4 note is the charter (why, granularity, deletion directive);
this note is the *how*: the concrete machine, the coverage split, the
staging that keeps every commit green, and the gates.

## 0. The scoping fact F4 didn't spell out

The interpreter's fragment is a strict superset of the relation's. The
relation (`Rel.lean`, 574 lines) covers the proof-facing core: scalar
arithmetic, `eqCmp`, `ref`/`deref`/`locLit`, `fieldGet`, `indexGet`,
assign, initialization, seq/block/if/while, break/continue/return, direct
calls. The interpreter (`Eval.lean`, 970 lines + `Ops.lean`) additionally
executes: strings and conversions, all comparisons, bitwise/shift ops,
short-circuit `and`/`or`, slices (make/index/slice/append/copy), maps
(make/get/assign/lookup/range), interfaces (`toInterface`, `typeAssert`,
dynamic dispatch), `assignMany`, `newValue`, labels.

The R2 gate is **zero drift on the full 718-case differential**, and the
differential runs the interpreter. So the new machine's *executable* must
cover the full interpreter fragment from day one, while the *relation*
keeps exactly its current claims surface. Consequence: the machine is
designed so both are instances of one configuration language, with the
relation's rules a subset of what `stepFn` executes (§3).

## 1. The machine

One configuration language (new module `GoLean/GoCore/Machine.lean`;
`Rel.lean` is retired at stage S4 — the "relation vs interpreter" file
split dissolves when the interpreter becomes the relation's
instantiation).

### Configurations

Extends the current CK `Config` with expression evaluation **in the
configuration language** (this is what kills BUG-002's root):

```
inductive Config where
  | exec (stmt : Stmt) (env : LocalEnv) (k : Cont)   -- as today
  | evalE (e : Expr) (env : LocalEnv) (k : Cont)     -- NEW: evaluating e
  | retV (v : GoValue) (k : Cont)                    -- NEW: delivering a value
  | next (k : Cont) | breaking (k : Cont)
  | continuing (k : Cont) | returning (k : Cont)
  | panicked (msg : String)
```

`retV` is the explicit value-delivery configuration (chosen over fusing
value delivery into each producing rule): it gives the machine a uniform
redex/value discipline — every frame receives its operand value through
one rule shape — which is what keeps the per-rule lemma set small.
`ToVal` remains `.next .stop` only; `retV` never reaches `.stop` (an
expression is always evaluated under at least one frame).

### Continuations

The statement frames survive unchanged (`seq`, `loop`, `frame` — with
`loop` now storing no condition re-evaluation shortcut; see rules).
Expression evaluation adds **defunctionalized operand frames**, and the
key design move is *one generic frame for all strict operators* instead
of one frame per operator:

```
  | strictOp (op : StrictOp) (done : List GoValue)
             (pending : List Expr) (env : LocalEnv) (k : Cont)
```

`StrictOp` is a defunctionalized head — `add`, `sub`, …, `eqCmp ty`,
`convert ty`, `deref ty`, `indexGet`, `mapGet kTy vTy`, `fieldGet id f`,
`slice`, `length`, `structLit ty`, `typeAssert ty`, … — everything whose
Go semantics is "evaluate operands left-to-right, then apply". Two step
rules serve every strict operator:

- shift: `retV v (strictOp op done (e :: rest) env k)
  → evalE e env (strictOp op (v :: done) rest env k)`
- apply: `retV v (strictOp op done [] env k)` → apply `op` to
  `(v :: done).reverse`, one step.

The apply step is where memory operations happen (`deref` = one load,
`indexGet` on a slice = one load, `mapGet` = one load of the map-data
cell), where panics fire (`→ .panicked msg`), and where the machine is
silent on stuck/unsupported (§4). The application functions are the
existing `Ops.lean`/`Eval.lean` helpers with their `evalExpr` recursion
stripped to pure value-level residues (they move to `Machine`-adjacent
ops; `evalExpr` itself is deleted).

Non-strict or zero-operand forms get their own small rule sets: literals /
`var` / `ref` / `locLit` / `nil` / `defaultValue` step directly to `retV`
(`var` is env lookup + **one load step**); `and`/`or` get short-circuit
frames; unary `not`/`bitNeg` fit `strictOp` with one operand.

### Statement decomposition

Statements stop consuming `ExprR` and instead push expression
configurations with statement frames:

- `if`/`while`: `exec (.ifThenElse c t e) env k → evalE c env (.ifCond t
  e env k)`; `retV (bool true) …` dispatches. Same for `while` with
  `.whileCond`.
- `assign`: target resolution then RHS then store, each its own step —
  `.var` target resolves in one pure step; `.addr e` target evaluates `e`
  through the machine; then `evalE rhs env (.assignStore loc k)`; then
  the **store step**. `Step.assign` no longer bundles reads with the
  write.
- `call`: staged frames — resolve targets (assignee list, machine-order),
  evaluate args left-to-right, then the frame-entry step (bind params,
  declare results, pin result locs — one step, as today's `Step.call`
  minus the argument evaluation it currently swallows).
- Wide statements (`assignMany`, `makeSlice`, `makeMap`, `mapAssign`,
  `mapLookup`, `typeAssert`, `appendSlice`, `copySlice`, `newValue`): one
  generic `stmtOp` frame in the same shape as `strictOp`, over an operand
  plan of exprs *and assignees* (so evaluation order exactly matches
  today's interpreter, which resolves targets first), ending in one apply
  step that performs the state update via the stripped helper.
- `mapRange`: an iteration frame (`remaining` snapshot); the pick-next
  step consumes a `Choices` entry (the one nondeterministic step class in
  the sequential machine, plus append's capacity choice).

### Granularity ledger (honest coarse spots, tracked)

Cell-level atomicity: our heap is cell-granular (a whole array/mapData is
one cell), so most "wide" apply steps are 1–2 memory operations already.
The deliberately-coarse residue, recorded per the F4 fault-model
discipline:

- `appendSlice` (BOTH paths — the in-place path is a store *loop* over
  the shared backing cell, the spill path a fresh-backing build; the
  in-place loop is the more concurrency-relevant of the two), `copySlice`:
  multi-write loops in one apply step. Fine sequentially; they must be
  decomposed (or their non-atomicity otherwise modeled) before any
  concurrency claim mentions them (R4 gate item — which in any case
  re-audits EVERY apply step, per below). Go itself gives these no
  atomicity. (Precision fix from the 2026-07-23 mid-arc audit: the
  earlier wording named only the spill path.)
- `stmtOp`/`strictOp` apply steps that both read and write remain single
  steps only where Go's own memory model would make the region
  single-threaded-observable; the R4 review re-audits every apply step
  against the goroutine interleaving before goroutine rules land.

## 2. Locals unification: `ExecState.locals` dies

The relation already carries the environment in the configuration (CEK,
env-in-control); the interpreter still resolves names via
`ExecState.locals` — the correspondence bridge. The new interpreter *is*
the relation instantiated, so it uses `Config`'s `env` and heap cells,
period. At stage S4, `ExecState.locals` is deleted; entry points
(`runFunctionWithContext`, CLI) allocate argument cells and build the
frame `LocalEnv` directly; `lookupLoc`/`declareLocal`'s locals half and
the `σ.locals ≈ Config.env` bridge disappear. One name-resolution story,
one scope story (continuation-carried), everywhere.

## 3. Relation vs. executable: one machine, two coverages

**S1 refinement (2026-07-23, supersedes the coverage phrasing below):**
the relation's expression rules are *generic* over the shared op table —
`enter` (via `strictPlan`), `shift`, and `apply` (via `applyStrictOp` as a
function premise) — so the relation automatically covers every strict
expression form the executable covers, with one table validated by the
differential oracle. This is "one semantics, instantiated" taken
literally: `stepFn`'s arms and the relation's premises call the same
functions, making the per-rule soundness/completeness lemmas nearly
definitional. The *claims* surface remains scoped by which WP laws and
witnesses exist (unchanged doctrine); statement-side wide features
(`assignMany`, map/slice statement forms, `mapRange`) still get their
frames/rules at S2.

- `Machine.Step : Config → ExecState → Config → ExecState → Prop` — rules
  for the current relation fragment's statements + generic expression
  rules (see refinement above). Panics are rules; stuck/unsupported is
  silence.
- `stepFn : Config → ExecState → Choices → Except GoError (Config ×
  ExecState × Choices)` — total on the full interpreter fragment;
  `.error` exactly where the machine is stuck/unsupported (with the
  *why*, as today); `.panicked` configs arise as normal steps.
- Execution = fuel-bounded iteration of `stepFn` to a terminal config
  (`next .stop` / `panicked`). Fuel exhaustion reports the existing
  message (runner compatibility).
- **Per-rule lemmas replace T1/T2** (`Correspondence.lean` deleted):
  soundness — on the relation fragment, `stepFn c σ ch = .ok (c', σ', _)`
  implies `Step c σ c' σ'`; completeness — every `Step c σ c' σ'` is
  realized by `stepFn` for suitable `Choices`. Stated per rule/config
  head, composed once. Wide-fragment configs are outside both lemmas,
  exactly as they are outside T1/T2 today.

## 4. Fault model in the machine

Unchanged classification, new mechanics (`docs/2026-07-22_fault-model.md`
still governs): panic = in-model behavior = a step to `.panicked` (both
relation and `stepFn`); stuck/unsupported = out-of-model = `stepFn` error
with reason, relation silence; fuel = driver-level, distinguished. The
runner's three-way split and messages are preserved verbatim — that is
part of the zero-drift gate (fault *identity*, not just existence).

## 5. Fuel

Fuel becomes **machine steps** (today: while back-edges + call entries
only). The CLI default (`GoLean/CLI.lean`, currently 100000) is retuned
upward (initial guess 10^6–10^7; set empirically at S3 so every currently
passing case passes with headroom ≥10×). `--fuel` keeps its shape; its
unit changes — noted in CLI help. This is the "concrete-fuel pins retune"
the F4 note anticipated. Corpus cases that intentionally exhaust fuel (if
any) must classify identically; verified at S3.

## 6. Staging: parallel build, flip, delete

The deletion directive (F4 §2) binds the **final state** — no big-step
survivors, no shim. The path there keeps every commit green by building
the new machine alongside, flipping the executable under the differential
gate, then deleting:

- **S0 — this note.**
- **S1 — `Machine.lean`**: Config/Cont/StrictOp + the fine-grained `Step`
  relation for the core fragment. Additive; builds green.
- **S2 — `stepFn`** covering the full interpreter fragment + iteration
  drivers, alternate entry points beside the old ones. Additive.
- **S3 — the flip**: CLI/eval-tests/differential entry points switch to
  the machine interpreter. Gate: full 718-case run, `scripts/
  coverage-baseline-diff` = zero drift; `gocore-eval-tests` green; fuel
  default retuned here. Old interpreter still present, now unreferenced.
- **S4 — the deletion**: `Eval.lean` big-step cluster, `ExprR` + old
  `Step` rules (`Rel.lean`), `Correspondence.lean`, `ExecState.locals` —
  removed. Proof modules that consumed them are temporarily pruned from
  the root import with a tracked list in `GoLeanProofs.lean` (visible,
  fail-closed: `Audit.lean` sweeps what remains; the pruned list is the
  restoration checklist). Gate: full run zero drift again (nothing
  executable changed — the flip already happened).
- **S5 — per-rule soundness/completeness lemmas** (§3), restoring the
  interpreter-relation link at strictly finer grain than T1/T2.
- **S6… — R3 rebuild**: `Lang` (new `Config` wiring; `wp_bind` via
  continuation plugging — the CK-machine bind: filling the terminal
  `.stop` of a continuation with a second continuation is the
  `LanguageCtx` candidate, to be validated against iris-lean's interface
  when we get there), `Lifting`, `Laws/*` (HeapLang-shaped now that bind
  exists), `Adequacy`, Surface exit pipes, golden/loop witnesses.
  Surface statements restored **byte-identical** (F4 §2's wrapper
  decision); `execStmt`-shaped wrapper = fuel-iterated `stepFn`.

**Merge gate**: the branch merges only after S6 — full `scripts/ci
--diff` green, Audit sweep with zero pruned modules, Surface statement
content byte-identical to `main`'s, plus the standing pre-merge audit
ask. R1+R2 alone never reach `main` with the proof layer pruned.

## 6′. Stage log (updated as stages land; branch `reshape-smallstep`)

- **S0–S4 DONE (2026-07-23):** design note; `Machine.lean` (fine-grained
  relation, shared op tables); `stepFn` + drivers; THE FLIP (zero drift on
  718, eval tests 40/40, fuel default 10^7); THE DELETION (`Eval`/`Rel`/
  `Correspondence` + `ExecState.locals` gone; proofs pruned with tracked
  checklists; golden pin extracted to pure-syntax `GoldenProgram`;
  `scripts/ci` 11/11 PASS incl. zero drift re-verified post-deletion).
- **S5 DONE (2026-07-23):** `MachineSound.lean` — `stepFn_sound`
  (fun_cases over the definition tree), `step_complete` (∃-choice-stream
  realization; nondet rules witnessed by the encoding stream), and
  `runConfig_sound` (terminating runs are reachable `Steps` traces — the
  `interpreterSound` analogue, now total over the FULL fragment). T1/T2
  are replaced; sweep 3179 decls axiom-clean. Two stepFn adjustments for
  rule/arm one-to-one correspondence (decidable-eq init scope check;
  target pre-check only when operands remain), re-validated by eval tests
  + a full differential run.
- **MID-ARC ADVERSARIAL AUDIT (2026-07-23, user-approved):** 3
  decorrelated Opus reviewers (transcription fidelity vs the deleted
  big-step originals at rev `5a9eab2`; relation design; proof+gate
  integrity) + 2 refute-by-default Opus verifiers per finding, 13 agents.
  **5 findings, 0 sustained** — no semantic defect, no transcription
  error, no gate weakening; refutations spot-checked. Three elective
  precision fixes folded in: the granularity ledger now names BOTH
  `appendSlice` paths (the in-place store loop is the concurrency-relevant
  one); the recorded-divergences list gains the bare-`.initialization`
  fail-closed case; and the **driver-level panic corollary is explicitly
  QUEUED, not claimed** — `runConfig_sound` covers the normal terminal
  only; a `runConfig` panic error arises either from a reached
  `.panicked` configuration (relation-covered) or from a helper-
  propagated panic at a relation-silent site (e.g. frame-exit stores),
  so the panic-side driver theorem needs a reachability argument, not a
  one-line corollary — build it when an R3 witness needs it.
- **S6/R3 COMPLETE (2026-07-23):** every stratum restored over the
  machine. Infrastructure: Lang/HeapBridge/Ghost (namespace ports; Ghost
  now pins `methods` beside `prog` — the machine consults `σ.methods` at
  frame entry), Lifting (rule-agnostic cores, namespace port), Inversions
  REWRITTEN as one generic `step_det`. Laws: Control/Init verbatim; NEW
  Eval (the expression-walk step laws — the `wp_bind` answer: per-step
  laws composed, no `LanguageCtx`); Assign/Call/Loop rewritten as
  composed walks with same-commit witnesses (`wp_assign_lit`; the golden
  frame-entry instances on kernel-bridged literals; `wp_while_eq_once`
  with the bind-form condition — the arc-E recorded divergence CLOSED).
  Adequacy: all four exit doors + `adequate_seqn_nil`. Surface: the
  `execStmt`-shaped wrapper (`execStmtLoop`/`execStmt` +
  `execStmt_sound_normal`, total); two RECORDED statement deltas, both
  strengthenings (env as wrapper argument after `ExecState.locals` died;
  `InitialSplit.frag`/`HeapFrag` retired — machine soundness is total);
  SurfaceBridge untouched; SurfaceExit lost its fragment shape checks.
  Specs: GoldenSliceWP rewritten (body walks + `wp_goldenCall`(/`_inv`) +
  `wp_goldenDriver`); **ALL SIX golden targets re-proven**
  (`goldenSpec`/`goldenFuncSpec`/`goldenInvariant`/`goldenTriple`/
  `goldenReturnsTwo`/`goldenNotThree`). NegativeSpecs rewritten (pins at
  the resolution step + the shared op table). RETIRED: `Specs.Slice`,
  `Specs.SliceCorrespondence`, `Specs.GoldenSlice` (superseded; content
  at rev 5a9eab2; mapping in the Audit ledger). Audit gates LIVE again
  (21 curated pins + non-vacuity refs + new ledger; sweep 4208 decls
  clean); ci allowlist back to its original single entry. One incident
  during final validation, caught by the gate working as designed: the
  wrapper-soundness theorem's lint warnings replayed into the runner's
  JSON channel (the RECORDED ops failure mode) — mass phantom drift with
  IDENTICAL observations; fixed by keeping the proof file lint-clean;
  zero drift re-verified (718/718). Remaining before merge: the standing
  pre-merge audit ask (mid-arc audit covered S1–S5; scope R3's delta),
  merge + push sign-offs.

## 7. What survives untouched

Frontend + wire format, corpus, oracle and runner scripts, tracked
baseline, negative lane, `Syntax.lean`, `Value.lean`, `Ops.lean`'s typed
load/store/default/equality substrate, `Choices` externalization, the
Iris functor bundle / genHeap pattern, `embed`/`reflect` boundary layers,
all doctrine docs. `Heap`/`HeapCell`/alloc are unchanged — the reshape is
control, not data.
