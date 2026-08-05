# Package initialization — design note (general-coverage slice 5)

Scope: package-level variable initialization (dependency order per the Go
spec), `init()` functions, and package-level variable access from
subjects. Targets, grounded in `baselines/native-full.tsv` (recorded
2026-08-05, 733/925): the six `init/*` reds plus
`control-flow/expressionless-switch-order` — the definitive list of reds
whose recorded reason is the package-level-variable refusal or the
`init` duplicate-FuncId refusal, verified by grepping the corpus for
package-level `var` declarations (exactly seven `main.go`s have one) and
by the recorded `latest.tsv` details:

- `init/blank-var-init` — frontend-export (package-level refusal)
- `init/global-zero-before-init` — frontend-export
- `init/init-sees-var-values` — frontend-export
- `init/multiple-init-order` — lean-observation (`duplicate function id
  init in program`: two `init()`s exported as same-named funcs)
- `init/package-init-order` — frontend-export
- `init/var-init-sequence` — frontend-export
- `control-flow/expressionless-switch-order` — frontend-export (switch
  semantics landed in slice 1; blocked only on its package-level trace
  variable)

Ground truth surveyed before deciding: the machine
(`GoLean/GoCore/{Machine,StepFn,State,StateWf}.lean` — env model, frame
entry, drivers), the frozen proof surface (`proofs/GoLeanProofs/Laws/
Call.lean`, `HeapBridge.lean`, `Surface.lean` — what a machine-shape
change would break), the frontend (`tools/nativefrontend/{main,emit}.go`
— both fail-closed refusal sites), the Go spec's Package initialization
section (`/usr/local/go/doc/go_spec.html`), a `go/types` probe
(`.tmp/init-probe/probe.go`, go1.26.5), and Goose/Perennial (§6).

## 1. The spec's order model, and where the latitude is

The spec (Package initialization), verbatim:

> Within a package, package-level variable initialization proceeds
> stepwise, with each step selecting the variable earliest in
> declaration order which has no dependencies on uninitialized
> variables.

> More precisely, a package-level variable is considered ready for
> initialization if it is not yet initialized and either has no
> initialization expression or its initialization expression has no
> dependencies on uninitialized variables. Initialization proceeds by
> repeatedly initializing the next package-level variable that is
> earliest in declaration order and ready for initialization, until
> there are no variables ready for initialization.

Multi-assign: "Multiple variables on the left-hand side of a variable
declaration initialized by single (multi-valued) expression on the
right-hand side are initialized together." Blanks: "For the purpose of
package initialization, blank variables are treated like any other
variables in declarations." Cycles: variables still uninitialized when
the process ends "are part of one or more initialization cycles, and the
program is not valid" (go/types rejects — compile-negative lane).
`init()` functions: "Multiple such functions may be defined per package
… the `init` identifier can be used only to declare `init` functions,
yet the identifier itself is not declared. Thus `init` functions cannot
be referred to from anywhere in a program." Order: "assigning initial
values to all its package-level variables followed by calling all
`init` functions in the order they appear in the source, possibly in
multiple files, as presented to the compiler." Everything runs "in a
single goroutine, sequentially".

**Dependency analysis is spec-pinned, not latitude — and we take it from
`go/types`.** `types.Info.InitOrder` is the type-checker's
implementation of exactly the stepwise rule above (probe-verified,
go1.26.5: dependency order with declaration-order tie-breaking; blank
vars included as ordinary entries; one `Initializer` with multiple `Lhs`
for `var a, b = f()`; **zero-valued vars — no initializer — are absent
from `InitOrder`**, so they need declaration/allocation but no init
step). Using it keeps the frontend's trust surface at go/types' already
trusted analysis (exactly like `Instances` for generics) instead of
re-deriving the spec's transitive lexical-reference analysis — a
re-derivation would be a second, unaudited implementation of a
spec-mandated algorithm. Goose delegates identically (§6).

**The latitude points, per the nondeterminism doctrine (envelope
statements):**

1. **Hidden dependencies.** The spec: "If other, hidden, data
   dependencies exist between variables, the initialization order
   between those variables is unspecified" (its example: `var x =
   I(T{}).ab()` reaching variables through an interface method the
   lexical analysis cannot see). A conforming compiler may order such
   variables differently. **We pin go/types' `InitOrder`** — a single
   conforming resolution, i.e. a deterministic PRAGMATIC SUBSET of the
   spec's latitude, the append-spill precedent. **Implementation
   finding (probe-verified, go1.26.5): gc's own initorder is a SEPARATE,
   COARSER analysis and already diverges from go/types on exactly this
   shape** — for `init/hidden-dep-order`, go/types orders
   `[hiddenX, hiddenB, hiddenA]` (an interface-typed receiver's method
   is NOT a spec "reference", so `hiddenX` has no dependencies and is
   earliest-declared-ready), while `go run` initializes `hiddenX` after
   `a`/`b` (observations 4242 vs 4624242 — gc conservatively pulls
   method-body dependencies through the conversion). Both orders
   conform; the spec text says so explicitly. Consequences, decided:
   the case stays in the corpus as an EXPECTED RED
   (`FAIL/differential`) — the visible, version-tracked record that on
   hidden-dependency programs our realized order is a different
   conforming member of the spec's set than gc's. Matching gc would
   mean re-implementing cmd/compile's unspecified internal analysis
   (over-specialization to an implementation, not to Go); widening the
   model to admit all conforming orders needs a named `Choices` site
   and an envelope discussion — deliberately deferred, recorded here.
   For programs WITHOUT hidden dependencies (everything else in the
   family) the two analyses agree, since both implement the spec's
   lexical-reference rule.
2. **Multi-file declaration order.** The spec defers to "the order in
   which the files are presented to the compiler" and encourages build
   systems to present files "in lexical file name order". The frontend
   presents files sorted by filename (`tools/nativefrontend/main.go`,
   `sort.Strings`), which is the go command's documented behavior — so
   model and oracle agree exactly. Today the exported package is
   SINGLE-FILE anyway (the differential exports the case dir, whose only
   `.go` file is `main.go`; the harness file exists only on the go-run
   side), so the pin is currently unexercised; when a multi-file case
   arrives it is already the recorded behavior: declaration order and
   `init()` order across files = lexical filename order. A conforming
   NON-go-command build system could present files differently — outside
   our envelope, recorded here, revisit only if a target ever ships one.
3. **`init()` order within the model** is spec-fixed (source order,
   files in presentation order) — no latitude once (2) is pinned.

Possibilistic scope unchanged: no distributional claims anywhere. No new
choice-consumption sites; the stream-obliviousness kit is untouched.

## 2. The machine shape: globals as driver-seeded base cells, statically resolved

**Decision: package-level variables are ordinary `.base` heap cells,
allocated by the driver as the FIRST `n` allocations (ids `0..n-1`, wire
declaration order) before anything runs; the frontend — which has
go/types and therefore knows statically which identifiers are
package-level — resolves every global reference to its cell at emission
(`globaladdr` wire nodes carrying the dense global index `gid`, decoded
to `Expr.locLit (.base gid)`); initialization itself is a synthesized
ordinary function `$pkginit` (reserved id — `$` cannot appear in a Go
identifier or package name, the `$runtime.Error` argument) that the
driver runs to completion before the subject, in the same state, with
the same choice stream threaded through.**

Reads lower to `deref(globaladdr)`, writes to an `addr(globaladdr)`
assignment target, `&g` to `globaladdr` itself — loads and stores at a
fixed location, exactly Perennial's model (§6). Closures need no capture
machinery for globals: a func literal mentioning a global emits the same
`globaladdr` (the existing capture-scan skip of package-scope vars
becomes correct rather than provisional). Mutation is shared across all
frames by construction — one cell.

Zero machine change: no new `Step` rule, no new `Cont`/`Config`/`Expr`/
`Loc`/`ExecState` shape, no `stepFn` arm, no StateWf/MachineSound
extension — `Expr.locLit` already evaluates to its address in both the
relation (`Step.evalLocLit`) and `stepFn`, and `Expr.locSup` already
counts locs in stored function bodies (the sem-adequacy slice-3 carrier
inventory recorded `.locLit` in program text and `ExecState.functions`
for precisely this shape of use). Relation/interpreter lockstep is
therefore trivially preserved. The one definitional amendment:
`Expr.locLit`'s docstring said "never emitted by the frontend" —
REVISED this slice: the frontend emits it for package-level variables
(statically resolved, driver-pinned allocation); it remains unused for
anything env-resolved.

### Alternatives considered and rejected (with the argument)

- **(b) Frontend inlines initialization into every subject.** WRONG for
  shared mutable state: globals would be subject-frame locals, so a
  subject calling another function that mutates a global could not see
  the mutation (the callee has no path to the caller's frame cells), and
  init-function effects could not persist. Pinned by
  `init/global-shared-mutation`.
- **Env-chain global frame** (frame environments rooted at a global
  scope, via `enterFrame`). Requires changing `enterFrame`'s output
  shape, and the frozen WP call laws
  (`proofs/GoLeanProofs/Laws/Call.lean`: `wp_call_enter_arg1`,
  `wp_call_enter_ret1`, …) prove exact `enterFrame … = .ok (func,
  [[(pid, …)]], …)` equalities quantified over every state the
  interpretation admits — false the moment frame envs root at a
  state-dependent scope, and unprovable even with a conditional root
  (the match on an abstract state's globals cannot reduce). It also
  re-does at runtime, per lookup, name resolution that go/types has
  already performed statically. Rejected; proofs/ stays bit-identical.
- **New `Loc.global name` constructor** (name-keyed heap cells,
  Goose-shaped). Breaks the heap-key invariant everywhere it is matched:
  `proofs/GoLeanProofs/HeapBridge.lean`'s `heapToMap` bridges do
  exhaustive `cases loc` (base/field/index) — a new constructor is a
  compile error in the frozen bridge, plus arms across
  `rootBase`/`locSup`/`loadLoc`/`storeLoc` for zero fidelity gain over
  index-resolved base cells.
- **`ExecState.globals` registry + new `Expr.globalAddr` rule.** A new
  state field, a new expression form, a new Step rule and stepFn arm,
  and StateWf/`ExecState.locSup` extension (the registry's locs must be
  bounded or preservation fails at the new rule) — `ExecState.locSup`'s
  definition is load-bearing inside `proofs/GoLeanProofs/Surface.lean`
  (`InitialSplit.heapBounded` decomposes it by `Nat.max_le`), so the
  extension is again a proofs/ break. All of it buys a dynamic lookup
  the frontend can do statically. Rejected.

### Fail-closed story for the static resolution

The gid assignment lives in ONE place (the emitter's package-var
collection loop; dense indices by construction, duplicate package-scope
names impossible in a type-checked package). The driver seeds from a
fresh state (`nextAddr = 0`, checked) and verifies each allocated cell
is exactly `.base gid` (internal error otherwise — the executable
analogue of Perennial's `GlobalAlloc` angelic check that the fresh loc
equals `global_addr v`). A `globaladdr` that somehow escapes seeding
(wire edited by hand, driver bug) dereferences a missing cell → machine
stuck (closed, never a silent value). A wire program with globals run
through a NON-seeding entry point (`runNamedFunctionM`) likewise goes
stuck at first access, never wrong.

### Driver composition (statement TCB untouched)

`runProgramM` (StepFn.lean, beside the existing drivers): seed globals
(zero values at declared types, wire order) → if `$pkginit` exists, run
it as a nullary/void function (`.exec body [] (.frame [] [] [] .stop)`,
arity fail-closed) with the given fuel and choice stream → thread the
resulting state and LEFTOVER stream into the ordinary subject entry
wiring (bindParams/allocDecls/pinResultLocs/runConfig). A panic in
`$pkginit` is the run's observation (Go: a panic during initialization
aborts the program), same classification surface as a subject panic.
`Surface`/`InitialSplit` and every designated statement are untouched —
initialization is driver-level composition, exactly like
`runFunctionWithContextM` already is. The membership-lane driver
(`CLI.enumSetup`/`enumRun`) mirrors the same composition per enumerated
stream (init consumes choices from the same stream as the subject — a
global map literal's iteration behavior is part of the run), and the
driver-agreement eval tests pin the two compositions against each other
as they pin the existing pair.

### `init()` functions

Each `init` FuncDecl exports as an ordinary Func under a reserved
mangled id `$init0`, `$init1`, … in source order (files in presentation
order); `$pkginit` calls them, in order, after the variable
initializers. go/types enforces the spec's declaration rules (cannot be
called or referenced; no params/results; blank-identifier rules) — the
compile-negative lane already pins `call-init`, `init-with-params`,
`init-return-value`, `duplicate-global`. Separate functions (not
inlining into `$pkginit`) because `return` inside an `init` body must
exit that init function only, `defer` must run at ITS exit, and
`recover` scopes to its frame — all free with a real frame, all wrong
under inlining. Lifted literals inside an init body qualify as
`$initN$litM` — collision-free (Go identifiers cannot contain `$`).

### Quarantine boundary (no per-decl quarantine for init code)

An unsupported construct in a package-level initializer expression, in
an `init()` body, or in a global's TYPE fails the WHOLE export
(fail-closed `unsup`, frontend-export stage) — not the per-decl
quarantine stub path. Rationale: initialization runs before every
subject; a stubbed initializer would let every subject in the package
run against silently-uninitialized state. This can only turn cases red
that were red already (today the same package refuses at the
package-level-variable read), and honest reds are the contract.

## 3. Ordering inside `$pkginit` — what is emitted

Body, in order:

1. Per `Info.InitOrder` entry: an assignment of the initializer
   expression to the target global(s), through the ordinary
   `emitAssign` machinery on a synthesized `ast.AssignStmt` whose Lhs
   are the ORIGINAL ValueSpec name idents (so hoisting of calls,
   interface boxing, multi-value call statements, and blank targets are
   the already-validated paths — `_` lowers to the existing blank
   target and evaluates its RHS for effects, `var a, b = f()` is one
   multi-target call statement, per the spec's "initialized together").
   The assign-target emitter learns to classify DEF idents of
   package-level vars like USE idents (the synthesized Lhs are Defs).
2. Per `init()` function, in order: a bare call statement to `$initN`.

Zero-valued globals get their cell (zero value at declared type) from
the driver's seeding — no `$pkginit` step, matching `InitOrder`'s
omission. `$pkginit` is emitted only when it has a body (some
initializer or some `init()`); packages with only zero-valued globals
seed cells and run nothing.

## 4. Goose/Perennial comparison

Surveyed at `deps/goose` (`goose.go`) and `deps/perennial`
(`new/golang/defn/pkg.v`, `postlang.v`, `src/goose_lang/lang.v`,
`new/golang/theory/pkg.v`).

- **Same decomposition.** Goose emits a generated `initialize'` per
  package: `GlobalAlloc` per global (zero value), then imported
  packages' `initialize'`, then the package-level initializers iterated
  from `ctx.info.InitOrder` (goose.go:2616 — the same go/types
  delegation, including the only-vars-with-initializers subtlety), then
  the `init()` bodies in source order (files alphabetical). Our
  `$pkginit` is the same object minus imports (below).
- **Same access model.** A Goose global read is a typed load from a
  fixed per-name address: `![ty] (GlobalVarAddr "pkg.x" #())`, where
  `GlobalVarAddr` reduces purely to `#(global_addr "pkg.x")` — an
  axiomatized `go_string → loc` function, with `GlobalAlloc`
  angelically pinning the allocation to that address
  (postlang.v:155-162). Our `globaladdr → locLit (.base gid)` is the
  executable concretization: the address function is "the first `n`
  allocations, in declaration order", and the angelic pin is the
  driver's allocation check. Deliberate divergence: name-keyed
  axiomatized addresses vs dense driver-pinned indices — we need an
  executable, differentially-testable allocator, and the index form
  avoids a new `Loc` constructor (frozen-bridge argument, §2).
- **Init functions:** Goose compiles each `init()` to an anonymous
  lambda spliced at the end of `initialize'` (no frame of record);
  ours are real named functions — see the `return`/`defer`/`recover`
  argument in §2. Divergence recorded.
- **Multi-package:** Goose's `initialize'` recursively initializes
  imports first, idempotently (`package.init`'s `PackageInitCheck`
  once-only guard, defn/pkg.v:16-22), with proof-side `IsPkgInit`
  typeclass machinery. Out of scope here: our exported package is the
  single main package (imports are the extern-policy lane); when
  imported-package state ever lands, the spec's "imported packages
  first, once" and Goose's once-only guard are the starting points.

## 5. Guardrails (the cases, before the implementation)

Existing (the six `init/*` reds + `expressionless-switch-order`), plus
added this slice, classified red (frontend-export) before the
implementation lands:

- `init/spec-dependency-example` — the spec's own `d, b, c, a` program:
  dependency through a FUNCTION BODY (`f` references `d`), ties broken
  by declaration order, values proving each step's timing.
- `init/hidden-dep-order` — the spec's hidden-dependency shape
  (interface method reaching globals the lexical analysis cannot see):
  the §1 envelope pin. EXPECTED RED (`FAIL/differential`): go/types'
  order and gc's ALREADY split on this shape (§1 finding); the red is
  the recorded deviation, re-checked on every run and every toolchain
  bump.
- `init/multi-value-var-init` — `var a, b = two()` initialized together
  in one step, ordered against a dependent third variable.
- `init/global-shared-mutation` — the subject calls helpers that
  mutate a global and reads it between calls: the §2 rejection pin for
  inlining designs.
- `init/global-composite` — package-level map and slice globals
  (composite literals allocate during init; cells and backing stores
  persist into the subject).
- `init/global-addr-taken` — `&global` flows through a pointer
  parameter; a write through the pointer is visible in a direct global
  read (cell identity).
- `init/global-in-closure` — a func literal stored in a global reads
  and writes another global when invoked by the subject (globals need
  no capture).
- `init/init-defer-recover` — an `init()` whose deferred recover
  cancels a panic and records into a global (init functions are real
  frames).
- `Corpus/coverage/negative/compile/init/initialization-cycle` —
  `var a = b; var b = a`: go/types rejects (the spec's "program is not
  valid"); pins that cycles never reach the lowering.

Package-level `const` needs no new machinery or case: constants fold at
every use (`emitConstValue`), and the `constants/*` family already
passes green through package-level declarations.

## 6. What stays red / out of scope

- `init/hidden-dep-order`: FAIL/differential by design — the §1
  hidden-dependency deviation record (our conforming order ≠ gc's
  conforming order; the spec leaves it unspecified).
- Imported-package globals and stdlib package state: the extern-policy
  lane; nothing here changes it.
- Any initializer/init body using unmodeled features: whole-export
  refusal (§2 quarantine boundary), visibly red.
- Concurrency interactions (`init` launching goroutines): the
  concurrency arc; the spec's single-goroutine sequencing for init
  itself is what the driver composition already implements.
