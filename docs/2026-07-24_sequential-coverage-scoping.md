# Sequential-coverage scoping: the widening ladder after the reshape (2026-07-24)

Design of record for the next arc series: closing the sequential Go
semantics. Written immediately after the reshape merged (`main` @
9e43afc): the fine-grained machine landed precisely so that features are
built ONCE — this note decides what gets built, in what order, and (the
governing principle) how we defer everything else without foreclosing it.

## 0. The governing principle: DEFER, NEVER FORECLOSE

(User direction, 2026-07-24.) We will not cover all of Go soon, and some
features (floats, generics, goto) may stay out for a long time. That is
fine. What is NOT fine is a representation or design decision that makes
a deferred feature *expensive to add later* — the reshape itself was the
cost of exactly one such decision (big-step evaluation foreclosing
concurrency), and BUG-002's ledger shows what catching it late costs.

Operationally, every deferral must carry three things:

1. **Fail-closed behavior today** — the frontend or machine rejects the
   construct loudly (`unsupported`), never approximates. (Standing
   doctrine; unchanged.)
2. **A red corpus guardrail** — the differential corpus already contains
   the feature's cases, visibly failing. (True today: the 530 red cases
   ARE the deferral ledger.)
3. **A recorded re-entry sketch** — §3 below: for each deferred feature,
   the design-shaped-hole it will fill, and an explicit check that no
   CURRENT structure blocks that hole. Any new arc that would entrench a
   blocking assumption must amend this note first.

"Foreclosing" concretely means: a representation without an additive
extension point (a closed value universe consumed by shared machinery), a
semantic shortcut that a later feature would have to *undo* rather than
*extend* (big-step evaluation was one; panic-as-teleport is the live one,
§3.3), or proof-layer machinery quantifying over a structure that must
later change shape.

## 1. Where coverage stands (census from the 718-case differential,
`main` @ 9e43afc: 188 PASS / 530 FAIL)

Failure buckets: **442 frontend-export** (the native frontend cannot emit
the construct), **80 lean-observation** (exported but our runtime side
falls short), **8 differential** (true fidelity disagreements with Go —
BUG-001 territory).

All-failing feature tags (zero passing cases), by size: generics 76;
channels/select/close 81 (concurrency — R4/R5, out of scope here); defer
40 + recover 27; type_sets/constraints/inference 57; switch/type_switch/
fallthrough/cases 64; append/copy/delete/new/clear builtin forms 71;
labels-as-targets 17 + goto 11; untyped constants 15; closures/
higher-order 9; globals/init 12; aliases 5. Cross-cutting and untagged:
**multi-result functions (`*types.Tuple` unsupported at the frontend)** —
which blocks the `(T, error)` idiom and therefore most real Go including
the raft north star — and **floats/complex have no `GoValue`
representation at all**.

## 2. The ladder (ordering = raft-need × bucket size × foreclosure risk)

- **W1 — multi-result functions & tuples.** The most load-bearing gap
  (`calls` is the top failing tag at 100). Machine check: ALREADY
  multi-result-shaped — `Func.results` is an array, frame exits
  read/store location LISTS, call targets are plural, `assignMany`
  exists. The work is almost entirely frontend (`types.Tuple` decode,
  multi-target call lowering) plus runner result plumbing. No machine
  foreclosure found.
- **W2 — switch / type-switch / fallthrough.** Frontend desugaring to
  if-chains (Go spec semantics: evaluate tag once, first match). Machine
  needs nothing new; type-switch reuses `typeAssert` machinery. Recorded
  cost, not a foreclosure: specs about a switch will read as its
  desugaring (acceptable at this tier; revisit only if spec-readability
  demands a native form).
- **W3 — defer / recover.** NOT mere coverage — machine design, and this
  ladder's one mandatory early item (§3.3): the current `panicked`
  configuration discards the continuation (panic-as-teleport), and
  `recover` requires panics to UNWIND frame-by-frame running defers.
  Every arc built on panic-as-teleport before W3 deepens the hole —
  BUG-002's lesson applied. W3 lands the unwinding representation even
  if `defer`'s surface coverage comes with it.
- **W4 — BUG-001 (struct/array writes) + the 88 non-frontend failures.**
  The already-planned widening, now unblocked; triage the 8 differential
  + 80 lean-observation cases with it.
- **W5 — closures & function values.** Lambda-lifting at the frontend
  (preserves the FuncId-as-semantic-identity doctrine); `GoValue` gains a
  function-value constructor carrying `FuncId` + captured environment —
  env-in-config makes capture natural. Method values ride along.
- **W6 — builtin forms, untyped constants, globals/init, labeled
  break/continue.** Mopping-up tier; each is additive (see §3).
- **Deferred indefinitely with re-entry sketches (§3): floats/complex,
  generics, goto.**

Each W-arc follows the standing pattern: guardrail cases first (already
red), frontend decode fail-closed, machine arms (`StrictOp`/`StmtOp` or
new rules — the shared-table architecture keeps this additive), zero-drift
differential gate, proof-layer laws only when a witness needs them.

## 3. Foreclosure audit: deferred features vs. current structures

### 3.1 Floats / complex (deferred; re-entry cost: LOW, additive)
`GoValue` is an open inductive — adding `| float (bits : UInt64)` (and
complex as a pair) is additive; `valueEq`/`normalizeValueForTy`/the
observation schema are per-tag and extensible; nothing shared assumes
"numbers are `Int`" outside int-specific arms. **The one decision to make
at re-entry, recorded now so nobody pre-decides it casually:** represent
float64 by IEEE-754 *bit pattern* (`UInt64`) with explicitly-defined
operations, NOT Lean's opaque `Float`, if the proof layer is ever to
reason about them; an executable-only shortcut through Lean `Float` would
itself be a foreclosure (kernel-opaque). Until then: frontend rejects
float types fail-closed. NO current structure blocks this.

### 3.2 Generics (deferred; re-entry cost: LOW for execution, recorded
limit for specs)
Strategy at re-entry: **monomorphization in the frontend** — zero machine
impact, zero foreclosure of execution semantics. Recorded limit: it
forecloses *generic specifications* (theorems per instantiation, not per
generic function); if generic library specs are ever wanted, that is a
separate, bigger decision (polymorphic values or a spec-level quantifier)
— nothing we build now makes it worse, and monomorphization does not have
to be undone for it.

### 3.3 defer / recover — THE live foreclosure risk (hence W3, early)
Current machine: `Config.panicked msg` is TERMINAL and drops the whole
continuation; the proof layer's #24 reads panicked-as-stuck; the queued
driver-level panic theorem already notes panics also travel as `.error`
through helper legs. `recover` breaks panic-as-teleport: a panic must
become an UNWINDING configuration — sketch: `Config.panicking (msg) (k)`
unwinds like `.returning`, frames carry a defer stack (a `List` of
suspended calls in `Cont.frame` or a sibling frame field), `frameFall`/
`frameReturn`/`panicking-at-frame` all run defers first, `recover` (legal
only directly inside a deferred call) converts `panicking` back to normal
control with the panic value. Terminal `panicked` remains only at `.stop`.
Foreclosure discipline UNTIL W3 lands: no new law, exit theorem, or
statement may *depend on* panic-as-teleport beyond what exists today
(#24's recorded scope); anything tempted to must land after W3. The
runner's fault-identity comparison (`docs/2026-07-22_fault-model.md`)
already treats recoverable panics as a class — unchanged.

### 3.4 goto (deferred indefinitely; re-entry path exists, frontend-side)
The one construct genuinely awkward for a structured-continuation
machine. Go's goto is already restricted (no jumps into blocks / over
declarations), and the re-entry path is **frontend desugaring**
(loops+flags or block restructuring) — frontend-side, hence
non-foreclosing by construction. Machine stays untouched; frontend
rejects today. Labeled break/continue (W6) is NOT goto: label-carrying
loop frames are an additive `Cont` extension.

### 3.5 Closures (W5; checked: no current block)
The FuncId-identity doctrine survives via lambda lifting; `GoValue` is
open for the function-value constructor; env-in-config gives capture.
The one thing NOT to do before W5: build any machinery assuming "every
callee is named in the static `Func` table at the CALL SITE" — the
frame-entry step already localizes function lookup in `enterFrame`, so
extension = a second entry form taking a function value; keep it that
way.

### 3.6 Channels / goroutines (R4/R5 — the machine was reshaped FOR this)
Out of this note's scope; the F4 note governs. The sequential ladder must
not entrench anything the granularity ledger flags — W-arcs adding
multi-cell apply steps must extend the ledger, per the standing rule.

### 3.7 Globals / init / untyped constants / builtins (W6; additive)
Globals: an outer scope in the entry environment + seeded heap cells —
`LocalEnv` is already a scope stack; no new state field. `init` functions:
driver-side sequencing. Untyped constants: frontend constant evaluation
(Go's spec makes them compile-time). Builtin forms (`append` variadic
spread, `delete`, `clear`, `new` forms): mostly frontend lowering onto
existing `StmtOp`s plus small new arms.

## 4. What this note deliberately does not decide

Arc-level sequencing beyond the ladder order (each W-arc gets its own
step-0 scoping); the generic-spec question (§3.2); native-switch spec
forms (§W2); float re-entry timing. Each deferred item's re-entry
DESIGN is sketched above precisely so that deciding to add it later is
an ordinary arc, not a reshape.
