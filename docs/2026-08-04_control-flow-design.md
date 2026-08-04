# Sequential control-flow completion — design note (general-coverage slice 1)

Scope: the ~23 red `control-flow/` cases (switch evaluation semantics,
labeled break/continue, goto, labeled statements, for-loop corners).
`break-label-select` / `goto-out-of-select` stay red — channel-blocked,
their labels/goto parts ride on the machinery below once `select` exists.

Ground truth surveyed before deciding: the CEK machine
(`GoLean/GoCore/{Machine,StepFn}.lean`), its existing break/continue
machinery (`Config.breaking`/`.continuing` unwinding through
`Cont.seq`/`Cont.loop`/`Cont.breakableK`/`Cont.mapIterK`), the frontend
lowerings (`tools/nativefrontend/emit.go`, `GoLean/NativeToIR.lean`), the
Go spec's rules for `goto`/labels, and Goose (`deps/goose/goose.go`).

**Goose comparison.** Goose supports only BARE break/continue
(`branchStmt`, goose.go:1643 — a labeled branch hits `noExample`), has no
`*ast.LabeledStmt` case in its `stmt` switch, and no goto at all.
Everything in this slice — labeled break/continue, goto in all its legal
scoping forms, switch fallthrough into declaring clauses, lazy
case-expression calls — exceeds Goose's coverage. Perennial's
`exception.v` monad gives it break/continue/return as effects; there is
no prior-art lowering to copy for goto. We therefore design against the
Go spec directly, with `go/types`' static label checks (labels.go:
undefined label, goto-into-block, goto-over-declaration — all in the
compile-negative corpus already) as the fail-closed front gate: a program
that violates them never exports.

## Stage 1 — switch semantics (frontend-only)

The red switch cases all trace to two frontend fail-closed guards, not to
missing machine features:

1. **Calls in case expressions / loop conditions** (`emitGuarded`
   forbids hoists in "lazy positions"). Fix by restructuring so the lazy
   position becomes a statement position where hoists are legal:
   - **Switch**: replace the nested-if desugar with a *selection index*
     desugar (below) whose case tests are a statement chain — each case
     expression's hoists splice immediately before its own test, giving
     Go's exact textual, lazy, stop-at-first-match evaluation order and
     panic timing.
   - **For conditions**: the `for` desugar already re-tests the
     condition INSIDE the loop body (`decodeFor`'s
     `if cond {} else break`), so condition hoists are legal there. The
     wire `for` node gains `condPre` (statements run before each test);
     `emitFor` captures the condition's hoists into it instead of
     failing closed.

2. **Fallthrough out of a declaring clause** (the old desugar inlined the
   next clause's body inside the current clause's scope — unsound under
   declarations, so it failed closed). The selection-index desugar makes
   clause bodies SIBLING blocks, which is Go's actual scoping, so the
   restriction disappears.

The selection-index desugar of `switch init; tag { ... }`:

```
breakable block {
  init                        // as before
  $swN := tag                 // once, as before (absent if expressionless)
  $swiN := <defaultClauseIdx | #clauses>   // selected clause; sentinel = none
  // test chain, nested else-blocks, textual order over case VALUES,
  // default's (empty) tests skipped:
  { hoists(c0); if $swN == c0 { $swiN = clause(c0) } else {
    { hoists(c1); if $swN == c1 { ... } else { ... } } } }
  // dispatch, source order over CLAUSES (default in position):
  $swfN := false              // fallthrough flag
  if $swfN || $swiN == 0 { $swfN = false; { body0 }  [$swfN = true] }
  if $swfN || $swiN == 1 { ... }
  ...
}
```

- `[$swfN = true]` is emitted exactly when the clause ends in
  `fallthrough` (already stripped as the statically-last statement); a
  body exiting via `break`/`return`/panic never reaches it, a body
  completing normally does — Go's rule.
- Bodies `{ body_i }` are sibling blocks: fallthrough into or out of a
  declaring clause resolves names exactly as Go does.
- Expressionless switch: the test is the case expression itself.
- The guard reads (`$swfN || $swiN == i`) are effect-free, so the extra
  control statements are observationally silent.

No machine change; `Stmt.breakable` keeps catching bare `break`.

Also stage 1 (for-loop corners in the red set):

- **`for-loopvar-escape` — Go ≥1.22 per-iteration variables.** The
  current guard rejects a func literal capturing a for-clause variable.
  Desugar with a carrier-pointer so `continue` needs no copy-back path:

  ```
  { $lv0 := <init value>; $lvp := &$lv0; $first := true
    while true { block {
      i := *$lvp; $lvp = &i          // fresh cell per iteration
      if $first { $first = false } else { post }   // post on the fresh i
      condPre...; if cond {} else { break }
      body } } }
  ```

  Everything per-iteration happens at the TOP of the iteration, so
  `continue` (which re-enters the while) carries the current cell's
  final value into the next iteration via `$lvp` — the spec's
  "initialized to the value of the previous iteration's variable".
  Captures see one distinct cell per iteration. Applied only when a
  literal captures a for-clause variable (the previously-rejected path);
  the ordinary desugar stays untouched otherwise.

## Stage 2 — labeled break/continue: label-carrying continuations

Machine-level, because break/continue are already machine-level signals
and a flag desugar would have to re-encode the unwinding the CEK already
does (and would foreclose `select`'s labeled break later).

- `Stmt.labeled (label) (body)`, `Stmt.breakTo (label)`,
  `Stmt.continueTo (label)` (new constructors; the inert `Stmt.label`
  no-op stays as is).
- `Cont.labelK (label) (k)` — pushed by executing `.labeled`.
- `Config.breakingTo (label) k` / `Config.continuingTo (label) k` — the
  labeled signals. Bare `.breaking`/`.continuing`/`.returning` pass
  THROUGH `labelK` (a bare break targets the innermost for/switch
  regardless of labels).
- **Placement invariant (the frontend's half):** `NativeToIR` attaches
  `.labeled` DIRECTLY around the loop-forming statement — the desugared
  `.while` for `for`/range-index loops, the `.mapRange` for map ranges,
  the `.breakable` for switch — so a labeled loop's `Cont.loop` /
  `Cont.mapIterK` has `labelK` as its IMMEDIATE continuation.
- Unwinding rules:
  - `breakingTo L` strips `seq`/`loop`/`breakableK`/`mapIterK`
    unconditionally; at `labelK n`: `n = L` → `next k` (the labeled
    statement is terminated), else strip. Never crosses `frame`
    (`go/types` guarantees enclosure; the machine fails stuck — closed).
  - `continuingTo L` strips `seq`/`breakableK` and non-matching
    `labelK`; at `loop c b env k` with `contHeadLabel k = some L` (the
    placement invariant makes this THE labeled-loop test) → re-execute
    `.while c b` under `k` (post/cond re-run by the loop desugar — Go's
    continue-runs-post, pinned by `continue-label-post`); at `mapIterK`
    with matching head label → `next (mapIterK …)` (advance the range).
    Mismatches strip. A matching `labelK` reached OTHER than through a
    loop head has no rule — statically impossible, fails closed.
- Metatheory in lockstep (the sem-adequacy disciplines): `Cont.locSup`/
  `Cont.itersNormalized`/`Config.locSup`/`Config.itersNormalized`/
  `Stmt.locSup` cases; `panicPassthrough`/`pushDefer`/`recoverResult`
  walk `labelK`; `step_preserves_wf`, `stepFn_sound`, `step_complete`,
  `step_complete_any_wf`, `stepFn_oblivious`, `step_det` extended. All
  new arms are deterministic and consume no choices, so the
  obliviousness sweep stays intact (no new envelope statement owed under
  the nondeterminism doctrine — no new choice-consumption site).

## Stage 3 — goto: frontend restructuring over the stage-2 machinery

The two honest options from the arc brief:

(b) **machine-level jump** — a step re-entering the function body at the
label. Rejected after working the details: the body is not reachable
from any continuation (`Cont.frame` does not carry it; `Cont.seq` holds
only the REST of its block, so a backward target is simply absent from
the configuration). Making it reachable means widening `frame` or `seq`
— an arity change through every rule, wf case, and correspondence proof
— and the re-entry step must ALSO solve the stale-environment problem
below, so the machine surgery buys no fidelity the frontend option
lacks.

(a) **frontend restructuring**, chosen, riding on stage 2's machine
labels (so it is NOT Goose-style avoidance-by-rewrite-into-flags inside
arbitrary control flow — the only flag is a program counter over
top-level segments, and the jump itself is a real machine signal):

A function body containing `goto` lowers to a dispatch loop:

```
block {
  var <every top-level-declared variable>   // hoisted, default values
  $pc := 0
  $gotoN: while true { block {
    if $pc <= 0 { seg0 }      // statements before the first label
    if $pc <= 1 { seg1 }      // statements from label L1 (exclusive)…
    ...
    break } }
}
```

- Top-level labels split the body into segments; `goto L` (at any
  depth, not crossing func literals) becomes
  `$pc = seg(L); continueTo $gotoN` — the stage-2 signal unwinds out of
  any enclosing blocks/loops/switches to the dispatch loop, which is
  exactly Go's out-of-block/for/switch jump. Backward and forward jumps
  are the same operation. Segments run in order within a sweep
  (`$pc <= i` guards; `$pc` only changes via goto, which immediately
  re-enters), giving normal sequential fall-through between segments.
- Top-level `:=`/`var` declarations are hoisted to pre-declared cells
  and rewritten to assignments (a `var x T` without initializer becomes
  `x = <zero>`), because segments must share one scope ACROSS sweeps.
  Deeper blocks are untouched — they re-execute wholesale, declarations
  included, which is Go's re-declaration semantics.

**Fidelity envelope — checked, fail-closed, in the frontend (it has
`go/types`; GoCore purity untouched).** The hoisting is observationally
equivalent EXCEPT where a fresh-cell-per-execution of a top-level
declaration is distinguishable, or where name resolution at runtime
(GoCore envs resolve by name, innermost-first) could diverge from Go's
static resolution. Reject (precise `unsup` reason) when:

1. a goto target label is not at the function body's top level (legal in
   Go — label in any enclosing block — but outside this envelope);
2. a hoisted (top-level-declared) variable is captured by a func literal
   or has its address (or the address of a SUB-OBJECT of its storage)
   observed anywhere in the body; capture/escape makes cell identity
   observable across a backward jump. The check (audit-response
   2026-08-04 — the original only caught `&x` / `x.M()` on a BARE
   identifier, so `&(x)`, `&s.f`, `&a[0]`, `a[:]`, and `s.f.M()` all
   escaped silently) traces each address-taking position to its storage
   root through parens, field selections on non-pointer bases, and
   array indexing, stopping at pointer indirections (deref, selector
   through a pointer, slice/map indexing — those reach heap storage,
   whose identity hoisting does not change). Positions checked:
   explicit `&expr`; slice expressions on array operands (`a[:]` takes
   `&a` implicitly); pointer-receiver method calls AND method values
   whose receiver chain roots at a hoisted cell (skipped when the
   operand is itself pointer-typed — the pointer value is the
   receiver). Recorded conservative narrowing: a pointer-receiver
   method promoted through an embedded POINTER field of a hoisted
   non-pointer root is refused although the address taken is behind
   that pointer;
3. a hoisted variable's name is ALSO used in the body resolving to an
   OUTER object (param/result/package-level) — hoisting would shadow the
   outer use (`x := x + 1` with `x` a parameter, uses before the
   declaration point, etc.).

Everything in the red corpus is inside the envelope; case
`goto-backward-capture` (added, expected red) pins rejection 2 visibly.
The compile-negative corpus already pins Go's own static rejections
(`goto-into-block`, `goto-over-declaration`, …) — those never reach the
lowering because the frontend type-checks first.

**Local type declarations** (needed by `goto-over-type-decl`, and a
standalone gap): `type T …` in a function registers through the same
`emitGenDeclTypes` path as package-level types (type declarations have
no runtime effect; jumping over one is legal Go). Fail-closed rider: the
export refuses duplicate TypeId keys (two same-named local types, or a
local type shadowing a package-level one, would alias in the global
type table).

## What stays red, and why

- `break-label-select`, `goto-out-of-select`: `select` is
  channel-blocked (its own arc). The label machinery here is what their
  eventual lowering will target.
- goto outside the envelope above: visible `unsup` with the reason
  strings `goto target label ... not at function body top level`,
  `goto function hoists a captured variable ...` /
  `... an address-taken variable ...` /
  `... whose array storage is sliced` /
  `... used as a pointer-method receiver` /
  `... shadowing an outer name in use` — never a silent approximation.
  Envelope pins (expected red, FAIL/frontend-export):
  `goto-backward-capture`, and audit-response 2026-08-04
  `goto-backward-field-addr` (`&s.v`), `goto-backward-elem-addr`
  (`&(a[0])`), `goto-backward-array-slice` (`a[:]`),
  `goto-backward-nested-recv` (pointer-receiver method on a field of a
  hoisted struct).
