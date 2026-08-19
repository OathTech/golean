# The bug-fix + language-bar arc — log

The running record for the arc chartered in
`docs/2026-08-19_bugfix-arc-charter.md`. One section per slice, in
execution order. Conventions (from the charter and the long-cycle
practice): every judgment call gets a one-line **JUDGMENT** entry with
its reasoning, for user review; every number is derivation-anchored
(the command that produced it); bounds ship as bounds.

## INDEX

| slice | subject | state |
| --- | --- | --- |
| 1 | BUG-058 — if-init condition-hoist scope | in progress |
| 2 | BUG-057 — two-var comma-ok var-decl arity | not started |
| 3 | BUG-056 — `&*p` nil collapse (design-gated) | not started |
| 4 | BUG-005 — live map iteration (design-gated) | not started |
| 5 | full red/bug triage (kill or justify) | not started |
| 6 | the whole-language bar (coverage ledger) | not started |

---

## Slice 1 — BUG-058: the if-init condition-hoist scope

Entry: `docs/BUGS.md` "BUG-058 — if-statement init scope: condition
hoist block emitted OUTSIDE the init". Diagnosis audit-hardened at the
P3 pre-merge audit; this slice verified its cites before touching
anything (see "diagnosis re-verification" below).

### Diagnosis re-verification (before any change)

- `emitIf` is at `tools/nativefrontend/emit.go:2517`; the entry's
  "2426 area" cite is the pre-P3 line number, off by ~91 lines after
  the intervening landings. The MECHANISM the entry describes is
  exact: `emitIf` emits `st.Init` into the node's `init` key
  (emit.go:2519-2525) and then calls `e.emitExpr(st.Cond)` with the
  ENCLOSING hoist accumulator still in force (emit.go:2526), so
  `emitStmtList` (emit.go:1616-1634) splices the condition's hoisted
  temps in front of the whole `if` node — outside the init's scope.
- The contrast the entry names is also exact and in the same
  function: the ELSE accumulator *is* scoped (emit.go:2542-2553,
  save/nil/restore + wrap), and so are `emitFor`'s condition
  (`condPre`, emit.go:2651-2662) and post (emit.go:2668-2679).
- The decoder side: `decodeIf` (`GoLean/NativeToIR.lean:1143-1153`)
  lowers `init` as `.block #[] #[init, ifThenElse …]` — i.e. the
  init's scope is ALREADY a block wrapping the if. That is what makes
  the fix frontend-local (below).

### Step 1 — edge enumeration (own commit, colors recorded BEFORE the fix)

Every expectation is `go run`'s, computed before the differential ran
(`artifacts/probe/ifinit`, `artifacts/probe/relatives`; scratch, not
tracked). Colors from
`scripts/coverage run --prefix spec-examples-stmt/if-init-hoist-order`
and `… --prefix spec-examples-stmt/init-hoist-relatives`.

**New reds — `spec-examples-stmt/if-init-hoist-order/` (7 rows added
to the 2 P3 pins):**

| row | shape | go | machine (pre-fix) | stage |
| --- | --- | --- | --- | --- |
| `else-if-chain` | `else if` with its own init + cond call | 12348 | 21438 | differential |
| `func-literal` | if-with-init inside a func literal | 125 | 215 | differential |
| `nested` | if-with-init inside if-with-init | 12349 | 21439 | differential |
| `cond-hoist-reads-init` | cond call reads the init var, no `&&` | 1 | stuck `unbound GoCore variable address: x` | lean-observation |
| `cond-panic-after-init` | init succeeds observably, cond call panics | 321 | 21 | differential |
| `comma-ok-short-circuit` | `if v, ok := m[k]; ok && f(v)` (raft shape) | 1 | stuck `unbound … ok` | lean-observation |
| `comma-ok-method-short-circuit` | `if pr, ok := m[k]; ok && pr.active()` | 1 | stuck `unbound … ok` | lean-observation |

All three observable modes of the entry are now pinned: mode 1
(stuck) by the three `reads-init` shapes, mode 2 (silent wrong order)
by `else-if-chain`/`func-literal`/`nested`, mode 3 (panic ordering) by
`cond-panic-after-init` (and the pre-existing `init-panic-first` in
the other direction).

**New pinned GREENS — `spec-examples-stmt/init-hoist-relatives/`
(6 rows, all PASS pre-fix):** `for-init-cond`,
`for-init-cond-reads-init`, `switch-init-tag`,
`switch-init-tag-reads-init`, `type-switch-init`,
`type-switch-init-reads-init`. These are the structurally-corroborated
non-affected relatives; pinning them green BEFORE the fix is what
makes a later silent regression in `emitFor`/`emitSwitch`/
`emitTypeSwitch` impossible to miss. Note that the `-reads-init`
variants put the init-declared variable INSIDE the hoisting call —
the exact position that goes stuck for `if` — so the pins are
load-bearing, not decorative.

**JUDGMENT (slice 1, edge enumeration):** the new `if` rows were
appended to the EXISTING `if-init-hoist-order` package rather than
given their own directories — one canonical file per evaluation-order
concern keeps the family readable and the ids stable, and the package
is still small. The relatives went to a NEW package because they are
pinned greens about *other statements*; mixing them into a package
named for a bug would misfile them.

**JUDGMENT (slice 1, raft shape):** the integration case ships in two
forms, a plain function (`big(v)`) and a METHOD (`pr.active()`),
because raft writes the method form
(`if pr, ok := m[id]; ok && pr.IsPaused()`) and the method call takes a
different emission path (receiver evaluation) into the same
short-circuit RHS accumulator. Pinning only the plain form would have
left the shape we actually care about unwitnessed.

**Gate at the enumeration commit:** `GOLEAN_MEM_MAX=24G scripts/ci
--diff`, full run — every step `ok`, and the baseline diff's ONLY
drift was the 13 `NEW id` lines (no PASS↔FAIL flip, no stage change,
no dropped id on any of the 2089 pre-existing rows; `diff` of the old
vs new row blocks shows 13 pure insertions). Baseline re-pinned in
this commit from that full run: 2102 cases, 1959 PASS / 143 FAIL.
`scripts/check-bugs.sh`: ok (61 bugs; pinned cases behave as claimed).

### Step 2 — the fix

`tools/nativefrontend/emit.go`, `emitIf` only (+52/-3 lines, all of it
in that one function). Two halves:

1. **Scope the condition's accumulator** — when `st.Init != nil`, the
   condition is emitted with `e.hoisted` saved/nil'd/restored around
   `e.emitExpr(st.Cond)`, the same save/capture/restore the ELSE
   branch has used since the else-if fix and `emitFor` uses for
   `condPre`/`post`. When `st.Init == nil` the old path is kept
   verbatim: there is no scope to stay inside, and the enclosing
   accumulator already places the temps immediately before the if.
2. **Re-establish the init's scope around them** — with a non-empty
   condition accumulator, `emitIf` returns a wire
   `block` of `[init, condHoists…, if]` instead of an `if` node
   carrying an `init` key. That block is *the same scope the decoder
   already builds*: `decodeIf` lowers the `init` key as
   `.block #[] #[init, ifThenElse …]`
   (`GoLean/NativeToIR.lean:1143-1153`). So the init-declared names
   are visible to the hoists, to the condition and to both branches —
   the implicit block spec#Blocks gives the statement ("Each `if`,
   `for`, and `switch` statement is considered to be in its own
   implicit block").

**JUDGMENT (slice 1, mechanism choice).** The obvious alternative was
to mirror `emitFor` exactly: add a `condPre` key to the wire `if`
node and splice it in `decodeIf`. Rejected: that is a wire-schema
change plus a decoder change to buy a shape the decoder *already*
produces for `init`. The block wrapper is frontend-local (the
charter's "emitIf-local"), touches no Lean file, and cannot introduce
a scope the decoder did not already have. `for` genuinely needs
`condPre` because its condition is re-tested every iteration —
`if` tests once, so a straight-line splice is exact.

**JUDGMENT (slice 1, minimality).** The wrap fires ONLY when there is
both an init and a non-empty condition accumulator. An `if` without an
init, or with an init and a hoist-free condition, emits the same bytes
as before — which is why the full run's drift is exactly the bug's own
family and nothing else.

**Predicted flip set, stated before the confirming run (10 red→green,
1 new green id, nothing else):**

- `spec-examples-lexical/panic-values/panic-error`
  (FAIL/lean-observation → PASS)
- `spec-examples-stmt/if-init-hoist-order/{cond-call-after-init,
  init-panic-first, else-if-chain, func-literal, nested,
  cond-panic-after-init}` (FAIL/differential → PASS)
- `spec-examples-stmt/if-init-hoist-order/{cond-hoist-reads-init,
  comma-ok-short-circuit, comma-ok-method-short-circuit}`
  (FAIL/lean-observation → PASS)
- `control-flow/goto-if-init-cond-hoist` (NEW → PASS)

**The goto interaction case, and why it is in this commit.** The fix
changes the SHAPE of a top-level statement inside a goto-restructured
segment (an `if` node becomes a `block`), and `degradeGotoDeclares`
(emit.go:1130) rewrites top-level source declarations there. The
init's declaration is nested in both shapes — under the `init` key
before, inside the block after — so it keeps its `declare` in both,
which is correct (a backward jump re-declares it). "Correct by the
same argument in both shapes" is the kind of claim that deserves a
case, so `control-flow/goto-if-init-cond-hoist` pins it.
**JUDGMENT (slice 1):** it is a NEW id in the fix commit rather than
in the enumeration commit because the interaction it probes is a
property of the fix, not of the bug — but it was verified RED under
the pre-fix emitter first (`git stash` of `emit.go`,
`scripts/coverage run --prefix control-flow/goto-if-init-cond-hoist`
→ `cases=1 pass=0 fail=1`), so it is a genuine BUG-058 witness and
not a case written to match the implementation.

### Step 3 — masked-green sweep

**Scope and method.** Mechanized: an AST scan
(`artifacts/probe/sweep`, scratch) over every `.go` file under
`Corpus/`, `raftharness/` and `compat/`, finding every `ast.IfStmt`
with `Init != nil` and reporting whether its `Cond` contains a
hoist-capable construct (call, composite literal, receive, func
literal). AST-based rather than grep-based so that multi-line and
nested shapes cannot hide — a line grep had already missed shapes,
which is why this was mechanized.

**Findings.**

- `Corpus/`: **85** if-with-init statements; **17** with a
  hoist-capable construct in the condition. 15 of the 17 are this
  slice's own `if-init-hoist-order` package. Of the other two:
  - `spec-examples-lexical/panic-values:40` — the already-pinned red
    (`ok && e.Error() == …`), now green.
  - `spec-examples-lexical/channel-direction-forms:19` —
    `if got := <-bidi; int(got) == 7`. The scanner counts `int(got)`
    as a call; it is a CONVERSION, which the frontend does not hoist.
    Green before the fix and after it — and that green is itself the
    evidence that conversions do not hoist (if they did, `got` would
    have been unbound and the case stuck).
- `raftharness/`: 20 if-with-init, 1 flagged (`scenarios.go:54`,
  `len(v) > 0` — a builtin, not a hoist). Not a differential case in
  any event; the harness runs in real Go.
- `compat/`: 0 if-with-init statements.

**Conclusion: no masked green.** No corpus case outside this bug's own
family combined an if-with-init with a hoisting condition, so no
green could have coincided with correctness. This is the honest
negative result the charter asked for, with its scope stated — not an
absence of looking.

**One disposition-level finding, recorded rather than dropped.** It is
a *sufficiency* gap, not a mask: `If_statements-3-23172299`'s five
rows (`spec-examples-stmt/if-init-else-chain/*`) pin the branch
structure of `if x := f(); x < y … else if … else …`, but nothing in
them can observe ORDER — the init's `f()` is un-hoisted and every
condition is a pure comparison. So the spec block's own sentence
("which executes before the expression is evaluated") was unwitnessed
while the machine had exactly that order wrong. The order witnesses
are the `if-init-hoist-order` and `init-hoist-relatives` families;
the disposition row now says so, and
`Handling_panics-2-e7d4cef6` now records that `panic-int` /
`panic-string` were never masked (a pure short-circuit right operand
hoists nothing) while `panic-error` was the family's only red.

**For the arc's later slices:** `deps/raft` itself has 103
if-with-init statements, 12 with a call in the condition — the shape
this fix unblocks is not hypothetical for W4.

### Gate at the fix commit

`GOLEAN_MEM_MAX=24G scripts/ci --diff`, full run at the fix tree. The
baseline diff's drift was **exactly the predicted set and nothing
else**: the 10 red→green flips listed above plus
`control-flow/goto-if-init-cond-hoist` as a NEW/PASS id, across 2103
cases. In particular the 6 `init-hoist-relatives` greens all held, so
the fix did not disturb `emitFor`/`emitSwitch`/`emitTypeSwitch`. Every
other step `ok`, including the re-pin guard (0 PASS→non-PASS flips)
and `eval tests (136 ok)`. Baseline re-pinned in the fix commit from
that run: 2103 cases, 1970 PASS / 133 FAIL (was 1959/143), reason in
its header. `scripts/check-bugs.sh` then reports ok (61 bugs) with
BUG-058 marked fixed — the cross-check is what refuses a
"fixed" entry whose cases are still red, so its green is a real
confirmation, not a formality.

The run that produced these numbers was started before two
COMMENT-ONLY edits to `emit.go` (a spec citation corrected from
`spec#Declarations_and_scope` to the accurate `spec#Blocks` implicit
-block sentence), so the gate was re-run at the committed tree to
keep the record exact; that re-run is the one recorded as the slice's
gate (see the slice-1 tail below).

**Slice 1 state: BUG-058 fixed and closed.** All 10 of its pinned
cases green, the edge set landed, the raft integration shape green in
both plain and method form, the non-affected relatives pinned green,
the masked-green sweep recorded with its scope and its one
disposition-level finding.
