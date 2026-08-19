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
| 1 | BUG-058 — if-init condition-hoist scope | DONE (`8a42e402` enumeration, `740f09f8` fix; gate PASS at `740f09f8`) |
| 2 | BUG-057 — two-var comma-ok var-decl arity | enumeration landed; fix pending |
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
keep the record exact. **That re-run is the slice's recorded gate:
`GOLEAN_MEM_MAX=24G scripts/ci --diff` at `740f09f8` →
`RESULT: PASS`, every step ok, `baseline diff FULL (2103/2103, no
regression)`, negative lane 390/390, `re-pin guard (0 PASS→non-PASS
flips, all listed in BUGS.md Cases)`.**

**Slice 1 state: BUG-058 fixed and closed.** All 10 of its pinned
cases green, the edge set landed, the raft integration shape green in
both plain and method form, the non-affected relatives pinned green,
the masked-green sweep recorded with its scope and its one
disposition-level finding.

---

## Slice 2 — BUG-057: the two-variable comma-ok var-declaration arity hole

Entry: `docs/BUGS.md` "BUG-057 — two-variable comma-ok VAR DECLARATIONS
drop the ok flag". Diagnosis audit-hardened at the P3 pre-merge audit
(F-2 corrected the scope, F-10 recorded the typed form's observational
limitation); this slice re-verified its cites before touching anything.

### Diagnosis re-verification (before any change)

- The pairing site is `emitDeclStmt`, `tools/nativefrontend/emit.go`.
  The entry's "2383-2392" cite is the P3-era line number; at slice-2
  start `emitDeclStmt` begins at emit.go:2436 and the offending loop is
  emit.go:2473-2513. The MECHANISM is exact:
  `for i, name := range vs.Names { … if i < len(vs.Values) { … } }`
  pairs the spec's names to its initializer expressions POSITIONALLY,
  with no arity check, so for `var v, ok = m[k]` (2 names, 1 value)
  name `v` gets the initializer and name `ok` gets a decl entry with no
  `init` key at all. `decodeVar` (`GoLean/NativeToIR.lean:1130-1141`)
  emits `.initialization` for every decl and `.assign` only when `init`
  is present, so `ok` is left at its zero value — false.
- The contrast the entry names is also exact, and it is in this same
  file: the PACKAGE-level path never uses `emitDeclStmt`. It fabricates
  ONE `ast.AssignStmt` carrying every name of a multi-value spec
  (emit.go:600-607) and runs it through `emitAssign`, whose comma-ok
  branches (type assertion emit.go:2136-2157, channel receive
  emit.go:2163-2167, map index via the generic 2-target path) are
  correct. So the fix direction the charter names — "lowered through the
  same path as the correct short-decl form" — is also the path the
  package-level declaration has always used.

### Step 1 — edge enumeration (own commit, colors recorded BEFORE the fix)

Every expectation is `go run`'s, computed before the differential ran
(`artifacts/probe/commaok`; scratch, not tracked). Colors from
`scripts/coverage run --prefix spec-examples-decl/var-comma-ok-matrix`
against the UNMODIFIED emitter: **46 cases, 22 PASS / 24 FAIL.**

**The matrix.** Three comma-ok sources (receive `<-ch`, map index
`m[k]`, type assertion `x.(T)`) × untyped (`var v, ok = …`) / typed
(`var v, ok T = …`) × blank in the value position / blank in the ok
position / neither × function-local / package-level = 36 rows, plus 3
interface-typed rows, 5 position/shape rows and 2 tuple-call rows.

Two design rules every row obeys:

- **TRUE ok on the observing line** (the MASKING lesson): a comma-ok
  case whose ok is FALSE cannot distinguish delivery from drop, because
  the dropped flag's zero value *is* false. That is exactly how the
  original P3 evidence went green on a closed-drained channel and an
  absent key.
- **Value and ok as SEPARATE observables** (closes F-10): the harness
  supports multi-result subjects, so every row returns `(value, ok)`
  rather than `value && ok`. Correct is `(v, true)`; a dropped ok is
  `(v, false)`; a dropped value is `(zero, true)` — three distinct
  observations where the old subject had one bit.

**Pre-fix reds — silent wrong answer, `differential` (11):**

| row | shape | go | machine (pre-fix) |
| --- | --- | --- | --- |
| `recv-untyped` | `var v, ok = <-ch` | 7, true | 7, **false** |
| `recv-untyped-blank-value` | `var _, ok = <-ch` | true | **false** |
| `recv-typed` | `var v, ok bool = <-ch` | true, true | true, **false** |
| `recv-typed-blank-value` | `var _, ok bool = <-ch` | true | **false** |
| `index-untyped` | `var v, ok = m[k]` | 7, true | 7, **false** |
| `index-untyped-blank-value` | `var _, ok = m[k]` | true | **false** |
| `index-typed` | `var v, ok bool = m[k]` | true, true | true, **false** |
| `index-typed-blank-value` | `var _, ok bool = m[k]` | true | **false** |
| `func-literal` | the declaration inside a closure | 7, true | 7, **false** |
| `grouped-spec` | comma-ok spec BETWEEN two ordinary specs | 2, 7, true | 2, 7, **false** |
| `after-goto` | the declaration in a goto-restructured body | 7, true | 7, **false** |

Note what the typed rows now show that F-10's `x && ok` could not: the
VALUE arrives correctly (`true`, not the zero `false`) and only the ok
is lost. The entry's "the value arrives, the boolean is lost" is now
case-pinned rather than wire-argued.

**Pre-fix reds — fail closed, `frontend-export` (13):** the six local
type-assertion rows (`assert-{untyped,typed}[-blank-value|-blank-ok]`,
"type assert form outside a 2-target assignment"); the three
interface-typed rows `{recv,index,assert}-typed-iface`; `iface-value`;
`shadow-capture`; and `tuple-call-{untyped,typed}` ("type
*types.Tuple").

**Pre-fix greens (22):** all **18** `pkg-*` rows — the package-level
form is correct for every source, typedness and blank position, now
with a TRUE ok observed — and the **4** local `*-blank-ok` rows
(`var v, _ = …`), which observe the VALUE half only and were therefore
never wrong. Those four are load-bearing pins, not decoration: they are
the only rows that can catch a fix which delivers `ok` by breaking the
value.

**Three findings the enumeration establishes** (all folded into the
BUGS.md entry):

1. The silent drop is **receive + map index only** — the type-assertion
   source fails CLOSED. The entry's "(probe: `= x.(T)`)" is resolved,
   and `spec-examples-decl/assert-comma-ok` was already red for exactly
   that reason.
2. Package-level correctness is now **case-pinned with a true ok**, not
   only wire-argued.
3. The typed form is **not bool-only**: `var v, ok T = x` also admits an
   interface T both values are assignable to — the shape
   spec#Type_assertions itself writes,
   `var v, ok interface{} = x.(T)`. My first draft of this package
   asserted "T must be bool"; the sweep (step 3) found
   `assert-comma-ok`'s `var v4, ok4 interface{} = x.(int)` and refuted
   it, which is why the three `-typed-iface` rows exist.

**JUDGMENT (slice 2, package placement):** the matrix went into a NEW
package `spec-examples-decl/var-comma-ok-matrix/` rather than being
appended to the three existing pin packages. Those three are
spec-BLOCK packages (`Receive_operator-2-…`, `Index_expressions-2-…`,
`Variable_declarations-2-…`) whose subjects mirror one spec block's
example; a 46-row cross-product indexed by lowering shape rather than
by spec block would misfile there and would break the one-block-one-
package reading of the dispositions. The four existing pins stay where
they are and stay in the entry's `Cases:` list.

**JUDGMENT (slice 2, the -typed-iface rows are RED on purpose):** they
are pinned even though they cannot pass, because the fix REROUTES
exactly these specs away from the guard that refuses them today. A
reroute that silently turned a fail-closed refusal into an unboxed
interface store would be invisible without them — the "fail-closed
classification" blindness the audit doctrine names.

**Gate at the enumeration commit:** `GOLEAN_MEM_MAX=24G scripts/ci
--diff`, full run. The pre-re-pin run's ONLY drift was the **46
`NEW id` lines** (2149 cases run vs the 2103-row baseline: no
PASS↔FAIL flip, no stage change, no dropped id on any pre-existing
row), and `bug-index cross-check` failed only with 11 "case not found
in baseline" lines — the new BUG-057 `Cases:` rows, which the ratchet
requires so 11 fresh `differential` reds cannot hide in the untriaged
pile. Baseline re-pinned in this commit from that full run: **2149
cases, 1992 PASS / 157 FAIL** (was 2103, 1970/133), reason in its
header. The confirming re-run at the committed tree is **`RESULT:
PASS`** — every step ok, `baseline diff FULL (2149/2149, no
regression)`, `re-pin guard (0 PASS→non-PASS flips…)`,
`eval tests (136 ok)`, negative lane clean, and
`scripts/check-bugs.sh: ok (61 bugs; pinned cases behave as claimed)`
with the untriaged backlog unchanged at 25/25.
