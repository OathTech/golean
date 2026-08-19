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

(recorded at the fix commit)

### Step 3 — masked-green sweep

(recorded at the fix commit)
