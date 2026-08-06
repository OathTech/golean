# Known fidelity bugs — the SINGLE canonical index

A **fidelity bug** is a case where GoLean gives a *wrong* answer relative to real
Go: a wrong value, or a wrongly-*stuck* run on a construct we claim to support.
(A construct we don't model yet is not a bug — it must fail closed at the
frontend boundary as `frontend-export`, and is tracked as coverage, not here.)

This file is machine-cross-checked against the recorded differential **baseline**
(`baselines/native-full.tsv`) by `scripts/check-bugs.sh` (part of `scripts/ci`),
so a bug can neither rot in prose nor silently outlive its evidence:

1. every `- Cases:` id of an open `Pinned-by: differential` bug **exists in the
   baseline and is currently `FAIL`** — if a listed case now `PASS`es, the bug is
   fixed-but-not-closed (or the case no longer pins it), and the check fails;
2. every `Status: open` + `Pinned-by: differential` bug lists ≥1 case;
3. (warning) the check reports how many baseline **fidelity failures**
   (`stage=lean-observation`, `stage=differential`, or `stage=membership` —
   wrong/stuck answers and membership-lane alarms, not frontend-coverage
   gaps; membership added at the arc-final audit, F9 2026-08-06) are **not**
   yet explained by any bug entry — the omission surface to ratchet toward
   zero.

Bugs that cannot yet be mechanically pinned use `Pinned-by: none (<reason>)` and
are exempt from (1)/(2) — but still listed, so they cannot disappear.

**Entry format (keep parseable):** a `## BUG-NNN — <title>` heading, then
`- Status: open|fixed`, `- Pinned-by: differential|none (<reason>)`, and (for
differential-pinned) `- Cases: <id>, <id>, …` (baseline case ids), then prose.

---

## BUG-033 — targetPlan defers only the OUTERMOST address op: `a[i].f` fires the inner index check in phase 1

- Status: fixed (2026-08-06, round-4 response: `targetPlan` now
  decomposes the FULL address-former spine — `targetSpine` collects
  the `indexAddr`/`fieldAddr` steps inner-first with the anchor and
  index operands as the phase-1 expressions, and `storeTarget`
  replays the chain (`resolveChain`) at the store, every bounds/nil
  check included. The probed boundary is preserved exactly: a VALUE
  step in the base (index-GET on `[][]int`, a deref) is an operand and
  stays phase 1 — the `inner-value-guard`/`array-nested` guards and
  all prior discriminators stay green. All five chain pins flip.)
- Pinned-by: differential
- Cases: multi-assign/chain-field-over-index, multi-assign/chain-field-over-index/nil-slice-field, multi-assign/chain-field-over-index/array-field, channels/recv-edge/chain-field-over-index, channels/select-recv-edge/chain-field-over-index
- Discovered: 2026-08-06 (round-4 convergence check, verified critical;
  pre-existing behavior — the round-3 spine closed the outermost level
  and left the same class one nesting level deeper — but the round-3
  prose claimed the boundary exact)

gc treats a target's whole address CHAIN — every `indexAddr`/
`fieldAddr` step from the anchor outward — as ONE phase-2 address
computation: its bounds/nil checks fire AT THE STORE, after earlier
targets' stores landed (probed: `x, a[9].f = 5, 1` go 105 on the
plain, receive-statement and select paths; nil-slice, array-index and
nested-array `arr[1][j]` variants all 105). `targetPlan` decomposes
one level, so the inner `indexAddr` rides the strict-op evaluator and
panics in phase 1 (ours 100). The probed CONTRAST boundary: a VALUE
step in the base — `aa[9][0]` on `[][]int`, whose inner element is an
index-GET producing a slice value — is an index-expression OPERAND and
stays phase 1 (go 100; `inner-value-guard` and `array-nested` pin the
green directions). Fix: recurse `targetPlan` through the address-former
chain, evaluating only the anchor and index operands in phase 1 and
replaying the chain (checks included) in `storeTarget`.

## BUG-034 — comma-ok `v, ok = m[k]` / `v, ok = x.(T)` still ride the eager stmtPlan path

- Status: open (round-4 disposition, migrate-or-scope-honestly: a full
  spine migration WAS built and validated (RhsOp/applyRhsOp, both pins
  flipped, zero corpus drift) and then REVERTED in the same round —
  retiring `StmtOp.mapLookup`/`.typeAssertStmt` breaks the shipped
  `wp_map_lookup` law family (`Laws/StmtOps.lean`, the three-cell
  comma-ok law used by the HEADLINE quorum walk at
  `GoldenQuorumWP.lean:183` plus its GoldenQuorumPin witnesses), whose
  spine restatement is a coordinated laws rework, not a round patch.
  Scheduled with the BUG-025 call-write-back and BUG-037 migrations as
  ONE machine+laws slice; the two pins stay red and visible.)
- Pinned-by: differential
- Cases: multi-assign/comma-ok-forms/map-oob, multi-assign/comma-ok-forms/assert-nil-field
- Discovered: 2026-08-06 (round-4 convergence check, verified major;
  pre-existing — outside the round-3 migration's enumeration, inside
  its "every multi-target store path" claim)

`stmtPlan` still classifies `.mapLookup`/`.typeAssert` with
`ntargets = 2`: both target addresses resolve eagerly (checks
included) and store all-or-nothing, so `xs[0], bs[9] = m[1]` and
`xs[0], p.b = iv.(int)` lose the first store gc performs before the
deferred oob/nil-field check (go 1007/1005, ours 1000/1000). The
phase-1 operand-capture half is correct (`dep-index` guard green).
Fix: route both forms onto the tgtOpK/storeK spine, applying the
lookup/assert after the RHS operands as the value source.

## BUG-035 — a blank among the targets diverts multi-assign off the spine (phase-1 capture lost)

- Status: fixed (2026-08-06, round-4 response: blank positions become
  fresh DISCARD locals (typed from the matching RHS expression) inside
  ONE `.assignMany`, so blank-containing statements ride the
  phase-split spine like every other multi-assign; `_ = e` keeps a
  single effect-evaluating assign. The pin flips;
  blank-discard-nonint stays green.)
- Pinned-by: differential
- Cases: multi-assign/blank-dep-index
- Discovered: 2026-08-06 (round-4 convergence check, verified major;
  pre-existing decoder lowering, vintage bca14c5)

The decoder's blank-containing multi-assign lowering (RHS temps +
per-target single assigns) evaluates a later target's index operands
AFTER earlier stores: `i, _, a[i] = 2, 0, 99` reads the POST-store `i`
(go 29920-class value vs ours) — the spec's own `i, a[i]` phase-1 rule,
silently wrong whenever ≥1 blank and ≥2 real targets with a
dependence. Fix: declare fresh discard temps for blank positions and
emit ONE `.assignMany` so the statement rides the spine.

## BUG-036 — select temp-fallback lowering retains the phase collapse (silent, not fail-closed)

- Status: fixed (2026-08-06, round-4 response: the fallback's user
  write-back is ONE body-side multi-assign — clause locality holds
  (temps, hoists and the write-back all inside the clause body, BOTH
  targets' hoists before both stores) and the statement rides the
  spine. The pin flips; unselected/selected-receive-lhs and
  closed-receive-declare guards stay green.)
- Pinned-by: differential
- Cases: channels/select-recv-edge/fallback-call-index
- Discovered: 2026-08-06 (round-4 convergence check, verified major;
  the fallback is the pre-existing lowering — round 3 shrank its
  domain but left it silently collapsing)

When a clause target's emission hoists (a call in an index) or needs
boxing, `selectRecvClause` falls back to temps + body-side SINGLE
assigns: target 1's store lands before target 2's address operands
evaluate (go 101 vs ours 102). Clause locality demands the temps, not
the collapse: the fallback can emit ONE body-side multi-assign (the
spine, post-BUG-025) and keep the phase split inside the clause.

## BUG-037 — single assignment fires the target's phase-2 check before evaluating the RHS

- Status: open (round-4 disposition, migrate-or-scope-honestly: the
  spine migration (`assignFirst`, retiring the `assignTargetK`/
  `assignStoreK` frames) WAS built and validated — all three pins
  flipped, zero corpus drift — and then REVERTED in the same round:
  those frames anchor the entire shipped WP assignment law family
  (`wp_assign_start`/`wp_assign_target`/`wp_assign_store*` in
  `Laws/Eval.lean`, with the `wp_assign_lit` non-vacuity witness in
  `Laws/Assign.lean`, and every golden walk's store steps; file
  pointer corrected 2026-08-06 final check — b86993e's commit message
  carries the old wording).
  Restating that family over the spine is the same coordinated
  machine+laws slice as BUG-025's call write-back and BUG-034;
  the three pins stay red and visible until it lands.)
- Pinned-by: differential
- Cases: assign-order/target-check-vs-rhs/index-target, assign-order/target-check-vs-rhs/nil-field-target, assign-order/target-check-vs-rhs/nil-deref-target
- Discovered: 2026-08-06 (round-4 convergence check, verified major;
  pre-existing — the round-3 doctrine was applied only to multi-target
  statements)

`.assign` evaluates the full target address (bounds/nil checks
included) BEFORE the RHS; spec §Assignments puts the RHS in phase 1
and the assignment's own check in phase 2, and gc realizes exactly
that: `a[9] = 1/z`, `p.f = 1/z` (nil p), `*p = 1/z` all panic with the
RHS's divide-by-zero in gc, with our index/nil-deref panic — a wrong,
recover-observable panic identity on the most common statement shape.
Adding a second target already flips us correct (the migrated path).
Fix: route `.assign` through the same tgtOpK/rhsK/storeK spine
(1-target multi-assign) and retire the assignTargetK/assignStoreK
frames.

## BUG-038 — storing through a nil pointer-to-array element goes STUCK instead of panicking

- Status: fixed (2026-08-06, round-4 response: `indexTargetLoc` gains
  the `.nil` arm mapping to gc's recoverable nil-pointer-dereference
  panic — the `valueAsLoc` convention — which fires at the store on
  the phase-2 path (second-target pin: earlier store lands first,
  go 105). The READ-position sibling `pointers/nil-array-index-panic`
  takes a different path (index-GET) and remains in the untriaged
  ledger, unchanged.)
- Pinned-by: differential
- Cases: pointers/nil-array-elem-store, pointers/nil-array-elem-store/second-target
- Discovered: 2026-08-06 (round-4 convergence check, verified minor;
  pre-existing — the round-3 factoring only moved the arm)

`indexTargetLoc` has arms for `.slice` and `.addr` bases only; a nil
`*[N]T` base falls to the stuck arm where gc panics with the
recoverable nil-pointer dereference (at the STORE — go 1 recovered,
105 in the second-target shape). Fail-closed in direction but a
wrongly-stuck supported construct. Fix: a `.nil` arm mapping to the
nil-pointer-dereference panic, the `valueAsLoc` convention.

## BUG-039 — panicFreeOperand misses IMPLICIT indirection through embedded pointer fields (BUG-032's hole)

- Status: fixed (2026-08-06, round-4 response: the `SelectorExpr` arm
  consults go/types `Selections[…].Indirect()` first — ANY implicit
  indirection makes the operand non-panic-free, so the BUG-032
  refusal applies. The pin moves differential -> frontend-export: a
  permanent fail-closed refusal marker like dead-recv-len-operand,
  never a silent wrong answer; the receive-free control stays green.)
- Pinned-by: none (the discriminating shape now fails closed at the
  frontend — channels/recv-order/dead-recv-len-embedded is a permanent
  frontend-export refusal, tracked as coverage, not a fidelity pin)
- Discovered: 2026-08-06 (round-4 convergence check, verified major:
  the predicate BUG-032 shipped is fail-open one route deeper)

The `SelectorExpr` arm walks the SYNTACTIC chain and checks
pointer-ness of visible bases only; a selector through an EMBEDDED
POINTER field (`o.xs` with `o.Inner` a `*Inner`) is claimed panic-free,
so the len hoist drags its nil deref ahead of the spec-unordered
type-assertion panic to its left — BUG-032's exact signature (a DEAD
receive elsewhere flips which panic fires; the receive-free control
`len-embedded-no-recv` is green). Fix: consult go/types
`Selections[…].Indirect()` — any implicit indirection makes the
operand non-panic-free (then the BUG-032 refusal applies).

## BUG-029 — receive/select delivery collapses spec §Assignments' two phases: target k's store happens before target k+1's ADDRESS evaluates

- Status: fixed (2026-08-06, convergence response, two movements. The
  MACHINE movement made spec §Assignments' two phases explicit
  structure: `tgtOpK` (phase 1) evaluates every target's OPERANDS
  left-to-right after the communication, resolving each target to a
  store-ready `TargetRef` (`targetPlan`/`completeTargetRef`) with the
  OUTER nil/bounds/nil-map check deferred; `storeK` (phase 2,
  `.next`-driven) stores left-to-right ONE step per target,
  `storeTarget` firing the deferred check at the store, after earlier
  stores landed. The FRONTEND movement routes select receive-clause
  user targets into the same delivery plan (`machineSelectTargets`)
  instead of body-side single assigns — falling back to the temp
  lowering for `:=`/blank/boxing/hoisting targets, where step-4
  clause-locality demands it. All four discriminators plus the three
  collapse-direction guards green.)
- Pinned-by: differential
- Cases: channels/select-recv-edge/dep-index-target, channels/select-recv-edge/nil-index-base-second
- Discovered: 2026-08-06 (channels-arc-s1 convergence round; introduced
  by the D3 fix, commit 12f2d42 — a regression of the OPPOSITE phase)

Spec §Assignments is two-phase: phase 1 evaluates the LHS
index/indirection OPERANDS (and the RHS) in the usual order; phase 2
carries the assignments out left-to-right. The D3 per-target
store-then-next rule (`selectRecvStore`) INTERLEAVES them: it stores
target k and only then evaluates target k+1's address expression. Two
silent wrong answers, no panic involved on the first: `i, bs[i] = <-ch`
reads the POST-store `i` for the index (go 301, ours 304), and
`xs[0], (*bp)[0] = <-ch` with nil `bp` stores `xs[0]` before the index
BASE's phase-1 nil deref (go 1000, ours 1050) — both on the
receive-statement AND select-clause paths. The pre-D3 shape
(all addresses, then one `storeMany`) got phase 1 right and phase 2
wrong; the two collapse directions can only trade divergence classes.
The fix must SPLIT the phases: phase 1 resolves every target to a
store-ready reference (operands evaluated left-to-right, the OUTER
nil/bounds check deferred), phase 2 stores left-to-right one step per
target — the deferral is pinned by the currently-green discriminators
channels/recv-edge/{field,oob}-second-target-stores-first and
channels/select-recv-edge/field-second-target-stores-first (gc fires a
nil FIELD target's and an out-of-range index's check AT THE STORE,
after earlier stores landed).

## BUG-030 — map-element FIRST target's store is lost when a later receive target's store panics (post-statement map-assign lowering)

- Status: fixed (2026-08-06, convergence response: a TWO-target
  receive's map-element target rides the machine's delivery plan as an
  `Assignee.mapElem` ("map" wire target) — base/key evaluate in phase 1
  (post-communication, the BUG-028 point), the map store is a phase-2
  left-to-right `storeTarget` step via the shared `mapAssignValue`, so
  it survives a later target's store panic. Interface-valued maps with
  a concrete element fail closed in this form (the machine stores the
  delivered value raw). The SINGLE-target `m[k] = <-ch` keeps the
  post-statement map-assign — one store, order cannot be violated, and
  it carries the boxing wrap. Select clauses reuse the same machinery
  through `machineSelectTargets`.)
- Pinned-by: differential
- Cases: channels/recv-map-elem/first-store-lands
- Discovered: 2026-08-06 (channels-arc-s1 convergence round, verified
  major; lowering shape pre-existing, S4)

`m[0], *okp = <-ch` with nil `okp`: gc stores `m[0]` (phase 2 is
left-to-right) and then panics storing `*okp` — the map store SURVIVES
(go 1050). The S4 lowering emits the map-assign AFTER the whole
chan-recv statement, so the later target's store panic skips it
entirely (ours 1000). This is the receive-path instance BUG-025's
original prose wrongly declared fixed: the general multi-assign
sibling (`m[0], *okp = 4, true`) fails closed at the frontend, making
this the one place a map-element multi-target silently answers wrong.

## BUG-031 — $deferRecoverNoop registration outlives a quarantined declaration: later `defer recover()` references a never-emitted function

- Status: fixed (2026-08-06, convergence response: the flag is
  saved before each declaration/stencil emission and restored on the
  same rollback paths that truncate `e.lifted` (per-decl quarantine and
  the mono stencil error path), so registration and emission stay
  atomic; the next `defer recover()` re-registers the no-op.)
- Pinned-by: differential
- Cases: defer/recover-noop-after-quarantine
- Discovered: 2026-08-06 (channels-arc-s1 convergence round, verified;
  pre-existing — `deferNoopEmitted` dates to 2026-07-25, untouched by
  this arc)

`deferNoopEmitted` is a sticky emitter flag set when the synthetic
no-op is appended to `e.lifted`, but `e.lifted` is rolled back
wholesale on the per-decl quarantine path (`e.lifted = nil`) and
truncated on the stencil path (`e.lifted[:liftedMark]`) — registration
and emission are non-atomic. If the FIRST `defer recover()` sits in a
declaration that is later quarantined (e.g. it also contains a `go`
statement), every subsequent `defer recover()` in the package
references a function that was never emitted: an unrelated, fully
supported subject is wedged (`GoCore function not found:
$deferRecoverNoop`, status stuck). Fail-closed (never a wrong answer),
but the BUG-024/BUG-027 blast-radius class. Fix: save/restore the flag
alongside every `e.lifted` rollback (both paths).

## BUG-032 — the fnHasRecv len/cap hoist drags its OPERAND's panic ahead of spec-unordered panics to its left

- Status: fixed (2026-08-06, convergence response: the hoist is
  restricted to syntactically PANIC-FREE operands — identifiers,
  literals, pointer-free selector chains (`panicFreeOperand`); a
  potentially-panicking operand in a receive-bearing function now FAILS
  CLOSED (`unsupported`) rather than picking between the two misorders
  (inline loses the len-vs-receive order, hoisted loses the
  operand-panic order — realizing gc's exact point for that shape needs
  full-statement linearization of the panicking operands to its left,
  deliberately not built this round; the refusal keeps it visible). The
  pin channels/recv-order/dead-recv-len-operand accordingly stays RED,
  reclassified differential -> frontend refusal — a permanent
  fail-closed marker like channels/select-multi-ready, not a silent
  wrong answer. The false "over-hoisting is unobservable" claims in
  wire.go and BUG-023/BUG-026 are corrected in place.
  ROUND-4 AMENDMENTS: (a) the predicate was fail-open one route deeper
  — implicit indirection through embedded pointer fields — closed by
  BUG-039 (go/types `Selections[…].Indirect()`); (b) the same
  unordered-panic ENVELOPE class exists in the assignment path's
  phase-1 order (targets' operands then RHS — `xs[ys[9]], b = zs[7],
  2` realizes the LHS-operand panic where gc realizes the RHS's; both
  points spec-legal, pre-existing, identical on the single-assign
  path, and realizing gc's exact point needs the same full-statement
  linearization this entry already records as deliberately not
  built). Amendment widened at the 2026-08-06 final check: the class
  also has an early-STORE manifestation crossing the phase boundary —
  `x, a[i].f = 1, 7/z` (z=0, recovered): gc lands the x=1 store before
  the phase-1 division panic; we follow the spec's literal two-phase
  order (x stays 0). Both spec-legal (§Order of evaluation orders only
  calls/receives/binary-logical), both sides panic identically when
  unrecovered, pre-existing on both the spine and pre-spine paths, no
  pin. Distinct mechanism from the panic-selection example above —
  a fix would need the store held back, not panics linearized; its
  natural home is the BUG-025 retirement slice. A future pin in this
  shape must use the membership/envelope treatment, not strict
  equality.)
- Pinned-by: none (the discriminating shape now fails closed at the
  frontend — channels/recv-order/dead-recv-len-operand is a permanent
  frontend-export refusal, tracked as coverage, not a fidelity pin)
- Discovered: 2026-08-06 (channels-arc-s1 convergence round, verified —
  severity minor: both realized orders are spec-legal, but the
  justifying claim in BUG-023/BUG-026 and wire.go was FALSE and the
  trigger is non-local)

The BUG-026 scope argument — "over-hoisting len/cap is unobservable
(pure, non-panicking, lexically placed)" — is true of the BUILTIN but
not of its OPERAND: `emitBuiltin` hoists the whole `len(b[j])` node,
dragging the operand's index panic ahead of a spec-unordered panicking
operand to its left. `return iv.(int) + len(b[j])` panics with gc's
interface-conversion message in a receive-free function but with our
index-out-of-range message as soon as a DEAD receive exists anywhere in
the enclosing function. Within the spec envelope (only calls, receives
and binary-logical ops are ordered) but outside gc's realized
left-to-right point, a regression against the per-statement sweep, and
the false comment is exactly what a maintainer would cite to widen the
hoist further.

## BUG-025 — multi-target assignment phase 2 is all-or-nothing, not left-to-right (earlier stores lost when a later store panics)

- Status: open (REOPENED at the round-4 convergence check: the round-3
  closure was over-broad. FIXED half — the `assignMany` STATEMENT no
  longer rides `stmtPlan`/`applyStmtOp`: it enters the phase-split
  spine (`tgtOpK` target operands with deferred checks, `rhsK` RHS
  left-to-right, `storeK` one store per step) — pinned GREEN by
  multi-assign/{store-order-plain,field-nil-store-time} and the twelve
  order/aliasing guards; `StmtOp.assignMany` and `locsOf` removed
  outright. OPEN half — the entry's own scope line always named
  "frame-exit `storeMany`": the multi-value CALL write-back path
  (`callTargetsK`/`callValTargetsK` → frame-exit `storeMany`) still
  resolves target addresses (checks INCLUDED) before the call and
  stores all-or-nothing, so a bad target SUPPRESSES the call and its
  side effects (go 117 vs ours 100), the call's own panic loses to our
  target check (wrong panic value), and a nil FIELD target on the call
  path loses the first result's store (go 107 vs ours 100). Migrating
  it means carrying `TargetRef`s through `Cont.frame` and routing
  frame exit through `storeK` — deliberately scoped to the next
  machine slice rather than rushed; the three pins keep it red and
  visible.)
- Pinned-by: differential
- Cases: multi-assign/call-write-back/effects-suppressed, multi-assign/call-write-back/panic-identity, multi-assign/call-write-back/nil-field-store
- Discovered: 2026-08-06 (channels-arc-s1 delta review D3, generalized
  by the verifier: pre-existing on main, NOT channel-specific)

Spec §Assignments: "Second, the assignments are carried out in
left-to-right order", with the spec's own example making an earlier
store observable before a later target's panic (`x[1], x[3] = 4, 5 //
set x[1] = 4, then panic setting x[3] = 5`). The machine's generic
multi-assign apply (`locsOf` + `storeMany` after all target addresses)
stores all-or-nothing: `v, *nilp = 7, 9` recovered leaves `v == 0`
where Go leaves 7. It ALSO fires the outer address check of an
index/field target at ADDRESS-evaluation time where gc defers it to
the store (phase 2): `xs[0], p.b = 3, true` with nil `p` loses the
`xs[0]` store (go 1150, ours 1000 — multi-assign/field-nil-store-time).
The receive-path instances are BUG-029 (phase collapse in the delivery
frames — the D3 store-then-next fix traded one collapse for the other;
this entry's earlier claim that the receive instance "IS fixed" was
WRONG in both directions: over-claimed granularity for map-element
targets, BUG-030, and the fix itself regressed phase 1) and BUG-030.
This entry tracks the GENERAL path (`applyStmtOpCore .assignMany`,
frame-exit `storeMany`).

## BUG-026 — BUG-023's statement-level receive flag misses for-init/for-cond/else-if/switch-case positions (regression vs the deleted binary pre-bind)

- Status: fixed (2026-08-06, delta response: the per-statement sweep —
  and its false justifying comment — were deleted; the flag is now
  FUNCTION-scoped (`fnHasRecv`, set at emitFuncDecl / emitFuncLit /
  synthesizePkgInit from a body scan that stops at nested literals).
  For-conditions re-evaluate their condPre per iteration, and the
  coarser scope covers every statement-emission path — including ones
  added later — by construction. All four regression pins plus the
  original five flip green. CLAIM CORRECTED at the convergence round:
  the original scope argument said over-hoisting `len`/`cap` is
  unobservable — TRUE of the builtin, FALSE of its OPERAND, whose panic
  the hoist drags ahead of spec-unordered panics to its left; BUG-032
  restricts the hoist to panic-free operands and fails closed on the
  rest.)
- Pinned-by: differential
- Cases: channels/recv-order/for-init, channels/recv-order/for-cond, channels/recv-order/else-if, channels/recv-order/switch-case
- Discovered: 2026-08-06 (channels-arc-s1 delta review D2, verified
  critical: silent wrong answers vs base in four positions)

The BUG-023 fix set its receive flag only in `emitStmtList`, but
for-init/for-cond (condPre), else-if chains, and switch case
expressions are emitted OUTSIDE that path — `len(ch)` stays inline
there while the receive hoists, reading post-receive state; the deleted
binary pre-bind had covered the binary shapes among these. The fix's
justifying comment ("for-loop conditions are hoist-forbidden") was
FALSE — `hoistForbidden` guards only short-circuit RHS. Fix: a
position-independent flag (receive anywhere in the enclosing function
body, nested func literals scanned separately). The scope argument's
"over-hoisting is unobservable" clause was itself FALSE for panicking
operands — see BUG-032 for the correction (panic-free operands only;
fail closed otherwise).

## BUG-027 — $deferClose<N> collides across functions (liftSeq resets per function): whole-package error

- Status: fixed (2026-08-06, delta response: the closer is qualified by
  the enclosing function name like every lifted literal —
  `<fn>$deferClose<N>`; the two-function pin and its unrelated-subject
  companion flip green, and the original single-site pin stays green.)
- Pinned-by: differential
- Cases: channels/defer-close-two/first, channels/defer-close-two/second, channels/defer-close-two/unrelated
- Discovered: 2026-08-06 (channels-arc-s1 delta review D1)

The S6 closer is named `"$deferClose" + liftSeq` UNQUALIFIED, while
every other lifted function is qualified by the enclosing function
(`$lit` path); `liftSeq` resets per function, so two functions each
containing `defer close(ch)` mint two `$deferClose0` entries and the
decoder rejects the whole package (`duplicate function id` — status
`error`, unrelated functions unrunnable, misclassified in the ledger as
a machine gap). The blast-radius class BUG-024 just fixed, reintroduced
by the S6 fix. Fix: qualify with the enclosing function name.

## BUG-028 — map-element receive targets pre-bind a panicking non-call key BEFORE the communication (gc drains first)

- Status: fixed (2026-08-06, delta response: base and key are emitted
  INLINE into the post-receive map-assign — calls in them still
  auto-hoist pre-receive via A-normal form and len(ch) keys still hoist
  via the fnHasRecv flag (both spec-ordered), while panicking non-call
  operands now fire post-receive, matching gc's receive-first point and
  the sibling pointer/slice target arm.)
- Pinned-by: differential
- Cases: channels/recv-map-elem/key-panic-drains
- Discovered: 2026-08-06 (channels-arc-s1 delta review D5)

The S4 lowering hoists the map base and key ahead of the chan-recv
statement, so a key whose evaluation panics (a non-call operand — an
out-of-range index, a nil deref) fires BEFORE the receive; gc receives
first and drains. Spec leaves a non-call index operand's order against
a receive UNSPECIFIED (only calls/receives/binary-logical ops are
lexically ordered), so this is inside the spec envelope but outside
gc's realized point — and inconsistent with the sibling pointer/slice
target arm, which BUG-022's fix moved to communication-first. Fix: emit
base/key INLINE into the post-receive map-assign (calls still auto-
hoist pre-receive via A-normal form; `len(ch)` keys still hoist via the
receive flag), aligning both target kinds with gc.

## BUG-022 — chan-recv statement inverts spec §Assignments' phases: target-address panics fire BEFORE the communication

- Status: fixed (2026-08-06, audit response: the receive statement now
  mirrors the select path — `ChanStOp.recv` carries its target
  expressions, `applyChanOp` performs the COMMUNICATION first
  (block/panic/dequeue) and delivers through the existing `selectRecvK`
  target-evaluation frames with an empty body, so target-address
  panics are phase-2 events after the receive; the target-first
  `chanStK` shift machinery (`ntargets`, target checks) was removed
  outright, not left dead. Spec-ordered `len(ch)` reads inside targets
  stay pre-receive via BUG-023's uniform frontend hoist. Relation,
  stepFn, WF lemmas, and correspondence proofs moved in lockstep.
  Delta review D3 then closed the remaining phase-2 half for this path:
  stores are per-target LEFT-TO-RIGHT (an earlier target's store is
  observable before a later target's panic); the GENERAL multi-assign
  path still stores all-or-nothing — BUG-025.)
- Pinned-by: differential
- Cases: channels/recv-edge/nil-deref-target-drains, channels/recv-edge/oob-target-drains, channels/recv-edge/bad-target-blocks
- Discovered: 2026-08-06 (channels-arc-s1 pre-merge audit S1+S7,
  independently verified; probes reproduced against go1.26.5)

`chanPlan` orders the receive STATEMENT as target-addresses-first and
`chanStK`/`applyChanOp` panic on a failing target (nil deref, index out
of range) before the channel operand is evaluated. Go's §Assignments is
two-phase: phase 1 evaluates LHS index/indirection OPERANDS and the RHS
(the receive); phase 2 performs the stores — where those panics live.
Consequences, all pinned: the channel is NOT drained when the store
panic is recovered (Go consumes the value); and a bad target turns a
BLOCKING receive (deadlock in the single-goroutine slice) into a panic.
The select-clause path (`commitClause` → `selectRecvK`) is correct —
communication before target evaluation — only the plain statement form
is inverted. Fix: reorder the statement form to the select shape
(receive first, then targets, then stores), with the frontend's ordered
pre-binds keeping spec-ordered `len(ch)` reads inside targets ahead of
the receive.

## BUG-023 — hoisted receive reorders ahead of inline len(ch) in every operand list except binary operands

- Status: fixed (2026-08-06, audit response, REVISED at the delta
  review: the first fix's per-statement sweep missed statement-emission
  paths — BUG-026 — so the mechanism is now the FUNCTION-scoped
  `fnHasRecv` flag driving `emitBuiltin`'s `len`/`cap` hoist; see
  BUG-026 for the scope argument. Under `hoistForbidden` (short-circuit
  RHS — the only such position) len/cap stay inline, which is correct
  because a receive there refuses outright.)
- Pinned-by: differential
- Cases: channels/recv-order/call-arg, channels/recv-order/return-list, channels/recv-order/composite-lit, channels/recv-order/multi-assign
- Discovered: 2026-08-06 (channels-arc-s1 pre-merge audit S2+S9,
  independently verified; go oracle 205 in all five positions)

A receive lowers to a hoisted statement placed before the enclosing
statement, so any inline (non-hoisted) spec-ordered evaluation lexically
LEFT of it — `len(ch)` is the observable one; ordinary calls hoist and
keep their order — reads POST-receive channel state. Spec §Order of
evaluation mandates lexical left-to-right for "all function calls,
method calls, receive operations" in expression, assignment, and return
statements. Slice 1 pre-bound only `emitBinary`'s left operand; call
arguments, composite-literal elements, multi-assign RHS lists, and
return lists still reorder (silent wrong answers vs the oracle). Fix:
one uniform mechanism — hoist `len`/`cap` operands whenever the emitted
statement's operand sweep contains a receive — replacing the
binary-only pre-bind.

## BUG-024 — bare `<-ch` statement emits a wire node the decoder rejects: whole-program error instead of receive-and-discard

- Status: fixed (2026-08-06, audit response: `emitStmt`'s ExprStmt arm
  intercepts `<-ch` / `(<-ch)` ahead of the generic path and emits the
  ZERO-target chan-recv statement directly — receive-and-discard, no
  residual ident, no whole-package decode abort.)
- Pinned-by: differential
- Cases: channels/recv-stmt
- Discovered: 2026-08-06 (channels-arc-s1 pre-merge audit S3+S8,
  independently verified)

`emitUnaryExpr` routes `<-` to the expression-position hoist, which
leaves a residual `$c` ident that the ExprStmt fallback wraps as
`{"stmt":"expr"}`; `NativeToIR` rejects it ("expression statement is
not a call") with status `error` — aborting the WHOLE package's
lowering (every unrelated function dies too), where the base commit
per-decl-quarantined the same source. Spec §Expression statements
lists `<-ch` and `(<-ch)` explicitly; `<-done` is the idiomatic
synchronization barrier (deps/raft/node.go:340). Fix: an ExprStmt arm
emitting the zero-target chan-recv statement directly.

## BUG-021 — append-spill capacity envelope is TOO NARROW on the oracle toolchain (gc realizes points outside growth+[0,8))

- Status: fixed (2026-08-06, arc-final audit response F2 — envelope
  widened to [newLen, max(32, 2·growth)], the containment argument on
  `appendSpillUpper` (Ops.lean): the lower end is the spec floor gc
  realizes, the upper end covers both element-size-dependent gc
  mechanisms (32-byte stack buffer ≤ 32 elements; size-class step ratio
  < 1.5 < 2 above 32 bytes). The choice is offset so the empty stream
  keeps the growth-formula point (strict lane unchanged — zero baseline
  drift outside the three pins); the site bound consumed from the
  stream is now the shape-dependent `appendSpillWidth`, absorbed by the
  shared applyStmtOp (relation and stepFn move in lockstep) and the
  obliviousness metatheory; enumerator width metadata updated
  (full-slice-cap-zero width 32, eval pins re-pinned to the 32-member
  set with the offset-preserved cap-7 panic member).)
- Pinned-by: differential
- Cases: slices/append-spill-stack-buffer, slices/append-spill-below-formula, slices/append-spill-size-class
- Discovered: 2026-08-06 (arc-final audit F2 — probe sweep over element
  sizes/shapes on go1.26.5, the differential oracle's own toolchain)

The append-spill Choices site models `newCap = growthFormula(oldCap,
newLen) + extra`, `extra ∈ [0,8)` — but gc's realized capacity is
element-size dependent (runtime/slice.go re-derives it from the
size-class-rounded allocation, `roundupsize`; cmd/compile additionally
stack-buffers small non-escaping appends in a 32-byte buffer), and the
formula has no element-size parameter. Probe-measured escapes, all three
directions: cap 32 for a byte append at oldCap 3 → newLen 4 (stack
buffer; window was [6,14)); cap 2 for nil []string → len 2 (BELOW the
formula's max(4,newLen)=4 — the spec's only floor is newLen); cap 224
for []int oldCap 100 → newLen 101 (size-class rounding; window was
[200,208)). This is the nondeterminism doctrine's too-narrow,
SOUNDNESS-relevant direction: ∀-stream theorems do not transfer while a
real behavior sits outside the envelope (no shipped theorem walks the
spill path yet — StmtOps.lean records it as owed — so the hole is
latent, not realized). The three membership pins fire the lane's
too-narrow alarm today. Fix shape: widen the envelope to
[newLen, max(32, 2·growthFormula)] — lower end the spec floor, upper
end covering both gc mechanisms (32-byte stack buffer at element size
≥ 1; size-class step ratio < 1.5 for allocations over 32 bytes) — with
the doctrine's envelope statement updated in the same commit. The
version-tracking pin (`full-slice-cap-zero`, samples=1) sat INSIDE the
old window for its one ([]int, oldCap 0, newLen 1) point, which is why
the lane never fired: it version-tracks one triple, not the site's
envelope; these three pins cover the escaping regimes.

## BUG-020 — conversions to UNNAMED composite targets (pointer/slice/map/func) are refused (missing kernel arms)

- Status: fixed (2026-08-06, arc-final audit response F10 —
  identical-underlying pass-through arms for pointer/slice/map/func
  targets (plus typed nil for each); go/types owns the
  identical-underlying check, the machine passes the unchanged runtime
  representation through and every other value shape stays at the
  fail-closed catch-all, so string→[]rune/[]byte remain refused and the
  five untriaged strings/*-conversion reds are unchanged. The
  tag-CHANGING pointer shape stays fail-closed downstream at the
  struct-tag check (structs/tag-pointer-conversion red, now stuck at
  field access rather than refused at the conversion). The mis-scoped
  "alias one cell under two tags" rationale at the struct arm was
  corrected under F20. DELTA-REVIEW D3 (2026-08-06): the first cut's
  slice/map arms returned the RAW machine nil for a nil operand, so
  []byte(nil)/[]int(nil)/map[K]V(nil) still failed at first use
  (fail-closed) — fixed to produce the machine's own nil-slice/nil-map
  representation (the typed-nil-literal shapes), pinned red-first by
  the slice-nil/map-nil cases; pointer/func targets were correct from
  the start, raw nil IS their representation.)
- Pinned-by: differential
- Cases: structs/unnamed-conversion-targets/pointer, structs/unnamed-conversion-targets/pointer-nil, structs/unnamed-conversion-targets/slice, structs/unnamed-conversion-targets/slice-to-defined, structs/unnamed-conversion-targets/map, structs/unnamed-conversion-targets/func, structs/unnamed-conversion-targets/func-from-defined, structs/unnamed-conversion-targets/slice-nil, structs/unnamed-conversion-targets/map-nil
- Discovered: 2026-08-06 (arc-final audit F10; pre-existing — the
  catch-all predates the general-coverage arc)

`convertValueToTyFuel` has arms for int/float/string/defined/struct/
interface targets only; a conversion whose target's RESOLVED shape is a
pointer, slice, map, or func falls into the catch-all `unsupported` —
including the spec's own canonical examples `(*Point)(p)`,
`(func() int)(x)`, `(*int)(nil)`, and BOTH directions through defined
types (`[]int(namedSlice)` and `uctInts(ys)` both resolve into the
missing arm). Fail-closed (never a wrong answer), but a refusal of
legal, idiomatic Go — `(*T)(nil)` occurs 12× in deps/raft. The five
untriaged `strings/*-conversion` reds (rune/string conversions) fail at
the SAME catch-all but need real conversion logic, not a retag — they
stay untriaged. NOTE the mis-scoped rationale at the struct arm
("pointer-to-struct conversions stay refused elsewhere: they ALIAS one
cell under two tags") — identity retags like `(*Cell)(&c)` alias
nothing; the true cause is that no target-kind arm exists. Fix shape:
identical-underlying retag arms for the four kinds (pass the runtime
value through; fail closed on shape mismatch), and correct the
rationale comment.

## BUG-019 — observation channel renders anonymous struct{} typeName as "struct{}" (reflect.Name() gives "")

- Status: fixed (2026-08-06, arc-final audit response F7 — the CLI
  renderer emits "" for the canonical anonymous-empty-struct key,
  matching reflect.Type.Name()'s non-defined-type contract; named empty
  structs keep their names, pinned by the ctl-named control. The
  interface-holding-anonymous-struct{} path is out of scope: the Go
  harness fails closed there by disposition, so no observation
  compares.)
- Pinned-by: differential
- Cases: structs/empty-struct-observation/direct, structs/empty-struct-observation/field, structs/empty-struct-observation/array
- Discovered: 2026-08-06 (arc-final audit F7; pre-existing — the old
  `unqualifiedTypeName` produced the same string)

`goValueJson` renders a struct's typeName as `TypeId.unqualified`, which
for the canonical anonymous empty struct is the literal internal key
"struct{}". The channel's stated contract is `reflect.Type.Name()`,
which is "" for ANY non-defined type — the Go harness renders "".
Fail-safe (a false RED, never a false green), but a live guardrail hole
in the area the arc extended (BUG-011 empty-struct assignability,
`Pair[struct{}]`): any case observing a bare struct{} fails on naming
alone. Fix shape: render "" for the canonical anonymous-empty-struct
key at the observation boundary (CLI renderer), both sides consistent;
named empty structs (defined types) keep their names.

## BUG-018 — a type declared INSIDE a generic function gets an un-parameterized TypeId

- Status: fixed (2026-08-06, arc-final audit response F3 —
  qualifiedTypeName parameterizes function-local TypeIds with the
  enclosing instantiation's rendered type arguments (the ordered targs
  threaded through the stencil work items), matching gc's
  reflect.Name() "box[int]" spelling; the duplicate-TypeId gate remains
  the collision boundary and still refuses two same-named locals at the
  same instantiation across functions — probe-verified. The
  two-instantiation shape now exports and runs;
  generics/local-type-argument stays red as M3's separate recorded
  refusal of the type-ARGUMENT direction.)
- Pinned-by: differential
- Cases: generics/local-type-in-generic/dynamic-name, generics/local-type-in-generic/assert-panic
- Discovered: 2026-08-06 (arc-final audit F3)

gc names a type declared inside a generic function with the enclosing
instantiation's type arguments (`reflect.Type.Name()` = "ltgBox[int]",
probe-verified go1.26.5). Local type decls in stenciled bodies bypass
mono.go's mangling boundary and mint the bare key `pkg.Name`: with ONE
instantiation the export succeeds and the observation channel and
interface-conversion panic text report the WRONG type name (the two
pinned differential reds — wrong answers on legal Go); with TWO
instantiations the name-only duplicate-TypeId gate refuses legal Go
with a misdiagnosis ("a function-local type collides with another
declaration" — there is ONE declaration at two instantiations;
`generics/local-type-two-instantiations`, a frontend-export red). The
mangled-key injectivity registry is never consulted on this path. Fix
shape: parameterize local-type TypeIds inside generic functions with
the enclosing instantiation's type arguments (the mechanism lifted func
literals already use), collision-checked at the one boundary.

## BUG-017 — mixed interface/non-interface comparison is unsupported (no wrap at comparison operands)

- Status: fixed (2026-08-06, arc-final audit response F4 — emitBinary
  boxes the non-interface operand of a mixed ==/!= into the interface
  side's type and carries the interface side as the GoCore operand
  type; emitSwitch does the same at interface-tagged case slots, incl.
  the reverse shape where the CASE value is the interface. The wrap
  no-ops on untyped nil, so `i == nil` lowerings are unchanged.)
- Pinned-by: differential
- Cases: interfaces/mixed-compare/eq-int-lit, interfaces/mixed-compare/eq-int-lit-reversed, interfaces/mixed-compare/neq-miss, interfaces/mixed-compare/switch-case, interfaces/mixed-compare/sentinel-error, interfaces/mixed-compare/sentinel-error-reversed, interfaces/mixed-compare/struct-both-orders
- Discovered: 2026-08-06 (arc-final audit F4; pre-existing — emitBinary
  is untouched by the general-coverage arc)

The spec's own bullet (§Comparison operators): "A value x of
non-interface type X and a value t of interface type T can be compared
if type X is comparable and X implements T." The interface-conversion
wrap (BUG-006's fix) is emitted at every assignable slot EXCEPT
comparison operands and switch-case slots, so the machine's equality
arms receive one box and one raw value and refuse — every mixed shape
fails closed (`i == 5`, both orders, `switch i { case 5: }`, the
sentinel-error idiom `err == ErrSentinel`). A whole spec bullet
including two dominant idioms, invisible to the corpus (zero mixed
comparisons existed — verified by a go/types scan). Fix shape: box the
non-interface operand at comparison and switch-case slots exactly like
every other slot (`wrapInterfaceConversion`), operand type = the
interface side.

## BUG-016 — untyped nil into a nilable slot stays a RAW nil everywhere except map-literal elements

- Status: fixed (2026-08-06, arc-final audit response F6 — ONE
  mechanism: `wrapInterfaceConversion`, the shared normalizer already
  called at every assignable-context emission site, now types an
  untyped nil at direct slice/map/pointer targets; the M1 map-literal
  special case folded into it, and the spread-call path (`f(nil...)`)
  routed through the same wrap. Func-typed, defined-typed, and
  interface slots keep their prior disposition — BUG-014's boundary.)
- Pinned-by: differential
- Cases: functions/untyped-nil-sinks/struct-lit-field, functions/untyped-nil-sinks/struct-lit-append, functions/untyped-nil-sinks/struct-lit-map-field, functions/untyped-nil-sinks/slice-lit-elem, functions/untyped-nil-sinks/array-lit-elem, functions/untyped-nil-sinks/return-nil, functions/untyped-nil-sinks/call-arg, functions/untyped-nil-sinks/plain-assign, functions/untyped-nil-sinks/variadic-spread, functions/untyped-nil-sinks/nested-map-value
- Discovered: 2026-08-06 (arc-final audit F6, widening the disclosure at
  the generics design note §"local types" — the audit's verifier showed
  the class is every assignability sink, not just composite literals)

The frontend types an untyped-nil map-literal VALUE to the element type
(the audit-response M1 fix) but nothing else: struct-literal fields,
slice/array-literal elements, `return nil` from a []T function, call
arguments, plain assignment, and variadic spread all emit a bare
`{"expr":"nil"}`, which the machine stores as a raw `.nil` — the first
`len`/`append`/index on it goes unsupported/stuck. Legal, ubiquitous Go
(`return nil` is verbatim etcd-raft's `log_unstable.nextEntries`, on
the north star's critical path). Fail-closed in direction (visible red,
never a wrong value — probed across the divergence surface). Distinct
from BUG-014 (DEFINED slice/map element types, blocked on the machine's
nil-literal arm): these sinks are plain slice/map/pointer slots the
machine already supports typed nils for; the frontend just never types
them. Fix shape: ONE mechanism — type the untyped nil to the target at
every assignable-context emission site (the sites that already call the
interface wrap), for slice/map/pointer targets; `func`-typed and
defined-typed slots keep their current disposition (BUG-014's
boundary).

## BUG-015 — recover() inside a PROMOTED method reached via a synthesized wrapper returns nil (wrapper frame breaks the recover walk)

- Status: fixed (2026-08-06, arc-final audit response F1 — the faithful
  machine-level fix, gc's own rule: synthesized wrappers are marked on
  the wire ("wrapper": true, a declared schema addition emitted only by
  synthesizeWrapper), `Func.wrapper` threads the flag into the frame
  continuation (`Cont.frame` gains a trailing `wrapper` marker,
  defaulted false so every pre-existing construction is unchanged), and
  the recover walk — and ONLY it — treats wrapper frames as transparent
  (`recoverThroughWrappers`; "exactly one non-wrapper frame between
  gopanic and gorecover"). Full lockstep: Step rules and stepFn carry
  the flag through frame exit/drain/panic paths, StateWf gains
  wrapper-aware recoverResult lemmas, MachineSound absorbed the arity
  change, and the WP frame laws generalize over the marker; designated
  statements untouched. All four divergence pins flip green; the four
  controls — direct dispatch, concrete promoted call, method value,
  chain-JOINING through the same wrapper — hold.)
- Pinned-by: differential
- Cases: interfaces/recover-promoted-wrapper/silent-value-embed, interfaces/recover-promoted-wrapper/status-value-embed, interfaces/recover-promoted-wrapper/silent-pointer-embed, interfaces/recover-promoted-wrapper/silent-iface-embed
- Discovered: 2026-08-06 (arc-final audit F1 — found by reading the
  slice-2 wrapper design against the pre-existing defer/recover
  machinery; invisible to the whole corpus)

Slice 2 lowers dynamic dispatch of a PROMOTED method through a
synthesized forwarding wrapper — an ordinary GoCore call frame. gc
emits the same wrappers but marks them `abi.FuncIDWrapper`, and the
runtime's recover walk skips them (runtime/panic.go, gorecover: "there
must be exactly one non-wrapper frame between gopanic and gorecover").
`recoverResult` requires the deferred function's frame DIRECTLY above
the suspended-chain marker, so the wrapper's extra frame makes
`recover()` inside the promoted method return nil: the panic is NOT
recovered where Go recovers it — a SILENT value divergence (both sides
status ok, values differ) and a status-level flip, across all three
wrapper paths (value embed, embedded pointer, embedded interface
field). Introduced by this arc (before slice 2 the same shape refused
via the BUG-007 satisfaction fail-closure). Chain-JOINING through the
same wrapper is correct (pinned as a control). Fix shape, faithful to
gc: mark synthesized wrappers on the wire, thread the marker into the
frame continuation, and make the recover walk (and ONLY it) treat
wrapper frames as transparent.

## BUG-014 — untyped nil at defined-slice/defined-map map-literal elements stays a raw nil (stuck at len/ops)

- Status: open
- Pinned-by: differential
- Cases: maps/nil-literal-values/defined-slice-element, maps/nil-literal-values/defined-map-element
- Discovered: 2026-08-05 (delta-review R2 of the generics-branch audit
  response — PRE-EXISTING on the merge base, verified by the reviewer;
  not a regression of this branch)

A map literal whose element type is a DEFINED slice/map type
(`type S []int; map[string]S{"s": nil}`) stores the untyped-nil value as
a RAW `.nil`: the frontend cannot emit a typed nil for it because the
machine's nil-literal arm rejects `.defined` targets ("nil literal for
non-nilable type GoLean.GoCore.Ty.defined …"), and the raw nil then goes
unsupported at use (`len for non-array/slice/map value GoValue.nil`).
Legal, ordinary Go; wrongly-stuck on a supported construct — a fidelity
bug, fail-closed in direction (visible red, never a wrong value).

Fix shape (NOT in the generics slice, deliberately — it is a GoCore
change, outside that slice's charter): the machine's nil-literal arm
resolves `.defined` targets through their underlying to decide
nilability (and the nil-comparison/len paths accept the resulting typed
nil), OR a defined-type-aware typed-nil representation. When it lands,
the frontend's map-literal rewrite (emitMapLit, audit-response M1
restriction) can extend to defined slice/map elements and the two pinned
cases flip.

## BUG-013 — CLI struct-observation typeName truncates mangled generic TypeIds

- Status: fixed
- Closed: 2026-08-05 (generics slice, branch `general-coverage-generics`,
  coordinator-authorized follow-up to the slice's stop-and-report)
- Fix: the private duplicate in `GoLean/CLI.lean` is DELETED — both use
  sites (struct observation `typeName`, `fieldAddr` rendering) now call
  `TypeId.unqualified` directly, leaving exactly ONE copy of the
  stripping logic in the codebase (`GoCore/Value.lean`; grep confirms no
  other `splitOn "."` renderer). The pinned case
  `generics/instantiated-type-assert/name` flips FAIL/differential →
  PASS; nothing else moves (full-run re-pin in the fix commit).
- Original status: open
- Pinned-by: differential
- Cases: generics/instantiated-type-assert/name
- Discovered: 2026-08-05 (generics slice G3 — flagged as latent in the G1
  commit, became differentially observable the moment instantiated
  struct values entered observations)

`GoLean/CLI.lean` has a private `unqualifiedTypeName` (used for the
struct observation `typeName` and `fieldAddr` rendering) that duplicates
the OLD `TypeId.unqualified` logic: `splitOn "." |>.getLast!`. For a
mangled instantiation key with a package-qualified type ARGUMENT —
`main.assertBox[main.assertInner]` — it renders `"assertInner]"` instead
of the `reflect.Type.Name()` contract's `"assertBox[main.assertInner]"`.
The pinned case observes exactly this through the INNER struct value of
an interface observation (the interface's `dynamic` name, rendered by
the FIXED `Ty.dynamicName`/`TypeId.unqualified` path in
`GoLean/GoCore/Value.lean`, matches Go verbatim in the same output —
the two renderers disagree inside one JSON object, the same
contract-inconsistency class as pre-merge-audit-2026-07-31 finding 12).

Fix shape (one line): `unqualifiedTypeName` delegates to
`TypeId.unqualified`. NOT fixed in the generics slice by its charter
constraint — the slice's sanctioned Lean-side change is exactly the
`Value.lean` fix, and anything further is a stop-and-report item
(reported in the slice hand-back; the fix needs its own reviewed
commit). Rendering-only; keys with at most one `.` and no brackets —
every pre-generics key — render identically in both.

## BUG-012 — a bare call statement discarding results goes stuck ("extra GoCore assignment value")

- Status: fixed (2026-08-06, arc-final audit response F11 — the decoder
  lowers a bare value-returning call with typed discard temps per
  result, decodeAssign's own blank-target mechanism driven by the call
  node's `resultTypes`; covers plain calls, method chaining, func-value
  calls, multi-result callees, and bare calls inside `init()` through
  `$pkginit`. The audit re-priced this from "deferred to its own small
  slice" after its novel-program sweep found it the single most
  frequent failure — 16 of 153 probes.)
- Pinned-by: differential
- Cases: functions/bare-call-discard-result, functions/bare-call-chain/chain, functions/bare-call-chain/helper, functions/bare-call-chain/func-value, functions/bare-call-chain/multi-result, init/bare-call-in-init
- Discovered: 2026-08-05 (init-slice audit, C5 — the multi-file verifier
  probe's init() bodies used bare `mark(x)` calls and hit it; the shape
  is pre-existing and UNRELATED to init: the diff under audit does not
  touch it)

A call statement with NO targets to a function that RETURNS values —
`f()` for `func f() int` — lowers to a targetless GoCore `call`, and the
machine's frame-exit write-back (`storeMany` on `targets=[]` vs one
result value) goes `.stuck "extra GoCore assignment value"`
(`Machine.lean`, `storeMany`'s arity arm). Legal, ubiquitous Go
(discarding a return value needs no `_ =`); wrongly-stuck on a supported
construct, hence a fidelity bug, though fail-closed in direction (a
visible red, never a wrong value). Until now no corpus case exercised
the shape — every bare call in the corpus called a void function.
Fix shape (NOT in the init slice, deliberately): either the frontend
lowers a result-discarding bare call with blank targets per result, or
the machine's frame exit tolerates `targets=[]` with nonempty results
(store nothing); either way the guardrail case flips and the pin moves
to the fix commit. (Resolved via the frontend/decoder path — the
machine's frame exit is untouched.)

## BUG-001 — struct-field / array-element WRITE lowers an address base as a value

- Status: fixed
- Closed: 2026-07-25 (W4 slice 1, branch `seq-coverage-scoping`)
- Fix: exactly where the 2026-07-19 diagnosis pointed — `emitAddressOf` in
  `tools/nativefrontend/emit.go` now emits ADDRESS chains (`a.b.c` →
  `fieldAddr(fieldAddr(ref a))`; pointer bases used as-is per auto-deref;
  array `index-addr` takes the array's address, slices stay by-value).
  GoCore needed zero changes, as predicted. All three pinned cases PASS
  (structs/copy-value, structs/pointer-field, arrays/arrays) plus 33 more
  in the same class (36 total, re-pin 2026-07-25). Fixing it exposed and
  fixed a second bug the fail-closed stuck had been masking:
  read-modify-write lvalues containing calls evaluated their address twice
  (`structs/selector-eval-once` — a WRONG ANSWER once reachable).
- Original status: open
- Pinned-by: differential
- Cases: structs/copy-value, structs/pointer-field, arrays/arrays
- Discovered: 2026-07-19 (directional audit, finding F1)

Writing through a struct field or array index — `b.n = 7`, `a[1] = …`,
`p.n = …` — fails closed at `lean-observation` with "expected address value, got
GoLean.GoValue.struct/array". Root cause is in the **frontend lowering**, not
GoCore: `tools/nativefrontend/emit.go` `fieldBase` (~736) and `emitAddressOf`'s
`SelectorExpr` case (~814) lower the base via a value-read (`.var`) where the
*address* path needs an address base (`.ref`/`.fieldAddr`). GoCore's
`valueAsLoc` correctly rejects the struct/array value and fails closed — so this
is a visible stuck, not a silent wrong answer, but the interpreter cannot perform
one of the most common Go mutations. On the north-star path (raft mutates struct
fields pervasively). GoCore already has the right primitives (`fieldAddr`,
`indexAddr`); the fix is in `emit.go`. Also: `docs/native-frontend-goal.md`
overclaims "field/index access" as working (true for reads, false for writes) —
correct it when the lowering is fixed. Tracked in `TODO.md` (F1).

## BUG-010 — TypeId keys are qualified by package NAME, not import PATH

- Status: open
- Pinned-by: differential
- Cases: interfaces/imported-package-name-collision
- Discovered: 2026-07-31 (final pre-merge adversarial audit of
  `quorum-pilot`, findings 4/7)

`qualifiedTypeName` (`tools/nativefrontend/emit.go`) builds every wire
`TypeId` from `obj.Pkg().Name()`. Go keys type identity on the import
PATH, so two packages that merely SHARE A NAME — `html/template` and
`text/template`, `math/rand` and `crypto/rand`, the many generated
`config`/`types`/`v1` packages — produced the SAME key, and `Ty.eqb`'s
`.defined a, .defined b => a == b` arm then called two unrelated Go types
identical. A single `package main` importing both stdlib templates was
enough:

    var p *ht.Template; var a any = p; _, ok := a.(*tt.Template)

Go answers `false`; the machine answered `true`. The panicking form is
worse — Go aborts with `interface conversion: interface {} is
*template.Template, not *template.Template (types from different
packages)`, its runtime message literally naming this class, and the
machine returned a value. No multi-package lowering was needed: an
imported named type needs no `TypeDef` to reach GoCore as `.defined`.

**v1 fail-closure (2026-07-31)**: the frontend COLLISION-CHECKS at the
one boundary constructor that builds the key
(`emitter.checkPackageNameCollisions`) and refuses the export when two
distinct import paths would share a qualifier — CLAUDE.md's "every
mangling strip happens at exactly one boundary constructor and
collision-checks", which `TypeId` (unlike `FuncId`) did not honour. The
pinned case is now an honest `frontend-export` refusal naming both paths.

The REAL fix is widening the key to `obj.Pkg().Path()`. It is deferred,
not forgotten: it re-keys every `TypeId` — every pinned lowering, every
`main.T(v)` panic rendering, every `TypeId.unqualified` observation — so
it belongs with the multi-package slice, scoped in
`docs/2026-07-30_quorum-extern-policy.md`. Escalate the moment
multi-package lowering is claimed.

## BUG-009 — an imported named type's METHOD SET is not on the wire, so interface satisfaction is UNKNOWN

- Status: fixed (2026-08-05, general-coverage slice 2 stage 6 — design
  note D5: for every imported concrete named type whose EXPORTED method
  set is fully emittable, the frontend emits an existence-marker TypeDef
  (`kind: unsupported` — structural use keeps failing closed) plus
  declaration-only method STUBS carrying the real signatures
  (`importedTypeDecls`/`importedMethodStubs`; NativeToIR decodes them as
  Funcs with fail-closed bodies), so `satisfiesMethodSig` answers from
  real information and a CALL still refuses. Fail-closed residue, both
  deliberate: a type with any un-emittable exported signature is skipped
  whole (satisfaction keeps refusing via `dynamicMethodSetRecorded`), and
  an UNEXPORTED requirement against a marker type refuses
  (`dynamicIsImportedMarker` guard in `firstUnsatisfiedMethod?` —
  cross-package unexported method identity is not expressible on the
  name-keyed wire). Both pinned cases green (`*strings.Builder`
  implements `fmt.Stringer`: comma-ok true, panic-form completes).)
- Pinned-by: differential
- Cases: interfaces/assert-imported-method-set/comma-ok, interfaces/assert-imported-method-set/panic-form
- Discovered: 2026-07-31 (final pre-merge adversarial audit of
  `quorum-pilot`, finding 8)

BUG-008's sibling in the other polarity, and the exact mirror of the
interim audit's finding 0 (vacuously TRUE satisfaction) — this one was
vacuously FALSE. `firstUnsatisfiedMethod?` derives satisfaction from
`state.methods`, which the frontend populates only for the ANALYZED
package. For an imported/stdlib named type the method table is empty and
no `TypeDef` exists, so `satisfiesMethodSig` answered `false` and
`dynamicHasEmbeddedFields` answered `false`, and the function returned a
DEFINITE `some name` — an answer derived from no information:

    var p *strings.Builder; var x any = p; _, ok := x.(fmt.Stringer)

`*strings.Builder` really does implement `fmt.Stringer`. Go gives
`ok == true`; the machine gave `false`. The panicking form `x.(fmt.Stringer)`
FABRICATED `interface conversion: *strings.Builder is not fmt.Stringer:
missing method String` on a program Go runs to completion. The sibling
function `tyUncomparable` was made three-valued on this same branch for
exactly this hazard ("Callers must fail CLOSED on `none`"); satisfaction
was not.

**Fail-closure (2026-07-31)**: `dynamicMethodSetRecorded` distinguishes
"the wire KNOWS this type, so an absent method really is absent" from
"this type was never declared, so the method set is UNKNOWN". Soundness
of the first half rests on a Go rule: methods can only be declared in
their type's own package, and the frontend emits a `TypeDef` for every
named type the analyzed package declares — so for a known `.defined`
name the recorded method set is COMPLETE. Non-`.defined` dynamic types
(basics, slices, maps, `**T`) can carry no methods in Go at all, so an
empty method set is correct for them; `*T` is known exactly when `T` is.
Only the definite-FALSE answer is guarded — finding a matching recorded
method is still sound.

Residual, recorded: a method declared for a package-local type in a
`_test.go` file is excluded by the frontend's `nonTestGoFile` filter,
which would leave a KNOWN type with an incomplete method set. No corpus
case has one (cases are single-file `main.go`), and the differential's
own oracle would not compile such a subject either.

The real fix is the same one BUG-008 names: emit declarations for
imported named types. The mechanism already exists for imported
INTERFACES (the interface-declaration pass); extending it to non-interface
named types is the owed sub-slice, and it closes both bugs at once.

## BUG-008 — imported named types have no declaration on the wire, so their comparability is UNKNOWN

- Status: open
- Pinned-by: differential
- Cases: maps/imported-named-key-unhashable
- Discovered: 2026-07-31 (pre-merge adversarial audit of the interfaces
  campaign, finding 11)

The frontend emits `TypeDef`s only for types declared in the analyzed
package, but it emits `{"kind":"named"}` for EVERY `*types.Named` — so any
imported/stdlib named type reaches GoCore as a `.defined` name the type
environment does not know. `tyUncomparable` used to answer `false`
("comparable") for such a name, which skipped Go's hash panic:
`m[sort.IntSlice{1,2}] = 1` inserted and returned len 1 where real Go
panics `runtime error: hash of unhashable type sort.IntSlice`. A silent
wrong answer on a program the tool accepted end to end.

`tyUncomparable` is now three-valued (`none` = unknown) and the map-key
hash precheck fails CLOSED on `none`, so the pinned case is an honest
`unsupported` instead. Neighbouring paths (default value, conversion,
same-type equality) already failed closed on unknown defined types; this
closes the boxing/hash hole. **Correction 2026-07-31 (final pre-merge
audit, finding 8): that enumeration was not exhaustive.** Interface
SATISFACTION — the path this branch added — did NOT fail closed on an
unknown defined type; it answered a definite `false`. Tracked separately
as BUG-009, closed the same way, and both are fixed for good by the same
owed sub-slice below. The real fix is emitting declarations for
imported named types — which is also what the interface-declaration pass
(finding 0's fix) now does for imported INTERFACES, so the mechanism
exists; extending it to imported non-interface named types is the owed
sub-slice.

## BUG-007 — method PROMOTION through embedded fields is unmodeled

- Status: fixed (2026-08-05, general-coverage slice 2 — the recorded fix
  direction landed: promotion is FLATTENED at emission
  (docs/2026-08-05_embedding-interfaces-design.md D1). Field promotion:
  Selection.Index() paths become field-get/deref chains (reads) and
  field-addr chains (writes/addresses). Method promotion: call sites and
  method values adjust the receiver through the hop path AT THAT MOMENT
  (evaluation order and capture moment pinned by
  embedding/promoted-nil-embedded-pointer/before-args and
  embedding/promoted-method-value/{snapshot,live}); dynamic dispatch and
  satisfaction go through synthesized forwarding WRAPPERS
  (synthesizePromotionWrappers, one per promoted method-set entry,
  receiver T or *T per Go's method-set asymmetry — mirroring gc's
  wrappers), so GoCore's method table stays flat and COMPLETE. The
  machine's over-approximate embedded-fields satisfaction fail-closure is
  retired under that wire contract (D2), with the definite-FALSE polarity
  pinned by embedding/promoted-ambiguous-not-satisfied and
  embedding/promoted-pointer-receiver-method-set/value-box.)
- Pinned-by: differential
- Cases: interfaces/embedded-interface-shadowing/interface-field-dispatch, interfaces/embedded-interface-shadowing/interface-field-nil-panic, interfaces/embedded-interface-shadowing/nil-pointer-method-promoted, interfaces/embedded-interface-shadowing/pointer-method-promoted, interfaces/error-idioms/promoted-method, interfaces/promoted-method-assert-ok, methods/embedded-interface-satisfaction, embedding/deep-promoted-method, embedding/embedded-method-promote, embedding/promoted-ambiguous-not-satisfied, embedding/promoted-method-value/live, embedding/promoted-method-value/snapshot, embedding/promoted-nil-embedded-pointer/before-args, embedding/promoted-nil-embedded-pointer/call, embedding/promoted-nil-embedded-pointer/nil-panic, embedding/promoted-pointer-receiver-method-set/pointer-box, embedding/promoted-pointer-receiver-method-set/value-box
- Discovered: 2026-07-30 (interfaces campaign — these cases were
  frontend-blocked before the campaign; the wrap/dispatch landing made
  the gap VISIBLE at the machine: `dynamic type main.T has no method m`)

Go promotes an embedded field's methods (and its interface's method
set) to the embedding struct, with receiver adjustment through the
field path — depth-first, shadowing by depth, ambiguity = compile
error. The machine's method table has only DECLARED methods, so a
promoted call finds no entry and dispatch fails stuck.

**Correction 2026-07-31 (pre-merge audit, finding 5): this entry used to
claim the gap was "fail-closed — never a wrong answer". That was FALSE on
the ASSERT path.** All eight originally pinned cases are dispatch/call
shapes; on `_, ok := any(Outer{…}).(I)` where `I` is satisfied via a
promoted method, the missing table entry made the method-SET check answer
`false`, and the comma-ok assert turned that into a silently WRONG boolean
(Go: true) with `status: ok` — no stuck, no unsupported. The machine now
fails CLOSED instead: a satisfaction check that would answer "unsatisfied"
on a struct (or pointer-to-struct) with EMBEDDED fields raises
`unsupported` naming the method and this bug, since promotion could supply
it. Detecting promotion soundly is the real fix, not the fail-closure;
until then `interfaces/promoted-method-assert-ok` is the added red pin, and
the fail-closure is deliberately over-approximate (it fires on any embedded
field, whether or not promotion would actually apply). The two pre-existing
`embedding/` untriaged ids are the same root cause and are folded in
here (untriaged 29 → 27 in the same commit). Fix direction (owed
sub-slice, recorded in
`docs/2026-07-30_interfaces-campaign-design.md`): frontend synthesizes
forwarding method entries for the promoted method set (receiver
adjustment = field access chain), which keeps GoCore's dispatch flat —
mirroring how gc actually compiles wrappers.

## BUG-006 — interface slots hold RAW values (no conversion wrap); guarded fail-closed

- Status: fixed (2026-07-30, interfaces campaign — the real
  conversion wrap landed: `wrapInterfaceConversion` emits
  `to-interface` at every former guard site; the machine boxes with the
  canonical dynamic `Ty`. `interfaces/typed-nil-pointer-compare` now
  PASSES (Go 111 = machine 111); the pinned case below flipped back
  FAIL→PASS with the wrap in place. Residue kept fail-closed: the two
  multi-value-assign tuple sites still refuse (deferred, message says
  so).)
- Pinned-by: differential
- Cases: comparisons/short-circuit/struct-skips-interface-panic
- Discovered: 2026-07-25/26 (slice 0d; scope completed by the pre-merge audit)

The lowering has no interface-conversion wrap: a concrete value flowing
into an interface-typed slot keeps its raw representation, which makes
typed-nil comparisons and cross-dynamic-type behavior silently WRONG
(`interfaces/typed-nil-pointer-compare`: Go 111, raw lowering 1). Until
the interfaces campaign lands the real wrap
(`docs/2026-07-25_arc-sequence.md` item 3), the frontend FAILS CLOSED at
every site a value implicitly converts to interface: assignment pairs,
var initializers, call arguments and packed variadic elements, append
elements, `new(expr)`, composite-literal fields/elements/keys/values,
the map-assign fast path, and `return` into interface results (the last
four were audit findings — the guard's first cut missed them). The
pinned case is the one PASS→FAIL this closed: a struct literal with an
interface field was accidentally green because Go's `==` short-circuits
on an earlier field before touching the raw payload — listed here per
the re-pin guard. The guard treats an untyped-nil source as exact
(a nil interface IS the raw nil).

## BUG-005 — map iteration snapshots ENTRIES, so it observes neither delete/clear nor value updates

- Status: open
- Pinned-by: differential
- Cases: maps/delete-during-range, maps/clear-during-range, maps/update-during-range
- Discovered: 2026-07-26 (pre-merge adversarial audit of `wrong-answers-builtins`)

`mapRange` snapshots the entry array once (the reshape's nondeterminism
design) and iterates the snapshot, so an entry removed during iteration
is still produced. The Go spec is explicit the other way: "If a map entry
that has not yet been reached is removed during iteration, the
corresponding iteration value will not be produced." The combination only
became REACHABLE when this arc landed `delete`/`clear` — the audit's
probe (`for k := range m { n++; delete all }`) gets one iteration from Go
and three from the machine, a silent wrong answer, now pinned red by the
two Cases. (Entries CREATED during iteration may or may not be produced,
so the snapshot's not-producing them is fine — removal is the defect.)

**Third symptom, added 2026-07-31 (final pre-merge audit, finding 1):
STALE VALUE READS.** The title and the paragraph above enumerate removal
and explicitly dismiss creation, and never mention UPDATE — so a reader
of this entry would not learn the symptom exists, and no case pinned it.
The snapshot freezes each entry's VALUE as well as its key, and
`Cont.mapIterK` hands both to `bindIterVars`, so a value written to an
already-present key from inside the loop is never observed:

    m := map[int]int{1: 10, 2: 10}
    sum := 0
    for _, v := range m { m[1] = 99; m[2] = 99; sum += v }

Go returns 109 (the second iteration reads the update); the machine
returns 20. Deterministic on BOTH sides — the two entries start equal and
end equal, so iteration order is irrelevant and the machine gives 20
under every choice stream — so this is a plain differential red, not a
nondet case: `maps/update-during-range`. The prescribed fix below already
covers it ("re-read values live"); this records the symptom and pins it.

The fix is real machine surgery: `Cont.mapIterK` must carry the map's
base location and the pick-next step must skip keys no longer present
(and re-read values live), which touches the nondeterministic rule pair
and `MachineSound` — scheduled as its own slice, not rushed into an
audit response.


COUPLING (sem-adequacy arc, 2026-08-04): the snapshot-time key/value
self-normalization check (`mapRangeSnapshotEntries`) and `MachineWf`'s
`itersNormalized` component are built ON the snapshot design this bug
schedules for replacement. The prescribed live-iteration fix
(`Cont.mapIterK` carrying the map's base loc, pick-next skipping absent
keys and re-reading values) must REPLAY the stream-obliviousness
analysis: the per-pick lookups it introduces must stay
choices-independent in ok-ness, and the wf typing component must move
from the snapshot to the live map cell. Do not land the BUG-005 surgery
without re-running `step_complete_any_wf`'s mapIterNext case.

## BUG-004 — panic abort rendering: boxing identity and defined-type payloads unmodeled

- Status: open
- Pinned-by: differential
- Cases: panic-recover/repanic-same-value-abort, panic-recover/panic-newline-abort, panic-recover/panic-defined-payload-methods/error, panic-recover/panic-defined-payload-methods/stringer
- Discovered: 2026-07-25 (pre-merge adversarial audit of `unwinding-arc`)

Go's abort output makes four demands the machine's value-level state
cannot meet, all found by audits and now FAILING CLOSED instead of
printing a wrong first line:

1. **`[recovered, repanicked]` collapse is eface IDENTITY** (a bitwise
   type-word + data-pointer compare in `preprintpanics`), not semantic
   equality. `panic(recover())` and re-panicked constant literals share a
   box and collapse; runtime-computed equal values do not (the arc's §A3
   probe was constant-folded — `"or"+"ig"` is one static eface). Unequal
   payloads certainly render ` [recovered]`; EQUAL payloads are
   undecidable without an allocation-identity model, so `renderPanicHead`
   returns none there. This turned `repanic-same-value-abort`
   PASS→FAIL (intentional, recorded here per the re-pin guard): the
   collapse it pins is real Go behavior our chain cannot decide.
2. **Defined-type payloads print qualified**: `panic(Code(7))` renders
   `main.Code(7)` via `printanycustomtype`. Root cause was deeper than
   the render arm: the lowering modeled a defined non-struct type as a
   GoCore ALIAS, erasing the identity before the machine saw it.
   **FIXED 2026-07-30 (interfaces campaign)**: `TypeDef.defined` keeps
   the identity, TypeId keys are package-qualified at the frontend, and
   `renderPanicPayload` renders the `main.Code(7)` form for
   int-underlying defined payloads (other underlyings stay closed).
   `panic-recover/panic-named-type-abort` flipped red→PASS with this.
   Items 1 (eface identity), 3 (multi-line payloads) and 4 (the
   `preprintpanics` rewrite) remain open; their pins stay red.
3. **Multi-line string payloads**: Go's first line stops at an embedded
   `\n` (`printindented`); `asciiString?` rejects the newline byte
   (`panic-newline-abort` is the red pin).
4. **`preprintpanics` REWRITES the payload before printing**: a payload
   implementing `error` prints `v.Error()`, one implementing
   `fmt.Stringer` prints `v.String()`, and `printanycustomtype`'s
   `main.T(v)` shape is reached only when the defined type has NEITHER.
   Item 2's fix shipped an UNCONDITIONAL `main.T(v)` arm, so
   `panic(Code(9))` with `func (Code) Error() string` rendered
   `main.payloadCode(9)` where Go prints `boom` — a fail-closed →
   wrong-answer regression (pre-merge audit 2026-07-31, finding 3).
   Rendering the rewritten form means CALLING a method at abort time,
   which the terminal rule cannot do, so the machine now checks the
   payload's method set (`Error() string` / `String() string`, the
   runtime's own two interfaces — checked directly, not through a wire
   interface declaration, since the rewrite applies whether or not the
   program mentions `error`) and returns `none` when either is present.
   `main.T(v)` survives for the method-less case
   (`panic-defined-payload-methods/plain` is the green pin; `/error` and
   `/stringer` are the red ones).

RECOVERING any of these payloads is fully supported — only the terminal
abort line is restricted. The remaining fixes, if ever needed, are an
allocation identity on boxed payloads (1), the multi-line `printindented`
shape (3), and a way to render the `preprintpanics` rewrite without
calling a method at abort time (4). (Corrected 2026-07-31, final
pre-merge audit finding 15: this sentence used to offer "a
package-qualification story (2)" as outstanding — item 2 SHIPPED on
2026-07-30, as the body says and the baseline's PASS on
`panic-recover/panic-named-type-abort` confirms — while omitting both
items that really are open. `scripts/check-bugs.sh` parses Status/Cases
and never prose, so no gate could catch it.)

## BUG-003 — for-clause per-iteration loop variables (Go 1.22) are not lowered

- Status: fixed
- Pinned-by: differential
- Cases: control-flow/for-loopvar-escape, functions/closure-loop-var-capture
- Discovered: 2026-07-25 (pre-merge adversarial audit of `seq-coverage-scoping`)
- Fixed: 2026-08-04 (control-flow slice stage 1,
  `docs/2026-08-04_control-flow-design.md`): `emitForPerIteration` desugars a
  captured-loop-var for-clause with a carrier POINTER — a fresh cell per
  iteration copied in at the TOP of the body, the carrier re-aimed at it, post
  running on the fresh cell — so `continue` needs no copy-back path and each
  iteration's captures see a distinct cell. Both pinned cases green.

A three-clause `for` declares its variable ONCE outside the loop in our
lowering, but Go ≥1.22 gives each iteration its own variable — a closure
escaping the iteration must see that iteration's value. With lambda-lifted
closures capturing by address, the shared cell was a **silent wrong answer**
(`for-loopvar-escape`: Go 01, we produced 22). The frontend now FAILS CLOSED
on any func literal capturing a for-clause loop variable, which also turned
`closure-loop-var-capture` red — its within-iteration capture was
observationally correct under the shared cell, but the cheap guard cannot
distinguish escaping from non-escaping captures (intentional red, recorded
here per the re-pin guard). Range loops are per-iteration already and are
unaffected (`range/range-loop-var-capture` stays green). The fix is a real
design item: the spec declares each subsequent iteration's variable before
the post statement, initialized from the previous one, and our
while-lowering cannot express that without a per-iteration copy-in that
survives `continue` (scoping note §8 has the re-entry sketch).

## BUG-002 — expression-step atomicity is wrong for concurrent Go (latent)

- Status: open
- Pinned-by: none (latent — `Rel` has no goroutine rules yet, so no
  concurrent claim is derivable today and no differential case can pin it;
  it becomes a live unsoundness the day concurrency lands without the fix)
- Discovered: 2026-07-22 (arc E loop-law review of the Goose divergence;
  classified a BUG, not a caveat, at user direction — concurrency is
  committed, so "coarser than Go" is wrong-by-default, not a scope note)

`ExprR` is a big-step premise relation inside statement steps, so a
compound expression reading several cells (`x == y`, `x == y+z`) is ONE
atomic `Rel` step. Real Go interleaves goroutines between the reads. If
goroutine rules are added over the current granularity, the model UNDER-
approximates real behaviors (misses torn reads), and Iris invariant
opening "around one atomic step" licenses reasoning across a multi-read
window — together enough to prove theorems false of real Go for racy
programs (e.g. invariant-mediated plain reads racing a two-step writer:
the model never shows the mixed pair a real schedule can produce). The
DRF escape ("coarse ≡ fine for race-free programs") is NOT self-enforcing:
the logic would verify such racy programs without complaint, so carrying
this granularity into a concurrent `Rel` violates fail-closed (a hidden
wrong answer, not a visible red).

**Consequence: the concurrency arc (F4) is BLOCKED on resolving this.**
Sequentially it is NOT a bug — GoCore `Expr` has no call constructor (the
frontend must lower calls out of expressions), so no sequential program
distinguishes the granularities; every current theorem is unaffected.

Fix paths (F4 decides; record the choice there):
1. **Refactor expression evaluation into the configuration language**
   (small-step expression machine): word-level granularity, `wp_bind` and
   `wp_atomic` become available (retiring two recorded workarounds), and
   the calls-in-expressions trigger in `Rel.lean` points the same way.
   The likely eventual fix; substantial correspondence rework.
2. **v1 confinement concurrency**: goroutine-confined heaps, ownership
   transferred only via channel externs (CSP-style) — no shared-memory
   invariants in v1, making expression granularity moot; matches the
   etcd-raft north star's actual architecture (single-threaded core,
   message passing). Defers (1) to a lock-free-code widening.
3. Law-discipline restriction (invariants openable only around
   single-access steps): fragile, easy to violate silently — likely
   reject.

See `docs/2026-07-22_arc-e-while-invariant.md` §2′ (the sequential
justification) and TODO.md F4 (the charter). This entry exists so the
constraint cannot rot in prose while goroutine machinery is built.

**Scope sharpening (2026-07-22, same day):** the full fix is bigger than
expressions. Even a small-step expression machine leaves `Step.assign`
bundling its reads and its write in one step — true word-level atomicity
requires decomposing statement steps into a HeapLang-style memory-op
machine, a major reshape of the trusted relation. This strengthens the
case for fix path 2 (confinement v1) and for making the F4 *decision*
early even while the *fix* is deferred: the rework cost of path 1 scales
with fragment size, so every Arc-E widening rung built before F4 decides
deepens the potential hole. Recommendation recorded: write the F4 note
before or alongside the next major fragment widening (structs/arrays),
not after.

**Direction pinned (2026-07-22, user):** fix path 2 (confinement-only
v1) is REJECTED as the target — it excludes most actually interesting
concurrent Go (mutex-protected shared state, sync/atomic, lock-free
patterns); "CSL-proofs-only is a trivial kind of concurrency." The target
is full shared-memory, fine-grained concurrency with the complete Iris
apparatus. Path 1 (the memory-op machine) is THE fix, and its scope is
larger than first recorded: the INTERPRETER is in scope too — it is the
executable side of the Choices split, and instantiating real schedules
requires preemption points at memory-op granularity (big-step `evalExpr`
cannot be preempted mid-expression; an earlier claim that the interpreter
survives unchanged was wrong). Alignment note: Go's sync/atomic is SC, so
an SC interleaving model at memory-op granularity honestly covers
atomics-based code; plain-access races remain out of verification scope
(UB-ish in Go — same position as Goose). Sequencing consequence: the
reshape is unavoidable and its cost scales with fragment size, so it
should be the next MAJOR arc after the current rung — BEFORE the
structs/arrays widening, which would otherwise be built twice.

**Reshape R1+R2 landed (2026-07-23, branch `reshape-smallstep`, stages
S0–S4 of `docs/2026-07-23_reshape-r1r2-machine-design.md`):** the
structural root is fixed. Expression evaluation is in the configuration
language (`GoLean/GoCore/Machine.lean`: `evalE`/`retV` configs, generic
`strictK` operand frames), loads and stores are individual `Step` rules,
and `Step.assign` no longer bundles reads with its write (target address,
RHS evaluation, and the store are separate steps around machine-evaluated
operands). The interpreter is the relation instantiated (`stepFn`,
iterated fuel-bounded), so preemption points exist at memory-op
granularity on the executable side too. The big-step rules (`ExprR`, old
statement rules, `Eval` cluster, T1/T2 correspondence) are DELETED per the
F4 §2 directive — validated by ZERO DRIFT on the full 718-case
differential plus 40/40 eval tests. Still open before this bug CLOSES
(R4): goroutine rules + scheduler `Choices`, and the granularity-ledger
re-audit of multi-cell apply steps (`appendSlice` spill, `copySlice`) —
coarse-but-recorded, fine sequentially, must not silently enter
concurrency claims.

## BUG-011 — anonymous `struct{}{}` literal stuck at named empty-struct types

- Status: fixed (2026-08-05, general-coverage slice 2 — corpus case FIRST
  (classified red, all six subjects), then the assignability-aware
  normalization: `emptyStructAssignable` (Ops.lean) retags the canonical
  unnamed `struct{}` value at a defined empty-underlying target (and the
  reverse direction) in `normalizeStructValueWith`, plus the same escape
  in `valueEqFuel`'s struct-tag checks for the mixed-operand comparison.
  Metatheory in the same commit: `normalizeStructValueWith_locSup`
  (StateWf) and the congruence/default-value lemmas (MachineSound) gained
  the escape branch. Design note D4,
  `docs/2026-08-05_embedding-interfaces-design.md`.)
- Pinned-by: differential
- Cases: structs/empty-struct-literal-at-named-type/var-init, structs/empty-struct-literal-at-named-type/param, structs/empty-struct-literal-at-named-type/return, structs/empty-struct-literal-at-named-type/map-store, structs/empty-struct-literal-at-named-type/reverse, structs/empty-struct-literal-at-named-type/compare
- Discovered: 2026-08-04 (sem-adequacy notions sub-branch audit, semantics
  reviewer probing beyond the diff; verifier reproduced independently)

`normalizeStructValueWith` (Ops.lean, the struct arm of value
normalization) compares the VALUE's carried `TypeId` against the target
defined type with raw disequality — Go type IDENTITY — where Go
assignment applies ASSIGNABILITY: an anonymous `struct{}{}` composite
literal is assignable to any defined type whose underlying type is
`struct{}`, so `var x T = struct{}{}` succeeds in Go and goes `.stuck`
here ("struct value type mismatch: expected main.T, got struct{}").
Same class as the conversion/assignability distinctions the interfaces
campaign handled elsewhere; fail-closed direction (visible red, no wrong
answer). Fix shape: assignability-aware normalization for identical
underlying struct types (or frontend-side retagging of untyped
composite literals at their assignment type); guardrail corpus case
FIRST per the standing rule.
