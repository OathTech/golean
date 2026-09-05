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
   (`stage=lean-observation`, `stage=differential`, `stage=membership`,
   `stage=confluent`, or `stage=racy` — wrong/stuck answers and
   enumeration-lane alarms, not frontend-coverage gaps; membership added
   at the arc-final audit F9 2026-08-06; confluent/racy at the
   channels-arc final audit F5 2026-08-08) are **not** yet explained by
   any bug entry — the omission surface to ratchet toward zero.

Bugs that cannot yet be mechanically pinned use `Pinned-by: none (<reason>)` and
are exempt from (1)/(2) — but still listed, so they cannot disappear.

**Entry format (keep parseable):** a `## BUG-NNN — <title>` heading, then
`- Status: open|fixed`, `- Pinned-by: differential|none (<reason>)`, and (for
differential-pinned) `- Cases: <id>, <id>, …` (baseline case ids), then prose.
A `Pinned-by: none` entry whose Cases are RED-BY-DESIGN pins may add
`- Expect: FAIL` (before its Cases line): check-bugs then requires every
listed id to be FAIL, so a designed refusal that stops firing trips the gate
(q-u4-gomem audit fix F4, 2026-09-02; the only accepted value is FAIL).

---

## BUG-061 — the pruning rule under-approximates `staticinit`, so a package gc folded into the data section is still scheduled

- Status: open
- Pinned-by: differential
- Cases: multipkg/init-order-staticinit/seq

gc schedules a PRUNED set of packages: `MakeTask`
(`cmd/compile/internal/pkginit/init.go`) emits a `..inittask` record
only for a package with residual initialization work or an
inittask-bearing import, and `cmd/link` orders exactly those records.
"Residual work" means what survives
`cmd/compile/internal/staticinit`. The frontend
(`tools/nativefrontend/load.go`, `sourceHasInitWork`) approximates that
syntactically: a `func init()` with a non-empty body is work, and a
package-scope variable initializer is work unless go/types folded it to
a constant.

`staticinit` folds strictly more than "is a constant" — composite
literals of static elements, copies from other statically initialized
globals, addresses of globals, conversions of constants, and, with the
inliner on, whole function calls. So the frontend UNDER-PRUNES: it
keeps a node gc deleted, which leaves a spurious EDGE, which can delay
an importer past a package it should have beaten.

Pinned witness (`multipkg/init-order-staticinit`): `zq`'s only
initializer is `var A = [3]int{1, 2, 3}`. Go has no array constants, so
go/types records no constant value, but the array goes straight into
the data section and `zq` gets no record. gc: `la` is ready at step one
and beats `lb` — 12. Frontend: `la` waits for `zq` — 21.

**Size, measured.** A 26-flavor probe over the ways a package can be
initialized (recorded in `docs/spec-divergence-ledger.md` L-011) puts
the residual at 11 of 26 flavors, every one in the same direction:
`addrglobal`, `arraylit`, `arrayofstr`, `bytesconv`, `callinit`,
`funcvalue`, `nestedlit`, `slicelit`, `staticcopy`, `structlit`,
`structzero`. The 120-seed randomized differential harness is at 0
mismatches and cannot see any of it — every package it generates has a
call-valued initializer, so it is a node under both rules. This bug is
found by construction, not by the corpus.

**Why it is not simply closed.** Ten of the eleven are chaseable: a
recursive "is this expression statically initializable" predicate over
composite literals, `&global`, static copies and constant conversions
would fold them in, at the cost of a mini-`staticinit` port whose own
failure mode would be OVER-pruning — deleting a real edge, the unsafe
direction. The eleventh, `callinit` (`var X = f()` for a foldable `f`),
is not chaseable at all: `go run` and
`go run -gcflags=all='-N -l'` produce DIFFERENT observable orders for
the same source, so that part of the schedule is an optimizer artifact
rather than a property of the program. Closing this bug therefore means
deciding what the machine should model at a point where gc itself is
not single-valued — see ledger L-011, which classes the whole area as
latitude rather than a forced point.

## BUG-060 — the initialization schedule omits the imported STDLIB packages, so a local package gated by a stdlib import is scheduled too early

- Status: fixed (2026-08-18, audit-fix round F1b, then RE-DIAGNOSED and
  re-fixed in the delta-review fix round: `specInitOrder` in
  `tools/nativefrontend/load.go` now builds gc's PRUNED node set — a
  package is a node iff it has residual init work or an
  inittask-bearing import — with stdlib node facts and edges read from
  the compiled archives via `tools/nativefrontend/inittask-std.tsv`,
  and walks it by linker symbol name. Non-source nodes are dropped only
  after taking their positions. Type-check order — a separate, weaker
  requirement — stays local-only; conflating the two was the original
  defect. Both cases PASS.)
- Pinned-by: differential
- Cases: multipkg/init-order-stdlib/seq, multipkg/init-order-stdlib/marks

The W1.1 loader built the initialization list over the case-local
source packages only, dropping every stdlib node, so a local package
whose readiness is gated by a stdlib import looked ready too early and
could be scheduled ahead of a lexicographically later package that was
genuinely ready.

The pinned witness: `aaa` (imports `rec` and `sync`) sorts before `bbb`
(imports `rec` only), yet Go observes 21 — `bbb` first — and the
local-only machine observed 12.

**MECHANISM CORRECTED (delta review, 2026-08-18).** The original entry
explained the 21 as "real Go initializes `rec` before `sync`, so at the
step after `rec` only `bbb` is ready". That is not what happens. `rec`
has no variable initializers and no `init` function, so it has no
initialization work at all: gc emits no record for it and it is NOT IN
THE SCHEDULE — it is never "initialized before `sync`", and it never
gates anybody. The real mechanism is that `bbb`'s only import is the
pruned `rec`, so `bbb` is ready at step ONE, while `aaa` is blocked by
`sync`, which does have work and IS a node. `bbb` goes first; hence 21.
Same observation, same fix direction, wrong story — and the wrong story
was load-bearing, because it implied every imported package occupies a
position, which is exactly the belief the delta review refuted
(BUG-061, `multipkg/init-order-pruned-stdlib`).

Likewise the original closing line — "the ORDERING effect of those
packages ... is computable from the import graph alone" — is false as
written. Which stdlib packages are nodes is NOT computable from the
import graph; it is a fact about compiled objects, which is why the
frontend now reads it from a generated table and refuses any std import
the table does not cover.

Found by the W1.1 pre-merge audit (finding F1), not by any green gate:
the lower bound cannot see an omission that no corpus case exercises,
which is why the reproduction lands as a case before the fix. The
re-diagnosis was found the same way one level down — by reading gc,
not by running anything.

## BUG-059 — panic messages render multi-segment TypeId qualifiers as the import PATH where gc renders the package NAME

- Status: fixed (2026-09-05, lane `fr19-bug097` [AGENT] — the structural fix this
  entry always named, "separating DISPLAY from IDENTITY in GoCore":
  design note `docs/2026-09-05_fr19-bug097-design.md` §3. Every wire
  TypeDef carries a REQUIRED `display` (gc's `NameString` — package-NAME
  qualified, scope-free, deliberately ambiguous; `cmd/compile/internal/
  types/fmt.go` fmtTypeIDName, the string `reflectdata.dcommontype`
  stores) and `pkg` (declaring import path); `Program`/`ExecState.
  typeDisplays` carry them; `goTypeNameForMessage`, `renderPanicPayload`
  render the record and never the key (no record → a VISIBLE marker, not
  a fabricated text); `typeAssertPanicMessage` appends gc's suffix when
  the displays collide — ` (types from different packages)` for distinct
  declaring paths, ` (types from different scopes)` otherwise
  (`runtime/error.go` `TypeAssertionError.Error`, probed go1.26.5). The
  pinned witness renders `interface conversion: interface {} is inner.T,
  not inner.T (types from different packages)` byte-exact; the R-1
  quotient this row waited on is no longer needed for it. The
  observation channel (`TypeId.unqualified`, reflect `Name()`) was
  checked for a remainder and has none: gc's `Name()` keeps an
  instantiation's PATH-qualified bracket (`Pair[red/inner.T]`, probe P5's
  `Name()="Pair[red/inner.T]"` line — added at the audit fix round R15;
  the first record cited a `Name()` observation the probe did not yet
  make), which is the key's spelling. The identity note's §3.3 residue is
  RETIRED. `dynamicTypeName?` (key-rendering, unused) deleted.
  CORRECTION at the audit fix round (R1 BLOCKER, 2026-09-05 [AGENT]): the
  first cut's `typePkgForMessage` answered `""` for EVERY non-TypeId `Ty`,
  so `*inner.Q, not *inner.Q` carried ` (types from different scopes)`
  where gc prints ` (types from different packages)` whenever `Q` has a
  method — gc's `pkgpath()` (`runtime/type.go`) reads the UNCOMMON
  section, which `*T` has exactly when its method set is non-empty
  (`reflectdata` `uncommonSize`; `typePkg(*T)` = `T`'s package). The
  machine now derives `*T`'s answer from the wire's method table and,
  with no method on the wire, from the method-set record (`full` ⇒ empty
  ⇒ `""`; `exported`-only or absent ⇒ REFUSE by name — never a guess);
  `[]T`/`map`/`chan`/`func`/`**T`/`*I` stay `""` (no methods, not
  struct/interface kind); a record-less TypeId REFUSES rather than
  `.getD ""` (R10). Pinned by the four `multipkg/same-name-pointer-panic`
  rows (`*P` no methods → scopes; `*Q` value method and `*R` pointer
  method → packages; `[]Q` → scopes), all PASS; auditor's reproducer
  `.tmp/audit/p/V`.)
- Pinned-by: differential
- Cases: multipkg/same-name-identity-panic, scoping/local-type-identity/scopes-panic, scoping/local-type-identity/shadow-panic, multipkg/same-name-pointer-panic/no-methods, multipkg/same-name-pointer-panic/value-method, multipkg/same-name-pointer-panic/pointer-method, multipkg/same-name-pointer-panic/slice-control

> **R-1 conversion state (2026-08-21, raft W4.3 item 5 —
> docs/raft-w43-log.md).** The 2026-08-20 R-1 ruling quotients this
> row's TEXT (the spec defines no panic-message string) and keeps the
> FORCED half exact. Executed case-level: the forced half is now
> PROVED by `multipkg/same-name-identity-panic/forced-half` (green:
> the failed assert panics and is recoverable, both oracles) — with
> the KIND clause recorded as BLOCKED (asserting the recovered value
> to `error` refuses: the runtime error type carries no
> MethodSetRecord, the BUG-009/BUG-053 fail-closed class). BOTH text
> members are recorded in the case file (gc's name-qualified ambiguous
> form; ours the path-qualified form). The row itself stays RED until
> the machine can carry the quotient — the display/identity split
> below is semantic-core work (formerly the W3.2 lane's; re-homed
> 2026-08-31, fidelity decision 6 [USER]: owner now this repo's
> TODO.md backlog), and this red is "inclusion not yet checkable",
> never relaxed.

Path-keyed TypeIds (the BUG-010 fix, multi-package arc W1.1,
`docs/2026-08-18_multipackage-identity.md` §3) made identity DECISIONS
correct, but GoCore's message renderers print `TypeId.key` VERBATIM
(`goTypeNameForMessage` / `dynamicTypeName?`, `GoLean/GoCore/Ops.lean`),
while gc qualifies panic-message type names by the package NAME: for
the pinned witness the machine says `interface conversion: interface {}
is red/inner.T, not blue/inner.T` where gc says `... is inner.T, not
inner.T (types from different packages)`. The divergence exists only
for types from packages whose import path ≠ package name (multi-segment
paths); for the whole vendored-raft scope (short paths, path == name,
identity note §4) rendering is exact. Not fixable frontend-side: no one
key string is both path-injective and byte-equal to gc's deliberately
ambiguous name-qualified message. The structural fix is separating
DISPLAY from IDENTITY in GoCore (a display-name table or TypeId field)
— a semantic-core change deliberately out of the W1.1 arc's scope;
dotted paths (which would additionally break `TypeId.unqualified`'s
reflect-Name strip) are refused at the frontend boundary
(`checkKeyPathGrammar`), so only the message-string channel diverges,
and only differentially-visibly.

## BUG-053 — interface satisfaction on bare sync primitives answered a false "no" (wrong comma-ok bool, wrong type-switch branch, fabricated missing-method panic)

- Status: fixed (2026-08-10, spec-parity arc-end fix round: the
  `emitType` sync branch returned its `{"kind":"sync"}` node BEFORE the
  imported-named registration that feeds the D5 method-stub pass, so
  the four modeled types were the only imported family with NO
  method-table entries — and the only one whose zero value is modeled,
  so queries ran past the point where a missing table yields an answer
  instead of a refusal. `Ty.sync` is not `.defined`, so the machine's
  BUG-009 not-recorded guard read the empty table as a CORRECT empty
  method set and answered a definite false "no": `i.(locker)` comma-ok
  false where gc says true, the wrong type-switch branch, and a
  fabricated `interface conversion: *sync.Mutex is not main.locker:
  missing method Lock` panic on a program gc completes — silent, status
  ok, invisible to every green gate (only the EMBEDDING shape had a
  stub + pin, `sync/stub-satisfaction`). FIX: a dedicated
  `syncMethodStubs` pass emits the four types' FULL exported pointer
  method sets as declaration-only stubs (real go/types signatures,
  fail-closed bodies), with a FAIL-THE-EXPORT posture on un-emittable
  signatures instead of D5's skip-whole (no refusal lane exists for a
  skipped sync set); `sync.Locker` is emitted as a plain named
  interface (its own boxing/satisfaction + `RLocker`'s signature).
  Same root, same fix: sync method CALLS through a user-defined
  interface — which escaped the F4 quarantine (it keys on the resolved
  receiver; interface dispatch resolves to the interface) and landed as
  runtime `stuck` one layer too late — now refuse per-stub as visible
  `frontend-export` markers, and `sync.Locker` boxing behaves
  identically to a user-defined equivalent instead of refusing at the
  type. Value boxes correctly keep an empty method set (all four types'
  exported methods are pointer-receiver, mutex.go/rwmutex.go/
  waitgroup.go/once.go). Frontend-only fix; the machine and the 44
  designated statements are untouched by it.)
  (All seven pins below PASS post-fix; the definite-no controls
  `sync/satisfaction/assert-negative-missing` and
  `bare-assert-missing-panics` were green throughout, and the dispatch
  markers `sync/iface-dispatch/{mutex-user-iface,wg-user-iface,
  locker-box-dispatch}` are permanent-until-lifted `frontend-export`
  reds by design.) (LIFT LANDED 2026-09-01, Q-SYNCVAL slice — P-S2-6
  bodied stubs; the three dispatch markers flip PASS, identity with
  the direct lowering. Historical text above kept verbatim.)
- **CLASS-CLOSURE ADDENDUM (2026-08-10, user direction):** the fix
  above closed the INSTANCE (sync stubs), not the CLASS — the machine
  still read an absent method table as a correct empty method set for
  any type outside the `.defined` taxonomy arm, so a future imported
  family, a new frontend path, or a re-introduction of this bug would
  answer wrong "no"s again. Closed generically by the METHOD-SET RECORD
  CONTRACT (`docs/2026-08-10_method-set-record-contract.md`): the wire
  carries a REQUIRED `methodSets` field with one explicit record per
  method-carrying type (`full`/`exported` coverage; empty-but-present =
  genuinely empty; strict decode, duplicates refused), and
  satisfaction/dispatch answer ONLY from records — a queried carrier
  with no record refuses `.unsupported`, never answers, never goes
  stuck (`methodCarrierKey?`/`methodSetCoverage?`, Ops.lean; carrier
  kinds gc-probed: `.defined` and `.sync`; non-carrier emptiness is a
  language fact, not a registration default). The renderer's
  defined-type `main.T(v)` arm joined the closure (no record ⇒
  unrenderable, never a fabricated message). Pinned forever at the wire
  boundary by the Tests/GoCoreEval "MS:" fixtures: a TypeDef-present /
  record-absent type REFUSES satisfaction (the guard keys on the
  record, not the TypeDef), the same wire WITH the record answers the
  definite no, and the `.sync` no-record state refuses (the
  re-introduction pin). All 12 pinned lowering terms + 3 golden repr
  baselines regenerated for the new `Program.methodSets` field
  (bit-identical semantics; contract note §4); corpus classification
  unchanged on all 1483 ids.
- Pinned-by: differential
- Cases: sync/satisfaction/assert-ok-mutex, sync/satisfaction/type-switch-mutex, sync/satisfaction/bare-assert-mutex, sync/satisfaction/assert-ok-waitgroup, sync/satisfaction/assert-ok-once, sync/satisfaction/trylock-sig-satisfies, sync/satisfaction-locker-sig/assert-ok-rwmutex

## BUG-054 — WaitGroup negative-counter panic payload carried `$runtime.Error`; gc panics with a plain string

- Status: fixed (2026-08-10, spec-parity arc-end fix round: gc's sync
  package raises the panic as PACKAGE CODE — `panic("sync: negative
  WaitGroup counter")`, waitgroup.go:118, a plain `string` — where the
  channel panics are `runtime.plainError`s (runtime/chan.go), for which
  `runtimeErrorValue` is the correct modeling. The recovered value's
  dynamic type is the observable: `recover().(string)` answers true in
  gc, false against our `$runtime.Error` box — silent, status ok; the
  abort TEXT is identical for both payload kinds, so the existing
  message-only pins could not see it. FIX: `stringPanicValue` (a plain
  `string` interface box) at the `wgAdd` arm; the channel sites keep
  `runtimeErrorValue`. This is the only modeled sync panic — the
  Mutex/RWMutex misuse class is `fatal`, and the waiter-side reuse
  panic is the recorded §8 narrowing.)
  (The pin PASSes post-fix: 1032, the 1000+len discriminator.)
- Pinned-by: differential
- Cases: sync/waitgroup-panic-payload/payload-is-string

## BUG-055 — WaitGroup counter modeled as unbounded Int; gc's is an int32 that wraps mod 2^32 before the negative test (divergent in BOTH directions)

- Status: fixed (2026-08-10, spec-parity arc-end fix round: gc keeps
  the counter in the high 32 bits of a uint64 state word
  (waitgroup.go:104 `wg.state.Add(uint64(delta) << 32)`, :109
  `v := int32(state >> 32)`), so the addition wraps BEFORE the `v < 0`
  panic test. Unbounded Int diverged both ways: `Add(1 << 31)` — gc
  wraps to -2^31 and panics, the model proceeded silently with 2^31;
  `Add(-(1 << 32))` — the shifted delta's high word is 0, gc's state is
  UNCHANGED (no panic, counter 0), the model computed -2^32 < 0 and
  fabricated the panic. FIX: `counter' = ((counter + delta + 2^31)
  emod 2^32) - 2^31` in the `wgAdd` arm — the stored counter always
  lies in int32 range, matching gc's bit pattern; interpreter and
  relation move in lockstep through the shared `applySyncOp`.)
  (Both pins PASS post-fix.)
- Pinned-by: differential
- Cases: sync/waitgroup-int32/add-overflow-panics, sync/waitgroup-int32/add-wrap-noop

## BUG-052 — call write-back reads target operands BEFORE the call; gc reads them after (deterministic divergence inside spec-unordered latitude)

- Status: fixed (2026-08-09, spec-parity-s1 audit-fix round: the call
  paths (`.call` and `.callValue` both) now evaluate the CALL first —
  arguments, frame entry — with the caller-target PLANS riding
  `Cont.frame` untouched (`targets : List (TargetShape × List Expr)` +
  the caller env `tenv`); the target operands evaluate at frame EXIT
  through the existing tgtOpK spine (the receive path's exact delivery
  shape: `frameReturnTargets`/`frameFallTargets` load the pinned
  results and enter phase 1 post-call), then the per-target `storeK`
  stores. The pre-call target frames (`callTargetsK`/`callValTargetsK`)
  are removed outright. The pinned latitude is recorded at the rule
  site (Machine.lean, the call rules' PINNED LATITUDE block: spec text
  verbatim, gc's realization probed go1.26.5, version-tracked — a
  future gc realizing the other order revisits the pin, not the spec
  claim). SCOPE (delta review, same date): the pin covers ONLY the
  call-vs-operand axis. The INTER-TARGET phase-1 operand order is a
  separate spec-unordered axis this fix does not touch and gc realizes
  compiler-internally (unpinnable) — recorded as OPEN envelope in
  BUG-026's amendment, not claimed here. Laws moved in lockstep: `wp_call_start` (entry),
  `wp_call_enter_ret1` restated at the call-statement config,
  `wp_tgtop_stores` (the known-values completion), and the frame-exit
  family (`wp_frame_return_int`/`_fall_int`/`_int_inv`/`₁`/`₂`)
  restated as read-exit → post-call operand evaluation (`hres` premise)
  → per-target store lifts → drain; consumers re-proved. The
  `Tests/GoCoreEval` "call target sequencing" pin retuned 901 → 91
  (it encoded the retired operand-first order; the oracle-backed
  guards are the five corpus pins). All five pins flip PASS; the
  hoisted-control guard stays green. The `.callValue` half gained its
  own discriminator pins at the delta review
  (multi-assign/call-write-back-order-value/{index-target,
  deref-target} — func-value callees mutating a target operand; the
  named-func pins exercise only `.call`), green at the fixed machine
  and VERIFIED RED at the pre-fix machine (worktree at 390ed13c:
  index-target Lean 420007 vs Go 4207 — the operand-first signature;
  both cases FAIL there, both PASS at tip; the delta-review verifier
  probed the same discrimination independently).)
- Pinned-by: differential
- Cases: multi-assign/call-write-back-order/index-missed-panic, multi-assign/call-write-back-order/index-spurious-panic, multi-assign/call-write-back-order/global-index, multi-assign/call-write-back-order/deref-target, multi-assign/call-write-back-order/slice-header-base
- Discovered: 2026-08-09 (S1 pre-merge audit, semantics dimension,
  verifier-reproduced with an independent probe matrix; PRE-EXISTING on
  main — the pre-migration `callTargetLoc` path also resolved target
  addresses pre-call — but exposed by the BUG-025 closure's own
  "phase-1 faithful" prose, and the case named for the genre
  (multi-assign/target-eval-before-call) is structurally blind: its
  callee never mutates a target operand)

For `lhs..., x = f(...)` the machine evaluates the left-hand target
OPERANDS (index operands, a deref target's pointer, an index target's
slice-header base) BEFORE the callee/arguments and the call body; gc
evaluates them AFTER the call. Go's spec leaves the relative order
UNSPECIFIED (§Order of evaluation: "the order of those events compared
to the evaluation and indexing of x and the evaluation of y ... is not
specified"), so neither realization is non-conforming — but the site
consumes NO Choices (the machine claims determinism), the differential
oracle is `go run`, and a callee that mutates a target operand
diverges observably in BOTH panic directions (missed panic 51 vs
420030; spurious panic; deref/slice-header/global-index value
variants). The hoisted-call control (`x[i], j = f(), 3` — the frontend
hoists single-value calls ahead of the statement) already realizes
gc's post-call read, so the machine is not even internally consistent
about the timing. Fix per the deterministic-latitude precedent (panic
identity, hidden-dep init order): PIN GC'S REALIZED POINT — evaluate
the call first, then the target operands (through the existing tgtOpK
spine at frame exit, the receive path's exact shape), then the
per-target stores; record the pinned latitude at the site (spec text
verbatim, gc realization version-tracked).

## BUG-051 — single-value call assigned into an interface-typed target: the boxing wrap lands on the CALL NODE, which the decoder refuses (whole-program over-refusal)

- Status: fixed (2026-08-09, same closing-review round, FRONTEND-only
  (no machine/decoder change): the call-assign arm now hoists the call
  into a temp at the call's own result type (the existing `hoist`
  mechanism — the call stays in statement position) and boxes the
  TEMP via `wrapInterfaceConversion`, exactly the hoist-then-wrap
  shape the per-pair site documents; non-boxing targets keep the
  bare-call statement emission unchanged. All three pins flip PASS,
  the three controls stay PASS; the closing reviewer's exact probe
  matrix a–f re-run post-fix: a/d/f now ok with correctly boxed
  observations, b/c/e unchanged; BUG-050's four range forms +
  escalation and BUG-049's six-form matrix re-run green as
  regression guards. Zero drift on all 1399 other ids.)
- Pinned-by: differential
- Cases: interfaces/call-assign-boxing/assign-any, interfaces/call-assign-boxing/assign-error, interfaces/call-assign-boxing/named-result
- Discovered: 2026-08-09 (closing review of the round's unreviewed
  diffs, Opus reviewer + independent verifier; pre-existing — blame
  85f3659 (2026-07-30), NOT introduced by any commit of this landing
  round. BUG-050's family sweep had checked exactly this site and
  misrecorded it as "wraps at the site / clean" — corrected there.)
- What: `var x I; x = f()` where f returns a concrete type. The
  assign-site special case (tools/nativefrontend/emit.go, the
  single-value effectful-call arm) keeps the call in statement
  position as the assign RHS but applies `wrapInterfaceConversion` to
  the CALL NODE itself, emitting `to-interface(call)` — and
  NativeToIR refuses any call in expression position ("call in
  expression position is not modeled (calls are statements)",
  GoLean/NativeToIR.lean), so the WHOLE PROGRAM fails to lower.
  Ordinary Go (`var err error; err = makeErr()`; `out = mk()` into an
  interface-typed named result) becomes a status=error refusal: a
  fail-closed OVER-refusal — no wrong answer, but exactly the
  "fail-closed classification" hole class the green gates are
  structurally blind to (nothing in the corpus had the shape).
  Structurally, at this site the wrap was NEVER correct: a
  non-interface target makes it a no-op, and whenever it actually
  boxes, the result is unlowerable.
- Verifier probe matrix (all reproduced end-to-end at 2570667):
  (a) `var a any; a = mk()` → error "call in expression position is
  not modeled (calls are statements)"; (d) `var err error;
  err = makeErr(); return err.Error()` (go vet-clean ordinary Go) →
  same error; (f) named result `func probe() (out any) { out = mk();
  return }` → same error. Controls clean: (b) `var a any = mk()` →
  ok, boxed {dynamic int, 11}; (c) `var a int; a = mk()` → ok, raw
  11; (e) `a, b = 3, 4` into any,any → ok, boxed. Pins: the three
  red shapes in interfaces/call-assign-boxing (the refusal poisons
  the whole package's lowering, so the three controls are green
  guards in interfaces/call-assign-boxing-controls).
- Fix shape: emit the call as a statement into a temp (the existing
  hoist mechanism, typed at the call's result type), then assign
  `to-interface(temp)` — the hoist-then-wrap shape every working
  conversion-owing site uses (per-pair assign's own comment: "wrapping
  AFTER the hoist keeps the temp at the value's static type").

## BUG-050 — ASSIGN-form range into interface-typed targets skips implicit boxing (silent WRONG answer)

- Status: fixed (2026-08-08, same review round, FRONTEND-only (no
  machine/decoder change): `emitRange` now computes the source
  key/value component types from the range operand (spec §For
  statements — slice/array/pointer-to-array: int/elem; map: key/elem;
  string: int/rune; int: operand type; chan: elem) and the bind
  closure applies destination-typed `wrapInterfaceConversion` to the
  temp — the same mechanism as the BUG-049 fix and the multi-assign
  quarantine's eventual shape. A collection shape with no computed
  source type now fails closed at an interface-typed target instead
  of ever handing it a raw value. All five pins flip PASS; zero
  drift on all 1394 other ids.)
- Pinned-by: differential
- Cases: range/assign-form-interface-target/slice-value, range/assign-form-interface-target/map-key, range/assign-form-interface-target/index, range/assign-form-interface-target/string-rune, range/assign-form-interface-target/assert-escalation
- Discovered: 2026-08-08 (codex-landing skeptical review round: an
  Opus reviewer probing beyond the BUG-049 fix's matrix; verifier
  reproduced all four forms verbatim at 6624cc83. Pre-existing —
  identical pre-fix; NOT introduced by the BUG-049 landing, whose
  emit.go diff is entirely in `emitCallArgs`.)
- What: `for i, v = range X` (ASSIGN form, `=` not `:=`) with an
  interface-typed target: `emitRange`'s bind closure
  (tools/nativefrontend/emit.go) emits `outer = $rangeKey/$rangeVal`
  with NO `wrapInterfaceConversion`, so the raw key/element lands in
  the interface variable — while labeling the temp ident with the
  interface type it never carries. Unlike the quarantined multi-value
  assign forms this does NOT fail closed: both sides run to status ok
  and the OBSERVATIONS differ (Go interface-boxed vs our raw value) —
  a differential-visible SILENT WRONG ANSWER, the class this project
  treats as worst; asserting the value inside the loop escalates to
  wrong-stuck ("type assertion from non-interface value
  GoLean.GoValue.int 3"). Verifier's four-form matrix, all confirmed:
  slice value (Go boxed int 4 vs raw 4), map key (boxed 7 vs raw 7),
  index (boxed 1 vs raw 1), string-rune (Go {dynamic int32, 98} vs
  raw 98). Second member of the wrapInterfaceConversion-omission
  FAMILY (BUG-049 was the call-argument arm) — found serially, like
  the BUG-042/043 kind-defaulting family.
- Family sweep (2026-08-08, with the fix — recorded per the
  BUG-042/043 serial-discovery precedent: a second member found
  serially means the FAMILY gets sweep-audited, not found one-by-one.
  **CORRECTED 2026-08-09 per the closing review — the original verdict
  "clean except this one site" was FALSE for one site, and the site
  accounting was incomplete; corrections inline below**):
  the `"stmt": "assign"` emission sites in emit.go were classified —
  the original record said "all 16"; the true count is 24 emissions
  (the original 16 were coarse groups, and three logical sites fell in
  no bucket at all — closing review, minor finding). ONE hole of THIS
  bug's shape — the range bind closure (fixed above). The rest, as
  corrected: 2 wrap correctly at the site (per-pair assign,
  select-recv write-back); the THIRD claimed wrap-at-site — the
  single-value call assign — wraps the CALL NODE itself, producing
  `to-interface(call)` which the decoder refuses: a fail-closed
  over-refusal on ordinary Go, misrecorded here as clean and now
  filed and fixed as BUG-051 (closing review, major finding — the
  sweep's stated purpose was closing the family, so the false "clean"
  is recorded plainly, not papered over). Var-decl inits wrap at
  emission (feeding the goto-context re-init site); 5 same-type temp
  transfers (loop-var per-iteration cells, type-switch guard temp +
  clause binding, promotion-wrapper results, interface-method-value
  hoist); 6 synthetic int/bool machinery ($pc x2, firstVar, idxVar,
  fallVar x2); PLUS the three sites the original sweep never
  classified, added with the closing verifier's checks: the generic
  `hoist` temp (every caller passes the SOURCE type — the temp holds
  the value at its own static type), `splatMultiCall`'s tuple temps
  (declared at tup.At(i).Type()), and `emitSwitch`'s $sw tag temp
  (declared at the tag's own type; interface-vs-case boxing applied
  separately, both directions, at the comparison). The `:=`-form
  range binds its variables AT the component types (no conversion
  owed). The multi-value assign / var-decl-from-call / plain
  chan-receive interface forms fail closed with explicit quarantine
  messages (deferred, visible). The skeptical-review verifier's
  behavioral pass ("ordinary/field/deref/index/named-result/closure
  assigns, append, composite literals, map store, chan send box
  correctly") used NON-CALL RHSes — scoped accordingly: the
  named-result-assign-from-call form was in fact BUG-051-refused.
  Corrected sweep verdict: clean except TWO sites — this bug's range
  bind (silent wrong answer, fixed) and BUG-051's call-assign wrap
  (fail-closed over-refusal, filed same day).

## BUG-049 — tuple-forwarded call arguments bypass interface boxing (`g(f())` into interface-typed slots)

- Status: fixed (2026-08-08, codex-review landing — established on-branch
  fix precedent per the BUG-047/048 user rulings, FRONTEND-only (no
  machine/decoder change): `emitCallArgs`' splat arm now pairs each
  splatted temp with its destination parameter type (nonvariadic path)
  or the variadic element type (packing path) and applies the same
  `wrapInterfaceConversion` ordinary arguments get — the source type is
  the forwarded tuple component's, mirroring `emitReturn`'s per-result
  wrap. All four red matrix pins flip PASS, both controls stay PASS;
  zero drift on all 1383 other ids.)
- Pinned-by: differential
- Cases: interfaces/tuple-forward-boxing/fixed-any, interfaces/tuple-forward-boxing/variadic-any, interfaces/tuple-forward-boxing/mixed-second-any, interfaces/tuple-forward-boxing/fixed-plus-variadic
- Discovered: 2026-08-08 (external: Codex semantic-divergence review,
  `docs/2026-08-08_semantic-divergence-review.md` §1, run at GoLean
  06933964; reproduced verbatim at the current tip — one infra commit
  past the review's base)
- What: tuple forwarding `g(f())` where a destination parameter slot is
  interface-typed skips the implicit interface conversion each
  forwarded component owes (spec: each value of f()'s tuple is
  assigned to g's parameters). `emitCallArgs`
  (tools/nativefrontend/emit.go, the splat arm at the top) hoists the
  inner call via `splatMultiCall` and returns the raw temp idents —
  the nonvariadic path returns `idents` directly, the variadic path
  copies fixed idents and packs the variadic slice from raw idents —
  and BOTH bypass `wrapInterfaceConversion`, which ordinary arguments
  get immediately below. The machine then receives a raw value in an
  `any` slot and a later assertion fails closed:
  "type assertion from non-interface value GoLean.GoValue.int 7".
  Fidelity bug, not a coverage refusal: the construct crosses the
  frontend boundary. The analogous tuple-forwarded RETURN path already
  wraps per result (`emitReturn`'s splat arm). [CORRECTED 2026-08-08:
  this entry originally claimed "the omission is localized to the
  call-argument special case" — WRONG as a class statement. This is
  the wrapInterfaceConversion-omission FAMILY (a special-case lowering
  arm that moves values into typed slots without the implicit
  interface conversion every assignable context owes), and a second
  member was found serially in the same review round: BUG-050,
  emitRange's ASSIGN-form bind. Per the BUG-042/043 kind-defaulting
  precedent, serial discovery means the family gets SWEEP-audited;
  the sweep of every assign-emission site is recorded in BUG-050's
  entry — whose verdict the closing review corrected (2026-08-09):
  clean except TWO sites, the range bind (BUG-050) and the
  call-assign wrap the sweep itself had misrecorded as clean
  (BUG-051).]
- Pin matrix (per the review's warning that an (any,any)-only pin can
  miss per-position errors): (int,string)→(any,any) red raw-int,
  →(...any) red raw-int, →(int,any) red raw-STRING (second slot),
  →(int,...any) red raw-STRING (variadic slot), plus two PASS
  controls (→(int,string) no boxing; (any,any)→(any,any) source
  already interface). The mixed forms reporting the raw string show
  concrete slots stay correct and exactly the boxing-owed component
  is malformed.
- Fix shape (review-located): pair each splatted temp with its
  destination parameter type (or variadic element type) and apply the
  same `wrapInterfaceConversion` logic ordinary arguments get, before
  returning fixed arguments or packing the variadic slice.

## BUG-048 — machine wrong-STUCK calling a VALUE-receiver method through a pointer-typed VARIABLE (Go auto-derefs; we refuse)

- Status: fixed (2026-08-08, check-in response round — user-authorized
  on-branch fix, FRONTEND-side (no machine change, no lockstep needed):
  `methodReceiverArg`'s value-receiver arm now emits a deref when the
  receiver operand is pointer-typed, mirroring `promotedReceiverArg`'s
  `!pointerRecv && ftIsPtr` arm (which is why promotion-through-
  embedding already worked). All three pins flip PASS, incl. the
  imported `embedded/live` row — `useEmbeddedMethod2`'s
  `d.embedB.Foo()` now runs — PLUS the two pre-existing tracked
  untriaged backlog reds of the same class, methods/value-auto-deref
  and pointers/nil-value-receiver-call-panic (the nil variant now
  realizes Go's panic through the emitted deref); zero drift
  elsewhere; backlog ratchets 18 -> 16.)
- Pinned-by: differential
- Cases: methods/value-receiver-via-pointer-var/addr-of-var, methods/value-receiver-via-pointer-var/addr-of-literal, imported-goose/unittest/embedded/live, methods/value-auto-deref, pointers/nil-value-receiver-call-panic
- Discovered: 2026-08-08, goose-parity buildout batch 8 (goose-import
  provenance: `testdata/examples/unittest/embedded.go` @ 3be88bb —
  `useEmbeddedMethod2`'s `d.embedB.Foo()`, an explicit selector through
  a pointer-embedded field, stuck the machine; minimized by probes to
  the basic idiom below).
- What: `p := &x; p.get()` where `get` has a VALUE receiver — Go
  auto-dereferences (`(*p).get()`, spec §Selectors/§Calls); the machine
  gets STUCK with "expected struct main.sVal value, got
  GoLean.GoValue.addr (Loc.base …)". Wrong-stuck on a supported-claimed
  construct = fidelity bug by this file's definition. The frontend
  exports the program (no fail-closed refusal), so the miss is in the
  lowering/machine receiver handling, not a recorded coverage gap.
- Probe matrix (2026-08-08, all vs go run green): STUCK — `p := &x;
  p.get()`; `p := &S{…}; p.get()` (literal and empty-literal);
  `c.inB.Foo()` (explicit selector of a pointer-embedded field, value
  receiver). OK (controls) — `x.get()` on an addressable var (auto
  address/deref both directions); pointer RECEIVERS through the same
  shapes (`d.PGet()`, `d.inA.PGet()`, `d.PCar()`); IMPLICIT promotion
  through an embedded-pointer hop, value receiver (`d.Foo()`, incl.
  two-level chains and method shadowing); explicit DEEP path through
  the pointer hop (`d.inA.Foo()`); `&E{S{…}}` holder with promoted
  value receiver (`p.Get()` — note: promoted-through-EMBEDDING via a
  pointer variable WORKS while the direct method on the pointer
  variable does not, which localizes the miss to the non-promoted
  direct-method path's receiver adaptation).
- Why it survived (CORRECTED at fix time — this entry first claimed
  the cell was unexercised, which was WRONG): the corpus DID pin the
  class — `methods/value-auto-deref` (`c := &T{}; c.value()`) and
  `pointers/nil-value-receiver-call-panic` (`var p *T; p.value()`,
  expecting Go's nil-deref panic) sat as long-standing FAILs in the
  TRACKED untriaged fidelity backlog (baselines/untriaged-ids), never
  triaged into a bug entry. The import surfaced the class a second
  time and forced the triage; the fix flips all five ids and the
  backlog ratchets 18 -> 16.
- Fix: deferred during the buildout (charter), then user-authorized
  and landed in the check-in response round (2026-08-08) — see the
  Status line.
- Triage record: docs/goose-parity-parked.md P4 (branch park/reasoning-2026-08-31).

## BUG-047 — frontend emits a call TWICE when the RHS of a single assign/define is a conversion of a call (silent divergence from Go)

- Status: fixed (2026-08-08, check-in response round — user-authorized
  on-branch fix: the assign-site speculative-emitCallNode guard now
  covers CONVERSIONS exactly like builtins (`isConversion` beside
  `isBuiltinCall`, emit.go — a conversion RHS routes through the
  generic single-emit path, so the operand hoists once). Both
  canonical pins flip PASS; the two green-by-luck corpus instances
  (semantics/copy, unittest/const) verified green on the corrected
  single-emission lowering and their annotations removed; the
  `constLowered` R2 pin term REGENERATED — the drift was caught by
  `scripts/check-imported-pins`, the staleness guard shipped in the
  same response round, exactly as designed.)
- Pinned-by: differential
- Cases: assign-order/conversion-call-eval-once/define, assign-order/conversion-call-eval-once/assign
- Discovered: 2026-08-08, goose-parity buildout phase-B checkpoint review
  (goose-import provenance: batch 6's authored wrapper
  `sum := int(useUntypedInt())` in
  `Corpus/coverage/exec/imported-goose/unittest/const/main.go:56`
  surfaced the class; the checkpoint reviewer isolated it, the
  verifier reproduced the matrix below; the buildout worker
  re-reproduced `x := int(bump())` -> 202 vs 101 independently).
- What: for `x := T(f())` and `x = T(f())` — a conversion of a call as
  the WHOLE RHS of a single assign/define — the native frontend emits
  the inner call twice, so a side-effecting callee (or an effectful
  builtin such as `copy`) executes twice and GoLean silently disagrees
  with `go run`.
- Verifier's repro matrix (golean native-json-run vs `go run`,
  go1.26.5, quoted verbatim from the phase-B checkpoint verification):
  `x := int(bump())` 202 vs 101; `x = int(bump())` 202 vs 101;
  unused-result define 2 vs 1; `int(uint32(bump()))` 202 vs 101;
  `uint64(bump())` 202 vs 101; `n := uint64(copy(s[1:], s))` 31112 vs
  31123; and an additional variant, `s := string(rune(bump()+64))` 102
  vs 101. Controls behave correctly (plain `x := bump()`,
  `var x int = int(bump())`, `int(bump())+0`, `any(bump())` all
  agree), so the defect is specific to a conversion-of-call as the
  whole RHS of a single assign/define. Buildout-side additional
  controls (2026-08-08): `return int(bump())` and `x := len(bump())`
  are also correct — return statements and builtin-of-call take other
  emission paths.
- Root cause (verifier-confirmed): `tools/nativefrontend/emit.go:2112`
  calls `emitCallNode(call)`; the conversion branch (emit.go:5271-5322)
  has ALREADY hoisted the inner call into the statement buffer via
  `emitExpr`, then reports `effectful == false`, so the early-return
  guard at :2116 is skipped and the generic path at :2132 re-emits the
  same RHS, hoisting a second copy ($c0 dead, $c1 used). The adjacent
  `isBuiltinCall` guard (:2085-2094) was written for exactly this
  hazard but covers only a bare builtin RHS, not a builtin (or call)
  under a conversion.
- Known green-by-luck instances in the landed corpus (annotated at
  their sites): `imported-goose/semantics/copy` rows shorter-dst /
  shorter-src (`n := uint64(copy(y, x))` — copy runs twice,
  observationally idempotent here); `imported-goose/unittest/const`
  (`int(useUntypedInt())` — pure callee, checksum unaffected; its R2
  pin `Specs/ImportedGooseConst.lean` pins the DOUBLE-EMITTED term,
  true-of-term, docstring annotated). Corpus-wide source sweep found
  no other landed instance of the trigger shape.
- Fix: deferred during the buildout (charter), then user-authorized and
  landed in the check-in response round (2026-08-08) — the guard-side
  direction (conversion RHS never takes the speculative path).
- Handling lapse, recorded: the class was triggered by a batch-6
  wrapper and went unparked while the batch log claimed "zero frontend
  refusals" — a charter MUST-PARK compliance miss, recorded plainly in
  docs/goose-parity-buildout-log.md (branch park/reasoning-2026-08-31) and ledger entry P3.

## BUG-046 — BUG-045's chan-object rule is fail-open for SELECT SEND clauses: selectgo pass 1 DOES racereadpc the channel object per polled send case

- Status: fixed (2026-08-08, convergence-check response — `raceUpdate`'s
  select-apply arm records a chan-object READ per SEND clause via
  `selectClauseChans` before any dispatch (commit, park, pairing,
  panic alike), with the gc-exactness granularity argument at the
  site: selectgo runs pass 1 once per call and a woken parked select
  does not re-poll, so once-per-apply matches; poll order is a random
  permutation in gc, and clause-order recording is
  detection-equivalent (same pre-op clock, same-goroutine upserts).
  The pinned case flips PASS/racy ("every enumerated path refuses");
  the wrong eval pin `closedSelRecvSelWaiterMain_F` now expects race
  and the new `selSendPairedCloseMain_F` green twin exercises the
  poll read race-free (op×select pairing orders it before the close).
  Zero drift on every other id — recv-only selects and
  same-goroutine-ordered select-sends are unaffected, which the
  select corpus certifies as the regression suite. U3's, the
  doctrine's, and BUG-045's "select clauses record nothing" prose
  corrected in place.)
- Pinned-by: differential
- Cases: goroutines/select-closed-arrival/send-close-race
- Discovered: 2026-08-08 (convergence check on the BUG-045 fix,
  major; verifier-reproduced from primary source — go1.26.5
  runtime/select.go:288 `racereadpc(c.raceaddr(), casePC(casi),
  chansendpc)` sits in selectgo pass 1's send branch ABOVE the closed
  check; recv cases are acquire-only (:512). Probes: a select-send
  clause racing a close is TSan-red 30/30 — including the genuine
  multi-case selectgo path and the send+default form — while the
  BUG-045 rule recorded NOTHING for select clauses on the false
  premise "selectgo's clause commits bypass chansend/closechan".
  Worse, the same commit shipped an eval pin,
  `closedSelRecvSelWaiterMain_F`, asserting a green value result (5)
  for a shape gc flags 30/30, with a comment claiming TSan-green.)
- What: the BUG-045 premise confused the COMMIT path (selectgo's
  send/recv branches do bypass chansend/chanrecv) with the
  INSTRUMENTATION point: the chan-object read happens in selectgo's
  POLL (pass 1), once per polled send case, before the closed check
  and before parking — so every select-send clause polled on a
  channel whose close is HB-unordered is a real TSan race our
  detector passed green. The two probes the original rationale cited
  (selectSendClosedArrival, selectWakeClosed) never tested the claim:
  the first's close is same-goroutine-sequenced before its select and
  the second's select has only recv clauses. No corpus row was
  misclassified (no corpus subject had a select-send racing a close)
  — a latent model gap plus one wrong shipped eval pin.
- Fix shape: at the select's POLL step — the `.selectOpsK` apply
  position in `raceUpdate` — record a chan-object READ for EVERY send
  clause's channel (nil channels skipped: selectgo's pollorder
  excludes them), before any dispatch, whatever the outcome (commit,
  park, refuse, panic). Granularity argument (recorded at the site):
  selectgo executes pass 1 once per selectgo call and a woken parked
  select does not re-poll with racereadpc, so once-per-apply is
  gc-exact; recv clauses stay acquire-only. The wrong eval pin
  re-pins as the racy form and gains an HB-ordered green twin (the
  op×select pairing orders the poll read before the close); corpus:
  send-close-race (racy) + send-paired-then-close (confluent green).
  The invariant-(iv) guard beside a parked SELECT-send waiter joins
  the plain-sender case as detector-unreachable in race-free
  programs (a parked select-send implies an HB-unordered poll read
  vs any close; an ordered close hits sclose at the poll instead).

## BUG-045 — the channel OBJECT is not a shadow location: three shipped confluent-green subjects are TSan data races (`-race` fail-open; doctrine violation)

- Status: fixed (2026-08-08, channels-arc audit response F1 —
  `RaceState.chanObjAccess` models gc's pair (send = entry
  read at the apply position on every outcome; successful close =
  write; recv acquire-only; select clauses AMENDED by BUG-046: send
  clauses DO record a poll read — selectgo pass 1's racereadpc; the
  original "select clauses nothing" premise was wrong), dispatched by
  `raceUpdate`'s chan-op arm under the pre-release clock. All three
  pinned cases certify "every enumerated path refuses" (PASS/racy)
  with `go run -race` the justifying oracle; zero drift on all 1196
  other ids — the rule over-refuses NOTHING (race/free lane intact).
  The forkJoinNoRace designated statement is byte-identical and its
  meaning is unshifted: the fork/join program has no close, so its
  only chan-object records are send reads, which cannot conflict —
  certs recomputed green. Eval pins updated: the
  closed-guard-past-parked-PLAIN-sender pin now expects race, and the
  guard initially gained a "race-free" twin via a parked SELECT-send
  waiter on the FALSE premise that selectgo is uninstrumented —
  REVERSED by BUG-046 (that twin is TSan-red 30/30 and now expects
  race too; invariant (iv) beside ANY parked sender, plain or
  select, is detector-unreachable race-free). The three
  overclaiming "refusal-set agreement holds
  anyway" sentences (raceWakeEvent, doctrine caption, design note ×2)
  and U3 corrected in place.)
- Pinned-by: differential
- Cases: goroutines/close-wake/sender-panics, goroutines/close-wake/sender-full-buffer, goroutines/select-closed-arrival/recv-parked-sender
- Discovered: 2026-08-08 (channels-arc final audit F1, major/envelope;
  verifier-reproduced from primary sources: go1.26.5 runtime/chan.go —
  `chansend` line 190 does `racereadpc(c.raceaddr(), …)` at ENTRY,
  `closechan` lines 430-431 do `racewritepc`/`racerelease`; `chanrecv`
  performs only `raceacquire` — and all three subjects are TSan-red
  through exactly that pair, 30/30, 20/20, 50/50, while the whole
  remaining goroutines corpus (44 subjects × 10) is green: the family
  is precisely close-beside-parked-plain-send)
- What: the detector modeled channel cells as pure synchronization
  (Race.lean U3) and recorded NO accesses on the channel OBJECT, so
  programs gc's `-race` flags via the chansend-read/closechan-write
  pair passed the strongest (confluent) lane green — violating the
  doctrine's binding input "programs the race detector flags must fail
  closed in our model" (`docs/2026-08-04_nondeterminism-doctrine.md`),
  by the doctrine's own epistemics ("TSan has no false positives — one
  red report is proof"). Structurally invisible to every gate: the
  strict/confluent lanes never build with `-race` (fail-open confirmed
  at `go_run_oracle`'s race_flag condition), and the three summary
  sentences (raceWakeEvent's docstring, the doctrine's racy-lane
  caption, the design note twice) claimed "refusal-set agreement holds
  anyway" via the very mechanism that broke it, while Race.lean's U3
  row was the honest same-tree contradiction.
- Fix shape: model exactly gc's chan-object pair as a detector rule —
  a plain send records a chan-object READ at its apply position
  (commit, park, or panic alike — gc reads at entry), a successful
  close records a chan-object WRITE (gc panics on closed/nil BEFORE
  instrumenting); HB-unordered read↔write or write↔write on the same
  channel is `raceDetected`; recv records NOTHING (acquire-only).
  [The original fix-shape clause here — "select clauses record
  nothing (selectgo commits bypass chansend/closechan)" — was WRONG
  and is superseded by BUG-046: selectgo pass 1 racereadpc's every
  polled SEND case, so send clauses record poll reads; recv clauses
  stay acquire-only, which — with same-goroutine sequencing — is the
  actual reason selectSendClosedArrival and selectWakeClosed are
  TSan-green.] The
  three cases move to the racy lane (`go run -race` the justifying
  oracle); their close-adjacent behavior coverage is preserved by
  HB-ordered variants (close-after-send-drains, send-closed-recovered,
  recv-closed-drains-hb — race-free, probed 0/30 each). The
  close-WAKES-parked-sender panic arm (resumeThread) is reachable only
  through a `-race`-red shape — no HB edge can order a close after a
  send entry that then parks — so under DRF-SC it becomes
  detector-unreachable; the arm stays (it is the semantics the racy
  members traverse pre-refusal), recorded honestly at its site.

## BUG-044 — no scheduling point between a wake-producing registry op and main's terminal: the woken goroutine is discarded, its gc-realized continuation excluded (L1 envelope too narrow at main-exit — BUG-040's class)

- Status: fixed (2026-08-08, channels-arc audit response F2 — the L5
  MAIN-EXIT WINDOW: `execProgLoop` (and the driver mirrors
  `enumPoolRun`/`poolDFS`) draw a bound-2 pick at `mainOutcome?`-some
  with runnable goroutines left — 0 = exit now (the default; empty
  streams and single-thread pools unchanged, sequential conservation
  literal), 1 = one more ordinary `stepMulti`. The ∀-streams checker
  (`allStreamsOkPool`) certifies BOTH window branches (shared stepping
  core `stepAllBranchesOk`); soundness + mono re-proved; the fork-join
  designated statements are byte-identical and their `decide +kernel`
  certs recompute green at the same fuel 400. Both pinned cases flip
  PASS as status-diverse membership rows (`statuses=ok+panic` — the
  audit-F8 machinery landed with this fix), certifying exactly the
  gc envelope {ok, panic}. 14 existing enumeration-lane cases needed
  only sites/work recalibration (deeper trees; every certified
  observation set unchanged — probed per case before re-pinning).)
- Pinned-by: differential
- Cases: goroutines/wake-window/buffered-send, goroutines/wake-window/close-recv
- Discovered: 2026-08-08 (channels-arc final audit F2, major/comparative;
  verifier-reproduced end to end with fresh probes — model
  `observations=1` {ok} vs gc `-race` 200/200 panic, and PLAIN gc
  1/100 at a 50k-iteration post-close delay, 50/50 at 20M — the
  excluded member is realized by the unperturbed oracle)
- What: when main's registry op wakes a parked partner (a pairing
  handoff, a close) and main then reaches its terminal with no further
  registry op, the model offers NO scheduling point: `Config.atBoundary`
  marks the PRE-op config, the post-op `.next k` is not a boundary (the
  only post-op boundary is `.spawned`, BUG-040's fix), and
  `execProgLoop` classifies `mainOutcome?` BEFORE stepping — so the
  woken goroutine is discarded on EVERY stream and its observable
  continuation (a panic aborting the program) is excluded from the
  certified observation set. gc runs it: spec §Program execution gives
  no ordering between main's return and other goroutines' progress, so
  any finite number of woken-partner steps may precede teardown. TRUE
  SCOPE (dossier F2's scope correction): ANY main-goroutine registry op
  that makes a partner runnable, followed by main's terminal with no
  intervening registry boundary — not just close-wake. This falsified
  the matrix's O9/L5 "faithful main-exit" advantage rows as stated, and
  the slice-6 too-narrow debt list (design note) omitted it. The pinned
  cases are RACE-FREE (probed: `go build -race`, 0 reports/30 runs
  each), so the NPDRF carve-out does not excuse the exclusion, and the
  envelope is STATUS-DIVERSE {ok, panic} — which the membership lane
  could not even express (audit F8; fixed with this bug's fix).
- Fix shape: the MAIN-EXIT WINDOW — a bound-2 choice site in
  `execProgLoop` (and its driver mirrors) at `mainOutcome?`-some with
  runnable goroutines remaining: pick 0 = exit now (the default, so
  empty/default streams and sequential conservation are untouched —
  a single-thread pool has no runnable others and consumes nothing),
  pick 1 = one more pool step (the ordinary `stepMulti`, L1 pick and
  all). The relation side needs NO change: `StepM`/`schedPick` already
  admit post-main-terminal steps of runnable goroutines — the driver
  was the narrow side. Membership lane gains status-diverse envelopes
  (`statuses=` param / `--expect-status` list) to express {ok, panic}.

## BUG-043 — range-over-integer desugar hard-codes the default int kind for the loop variable and index arithmetic

- Status: fixed (2026-08-07, channels-arc-maint — the frontend emits
  `operandType` (the operand's underlying integer kind, `emitBasic` of
  the already-Underlying basic; the array-pointer static-length form
  carries int) and the decoder threads it through
  `$ridx`/`$rlen`/loop-variable/increment, failing closed on a
  missing/non-integer operandType. Same commit: the incdec arm's
  absent-type default removed (fail closed, the float-literal
  precedent). All 3 pinned cases flip PASS; conversion control stays
  green.)
- Pinned-by: differential
- Cases: range/int-kind-arith/uint8-arith, range/int-kind-arith/defined-arith, range/int-kind-arith/int8-arith
- Discovered: 2026-08-07 (maint-check pre-merge review M1, verified
  against go run: 21368 vs stuck; found auditing BUG-042's family —
  the unexercised-path class)
- What: for `for i := range n` over an integer, the spec gives the
  iteration variable the OPERAND's type (§For statements), but
  `decodeRange`'s index-loop desugar (GoLean/NativeToIR.lean, the
  slice/array/int/array-pointer arm) declares `$ridx`/`$rlen`/the
  loop variable at the default int kind and increments with an
  int-kinded 1 — and the frontend (tools/nativefrontend/emit.go,
  range emission, `*types.Basic` integer case) emits NO operand kind
  on the wire at all, so the decoder has nothing to key off.
  Arithmetic on the loop variable in the operand's kind
  (`i * 2` with i uint8) is a mismatched-kind STUCK. RELATED to
  BUG-042 (kind-defaulting family) but a BROADER mechanism: the wire
  carries no kind and the decoder hard-codes `.int`, so it bites
  UNNAMED non-int kinds too (BUG-042's incdec facet passed its
  unnamed control). Stuck-not-wrong (fail-visible): comparisons and
  map-key lookups are kind-blind, which is why the conversion-only
  shape (`range/range-int-typed`, green since it converts with
  `int(last)` before any arithmetic) never exposed it — the corpus
  gap was the arithmetic-in-kind shape, now pinned with its
  conversion-only control (`range/int-kind-arith/conversion-control`).
- Fix shape: the frontend emits the operand's underlying integer kind
  (`operandType`) for range-over-int; the decoder threads it through
  `$ridx`/`$rlen`/loop-variable/increment and FAILS CLOSED on a
  missing/non-integer operandType (the incdec precedent — silent
  int-defaulting is this defect class).

## BUG-042 — IncDec desugar's synthetic 1 takes the default int kind instead of the operand's underlying kind (defined types; map values of any non-default kind)

- Status: fixed (2026-08-07, channels-arc-maint — both desugar sites
  resolve the carried kind through `Underlying()` mirroring
  `emitConstValue` (`emitIncDec` keeps the substitution-aware `typeOf`
  path for non-basic underlying, i.e. type parameters outside a
  stencil); the decoder's incdec arm now FAILS CLOSED on a non-numeric
  carried type instead of silently defaulting to int. All 11 pinned
  cases flip PASS; unnamed control stays green.)
- Pinned-by: differential
- Cases: ints/defined-incdec/inc-signed, ints/defined-incdec/dec-signed, ints/defined-incdec/inc-unsigned, ints/defined-incdec/dec-unsigned, ints/defined-incdec/inc-signed-wrap, ints/defined-incdec/dec-signed-wrap, ints/defined-incdec/inc-unsigned-wrap, ints/defined-incdec/dec-unsigned-wrap, floats/defined-incdec, maps/incdec-value-kinds/uint8, maps/incdec-value-kinds/defined
- Discovered: 2026-08-07 (external: the grossmith differential
  generator, seed 559 minimized — docs/2026-08-07_grossmith-findings.md
  §1; probes here widened the family to the map facet)
- What: two sites of one family — the IncDec desugar's synthetic 1
  literal is kinded from the wire `type` field, and that field is not
  resolved through defined types to the underlying basic kind:
  (a) `emitIncDec` (tools/nativefrontend/emit.go) carries
  `e.typeOf(st.X)`, which for a defined type is `{"kind":"named"}` —
  the decoder's `intKindOfOptType` (GoLean/NativeToIR.lean) silently
  falls to the default `int`, so `T1(5)++` (T1 int8) desugars to an
  int8 + int add and the machine goes STUCK ("mismatched + integer
  kinds: int8 and int"). Hits every defined integer AND float type,
  inc and dec, with and without wrap; the unnamed control passes
  (kind picked up when the type is unnamed), which localizes the
  defect. (b) `emitMapCompound` synthesizes a default-int 1 for every
  non-float map value type, so `m[k]++` over even UNNAMED uint8
  values — or any defined-type values — is stuck the same way (the
  floats slice F3 fixed only the float kinds at this site).
  Both are stuck-not-wrong (fail-visible), past the frontend gate:
  machine/lowering defects per the fail-closed doctrine, not
  frontend-export coverage gaps. Same site family `emitConstValue`
  already resolves for defined-typed literals (`tv.Type.Underlying()`).
- Fix shape: resolve the carried kind through `Underlying()` at both
  desugar sites (frontend), mirroring `emitConstValue`; tighten the
  decoder's incdec arm to fail closed on a non-numeric carried type
  instead of silently defaulting.
- Scoping correction (2026-08-07, maint-check M1): "two sites of one
  family" was incomplete — a third, RELATED kind-defaulting site
  exists in the range-over-integer desugar, with a broader mechanism
  (the decoder hard-codes `.int` and the wire carries no kind at all,
  so it bites unnamed non-int kinds too, unlike this bug's incdec
  facet whose unnamed control passes). Filed separately as BUG-043.

## BUG-041 — race-detector footprint over-approximation: value-path composite reads are whole-cell (array elements; non-fieldGet uses), refusing race-free programs

- Status: open — NARROWED 2026-09-02 (Q-RACEPATH, RULED [USER]
  2026-08-31 `docs/2026-08-31_qrow-rulings.md` row 4; implemented on
  the Tier-4 detector-soundness lane): the CONSTANT-index half is
  FIXED — `projChainTarget` (Race.lean, the generalization of the
  shipped `fieldChainTarget`) narrows a whole-cell read through
  `indexGet` frames whose pending index is an `intLit` over an ARRAY
  cell, composing with the `fieldGet` chain in either order (`a[1]`,
  `a[1].x`, `s.arr[1]`); the former red pin `race/free/array-read-write`
  flipped FAIL→PASS (confluent, |set|=1 certified) with two chain-form
  green guards (`race/free/{array-const-index-field,
  field-array-const-index}`) and two must-stay-racy guards
  (`race/negative/{array-const-index-same-elem,
  array-const-index-whole-write}`: the narrowed element read still
  conflicts with a same-element write and with a whole-array write).
  What REMAINS OPEN is the DYNAMIC-index residual below.
- Pinned-by: differential
- Cases: race/free/array-dyn-index-read-write
- Discovered: 2026-08-07 (S3 pre-merge audit, major finding 3 — the
  original record named only `evalVar` and shipped write/write-only
  free-lane guards, so the read/write direction that actually trips
  was neither scoped nor pinned)
- What: `stepAccesses` records a WHOLE-CELL read when a composite
  value is materialized (`evalVar` on a composite local; `.deref` of a
  composite pointee), so an interior read overlapping a concurrent
  DISJOINT-path write refuses a `-race`-green race-free program. The
  S3 audit response NARROWED the dominant class — a read delivered
  straight into single-operand `fieldGet` frames records only the
  projected field path (the then-named `fieldChainTarget`, since
  Q-RACEPATH `projChainTarget`; covers `p.a` on struct
  locals and on `*struct`, green-pinned by
  `race/free/{field-read-write,ptr-field-read-write}`) — leaving
  exactly: value-path ARRAY-element reads (`a[1]`: the index operand
  is unevaluated when the base cell is read, so no continuation
  narrowing exists) and composite reads whose continuation is not a
  fieldGet chain. Over-refusal is the FAIL-CLOSED direction (a
  refusal, never a wrong value), recorded as O1 in
  `GoLean/GoCore/Race.lean`'s inventory.
- RESIDUAL (the open half, born-FAIL pin 2026-09-02
  `race/free/array-dyn-index-read-write`: `a[i]` with i = 1 beside an
  `a[0]` write — race-free Go refused): when go/types cannot fold the
  index to a literal, the element path is undetermined at the base
  read and the read stays whole-cell. Fail-closed (over-refusal, never
  a missed race). Fix shape for the residual — memo §4 option (B),
  deferred-footprint recording (delay the composite read's footprint
  until the projection applies, with the EVALUATED index; the panic
  window between base read and projection needs its own footprint
  argument; fail-closed on every unrecognized shape) — effort M,
  touching the `stepAccesses` architecture. RE-OPEN TRIGGER (ruled
  with the narrowing): a real target exhibiting dynamic-index
  DISJOINTNESS on a value-path ARRAY; raft's hot indexing is on
  SLICES, whose element reads are address-based and already precise.
  (The pre-fix "Fix shape" — provenance-carrying array values or
  frontend address-based element reads — is superseded by the ruling.)
- S3 convergence addendum: the class gained a FRAME-ENTRY member and
  its narrowing — a needsDeref dispatch to a synthesized promotion
  wrapper is narrowed to the wrapper's hop path
  (`race/free/promoted-ptr-box` green, `race/negative/
  {promoted-dispatch,iface-dispatch}` red guards); wrapper shapes the
  extractor does not recognize (embedded-POINTER hops, non-synthesized
  bodies) fall back to the whole-pointee read and belong to this
  entry's over-refusal envelope (no corpus case constructs one yet —
  a future embedded-pointer-hop promotion case through a *T box would
  land red here, never silently wrong).

## BUG-040 — no POST-SPAWN reschedule point: a child can never run before a sync-free parent segment (L1 envelope too narrow; exit-no-sync races undetectable)

- Status: fixed (2026-08-07, slice 4 — the anticipated-by-D8 fix:
  `spawnStep` leaves the parent on the new `.spawned k` Config marker,
  a registry boundary of its own (`Config.atBoundary`), whose only
  step is the pool-level strip to `.next k` (`stepThread`; relation
  rule `StepM.spawned`, mirrored in `StepMFine`; `stepFn` fails closed
  `.internal` on it — pool-only). The "who runs after the fork"
  decision is therefore a real L1 consumption site, the child CAN
  preempt a sync-free parent segment, and the exit-no-sync race class
  is detectable: the `GoCore race BUG-040` eval pins flipped — stream
  [1] now refuses `race` (child-first), the empty stream keeps the
  value leaf (main-first, gc's dominant corner). Pinned-stream shift,
  as predicted: the three designated fork/join witnesses'
  STATEMENTS (shapes AND literals) survived unchanged — every stream
  still completes `.normal`/42 — but the schedules those literals
  realize moved and were re-derived by probe; the distinctness
  argument is re-recorded in GoldenForkJoin.lean. Full corpus:
  ZERO drift on all 1173 prior ids under the new boundary (the empty
  stream's pick-0 defaults preserve the lowest-index-runnable
  schedule). The arc-end Comparator landmark certifies the (textually
  unchanged) designated set over the changed machine.)
- Pinned-by: none (eval pins `GoCore race BUG-040 …` in
  Tests/GoCoreEval.lean: stream [1] refuses race, stream [] is the
  value leaf; a differential case cannot pin the class — the
  gc scheduler realizes the same main-first corner ~always, so `go run`
  and `go run -race` agree with our value leaf, 0/700-style —
  validation note §3's mainfirst measurement is exactly this shape)
- Discovered: 2026-08-07 (slice-3 detector work, by reasoning — the
  green gates structurally cannot see it, the audit dimension's
  "unexercised paths" class)
- What: `Config.atBoundary` marks the PRE-fork spawn position, so the
  scheduling decision at a `go` statement happens while the child does
  not exist yet (|runnable| = 1 beside a running parent — no pick).
  After the fork the parent's post-spawn config (`.next k`) is not a
  boundary, so the parent runs privately to its NEXT registry op. A
  parent whose remaining segment contains no channel/select op —
  the exit-no-sync class, `raceExitNoSyncMain_F`: `go func(){ x = 7 }();
  return x` — can therefore NEVER be preempted by its child on any
  stream: the child-first interleaving (legal Go — the spec makes no
  scheduling promise) is outside the modeled envelope, and the race
  detector, which is complete only over accesses that EXECUTE on the
  chosen path, sees a value leaf on every stream.
- Why it matters: (a) L1 envelope too narrow — the
  theorem-transfer-breaking direction; (b) it breaks the racy-refusal
  coupling the NPDRF reduction needs ("programs outside DRF are exactly
  those the machine refuses") for races reachable ONLY via a post-spawn
  preemption; the slice-4 enumerator's lane-d claim "every enumerated
  path refuses" is scoped to the registry-point path set until fixed.
- Fix shape (deliberately NOT patched in slice 3 — charter stop
  condition): a post-spawn scheduling decision (e.g. a pool-level
  `spawnedK` boundary strip, or a fork-then-pick `stepMulti` arm). ANY
  form adds a `Choices` consumption site at |runnable| > 1, which
  SHIFTS every pinned stream — including the three pinned-stream
  fork/join designated witnesses (statement restatement → needs its own
  sign-off + Comparator landmark) — and reworks the
  `StepM`/`stepMulti` correspondence. Schedule together with the
  slice-4 enumerator, which needs the same machinery to enumerate the
  child-first paths at all.

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

- Status: fixed (2026-08-09, spec-parity-s1 — the assignment-spine laws
  slice: the round-4 machine migration re-applied (RhsOp/applyRhsOp;
  `StmtOp.mapLookup`/`.typeAssertStmt` removed outright; the comma-ok
  forms enter tgtOpK via `mapLookupFirst`/`typeAssertFirst` with the
  source applied at the end of phase 1) AND the anchoring law family
  restated over the spine in the same movement: `wp_map_lookup`
  (`Laws/StmtOps.lean`) is now the value-source apply (map read) plus
  two `storeK` store lifts with UNCHANGED premises, the spine entry is
  `wp_map_lookup_start` (witnessed by the reworked
  `wp_map_lookup_ackedIndex_entries` walk in GoldenQuorumPin), and the
  quorum walks (WP/Three/All + the registered one-entry law) re-prove
  with their statements unchanged. The `typeAssert` spine entry has NO
  WP law yet — deliberately, a law without a witness is a scaffold; it
  lands with its first consumer. Race.lean lockstep: the
  mapLookup/typeAssertStmt footprint rows retired, the `rhsK`-apply map
  read added. Both pins flip PASS.)
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

- Status: fixed (2026-08-09, spec-parity-s1 — the assignment-spine laws
  slice: the round-4 machine migration re-applied (`assignFirst` — a
  single assignment rides tgtOpK/rhsK/storeK as a one-target
  multi-assign; the `assignTargetK`/`assignStoreK` frames and their
  five rules removed outright) AND the anchoring WP assignment law
  family restated over the spine in the same movement:
  `wp_assign_start` enters the spine, the new pure step laws
  (`wp_tgtop_shift`/`wp_tgtop_next`/`wp_tgtop_rhs`/`wp_rhs_shift`/
  `wp_rhs_stores_vals`/`wp_stores_done`, all registered `go_walk`
  laws) cover phase 1 and the phase transitions, the store lift is
  `wp_store_target` (general chain replay; `wp_assign_store_loc`/
  `wp_assign_store` keep their `storeLoc`-shaped premises as bare-chain
  instances), and the generic-continuation drain is
  `wp_stores_done_nil` via the empty-splice absorber `wp_seqCont_nil`
  (`Laws/Control.lean`). The `wp_assign_lit` non-vacuity witness
  re-proved as the full spine walk with its statement's `Config.next k`
  post intact; every golden/loop/range/unwind walk re-proved. All
  three pins flip PASS.)
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
  takes a different path (index-GET) and remained in the untriaged
  ledger until 2026-08-19, when the 19-red GoCore slice (triage
  L5+L6) gave `.indexGet` the matching `.addr` auto-deref and `.nil`
  panic arms — both read-position cases now PASS.)
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

- Ruling 2026-09-05 ([USER], relayed via the [AGENT] coordinator; no status change): E13's four-way treatment RULED (b) — the A6 residual refusal (`panicky-between` and kin) retires into a membership shape admitting both orders where the spec leaves them unsequenced; `docs/2026-08-11_latitude-inventory.md` E13, lane `e13-b`.
- A6 AMENDMENT (2026-08-31, t1-fidelity-fixes — the over-refusal
  retirement this entry's F23 paragraph priced): the refusal is
  narrowed to its TRUE residual. The predicate is now sweep-scoped
  (BUG-062's fix, `sweepOrderedEventAfter`): with NO ordered event
  after the builtin in its sweep, len stays inline and realizes gc's
  left-to-right point — so `iv.(int) + len(b[j])` is now GREEN with
  gc's interface-conversion panic whether or not a dead receive exists
  anywhere in the function, and the four standing over-refusal rows
  flip PASS (the Cases below, all oracle-matched). With an event after,
  the hoist is taken unless BOTH the residual operand can panic
  (`residualPanicFreeOperand` — real calls hoist out first, retiring
  the F23 `len(f())` instance) AND potentially-panicking INLINE
  material sits to the builtin's left (`sweepPanickyInlineBefore`);
  only that composition still needs the unbuilt full-statement
  linearization and still fails closed, pinned red-by-design at
  builtins/len-vs-call-order/panicky-between. The
  channels/recv-order/dead-recv-len-operand row this entry called a
  permanent refusal marker is that marker no longer — it pins the
  inline realization green instead. NOT A PURE NARROWING (B-3
  correction, 2026-09-01 audit fix round): the sweep-scoped predicate
  fires on CALLS as well as receives, so receive-FREE functions —
  which the fnHasRecv trigger never touched — GAINED the refusal on
  the panicky composition (panicky operand x panicky inline left x
  ordered call after), while the silent wrong answer the old scope
  shipped in exactly those functions (inline len reading post-call
  state, BUG-062's forced-point divergence) DIED. Trade stated: new
  visible refusals on one rare composition in receive-free functions,
  in exchange for retiring a spec-FORCED silent wrong answer; the
  four flipped Cases rows measure the retirement side only.
- FR-28 AMENDMENT (2026-09-04, lane `fr27-fr28`, [AGENT] under the
  [USER]-ratified frontier queue, relayed): the mechanism GAINED a
  consumer and a refinement, its residual is unchanged in kind. (1) The
  predicate pair is now `hoistReordersPanic` (emit.go) and `emitMake`
  calls it over every size/hint operand — BUG-083's make shapes refuse
  by name instead of realizing the hint's panic first (BUG-083, now
  fixed-as-refusal, has the table and the E13 tension note). (2)
  `residualPanicFreeOperand` recurses into an INLINE builtin's operand
  (`len`/`cap`: `len(b[j])` as a make size or an outer len's operand is
  not a hoisted temp — a hole the F23 call arm left, closed; row
  `make-inner-len`). (3) NIL-DEREF TRANSPARENCY: when the hoisted
  operand's residual AND every panicky inline node to its left can
  panic ONLY by nil dereference (`nilDerefOnlyResidual`;
  `sweepPanickyInlineBeforeKinds` reports the census), the hoist is
  taken — the two candidate panics are the same runtime error
  ("invalid memory address or nil pointer dereference": one
  runtime.Error, no site-specific text, the machine's panicking family
  emits the same text at every deref site) and the inline material
  between them is pure by construction (calls/receives hoisted), so
  which nil test fires first is unobservable: some nil-deref panic fires
  iff some pointer on the path is nil. This lowers the lexer idiom
  `for l.pos < len(l.src) && l.peek() != '\n'` (cedar-go x/exp/schema/
  internal/parser token.go:119, census §11's FR-28 witness — the
  `drv-validate` driver now passes it and stops at an `fmt.Errorf` verb
  instead). Pinned green on every nil-ness combination (`len-nil-only-
  {none,left,operand,both}`, `make-nil-only-*`, `lexer-idiom`); the arm
  is nil-deref ONLY — an assertion or an index on either side keeps the
  refusal (`len-assert-vs-nil-operand`, `len-nil-left-vs-index-operand`,
  red by design). (4) A MAP read whose key type contains NO interface
  anywhere (`containsInterface` — audit fix round F1, 2026-09-05: the
  first cut tested the top-level type only and admitted `struct{v any}` /
  `[1]any` keys, whose hash can panic — a wrong answer on the make path
  and a REGRESSION of this entry's refusal on the len path, `iv.(int) +
  len(nm[k]) + wit(5)`, both closed; BUG-083 has the rows) is panic-free
  to `panicFreeOperand` and the sweep census (spec#Index_expressions:
  zero value on a missing key or nil map).
  The `panicky-between` pin is unchanged (assert left, index operand).
  What REMAINS of this entry's residual after FR-28: exactly the
  refusal — a panicky operand between panicky inline material to its
  left and a later ordered event (len/cap) or an unconditional hoist
  (make), where the two panics differ in kind; realizing gc's point
  there is still the unbuilt linearization. Ledger FR-28 is PARTIALLY
  CLOSED on that basis.
- M1 AMENDMENT (2026-09-02, bug082-maphint audit fix round, [AGENT]) —
  SUPERSEDED 2026-09-04 by the FR-28 amendment above (the `make` hoist
  now carries the A6 guard; `hint-panicky-between` is a frontend-export
  refusal, not a differential red; BUG-083 is fixed AS A REFUSAL, no
  longer open) — the paragraph is kept as history and its "pinned
  red-by-design at stage differential (a wrong answer, not a refusal)"
  and "BUG-083 (open)" clauses no longer describe the tree:
  the class gained INSTANCES, not a mechanism. `make(...)` ALWAYS
  hoists (a statement-level allocation) with no A6 guard
  (`residualPanicFreeOperand` × `sweepPanickyInlineBefore` is wired
  into `len`/`cap` only, not `emitMake`), so a panicky size/hint
  operand is evaluated ahead of a spec-UNORDERED panicky operand to
  its left. Pre-existing on main for `make([]T, t[k])`, `make(chan T,
  t[k])` and for PLAIN CALLS (`iv.(int) + boom()`: gc realizes the
  interface-conversion panic, the machine `boom-call`); BUG-082's fix
  ADDED the map-hint instances `iv.(int) + len(make(map[int]int,
  t[k]))` and `iv.(int) + len(make(map[int]int, boom()))` — main was
  right on exactly those two only because it dropped the hint, while
  it was WRONG on five sibling shapes the fix made right (a left index
  / division / nil-deref panic vs a hint index panic, where gc too
  realizes the hint's panic first — gc hoists the `make`). The full
  gc-vs-machine table: docs/evidence/2026-09-02_bug082-maphint/README.md
  §M1. gc's realization is compiler-internal (the interface-conversion
  panic on the left is the ONE left-operand class gc orders ahead of a
  hoisted make/call); both points spec-legal; the shared fix is the
  full-statement linearization this entry records as deliberately not
  built. Extending the A6 guard to `emitMake` would newly REFUSE the
  pre-existing slice/chan shapes — a separate arc, NOT done in the
  records-only fix round. Pinned red-by-design at stage differential
  (a wrong answer, not a refusal) by
  builtins/len-vs-call-order/hint-panicky-between, which lives on the
  Cases line of BUG-083 (open) because check-bugs (3) forbids a FAIL
  row on a fixed differential entry — BUG-083 is this class's open
  instance ledger; this entry stays its owner.
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
  built). Amendment widened again at the S1 delta review
  (spec-parity-s1, 2026-08-09): the class has a THIRD axis —
  INTER-TARGET phase-1 operand order (target-vs-target, distinct from
  the targets-vs-RHS axis above): for `aa[5][0], b[*pn] = f6()` (and
  the untouched assignMany twin `aa[5][0], b[*pn] = 42, 7`) gc
  reports the SECOND target's operand panic and we the FIRST's, and
  the answers FLIP when the targets are swapped — pinning it as
  ordering, not deref priority. At three panicking targets gc picks
  the MIDDLE one (`aa[5][0], cc[9][0], dd[7][0] = f8()` → gc
  `[9] with length 3`), so gc's realization is neither left-to-right
  nor right-to-left but compiler-internal (go1.26.5, stable under
  `-gcflags=all="-N -l"` — not an optimizer artifact; reviewer probes
  `.tmp/probe052/case12,13` genres, verifier-reproduced
  independently). Both realizations spec-legal (§Order of evaluation
  orders only calls/receives/binary-logical, and the frontend hoists
  calls out of target operands, so the divergence CANNOT escape panic
  selection into side effects — probed); pre-existing on the
  assignMany, receive, and call-write-back paths alike; UNPINNABLE
  (gc's order is compiler-internal and hence fragile to pin), so
  recorded as OPEN envelope per this entry's precedent — no pin, and
  the BUG-052 call-order pin explicitly does NOT cover this axis (the
  rule-site latitude block's SCOPE clause). Amendment widened at the
  2026-08-06 final check: the class
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
  equality.) **CORRECTION (2026-09-02, [USER] ruling — Mike: "agree
  we should mark as a gc deviation, and record in our gc bug
  backlog"):** the early-STORE manifestation's "Both spec-legal"
  verdict just above is WITHDRAWN. spec#Assignment_statements' two-phase
  sentence is normative (every store after every operand evaluation);
  spec#Order_of_evaluation's list of ordered events governs the order
  WITHIN phase 1 and does not license a phase-2 store inside it. gc's
  own regression test `deps/go/test/fixedbugs/issue43835.go` asserts
  no early store under a recovered panic; its fix (walk/assign.go
  `ascompatee`) covers result parameters and `return` only — the
  observed early store on ordinary locals is an aliasing optimization
  leaking through `recover`; and BUG-075 (fixed 2026-09-01) treats the
  machine's own identical early store at `return` as a wrong answer
  under the same sentence. The machine's behaviour here (x stays 0) is
  the FORCED point, not one of two legal members; gc's is a DEVIATION,
  recorded as `docs/spec-divergence-ledger.md` **L-016** (gc-bug,
  UNFILED) with the reproducer matrix at
  `docs/evidence/2026-09-02_e5-gc-deviation/`. Inventory row E5 is
  re-classed (c) FORCED and its re-envelope obligation withdrawn; "no
  pin / membership treatment" above stands for the reason L-014's does
  — a strict row would pin gc's WRONG answer — not because either
  answer is legal. The panic-SELECTION axes (E3/E4, the paragraph's
  first half) are unaffected: still both-legal, still open envelope.
  Analysis [AGENT] (grossmith campaign-3 verifier, 2026-09-02); the
  class call [USER].
- E13-b AMENDMENT (2026-09-05, lane `e13-b`, [USER] ruling (b) relayed
  — design `docs/2026-09-05_e13-b-design.md`): THE RESIDUAL IS GONE.
  The A6 guard (`hoistReordersPanic` = `residualPanicFreeOperand` ×
  `sweepPanickyInlineBeforeKinds`, the nil-deref transparency arm, and
  the `emitMake` wiring FR-28 added) is DELETED: the composition it
  refused — a panicky hoisted operand beside panicky inline material to
  its left — is spec-UNSEQUENCED, and the frontend now emits an
  `unseq-probe` at the left material's lexical position so the machine
  realizes BOTH orders (`ChoiceSite.unseqPanic`). "Realizing gc's point
  needs full-statement linearization" was the wrong target: gc's point
  is ONE member (early for assertions, late for index/deref/division/
  shift/conversion); the envelope is the product. `panicky-between`
  (this entry's red-by-design pin) LOWERS and PASSes strict — its
  witness is 0 under both orders (a singleton set); `len-nil-left-vs-
  index-operand` and `len-assert-vs-nil-operand` likewise (their left
  operands cannot panic at run time); the rows whose two orders differ
  are membership rows on BUG-083's Cases line. The FORCED half —
  `sweepOrderedEventAfter`'s hoist of `len`/`cap`/`min`/`max` when an
  event follows (BUG-062) — is unchanged, and the four Cases rows below
  keep pinning the inline realization green. Latitude E6 (this entry's
  refusal, as the inventory listed it) is RETIRED into E13.
- Pinned-by: differential (since the 2026-08-31 A6 amendment above:
  the once-refused rows now pin the inline realization green; the
  refusal shape that survived A6 and FR-28 was RETIRED 2026-09-05 —
  the E13-b amendment above)
- Cases: channels/recv-order/dead-recv-len-operand, channels/recv-order/dead-recv-len-embedded, bools/short-circuit-funclit/e6-recv-len-in-sc, bools/short-circuit-funclit/e6-recv-len-outside, builtins/len-vs-call-order/panicky-between, builtins/len-vs-call-order/len-assert-vs-nil-operand, builtins/len-vs-call-order/len-nil-left-vs-index-operand
- E13-b AUDIT FIX ROUND AMENDMENT (2026-09-05, [AGENT] worker; findings
  R1/R2/R3 of the lane's adversarial audit): (i) the three len-path rows
  the e13-b re-pin flipped FAIL→PASS (`panicky-between`, `len-assert-vs-
  nil-operand`, `len-nil-left-vs-index-operand`) are on THIS Cases line
  now — the re-pin's "every id on a Cases line" was false for them (they
  sat in this entry's prose only; R3). (ii) The retirement above was
  OVER-WIDE: the first cut deleted the whole A6 family, and the
  composition it refused lowered as a SILENT single-member answer ≠ gc
  wherever the left material is NOT probed — the envelope's `emitExpr`
  hook never fires on an assignment/IncDec/compound TARGET operand
  (`x[iv.(int)] = len(b[j]) + wit(5)`: gc the interface conversion, the
  machine `index out of range [5]`), an address-of operand, an operand
  containing `recover()` (`r = recover().(int) + len(b[j]) + wit(5)` in a
  defer) or an allocating conversion (`[]byte(s)[i]`, R7). A NARROWED A6
  guard is reinstated at exactly that boundary (emit.go
  `hoistReordersUnprobedPanic` = `residualPanicFreeOperand` [verbatim] ×
  `unprobedPanickyBefore` [the old census MINUS every node that carries
  a probe, `probedNodes`] with FR-28's `nilDerefOnlyResidual`
  transparency [verbatim]): the len/cap arm and `emitMake` refuse BY
  NAME (`… hoisted past UNPROBED panicky material to its left …`) where
  the hoist would realize only the events-first order the spec does not
  fix; where the left material IS probed the two-member envelope stands.
  The map-assign target path had been left probed against design §4 D4
  — one rule for every target now (`m[iv.(string)] = …` refuses like a
  slice target; the twin's `ro.acks[from] = max(…)` loses its probe). The
  rows are red by design: `builtins/e13-sibling-panic-order/{tgt-assert-
  vs-len-hoist,compound-assert-vs-len,map-key-assert-vs-len,recover-
  assert-vs-len,bytes-conv-left-len-hoist,tgt-assert-vs-make}` — on
  BUG-102's Cases line (the designed-red entry with `Expect: FAIL`; this
  entry stays `fixed` with a PASS-only Cases line, as the check-bugs
  invariant requires). (iii) STRUCTURAL ALLOCATIONS (R2): a `&T{…}`,
  elided `&T`, slice or map literal, or an interface method value hoists
  to its lexical position and evaluates its PAYLOAD there, ahead of every
  ordered event lexically after it; gc evaluates the payload in the
  residual, AFTER the calls (`(&T{x: s[i]}).x + wit(5)`: gc prints `wit
  5` then panics; the machine panics before the call, on every stream —
  the probe on `s[i]` cannot reach gc's member because the allocation
  statement re-raises a deferred panic at the same early position).
  Pre-existing on main (the hoist order was emission order there too),
  undisclosed under an axis the lane declared discharged; refused by name
  since the fix round (`structuralAllocGuard`: panicky payload + an
  ordered event after the literal) — `{composite-ptr-payload-vs-call,
  slice-lit-payload-vs-call}` red by design on BUG-102's line; the no-event,
  event-inside-the-literal (`assert-composite-lit`) and variadic-pack
  shapes lower. Design `docs/2026-09-05_e13-b-design.md` §4 D4/D5, §6;
  ledger FR-28 (REOPENED, narrowed); inventory E6/E13.
- Discovered: 2026-08-06 (channels-arc-s1 convergence round, verified —
  severity minor: both realized orders are spec-legal, but the
  justifying claim in BUG-023/BUG-026 and wire.go was FALSE and the
  trigger is non-local)

CLASS REACH, stated plainly (arc-final audit F23, 2026-08-08 — the
record stated the predicate but never calibrated its reach, and the
"deferred until a real target needs the shape" framing read as an
exotic dead-receive shape): the refusal fires on `len`/`cap` of
ANYTHING other than a bare identifier, a literal, or a non-indirecting
selector chain, anywhere in a function containing ANY receive
(`fnHasRecv` is function-scoped) — i.e. the idiomatic `len(p.xs)`
(pointer receiver/param), `len(g[i])`, `len(f())`, `len(s[1:])`, and
even the provably-panic-free `len([]byte(s))` (the predicate is
conservatively syntactic; the "potentially-panicking" message
over-states for that shape). The audit's verifier hit it on the first
naive composed program. AMPLIFICATION (audit F21 — the composition is
arc-new even though both halves predate it): methods have NO per-decl
quarantine (emit.go's `d.Recv == nil` gate; mono.go's stencil twin),
so this refusal inside any METHOD kills the WHOLE package export —
and receive-bearing decls in etcd-io/raft are 12/12 METHODS (verifier
AST scan), so the import lane's blast radius is per-package, not
per-declaration. Mitigating datum, also verified: ZERO of those raft
methods contain any len/cap call today, so the deferral holds for the
north star — but the goose-parity import lane should expect this
cliff (pointer from `docs/2026-08-07_goose-comparative-scoping.md`'s
refusal-class list).

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

- Status: fixed (2026-08-09, spec-parity-s1 — the assignment-spine laws
  slice, movement B2, completing the round-4 FIXED half (`assignMany`
  on the spine since the convergence round): the multi-value CALL
  write-back path migrated onto the tgtOpK/storeK spine — target
  checks deferred to the stores, stores left-to-right one per step,
  each check firing at its own store after the call's effects and
  earlier stores landed; frame-exit `storeMany` retired (the
  targetless resultless exit stays a single unchanged step; a
  targetless frame with pinned results stays stuck-closed as before).
  TIMING SCOPED HONESTLY at the same round's audit (BUG-052): the
  first landing of this migration evaluated the target OPERANDS before
  the call — spec-§Assignments-shaped but inside §Order of
  evaluation's UNSPECIFIED call-vs-operand carve-out, where gc
  deterministically realizes CALL-FIRST — so the shipped shape is:
  the call evaluates first (args, frame), the caller-target PLANS ride
  `Cont.frame` with the caller env, and the operands evaluate at frame
  EXIT through the tgtOpK spine (`frameReturnTargets`/
  `frameFallTargets` — the receive path's delivery shape), then the
  `storeK` stores. The pinned latitude is recorded at the rule site
  (Machine.lean, PINNED LATITUDE block). Laws restated over the final
  shape (`wp_call_start`, `wp_call_enter_ret1` at the call-statement
  config, `wp_tgtop_stores`, the frame-exit family with post-call
  `hres` operand premises + the `wp_stores_done_nil` drain), cell
  pre/posts unchanged; every golden/quorum consumer re-proved. All
  three pins flip PASS, and the BUG-052 timing pins guard the order.)
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

ADDENDUM 2026-09-05 (lane `fr19-bug097` audit fix round R20 [AGENT]): the same
guard sits ONLY at the observation boundary (`CLI.lean` `goValueJson`'s struct
arm); `Ty.dynamicName` (`GoLean/GoCore/Value.lean`) still passes every synthetic
key through `TypeId.unqualified` — `any` → `any`, `struct{}` → `struct{}`,
`$runtime.Error` → `Error` — into the `dynamic` field of an interface
observation. For `any`/`struct{}`/`interface{…}` this is unreachable as a box's
dynamic type (a dynamic type is concrete) and reachable only inside composite
spellings (`*any`, `[]struct{}`) where the Go harness refuses first (`Name()` of
an unnamed type is `""`, `coverageharness` fails closed) — a refusal, not a
wrong answer. For `$runtime.Error` it IS reachable and IS wrong: a recovered
runtime error returned as `any` observes `dynamic:"Error"` where gc's is
`boundsError` — measured and filed as its own open bug with a red pin,
**BUG-099** (the payload's VALUE differs too: gc's concrete struct vs the
machine's message string). Owed here: fold the synthetic-key guard into ONE
place both channels use (the boundary refusing by name for a synthetic
dynamic), not a second special case in `dynamicName`; sequenced with BUG-099's
payload model, since a correct `dynamic` needs the concrete type.

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
  refusal of the type-ARGUMENT direction.) (ADDENDUM 2026-09-05, lane
  `fr19-bug097` [AGENT]: the key is now `main.box·N[int]` — the FR-19 scope
  ordinal before the instantiation bracket; `TypeId.unqualified` strips
  both the qualifier and the ordinal, so the observation stays
  `box[int]`; the display record is gc's `main.box[int]`. The
  parameterization applies only to a type declared INSIDE the stencil's
  declaration (`declaredInActiveStencil`), not to every local type the
  stencil mentions — the first cut of this fix parameterized a stencil's
  OWN local type ARGUMENT and hit C6 on it. `generics/local-type-argument`
  is green since the same day (BUG-092).)
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

- Status: fixed
- Closed: 2026-08-20 (raft W4.1 item 5, branch `raft-w41` — found LIVE
  by the first RawNode probe: tracker.Config.Clone returns nil at the
  defined map type quorum.MajorityConfig and checkInvariants' map
  comparison stuck the machine on two raw nils)
- Fix: the SECOND shape the entry below envisioned — a defined-type-
  aware typed-nil emission, realized in the FRONTEND: the BUG-016
  nil-typing arm (wrapInterfaceConversion) now classifies by the
  target's UNDERLYING kind and emits the UNDERLYING type's wire node,
  so a defined-slice/map/pointer slot receives the same typed nil an
  unnamed one always did (representation only — static-type
  consequences stay with go/types at the use sites; the machine's
  nil-literal arm never sees a `.defined` target). Covers every
  assignable context through the wrap: composite elements, returns,
  call arguments, assigns. The two pinned cases flip FAIL→PASS, plus
  the new maps/named-nil-flows family (5 rows) pins the
  return/composite/literal-elem/arg/slice flows; full-run re-pin in
  the fix commit (the item-5 baseline header records the flips).
  Func/chan slots keep the bare-nil emission (their comparison arms
  accept nil/nil; chan ops on a stored bare nil are recorded untested
  surface).
- Original status: open
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

- Status: fixed (2026-08-18, multi-package arc W1.1 — the REAL fix this
  entry always named: `qualifiedTypeName`/`funcWireName` qualify by
  `pkg.Path()` at the identity boundary
  (`tools/nativefrontend/identity.go`;
  `docs/2026-08-18_multipackage-identity.md` §1). Single-package keys
  are byte-identical (the main package's path IS its name — golden
  pins verified by `scripts/check-golden`), so no re-key wave
  materialized; the v1 name-collision refusal
  (`checkPackageNameCollisions`) retired in favor of the dotted-path
  key-grammar guard (`checkKeyPathGrammar`), and the pinned case now
  PASSES with Go's `false`. Residue split out honestly: the
  panic-message RENDERING of multi-segment qualifiers is BUG-059,
  pinned by multipkg/same-name-identity-panic.)
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

The REAL fix — widening the key to `obj.Pkg().Path()` — landed with the
multi-package slice (2026-08-18), as this entry's escalation clause
demanded. The feared re-key wave did not materialize: `main`-package and
single-segment stdlib qualifiers are path == name, so every pinned
lowering, `main.T(v)` panic rendering, and `TypeId.unqualified`
observation is byte-identical; the one genuinely divergent channel
(multi-segment-path qualifiers in panic MESSAGES) is BUG-059.

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

**Re-check 2026-09-01 (T2 records lane, item 9) [AGENT]: still red;
the D5 mechanism did not — and by its own design could not — close
this bug.** BUG-009's 2026-08-05 D5 fix landed after this entry was
written and had never been re-run against this entry's pin; isolated
`scripts/diff-one maps/imported-named-key-unhashable` (artifact root
redirected via `GOLEAN_COVERAGE_ARTIFACTS` to a scratch dir, so the
recorded full-run `latest.tsv` pair is untouched) at 439d4543,
go1.26.5: FAIL at stage lean-observation, `expected status panic, got
unsupported "map key hashability for unknown defined type
sort.IntSlice"` — the same honest fail-closed refusal recorded above,
corroborated by the identical row in the 2478/2478 full run recorded
at this same commit. This is exactly D5's stated residue: its
existence-marker TypeDefs are `kind: unsupported` precisely so that
STRUCTURAL use (comparability included) keeps failing closed; D5 fed
method-set queries, not `tyUncomparable`. Status stays open, the
baseline FAIL row stays true, and nothing is owed to a re-pin; the
case goes green only when the owed sub-slice (real declarations for
imported non-interface named types) lands.

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

- Status: fixed (2026-08-19, bug-fix arc slice 4 — the (L) surgery,
  user-ruled full literal envelope: `Cont.mapIterK` carries the map's
  base loc, the produced-key set and the START-KEY set; each pick
  recomputes candidates = live entries minus produced (validated
  self-normalized, fail closed) and LOADS the value from the live
  cell (the per-pick read footprint closes race-inventory U1); the
  stop slot (width candidates+1, stop LAST — the zero stream is the
  canonical member BY DEFINITION) is legal exactly when no
  never-removed start key remains unproduced; `mapDelete`/`clearMap`
  prune deleted keys out of same-goroutine `mapIterK` frames via
  `contAfterStmtOp` (delete-prune), making the FORCED
  removed-before-reached clause exact. All seven Cases flipped green
  (the five differential/race reds PASS; the two membership rows PASS
  with the admitted sets exhibited); `maps/added-entries-bound`
  stayed green as required. The obliviousness and wf analyses were
  replayed (`step_complete_any_wf`'s mapIterNext case re-proved on
  the live design; `MachineWf.itersNormalized` moved to per-pick
  validation); the WP kit moved to owned-cell laws
  (`wp_map_range_enter`, `wp_map_iter_next_key`/`_done`/`_inv` with
  the pick-coherence relation `P pr rem`). Residual, recorded at
  inventory E9 + `Cont.mapIterK`'s docstring: delete-prune rewrites
  only same-goroutine frames — cross-goroutine delete-during-range is
  racy-red via the new footprint, and the prune widening is owed at
  the first non-racy cross-goroutine shape. [CLOSED 2026-09-02: the
  "racy-red" dismissal was wrong for the handshake-synchronized (DRF)
  shape (fidelity finding A1-20); the pool-level `pruneForeign`
  (Multi.lean) now prunes every goroutine's in-flight frames — rows
  `maps/cross-goroutine-delete-readd/{drf,insert,racy}`; inventory E9.]
  [MECHANISM REPLACED 2026-09-03 (design-hygiene arc slice 1, B1 —
  entry-identity stamps): the key-set frames and the whole prune family
  (`contAfterStmtOp`, `pruneIterFrames*`, `pruneForeign*`) are deleted;
  `mapIterK` carries entry-ID sets and a delete is a heap write only —
  same envelope, same sets on every row above (evidence dir
  `docs/evidence/2026-09-03_hygiene-b1-stamps/`); the NaN-key range
  defect the key-set frame carried is BUG-088.] Kit obligations recorded
  in the arc log: the termination theorem "body stores no key into
  the ranged map ⇒ range terminates" (record, not prove);
  stop-admitting/mutating-range WP laws land with the first walk that
  needs them.)
- Pinned-by: differential
- Cases: maps/delete-during-range, maps/clear-during-range, maps/update-during-range, race/negative/map-range-iter, maps/delete-unreached-during-range, maps/delete-readd-during-range, maps/added-entry-count
- Discovered: 2026-07-26 (pre-merge adversarial audit of `wrong-answers-builtins`)
- RULING + guardrail REWORK (2026-08-19, memo §5 USER RULING): the (L)
  surgery is approved with the memo's two narrowings REJECTED — the
  FULL literal envelope ships (deletion prunes the produced-set AND
  the mandatory start-set; a deleted-then-re-created key is a NEW
  created entry, re-producible — the adopted reading, ledger L-012).
  Guardrails-first: the two rows whose exact-count pins encoded the
  dead narrowings are reworked to MEMBERSHIP rows ahead of the
  surgery, and both are deliberately RED under the snapshot machine
  (now on the Cases line): `maps/delete-readd-during-range` (raw
  count, admitted set {3,4,-1} with -1 the subject's own truncation of
  the genuinely unbounded tail; snapshot machine enumerates the
  singleton {3} — the membership lint refuses it) and the NEW
  `maps/added-entry-count` (raw created-entry produce-or-skip count,
  admitted set {1,2}; gc exhibits BOTH members — 1: 9/60, 2: 51/60 at
  the rework probe — while the snapshot machine enumerates {1}: the
  narrowing is oracle-visible on this shape). The member-invariant
  strict bound `maps/added-entries-bound` STAYS strict (attempted
  membership; the harness lint correctly refused the singleton-set
  row — its observable is 7 across the whole ruled envelope). Both
  reds flip green at the (L) surgery; self-inserting loops are
  genuinely unbounded there and ∀-streams certification fails closed
  on them (the membership lane carries them, and the claim says so).
- PROBES + design memo (bug-fix arc slice 4, 2026-08-19;
  `docs/2026-08-19_bug005-map-range-memo.md` — slice 4 is
  design-gated, no fix in that commit). Three rows added:
  `delete-unreached-during-range` (RED, differential — the forced
  removal clause isolated from the delete-everything shape: machine
  20, go 11) and two member-invariant GREEN envelope-bound pins
  (`maps/added-entries-bound`, `maps/delete-readd-during-range` —
  guard pins, at memo time deliberately NOT on the Cases line; the
  2026-08-19 ruling rework since moved `delete-readd-during-range` to
  a membership row that is deliberately RED pre-surgery and therefore
  IS on the Cases line now — see the RULING + REWORK bullet above)
  that stay green under snapshot AND any conforming live model and go
  red on over-production, alien keys, or divergence. Probe findings the memo
  rests on (artifacts/probe/map005, scratch; 400 runs each): gc
  exhibits the FULL added-entries latitude across plain re-runs
  (counts 4..8 all realized on a 4+4 shape); gc NEVER re-produces a
  deleted-then-re-created already-produced key, even under forced
  mid-iteration growth (800 runs) — though the spec's created-entries
  sentence literally admits it; and the memo SHARPENS this entry:
  stale values violate a FORCED point (the range clause's production
  table defines the map 2nd value as `m[k]`, produced "for each
  iteration"), not merely gc behavior.

**Fourth symptom, added 2026-08-07 (S3 pre-merge audit, major): RACE
INVISIBILITY.** gc's live iteration reads the map at every
`mapIterNext` — `-race`-instrumented, so a concurrent map write landing
while another goroutine's range is ACTIVE is a TSan-red data race
(probed: "Previous read ... runtime.mapIterNext()", exit 66). Our
snapshot range performs no per-iteration read (the pick steps consume
the snapshot from `Cont.mapIterK`, touching no user memory), so the S3
race detector records only the entry-snapshot read and such programs
run to a silent value (`race/negative/map-range-iter`, the fourth
Cases pin — red until this entry's live-iteration surgery landed). The
detector's footprint-table lockstep obligation is structurally blind
here because the gc accesses have no `stepFn` arm at all; recorded as
under-approximation U1 in `GoLean/GoCore/Race.lean`'s inventory. The
live-iteration fix must add the per-iteration footprint arm as part of
the same movement.

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

> **R-1 conversion state (2026-08-21, raft W4.3 item 5 —
> docs/raft-w43-log.md).** The 2026-08-20 R-1 ruling quotients the
> abort-line TEXT of the three (c) rows here (the spec describes none
> of preprintpanics' rewriting or the [recovered, repanicked]
> collapse) and keeps the FORCED half exact. Executed case-level: the
> forced halves are now PROVED in-language by the green rows
> `panic-defined-payload-methods/{error,stringer}-forced-half` (the
> same payloads recovered: kind via type assertion, identity via the
> method results and the value round-trip) and
> `repanic-same-value-abort/forced-half` (the repanic caught in an
> outer frame, `r == orig` — the very identity the collapse renders,
> decided in-language where the abort line cannot). The three (c)
> rows stay RED: the machine has NO text member yet
> (`renderPanicHead` refuses — the impossibilities below are about
> producing gc's bytes, but under the quotient a member need only
> CONFORM, and producing ours is semantic-core work formerly owned
> by the W3.2 lane — re-homed 2026-08-31, fidelity decision 6
> [USER]: owner now this repo's TODO.md backlog). No red was
> relaxed; the conversion completes when the member lands.
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

**Triage disposition, user-ratified 2026-08-20** (bug-fix arc gate,
`docs/2026-08-19_triage-table.md` §7): this entry's four cases are NOT
one category. Items 1 and 4 — eface allocation identity and the
`preprintpanics` method rewrite, i.e. `repanic-same-value-abort` and
`panic-defined-payload-methods/{error,stringer}` — are ratified
category-(c) profound-reason pins (triage row C4/L12). **Item 3, the
multi-line payload (`panic-newline-abort`), is category (a)** (triage
row L12b) and is queued as mini-slice **A7** in the coverage ledger's
build queue: gc's first abort line stops at an embedded `\n`
(`printindented`), which is a rendering shape with no identity or
abort-time-method demand behind it. A7's binding constraint is the
CHECK ORDER — the item-1/item-4 refusals must keep returning `none`
first, or the fix re-opens the unconditional-arm regression class this
entry already paid for once (2026-07-31 finding 3, above). Status and
Cases are unchanged: all four cases remain open and red under this
entry until A7 lands.

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

**Owner (re-homed 2026-08-31, fidelity decision 6 [USER]):** the F4
arc referenced below is parked on `park/reasoning-2026-08-31`; this
obligation's live owner is THIS repo's TODO.md backlog ("Re-homed
obligations"). The F4 references stay as historical routing.

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

## BUG-056 — `&*x` on a nil pointer collapses instead of panicking

- Status: fixed (2026-08-19, bug-fix arc slice 3, user-gated — memo
  `docs/2026-08-19_bug056-addr-deref-memo.md`, ruling §6. Mechanism
  (b): one new GoCore strict op `addrOfDeref` (wire `addr-of-deref`) —
  evaluate the pointer operand, nil-assert on the VALUE via
  `valueAsLoc`'s existing runtime-panic arm, yield the same pointer,
  touch NO memory (gc's TESTB shape; no race-footprint arm ON PURPOSE
  — Race.lean's call-site inventory records the decision). The
  emitter arm lives in `emitUnaryExpr`'s `token.AND` path — the `&`
  OPERATOR's immediate-`*` operand only; `emitAddressOf`'s StarExpr
  arm DELIBERATELY kept the collapse, because that is the general
  addressable path whose consumers nil-check at their own spec points
  (the five store-order pins — the slice-3 JUDGMENT records the first
  draft putting the op there and flipping all five red). Corrected at
  the audit fix round (A2): this sentence used to place the arm in
  `emitAddressOf`, the exact placement the fix rejected. EXTENSION
  (same round): the RECEIVER-position IMPLICIT `&` reused that
  collapse and lost the panic silently — BUG-063, fixed by routing
  `methodReceiverArg`/`syncRecvAddr` through `receiverAddr`'s
  addr-of-deref emission. Field/index compositions keep their
  pinned-green lowerings. Flipped exactly the 5 pinned reds; the 7
  matrix guard greens held. Acceptance: `race/free/addr-deref-no-read`
  pins the no-load/no-race-visibility ground truths — `&*p` beside a
  concurrent pointee write stays race-free (gc TSan-green 20/20 at the
  fix probe; the real-load control TSan-red), and would go red if the
  op ever grew a memory access. Discovery record below kept verbatim.)
- Pinned-by: differential
- Cases: spec-examples-decl/address-op-nil-indirection/addr-deref-nil, spec-examples-decl/address-op-nil-indirection/addr-deref-nil-paren, spec-examples-decl/addr-deref-nil-matrix/two-deref-inner-nil, spec-examples-decl/addr-deref-nil-matrix/deref-arg, spec-examples-decl/addr-deref-nil-matrix/deref-call
- PROBE MATRIX (bug-fix arc slice 3, 2026-08-19; design memo
  `docs/2026-08-19_bug056-addr-deref-memo.md` — slice 3 is
  design-gated, no fix in that commit): 10 rows in
  `spec-examples-decl/addr-deref-nil-matrix/`, colors recorded
  PRE-fix (7 PASS / 3 FAIL, every color predicted from the wire
  reading before the run). The red boundary is sharp: exactly the
  compositions where `*` is the immediate operand of `&` and no
  enclosing address node re-checks the base (`two-deref-inner-nil`,
  `deref-arg`, `deref-call` join the two pins above); every neighbor
  — field/index composition either sugar direction, the operand's own
  inner deref, and the non-nil `&*p` aliasing identity — is pinned
  GREEN so a fix cannot regress it (the 7 green rows
  `two-deref-outer-nil`, `index-slice-ptr-nil`, `index-arr-ptr-nil`,
  `index-auto-deref`, `field-explicit`, `field-auto-deref`,
  `alias-non-nil` — guard pins, deliberately NOT on the Cases line,
  which the bug-index cross-check reserves for this bug's reds). The
  entry's record-only claims (`&p.f`/`&p[i]` on nil panic correctly)
  are now case-witnessed (`field-auto-deref`, `index-auto-deref`). Ground truths for any
  mechanism (probed, gc go1.26.5: memo §2): `&*p` compiles to a
  single uninstrumented `TESTB` nil-probe — NO pointee load even for
  a 64-byte pointee, TSan-green beside a concurrent pointee write —
  so a `_ = *p` desugar is wrong by probe, not just by taste.
- Discovered: spec#Address_operators' own exhibit — "if the evaluation
  of x would cause a run-time panic, then the evaluation of &x does
  too" — so `&*p` with `p == nil` must panic (gc go1.26.5: panics;
  spec-derived expectation computed first). The machine returns ok/0:
  the `&*` composition is collapsed before the nil indirection check
  fires. Sibling case `deref-nil` (bare `*p`) PASSES — the panic
  machinery exists; the address-of-indirection path skips it.
- Class: unexercised path (the audit doctrine's first structural
  class); nothing in the pre-P3 corpus exercised `&*` on nil.
  BOUNDARY (P3 audit N2 → integrator "refutation" → refutation
  itself REFUTED at the delta-review F-1; the reversal recorded
  deliberately): the frontend wire for `&*p` and `&(*p)` is
  BYTE-IDENTICAL — both collapse to `q := p`. The short-lived green
  "witness" ended `return q.x`, whose trailing deref panicked
  regardless: a masked green, the same pattern BUG-057's rows fix.
  The discriminating paren case (addr-deref-nil-paren, `_ = q`) is
  RED and pinned above. `&p.f` and `&p[i]` on nil pointers panic
  correctly (wire emits real field-addr/index-addr nodes —
  record-only, no corpus witness). The defect: the `&`-of-`*`
  composition, parenthesized or not.

## BUG-057 — two-variable comma-ok VAR DECLARATIONS drop the ok flag

- Status: fixed (2026-08-19, bug-fix arc slice 2 — `emitDeclStmt` now
  ARITY-CHECKS each `ValueSpec` before pairing names to initializers.
  A spec whose ONE initializer has a `*types.Tuple` type of exactly
  `len(Names)` components (the comma-ok sources and a multi-valued
  call) is lowered by `emitAssign` on a fabricated
  `ast.AssignStmt{Lhs: Names, Tok: DEFINE, Rhs: Values}` — the SAME
  path the correct short declaration `v, ok := m[k]` uses, and the
  same path the package-level declaration has always used
  (emit.go:600-607). Any other name/value mismatch is now an explicit
  refusal instead of a silent drop. A grouped declaration that mixes
  ordinary and multi-value specs lowers to a SEQUENCE of wire
  statements, each spec's own hoists captured ahead of its own
  statement and all but the last placed in the hoist accumulator that
  `emitStmtList` splices in at the same scope — not a wire `block`,
  which would scope the declarations away. The interface-conversion
  refusal the old blanket tuple/interface check provided is preserved
  at the reroute, sharpened to fire only when a conversion is
  genuinely owed (declared name interface-typed, tuple component not).
  A declaration with 0 or N initializers emits exactly the wire it
  emitted before. Flips, all in the fix commit: 24 red→green
  (15 differential, 9 frontend-export) plus 4 new green ids and 1 new
  red id — the full list is in `docs/bugfix-arc-log.md` §slice 2.)
  (discovered 2026-08-18, spec-truth P3; DIAGNOSIS
  CORRECTED at the P3 pre-merge audit — the original entry titled
  this "typed receive declaration drops the received value" and both
  halves were wrong).
- Pinned-by: differential
- Cases: spec-examples-decl/receive-comma-ok/typed-form, spec-examples-decl/receive-comma-ok/untyped-form-live, spec-examples-decl/index-comma-ok/var-form-present, spec-examples-decl/var-decl-forms/found-present, spec-examples-decl/var-comma-ok-matrix/recv-untyped, spec-examples-decl/var-comma-ok-matrix/recv-untyped-blank-value, spec-examples-decl/var-comma-ok-matrix/recv-typed, spec-examples-decl/var-comma-ok-matrix/recv-typed-blank-value, spec-examples-decl/var-comma-ok-matrix/index-untyped, spec-examples-decl/var-comma-ok-matrix/index-untyped-blank-value, spec-examples-decl/var-comma-ok-matrix/index-typed, spec-examples-decl/var-comma-ok-matrix/index-typed-blank-value, spec-examples-decl/var-comma-ok-matrix/func-literal, spec-examples-decl/var-comma-ok-matrix/grouped-spec, spec-examples-decl/var-comma-ok-matrix/after-goto, spec-examples-decl/var-comma-ok-matrix/after-goto-recv, spec-examples-decl/var-comma-ok-matrix/after-goto-assert, spec-examples-decl/var-comma-ok-matrix/assert-untyped, spec-examples-decl/var-comma-ok-matrix/assert-untyped-blank-value, spec-examples-decl/var-comma-ok-matrix/assert-untyped-blank-ok, spec-examples-decl/var-comma-ok-matrix/assert-typed, spec-examples-decl/var-comma-ok-matrix/assert-typed-blank-value, spec-examples-decl/var-comma-ok-matrix/assert-typed-blank-ok
- Discovered: spec#Receive_operator's four comma-ok forms. Audit
  probe matrix (machine vs go, value/ok per form): assignment and
  short-decl forms are CORRECT; `var x, ok = <-ch` (untyped) and
  `var x, ok bool = <-ch` (typed) deliver the VALUE but drop `ok`
  (false where gc says true); `var v, ok = m[k]` (map index) drops
  `ok` identically. Scope tightened at the delta-review F-2: the
  defect is the FUNCTION-LOCAL two-variable comma-ok
  var-declaration lowering (emit.go:2383-2392 pairs names to values
  with no arity check, so the second name gets no init —
  wire-verified); package-level `var v, ok = m[k]` lowers correctly
  via $pkginit. Not typed-specific, not receive-specific; the value
  arrives, the boolean is lost. Adjacent honesty notes: the
  analogous `var a, b = two()` tuple case FAILS CLOSED (the
  silent-mis-lower arity hole is comma-ok-specific), and
  typed-form's value-delivery half is wire-verified rather than
  case-pinned — its subject returns x&&ok, which cannot distinguish
  the two drops (F-10).
- MASKING record (corrected at the delta-review F-2): the original
  "untyped form PASSes" evidence used a closed-drained channel /
  absent map key, where ok=false is the RIGHT answer — the bug's
  output coincided with correctness. TWO tranche cases carried that
  masked green (receive-comma-ok/forms and index-comma-ok, both
  function-local); var-decl-forms' package-level `var _, found`,
  originally listed as a third, was never masked (package-level is
  correct-by-construction) — its new row found-present pins the
  LOCAL form instead. All three unmasking rows red and pinned here.
- Class: unexercised path (no pre-P3 case used a two-var comma-ok
  var declaration with a TRUE ok on the line that matters).
- EDGE ENUMERATION (bug-fix arc slice 2, 2026-08-19; landed as its
  own commit BEFORE any fix, colors recorded pre-fix). 51 rows in the
  new package `spec-examples-decl/var-comma-ok-matrix/` (this figure
  said 46 while the family has 51 rows — five were added after the
  entry was written; re-counted 2026-08-22, launch audit D7) walk the full
  matrix — three comma-ok sources (receive, map index, type assertion)
  × untyped/typed declaration × blank in the value position / blank in
  the ok position / neither × function-local vs package-level — plus
  the positions the declaration can occupy (function literal, grouped
  multi-spec declaration, goto-restructured body, interface-valued
  map), the shadow-capture shape, and the adjacent tuple-call
  declaration. EVERY new row observes a TRUE ok (the MASKING record
  above), and every row returns the value and the ok as SEPARATE
  observables, which closes F-10: `x && ok` collapsed the two
  deliveries into one bit, so a dropped value and a dropped ok were
  indistinguishable. Pre-fix colors (`scripts/coverage run --prefix
  spec-examples-decl/var-comma-ok-matrix`): 22 PASS / 24 FAIL.
  Three findings the enumeration establishes and this entry did not
  previously state exactly:
  1. **The silent drop is receive + map index only.** All six
     function-local TYPE-ASSERTION rows FAIL CLOSED at
     `frontend-export` ("type assert form outside a 2-target
     assignment"), not silently. The entry's "(probe: `= x.(T)`)" is
     resolved: the type-assertion source never produced a wrong
     answer, and `spec-examples-decl/assert-comma-ok` was already red
     for that reason.
  2. **Package-level is correct with a TRUE ok, now case-pinned.** All
     18 `pkg-*` rows PASS pre-fix, so the "$pkginit is
     correct-by-construction" claim is no longer only wire-argued —
     the $pkginit path fabricates ONE `ast.AssignStmt` carrying every
     name for a multi-value spec and runs `emitAssign`
     (emit.go:600-607), which is exactly the lowering the
     function-local path was missing.
  3. **The typed form is not bool-only.** `var v, ok T = x` also
     admits an INTERFACE T that both values are assignable to — the
     shape spec#Type_assertions itself writes,
     `var v, ok interface{} = x.(T)`. Those three rows
     (`{recv,index,assert}-typed-iface`) are red at `frontend-export`
     under the deferred interfaces campaign and must STAY red across
     the fix: the reroute must not turn a fail-closed refusal into an
     unboxed store.
  Two further pre-fix reds, both fail-closed: `shadow-capture`
  (`{ var v, ok = m[v] }`, whose initializer reads the OUTER v per
  spec#Declarations_and_scope — refused because the capture hoist
  cannot type a tuple temp) and `iface-value` (a `map[string]any`
  lookup — refused by the var path's BLANKET tuple/interface guard,
  which fires whenever a declared name is interface-typed even when
  the tuple component already is one, so no conversion is owed).
- STILL RED after the fix, all fail-closed and all handed to the
  arc's triage (slice 5) as frontier rows, none of them a wrong
  answer: `{recv,index,assert}-typed-iface`, `tuple-call-iface` and
  `spec-examples-decl/assert-comma-ok` — the deferred implicit
  multi-value interface conversion, refused by the preserved guard;
  and `shadow-capture` — the capture pre-bind cannot hoist a tuple to
  a temp, so a comma-ok initializer that reads a name the same
  VarSpec declares is refused rather than mis-scoped. Both are
  language gaps that predate this bug and are out of its scope; the
  reroute neither widened nor narrowed them.
- MASKED-GREEN SWEEP (bug-fix arc slice 2): mechanized with an AST
  scan (`artifacts/probe/sweep057`, scratch) over every `.go` file
  under `Corpus/`, `raftharness/`, `compat/`, `tools/`, `scripts/`,
  `proofs/`, `GoLean/` and `deps/raft`, reporting every `ValueSpec`
  with ≥2 names and exactly ONE initializer, classified by source
  kind and by package/function scope — the exact arity shape this bug
  mis-lowers, found structurally so multi-line and grouped forms
  cannot hide. 62 hits, 51 of them this bug's own package. The other
  **11**: 4 package-level (`init/multi-value-var-init:11`,
  `pkg-init-together:13`, `var-decl-forms:{28,30}` — the correct
  $pkginit path, PASS throughout), 3 that are the P3 audit's own
  unmasking rows (`index-comma-ok:34`, `receive-comma-ok:50`,
  `var-decl-forms:68`), 1 that is the typed pin
  (`receive-comma-ok:35`), 1 already-red fail-closed
  (`assert-comma-ok:15`, the interface-typed assertion — so it was
  never a masked green), and exactly **2 masked greens**:
  `index-comma-ok:15` (`var v3, ok3 = a["missing"]`, absent key) and
  `receive-comma-ok:18` (`var x3, ok3 = <-ch`, closed and drained).
  **Those two are precisely the pair the P3 delta-review's MASKING
  record already names, and both already carry an unmasking row.** So
  the sweep found no NEW masked green and confirms the record is
  complete rather than merely plausible. `deps/raft` has ZERO
  occurrences of the shape (contrast slice 1, where raft had 103
  if-with-init statements) — this bug's raft blast radius was
  indirect: it is the `if v, ok := m[k]` short-decl form raft writes,
  which was never affected.

## BUG-058 — if-statement init scope: condition hoist block emitted OUTSIDE the init

- Status: fixed (2026-08-19, bug-fix arc slice 1 — `emitIf` now emits
  the condition into its OWN hoist accumulator and, when that
  accumulator is non-empty, returns a wire `block` of
  `[init, condHoists…, if]` instead of an `if` node carrying an
  `init` key. That block is the same scope `decodeIf` already builds
  for the `init` key (`.block #[] #[init, ifThenElse …]`,
  GoLean/NativeToIR.lean:1143-1153), so the init-declared names are
  visible to the hoists, the condition and both branches — no wire
  schema change, no decoder change, no GoCore change. An `if` with no
  init, or with an init and a hoist-free condition, emits exactly the
  wire it emitted before. Flipped, all in the fix commit: the 9
  `if-init-hoist-order/*` rows and `panic-values/panic-error`
  (10 red→green), plus the new `control-flow/goto-if-init-cond-hoist`
  landing green; nothing else moved in the full run.)
  (discovered 2026-08-18, spec-truth P3; DIAGNOSIS
  REWRITTEN at the P3 pre-merge audit — the original entry blamed
  comma-ok assertion in a recover handler and prescribed a frontend
  quarantine; every axis of that was wrong, and the quarantine would
  have permanently darkened `if v, ok := m[k]; ok && f(v)` — one of
  the most common shapes in real Go, including deps/raft).
- Pinned-by: differential
- Cases: spec-examples-lexical/panic-values/panic-error, spec-examples-stmt/if-init-hoist-order/cond-call-after-init, spec-examples-stmt/if-init-hoist-order/init-panic-first, spec-examples-stmt/if-init-hoist-order/else-if-chain, spec-examples-stmt/if-init-hoist-order/func-literal, spec-examples-stmt/if-init-hoist-order/nested, spec-examples-stmt/if-init-hoist-order/cond-hoist-reads-init, spec-examples-stmt/if-init-hoist-order/cond-panic-after-init, spec-examples-stmt/if-init-hoist-order/comma-ok-short-circuit, spec-examples-stmt/if-init-hoist-order/comma-ok-method-short-circuit
- Discovered: `emitIf` (tools/nativefrontend/emit.go:2426) emits
  `st.Init` INSIDE the if node, but the condition is emitted with the
  enclosing hoist accumulator in force, so `emitStmtList` places the
  short-circuit desugar block BEFORE the if — outside the init's
  scope. Trigger widened at the delta-review F-3: any `if` (or
  `else if`, incl. in function literals) with an init statement plus
  ANY hoisting call/alloc anywhere in the condition — no
  short-circuit operator required (modes 2-3 below have none;
  `emitter.hoist` is generic, and `emitIf` scopes the else
  accumulator but not the condition's). Comma-ok, type assertions,
  recover, closures — all incidental. Observable modes:
  (1) STUCK "unbound GoCore variable address: <init var>" when the
      hoisted prefix reads the init-declared variable (the original
      case's symptom);
  (2) SILENT WRONG ANSWER — `if x := a(); b() == x`: go runs a then
      b ("ab"); the machine runs the hoisted b first ("ba");
  (3) SILENT WRONG ANSWER — `if x := s[0]; b() == x` with s nil: go
      panics in the init before b runs; the machine runs b first.
  Modes 2-3 are pinned red by the new if-init-hoist-order cases.
- Class: frontend lowering (evaluation-order fidelity), NOT
  fail-closed classification. Fix direction: scope the condition's
  hoist accumulator inside the emitted if (est. small, emitIf-local);
  a frontend arc, out of this corpus lane's scope.
- For-init and switch-init are NOT affected — probed clean AND
  corroborated structurally at the delta-review (emitFor routes cond
  hoists into condPre inside the loop node; emitSwitch/emitTypeSwitch
  append tag hoists after the init); the receive-hoist family
  (BUG-023/026) is a different position set.
- EDGE ENUMERATION (bug-fix arc slice 1, 2026-08-19; landed as its
  own commit BEFORE any fix, colors recorded pre-fix): the `Cases:`
  list above grew from the 2 P3 pins to 9 — `else-if-chain`,
  `func-literal`, `nested`, `cond-hoist-reads-init`,
  `cond-panic-after-init`, `comma-ok-short-circuit` and
  `comma-ok-method-short-circuit` walk the positions the trigger can
  occupy and pin all three observable modes (see
  `docs/bugfix-arc-log.md` §slice 1 for the per-row go/machine
  values). The non-affected relatives are now pinned GREEN in
  `spec-examples-stmt/init-hoist-relatives/` (6 rows: for-init,
  switch-init, type-switch-init, each also in a `-reads-init` form
  that puts the init-declared variable inside the hoisting call), so
  the fix cannot regress them silently.
- Emitter line numbers in this entry are the P3-era ones; at the fix
  commit `emitIf` is at emit.go:2517.
- MASKED-GREEN SWEEP (bug-fix arc slice 1): mechanized with an AST
  scan of every `.go` file under `Corpus/` — 85 `if`-with-init
  statements, 17 with a hoist-capable construct in the CONDITION, of
  which 15 are this bug's own package, 1 is `panic-values/panic-error`
  (already pinned red) and 1 is
  `spec-examples-lexical/channel-direction-forms:19`, where the
  "call" is the CONVERSION `int(got)`, which the frontend does not
  hoist — the case was green before the fix and after it, so the
  scanner's classification is conservative there. **No masked green:
  no corpus case outside this family combined an if-init with a
  hoisting condition, so none could coincide with correctness.** The
  disposition-level finding is a SUFFICIENCY gap rather than a mask:
  `If_statements-3-23172299`'s five green rows
  (`if-init-else-chain/*`) cannot observe order at all, so the spec
  block's own "executes before the expression is evaluated" was
  unwitnessed while the machine had it wrong — recorded on that row
  in docs/spec-archaeology/spec-examples-dispositions.tsv.


## BUG-062 — inline `len`/`cap` reads reorder against calls in the same expression (receive-free functions)

- Status: fixed (2026-08-31, t1-fidelity-fixes mini-slice A6 — the
  hoist predicate is now the SWEEP-SCOPED ordered-event scan the triage
  prescribed: `sweepOrderedEventAfter` (emit.go) hoists an inline
  builtin — len/cap AND min/max, closing the widened statement below —
  exactly when an ordered event (receive or non-conversion,
  non-constant call) lexically FOLLOWS it in the same sweep, where the
  sweep is the hoist-accumulator scope tracked per statement and per
  sub-accumulator site (`e.sweepStmt`: if/for cond+init+post, switch
  tag/case values, range operands, short-circuit RHS, per-spec var
  initializers, assign-target probes). The function-scoped `fnHasRecv`
  flag and `containsRecv` are retired. min/max hoist with NO
  panic-free restriction — they are calls, and a hoisted arg panic
  joins the recorded frontend-ANF call-first family (latitude E12/E13)
  on the same terms as any user call's; len/cap keep BUG-032's
  fail-closed refusal, narrowed to its true residual (see BUG-032's
  2026-08-31 amendment). All five reds flip PASS; both green controls
  and the whole recv-order family hold; four A6 guardrail rows added
  (len-vs-call-order/{short-circuit,short-circuit-skipped,
  panicky-before-call} green, panicky-between the surviving refusal
  pin, red frontend-export by design). B-3 correction (2026-09-01
  audit fix round): A6 is NOT a pure narrowing of BUG-032's refusal —
  receive-FREE functions, where this bug's silent wrong answer lived,
  GAINED the fail-closed refusal on the panicky composition at the
  same time the wrong answer died; trade stated in BUG-032's A6
  amendment.)
- Pinned-by: differential
- Cases: builtins/len-vs-call-order/chan, builtins/len-vs-call-order/slice, builtins/min-max-vs-call-order/min-value, builtins/min-max-vs-call-order/max-value, builtins/min-max-vs-call-order/min-arg-panic, builtins/len-vs-call-order/short-circuit, builtins/len-vs-call-order/panicky-before-call, builtins/len-vs-call-order/lexer-idiom, builtins/len-vs-call-order/len-nil-only-none
- FR-28 note (2026-09-04, lane `fr27-fr28`): the "one fail-closed
  refusal residual" this fix left (ledger §2 Order_of_evaluation /
  Length_and_capacity; frontier row FR-28) is narrowed by the nil-deref
  transparency arm and extended to the `make` hoist — BUG-032's FR-28
  amendment has the mechanism, BUG-083 the make table. `lexer-idiom`
  and `len-nil-only-none` join this Cases line as the hoist-with-a-
  nil-deref-only-operand realization of the spec-forced len-before-
  call order (the len/cap hoist this entry built, taken where it was
  refused before).
- E13-b note (2026-09-05, lane `e13-b`): the residual refusal is
  RETIRED (BUG-032's E13-b amendment; latitude E13 option (b), [USER]
  ruling relayed). This entry's FORCED-point fix — the sweep-scoped
  hoist of a builtin when an ordered event follows — is untouched and
  is exactly the F2 side of the E13 decision procedure (design §1): an
  ARGUMENT of a later call is evaluated before the call, never a
  choice. What changed is the OTHER side: panicky inline material LEFT
  of the hoisted builtin now carries an `unseq-probe`, so `iv.(int) +
  len(b[j]) + f()` lowers instead of refusing and realizes both spec-
  permitted panic orders. Every row on this Cases line stays green.

WIDENED 2026-08-22 (grossmith campaign-2 F-1, promoted by the
launch-audit fix round): the predicate gap is not `len`/`cap`
specifically — **the ordered-event set omits the value-returning
built-ins**. `min`/`max` are calls (`spec#Built-in_functions`: "called
like any other function") and the machine runs a lexically LATER call
first, observable both as a silent wrong value
(`min(n,100) + bump()` → machine 5, gc 1) and as a wrong panic order
(`min(b, s[i]), wit(7,9)` → machine 9, gc 0 — the operand panic must
precede the later call). Three new RED pins above; two GREEN controls
(`append-arg-panic`, `call-in-builtin-arg`) pin that `append` is
already ordered and calls INSIDE a built-in's argument list already
hoist lexically — A6 must not regress either. A6's scope is re-stated
accordingly: enumerate built-in call sites, not just inline `len`/`cap`
reads.

`spec#Order_of_evaluation` orders "all function calls, method calls,
receive operations, and binary logical operations" lexically
left-to-right when evaluating an expression's operands, and
`spec#Built-in_functions` says built-ins "are called like any other
function" — so in `len(ch) + fill(ch)` the `len` operand is read BEFORE
the call runs. gc agrees (probed at go1.26.5, slice-5 triage §3.4:
`go run` → 1, and re-derived at the slice-6 pin,
artifacts/probe/slice6a).

The frontend hoists CALLS out of expressions (ANF) but leaves `len`
inline in a receive-FREE function — the `fnHasRecv` hoist is the only
mechanism that ever hoists `len` — so the machine runs `fill` first and
reads the post-call length: machine 3 vs go 1 on both pinned rows, a
FORCED-point silent wrong answer. BUG-023's exact class on the
len-vs-CALL axis instead of len-vs-RECEIVE, in exactly the functions
BUG-023's fix did not cover. Found by the slice-5 triage REASONING over
the emitter (no case could see it — the shape had no corpus row), and
measured on both sides when slice 6 landed the guardrail.

Receive-BEARING functions get this RIGHT by accident today (the hoisted
`len` is appended to the accumulator before the call's hoist) — pinned
green by `builtins/len-vs-call-order/recv-bearing`, so the fix cannot
regress them.

Fix shape (triage §3.4, mini-slice A6's corrected mechanism): the hoist
predicate becomes "the statement's sweep contains an ORDERED EVENT"
(receive OR call), scoped to the STATEMENT — one movement that fixes
both this entry and the A6 refusal family (F23) without extending the
divergence. Owner: mini-slice A6 (queued, category (a) in
docs/2026-08-19_triage-table.md; queue position in
docs/language-coverage-ledger.md). LANDED 2026-08-31 exactly in that
shape, refined one notch: the scan asks for an event lexically AFTER
the builtin (an earlier event's hoist precedes the builtin's inline
position anyway), and the scope is the SWEEP — the hoist-accumulator
unit — not the whole statement, so a loop body's calls do not force
hoists into the loop's condition (see the Status paragraph).

## BUG-063 — receiver-position implicit `&*q` collapses instead of panicking (BUG-056's implicit-& sibling)

- Status: fixed (2026-08-19, bug-fix arc AUDIT FIX ROUND — new
  `receiverAddr` helper in `tools/nativefrontend/emit.go`: the
  receiver-position implicit `&` (parens stripped, immediate `*`
  operand only) lowers to the existing `addr-of-deref` strict op, every
  other operand keeps the general `emitAddressOf` path.
  `methodReceiverArg`'s pointer-receiver arm and `syncRecvAddr` route
  through it; `emitAddressOf`'s StarExpr arm keeps its collapse
  UNTOUCHED for the store-target/index/field/slice consumers (the five
  store-order pins — the slice-3 JUDGMENT's trap, avoided by
  construction this time). No GoCore, decoder, or wire-schema change:
  the strict op is BUG-056's, reused. Flipped exactly the 2 predicted
  reds (both Cases below); the 5 store-order pins, the 10-row
  addr-deref-nil-matrix, both guardrail controls, and the
  nil-receiver/nil-pointer-method-value family all held in the same
  full run. `slice-expr-nil` (the lesser sibling) stays red by scope,
  as its untriaged-ids row records. Discovery record below kept
  verbatim.)
- Pinned-by: differential
- Cases: methods/recv-implicit-addr-deref/explicit-call-nil, methods/recv-implicit-addr-deref/method-value-nil

spec#Calls: for a pointer-receiver method `m` in `&x`'s method set,
"x.m() is shorthand for (&x).m()" when `x` is addressable. When `x` is
itself the indirection `*q`, that implicit `&x` is the `&*q`
composition spec#Address_operators gives an eager panic clause ("if the
evaluation of x would cause a run-time panic, then the evaluation of &x
does too"). gc panics on nil `q` at receiver evaluation (probed
go1.26.5, artifacts/probe/a1-recv, scratch — expectations computed from
`go run` before the differential ran). spec#Method_values makes the
method-value form `f := (*q).M` panic at the BINDING (the receiver is
evaluated and saved then).

BUG-056's fix scoped `addr-of-deref` to the EXPLICIT `&` operator
(`emitUnaryExpr`) and deliberately left `emitAddressOf`'s StarExpr arm
collapsing `&*x` to `x` — correct for its store-target/index/field
consumers, whose own spec points nil-check the base (the five
store-order pins). But the RECEIVER-position callers of `emitAddressOf`
(`methodReceiverArg` for method calls and method values,
`syncRecvAddr` for sync primitives) reuse that collapse for the
implicit `&`, where NO downstream consumer owes the check: the method
runs on a nil receiver and the panic is silently lost. Machine 5 vs go
100 on the call form, 15 vs 100 on the method-value form (the machine
also mis-times the loss: it binds and calls where gc never passes the
binding). Found by the pre-merge audit (finding A1) reasoning over the
emitter's caller graph — the corpus had zero `(*q).M` receiver shapes
(sweep at the guardrail commit: none in `Corpus/`, `raftharness/`,
`compat/`, or `deps/raft` outside this bug's package), the
unexercised-path class.

Boundaries established by the same guardrail package, so the fix cannot
overshoot:

- `sync-recv-nil` is GREEN pre-fix: the sync-op consumer nil-checks its
  operand itself (`valueAsLoc`), so the collapse is benign there — the
  `index-arr-ptr-nil` precedent. The row is the control that unified
  receiver routing must not disturb.
- The implicit-& panic's order against ARGUMENT calls
  (`(*wp).Add(bump())`) is UNSEQ latitude (the receiver probe is not a
  call, so lexical left-to-right does not order it; I-2's reading), and
  gc realizes args-first (probe: 1007). No strict row pins that shape —
  it would pin one conforming member against another.
- `pointers/nil-array-ptr-slice/slice-expr-nil` pins the LESSER sibling
  at its CURRENT class: `(*ap)[0:1]` on nil `ap` goes honest-STUCK
  ("expected array or slice value for slice expression, got
  GoValue.nil") — a visible refusal, never a wrong answer, so it is a
  coverage-disposition row in `baselines/untriaged-ids`, NOT on this
  Cases line; it flips only if the slice-base path grows nil handling.

Fix shape: route the receiver-position implicit-& emission
(`methodReceiverArg`'s pointer-receiver arm, `syncRecvAddr`) through
the same scoped `addr-of-deref` lowering the explicit arm uses when the
operand (parens stripped) is an immediate `*` — preserving
`emitAddressOf`'s collapse for the store-target positions where the
five store-order pins live (the slice-3 JUDGMENT's exact trap).

## BUG-064 — the inittask double-escape: the init-graph worklist re-escapes the table's symbol prefixes

- Status: fixed (2026-08-20, raft W4.0 — `buildInitGraph`
  (`tools/nativefrontend/load.go`) now carries LINKER SYMBOL PREFIXES on
  its worklist, never import paths: source imports convert via
  `pathToPrefix` exactly once, on push, and the table's dep columns —
  already prefixes, gc's own R_INITORDER edges — go on verbatim. No
  wire, decoder, or table change; the graph's CONTENT was always right,
  only the closure's lookups missed. Flipped exactly the 2 predicted
  reds; the single-package control and the whole pre-existing baseline
  held.)
- Pinned-by: differential
- Cases: multipkg/inittask-escape, multipkg/inittask-escape-closure
  (multipkg/inittask-escape-single is the green single-package control)

Found by the raft-W2.2 frontier sweep (`docs/raft-w3-log.md` §2.2,
handoff H-9): with the raft root package vendored, the export refused
with `package "crypto/internal/entropy/v1%2e0%2e0" is not in the stdlib
inittask table` — and the table HAS that row (`inittask-std.tsv`, the
one escaped prefix in the go1.26.5 stdlib, with the unescaped path in
its 4th column).

The defect: `buildInitGraph`'s worklist mixed two namespaces. Source
units pushed their imports as PATHS; the closure loop then pushed
`entry.deps` — which are already-escaped symbol PREFIXES read from the
compiled archives — onto the same list, and re-applied `pathToPrefix`
to every popped item. `pathToPrefix` escapes `%` (it must — objabi
does), so `crypto/internal/entropy/v1%2e0%2e0` became
`crypto/internal/entropy/v1%252e0%252e0` and the lookup missed. Not a
raft quirk: ANY multi-package program whose stdlib init closure reaches
the fips140 entropy module refused — measured from the table, that is
the whole crypto family plus net/http, expvar, and ~30 more non-internal
std packages, most of them deps-of-deps away from the escaped row
(the `-closure` case pins crypto/sha256, which never names entropy
directly).

Why no corpus case ever hit it: `specInitOrder` returns early below two
source units (`load.go`), so single-package programs — the overwhelming
majority of the corpus — never build the init graph at all
(`inittask-escape-single` pins that immunity as a control). The bug was
reachable only from the multi-package corpus, whose stdlib imports
(`sync`, `errors`) all carry escape-free prefixes.


## BUG-065 — W3.2 boundary widening: five rows' exhaustive envelope certification left tractability

- Status: open — NARROWED to one row (POR slice 2026-08-21,
  `docs/2026-08-21_w32-por-design.md`): four of the five certify under
  `engine=dedup` — the state-graph dedup certifier whose accepted
  certificates are THEOREM-backed equal to `SlowObs`
  (`checkCertM_slowObs`) — request-reply (36k node+edge work: 17.6k
  nodes + 18.4k edges, 0.3 s; corrected 2026-08-21 from "18k", which
  was the EDGE count alone and so was inconsistent with the three
  node+edge sums beside it — audit finding B-F6),
  sb-chan (736k, 5.7 s), google-search (12.8M, ~157 s; fresh
  tier=slow record), rwmutex-order (207k, 0.9 s; tier dropped). The
  two standing `--slow` alarms are RESOLVED. Residual:
  goroutines/worker-pool/sum — its (pool × detector) state graph
  exceeds the dedup budget too (>9.5M nodes without closure); it
  stays an honest fast-lane red awaiting the reduction/mover lane
  (slice 5) or a per-row ruling. (Re-homed 2026-08-31, fidelity
  decision 6 [USER]: the reduction/mover lane is parked on
  `park/reasoning-2026-08-31`; the live owner is this repo's
  TODO.md backlog — a per-row ruling or a revived reduction lane.)
- Pinned-by: differential (enumeration cap breaches, fail-loud)
- Cases: goroutines/worker-pool/sum

W3.2 slice 1 stages C/D (B1 `.opDone` post-op boundaries + B2
back-edge boundaries; G1 ruling 2026-08-20) widen the scheduling-point
set — the doctrine's re-envelope of register #1, implemented as
designed. The cost: enumeration trees branch at every new point, and
five rows' exhaustive certification left tractability entirely
(measured 2026-08-20/21, dev box):

- goroutines/pipeline/request-reply (confluent): >400M steps
  unfinished (pre-B1 tree ≤ 1.2M).
- goroutines/worker-pool/sum (confluent): >400M (pre-B1 ≤ 15M).
- race/litmus/sb-chan (membership, members=3): >400M (pre-B1 ≤ 5M).
- imported-goose/channel/google-search (membership, tier=slow):
  >900M (pre-B1 40.0M). NOT on the Cases line: its fast-lane result
  is CERTIFIED-CACHED green against the pre-B1 record per the tiering
  design; the staleness surfaces as the recorded `--slow` drift alarm.
- sync/rwmutex-order (membership, tier=slow): >~900M (pre-B1 2.2M).
  Same cached-green/slow-alarm structure.

The Cases row fails loud at its existing cap on every run (the entry
previously said "the three Cases rows" while the Cases line carries
ONE id — the POR narrowing shrank the list without this sentence;
corrected 2026-08-22, launch audit D7)
(honest reds, seconds each). Fix directions, all recorded in
`docs/w32-log.md` stage C: (a) the boundary-set note §5c sampled
fallback (witness-replay machinery drafted and REVERTED pending the
user ruling — a claim-standard change is not the arc's to make);
(b) budget raises (measured infeasible at hosted-runner scale);
(c) THE PRINCIPLED FIX: the reduction/DPOR lane (NPDRF, slice 5) —
sound schedule reduction re-shrinks exactly these trees, and the
mover theorem resumes over the widened point set by design.

## BUG-066 — slice expression with an elided high bound evaluates its base TWICE

- Status: fixed (2026-08-21, holes arc — `emitSliceExpr`'s default-high
  arm: an array operand takes its static length constant; a
  slice/string operand's `builtin-len` reuses the single emitted base
  node. All four pinned rows flipped FAIL→PASS; explicit-high control
  and every slice/eval-order relative unmoved; goldens unchanged.)
- Pinned-by: differential
- Cases: slices/slice-elided-high-eval-once/call-base, slices/slice-elided-high-eval-once/call-base-low-only, pointers/slice-elided-high-pointer-array-base, strings/slice-eval-order-elided-high, slices/slice-elided-high-eval-once/nested-slice-expr, slices/slice-elided-high-eval-once/map-index-effectful-key, slices/slice-elided-high-eval-once/pointer-array-call-base, slices/slice-elided-high-eval-once/conversion-base

`spec#Slice_expressions` evaluates the sliced operand ONCE; the elided
high bound "defaults to the length of the sliced operand" — a default
over the one evaluated operand, not a second evaluation. The frontend's
`emitSliceExpr` (`tools/nativefrontend/emit.go`) emitted the base at
the base slot and then, for an elided high, emitted the SAME operand a
second time as the `builtin-len` argument. Each emission of a
call-valued operand hoists a fresh `$cN := call` temp, so the call ran
twice: `expensive()[:]` — gc 1 call, machine 2, status `ok` on both
sides. The wire shows it directly: two call statements, `$c1` as the
slice base and `$c2` inside the `builtin-len`.

Both witnessed forms reproduce: the slice base (`expensive()[:]`,
machine 230 vs go 130 on the pinned encoding; low-only `[1:]` sibling
220 vs 120) and the pointer-returning array base (`pf().arr[2:]`,
machine 223 vs go 123 — the census's first-pass value-returning form
`f().arr[2:]` is not legal Go, an array sliced through a call result is
unaddressable). The explicit-high control (`expensive()[0:3]`) agrees
at 1 call on both sides, pinned green. `strings/slice-eval-order` was
the near miss — it pins base→low→high order with an EXPLICIT high, so
its elided-high sibling (`strings/slice-eval-order-elided-high`,
machine 12228 vs go 1328: source, lo, source again) is what an
eval-once regression would trip.

Every other documented eval-once hazard was guarded
(`emitReadWriteTarget`; BUG-047's conversion guard) — this one was
unguarded and unpinned, `ok`-status silent since `a18ebd24`
(2026-07-18). Found by the W7 desugar census (§10 H-a,
`docs/2026-08-21_w7-desugar-inventory.md`), reduced to a witness by its
pre-merge audit — reasoning over the emitter, not any gate.

Fix shape: emit the base once and reuse it — slices/strings reuse the
single emitted base node as the `builtin-len` operand (its effects were
hoisted by that one emission); array bases take the STATIC array length
as the default high (exactly the spec's `len(a)` for an array operand,
constant even when the operand expression contains calls — the operand
itself still evaluates once at the base slot, through its address).

WIDENING (holes-arc audit fix round, 2026-08-21, finding F1 — recorded
here because it is a movement this fix caused, even though it is not a
defect). Removing the second emission removed an ACCIDENT that was
covering a different, pre-existing hole: for a NIL pointer-to-array with
an elided high, `(*ap)[:]` and `(*ap)[1:]` used to answer gc's recovered
panic — because the re-emitted operand inside the `builtin-len`
dereferenced the nil pointer and panicked. With the base evaluated once
and the array's static length used as the default high, nothing
dereferences, and the shape converges on the documented refusal of the
slice-base nil arm (`pointers/nil-array-ptr-slice/slice-expr-nil`, the
explicit-high sibling, red since 2026-08-19): an honest STUCK,
"expected array or slice value for slice expression, got GoValue.nil".
Measured, not argued — the 6146b217 emitter vs the 90b12339 one through
the same decoder: `(*ap)[:]`/`(*ap)[1:]` ok/100 → stuck, while `ap[:]`
and the `*[0]int` form were ALREADY stuck before the fix. **Fail-closed
in both directions: a right answer for the wrong reason became a visible
refusal, never a wrong answer.** Pinned by
`pointers/nil-array-ptr-slice-elided-high/*` — four reds tracked in
`baselines/untriaged-ids` at the sibling's `coverage` disposition (they
retire together, with that arm), and two greens (`field-through-nil-ptr`,
`field-through-nil-call`) showing the refusal is the slice-base arm
specifically: a nil pointer reached through a FIELD selector still
panics correctly.

Also newly pinned in the same round (finding F2), four base shapes the
fix corrected that nothing covered — `f()[1:][1:]` (the nested case, the
sharpest one: the inner slice expression is the outer's base, so the
call ran FOUR times, gc 133 vs pre-fix machine 433), a map-index base
with an effectful key (122 vs 222), `pf()[1:]` on the pointer-reuse path
(128 vs 228), and a conversion base `[]byte(f())[1:]` (131 vs 231, the
shape BUG-047's conversion guard does not reach). All four green
post-fix; `slices/slice-elided-high-eval-once/{nested-slice-expr,
map-index-effectful-key,pointer-array-call-base,conversion-base}`.

## BUG-068 — a local shadowing a NAMED RESULT aliased the result slot at the return/frame-exit seam (silent wrong answer)

- Status: fixed (2026-08-21, raft W4.3 wave 6 — emit-time renaming of
  shadowing locals, object-keyed: `tools/nativefrontend/resultshadow.go`
  + the local-name emission sites. Boundary CORRECTED by the 2026-08-22
  audit fix round, which found this entry's first version claiming
  refusals the scan did not deliver: range clauses refuse (pinned by
  the red-by-design `range-clause` row); type-switch guards were
  SILENTLY MISSED — their bindings live in go/types Implicits, not
  Defs — and aliased exactly as this bug describes (audit R1-C3, probe
  machine-false-vs-go-true; now explicitly refused, red-by-design
  `ts-guard` row); comma-ok `:=` receive/map/assert targets are NOT
  refused — they are admissible AssignStmt-DEFINE forms and are
  RENAMED correctly (audit R1-D1, green rows `commaok-{map,recv,
  assert}`). The audit round also fixed two more seams the rename did
  not reach: the closure-capture ref (R1-C1) and the per-iteration
  cell machinery (R1-C2), each with its own witnessed-red guardrails.)
- Pinned-by: differential
- Cases: scoping/named-result-shadow/enterjoint-shape, scoping/named-result-shadow/bare-return, scoping/named-result-shadow/short-decl, scoping/named-result-shadow/deferred-write
  (`range-clause` and `ts-guard` stay RED BY DESIGN —
  they pin the fail-closed REFUSAL for shadows outside the rename set,
  not the fix, so they are not listed as fixed cases)
- Discovered: 2026-08-21 (the trace differential's RENDERED tier — the
  first tier that could see it: `confchange_v2_add_double_{auto,implicit}`
  machine-vs-go DISAGREE on `... switched to configuration ... autoleave`)

The wire carries variable NAMES; the machine writes named results at
`return` and reads them at frame exit BY NAME. A function-local
variable declared with the same name as a named result — upstream
raft's `ConfChangeV2.EnterJoint` does exactly this (`(autoLeave bool,
ok bool)` with an inner `var autoLeave bool`) — aliased the slot: the
return's write landed on the lexically-nearest (inner) binding while
the frame exit read the outer result local. go/types resolves the
source correctly; the wire's name channel could not carry the
distinction. Minimized to a 50-line probe
(`artifacts/w43/probe-autoleave`: go 111110, machine-before 111010 —
the shadowed closure returning false where gc returns true), fixed,
probe and both traces re-verified agreeing. Found by READING NOTHING:
the ok tier and the oracle-symmetric byte tier were structurally blind
to it (the W4.2 tier-strength bound, vindicated in its first campaign
— the rendered tier is the mirror-falsifying channel, and here it
falsified the MACHINE).

## BUG-067 — wire func TYPE nodes drop the variadic bit: `func(...int)` ≡ `func([]int)` to the machine

- Status: fixed (2026-08-21, holes arc — the wire func type node
  carries `variadic`, the decoder REQUIRES it, `Ty.funcType` gained
  the field into `Ty.eqbFuel` identity and the panic-message render
  (`...E` last parameter). Blast radius swept over all 1119 emittable
  corpus wires BEFORE the confirming run: besides the new guardrails,
  exactly three `variadic/*` rows carry a `variadic:true` func TYPE
  node, all value-storage/call shapes with nothing consuming the bit —
  predicted flips exactly the two pinned reds, confirmed. Pinned
  Muxer/Defer terms extended with the explicit `false` the fresh
  decode now produces; imported-pin and golden gates green.)
- Pinned-by: differential
- Cases: interfaces/assert-func-variadic/mismatch-variadic-at-slice, interfaces/assert-func-variadic/mismatch-slice-at-variadic, interfaces/assert-func-variadic/assert-variadic-at-slice-panic

`spec#Type_identity`: two function types are identical only if they
have "the same number of parameters and result values, corresponding
parameter and result types are identical, and either both functions
are variadic or neither is." The emitter's `emitType` Signature arm
(`tools/nativefrontend/wire.go`) lowered `func(...int) int` and
`func([]int) int` to the same `{"kind":"func","params":[[]int],
"results":[int]}` — go/types types the variadic parameter `[]int` and
the bit lived nowhere else in the node. The contrast was deliberate
elsewhere: `variadic` IS carried on `Func` declarations and on
interface-method requirements (pre-merge audit 2026-07-31 finding 0),
so the METHOD-SET direction answers correctly — the existing
`interfaces/method-set-variadic-mismatch/*` family (5 rows, finding 0's
own guardrails) is the standing green control; the TYPE nodes were the
hole.

Witness (census §10 H-d, `docs/2026-08-21_w7-desugar-inventory.md`,
verified end to end): box a variadic func in `any`, comma-ok assert at
`func([]int) int` — gc `false`, machine `true`, status `ok`. Both
`type-assert` statements carry byte-identical `targetType` and the
boxed value's dynamic type is that same node, so no semantics the
machine could give the node answers both assertions correctly — the
information is gone before Lean sees it. Both directions pinned
(machine 11 vs go 1 on the int encodings). Silent since `7ce738bc`
(2026-07-25). The first pass's "not observable in the current refusal
envelope (reflection is refused)" was refuted by the audit: a comma-ok
func-type assertion is ordinary supported Go.

Fix shape: the wire func type node carries `variadic`; the decoder
REQUIRES it (the §9.5 fail-closed discipline, same as func/method/
interface-requirement decodes) and `Ty.funcType` carries the bit into
type identity, where `Ty.eqbFuel` compares it.

STATUS-DIVERGENCE CLASS (holes-arc audit fix round, 2026-08-21, finding
F3). The comma-ok witness above understates the hole: it loses a
BOOLEAN. The single-result form loses the CONTROL PATH — `_ =
i.(func([]int) int)` on a boxed `func(...int) int` must panic, and
pre-fix the machine returned normally, `{"status":"ok","values":[0]}`,
against gc's `panic: interface conversion: interface {} is
func(...int) int, not func([]int) int`. A status-direction divergence at
status `ok` is the worst readout this ledger has a name for: a caller's
`recover` never runs and the program continues past a point Go stops at.
The row also pins the RENDER, byte-exact against gc's message, so the
`...E` spelling `goTypeNameForMessageFuel` emits for a variadic
signature's last parameter is regression-covered — dropping the bit from
the message, not just from identity, is red.
`interfaces/assert-func-variadic/assert-variadic-at-slice-panic`; green
post-fix.

## BUG-069 — shadowed predeclared `true`/`false`/`nil` mis-lowered as the universe constants (silent wrong answer)

- Status: fixed (2026-08-22, launch-audit fix round — `emitIdent`'s
  name-keyed switch deleted; `nil` recognized by its go/types object
  (`*types.Nil` in `Uses`), `true`/`false` need no arm at all since
  genuine uses carry a constant value and fold through
  `emitConstValue`'s `constant.Bool` arm, which emits the identical
  wire node)
- Pinned-by: differential
- Cases: scoping/predeclared-shadow/shadow-true-branch, scoping/predeclared-shadow/shadow-false-branch, scoping/predeclared-shadow/shadow-param, scoping/predeclared-shadow/shadow-var-form, scoping/predeclared-shadow/shadow-nil-len, scoping/predeclared-shadow/shadow-nil-append, scoping/predeclared-shadow/shadow-nil-int, scoping/predeclared-shadow/genuine-ctrl
- Discovered: 2026-08-22 (the whole-stack launch audit's broad-brief
  reviewer D10, probing weird-but-legal programs; blast radius widened
  by verifier V1)

`emitIdent` opened with `switch id.Name { case "true": ... case
"false": ... case "nil": ... }` — resolving the three names to the
universe constants BEFORE consulting `e.info.Uses`. The predeclared
identifiers live in the universe scope and are shadowable
(`spec#Declarations_and_scope`); a local `true := false`, a parameter
named `true`, or `nil := []int{...}` is an ordinary variable, and every
READ of it was mis-lowered as the literal. Observed outcomes depended
only on how the literal type-checked downstream: silent wrong values
(`true := false; return true` → machine true, gc false), a silently
wrong BRANCH (`false := (1==1); if false {...}` took the wrong arm), a
silent wrong `len` (`nil := []int{1,2,3}; len(nil)` → machine 0, gc 3),
a FABRICATED panic (append-then-index through a shadowed `nil` slice:
machine index-out-of-range, gc 29), and one honest stuck (`nil := 5`).
The write path was always correct (declarations travel through `Defs`,
name-preserving) — only reads short-circuited. Shadowed `len`/`cap`
etc. were never affected: builtins are not in the switch and resolve
through go/types.

The switch was the oldest untouched line in the frontend (first
vertical slice, 2026-07-18, `59c20a46`), and no idiomatic program
shadows these names — the corpus had zero occurrences, so the
differential was structurally blind (BUG-002's epistemic class: found
by probing imagination, not by any green gate). Adjacent to BUG-068
(shadowing a NAMED RESULT) but a different mechanism: 068 was the
wire's name channel too weak to carry a resolved distinction; 069 was
the emitter not consulting the resolution at all.

## BUG-070 — unsafe.Sizeof/Offsetof/Alignof folded gc's layout into the wire with no refusal

- Status: fixed (2026-08-31, t1-fidelity-fixes — `checkUnsafeLayoutOps`
  in tools/nativefrontend/emit.go: any reference to unsafe.Sizeof /
  unsafe.Offsetof / unsafe.Alignof refuses the WHOLE export, naming
  the operator and its source position. Whole-export rather than
  per-decl quarantine because the folded constant launders through
  named constants (`const s = unsafe.Sizeof(...)`) into use sites
  whose own subtrees a per-site scan would never flag. No
  spec-forcedness carve-out: even fixed-width-type operands refuse —
  a carve-out would embed a layout-forcedness census in the frontend
  to preserve one attestation row, and the fold that row attested was
  go/types', not the machine's. COMPLETED at the audit fix round
  2026-09-01: the scan is selector-based, and `import . "unsafe"`
  made the layout ops BARE identifiers that walked straight past it
  (audit probe u2 exported Sizeof's fold cleanly) — dot-imports of
  unsafe now refuse OUTRIGHT, before the selector walk, pinned by
  unsafe/dot-import/sizeof-bare.)
- Pinned-by: none (the refusal surfaces at `frontend-export` — a
  coverage-stage boundary marker, not a fidelity pin; the rows below
  are listed so the baseline deltas of the fix ride a Cases: line.
  The fix's one PASS→gone flip was the REMOVAL of the row
  `unsafe/boundary/sizeof-const` — named here in prose, not on the
  Cases line, because the id no longer exists in the baseline for
  check-bugs to verify; the Baseline-deltas paragraph below carries
  the removal record)
- Cases: unsafe/layout-ops/sizeof-fixed, unsafe/layout-ops/layout-struct, unsafe/dot-import/sizeof-bare
- Discovered: 2026-08-31 (fidelity assessment phase 2,
  p2-keeps-a2a3bcd §1.1 — severity: boundary breach, not a
  wrong-vs-pinned-oracle answer)

Pre-fix, the three layout operators passed through `go/constant` at
type-check time and landed on the wire as anonymous integer literals:
the assessment probe's `int(unsafe.Sizeof(int(0)))*1000 +
int(unsafe.Sizeof(S{}))*10 + int(unsafe.Offsetof(S{}.b))` exported
clean as the literal `8248` — gc-amd64's implementation-specific
layout (386/arm: `4164`; only the fixed-width types' sizes are forced
by spec#Size_and_alignment_guarantees) inside a model that claims
portability, with the pinned-oracle differential structurally green on
it. The language-coverage ledger classified Package_unsafe
out-of-language with the boundary "kept VISIBLE" by marker reds — but
the only mechanism was the unsafe.Pointer wire-TYPE refusal; the
layout operators had no mechanism at all, and what kept the corpus
honest was curation (the boundary case deliberately used only
spec-forced operands). The boundary is now a mechanism. Baseline
deltas: `unsafe/boundary/sizeof-const` (PASS) REMOVED — its
spec-forced shape moved to `unsafe/layout-ops/sizeof-fixed`, refused
by the mechanism like every other operand; `unsafe/layout-ops/
{sizeof-fixed,layout-struct}` are the new red-by-design refusal pins;
`unsafe/boundary/pointer-roundtrip` keeps its own distinct
Pointer-type refusal (the two boundary mechanisms stay separately
attested).

## BUG-071 — the dynamic fmt shim rendered fmt.Formatter implementors through error/Stringer (recorded silent-wrong-answer class, now closed at emit time)

- Status: fixed (2026-08-31, t1-fidelity-fixes; key NARROWED at the
  gate-red fix round 2026-09-01 and COMPLETED at the audit fix round
  2026-09-01 — `checkFormatterDynHole` + `walkFormatterBoxing` in
  tools/nativefrontend/fmtdesugar.go, called from emitProgram. The
  original whole-export key ("dyn bundle injected AND any declared
  type implements Formatter") over-fired — v-composites' deliberate
  static-refusal implementor killed its 16 sibling rows — so it was
  narrowed to BOXING REACHABILITY: with the dynamic fmt bundle
  (goleanShimFmtDynVerb) injected and a fmt.Formatter implementor
  (value or pointer receiver) declared in ANY unit, the export
  refuses iff some unit boxes an implementor into an interface
  OUTSIDE the fmt-owned operand positions the static path already
  polices — an implementor that is never boxed cannot reach a dyn
  site. THE KEY IS ENUMERATIVE, NOT DERIVED: its soundness rests on
  walkFormatterBoxing's context list matching every boxing context
  the modeled fragment admits (assignments/var specs incl. tuple
  results, non-fmt call arguments incl. variadic, returns,
  conversions, composite-literal fields/elements/keys, map index
  keys, channel sends, interface-operand comparisons, `=`-form range
  key/value targets, expression-switch case comparisons). That list —
  in the checkFormatterDynHole header — is the NAMED EXTENSION POINT:
  a construct added to the modeled fragment that can box must be
  added there in the same change, and a context missing from it is a
  reopened silent-wrong-answer channel (the 2026-09-01 audit found
  four: see below). Two conservative closures ride the key: a
  TYPE-PARAMETER-typed operand boxed inside a generic body is a HIT
  whenever an implementor is declared anywhere (types.Implements is
  undecidable for a type parameter), and the implementor scan is
  DECOUPLED from the boxing walk (implementor in pkg A + boxing in
  pkg B refuses). Whole-export because boxing travels — no per-decl
  scan can bound which dyn site the implementor reaches. Static fmt
  sites keep their standing per-verb refusals (refuseFormatter,
  fmt/formatter-precedence pins); the two mechanisms stay separately
  attested.)
- Pinned-by: none (the refusals surface at `frontend-export` — the
  rows below are the red-by-design refusal pins, listed so the
  baseline deltas of the fix ride a Cases: line)
- Cases: fmt/formatter-dyn-hole/dyn-boxed, fmt/formatter-box-range/range-assign, fmt/formatter-box-generic/generic-body, fmt/formatter-box-crosspkg/cross-package
- Discovered: 2026-08-22 as audit R1-F2's RECORDED BOUND (W4.3 fix
  round: "recorded, not closed; nothing in the subject tree
  implements fmt.Formatter" — a raft-subject bound, not a mechanism);
  promoted to a fix by the 2026-08-31 fidelity assessment (A3-S3:
  under the fail-closed doctrine a recorded silent-wrong-answer
  channel is a defect, its subject-tree bound curation)

gc's handleMethods consults Format FIRST, for every verb; the dyn
shim runs inside the model with no reflection and cannot ask "does
the dynamic type implement fmt.Formatter" (fmt.State is unmodeled, so
no goleanShim interface can name Format's signature). Pre-fix, a
value whose type implements BOTH Formatter and error/Stringer, boxed
through any/variadic into a dyn site, rendered via Error/String where
gc calls Format — both sides `ok`, different strings, nothing red
(probed: machine "via-string" vs gc "via-format" on the dyn-boxed
shape). The boxing key is conservative WITHIN its enumeration — an
implementor boxed on a path that never reaches a dyn site still
refuses (visible over-refusal) — but its soundness is ENUMERATIVE: a
boxing context missing from walkFormatterBoxing's list is a reopened
silent-wrong-answer channel, which is exactly what the 2026-09-01
pre-merge audit found in the narrowed key's first shipping: four
shapes exported and rendered "via-string" where gc prints
"via-format" (`=`-form range assignment; type-parameter boxing inside
a generic body, where types.Implements answers false; the
expression-switch case comparison; and the implementor-in-pkg-A /
boxing-in-pkg-B split the per-unit scan coupling missed). All four
refuse since the audit fix round; three are pinned by the
formatter-box-* rows on the Cases line, and the switch-case shape is
covered by the same walk arm as interface comparisons (audit probe
fm7 re-verified). The context list in the checkFormatterDynHole
header is the standing extension point. Formatter-ONLY types (no
error/Stringer leg) already fell to the dyn shim's unmodeled-kind
refusal; the boxing key refuses those exports up front too,
uniformly.

## BUG-072 — the stdlib function-VALUE refusal named a phantom cause ("field selector on anonymous struct type invalid type")

- Status: fixed (2026-08-31, t1-fidelity-fixes — emitSelector
  (tools/nativefrontend/emit.go) intercepts NON-source
  package-qualified selectors in value position before the
  field-selection machinery: an allowlisted shim member as a value
  (`f := strings.Fields`) refuses naming the E5 direct-call-only
  policy; every other stdlib-qualified value-position selector
  refuses naming the modeled-surface boundary. The BOUNDARY is
  unchanged — those shapes always quarantined — only the refusal's
  cause is honest now.)
- Pinned-by: none (the rows below pinned the two refusal messages, red
  by design, until 2026-09-03; under stdlib source-through slice 1
  (`stdlib-source-1`, docs/2026-09-03_stdlib-boundary-design.md §6) the
  VALUE shape of a `strings` member is a real function value — the
  library unit is on the wire — so both rows now PASS: `f :=
  strings.Fields` and `f := strings.Contains` call the lowered upstream
  bodies. The boundary this bug was about (an honest cause for a refusal)
  is moot for source-through packages; it still holds, unchanged, for
  every package NOT on the allowed-library list. Evidence: `docs/evidence/2026-09-03_stdlib-source-1/`.)
- Cases: strings/shim-value-refused/shimmed-value, strings/shim-value-refused/unmodeled-value
- Discovered: 2026-08-31 (fidelity assessment phase 2,
  p2-keeps-a2a3bcd §1.3 instance 1 — severity: charter conformance,
  not a wrong answer: "an explicit refusal that NAMES ITS CAUSE at
  the point of failure" named an anonymous struct that does not exist
  in the program)

Mechanism: `strings.Fields` in value position has no go/types
Selection (qualified identifiers resolve by name, not selection) and
`strings` is not a source package, so the selector fell through to
the promoted-field/fieldBase machinery, where goTypeOf of a package
name is the invalid type — hence the phantom. The stdlib-shim policy
header (stdlibshim.go) had always said the function-value shape
"keeps existing refusals"; assessment A3-S7's claim (iv) ("narrowings
named in refusals") failed on exactly the row it cited.

## BUG-073 — strings.Repeat's oversized-output stop named no cause (fuel-out/OOM instead of a refusal); upstream's overflow panic was unmodeled

- Status: fixed (2026-08-31, t1-fidelity-fixes — two arms in the
  Repeat shim (stdlibshim.go), both checked UP FRONT from len(s) and
  count before any allocation: (1) upstream's output-length overflow
  panic modeled VERBATIM — `panic("strings: Repeat output length
  overflow")` exactly when len(s)*count > maxInt, matching deps/go @
  go1.26.5 strings.Repeat; an ordinary RECOVERABLE panic per the shim
  header's split, upstream-faithful panics stay panics. (2) below
  overflow, outputs past the golean bound (1<<24 bytes) refuse BY
  NAME through the force-quarantined cause-named helper
  goleanShimStringsRepeatBound (shimRuntimeRefusalReasons, emit.go) —
  the unrecoverable R4-C-3 stop whose observation text itself names
  the Repeat bound.)
- Pinned-by: differential (repeat-overflow, both sides panic with the
  identical message — since 2026-09-03 (`stdlib-source-2`) from the REAL
  `strings.Repeat` body, the shim and its two arms being RETIRED).
  repeat-bound-refused WAS the red-by-design refusal pin demonstrating
  the shim's cause-named 1<<24 bound; with the shim gone there is no
  golean bound in Repeat at all — the row (a 16 MiB output gc allocates
  fine) is now a RUNNER-BUDGET red: the machine cannot materialize it
  within the 30 s row budget (`lean-observation`, "TIMED OUT after 30s
  (LEAN_TIMEOUT_SECONDS)" — the runner names the cause; the cost is
  BUG-090's allocation-count-quadratic interpreter heap, measured in the
  slice-2 evidence README), deliberately FAIL forever, so it stays OFF
  the Cases line (check-bugs rule 3). The red's COLOUR depends on the
  box and on LEAN_TIMEOUT_SECONDS: a faster host or a longer budget
  could turn a 16 MiB Repeat green without any change here — which is
  why it sits on BUG-090's Cases line as a BUDGET pin (a resource
  refusal), not as a designed semantic red. The memo (§3 row 5) pre-announced
  exactly this outcome: "else stays an honest budget refusal
  (re-expected with reason)".
- Cases: strings/trimspace-repeat/repeat-overflow
- Discovered: 2026-08-31 (fidelity assessment phase 2, A3-S5: the
  Repeat output-length delta was argued "a visible stop, never a
  wrong answer" — but the stop was fuel exhaustion or a memory
  blow-up that under scripts/capped presents as infra death, the one
  delta in the shim table whose failure mode did not name its cause)

The golean bound is honest-refusal territory, not fidelity: upstream
gc allocates a 16 MiB+ Repeat fine, while the shim's quadratic loop
concatenation could never realize it within machine resources — the
bound converts an hours-long fuel grind (or a capped OOM) into an
instant, cause-named, unrecoverable refusal. Recorded residual: the
region between the bound and upstream's overflow stays a
machine-refuses/gc-succeeds delta BY DESIGN (visible red, never a
wrong answer); outputs at or above overflow now agree with gc
exactly.

## BUG-074 — select left effect-free clause operands un-snapshotted: re-read at COMMIT, after a later clause's entry-time effects (silent wrong answer / wrong deadlock)

- Status: fixed (2026-09-01, gotest-fixes — emitSelect +
  selectRecvClause (tools/nativefrontend/emit.go) now hoist EVERY
  clause channel operand and send RHS value into an entry-time temp,
  in source order, effect-free or not; the clauses reference the
  temps, so commit-time reads see the entry snapshot)
- Pinned-by: differential
- Cases: channels/select-entry-snapshot/send-value-snapshot, channels/select-entry-snapshot/chan-operand-snapshot
- Discovered: 2026-09-01 ($GOROOT/test harvest,
  docs/2026-09-01_gotest-triage.md M1 — fixedbugs/issue4313.go, go ok
  vs machine panics 42; fixedbugs/issue43111.go, go ok vs machine
  deadlocks; one root cause)

Spec (spec#Select_statements step 1): on entry, ALL channel operands
of receive clauses and BOTH the channel and right-hand-side
expressions of send clauses are evaluated exactly once, in source
order. The lowering realized entry-time evaluation only for EFFECTFUL
subexpressions (the A-normal-form statement hoists); an effect-free
operand (a plain `x`, a global `ch`) stayed embedded in the clause
node and was read again at COMMIT time — after a LATER clause's
hoisted entry-time effects had mutated it. issue4313's shape sends 42
where gc sends the entry-time 0; issue43111's shape re-reads a
channel variable its sibling clause's RHS closed-and-nil'd at entry,
and deadlocks on the nil where gc receives from the entry-time
(closed) channel. Latitude check: C5/C6/C7 (which clause commits) are
untouched — this is spec-PINNED evaluation order, not clause-choice
latitude; the fix adds entry-time temp assigns and changes no
readiness/commit machinery. The full select corpus slice re-ran green
(counts in the branch record).

## BUG-075 — multi-value `return` stored result 1 before operand 2 evaluated: a recovered panic exposed the partial store (silent wrong answer) [TRUST-ADJACENT: wire decoder]

- Status: fixed (2026-09-01, gotest-fixes — decodeReturn
  (GoLean/NativeToIR.lean) lowers `return e1, .., en` (n ≥ 2)
  two-phase: every operand evaluates left-to-right into a fresh
  `$ret<i>` temp, THEN all temps store to the result locals, then
  returnStmt — the same phase split the multi-assign path already
  had; n = 1 keeps the single-assign shape)
- Pinned-by: differential
- Cases: returns/multi-return-two-phase/panic-second-operand-unnamed, returns/multi-return-two-phase/panic-second-operand-blank-named
- Discovered: 2026-09-01 ($GOROOT/test harvest,
  docs/2026-09-01_gotest-triage.md M2 — fixedbugs/issue43835.go, go
  ok vs machine panics FAIL; the f/g/h probes isolated the return
  path: the assign path was already two-phase and correct)

Spec (spec#Return_statements): "return e1, .., en" assigns to the
result variables LIKE AN ASSIGNMENT — all right-hand operands
evaluate before any store. The decoder lowered it as sequential
per-result assigns (`assign r1 := e1; assign r2 := e2; ...`), so e1's
store landed before e2's panic; with a deferred recover, the partial
store was observable through named/blank results (issue43835 g/h). A
control row pins the already-correct assign-path sibling
(returns/multi-return-two-phase/assign-control). This is the wire
decoder — trusted surface — flagged [TRUST-ADJACENT]; the change is
the documented two-phase lowering only, no new machine operations.

Cross-reference (2026-09-02): the assignment-side twin of this bug,
latitude-inventory row **E5** (gc stores an earlier multi-assign
target before a LATER operand's panic, visible under recover), was
RE-LABELLED from latitude to **gc DEVIATION** by [USER] ruling on
2026-09-02 — `docs/spec-divergence-ledger.md` L-016. This entry was
one of the three witnesses for that ruling: the machine's early store
at `return` was treated here as a wrong answer under the SAME two-phase
sentence, so gc's identical shape at `=` cannot be latitude. The same
gc regression test (issue43835.go) that exposed this bug is gc's own
assertion of the no-early-store rule — gc passes it (its fix covers
result parameters and `return`) and deviates only on ordinary locals,
which is the E5 shape.

## BUG-076 — array/pointer-to-array range expressions were ALWAYS evaluated: the spec's non-evaluation special case was missing (spurious panic)

- Status: fixed (2026-09-01, gotest-fixes — emitRange
  (tools/nativefrontend/emit.go): with at most one iteration variable
  present (rs.Value syntactically absent — a blank second variable
  counts as present, go/types' sValue test) and no channel receives
  or function calls in the range expression (exprHasCallOrRecv, an
  arm-for-arm mirror of go/types' hasCallOrRecv — conversions don't
  count, constant-folded builtins don't count and discard their
  argument's events, func-literal bodies are skipped), BOTH the
  direct-array and the pointer-to-array lowerings emit the
  static-length int desugar WITHOUT emitting the range expression at
  all)
- Pinned-by: differential
- Cases: range/range-not-evaluated/deref-nil-no-var, range/range-not-evaluated/deref-nil-key-only, range/range-not-evaluated/field-ptr-nil-no-var
- Discovered: 2026-09-01 ($GOROOT/test harvest,
  docs/2026-09-01_gotest-triage.md M3 — fixedbugs/issue72844.go, go
  ok vs machine panics nil-dereference on `for range *p`; the len(*p)
  special case was already right, range was missing exactly the same
  treatment)

Spec (spec#For_statements: "if at most one iteration variable is
present and len(x) is constant, the range expression is not
evaluated"; spec#Length_and_capacity: len(x) is constant for array /
pointer-to-array x with no channel receives or function calls). The
old lowering evaluated the direct-array expression unconditionally
(`for range *p`, nil p: panic where gc iterates 4 times), and the
pointer-to-array index-only arm evaluated the POINTER expression once
(right for `for range p`, wrong for `for range s.p` with s nil — the
selector's implicit deref panicked where gc, not evaluating, does
not; caught by inspection at the fix, not by the harvest — the
sibling shape rode the same fix). Both boundary directions are
pinned: two iteration variables → evaluated → panic
(range/range-not-evaluated/deref-nil-two-vars-panic), a call in x →
evaluated exactly once
(range/range-not-evaluated/call-evaluated-once).

## BUG-077 — the CONVERSION form of nil at interface/func types (`error(nil)`, `any(nil)`, `(func())(nil)`) refused: the machine's nil-literal arm had no interface/func arms (wrongly-stuck) [TRUST-ADJACENT: interpreter]

- Status: fixed (2026-09-01, gotest-fixes — the `.nilLit` operator
  (GoLean/GoCore/Machine.lean) gains `.interface _ => .nil` and
  `.funcType _ _ _ => .nil` arms, the zero values `defaultValue`
  already yields for both types)
- Pinned-by: differential
- Cases: interfaces/nil-conversion/error-nil, interfaces/nil-conversion/any-nil, interfaces/nil-conversion/typed-nil-vs-error-nil, interfaces/nil-conversion/func-nil
- Discovered: 2026-09-01 ($GOROOT/test harvest,
  docs/2026-09-01_gotest-triage.md suspicious-refusal 1 —
  issue19911.go, issue53619.go, typeparam/issue42758.go refused "nil
  literal for non-nilable type …interface…")

Mechanism: the ASSIGNMENT form's untyped nil reaches the machine as a
bare nil node (no type), which `.nilLit none` accepts; the CONVERSION
form flows through emitCallNode → emitExpr, whose generic
type-attachment (emit.go:4655 at this tip — `m["type"] = ty` in
emitExpr) stamps the target type onto the
typeless nil node — so the machine saw `.nilLit (some (.interface
…))` and the arm enumeration, written for the assignment-form kinds,
fell through to the fail-closed refusal. Interface and func ARE
nilable types (spec#Assignability); their nil is the zero value. The
frontend is unchanged — the typed nil node is a faithful wire shape;
the missing arms were the machine's. Trusted surface — flagged
[TRUST-ADJACENT]; the arms are zero-value returns identical to
`defaultValue`'s.

Scope correction (audit fix round 2026-09-01, SHOULD-FIX 6): this
entry closes the nil-CONVERSION refusal ONLY — it does not make the
three harvest tests it names comparable. Of the three, only
typeparam/issue42758.go MATCHes after the fix; issue19911.go
progresses to a strings.Index frontier refusal (FR-14); issue53619.go
carries a SECOND, independent defect — its comma-ok assertion into
INTERFACE-typed globals (`var a, b any = any(nil).(bool)`) stored an
unboxed bool, refused downstream at the first interface equality
rather than at the lowering — which is BUG-079 (now refused at the
lowering, by name). The earlier framing of this entry as resolving
the issue53619 family was wrong.

## BUG-078 — array types past the interpreter's materialization capacity killed golean with a native stack overflow instead of a refusal (process abort, not a cause-naming refusal) [TRUST-ADJACENT: wire decoder; refusal-only]

- Status: fixed (2026-09-01, gotest-fixes — decodeTy's array arm
  (GoLean/NativeToIR.lean) refuses array types longer than
  `arrayLenBudget` BY NAME, citing the budget and this entry. Budget
  1<<20 at the slice; RE-DERIVED to 1<<16 at the audit fix round
  2026-09-01 (SHOULD-FIX 2) — the 1<<20 figure had been measured on
  the default-value path, not the literal/store path the bug names;
  the constant's docstring now states each number's path)
- Pinned-by: none (the refusal surfaces at `lean-observation`; the
  row below is a FAIL-BY-DESIGN refusal pin, red forever at the
  oracle's `ok`, listed on the Cases line per the BUG-070/071/072
  precedent — check-bugs verifies EXISTENCE only for none-entries and
  counts a listed row as explained, so the row leaves untriaged-ids.
  Audit fix round 2026-09-01, RECORD 8: the slice had parked it in
  untriaged-ids with a ceiling raise 11→12 instead; reverted)
- Cases: arrays/materialization-budget/over-budget
- Discovered: 2026-09-01 ($GOROOT/test harvest,
  docs/2026-09-01_gotest-triage.md INFRA note — issue34395.go's
  `[100<<20]byte` global: exit 134, "Stack overflow detected.
  Aborting." The triage note filed it as "a very deep recursion
  program"; this entry CORRECTS that description — issue34395 is a
  `[100<<20]byte` global with a two-line main, and the overflowing
  recursion was the normalizer's over the array's elements, not the
  program's)

Diagnosis: the machine materializes array VALUES element-wise; the
normalize path (`normalizeListWith`, GoLean/GoCore/Ops.lean:863) is
non-tail-recursive over the element list AND quadratic (`#[head] ++
tail` per element). Measured, BY PATH (audit fix round 2026-09-01 —
the slice's "10^5 fast, 10^6 grinds, 10^8 aborts" were DEFAULT-VALUE
numbers, `Array.replicate`, linear: 0.03 s at 10^5, 0.06 s at 1<<20):
the LITERAL initializer `var a = [N]byte{42}` and an ELEMENT STORE
into a default array both take the quadratic normalize — 0.13 s at
10^4, 2.7 s at 5×10^4, 5.0/5.5 s at 1<<16 (literal/store), 11.4 s at
10^5, 20.5 s at 1<<17, 46 s at 2×10^5, 224 s at 4×10^5, ≈25 min
extrapolated at 1<<20 — against the gate's 30 s per-case wall. The
budget is 1<<16: >5× under the wall on the worst flat path, 500× the
largest corpus array type (128). It is a PER-TYPE FLAT bound, not a
value-size bound (nested `[1024][1024][128]byte` is admitted; default
value 1.1 s). The
clean fix (an iterative, linear normalize) is semantic-core surgery —
`normalizeListWith` sits arm-for-arm in lockstep with
`isNormalForTyFuel` and the MachineSound soundness proofs — beyond
this slice's scope; recorded here as the owed follow-up. The honest
minimal fix is a refusal at the single choke point every array type
flows through, the wire decoder (runtime-length allocations are
slices, whose values normalize by reference — probed:
`make([]byte, 100<<20)` grinds at interpreter speed but does not
abort). IDEALIZATION BOUNDARY, not fidelity: gc materializes such
arrays fine; the region past the budget is a deliberate visible
machine-refuses/gc-succeeds red, never a wrong answer, never an
abort. Owed residuals recorded (owner: TODO.md, "Owed core fixes"):
(1) the linear-normalize core fix lifts the budget need; (2) huge
`make` lengths still grind to the wall-clock/fuel budget (an honest
stop, but slow); (3) the flat per-type bound does not cap NESTED
values — one element store into an admitted `[1024][1024][128]byte`
measured 46 s (the store re-normalizes through the nesting), so an
oversized nested value can still reach the wall clock: an honest
kill, never a wrong answer, lifted by (1).

## BUG-080 — race detector U4: the sync primitives' OWN state-word accesses are unmodeled, so a plain access to a primitive in use by another goroutine (copy / overwrite) runs to a value where gc's -race build refuses

- Status: fixed (2026-09-02, the `bug080-atomic-kind` slice — [USER]-ruled
  the same day as its own S–M slice ahead of the Q-ATOMIC arc,
  `docs/2026-08-31_qrow-rulings.md` row 2; [AGENT]-executed. THE FIX:
  `GoLean/GoCore/Race.lean` `RaceAccess := AccessKind × Loc`, `AccessKind ∈
  {read, write, atomicRead, atomicWrite}`, conflict ⇔ at least one write ∧
  not both atomic (mem#model's read-write/write-write data-race
  definitions — read-like/write-like operations "at least one of which is
  non-synchronizing"; the one-sentence informal form is mem#overview;
  TSan's shadow rule); the
  per-op set gc's -race build realizes on the primitive's own words —
  `syncEntryKinds` (before the op's hook) / `syncReleaseTailKinds` (Unlock's
  state Add after `race.Release`) — derived PRIMITIVE BY PRIMITIVE from
  go1.26.5's sources and recorded by `raceUpdate`'s sync arm (Multi.lean)
  at the sync cell's path, in the DATA shadow: Mutex Lock/Unlock atomic
  writes; RWMutex ops ONE PLAIN READ (`race.Read(&rw.w)`; the counters run
  under `race.Disable`); the WaitGroup `wg.sema` misuse pair (the former
  `wgSemaAccess` private-shadow carve-out, retired — same pair, same
  check, now overlapping a copy/overwrite of the enclosing struct); Once's
  atomic read (a Do observing completion) / atomic writes (the slow path,
  the completion Store + Unlock). THE TWO RULED CHECKS: (i) one `syncData`
  cell vs `locPrefix` — the access sits at the primitive's own PATH, so
  sibling fields and other primitives in the same struct are disjoint
  (green guards born PASS: `race/free-sync/{mutex-siblings,
  disjoint-prims}` + probe controls; the wgSema pair composes by
  RETIREMENT, not double-recording); (ii) per-primitive instrumentation —
  the 28-subject probe family `probes/u4kind` (both directions per
  primitive: copy and overwrite, plain access in main and in the child)
  went 8 HOLE + 7 possible-HOLE + 13 agree-DRF (the tracked-source PRE
  matrix on main's 0f3c05ff binary, re-run at audit G2 F4 — the slice's
  first pre run read 7/7/14 on a first-cut source whose
  `wg-copy-vs-first-wait` had its roles swapped; evidence README) → 0
  HOLE, 26 agree, 2 possible-HOLE (residual (b) below); the in-scope
  corpus matrix's HOLE
  cell went 2 → 0. RESIDUALS, recorded in Race.lean's sync-words section
  and flagged for the audit: (a) [AGENT] the go_mem-racy-but-TSan-
  INVISIBLE class, stated precisely (audit G2 F10 — the first statement
  over-counted): a plain access beside a WRITE-LIKE op gc runs under
  `race.Disable` — `RUnlock`, RWMutex `Unlock` (mem#model: unlock is
  write-like), WaitGroup `Add`/`Done` (the state RMW) — or a plain
  OVERWRITE beside a `Wait` at counter 0. NOT in the class: a plain COPY
  beside RWMutex `RLock`/`Lock` — lock is read-like, a copy is read-like,
  no write-like operand, no race by mem#model; `rw-copy-vs-{rlock,lock}`
  agree-DRF is the CORRECT verdict (not a bug to fix). At the slice the
  machine followed the -race oracle (register #13) and RAN the class
  (probes `wg-copy-vs-add-from-0`, `wg-copy-vs-done`,
  `wg-overwrite-vs-done`, `wg-overwrite-vs-wait-at-0`: agree-DRF; a copy
  beside RUnlock/Unlock unprobed) — an [AGENT] choice inside a brief
  that said "no new over-refusal rows"; POSED to the [USER] as
  Q-U4RESIDUAL, `docs/2026-08-31_qrow-rulings.md` row 9. **CLOSED
  2026-09-02 — RULED [USER] option (A), the go_mem register wins
  (quotes relayed via the [AGENT] coordinator, recorded in the ruling
  sheet's appendix), IMPLEMENTED on lane `q-u4-gomem`:** the tables
  record TSan's realized set ∪ go_mem's operation kind, each at its gc
  word (`syncWord`), so the class REFUSES; the over-refusal rows are
  classified BY DESIGN and pinned born-FAIL at `race/gomem-only/*` on
  **BUG-084**'s Cases line (that entry is the record of the designed
  divergence); the unprobed shapes are probed (`probes/u4gomem`). (b) an
  overwrite that unlocks a held Mutex/RWMutex and is FOLLOWED by another
  goroutine's Unlock/RUnlock: gc's `race.Read`/Add precedes its misuse
  check so TSan reports the race and THEN the fatal fires; the machine's
  fatal fires in the apply step and the detector — which folds only
  successful steps — never sees the entry access: machine `fatal` where
  gc is race+fatal — both abort; the machine's is an asserted program
  outcome (`GoError.fatal`, Value.lean:207-217), gc's is the race report
  then the same abort — outcome CLASS differs (probes
  `rw-overwrite-vs-{runlock,unlock}`, possible-HOLE by the runner's
  definition, diagnosed; the owed fix's scope and call-site list are
  AUTHORITATIVE at TODO.md's BUG-080 follow-up item — S–M,
  trust-surface). Evidence: `docs/evidence/2026-09-02_detector-soundness/
  probes-u4kind-{pre,post}.*`, `corpus-bug080.*`.)
- Pinned-by: differential
- Cases: race/negative-sync/wg-overwrite, race/negative-sync/mutex-copy, race/negative-sync/rw-overwrite, race/negative-sync/once-copy
- Discovered: 2026-09-02 (the Tier-4 detector-soundness differential,
  `scripts/detector-soundness`, probe family U4 —
  `docs/evidence/2026-09-02_detector-soundness/probes/u4/`; report
  `docs/2026-09-02_detector-soundness.md` §3). The class was RECORDED
  as under-approximation U4 in `GoLean/GoCore/Race.lean`'s inventory
  since spec-parity slice 2 ("misuse-only") but never pinned; this
  entry pins it and classifies it honestly as the third cell of the
  soundness matrix (gc `-race` RED, machine DRF): a program that is
  racy by mem#restrictions is given SC value semantics.
- What: gc's `-race` build performs real instrumented accesses on the
  primitive's own words — `Mutex.Lock` is an atomic CAS on `m.state`
  (TSan: "Write … sync/atomic.CompareAndSwapInt32", race_amd64.s),
  `WaitGroup.Add` reads its state word (`runtime.raceread`),
  `RWMutex` ops `race.Read(&rw.w)`, `Once.Do` likewise — so a PLAIN
  read (a struct copy) or write (a whole-struct overwrite) of a
  primitive another goroutine is operating on is a data race
  (mem#restrictions: a non-atomic access beside an atomic one), TSan-
  red 10/10 at GOMAXPROCS 1 and 8 on the pinned toolchain. The machine
  records NO access for a sync op (the sync cell's `syncCell`/
  `syncData` traffic is classified SYNCHRONIZATION in the footprint
  inventory), so the copy/overwrite's plain access has nothing to
  conflict with: the run completes (copy carries state gc-faithfully,
  sync design §3; an overwrite of a held mutex makes the later Unlock
  a fatal "unlock of unlocked mutex" member) and the racy lane's
  every-path-refuses claim FAILS on the pinned rows. Scope: MISUSE
  ONLY (vet's copylocks flags every shape; no race-free program is
  affected) — but under the DRF-SC doctrine (register #4) a racy
  program must refuse, so this is a soundness-direction gap, narrow
  and now pinned.
- Probe evidence (10/10 TSan-red each, machine DRF or uncertified by
  fatal members): `probe/u4/{struct-overwrite-vs-lock,
  wg-overwrite-vs-add, rw-overwrite-vs-rlock, once-overwrite-vs-do,
  struct-copy-vs-lock}`; the control `probe/u4/disjoint-field-vs-lock`
  (a sibling-field write beside the lock) is agree-DRF, so the class
  is exactly the primitive's own words.
- Fix shape: NOT a missing footprint-table entry. Recording sync ops as
  plain WRITES on the primitive's cell would make two legal contending
  `Lock`s conflict (atomic-vs-atomic is not a race); what gc realizes
  is a third access KIND — atomic — that conflicts with plain accesses
  only (`RaceAccess := Kind × Loc`; atomic↔atomic non-conflicting,
  atomic↔plain conflicting; recorded at the sync cell's path from
  `raceUpdate`'s sync arm). SCHEDULED [USER] 2026-09-02 (Q-row ruling
  sheet row 2, ruled with the A′ ratification — "I agree with this
  approach"): the fix lands as its OWN S–M slice, sequenced BEFORE
  the atomics arc rather than riding it — TODO.md "BUG-080 detector
  atomic-access-kind slice"; the two costs named below are that
  slice's design checks. The sequencing paragraph that follows is the
  SUPERSEDED [AGENT] judgment (was: rides the arc's detector wave),
  kept for the record. SEQUENCING ([AGENT] judgment, audit fix
  round 2026-09-02 S4 — NOT a forced dependency): that kind is
  separable from the sync/atomic lowering and could land alone (S–M);
  it is sequenced to ride the atomics arc's detector wave
  (`docs/2026-09-01_qatomic-owner-proposal.md` §4; Q-ATOMIC row 2 of
  the ruling sheet, OPEN) for two stated reasons: (i) each primitive
  is ONE `syncData` cell, so the atomic access at the cell's path
  must be checked against the `locPrefix` over-refusal (a sibling-
  field plain access beside the lock — the `disjoint-field-vs-lock`
  control — must stay green) and reconciled with the `wgSemaAccess`
  carve-out, which already records one PLAIN pair on that cell;
  (ii) gc's per-primitive instrumentation differs (WaitGroup under
  `race.Disable` + the `wg.sema` pair; Mutex's state CAS as an
  atomic), so the per-op recorded set (Lock/Unlock/RLock/RUnlock/
  Add/Done/Wait/Do — TSan's realized set, per register #13) must be
  derived primitive by primitive, which the atomics arc's `-race`
  alignment work already does. Once the kind lands these rows flip
  without further design. Recorded against decision 1's deferred
  investment as the mandate directs; until then the rows stay red and
  Race.lean's U4 text points here.

## BUG-079 — comma-ok type assertion ASSIGNED into interface-typed targets stored the component RAW: the package-level `var a, b any = any(nil).(bool)` and local `a, b = x.(T)` forms bypassed the multi-value boxing guard (refused downstream at interface equality — the wrong site)

- Status: fixed (2026-09-01, gotest-fixes audit fix round — emitAssign's
  comma-ok type-assertion path (tools/nativefrontend/emit.go) refuses,
  for `=` (never `:=`, whose targets take the component types via
  Defs), any INTERFACE-typed target whose component — the asserted T
  for the value slot, bool for the ok slot — is non-interface, with the
  declaration forms' exact named cause: "implicit interface conversion
  in multi-value assignment (interfaces campaign, deferred)". Refusal
  moved to the lowering; no boxing is implemented — FR-7 owns the
  feature)
- Pinned-by: none (the refusals surface at `frontend-export`, a
  coverage stage; the rows below are FAIL-by-design refusal pins of
  the FR-7 family, listed so the fix's baseline rows ride a Cases:
  line — the BUG-070/071/072 precedent. Oracle truth `ok` in both
  expected columns; gc runs both)
- Cases: interfaces/comma-ok-into-interface/global-form, interfaces/comma-ok-into-interface/local-assign-form
- Discovered: 2026-09-01 (audit of the gotest-fixes slice, SHOULD-FIX
  6: $GOROOT/test issue53619.go's post-BUG-077 residual — the slice's
  triage re-run reported it as "an honest raw-vs-boxed bool
  interface-equality refusal", which is a refusal at the WRONG site)

Mechanism: spec#Type_assertions writes the comma-ok form as `var v,
ok interface{} = x.(T)` — an implicit multi-value interface
conversion the tuple-producing type-assert statement cannot express
(the machine stores the component RAW into the interface cell). The
DECLARATION forms (`var a, b any = x.(bool)` in a function body)
already refused at emitDeclStmt with the BUG-057 reroute's guard; the
ASSIGNMENT forms did not: emitAssign's dedicated comma-ok path
(`v, ok = x.(T)`) never asked whether a target was interface-typed,
and the package-level declaration reaches exactly that path — the
init lowering fabricates `a, b = any(nil).(bool)` as an AssignStmt so
emitAssign's machinery applies unchanged. Measured red-first (HEAD
frontend, tip golean): both rows lowered and stopped downstream with
`unsupported: interface equality for GoValue.bool false and
GoValue.interface (Ty.bool) (GoValue.bool false)` — fail-closed, so
no fidelity lie, but the cause was named at the wrong site and a
program that never compares the cell would have run on an unboxed
interface value. With the guard both rows refuse at frontend-export
by name. Frontend only, fail-closed-strengthening.


## BUG-081 — `make` past gc's maximum allocatable size ran on (materializing its backing toward the wall clock) where gc panics deterministically `makeslice: len/cap out of range` / `makechan: size out of range`: the allocation-limit panic class was unmodeled (observed ∉ modeled) [TRUST-ADJACENT: GoCore make/append arms]

- Status: fixed (2026-09-02, t5-maxalloc — fidelity decision 5(b)
  [USER] 2026-08-31 "the deterministic maxAlloc panic class modeled",
  landed as PINNED latitude R16: `maxAllocBytes` 2^48, `chanHeaderBytes`
  112, the gc linux/amd64 layout `tySizeAlign` (GoLean/GoCore/
  Ops.lean, R16 docstrings); gc's check ORDER and message texts at the
  `makeSlice` / `makeChan` arms of `applyStmtOpCore` and the
  `appendSlice` spill path of `applyStmtOp` (GoLean/GoCore/Machine.lean),
  each BEFORE the backing is materialized; `StmtOp.makeChan` now carries
  the element type the threshold needs)
- Pinned-by: differential
- Cases: builtins/make-maxalloc/slice-len-over-byte, builtins/make-maxalloc/slice-len-over-const, builtins/make-maxalloc/slice-len-over-int64, builtins/make-maxalloc/slice-len-over-padded-struct, builtins/make-maxalloc/slice-cap-over-byte, builtins/make-maxalloc/slice-len-and-cap-over, builtins/make-maxalloc/chan-size-over-byte, builtins/make-maxalloc/chan-size-header-boundary, builtins/make-maxalloc/chan-size-over-int64, builtins/make-maxalloc/chan-zero-size-elem-huge, builtins/make-maxalloc/recover-slice-len-over, builtins/make-maxalloc/recover-chan-size-over
- Discovered: 2026-09-02 (the t5-maxalloc gc probe matrix,
  docs/evidence/2026-09-02_t5-maxalloc-probes/ — filed with the probe as
  witness. The CLASS was on the books unpinned since 2026-08-14:
  doctrine register #7 recorded "allocation never fails" as a standing
  idealization, and fidelity decision 5 split it into behavior 1 (true
  OOM, still under the rider) and behavior 2 (this entry))

Mechanism: the spec sanctions a run-time panic for a negative or
len>cap `make` and says nothing about a size limit; gc's runtime adds
one — `maxAlloc = 1<<48` on amd64 (malloc.go:220) — and refuses ONE
request whose byte size exceeds it with a recoverable `runtime.Error`
(`makeslice`, slice.go:102–115: cap's bytes over the limit, or len<0,
or len>cap, blaming LEN when the len alone is bad — issue 4085;
`makechan`, chan.go:86–89: buffer bytes over `maxAlloc - hchanSize`,
hchanSize = 112; `growslice`, slice.go:191–252: the grown cap's bytes,
or `int` overflow of the new length). The machine had only the
negative and len>cap arms: `make([]byte, 1<<48+1)` passed them and
went to `buildDefaultArrayValue`, i.e. an eager 2^48-element backing —
a grind to the 30 s wall (an honest kill, never a wrong value, but
observed ∉ modeled: gc's panic is a behavior no machine stream
produced). Probed both sides of every boundary (go1.26.5: 2^48+1 bytes
panics, exactly 2^48 attempts the allocation and dies of true OOM;
chan 2^48-111 panics, 2^48-112 allocates; int64 and padded-struct
elements scale the threshold by gc's LAYOUT size — 16 bytes for
`struct{int64; byte}`, padding included). The fix reifies the limit as
a declared machine parameter (R1's mold: pinned to the oracle host,
envelope and 32-bit interaction recorded on R16) with a gc-layout size
function transcribed from go/types `gcsizes.go`, failing closed on
unsupported types. What is deliberately NOT modeled, and why, is on
R16: behavior 1 (allocation failure of a request that passes the
check — the D-001 residual, under the register #7 rider), and the
append band where gc's grown-cap check raises a recoverable
`runtime.Error` but the machine's newLen-based one allocates — a
deterministic-panic residual of 5(b) itself, NOT an allocation failure
and NOT a rider case (the newLen decision is forced by
`applyStmtOp_appendSlice_congr`, which states spill outcome class is
choice-independent; machine-panics ⊊ gc-panics there). Corpus rows are
all just-over (gc panics); the just-under controls are fatal OOM in
gc and eager-materialization grinds in the machine (BUG-078 residual
(2)) — the one feasible control is `make(chan struct{}, 1<<62)`, whose
zero-size element never trips the limit and whose machine buffer is a
capacity NUMBER. The `append` class has no corpus witness (it needs an
existing >2^47-byte slice or `unsafe.Slice`, which the frontend
refuses); the gc probe append-growth-over-unsafe is its evidence.

## BUG-082 — the `make(map[K]V, hint)` HINT is not lowered: the native frontend emits `make-map` without it, so the hint expression's evaluation (its side effects) is dropped — and the machine arm's `makemap: size out of range` panic on a negative hint (a string gc no longer realizes) was dead code behind it

- Status: fixed (2026-09-02, the `bug082-maphint` lane — [USER] Mike,
  2026-09-02, relayed by the [AGENT] coordinator, NOT firsthand: «Issue
  (2) sounds like a clear win, it's a bug fix right? do it», issue (2)
  being the coordinator's "BUG-082 frontend fix: authorizes moving the
  twin-wire pin"; [AGENT]-executed inside that mandate. THE FIX
  [TRUST-ADJACENT: frontend lowering + decoder key list]:
  `tools/nativefrontend/emit.go` `emitMake`'s `*types.Map` arm visits
  `c.Args[1]` and emits it as the `make-map` node's `hint` field —
  present EXACTLY when the source has a second argument, absent
  otherwise; `GoLean/NativeToIR.lean`'s strict key list for `make-map`
  gains `hint` (the only widening; any other key still refuses) and the
  decoder passes it as `Stmt.makeMap`'s `initialSpace`. NO GoCore
  change: the `makeMap` arm of `applyStmtOpCore` already evaluated an
  optional hint operand (type, order) and ignored its value. WHERE THE
  HINT IS EVALUATED: its calls are hoisted by the frontend into `$c`
  temps in operand order BEFORE the `make-map` statement (the same
  path every effectful operand takes — spec#Order_of_evaluation), and
  the residual expression is evaluated by the machine arm as the
  operand after the target address (a call-free panicking hint, e.g.
  an out-of-range index, panics THERE, before the map exists). Twin-
  wire frontend pin re-pinned `b4ef84e433c1…` → `eef32142627a…`
  ([USER]-authorized as above; the delta is exactly the two
  raftsubject `make(map…, n)` sites gaining `hint`, structural diff in
  the evidence dir); deviation pin unchanged. Evidence:
  docs/evidence/2026-09-02_bug082-maphint/ — gc vs machine on the
  side-effect probe family (gc 31 / 50 / -677 / 1 / 12341 = fixed
  machine; the PRE-FIX frontend through the fixed decoder gives 11 /
  10 / -877 / 11 / 1341, the red-first), and the frontend's go/types
  refusal of a non-integer / non-representable constant hint, pinned
  by the negative rows `maps/make-map-{float,string,negative-const,
  overflow-const}-hint`.)
- Pinned-by: differential
- Cases: builtins/make-maxalloc/map-hint-eval-order, builtins/make-maxalloc/map-hint-over, builtins/make-maxalloc/map-hint-negative, builtins/make-map-hint-eval/panic-map-never-created, builtins/make-map-hint-eval/panic-uncaught, builtins/make-map-hint-eval/index-panic-map-never-created, builtins/make-map-hint-eval/index-panic-uncaught, builtins/make-map-hint-eval/evaluated-once, builtins/make-map-hint-eval/negative-from-call, builtins/make-map-hint-eval/zero, builtins/make-map-hint-eval/named-int-type, builtins/make-map-hint-eval/uint8-var, builtins/make-map-hint-eval/untyped-const, builtins/make-map-hint-eval/typed-const, builtins/make-map-hint-eval/eval-order-with-neighbors, builtins/make-map-hint-eval/eval-order-in-expression
- Discovered: 2026-09-02 (t5-maxalloc probe matrix, probes map-hint-neg
  / map-hint-over: gc runs `make(map[int]int, -1)` and `make(map[int]
  int, 1<<48+1)` — NO PANIC, len 1 after one insert — where the
  machine's `makeMap` arm panicked on a negative hint. Filing the wrong
  answer, the red-first check against the pre-slice golean binary
  showed the rows PASS on BOTH binaries: the panic never fired because
  the hint never reaches the machine. `tools/nativefrontend/emit.go`'s
  `*types.Map` make arm emits `{"stmt":"make-map", target, keyType,
  valueType}` — `c.Args[1]` is never visited — and NativeToIR's
  `"make-map"` decoder passes `none` for the hint. The corpus had
  `builtins/make-map-hint` with a constant hint 8, which cannot see
  either half.)

Two halves, one site. (1) FIDELITY, FIXED the same day on the
`bug082-maphint` lane (Status above): spec §Making slices, maps
and channels lists the hint among the ordinary operands of a `make`
call (§Order_of_evaluation: operands evaluated left to right), and gc
evaluates it — `make(map[int]int, bump(&n))` bumps `n`; the machine
never runs `bump`. Observed side effect ∉ modeled: the red-first row
`map-hint-eval-order` (gc 31, machine 11). The FIX is a frontend +
decoder change — emit the hint as an optional `"hint"` field, decode
it into `Stmt.makeMap`'s `initialSpace` — which MOVES the twin-wire
frontend pin (`scripts/check-frontend-pins`: `raftsubject` uses
`make(map[uint64]struct{}, len(m))` and `make(map[int]struct{}, n)`),
so it is a deliberate pin re-pin with its reason and was NOT done
inside the t5-maxalloc lane ([AGENT] fail-closed call: frontend-pin
moves are not within a GoCore slice's mandate; the row stays red on
this line until the fix lands). (2) The machine arm, fixed in the
same slice as a by-product: it evaluates the hint operand (type,
order) and IGNORES its value, as gc's runtime/map.go:60–67 clamps a
negative or over-`maxAlloc` hint to 0 — the old negative-hint panic
was an R9 violation in waiting (a text the pinned oracle never
produces), dead only because of (1). The two gc-truth rows
`map-hint-over` / `map-hint-negative` (PASS on both binaries) pin that
gc does not panic there; they did not exercise the machine arm until
(1) landed (they do now, and sit on this Cases line for that reason).

AUDIT FIX ROUND M1 (2026-09-02): lowering the hint puts it on the
`make` hoist, which has no A6 unordered-panic guard — so the fix joins
BUG-032's class with two NEW instances (`iv.(int) + len(make(map[int]
int, t[k]))`, `… boom()`: gc realizes the interface-conversion panic,
the machine the hint's) while correcting five sibling shapes main got
wrong by dropping the hint. Recorded on BUG-032 (M1 amendment) and
pinned red-by-design on BUG-083's Cases line
(builtins/len-vs-call-order/hint-panicky-between); the table is in
this entry's evidence dir, §M1.

## BUG-083 — the `make` hoist has no unordered-panic guard: a panicky size/hint operand is evaluated ahead of a spec-unordered panicky operand to its left (BUG-032's class; the open-instance ledger for the make shapes)

- Ruling 2026-09-05 ([USER], relayed via the [AGENT] coordinator; no status change): E13's four-way treatment RULED (b) — the `make` refusals below retire into a membership shape admitting both orders where the spec leaves them unsequenced (the E13 tension this entry records is resolved toward latitude); `docs/2026-08-11_latitude-inventory.md` E13, lane `e13-b`.
- Status: fixed (2026-09-04, lane `fr27-fr28`, FR-28 — fixed AS A NAMED
  REFUSAL, not as gc's point: the A6 guard (`hoistReordersPanic` =
  `residualPanicFreeOperand` × `sweepPanickyInlineBefore`, emit.go) is
  wired into `emitMake` over every size/hint operand, so the shapes
  below refuse at frontend-export naming the shape (`make of a
  potentially-panicking size/hint operand with a potentially-panicking
  operand to its left in the same statement …`) instead of realizing
  the hint's panic ahead of the left operand's. WHAT IS CLOSED, exactly:
  every make size/hint operand whose residual can panic, beside panicky
  inline material to its left, refuses — the filed shapes are refusals
  by name; the full-statement linearization BUG-032 records as unbuilt
  is still the only fix that would realize gc's point. AUDIT FIX ROUND
  F1 (2026-09-05): the first cut's map-read refinement (i) tested the key
  TYPE with `types.IsInterface`, admitting key types that are statically
  comparable but CONTAIN an interface (`struct{v any}`, `[1]any`) — such
  a key is hashed at run time and panics on an uncomparable dynamic
  value (`hash of unhashable type: []int`, the mechanism of
  `maps/array-key-interface-elem-unhashable`) — so between 6441bd37 and
  the fix round the slice was itself WRONG on `iv.(int) + len(make(map,
  nm[k]))` with such a key (gc: interface conversion; machine: the hash
  panic) and had REGRESSED the A6 refusal on the len path (`iv.(int) +
  len(nm[k]) + wit(5)`, refused on main, lowered wrong). Closed by
  `containsInterface` (an interface anywhere in the key type — struct
  fields recursively, array elements, named through underlying, a type
  parameter until substituted) at every site: `hashSafeMapRead`
  (panicFreeOperand / nilDerefOnlyResidual / the sweep census) and the
  sweep's `==`/`!=` arm, which had the same top-level-only test. Rows
  `make-hint-struct-any-key`, `make-hint-array-any-key`,
  `len-struct-any-key-left-assert` red BY NAME; `make-hint-generic-
  {any,int}-key` pin the `K comparable` twin (`any` refuses after
  applySubst, `int` lowers). The M1 table re-measured at the fix
  (evidence dir `docs/evidence/2026-09-04_fr27-fr28/m1-table.tsv`;
  counts derivation-anchored to the TSV, audit fix round F2): SIX
  probes REFUSE — the three assert-left shapes that were WRONG
  (`iv.(int) + len(make(map, t[k]))`, `… make([]int, t[k])`, `…
  cap(make(chan int, t[k]))`) and the THREE index/division/nil-deref-
  left shapes (`s[i] + …`, `1/z + …`, `*p + …`) that MATCHED gc — the
  trade this entry priced ("would newly refuse the pre-existing
  slice/chan shapes"), taken under the relayed posture «break rather
  than preserve incorrect behaviour»; SEVEN lower. On those three traded
  shapes gc's point IS the hoist's point (gc hoists the make too, so the
  hint's panic fires first on both sides) — the refusal there is
  defensible not because the machine was wrong but because the guard is
  conservative-syntactic (it does not encode gc's compiler-internal rule
  that ONLY an interface-conversion panic on the left is ordered ahead of
  a hoisted make), and because latitude E13 takes NO pin on the indexing
  axis: an agreement there is not spec-required, so freezing it would
  pin latitude, and refusing it leaves nothing wrong on the record (F6).
  Two refinements narrow the over-refusal where the argument is exact:
  (i) a MAP read whose key type contains no interface is panic-free
  (`gAssertVsMapIndexHint`, `iv.(int) + len(make(map, nm[1]))`, stays
  green — spec#Index_expressions gives the zero value on a missing key or
  nil map); (ii) when BOTH the hoisted operand and every panicky inline
  node to its left can panic ONLY by nil dereference, the two candidate
  panics are one runtime error and nothing effectful lies between them,
  so the hoist is order-transparent and taken (`make-nil-only-*`, all
  four nil-ness combinations green; the same arm lowers the len/cap
  lexer idiom, BUG-032's amendment). `gAssertVsHintCall` (`iv.(int) +
  len(make(map, boom()))`) and `gAssertVsPlainCall` are NOT refused and
  not pinned: the hint is a real CALL whose residual is its temp, so
  this is the frontend-ANF call-first family the latitude inventory
  census's at E13 (calls run ahead of a left assertion; both members
  conforming; NO PIN by that entry's rule) — this entry's original
  instance list put `… boom()` beside the hint shapes, but its mechanism
  is E13's, not the hoist guard's, exactly as BUG-032's F23 retirement
  treats `len(f())`. TENSION RECORDED [AGENT], for the audit: E13 reads
  the assert-vs-sibling-call axis as latitude with no pin, and `make` is
  a call ("called like any other function"), so under E13's reading the
  assert-left make-hint shapes were latitude too — this entry (ratified
  by the coordinator 2026-09-02) filed them as a wrong answer, and the
  FR-28 brief asked for a named refusal; the refusal is honest under
  either reading (a red, never a guessed order) but it is STRICTER than
  E13's treatment of `min`/`max`/user calls, which still run first.
  Rows: `hint-panicky-between` flips stage differential → frontend-
  export (still FAIL by design); `make-slice-panicky-between`,
  `make-chan-cap-panicky-between` (the pre-existing siblings),
  `make-index-left` (the priced trade) and `make-inner-len` (the
  `residualPanicFreeOperand` hole for an INLINE builtin's operand —
  `len(b[j])` as a size is not a hoisted temp — closed in the same
  slice) born FAIL/frontend-export by design; `make-hint-panic-free`,
  `make-hint-call`, `make-hint-map-read` are the guard's green controls.
  Pinned-by moves to none with `Expect: FAIL` (the BUG-070/078/084
  precedent: red-by-design refusal pins on a fixed entry — check-bugs
  (3) forbids a FAIL row on a fixed differential entry).)
  **REFUSAL RETIRED INTO LATITUDE (2026-09-05, lane `e13-b` — E13
  option (b), RULED [USER] Mike 2026-09-05, relayed by the [AGENT]
  coordinator: «we should do what the standard supports, and avoid
  over-refusal if we can. That's what (b) means right?»; design
  `docs/2026-09-05_e13-b-design.md`).** STATUS CHANGE with its reason:
  the shapes this entry filed were never a wrong answer in the sense of
  observed-∉-modeled-by-right — gc's realization (the assertion's panic
  first) and the machine's (the hint's) are BOTH conforming members of
  a spec-UNSEQUENCED pair (the TENSION paragraph above said so); the
  A6 guard that closed the entry AS A REFUSAL was standing in for
  latitude, and the ruling retires it. The `make` guard and the whole
  `hoistReordersPanic` predicate family are DELETED (emit.go); the
  frontend emits an `unseq-probe` at the left operand's lexical
  position and the machine realizes both orders (`ChoiceSite.unseqPanic`:
  DEFER = the hint first, RAISE = the assertion first). Every row on
  the Cases line below LOWERS and is a `lane=membership` row with two
  certified members, gc's draw inside the set (its member is RAISE on
  the assert-left rows — gc evaluates type assertions early — and DEFER
  on `make-index-left`); `hint-panicky-between` flips FAIL/frontend-
  export → PASS/membership with its siblings (a refusal became an
  answer, not a pin). `Expect: FAIL` is dropped and Pinned-by returns to
  differential: check-bugs (3) now demands these rows PASS, which they
  do. The full-statement linearization this entry named as "the only
  fix that would realize gc's point" is NOT what landed — gc's point is
  one member, not the target; the design note §3 has the argument.
- Pinned-by: differential
- Cases: builtins/len-vs-call-order/hint-panicky-between, builtins/len-vs-call-order/make-slice-panicky-between, builtins/len-vs-call-order/make-chan-cap-panicky-between, builtins/len-vs-call-order/make-index-left, builtins/len-vs-call-order/make-inner-len, builtins/len-vs-call-order/make-hint-struct-any-key, builtins/len-vs-call-order/make-hint-array-any-key, builtins/len-vs-call-order/make-hint-generic-any-key, builtins/len-vs-call-order/len-struct-any-key-left-assert, builtins/e13-sibling-panic-order/tgt-assert-vs-len-hoist, builtins/e13-sibling-panic-order/tgt-assert-vs-make, builtins/e13-sibling-panic-order/compound-assert-vs-len, builtins/e13-sibling-panic-order/map-key-assert-vs-len, builtins/e13-sibling-panic-order/recover-assert-vs-len, builtins/e13-sibling-panic-order/bytes-conv-left-len-hoist

RE-AUDIT FIX ROUND (e13-b, 2026-09-05, [AGENT]): the six ids after
`len-struct-any-key-left-assert` were BUG-102's designed reds at the
lane's first fix round (the NARROWED A6 guard refused a len/cap/make
hoist beside an UNPROBED assignment-target / recover() / allocating-
conversion operand). The re-audit (R1'-1, R1'-4) found the target
operands to be spec#Assignment_statements PHASE-1 material — siblings of the RHS's
calls, unsequenced — so the refusal stood in for latitude exactly as
this entry's make rows did: the frontend now probes them (and the
hoisted `recover()`'s residual, and a HOISTED allocating conversion),
the rows lower as two-member membership sets with gc's EARLY assertion
in the set (`recover-assert-vs-len` is a singleton: `recover().(int)`
succeeds on `panic(3)`, so nothing panics early), and they move here —
the same retirement-into-latitude this entry records, with the same
reason. Their history stays on BUG-102.
- E13-b AUDIT FIX ROUND AMENDMENT (2026-09-05, [AGENT]; audit finding
  R1): the retirement into E13 holds for PROBED left material only. The
  first cut deleted the make guard whole, so `x[iv.(int)] = len(make(
  []int, t[k]))` — a TARGET operand the envelope never probes — lowered
  as the hint's index panic where gc raises the interface conversion: the
  refusal this entry "fixed as" had become a silent wrong answer. The
  NARROWED guard is back in `emitMake` over every size/hint operand
  (BUG-032's fix-round amendment has the mechanism and the subclass list:
  target / address-of / recover() / allocating-conversion material); its
  row `builtins/e13-sibling-panic-order/tgt-assert-vs-make` is red by
  design on BUG-102's Cases line (the designed-red entry). `Pinned-by:
  differential` and the dropped `Expect: FAIL` stand here: the nine rows
  above remain PASS/membership.
- Discovered: 2026-09-02 (bug082-maphint pre-merge audit, M1; the
  auditor's probes `.tmp/audit-bug082/p4`, `p5`, reproduced in
  docs/evidence/2026-09-02_bug082-maphint/README.md §M1)

The mechanism and its history are BUG-032's (M1 amendment there):
`emitMake` hoists `make(...)` unconditionally, and since BUG-082's fix
the map hint hoists with the slice len/cap and chan cap it always
carried — none of them behind the A6 guard `len`/`cap` have. On
`iv.(int) + len(make(map[int]int, t[k]))` (k out of range) gc realizes
`interface conversion: interface {} is string, not int` and the machine
`runtime error: index out of range [5] with length 2`; on `… boom()`
gc the conversion panic, the machine `boom-call`. Both spec-legal
(spec#Order_of_evaluation orders only calls, receives and binary
logical operations), gc's point compiler-internal, but observed ∉
modeled: a wrong answer in a documented class, hence an OPEN
differential pin rather than a refusal. The same hole is pre-existing
for `make([]T, t[k])`, `make(chan T, t[k])` and plain `iv.(int) +
boom()` (table, evidence §M1); the shapes where a left INDEX /
DIVISION / NIL-DEREF panic meets a hint panic MATCH gc (gc hoists the
make too). This entry exists because check-bugs (3) cannot hold a FAIL
row on the fixed BUG-032; it closes when either the full-statement
linearization BUG-032 records as unbuilt lands, or the A6 guard is
extended to `emitMake` (which would REFUSE — and newly refuse the
pre-existing slice/chan shapes; a separate arc, [AGENT] not done in
the records-only fix round).

## BUG-084 — DESIGNED divergence from the `-race` oracle: a plain access to a sync primitive beside an op gc runs under `race.Disable` (RWMutex `RUnlock`/`Unlock`, WaitGroup `Add`/`Done`, an overwrite beside `Wait` at 0) is REFUSED here and RUN by gc's `-race` build — go_mem calls it a data race, TSan cannot see it [TRUST-ADJACENT: Race.lean tables; refusal-only]

- Status: fixed (2026-09-02, the `q-u4-gomem` lane — this is NOT a
  machine defect but the RECORD of a ruled divergence, filed in the
  bug index because that is where a red row's explanation must live for
  `scripts/check-bugs.sh` (the BUG-070/078 precedent: a Pinned-by:none
  entry carries its FAIL-by-design rows on its Cases line, so they are
  explained, never untriaged, and can never be laundered into a pass by
  a re-pin). "fixed" here means: the ruling is IMPLEMENTED and the rows
  are red exactly as designed; they are not expected to flip PASS, and
  a PASS on any of them would mean the detector stopped refusing a
  go_mem-racy shape — the guard direction is stated in prose because
  check-bugs verifies existence only for none-entries.)
- Pinned-by: none (the rows FAIL at `lean-observation` — gc's `ok`
  value vs the machine's `race` refusal — by DESIGN; a differential pin
  would assert the wrong direction. The re-pin guard still reads this
  Cases line: any of these ids flipping PASS→non-PASS or appearing as a
  born-FAIL row is explained here.)
- Expect: FAIL
- Cases: race/gomem-only/rw-copy-vs-runlock, race/gomem-only/rw-copy-vs-unlock, race/gomem-only/wg-copy-vs-add-from-0, race/gomem-only/wg-copy-vs-done, race/gomem-only/wg-overwrite-vs-wait-at-0
- Discovered: 2026-09-02 as BUG-080's residual (a) — the go_mem-racy-
  but-TSan-invisible class the BUG-080 slice chose to RUN (aligned with
  the oracle, [AGENT], inside a brief that said "no new over-refusal
  rows"); posed to the [USER] as Q-U4RESIDUAL
  (`docs/2026-08-31_qrow-rulings.md` row 9) by the bug080-atomic-kind
  audit fix round (G2 F10), which also corrected the class's statement
  (a copy beside `RLock`/`Lock` is two read-likes — NOT in the class).
- The ruling ([USER] 2026-09-02, option (A) — the quotes were relayed
  to the recording worker by the [AGENT] coordinator; the verbatim
  record and provenance chain are in the ruling sheet's appendix, "The
  row-9 ruling record"): follow go_mem exactly. The register of record
  for what a race IS is mem#model's read-like/write-like definition —
  "A read-write data race on memory location x consists of a read-like
  memory operation r on x and a write-like memory operation w on x, at
  least one of which is non-synchronizing, which are unordered by
  happens before" (and the write-write twin) — and mem#model names
  mutex unlock write-like and mutex lock read-like (mem#locks: both
  `sync.Mutex` and `sync.RWMutex`); WaitGroup/Once are deferred to
  their package docs by mem#more (`Done` "synchronizes before" the
  `Wait` it unblocks, the release/acquire shape → Add/Done write-like,
  Wait read-like). A plain copy of a WaitGroup beside another
  goroutine's `Done` is therefore a data race whether or not gc's
  `-race` build, which runs the state RMW under `race.Disable`,
  instruments it. mem#restrictions licenses the refusal ("Any
  implementation can, upon detecting a data race, report the race and
  halt execution of the program"). RATIONALE, as ruled: the machine is
  the substrate for a verification tool; refusal-freedom is the proof
  obligation (a program shown refusal-free on every path is go_mem-DRF
  and hence SC — the DRF-guarantee shape), so over-refusal costs
  COMPLETENESS (a correct-by-gc program that copies a live primitive
  cannot be verified — every such shape is a vet `copylocks` finding)
  and never SOUNDNESS; under-refusal would be unsound. go_mem's racy
  semantics is BOUNDED, not C-style undefined behaviour: the
  report-and-terminate branch the machine takes, or else word-sized
  racy reads observe an actually-written value, multiword values may
  tear, no out-of-thin-air — the bounded-VALUE branch is deliberately
  unmodeled (register #4's scoping; recorded with this ruling at
  register #13).
- What changed (`GoLean/GoCore/Race.lean` `syncEntryKinds` /
  `syncReleaseTailKinds`, consumed by `raceUpdate`'s sync arm in
  Multi.lean — the section docstring "The sync primitives' OWN state
  words" carries the per-entry derivation): each op records TSan's
  realized set ∪ go_mem's operation kind — THE UNION RULE, an [AGENT]
  READING inside the ruling (audit fix F3), not the ruling's words: the
  [USER] said "follow go_mem exactly", and go_mem's operation-level
  list makes EVERY mutex lock read-like, `sync.Mutex.Lock` included.
  Literal go_mem would therefore RUN a lone copy beside `Mutex.Lock`;
  gc's `-race` build REFUSES it (the Lock is a CAS on `m.state`, which
  TSan reports as a Write — measured: probe
  `u4gomem/mu-copy-vs-lock-only`, the copy unordered with the Lock op
  alone, gc RACE 20/20 at GOMAXPROCS 1 and 8, machine RACE — agree-race,
  and the BUG-080 pin `race/negative-sync/mutex-copy`). Dropping the
  realized atomicWrite would open a HOLE cell against the oracle (gc
  red, machine DRF), so the [AGENT] kept it, grounded in mem#model's own
  sentence that a compare-and-swap "is both read-like and write-like":
  the union never runs what the oracle refuses and never runs what go_mem
  calls racy. CONSEQUENCE, stated plainly: a lone copy beside
  `sync.Mutex.Lock` REFUSES (TSan realizes the CAS) while a lone copy
  beside `sync.RWMutex.Lock`/`RLock` RUNS (its counter RMW is under
  `race.Disable`, so only go_mem's read-like lock kind applies —
  `race/free-sync/rw-copy-beside-{rlock,lock}`). The asymmetry is the
  oracle's, inherited on purpose; COUNTERSIGNED [USER] 2026-09-03 at the
  round-5 merge sign-off («sounds good merge it», relayed to the
  recording worker by the [AGENT] coordinator, not firsthand — record:
  `docs/2026-08-31_qrow-rulings.md` row-9 appendix, "Countersign of
  the two [AGENT] readings"; per-gc-word keying countersigned by the
  same quote). EACH AT ITS gc WORD
  (`syncWord loc kind word` = `.field loc ⟨"sync.<Kind>"⟩ word`).
  RWMutex `RLock`/`Lock` → `.read @w` (realized, kept) + `.atomicRead
  @readerCount` (lock read-like); `RUnlock`/`Unlock` → `.read @w` +
  `.atomicWrite @readerCount` (unlock write-like). WaitGroup `Add`/`Done`
  → `.atomicWrite @state` (+ the realized `.read @sema` when the counter
  leaves 0 upward); `Wait` → `.atomicRead @state` (+ the realized `.write
  @sema` for the first blocking waiter). Mutex `Lock` → `.atomicWrite
  @state` UNCHANGED (mem#model: a CAS "is both read-like and write-like",
  so TSan's realized kind subsumes the read-like lock); Mutex `Unlock`'s
  release-tail `.atomicWrite @state` UNCHANGED (an access unordered with
  the unlock op is unordered with its tail, so the tail covers go_mem's
  write-like unlock and additionally TSan's acquirer-then-read verdict).
  Once → `.atomicRead @done` / `.atomicWrite @m` / `.atomicWrite @done` +
  tail `@m`, kinds unchanged. WHY THE WORDS (an [AGENT] design necessity
  inside the ruling, not a deviation from it): the realized `wg.sema`
  pair and `race.Read(&rw.w)` are PLAIN kinds; recorded at ONE path with
  the go_mem atomic kinds they would make a legal `Done` (atomic write)
  conflict with a legal first `Wait` (plain sema write), and a
  contending `RLock` (plain `rw.w` read) with an `Unlock` (atomic write)
  — refusing the canonical WaitGroup and RWMutex idioms. On gc's own
  struct layout these are DISTINCT words that never meet under TSan
  either; keying by word keeps every whole-primitive copy/overwrite
  overlapping all of them (`locPrefix`) while sibling fields and
  sibling words stay disjoint (check (i)'s guards
  `race/free-sync/{mutex-siblings,disjoint-prims}` stay green).
- What the rows pin: gc `-race` GREEN 20/20 at GOMAXPROCS 1 and 8 for
  each of the FIVE pinned shapes (`docs/evidence/2026-09-02_q-u4-gomem/`, families
  `u4gomem` — the formerly UNPROBED copy-beside-`RUnlock`/`Unlock` — and
  the BUG-080 family `u4kind` re-run: SIX rows move agree-DRF →
  `over-refusal` — `wg-copy-vs-add-from-0`, `wg-copy-vs-done`,
  `wg-overwrite-vs-done`, `wg-overwrite-vs-wait-at-0`, AND
  `rw-copy-vs-{rlock,lock}`, whose subjects pair the lock with its
  UNLOCK unordered with the copy and so refuse THROUGH the write-like
  unlock (the shape never isolated the lock op); every other u4kind
  cell unchanged. The ruling's "a copy beside `RLock`/`Lock` is NOT a
  race" is about the lock OP and holds: the isolated shapes
  `probes/u4gomem/rw-copy-vs-{rlock,lock}-only` (the child unlocks only
  after main's ack) are agree-DRF, and the corpus guards
  `race/free-sync/rw-copy-beside-{rlock,lock}` are born PASS/confluent
  — a write-like keying of the lock would refuse them). The racy
  lane's three-way rule files our-refusal +
  `-race`-green as an INVESTIGATION, never a pass; its outcome here is
  the fourth, ruled one — the program IS racy by go_mem, TSan's
  realized set is the incomplete side. The corpus rows carry gc's `ok`
  as expected_status and FAIL at lean-observation on the machine's
  `race`; the shape `wg-overwrite-vs-done` is a probe only (its gc
  outcome is schedule-dependent: the reset counter makes the Done a
  negative-counter panic on some schedules). AUDIT FIX F1 (2026-09-02):
  the slice had ALSO pinned `wg-overwrite-vs-add-nonzero` here as a
  go_mem-only shape — WRONG: gc `-race` is RED 20/20 at both GOMAXPROCS
  values (auditor's isolates; reproduced by the lane, probe
  `u4gomem/wg-overwrite-vs-add-nonzero` agree-race), because the racing
  overwrite resets the counter to 0 and the child's Add then IS the
  counter-off-0 case that executes `race.Read(&wg.sema)`
  (waitgroup.go:111-115). It is NOT reliably red either: when the Add
  lands first the counter goes 1→2 and TSan sees nothing — the fix
  round's first attempt re-homed the row in the racy lane and the full
  gate's single `-race` sample came back GREEN
  (`docs/evidence/2026-09-02_q-u4-gomem/f1-gc-green-sample.txt`). The
  gc side is schedule-dependent (red or green by schedule), the machine
  refuses on every path (the Add's write-like RMW is unordered with the
  overwrite on every schedule) — the same disposition as
  `wg-overwrite-vs-done`: not corpus-pinnable in any lane (a green
  sample fails a racy row, a red one an `ok` row), PROBE ONLY
  (`u4gomem/wg-overwrite-vs-add-nonzero`, agree-race under the
  runner's any-red-run definition, 20/20 red in the sampler). The
  corpus row was removed and left this Cases line.
- Scope: MISUSE ONLY — every shape is a whole-primitive copy or
  overwrite while another goroutine operates on it (vet `copylocks`);
  no race-free program's verdict moves (full `ci --diff`: no
  pre-existing row changed result or stage). Over-refusal vs the oracle
  in this class is the designed, recorded cost; the differential's
  lower bound (observed ∈ modeled) is untouched.

## BUG-085 — `storeLoc` at an UNALLOCATED `.base` address MATERIALIZED an untyped phantom cell instead of refusing: a fail-open fallback on the trusted surface, LATENT (unreachable on well-formed states) [TRUST-ADJACENT: GoCore Ops.lean; zero baseline drift]

- Status: fixed (2026-09-03, the `storeloc-failclosed` lane — the
  `none` arm of `storeLoc`'s `.base` case now refuses:
  `throw (.internal "store to unallocated address …: no heap cell
  (allocation goes through ExecState.alloc only)")`. Three proofs that
  had unfolded the arm lose a case: `storeLoc_shape` (StateWf.lean),
  `storeLoc_root_frame` (NPDRF.lean), `storeLoc_congr` (MachineSound.lean).
  No other semantics changed.)
- Pinned-by: none (LATENT fail-open — no corpus row can reach the arm,
  so a red-first differential row is impossible without breaking the
  allocation discipline. WHY unreachable: HEAP DENSITY — every address
  below `nextAddr` has a cell. Density is an audited CALL-GRAPH
  INVARIANT, not a `StateWf` consequence and not a theorem: `StateWf`
  (StateWf.lean:567) is only the bound `locSup σ ≤ nextAddr`, so it
  says every address a value carries is below `nextAddr`, NOT that
  such an address is populated. The audit (2026-09-03, [AGENT],
  corrected at the merge audit F1): `nextAddr` advances only in
  `ExecState.freshLoc` (State.lean:363), whose SOLE caller
  `ExecState.alloc` writes the cell with `Heap.set` in the same step;
  the only non-proof `Heap.set` sites are `alloc` and `storeLoc`'s hit
  arm; nothing erases a cell; the only non-proof `Loc.base`
  constructions are `freshLoc` (State.lean:362) and the decoder's
  bound-checked `globaladdr` (NativeToIR.lean:437, gid < the
  driver-seeded global count). Density is TRUE BY TYPE since the A2
  dense heap (design-hygiene A-series, 2026-09-04: `Heap := Array
  HeapCell`, every root write is `ExecState.updateCell`'s bounds-checked
  `Array.set`; the `.internal` refusal is the only out-of-range
  behaviour — `docs/2026-09-03_hygiene-a-series-design.md` §A2/§A3).
  The pin is therefore a Lean-level executable guard in `Tests/GoCoreEval.lean`
  (`gocore-eval-tests`, run by `scripts/ci`): `storeLoc {} (.base ⟨0⟩)
  (.int 7)` must be `.error (.internal _)` — shown FAIL against main's
  definition before the fix ("condition is false"), ok after — beside
  a positive control that the same store to an `alloc`'d cell succeeds
  and reads back. Cases: none — no baseline row is named, by design.)
- Discovered: 2026-09-03 by the grumpy-professor review
  (`docs/2026-09-03_grumpy-professor-review.md`, §2 U5 "The memory
  model is not a module" and §3 A2 "Dense heap"), which named the arm
  as "the fail-open aliasing the decoder's `globaladdr` bound check and
  the driver's `StateWf` assert exist to prevent".

Pre-fix (Ops.lean, `storeLoc`'s root case): `| none => return { state
with heap := Heap.set state.heap loc { value } }` — a lookup miss at
a `.base` address APPENDED a fresh cell with no `declaredTy` and
returned success. Under the charter's doctrine ("never a silent
default, never an absorbing fallback") that is a defect regardless of
reachability: had a dangling `.addr` ever reached it (a decoder gid
escaping its bound, a future allocator that forgot to write its cell),
the store would have silently succeeded and the phantom cell would
have ALIASED whatever later `alloc` landed on that address (alloc's
`Heap.set` overwrites an existing key), with no red anywhere. The two
external nets the review names — the decoder's `globaladdr` bound
check (NativeToIR.lean) and the driver's `StateWf` assert
(StepFn.lean `runProgramSetupM`) — are defense in depth, not a reason
to keep the fallback; the trusted surface must refuse on its own.

Refusal constructor ([AGENT] choice, inside the brief's suggestion):
`.internal`, not `.stuck`. The review's U12 notes the taxonomy rule is
unstated; the existing analogous sites are the rule this slice
follows — Multi.lean uses `.internal` for "cannot happen on a
well-formed state" (hchan-invariant breaches in `applyPairing`,
`resume on an unready blocked …`), and `.stuck` for an ill-shaped
program operand (`expected struct base for field store`). A store to
an unallocated address is the former. The READ side, `loadLoc`'s
`| none => stuck "unbound GoCore heap location"`, already refuses and
is left untouched: reclassifying it to `.internal` would change an
observable status string (`stuck` → `error`) for a taxonomy tidy-up
outside this slice — recorded here as a U12 instance, not fixed.

The same audit over every `Heap.lookup … | none =>` in the semantic
core (Ops.lean, Machine.lean, Multi.lean, StepFn.lean, Race.lean):
there are exactly TWO such sites — `loadLoc` (already refuses) and
`storeLoc` (fixed here). Every other heap access flows through those
two (Race.lean's call-site inventory says so and the grep confirms
it; the only direct `Heap.set` outside `storeLoc`'s hit arm is
`ExecState.alloc`). The other `| none => return …` arms in those files
are `Option` results of map/method/record lookups whose absence is a
modeled Go outcome (a missing map key reads the zero value; a nil map
delete is a no-op; a method-set miss is a `false` satisfaction
answer), not heap misses — legitimately optional.

What this slice does NOT do: the review's A2 proposal (dense heap,
`Heap := Array HeapCell`, addresses are indices) would make the arm
UNREPRESENTABLE by type; that is a representation change with its
own proof churn and belongs to its own arc. This entry is the minimal
fail-closed guard until then. Gate: full `ci --diff` with ZERO
baseline drift — the arm was indeed unreachable on every corpus row.
## BUG-086 — `strconv.FormatInt` used WITHOUT `strconv.FormatUint` in the same program: the injection plants FormatInt's shim SOURCE but not the FormatUint shim it calls, and the export dies in the type-checker (`type-check: golean-stdlib-shims.go:N: undefined: goleanShimStrconvFormatUint`) — a whole-program spurious refusal of an ALLOWLISTED stdlib function [frontend; `injectStdlibShims` plumbing on the D-002 surface]

- Status: fixed (2026-09-03, the `bug086-shim-closure` lane — [AGENT]-
  executed inside the coordinator's brief; a dependency-closure repair of
  injection PLUMBING: no shim, no body, no allowlist row — the D-002
  reading below holds. THE FIX [TRUST-ADJACENT: frontend shim injection
  plumbing]: `tools/nativefrontend/stdlibshim.go` gains `stdlibShimDeps`
  (shim key -> the OTHER shim keys its SOURCE calls: FormatInt ->
  FormatUint; fmtDyn -> fmtBundle, the latter already co-listed by every
  desugar row that plants it) and `closeShimDeps`, which
  `injectStdlibShims` runs on the scanned `needed` set — transitively,
  BEFORE the reserved-name collision scan (a co-injected name is
  collision-checked like a directly-named one), failing closed on a dep
  that names no shim source. Fix shape (i) generalized, chosen over the
  list-valued allowlist (ii) because a dependency is a property of the
  shim SOURCE, not of a call-site row: one table, declared once, and
  CHECKED against the sources in both directions by
  `stdlibshim_closure_test.go` (`TestStdlibShimDepsExact`: a reference
  with no row = this bug's shape; a row with no reference = a stale
  entry). The build-time closure tests: `TestStdlibShimInjectionClosedPerEntry`
  (every entry of the four call-shape tables — 20 — planted alone, the
  shim file type-checked STANDING ALONE; RED-FIRST on the pre-fix
  plumbing at exactly `strconv.FormatInt` and nothing else, green after —
  `docs/evidence/2026-09-03_bug086-shim-closure/transcripts/
  red-first-per-entry-prefix.txt`), `TestStdlibShimEachKeyClosedAlone`
  (all 19 shim sources, each with its declared closure — this one also
  covers fmtDyn, which no single table entry plants alone, so no corpus
  row can exercise that dep in isolation), `TestCloseShimDepsRefusesUnknownDep`.
  The Cases below flipped FAIL/frontend-export -> PASS (focused diff-one
  4/4 incl. the `strconv/format-parse` controls, then the full `ci --diff`
  re-pin, 0 PASS->non-PASS; evidence dir). Twin-wire pin UNMOVED
  (`eef32142627a…` — raftsubject/quorum calls FormatInt AND FormatUint in
  one unit, so its bundle was already closed) and the deviation pin
  unchanged.)
- Pinned-by: differential
- Cases: noodler/strconv-formatint/edges, noodler/strconv-formatint/positive
- Discovered: 2026-09-03 (the noodler lane — `docs/2026-09-03_noodler-report.md`
  finding F2; bisect record `docs/evidence/2026-09-03_noodler/probes/
  formatint-bisect/` + `transcripts/formatint-bisect.txt`). Mechanism
  CORRECTED at the lane's audit fix round (F-A): the first version of
  this entry blamed the `stdlibShimDeclNames` table at :234 and sketched
  a one-line fix there; the auditor built that fix and FormatInt-alone is
  STILL refused — that table is read exactly once, at :1462, for the
  reserved-name collision check, and plays no part in what gets injected.

Mechanism (`tools/nativefrontend/stdlibshim.go`, go1.26.5 pin tree):
`injectStdlibShims` walks the program's CALL SITES (:1391, the
`pkg.Sel(...)` selector scan) and marks `needed[shim]` for the shim the
allowlist maps each call to — `stdlibShimAllowlist["strconv"]["FormatInt"]
= strconvFormatIntShimName` (:165-167) — then concatenates
`stdlibShimSources[name]` for every needed name (:1498). The FormatInt
shim SOURCE (:973-985) calls `goleanShimStrconvFormatUint` on both of its
paths (:982, :984), but that function's source is planted only when
`needed[strconvFormatUintShimName]` is set, i.e. only when the program
itself calls `strconv.FormatUint`. Nothing in the pipeline expresses
"shim A's source depends on shim B's source": `stdlibShimDeclNames`
(:229-236) lists the NAMES a shim declares (for the collision check),
not the shims it needs. So a FormatInt-only program gets a shim file
that does not type-check, and the frontend refuses the WHOLE export.
Every FormatInt call shape is affected (bisect: ±, bases 2/10/16/36,
constant and variable arguments — five one-function programs, all
refused; the both-functions control exports). The existing conformance
pin `strconv/format-parse` calls FormatUint AND FormatInt in one body,
which is why the corpus never saw it.

Auditor's sweep (fix round F-A, recorded here): all 27 allowlisted
entries exercised ALONE, one program each — FormatInt is the ONLY entry
whose injected bundle is not closed under its own calls.

Working fix shapes (auditor-verified to export FormatInt-alone; the
both-functions control shows no redeclaration): (i) co-injection at
:1455 — when `needed[strconvFormatIntShimName]`, also set
`needed[strconvFormatUintShimName]` (the `shimUnsupportedName` rider
just above it is the precedent for a bundle-wide dependency); or (ii)
make `stdlibShimAllowlist` list-valued like the desugar tables at
:175-194 (`"FormatInt": {strconvFormatIntShimName,
strconvFormatUintShimName}`), so a call plants its whole closure.
Recommended alongside either: a build-time CLOSURE test in
`tools/nativefrontend/*_test.go` that, for each allowlist entry, injects
that entry alone and type-checks the result — the property this bug
violates, mechanized once for all 27.

D-002 reading (precise): the repair touches `injectStdlibShims` PLUMBING
(which already-written source gets planted), not a table row's meaning
and not a shim body; it adds no mechanism and no shim — FormatUint is
already allowlisted (:165), already in the tree (:956-970), already
validated by the `strconv/format-parse` rows and used by
`raftsubject`/`quorum`. So it is neither a widening of the frozen
surface nor a "shim that changes" under the Fields-standard rule; it
makes the surface's stated closure true. Classification:
spurious-refusal, frontend, whole-package kill. Not built here — the
noodler writes tests and records only. (Built at the `bug086-shim-closure`
lane, 2026-09-03 — see Status.)


## BUG-088 — a range over a map with an IRREFLEXIVE key (NaN, or an aggregate/interface holding one) never terminated: the key-set `mapIterK` frame could not mark a NaN entry produced, so the canonical run re-produced it forever (fuel-out) and the modeled set admitted any number of productions [FIXED BY CONSTRUCTION by the B1 entry-identity stamps; zero drift on every pre-existing row]

- Status: fixed (2026-09-03, design-hygiene arc slice 1 — the frame's
  `produced`/`start` sets are entry IDS, so a NaN entry is marked
  produced like any other and the range ends; `maps/nan-key-range`
  born green under the stamps, RED-FIRST shown against main's binary:
  `docs/evidence/2026-09-03_hygiene-b1-stamps/transcripts/nan-key-range-red-first.txt`)
- Pinned-by: differential
- Cases: maps/nan-key-range, maps/nan-key-range-aggregate/array, maps/nan-key-range-aggregate/struct, maps/nan-key-range-aggregate/interface
- [USER] ratification of the E9 narrowing on irreflexive keys: RATIFIED
  [USER] 2026-09-03 (relayed quote — Mike, via the [AGENT] coordinator,
  not firsthand: «(b) it sounds like this breaks an old ruling but ends up more accurate to real go - approved»; ruling record
  `docs/2026-08-31_qrow-rulings.md`, "The E9 irreflexive-key ruling
  record (2026-09-03)"). History of the referral (audit fix round F1,
  2026-09-03 — the fix shrinks the
  modeled set on this class from "any number ≥ 1 of productions of a
  NaN entry, or an immediate stop" to "each entry once"; E9's envelope
  is the [USER]'s 2026-08-19 ruling, so the narrowing is disclosed and
  referred, not self-adjudicated; the coordinator poses it at the
  sign-off). The aggregate rows (F2): `[1]float64{NaN}`, a struct
  field NaN, an `any` box NaN — all fuel-out on main @ 345ef090, gc
  32 / 73 / 32 = the branch; red-first transcript
  `docs/evidence/2026-09-03_hygiene-b1-stamps/transcripts/nan-key-range-aggregate-red-first.txt`.
- Discovered: 2026-09-03 (found while writing the B1 bisimulation
  argument — `docs/2026-09-03_hygiene-b1-stamps-design.md` §4: the
  key-set/id-set relation needs `valueEq` reflexive on the live keys,
  which it is not on NaN; no earlier corpus row ranged over a NaN-keyed
  map — the noodler NaN rows only insert/delete/len)

The retired mechanism: `Cont.mapIterK` carried `produced : Array
GoValue` and filtered candidates by `keyInKeys produced k`, i.e. Go
map-key equality (`valueEq`) — which is FALSE for NaN against itself
(spec#Comparison_operators: floating-point NaN compares unequal to
everything, itself included). A NaN-keyed entry therefore stayed a
candidate after every production, was never mandatory (its key is not
`valueEq`-equal to any start key either, so the stop slot was legal),
and at the zero stream the first candidate was picked forever:
`golean native-json-run --fuel 200000` on the pin row returns
`fuel-out` on main @ 345ef090 where gc prints 32. The spec's production
table ("For each iteration, iteration values are produced …") is over
ENTRIES, not keys: each of the two NaN entries is produced once. The
stamped frame marks the entry's id produced and terminates with 32 on
every stream (schedule-confluent). Observed ∈ modeled held before (a
stop after two productions was a member), so this was an over-wide
model with a wrong canonical member, not a differential mismatch on a
tracked row; it is recorded as a bug because the zero-stream run — the
member the strict lane compares — was wrong.

## BUG-087 — a VALUE-receiver method on a nil `*T` reached through gc's autogenerated `(*T).M` wrapper panics with gc's `panicwrap` text (`value method main.T.M called using nil *T pointer`, a `runtime.Error` WITHOUT the "runtime error: " prefix); the machine raises the generic nil-dereference text — gc's own text is OPTIMIZER-DEPENDENT on one source (latitude, not a forced point)

- Status: fixed
- Pinned-by: differential
- Cases: noodler/ifaces/mv-iface-nil-call, noodler/ifaces/iface-param-value-nil, noodler/ifaces/global-iface-value-nil, noodler/ifaces/mk-helper-value-nil, noodler/ifaces/iface-dispatch-value-nil, noodler/ifaces/spawn-iface-value-nil, noodler/ifaces/spawn-iface-value-nil-devirt, noodler/ifaces/spawn-helper-value-nil, multipkg/nil-value-method-text
- Discovered: 2026-09-03 (the noodler lane — `docs/2026-09-03_noodler-report.md`
  finding F1; probe records `docs/evidence/2026-09-03_noodler/probes/
  gc-wrapper-text/` (seven call shapes) and, the decisive one,
  `probes/gc-wrapper-text-mk-helper/` with transcript
  `transcripts/gc-wrapper-text-mk-helper.txt`). Numbered 085 on the
  lane's first records commit; renumbered at the audit fix round because
  the `storeloc-failclosed` lane owns that id and merges first.

The mechanism (auditor-verified at the pin, fix round F-B): gc emits the
pointer wrapper `(*T).M` around a value-receiver `T.M` with a nil check
ONLY for "simple *T wrappers around T methods" — `cmd/compile/internal/
noder/reader.go:3881`: `if wrapper.IsPtr() && types.Identical(
wrapper.Elem(), wrappee)` the wrapper body starts with `if recv == nil
{ runtime.panicwrap() }`. `panicwrap` (`runtime/error.go:324-348`)
panics with `plainError("value method " + pkg + "." + typ + "." + meth +
" called using nil *" + typ + " pointer")`; `plainError` is a
`runtime.Error` (`RuntimeError()` at error.go:120) whose text carries NO
"runtime error: " prefix. Promoted / embedded shapes are NOT in the
family (the wrapper's element is not identical to the wrappee) — there
gc dereferences and gives the ordinary nil-deref text, which the machine
already matches (`noodler/ifaces/promoted-value-nil` PASS). Whether a
given CALL SITE reaches the wrapper at all is decided by
devirtualization (`devirtualize.go` `StaticCall`, run from `gc/main.go:
251`; `go126ImprovedConcreteTypeAnalysis` is `const true` at :21 and
there is NO flag gate at :25) — which in turn depends on INLINING having
exposed the concrete type.

The same-source witness (one program, four flag sets; go1.26.5):

```go
func mk(p *Inner) Valuer { return p }      // inlinable helper
var p *Inner; v := mk(p); v.Val()
```

| gc flags | text |
| --- | --- |
| default | `runtime error: invalid memory address or nil pointer dereference` (mk inlined → devirtualized → plain deref) |
| `-gcflags=-l=4` | nil-deref text |
| `-gcflags=-l` | `value method main.Inner.Val called using nil *Inner pointer` (no inlining → wrapper → panicwrap) |
| `-gcflags=-N -l` | panicwrap text |

So there is no single gc answer to match — only an optimizer artifact,
the class the triage table ratified as a (c)-pin at C2 / BUG-061
("`go run` and `go run -gcflags=-N -l` disagree — there is no single gc
answer to match, only an optimizer artifact", [USER] ratified
2026-08-20) and the latitude inventory records at R15 (one
implementation, two realizations). The earlier "‑N ‑l still
devirtualizes" sentence in this entry's first version proved nothing
(the four probe shapes were different source and devirtualization is
not flag-gated); it is withdrawn.

Spec: the PANIC is forced — spec#Method_values / spec#Calls make the
call shorthand for `(*x).M`, spec#Address_operators: "If x is nil, an
attempt to evaluate *x will cause a run-time panic", spec#Run_time_panics
(a `runtime.Error`). The TEXT is not spec text: it is the (b)-PINNED
latitude row R9 ("Run-time panic VALUES and message texts — PINNED to
gc's realized strings"), and at this point gc's realized string is
two-valued.

Classification: **latitude** — a spec-open point (the message text)
where the machine holds ONE conforming member and gc realizes two,
decided by its optimizer (check-bugs.sh:171: `wrong-answer` is a
divergence at a FORCED point; this is not one). Both members are
`runtime.Error` values, so the recoverable KIND agrees
(`noodler/ifaces/iface-dispatch-value-nil-recovered` PASS); only the
message channel diverges. The three Cases rows stay RED on this line as
the latitude record; the machine's text is the default-flags text on
the devirtualized shapes (`noodler/ifaces/{iface-dispatch-value-nil,
mk-helper-value-nil}` PASS — the runner's oracle is default `go run`).

Proposed fix shape, for the [USER] (a records + envelope decision, not
implemented here): (1) an R9a sub-row in the latitude inventory
admitting the two-member set {nil-deref text, panicwrap text} for
value-receiver methods on a nil `*T` reached through an interface, with
the `-l` witness above as its evidence; (2) a (c)-pin row beside triage
C2 (the same "optimizer artifact" argument); (3) the three Cases rows
kept red here as `latitude`; (4) the re-envelope, when built: ONE
demonic choice at the pointer-box receiver's nil arm — `GoLean/GoCore/
Ops.lean:2147` (`| .nil => throw (.panic "runtime error: invalid memory
address or nil pointer dereference")`) — between the two texts, routed
to the membership lane like every other R-row envelope; the three rows
then move to `lane=membership` with `members=2`.

**[USER] 2026-09-03: fix shape item (4) — the demonic choice at the nil arm
— slice pending.** Ruling relayed by the [AGENT] coordinator («(2) panic-text,
agree, demonic choice so both are admitted» — full quote and provenance
chain in `docs/2026-08-31_qrow-rulings.md`, 2026-09-03 ruling record):
the re-envelope is item (4) above — one demonic choice between the two
texts at `Ops.lean`'s nil arm, routed to the membership lane; the three
Cases rows stay red on this line until that slice lands (a separate
lane implements it).

**FIXED 2026-09-03 (lane `bug087-paniktext`, [AGENT] implementing the
[USER] ruling above — cited as relayed, not firsthand).** The
re-envelope is `ChoiceSite.nilValueMethodText` (State.lean; width 2,
demonic, no pop at its bound-1 consults — then the site's `consumeAtOne
:= false` policy flag, since G-U 2026-09-04 the uniform rule), drawn in the frame-entry funnels
`enterFrameStep`/`enterFrameDeferPanicking` (StepFn.lean — the only
places the stream meets a frame entry; `Ops.lean`'s nil arm itself stays
`Except`-land and raises member 0). The shape predicate is
`nilValueMethodText?` (Ops.lean, the envelope statement): the anchor is
an interface-receiver method, the receiver argument is an interface box
holding a NIL pointer, `concreteMethodForDynamic?` resolves with
`needsDeref = true` (a value-receiver method whose receiver is EXACTLY
the pointee), and the target `Func` is not a synthesized promotion
wrapper (`Func.wrapper` — gc's `types.Identical(wrapper.Elem(),
wrappee)` with `wrappee := method.Type.Recv().Type`, so promoted
methods are outside the family; probed at the pin for value-embedding,
pointer-embedding and the value box: all nil-deref, `docs/evidence/
2026-09-03_bug087-paniktext/transcripts/shapes.txt`). Member 1 renders
`value method <key>.<M> called using nil *<T> pointer` from the
receiver's path-qualified `TypeId.key` — gc's `panicwrap` derives `pkg`
from the wrapper SYMBOL, i.e. the import PATH (`probe087/sub.T.Val …
nil *T pointer`), so this text is NOT in BUG-059's name-vs-path class;
a generic receiver's arguments collapse to `[...]` as gc prints them.
Mirrors extended in step: the relation's seven entry-panic rules
quantify the pick (`entryPanicText`), `stepFn_oblivious`/
`poolThreadOblivious`/`innerVecs`/`allStreamsOk` exclude the family
(fail closed), `CLI.stepNeeds`/`stepNeedsSeq` and the tracer's
`seqSite` mirror the bound via `entryCallSite?`+`nilValueMethodWidth`,
the census docs (latitude inventory §0 table, R9a; nondeterminism
doctrine mirror; triage note beside C2). The five family rows —
the three above plus `mk-helper-value-nil` and
`iface-dispatch-value-nil` (the latter two were strict PASS on member 0
and would have failed the strict lane's adversarial-stream check once
the site existed) — move to `lane=membership`, `members=2`, `samples=1`
(gc decides the text per toolchain — the version-tracking mode), with
the `-gcflags=-l` draws of the other member recorded as evidence
(`transcripts/rows-gcflags.txt`; the lane's oracle is `go run` only).
Audit fix round F1–F3 (2026-09-03): the `go`-statement entry twin
(`spawnStep`, Multi.lean) — first landed as a recorded member-0-only
residual — was a LIVE observed-∉-modeled (`go v.Val()` on a nil `*T` box
whose concrete type gc cannot see: panicwrap text under default/`-l`/
`-N -l`), so the pick is now threaded through `spawnStep` (`StepE.spawn`
quantifies it; the obliviousness layers exclude consuming spawns) with
rows `noodler/ifaces/{spawn-iface-value-nil,spawn-iface-value-nil-devirt,
spawn-helper-value-nil}` (gc: member 1 / member 0 — it devirtualizes
across the spawn when the type is visible / member 1); the
multi-package rendering row `multipkg/nil-value-method-text` makes the
path-qualifier claim a differential observation; `samples=` (retired on
main) dropped from every row. Audit finding recorded: the two re-laned
strict rows fail the pre-existing strict invariance check (stage
`nondet`, default = {nil-deref}, variant = {panicwrap}), so re-laning was
necessary.

## BUG-089 — `strconv.ParseUint` retired pending the slice-2 overlay (D-002 exception denied [USER] 2026-09-03): every ParseUint ERROR path refuses by name at `internal/stringslite.Clone` (`unsafe.String`) — [USER]-DIRECTED designed reds [frontend; stdlib source-through slice 1]

- Status: fixed (2026-09-03, lane `stdlib-source-2` — the OVERLAY
  mechanism landed exactly as this entry's Plan says: `tools/nativefrontend/
  stdlib-overlay.tsv` row `internal/stringslite/strings.go:149`
  substitutes `string(b)` for `unsafe.String(&b[0], len(b))`, byte-checked
  against the pinned file at every load (the line must carry the recorded
  bytes exactly once, else the unit refuses by site) and counted against
  the register's cap (5 of 12 sites used). All nine Cases rows flipped
  FAIL→PASS with the REAL `*strconv.NumError` values, texts and sentinels
  now coming from upstream text end to end (`strconv/format-parse/parse-uint-*`,
  `noodler/strings/parse-uint-edges`, `stdlib-source/strconv-parseuint/*`);
  `stdlib-source/frontier/atoi-error-path-clone` flipped too. No shim,
  no compensating body: the [USER]'s "clean retirement" is complete for
  ParseUint. Evidence: `docs/evidence/2026-09-03_stdlib-source-2/`;
  register `docs/stdlib-admission-register.md` (slice log 2026-09-03
  `stdlib-source-2`).)
- Pinned-by: differential
- Cases: noodler/strings/parse-uint-edges, stdlib-source/strconv-parseuint/bitsize-saturation, stdlib-source/strconv-parseuint/error-quoting, stdlib-source/strconv-parseuint/error-texts, stdlib-source/strconv-parseuint/numerror-type, stdlib-source/strconv-parseuint/range-sentinel, strconv/format-parse/parse-uint-bitsize, strconv/format-parse/parse-uint-errors, strconv/format-parse/parse-uint-range-value
- Discovered: 2026-09-03, lane `stdlib-source-1` — stdlib source-through
  slice 1 (docs/2026-09-03_stdlib-boundary-design.md §6; register
  docs/stdlib-admission-register.md; evidence `docs/evidence/2026-09-03_stdlib-source-1/`).

NOT A WRONG ANSWER: every case refuses at `frontend-export` with the cause
named at the site — `internal/stringslite.Clone: stdlib source-through:
internal/stringslite.Clone needs unsafe.String (… reached by every strconv
Parse* error path … pending the slice-2 overlay for stringslite.Clone)`.
Listed here because these nine rows were GREEN under the hand-written
ParseUint shim and are RED by [USER] direction now, and the re-pin guard
requires every PASS→non-PASS flip to sit on a Cases line.

**Mechanism.** `strconv.ParseUint` lowers from the pinned GOROOT source
(`deps/go/src/strconv/number.go`) like the other retired shims. Its
happy path is pure and PASSes (`strconv/format-parse/parse-uint-happy`,
`stdlib-source/strconv-parseuint/happy-bases`,
`panic-recover/shim-refusal-unrecoverable/parse-recover` — base 0 now
works, that row flipped FAIL→PASS). Its error path — `toError` →
`syntaxError`/`rangeError`/`baseError`/`bitSizeError` — copies the input
through `internal/stringslite.Clone`, whose body is
`unsafe.String(&b[0], len(b))`: an `unsafe` idiom in otherwise pure
library text (memo §2.3.2's overlay class) that the memo's §1.3 impurity
census did not list. The frontend quarantines `Clone` per declaration
(H-3), so any ParseUint call that takes the error path stops there, by
name.

**Why red rather than a shim.** The lane first kept a re-bodied ParseUint
shim constructing the real `*strconv.NumError` (a body change under the
D-002 freeze plus a new shim→library import coupling, `stdlibShimImports`)
and posed it as a D-002 exception. DENIED — [USER] Mike, 2026-09-03,
relayed by the [AGENT] coordinator (cited as relayed): «(a) we're not
running Raft right now, I think going red is simpler and safer, and lets
us do a clean retirement». The shim and its plumbing are gone; the
freeze is intact (no shim body changed); 15 shims remain.

**Plan (closes this entry).** Slice 2's OVERLAY mechanism (memo §2.3.2,
register cap 12): `internal/stringslite.Clone` = `string(b)` — the
`unsafe.String` is an allocation-avoidance idiom, the bytes are equal —
byte-checked against upstream at the pin and Fields-standard validated;
the same slice owes `strings.Builder`'s three sites, `errors.Join`, and
`internal/strconv/deps.go`'s float-bits casts. When it lands, these nine
rows flip FAIL→PASS (free) and this entry closes. Ledger row FR-21
carries the same shape. Raft: the twin subject's `raftpb.
ConfChangesFromString` calls ParseUint; the twin WIRE carries the real
body + the `Clone` stub (pin moved, structural diff in the evidence dir);
no corpus row exercises that path at this tip.

## BUG-090 — the interpreter's heap is an association list: every allocation and every cell write costs O(live cells), so allocation-heavy loops are QUADRATIC in allocation count and byte-slice `append` workloads worse — a cost bound that shapes corpus design (fuzz sizes, Builder rows, the 16 MiB Repeat row) [PERFORMANCE class; no wrong answer; GoCore representation]

- Status: open (found 2026-09-03/04 at the stdlib-source-2 landing and
  RE-DERIVED at its audit fix round F5 — the slice first attributed the
  cost to the in-place `append` path alone; the auditor's `make([]byte,
  4)`-in-a-loop probe showed allocation COUNT is the driver)
- Pinned-by: none (a performance bound, not a fidelity divergence: no
  row's observable is wrong; the row below exceeds the budget and refuses
  at `lean-observation` with the runner's named timeout — a FAIL-BY-DESIGN
  budget pin listed on the Cases line per the BUG-078 precedent, RECORD 8:
  check-bugs verifies EXISTENCE only for none-entries and counts a listed
  row as explained, so the row leaves baselines/untriaged-ids)
- Cases: strings/trimspace-repeat/repeat-bound-refused
- Discovered: 2026-09-03, lane `stdlib-source-2` (the real
  `strings.Repeat`/`Builder` bodies made multi-KB byte buffers reachable
  for the first time); measured
  `docs/evidence/2026-09-03_stdlib-source-2/append-cost-probes.tsv`

**Measurements** (golean `native-json-run`, single runs, shared box):
`make([]byte, 4)` in a loop — 1,000: 0.15 s, 2,000: 0.63 s, 4,000:
3.0 s (×4 count → ×20 time, quadratic); `new(int)` 1,000: 0.19 s,
4,000: 4.1 s; `string([]byte{…})` 4,000: 4.2 s; pure arithmetic 4,000:
0.09 s, 40,000: 0.68 s (linear). In-place `append` of one byte into a
pre-sized `make([]byte, 0, n)`: 256: 0.07 s, 512: 0.26 s, 1,024: 1.6 s,
2,048: 10.8 s, 4,096: 82 s; the SAME 1,000 appends after 4,000 live
4-byte allocations: > 120 s (timeout) — the append cost scales with the
LIVE HEAP, not only with the slice.

**Mechanism** (`GoLean/GoCore/State.lean`): `abbrev Heap := List (Loc ×
HeapCell)` with `Heap.lookup`/`Heap.set` walking the list — O(live cells)
per read/write; a fresh allocation appends past every existing cell.
Every allocation, every cell write, every value materialization pays
it; a byte-slice `append` writes cap-many cells (or re-materializes the
backing array), which is the amplification the slice first mistook for
the whole cause. (Hypothesis-with-evidence: the assoc-list
representation is confirmed by the source; a profile is owed at the
fix.)

**Consequences recorded**: Builder/Buffer rows stay ≤ ~1 KB; the
`strings.Repeat` 8 KB chunk-limit arm cannot be exercised; the Builder
fuzz is 10 × 300 operations, not the 100k the slice brief asked for
(`stdlib-source/builder-fuzz`); the 16 MiB `repeat-bound-refused` row is
a runner-budget red (BUG-073); the gotest lane's `fixedbugs/issue24419.go`
sits at MACHINE-REFUSED (30 s).

**Plan (closes this entry)**: the design-hygiene arc's A2 item (a DENSE
heap — `Array`-indexed cells keyed by `Loc`, O(1) lookup/set) with A3
(the professor's allocation-path items), `docs/2026-09-03_design-hygiene-arc.md`;
a GoCore REPRESENTATION change, semantics-preserving by the same
argument shape as B1's map stamps, gated by the full differential. When
it lands: re-measure the probes above, re-size the fuzz toward the
asked 100k, and re-expect `repeat-bound-refused`.

## BUG-091 — the native frontend's quarantine-reason text for multi-label `goto` shapes is EXPORT-NONDETERMINISTIC: `emit.go` ranges a Go MAP to name the offending label, so the wire bytes of one program differ run to run [frontend export nondeterminism; fail-closed but non-reproducible refusal text]

- Status: fixed (2026-09-04, lane `fr22-fr23`, commit 977b92e5 (pre-rebase 1aa49562; snapshot refs/snapshots/round11-fr22-fr23-2026-09-04) — the goto-label set
  is `sort.Strings`-ed before the refusal loop; the slice's go/types-typed audit of
  every `range <map>` in the frontend (57 sites) found and sorted two sibling
  first-hit refusals, `langversion.go` (build-constraint reserved tags) and
  `stdlibreach.go` (library layout-constant scan, now source-position order);
  guard = `TestEmitIsDeterministic` (20 emissions byte-compared; RED-FIRST on
  main's emitter: `docs/evidence/2026-09-04_fr22-fr23/bug091-red-first.txt`;
  audit inventory `bug091-map-range-audit.tsv`). The Cases row keeps `Expect:
  FAIL` BY DESIGN: the fix makes the refusal TEXT reproducible, not the result.)
- Pinned-by: none (the affected row is already RED by design — FR-21 frontier refusal; the nondeterminism is in the refusal's TEXT, invisible to the `result id stage` baseline and to the differential's status comparison; visible only through the tracer's `obsHash`)
- Expect: FAIL
- Cases: stdlib-source/frontier/index-rune-goto
- Discovered: 2026-09-04, the design-hygiene A-series (lane `hygiene-a-series`)
  choice-trace comparison — the row's `obsHash` moved between two whole-corpus
  runs of IDENTICAL machine sources; diagnosis and transcripts:
  `docs/evidence/2026-09-03_hygiene-a-series/choice-trace/a3-summary.txt`
  and `a6-summary.txt` (md5 of the two wires, the one-line JSON diff,
  and the hash-by-(binary, wire) matrix showing the hash is a function
  of the wire alone). Confirmed at the pre-merge audit: 30 exports of one
  2-label program gave 26× "next" / 4× "fallback".

WHAT: `tools/nativefrontend/emit.go:2194` — `for name := range e.gotoLabels`
picks the label named in the `unsup` reason text by Go MAP iteration order,
so the emitted `"unsupported": "strings.IndexRune: goto target label
<next|fallback> not at function body top level"` differs across exports of
the same program. Every export still REFUSES (fail closed, same class,
same row status); what breaks is the premise "wire = f(program)" that the
twin-wire pin and every wire-hash record rest on — for this shape the
emitted bytes are not reproducible. The same file already sorts label
sets deterministically at :1390 and :5857 (`// deterministic refusal
message`); this site is the omission.

PLAN (being taken by lane `fr22-fr23`; NOT this lane's — the A-series
makes no frontend edits): collect the label names, `sort.Strings`, name
the first (one line), plus a determinism unit test (emit N× → identical
bytes) so the class cannot recur silently. Fix criterion: N exports of
the affected program are byte-identical; the row stays red on FR-21.

## BUG-092 — `cmp.Compare` at a FUNCTION-LOCAL defined type argument refuses (mono.go's C6 naming rule) now that the kind-dispatch desugar is retired — a designed red BY [USER] RULING, plan on FR-19 [coverage; frontend generic instantiation at local types]

- Status: fixed (2026-09-05, lane `fr19-bug097` [AGENT] — FR-19's plan landed,
  design note `docs/2026-09-05_fr19-bug097-design.md` §2.2: a function-
  local type keys by SCOPE ORDINAL (`main.index·1`), and a FUNCTION
  instantiation's FuncId is identity-only (never a gc text), so
  `cmp.Compare[main.index·1]` / `slices.SortFunc[[]main.ltup·1,main.ltup·1]`
  stencil through the real generic — `renderTypeKey` admits local types
  in `funcInstCtx`. C6 stays for a generic TYPE's argument (observable
  `main.box[main.score·N]`, gc's compiler counter), pinned red by design
  by `scoping/local-type-identity/type-instantiation-refused`. The PLAN's
  `@cmpCompareKinds` spelling became the per-package source-order ordinal
  `·N` (design note §2.2, decisions log). All three rows PASS.)
- Pinned-by: differential
- Cases: slices/sortfunc-cmp/cmp-compare-kinds, stdlib-source/cmp-compare/local-float-type, slices/sortfunc-cmp/sortfunc-local-type, generics/local-type-argument
- Discovered: 2026-09-03 (stdlib source-through slice 2: retiring the desugar flipped `cmp-compare-kinds` red; the slice's STOP rule restored it and POSED the choice to the [USER]); DECIDED 2026-09-04 — [USER] Mike, relayed by the [AGENT] coordinator (cited as relayed): «(2) given we have a plan, I think this should be an honest red». Landed by lane `fr24`, checkpoint C (`docs/evidence/2026-09-04_fr24-fr25/`).

WHAT: `cmp` is a source-through library unit and `cmp.Compare[T]` is the real
generic at every type argument. A call whose type argument is a defined type
declared INSIDE a function body (`type index uint64` in `cmpCompareKinds`;
`type score float64` in `cmpLocalFloatType`; `type ltup struct{…}` in
`sortFuncLocalType` — `slices.SortFunc[[]ltup, ltup]`, added at the fr24
audit fix round L5: the identical mono.go text) instantiates the generic at a
type mono.go refuses to NAME: gc renders function-local types in
instantiation renderings with a compiler-internal unique suffix
(`score·1`), the ratified impossibility C6 (ledger §5.1 item 1). The
retired desugar (`cmpshim.go`, W4.3 landing B) sidestepped the naming by
never instantiating anything — it converted to a monomorphic kind shim —
which is why `cmp-compare-kinds` was green under it for integer/string
kinds while the float row was already red (the asymmetry the slice-2 audit
rowed). Both rows now refuse the same way, by name, at frontend-export.

WHY A BUG ENTRY: the [USER] ruled the row an honest red rather than keep a
shim whose only remaining purpose was masking a frontend generality gap
(D-002: 6 fmt shims remain; the freeze is intact). The re-pin guard
requires every PASS→non-PASS flip on a Cases line; this is that line.

PLAN (FR-19, ledger §4 / queue 19): scope-qualify the identity KEY of a
function-local type (enclosing function + declaration position) while the
RENDERED name keeps gc's spelling — the mangled instantiation key then
carries the scope and `cmp.Compare[main.index@cmpCompareKinds]` stencils;
C6 stays the impossibility only where the NAME is observable (`%T`/`%v` of
a value of the type), which neither row does. Fix criterion: both Cases
rows PASS through the real generic; the entry flips to fixed.

## BUG-093 — `print`/`println` residuals of stdlib slice 3: float/complex operands, the zero-operand spellings, and prints during `$pkginit` REFUSE by name (FR-29) — designed reds, the machine built-in admitted for bool/integer/string only [coverage; frontier residual of a [USER]-ruled admission]

- Status: open
- Pinned-by: none (every row is RED by design: the frontend refuses at `emitPrintStmt` by name — floats/complex (`floats and complex print through internal/strconv.AppendFloat …`), zero operands (`with zero operands …`), the address-printing kinds (`prints an address in gc …`, PERMANENT — ledger §5.1 item 3) — and the machine refuses an init-phase print at `runInitConfig` (`print/println during package initialization …`); a lowering that produced bytes here would be a wrong answer against gc's stderr)
- Expect: FAIL
- Cases: builtins/print/refused/float, builtins/print/refused/float32, builtins/print/refused/zero-operands, builtins/print/refused/pointer, builtins/print/refused/nil-pointer, builtins/print/refused/slice, builtins/print/refused/map, builtins/print/refused/chan, builtins/print/refused/func, builtins/print/refused/interface, builtins/print/refused/unsafe-pointer, builtins/print/in-init, builtins/print/refused/race-with-output
- Discovered: 2026-09-04 (stdlib slice 3, lane `stdlib-slice-3`; design note `docs/2026-09-04_stdlib-slice-3-design.md` §3.3–§3.4)

WHAT: gate G2 (RULED [USER] 2026-09-03 as recommended, relayed by the
[AGENT] coordinator, cited as relayed: «print/println as machine built-ins
with a stderr observable: admit with gc's pinned format for
int/uint/bool/string, refuse address-printing kinds and initially floats»)
admitted `print`/`println` as the `Stmt.print` machine statement whose
bytes are the `StepEvent.out` OUTPUT EVENT (G-OUT) and the differential's
new `output` field. Three operand classes stay outside this slice, each
a fail-closed refusal naming its cause: (i) floats/complex — gc's
`printfloat64` is `internal/strconv.AppendFloat(v, 'g', -1, 64)`
(runtime/print.go @ go1.26.5), the SHORTEST round-trip decimal (a Ryū-class
algorithm; a go1.26 change, commit 9035f7ae), not a ~40-line transcription
— [AGENT] call, disclosed: refuse now, row it, the faithful route is
source-through `internal/strconv` (its deps.go casts are the `float-bits`
primitive, now admitted) CALLED from the print arm — a machine-op-calls-
library-Func shape that needs its own argument; (ii) the zero-operand
spellings `print()`/`println()` — the wide-statement mold has no nullary
plan (A8); (iii) a print reached during `$pkginit` — the init phase runs
on the sequential driver, which has no event fold; `runInitConfig` refuses
rather than DROPPING the bytes (the CLI's init mirrors carry the same
guard). The address-printing kinds (pointer/chan/map/func/slice/interface/
unsafe.Pointer) are on the same Cases line but are NOT residuals: gc
prints ADDRESSES (`printpointer`, `printslice` `[len/cap]0xaddr`,
`printeface`/`printiface` `(0xtype,0xdata)`) the machine does not have —
a permanent by-name refusal (ledger §5.1 item 3, re-posed at this slice).

MEASURED (gotest triage re-run over the 195 formerly print-refused
$GOROOT/test files, `docs/evidence/2026-09-04_stdlib-slice-3/gotest-results.tsv`):
120 MATCH with output compared, 23 refuse on these print kinds (10 float,
13 address — counted on the refusal texts, audit fix round C2), 3 on the
init-phase guard, the rest on unrelated frontiers (os.Exit ×14 — gate G7
— time.Sleep, runtime.FuncForPC, reflect …). (iv), added at the audit fix
round A2: a RACY program that prints — TSan's report interleaves
asynchronously with the program's fd-2 bytes, so the harness split
refuses any output before the report and does NOT detect output after
it; row `builtins/print/refused/race-with-output` is the rowed
limitation (red at stage go-observation by the split's own name).

PLAN: ledger FR-29 (queue 29, M).

## BUG-094 — `math.Float64bits`/`Float32bits` of the machine's CANONICAL NaN REFUSES by name — the `float-bits` primitive makes NaN payloads observable, and every NaN the machine PRODUCES is narrowed to one pattern (latitude R7) that gc/amd64 does not realize [latitude; R7's re-envelope obligation surfaced by a [USER]-admitted primitive]

- Status: open
- Pinned-by: none (all three rows are RED by design at lean-observation: `floatBitsApply` refuses `unsupported "math.Float64bits of the machine's canonical NaN (0x7FF8000000000000): the payload of a machine-PRODUCED NaN is latitude the machine narrows (inventory R7) and gc/amd64 realizes differently — refused rather than reported"`; a reported 0x7FF8000000000000 would be a wrong answer against gc's 0xFFF8000000000000 (0/0) or 0x7FF8000000000001 (payload propagation))
- Expect: FAIL
- Cases: builtins/float-bits/canonical-nan-refused, builtins/float-bits/nan-arith-payload-refused, builtins/float-bits/nan-arith-payload-refused/canonical-roundtrip, builtins/float-bits/neg-canonical-refused, builtins/float-bits/neg-canonical-refused/float32, builtins/float-bits/min-max-canonical-refused, builtins/float-bits/roundtrip-payloads
- Discovered: 2026-09-04 (stdlib slice 3; the primitive's admission condition — «preserve NaN payloads exactly … ±0 / quiet/signaling round-trip probes» — is MET for every pattern that enters through `Float64frombits` (rows `builtins/float-bits/roundtrip-payloads`, `nan-semantics`, `float32`: bit-exact, green); what the condition did not anticipate is the machine's OWN NaNs)

WHAT: R7 narrows every NaN the machine produces (arithmetic, conversion) to
the canonical quiet NaN — softfloat64.go's own `return nan64` at every
NaN-producing case — and its argument was "payloads are unobservable
in-language". `math.Float64bits` (ADMITTED [USER] 2026-09-04 as a
primitive) makes them observable: gc/amd64 (SSE) realizes 0xFFF8000000000000
for 0/0 ("real indefinite", sign bit set) and PROPAGATES the first NaN
operand's payload through arithmetic (`Float64frombits(0x7FF8000000000001) * 2`
keeps the payload), so the machine's canonical result would present as a
wrong answer at exactly one observable pattern. `floatBitsApply` therefore
refuses the DEFAULT NaN under `*bits` by name (Ops.lean) — under EITHER
sign, since the audit fix round A1 (2026-09-05): the first cut tested the
canonical pattern exactly, but `fneg64` is a bare sign flip, so
`Float64bits(-(zero/zero))` REPORTED 0xFFF8000000000000 where gc gives
0x7FF8000000000000 — a wrong answer (row `neg-canonical-refused{,/float32}`
pins it red now). A1's second family: float `min`/`max`. gc/amd64's
lowering ORs the two operands' bits when one is a NaN (AMD64.rules
MINSD/MINSD/POR; `max = -min(-x,-y)`), so `Float64bits(min(Float64frombits
(0x7FF8000000000001), 2.5))` is 0x7FFC000000000001 in gc — the first cut
returned the NaN operand's bits and was WRONG; `floatMinMaxBits` is now
transcribed from the idiom (rows `min-max-payload{,/float32}` green, both
operand orders, ±0 ties, NaN/NaN) and returns the default NaN whenever
either operand is one (gc's default carries the opposite sign — an OR
over it would report a sign-wrong pattern the guard cannot recognize;
row `min-max-canonical-refused`). The producible-NaN set is therefore
exactly {default, −default}; every other pattern entered through
`*frombits` and passes bit-exact. The OVER-refusals —
`Float64bits(Float64frombits(0x7FF8000000000000))` and the 0xFFF8… entry
of `roundtrip-payloads` (PASS→FAIL at A1: the row's own reason line in
the baseline header) — are the price of not distinguishing provenance,
recorded rather than absorbed. Same class as the R6 float→int refusal
pins: a declared latitude resolved by failing closed. [AGENT] decision,
disclosed in the design note §2.3; falsified invariant texts ("the
machine never produces a non-canonical NaN") corrected at A1.

PLAN: R7's re-envelope — either make NaN payload production platform-
faithful (x86 SSE rules: first-operand propagation, 0xFFF8… for invalid
ops — a FloatBits.lean transcription decision of the floats design note's
class, scoped to the oracle platform like R4) or widen R7 to an (a)
envelope over the payloads gc's ports realize. Owner: the floats design
(`docs/2026-08-04_floats-design.md`); the latitude inventory R7 entry
carries the trigger.

## BUG-095 — a type switch (and its `case`) against an interface type that EMBEDS another interface answers "satisfied" for a dynamic type that implements only the EMBEDDED interface's methods (`case J` with `J interface{ I; bar() }` matches a `myint` that has `foo` but no `bar`) [fidelity; interfaces/embedding; surfaced by the output observable]

- Status: fixed (2026-09-05, lane `bug095-096` [AGENT] under [USER] direction 3 — the ROOT is the
  FRONTEND's interface-declaration emission, not the machine's satisfaction walk: at every
  interface DISPATCH site (`emitCall`'s interface-receiver arm, the method-value and
  method-expression arms, and the promotion wrapper over an embedded interface FIELD)
  `tools/nativefrontend/emit.go` registered the interface under the STATIC operand's wire
  name but with the METHOD'S DECLARING interface (`Signature.Recv()`), which for a method
  promoted from an embedded interface is the EMBEDDED one; `noteInterface` was
  last-writer-wins, so `j.foo()` with `j : J` and `foo` declared in `I` rewrote `main.J`'s
  wire TypeDef to `I`'s method set `{foo}`. The machine then answered exactly what the wire
  declared (evidence: the CONTROL block of `bug095-machine-transcripts.tsv` — main's wire on
  the fixed machine reproduces every wrong answer). FIX: the four sites register the static
  interface type's OWN `*types.Interface` (`staticIfaceOf`, alias-transparent and
  substitution-aware; `tools/nativefrontend/wire.go`), and `noteInterface` now REFUSES the
  export by name when one wire name is registered with two non-identical method sets
  (`ifaceConflicts`, checked in `emitProgram`'s declaration pass) — the silent mechanism is a
  named refusal. Guards: `TestEmbeddingInterfaceDefKeepsOwnMethods` (RED-FIRST on main's
  emitter: `main.J` = `[foo]`, `docs/evidence/2026-09-05_bug095-096/embedding-satisfaction.interface-defs.txt`)
  and `TestNoteInterfaceConflictRecorded`. Twin pin: unmoved (the raft twin declares no
  embedding interface; `scripts/check-frontend-pins` green).)
- Pinned-by: differential
- Cases: interfaces/embedding-satisfaction/typeswitch, interfaces/embedding-satisfaction/assert, interfaces/embedding-satisfaction/assert-ok, interfaces/embedding-satisfaction/nested, interfaces/embedding-satisfaction/method-value, interfaces/embedding-satisfaction/method-expr, interfaces/embedding-satisfaction/promoted, interfaces/embedding-satisfaction/generic, generics/type-switch-interface-param, generics/type-switch-interface-param/bound, generics/type-switch-interface-param/plain
- Discovered: 2026-09-04 (stdlib slice 3's gotest triage re-run — $GOROOT/test/typeparam/typeswitch3.go,
  whose printed output is compared since that slice: gc `myint 11`, machine `T 11`; the slice-3
  lane recorded this entry OPEN on its branch (a4865e66) with Cases
  generics/type-switch-interface-param{,/bound,/plain}. MERGE-TRAIN NOTE [AGENT]: this entry and
  slice 3's are ONE bug under ONE number (095 was already allocated to it there; main's next free
  number, 093, belongs to other in-flight lanes) — whichever merges second keeps THIS entry's
  Status/prose and APPENDS slice 3's three Cases ids to the line above; those three rows flip
  FAIL -> PASS at that merge (a non-PASS -> PASS flip, allowed; baseline re-pin note owed there).
  BOTH ARMS, spelled out (audit fix round 2026-09-05 [AGENT]): (i) THIS lane merges first —
  slice 3's three rows are BORN PASS at slice 3's merge (no flip; slice 3's rebase re-pins them
  PASS and its OPEN entry text yields to this FIXED one); (ii) slice 3 merges first — this lane's
  rebase re-pins them FAIL -> PASS with a baseline re-pin note naming the flip. Either arm resolves
  the `docs/BUGS.md` conflict by keeping THIS entry's Status/prose and appending the Cases ids.
  RESOLVED at merge train round 15 (2026-09-05, [AGENT] rebase of this lane onto main 102f4dae): arm
  (ii) happened — `stdlib-slice-3` merged first (round 14). Slice 3 FILED this bug (its OPEN entry's
  B1 root-cause diagnosis — `emit.go` `noteInterface(ifaceName, recvIface)` keyed by the static
  interface but registering the declaring receiver's set, last-write-wins — agrees with this entry)
  and this lane FIXED it; slice 3's entry text yielded to this one, its three Cases ids were appended
  above, and the three rows were re-pinned FAIL -> PASS (stage `-`) in this lane's baseline block.)

WHAT (spec#Embedded_interfaces, spec#Interface_types, spec#Method_sets): the method set of
`J interface{ I; bar() }` is the UNION `{foo, bar}`; a type implements `J` iff its method set
is a superset. On main, with `type myint int` carrying `foo` only, `x.(J)` succeeded, the
comma-ok form answered `true`, `case J` matched before `case myint`, the one-value
assertion `i.(J)` returned normally where gc panics (RED-FIRST block: machine `ok [8]`), and
— the slice-3 auditor's shape — `i.(J).bar()` reached the machine's dispatch-invariant STUCK
`dynamic type main.esOnlyFoo has no method bar`. Two levels are lost at once for `K ⊃ J ⊃ I`
(main's wire: `main.esK = [foo]`). The direction is always ACCEPTS TOO MUCH. The defect is
EMISSION-ORDER DEPENDENT: a dispatch of the embedding interface's OWN method through it
(`j.bar()`) re-registers the full set, so a program containing one such dispatch AFTER the
poisoner is correct by accident — which is why (slice-3 audit, relayed by the coordinator)
the slice-3 entry's claim that "the NON-generic twin also fails" is FALSE in isolation, and
its three pins are order-fragile (an emission-order change would turn them green with the
defect alive). The `interfaces/embedding-satisfaction` file therefore contains NO dispatch of
an embedding interface's own method through it: every row exercises the wrong satisfaction
directly, whatever order the emitter visits bodies in (8 rows red-first; `negative` — own
method present, EMBEDDED one missing — is correct on main by construction and stays as the
control). The pre-existing rows `interfaces/embedded-interface{,-assertion}` never saw it
because their dynamic types carry every method.

CLASS PROBE vs gc (all nine rows PASS; `docs/evidence/2026-09-05_bug095-096/README.md`):
type switch `case J` (typeswitch), one-value assertion panic text `interface conversion:
main.esOnlyFoo is not main.esJ: missing method bar` (assert), comma-ok (assert-ok), nested
embedding K ⊃ J ⊃ I with the two-levels-down method dispatched — gc rejects a type carrying
two of K's three methods, main accepted one of three (nested), the reverse cell —
own method present, embedded one missing → `missing method foo` (negative), the trigger as a
method value / method expression / promoted wrapper (method-value, method-expr, promoted),
and the type-parameter case instantiated to `J` — typeswitch3.go's exact shape (generic:
gc 211 112 110 205, main 111 112 110 205). Interface-to-interface CONVERSION is static
(go/types checks it; no runtime check exists to be wrong). Embedding two interfaces with a
same-named method of DIFFERENT signature is a compile error (`duplicate method`) — not a
runtime question; the identical-signature duplicate is already pinned
(`interfaces/embedded-interface-duplicate-method`).

## BUG-096 — a shift by a count far past the operand width (`x << (1<<32)`, `u << (1<<40)`) makes the machine compute `2^count` in `Nat` and DIE with an INTERNAL PANIC (`Nat.pow exponent is too big`) instead of yielding 0 [fidelity/robustness; ints/shifts; surfaced by the gotest re-run]

- Status: fixed (2026-09-05, lane `bug095-096` [AGENT] under [USER] direction 3 —
  `GoLean/GoCore/Ops.lean` `intShiftLeftResult` / `intShiftRightResult` now look up the
  operand kind's width and SATURATE before any power is formed: `count ≥ bits` yields 0 for
  a left shift and an unsigned right shift, and the sign fill (−1 for a negative signed
  operand, else 0) for a signed right shift; the in-width path is unchanged. The width lookup
  (`intKindBitWidth`) refuses an `unbounded` kind by name — none reaches the machine (the wire
  decoder never produces one), so that arm is fail-closed, not a regression. The two
  `StateWf` lemmas (`intShift{Left,Right}Result_locSup`) follow the new branch. GoCore audit:
  these were the ONLY `^`/`Nat.pow` sites with a RUNTIME exponent — every other power in
  `GoLean/GoCore/` is over a kind width (≤ 64), a platform constant, or a FloatBits
  exponent-difference bounded by the float format. Cost, not just abort: the coordinator's
  measurement (slice-3 audit, relayed) puts a count of `1<<31` at ~1.1 GB RSS on main —
  a `2^count` that fits under the `Nat.pow` guard is still materialized; the saturation
  removes that too. The [AGENT audit, 2026-09-05] ladder on main's binary: 2^24 → 76 MB,
  2^28 → 200 MB, 2^30 → 591 MB, 2^31 → 1116 MB RSS, all answered correctly; 2^32 is the
  FIRST abort — the abort boundary is the `Nat.pow` guard, not ~2^24 as the evidence README
  first said (corrected at that round, finding R1).)
- Pinned-by: differential
- Cases: ints/shift-count-bound/left-huge, ints/shift-count-bound/right-huge-signed, ints/shift-count-bound/right-huge-unsigned, ints/shift-count-bound/int-count, ints/shift-count-bound/untyped-const, ints/shift-count-huge
- Discovered: 2026-09-04 (stdlib slice 3's gotest triage re-run — $GOROOT/test/fixedbugs/bug356.go:
  `go run` prints nothing, `native-json-run` aborts the PROCESS with `INTERNAL PANIC: Nat.pow
  exponent is too big`. The slice-3 lane recorded this entry OPEN on its branch (a4865e66) with
  Cases ints/shift-count-huge. MERGE-TRAIN NOTE [AGENT]: same rule as BUG-095 — one bug, one
  number; the second merge keeps this entry and appends `ints/shift-count-huge`, which flips
  FAIL -> PASS at that merge. BOTH ARMS (audit fix round 2026-09-05): this lane first — the row is
  BORN PASS at slice 3's merge, no flip; slice 3 first — this lane's rebase re-pins it FAIL -> PASS
  with a baseline re-pin note. Either arm keeps THIS entry's Status/prose in the conflict. RESOLVED at merge train
  round 15 (2026-09-05, [AGENT] rebase onto main 102f4dae): slice 3 first — filed there, fixed here;
  `ints/shift-count-huge` appended above and re-pinned FAIL -> PASS (stage `-`) in this lane's
  baseline block.)

WHAT (spec#Operators — "There is no upper limit on the shift count. Shifts behave as if the
left operand is shifted n times by 1"): `12345 << (1<<32)` is 0 for an `int`, `1 << (1<<40)`
is 0 for a `uint64`, `-x >> (1<<32)` is −1. The machine's shift arms evaluated `2^count` over
unbounded `Int` BEFORE normalizing to the kind's width — fine below Lean's `Nat.pow` guard,
fatal beyond it: a process abort is neither an observation nor a refusal (the harness sees
no JSON). RED-FIRST transcript (main's binary at ac45aedd, `bug096-machine-transcripts.tsv`):
left-huge / right-huge-signed / right-huge-unsigned / int-count / untyped-const all
`INTERNAL PANIC`; width (count exactly 64/8/32), width-minus-one (63/7/31) and
negative-panic (a hugely NEGATIVE count → `runtime error: negative shift amount`) were
already right and stay as controls.

CLASS PROBE vs gc (all eight rows PASS): `x << (1<<32)` over int/uint64/int32/uint8;
signed `>>` by 1<<40 of positive and negative operands (0 / −1); unsigned `>>` (0); count
exactly at the width; the last in-width count (`1<<63`, `int8(1)<<7` = −128); a SIGNED count
type (`int`, Go 1.13+) both huge and in-width; the negative-count panic text; and the
untyped-constant left operand of a non-constant shift (`var b uint8 = 1 << m` with m = 8 → 0;
`d := 1 << big` → int → 0; `var c int32 = 1 << k`, k = 31 → MinInt32) — the type rule is
go/types' (spec#Operators), the width that saturates is the assumed type's.

## BUG-097 — the ANONYMOUS-interface wire name is qualified with package NAMES while every other TypeId is keyed by import PATH: two same-named packages at different paths fuse two DISTINCT `interface{ M() T }` types onto ONE wire name — a wrong satisfaction answer on main, a named refusal since BUG-095's conflict guard [fidelity; frontend identity; multipkg; surfaced by the bug095-096 audit (R2)]

- Status: fixed (2026-09-05, lane `fr19-bug097` [AGENT], design note
  `docs/2026-09-05_fr19-bug097-design.md` §2.3: the anonymous-interface
  key is minted by ONE constructor, `anonIfaceKey` (identity.go), used by
  both `emitType`'s interface arm and `ifaceWireName` — path-qualified
  named types, PATH-qualified UNEXPORTED method names (the probe found
  that `types.TypeString` never qualifies those even with a qualifier,
  so the PLAN's one-liner would have left a second fusion class —
  BUG-098), function-local types by scope ordinal, methods in gc's
  order. `interface{Get() red/inner.T}` ≠ `interface{Get() blue/inner.T}`;
  the conflict guard never sees them as one. The gc display
  `interface { Get() inner.T }` travels beside the key (BUG-059's split),
  so the missing-method / nil / source-position texts are byte-exact —
  pinned by `multipkg/same-name-anon-iface-panic/{missing,source}` and
  the single-package display suite `interfaces/anon-iface-display/*`.
  Evidence: `docs/evidence/2026-09-05_fr19-bug097/` (gc probes P2/P3/P5).)
- Pinned-by: differential
- Cases: multipkg/same-name-anon-iface, multipkg/same-name-anon-iface-panic/missing, multipkg/same-name-anon-iface-panic/source, interfaces/anon-iface-display/missing-order, interfaces/anon-iface-display/unexported, interfaces/anon-iface-display/unexported-satisfied, interfaces/anon-iface-display/embedded-flattened, interfaces/anon-iface-display/source-display, interfaces/anon-iface-display/nil, interfaces/anon-iface-display/slice-target, interfaces/anon-iface-display/named-result

WHAT (spec#Type_identity: two named types are identical only if they are the same type —
`red/inner.T` is not `blue/inner.T`; two interface types are identical iff they have the same
method set, signatures compared under type identity — so `interface{ Get() red/inner.T }` and
`interface{ Get() blue/inner.T }` are DIFFERENT types): `tools/nativefrontend/wire.go`
(`emitType`'s anonymous non-empty interface arm) and `emit.go` (`ifaceWireName`'s structural
fallback) mint the anonymous interface's wire name with
`types.TypeString(iface, func(p *types.Package) string { return p.Name() })` — the package
NAME — while every other TypeId qualifies by IMPORT PATH (`identity.go` `pkgQualifier`, the
BUG-010 fix). Two packages named `inner` at `red/inner` and `blue/inner`, each with its own `T`
and its own `interface{ Get() T }`, therefore render as one name, `interface{Get() inner.T}`.
On main `noteInterface` was last-writer-wins, so whichever package's interface was registered
LAST supplied the machine's requirement list for BOTH: the [AGENT audit, 2026-09-05] measured
gc `1 4 true false` against main `1 4 false false` — red's value judged NOT to satisfy red's own
interface: a WRONG ANSWER, emission-order-dependent. Since this lane's BUG-095 fix the collision
is caught by `noteInterface`'s conflict record and refused by name in `emitProgram`
(`interface wire name registered with two different method sets: interface{Get() inner.T}
(interface{Get() red/inner.T} vs interface{Get() blue/inner.T})`) — fail-closed, never a wrong
answer, but the row is RED. Pinned by `multipkg/same-name-anon-iface` (gc `1 4 true false`; the
frontend refuses at `frontend-export`; the raft-W1.1 `multipkg/same-name-identity` twin (2026-08-18) already
pins the NAMED-type half of the same hazard, green since BUG-010). Root cause: FRONTEND (wire
identity), not the machine — the machine answers exactly what the wire declares.

PLAN [AGENT]: pass `e.pkgQualifier` as the qualifier at BOTH sites (they must stay byte-identical
spellings of one name — `emitType` for type positions, `ifaceWireName` for dispatch sites), so
the anonymous name is path-keyed like every named TypeId (`interface{Get() red/inner.T}`); the
key-grammar guard (`checkKeyPathGrammar`) already covers dotted paths reaching a qualifier.
Single-package wires are byte-identical (path == name for `main`); wires mentioning a
sub-path package's type inside an anonymous interface's method signature (`math/rand`,
`internal/abi`) change their anonymous TypeIds — an identity change, invisible to the
observable unless the name reaches a panic text. THAT is the one design question to settle
first: `Ops.lean` `goTypeNameForMessage` prints an `.interface name` by its key, so a
path-qualified anonymous name prints `interface{Get() red/inner.T}` where gc prints
`interface { Get() inner.T }` — the display/identity split BUG-059 already records for
`.defined` keys (`multipkg/same-name-identity-panic`); the fix should land under BUG-059's
display rule (identity by path on the wire, rendering by name in messages), not invent a
second one. Not fixed in the audit fix round: a two-site one-liner, but its blast radius
(every anonymous TypeId over a sub-path package) needs its own full run and the BUG-059
rendering decision — recorded, rowed, red. Ledger: FR-13's structural-TypeId row is the
neighbouring frontier (anonymous STRUCT types); this entry keeps the anonymous-INTERFACE
identity defect on its own line since it is a wrong-answer class, not a coverage gap.

## BUG-098 — UNEXPORTED interface method names are package-scoped in Go but BARE on the wire: a requirement `get` declared in one package would be judged satisfied by a concrete `get` from another — a wrong satisfaction answer, refused whole-export by a guard until the names are qualified [fidelity; frontend + machine identity; multipkg; found by the fr19-bug097 gc probes (P3/P5)]

- Status: open
- Pinned-by: none (all rows are RED BY DESIGN at frontend-export: the guard `checkUnexportedMethodScopes` (identity.go) refuses `unexported interface method name(s) shared across packages: get (required by blue/inner, implemented in red/inner); get (required by red/inner, implemented in blue/inner) …`; nothing on the wire answers) [AGENT]
- Expect: FAIL
- Cases: multipkg/unexported-method-scope/assert-panic, multipkg/unexported-method-scope/distinct, multipkg/unexported-method-scope/distinct-names
- Discovered: 2026-09-05 (lane `fr19-bug097`, gc probe P3: `types.TypeString` never qualifies unexported interface METHOD names, even with a qualifier — so BUG-097's planned one-liner would have left this fusion class; P5: gc answers `true false` for red's `interface{ get() int }` vs blue's on a red value)

WHAT (spec#Type_identity: two interface types are identical iff they have the same
set of methods with the same names and identical signatures, where NON-EXPORTED
method names must originate in the same package; spec#Uniqueness_of_identifiers /
spec#Exported_identifiers): `red/inner.T`'s method `get` is `red/inner.get`, not
`blue/inner.get`, so red's `T` does NOT implement blue's `interface{ get() int }`
(gc probe P5: `ri.IsGet(x), bi.IsGet(x)` = `true false`; the failed assert says
`interface conversion: inner.T is not interface { inner.get() int }: missing method
get`). The wire's requirement lists (`MethodSig.name`), method tables
(`MethodInfo.name`) and dispatch anchors (`<Iface>.<method>`) carry BARE method
names, and the machine matches requirements to concrete methods by that bare name
— so once the two anonymous interfaces are distinct KEYS (BUG-097's fix) the
machine answers `true true`: a WRONG ANSWER. What main did BEFORE this lane
depends on the shape (corrected at the audit fix round R4, 2026-09-05 [AGENT] —
the first record said "main REFUSED by accident" as if for the whole class):
* SAME-NAME packages (`red/inner`, `blue/inner`, both named `inner`): main
  refused by accident — the two anonymous interfaces fused onto one key and
  BUG-095's conflict guard killed the export.
* DISTINCT-NAME packages: main ANSWERS WRONG today. Measured by the [AGENT
  audit, 2026-09-05]: `type S struct{ emb.E }` (package `emb` declares
  `func (E) get() int`) against main's `type J interface{ get() int }` — gc
  `false` (S's promoted `get` is `emb.get`, not `main.get`), main `true`; the
  same for a main-vs-package pair. Nothing fused, so nothing tripped: the bare
  name matched. Pinned by `multipkg/unexported-method-scope/distinct-names`
  (red by design under the guard).
So the branch does not "turn a refusal into a refusal": it converts a
PRE-EXISTING SILENT WRONG-ANSWER class into a named refusal, and keeps the
same-name shape's accidental refusal as a deliberate one.

GUARD (2026-09-05, this lane [AGENT], fail closed): `emitProgram` refuses the WHOLE
export when an unexported requirement name declared in source package P has a
concrete method of that name declared in a DIFFERENT source package Q
(`noteInterface` records requirement names → declaring paths;
`checkUnexportedMethodScopes` walks every unit's `Defs` for unexported methods)
— the only shape on which bare-name tables can answer wrong. Single-package
programs never trip it (P == Q); promoted methods keep their declaring package,
so a struct embedding another package's type satisfying THAT package's
interface is not flagged. Static twin in `tools/lowerdiag`
(`unexported-method-scope`, FR-31). MEASURED on cedar-go
(`docs/2026-09-03_cedar-go-coverage-census.md` §13; narration corrected at the
audit fix round R17): the hazard is SYMMETRIC — `x/exp/schema/ast` and
`x/exp/schema/resolved` EACH declare an `isType` requirement (`IsType`
interfaces) and each implements `isType` on its own types, so the guard names
both directions (`isType (required by …/ast, implemented in …/resolved); isType
(required by …/resolved, implemented in …/ast)`) and kills BOTH packages on
their own (17 declarations: 9 `ast` + 7 `resolved` methods + the 2 interface
declarations); 6 more packages inherit the kill (8 of 24 in total, own or
inherited). The census had counted all of it as lowering: that count was a
LATENT WRONG-ANSWER class, now an honest red. The guard is a GUARD, not the
fix ([AGENT] judgement, design note §2.5/§7): the fix is frontend-wide in a file
two parallel lanes are editing, so it is rowed (FR-31) and sequenced after them.

PLAN (FR-31, ledger §4 / queue 31) [AGENT]: qualify unexported method names by declaring
package PATH wherever the wire carries a matching name — `MethodSig.name`,
`MethodInfo.name`, the interface dispatch anchors and `calledIfaceMethods` keys,
method-value/expression emission — leaving FuncIds (`<recv TypeId>.<name>`, whose
receiver already carries the path) untouched; the machine's `missing method`
text renders the bare name (display, like TypeIds). Frontend-wide but mechanical
(one `methodWireName(*types.Func)` helper at every `"name":` site of a method
entry); sequenced after the parallel emit.go lanes land. Fix criterion: all
three Cases rows PASS (`true false`; the gc text above; `false` for the
distinct-names shape), the guard retires, the cedar-go `ast`/`resolved`
exports revive.

## BUG-099 — a RECOVERED runtime error's dynamic type is one synthetic id (`$runtime.Error`) where gc has a concrete type per fault: the observation channel names it `Error` (gc `boundsError`) and carries a string payload (gc a struct) — a wrong observation; the concrete-target assert text REFUSES by name [fidelity; machine runtime-error payload model; found by the fr19-bug097 audit (R3/R20) and measured at its fix round]

- Status: open
- Pinned-by: differential
- Cases: panic-recover/recovered-runtime-error-type/observed, panic-recover/recovered-runtime-error-type/assert-int
- Discovered: 2026-09-05 (lane `fr19-bug097` adversarial audit R3 — the `<TypeId $runtime.Error has no display record>` marker inside a `recover(); r.(error).Error()` refusal disproved the design note's "unreachable" — and R20 — `Ty.dynamicName` passes the synthetic key to the observation channel; the wrong observation measured at the fix round: `docs/evidence/2026-09-05_fr19-bug097/gc-probe-r3-recovered-runtime-error.go`, transcript in the evidence README)

WHAT: gc's runtime panics carry CONCRETE types — an index fault is
`runtime.boundsError` (a struct `{x int64; y int; signed bool; code
boundsErrorCode}`), a nil dereference `runtime.errorString`, a failed type
assertion `*runtime.TypeAssertionError`, an integer divide `runtime.runtimeError`
— each with `Error()` (and `RuntimeError()`). The machine mints ONE synthetic
`TypeId` for every runtime fault, `$runtime.Error` (`GoLean/GoCore/Syntax.lean`
`runtimeErrorTypeId`), boxing the MESSAGE STRING as the payload
(`Machine.lean` `runtimeErrorValue`). Two channels expose the difference:
* the OBSERVATION channel — `recoveredRuntimeErrorAsAny` returns the recovered
  value as `any`: gc observes `{"dynamic":"boundsError","value":{"tag":"struct",
  "typeName":"boundsError","fields":[x=3,y=0,signed=false,code=0]}}`; the machine
  observes `{"dynamic":"Error","value":{"tag":"string",…"runtime error: index out
  of range [3] with length 0"}}` (`TypeId.unqualified` of `$runtime.Error`) — a
  WRONG ANSWER at the differential stage (row `observed`, FAIL/differential).
* a CONCRETE-TARGET assert's panic text — `r.(int)` on the recovered value: gc
  `interface conversion: interface {} is runtime.boundsError, not int`; the
  machine REFUSES by name since the audit fix round R3 (`typeAssertPanicMessage`:
  «names the dynamic type of a recovered runtime error, which the machine models
  as one synthetic id … no byte-exact text exists») — before it, the text carried
  the display marker (row `assert-int`, FAIL/lean-observation, a designed red).
  The interface-target forms (`r.(error)`, `r.(fmt.Stringer)`) already refused on
  the missing method-set record (BUG-009/BUG-053 class), the marker
  `runtimeErrorDisplayMarker` now naming the cause inside that refusal text.
Root cause: MACHINE (payload model), not the frontend — the wire never spells
`$runtime.Error`; the decoder synthesizes it for the nil-interface method-value
check and the machine for every runtime fault.

PLAN [AGENT]: model gc's concrete runtime-error types — a per-fault `TypeId`
(`runtime.boundsError`, `runtime.errorString`, `runtime.runtimeError`,
`*runtime.TypeAssertionError`, …) with the display record `runtime.<T>` /
`*runtime.TypeAssertionError`, pkg `runtime`, a method-set record (`Error`,
`RuntimeError`; `exported` coverage suffices — both names are exported), and a
payload VALUE shaped as gc's (the `boundsError` fields are what the observation
channel compares; `errorString`'s is the string). The `Error()` text stays the
message the machine already computes. Then `r.(error)` answers (BUG-009/BUG-053's
runtime-error face closes), the assert text renders, and both rows flip PASS.
Scope: `Machine.lean` panic sites (`panicEntry`/`deliver`), `Syntax.lean`
(`runtimeErrorTypeId` → a small closed table), `renderPanicPayload`'s
`runtimeErrorTypeId` arms, `NativeToIR.lean:818`. Not a frontend change; not this
lane's slice (a machine-model arc with its own probes of every fault's concrete
type). Fix criterion: both Cases rows PASS; the `$runtime.Error` id is gone.

## BUG-100 — C6 DESIGNED RED, pinned: a function-local defined type as a generic TYPE's argument (`box[score]`) refuses by name — gc's observable instantiation name embeds the compiler counter `decl.gen`, a ratified impossibility (ledger §5.1 item 1), not a bug [coverage; (c)-pin; the entry exists so the refusal cannot stop firing unnoticed]

- Status: open
- Pinned-by: none (the row is RED BY DESIGN at frontend-export: mono.go's C6 refusal `function-local defined type main.score as a type argument …`; `tools/lowerdiag/causes.tsv` `local-type-type-argument`) [AGENT]
- Expect: FAIL
- Cases: scoping/local-type-identity/type-instantiation-refused
- Discovered: 2026-09-05 (lane `fr19-bug097` design note §2.2/§2.4 narrowed C6 to this shape and born the pin; the adversarial audit R19 found the pin on NO `Cases:` line — nothing would have tripped had the refusal stopped firing)

WHAT (not a defect — the record of a ratified impossibility, in the form the
gate can enforce): gc names the instantiated type `main.box[main.score·N]` (`%T`,
a failed assert's text) with `N` = `decl.gen`, a per-package compiler counter
(`noder/writer.go:1013`; probe P4: `score·1`, `other·2`, `score·3`) that is not a
function of anything the language defines; the machine's scope ordinal is
source-order and deliberately NOT gc's counter (design note §7). The
FUNCTION-instantiation shape (`cmp.Compare[index]`) is ADMITTED — a FuncId is
never a gc text (BUG-092 closed on it). This entry uses the repo's mechanism for
a red-by-design pin (BUG-093/BUG-094 precedent; check-bugs `Expect: FAIL`): a
`Pinned-by: none` entry whose Cases must stay FAIL, so the pin trips the gate if
the refusal stops firing or the row stops pinning it. There is no ledger-backed
check for (c)-pins (`scripts/` reads only BUGS.md `Cases:` lines), and the
`Status: fixed` differential entries that narrate C6 (BUG-092, BUG-018) cannot
carry a FAIL row (check-bugs (3)). Retires only with a [USER] re-ruling of §5.1
item 1 — never by a fix.

## BUG-101 — the VALUE observable of a spec-unsequenced operand reached through the E13 (b) probe: a type assertion that SUCCEEDS early and FAILS late (`iv.(int) + len(b[j:]) + func() int { iv = "s"; return 1 }()`) — gc evaluates the assertion first (value 6), the machine's probe evaluates it early too but DISCARDS the value and the residual re-evaluation after the mutating call panics [latitude E12's known divergence, now reachable through the shape the retired A6 guard used to refuse; frontend/machine evaluation order]

- Status: open ([AGENT], e13-b audit fix round 2026-09-05 — audit finding R1, value axis)
- Pinned-by: differential
- Cases: builtins/e13-sibling-panic-order/assert-ok-early-len-hoist, builtins/e13-sibling-panic-order/slice-value-early-len-hoist

THE CLASS (re-audit fix round R1'-7, 2026-09-05, [AGENT]): every
EARLY-realized probe kind — the operand kinds gc evaluates BEFORE the
sibling calls (type assertion, slice expression; interface comparison
measured to MATCH: `(jv == jv)` reads no mutable index, `h3`/`h4` in the
re-audit probes) — whose early evaluation SUCCEEDS while a sibling call
mutates what it reads: the probe discards the early value, the residual
re-reads after the mutation. Second row, the slice instance: `n = a[i:][0]
+ len(b[j:]) + mut()` with `mut` setting `i = 1` — gc prints `mut` then
`12` (the slice taken before the call), the machine `mut` then `22`; it
was REFUSED at b77f3298 (the whole A6 guard), lowers since the lane tip.
Index/dereference/division/shift/conversion operands are LATE in gc and
agree with the machine's residual re-evaluation (`h1`, `m1`, `m2`).

WHAT: `Stmt.unseqProbe` (E13 option (b)) evaluates a panicky non-call
operand at its lexical position and, when the evaluation YIELDS A VALUE,
discards it — the operand is re-evaluated at its residual position after
the sibling ordered events (design §3: the probe is the PANIC-axis
mechanism; the value axis is E12's (b) call-first pin). When a sibling
call MUTATES what the operand reads, the two evaluations differ: with
`iv` holding 3, gc realizes `iv.(int)` EARLY (order.go's safe-expression
rule for `ODOTTYPE`) and prints `mut` then `6`; the machine's early
evaluation succeeds and is dropped, the closure sets `iv = "s"`, and the
residual `iv.(int)` panics `interface conversion: interface {} is string,
not int` — on EVERY stream (the probe consults only on an early PANIC, and
here none occurs). Observed (gc) ∉ modeled: a lower-bound violation on
this shape, deterministic. It is E12's recorded divergence (`a[i] + f()`
with `f` repairing `i`: the operand's value read early vs late across a
mutating call — E12 (b) pins call-first and carries the re-envelope
obligation) reached through the `len` shape the whole A6 guard used to
REFUSE (`iv.(int) + len(b[j:]) + f()` was `unsupported` at b77f3298 —
BUG-032's guard, blind to whether the left material is probed); the
e13-b retirement lowers it, so the E12 divergence is now reachable
where a refusal stood. The auditor's twin witness WITHOUT a len
(`iv.(int) + func() int { iv = "s"; return 1 }()`) was never refused —
E12's territory on main all along (the `assert-vs-mutating-call` row's
PANIC-status sibling: there iv starts as a string and both members are
certified; here it starts as an int and the machine has one member, not
gc's).

WHY NOT REFUSED: whether the early evaluation succeeds (and the late one
fails) is a RUN-TIME fact — the same syntax with `iv` holding a string is
the certified two-member membership row `assert-vs-mutating-call`. A
static guard would have to refuse every probed operand beside a call
that MAY mutate its inputs (any call, absent an effect analysis) — the
ordinary `a[i] + f()` idiom class, option (a) of E13's four-way
treatment, rejected by the [USER] ruling (relayed). So: rowed, not
guessed — red-first rows with gc's value pinned, red by design until the
value axis is enveloped. THE STAGES, per row (final verification fix
round R''-9, [AGENT]): `assert-ok-early-len-hoist` FAILS at stage
`lean-observation` (gc `ok`, value 6, output `mut`; the machine PANICS —
a status mismatch surfaces at the machine-observation stage, before the
differential compare), `slice-value-early-len-hoist` at stage
`differential` (both `ok`; 12 vs 22). `Pinned-by: differential` above is
`check-bugs.sh`'s vocabulary (a Go-vs-Lean fidelity red at a fidelity
stage, as opposed to `none`; the field admits only those two tokens), not
the row's stage name — the baseline header and the rows carry the stage.

FIX DIRECTION (E12's obligation, not this lane's): realize BOTH values —
the probe would have to CARRY its early value into the residual (a
"value-or-not-yet" pick on the value path, consulted only when the two
evaluations could differ, i.e. when a sibling event intervenes), which
is a second choice site on the VALUE axis with a bound that is not
data-dependent in the E13 way (the pick is needed even when nothing
panics) — exactly the re-index E13's design §7 avoided and the design
gate the brief names. Inventory E12 carries the note; §6 residual 2 of
the e13-b design cross-references this entry.

## BUG-102 — DESIGNED REDS of the E13 (b) envelope's BOUNDARY, as moved by the re-audit fix round: the structural-allocation class (a `&T{…}`/slice literal or an interface method value whose PANICKY payload precedes an ordered call/receive — in return-, println- and sink-rooted spellings) and the narrowed A6 guard's residue (a compound target that CONTAINS A CALL beside a hoisted len) refuse by name [coverage; frontend hoist/guard surface; e13-b audit fix round R1/R2 + re-audit fix round R1'-1..R1'-4, R2'-1; the entry exists so the refusals cannot stop firing unnoticed]

- Status: open (designed reds — a refusal standing in for latitude, inventory E6 narrowed / E13 residuals 3 and 5; [AGENT], e13-b audit fix round 2026-09-05; Cases line re-derived at the re-audit fix round the same day)
- Pinned-by: none
- Expect: FAIL
- Cases: builtins/e13-sibling-panic-order/composite-ptr-payload-vs-call, builtins/e13-sibling-panic-order/slice-lit-payload-vs-call, builtins/e13-sibling-panic-order/composite-ptr-payload-vs-call-printroot, builtins/e13-sibling-panic-order/slice-lit-payload-vs-call-sinkroot, builtins/e13-sibling-panic-order/slice-lit-payload-vs-recv, builtins/e13-sibling-panic-order/compound-call-target-vs-len

HISTORY (the first fix round's six rows, RETIRED at the re-audit fix
round): `tgt-assert-vs-len-hoist`, `tgt-assert-vs-make`,
`compound-assert-vs-len`, `map-key-assert-vs-len`, `recover-assert-vs-
len`, `bytes-conv-left-len-hoist` were red by design here because the
first fix round SUPPRESSED probing on every assignment target (design §4
D4 as first written) and never probed a `recover()`-bearing or
allocating-conversion-bearing operand, so the narrowed A6 guard refused
a len/cap/make hoist beside them. The re-audit (2026-09-05) found that
spec#Assignment_statements phase 1 makes a target's index/deref OPERANDS siblings
of the RHS's calls — unsequenced, gc raising the assertion FIRST — so the
suppression had PINNED the events-first member (`m[iv.(string)] =
wit(5)`: two members with gc's in the set at b2fd9f15, ONE member
without at d75049c0 — a regression, R1'-1). The re-audit fix round
probes phase-1 target operands (the target's own index/deref/map-write
check is the phase-2 STORE's and is exempt from the census), address-of
operands (`&a[i]`/`&p.f` — bounds-/nil-checking address computations),
array-of-array target bases, the hoisted `recover()`'s residual (`$c :=
recover()` is an ordered event the emitter already hoisted; `$c.(int)`
is pure — R1'-4) and a HOISTED allocating conversion (`[]byte(s)` hoists
to a temp when an ordered event follows it; its residual `$b[1:7][0]` is
pure — R1'-3); the six rows lower as membership sets (one a singleton)
and sit on BUG-083's Cases line with the reason.

WHAT REMAINS (spec#Order_of_evaluation, the OMISSION: a literal's
payload and a compound target's read are not calls, so their order
against a sibling call/receive is unspecified — latitude E13/E2's
territory; the machine realizes ONE member where gc realizes the OTHER,
and no probe reaches gc's member):

THE STRUCTURAL-ALLOCATION CLASS (audit R2; re-audit R1'-3/R2'-1): a
composite-literal `&T{…}` / elided `&T`, a slice literal, or an interface
method value hoists to its lexical position and evaluates its payload
THERE, ahead of every ordered event lexically after it, while
gc leaves the literal in the residual after the call temps — `(&T{x:
s[i]}).x + wit(5)`: gc prints `wit 5` then panics, the machine panics
with no output on every stream (a probe on `s[i]` cannot reach gc's
member: the allocation statement re-raises a deferred panic at the same
early position — disposition (a) measured and rejected); with a RECEIVE
as the event gc receives first (`[]int{s[i]}[0] + <-ch`, witness
`len(ch)` = 0 after recovery). Pre-existing on main. `structuralAllocGuard`
refuses by name when the payload is panicky and
`sweepOrderedEventAfter(lit.End())`, in the return-rooted spelling and
— since the re-audit's census fix (R1'-3: a call that ENCLOSES the
hoisting construct is descended, not pruned) — the println-/sink-rooted
spellings too. An ALLOCATING CONVERSION whose own operand can panic
(`[]byte(s[i:j])`) is NOT this class: it stays inline and its operand's
probe realizes both orders (`bytes-conv-payload-vs-call`, a membership
row). NOT refused (controls, green): a MAP literal (gc's
order.go `OMAPLIT` emits its dynamic entries as statements at the
literal's position — the machine's member IS gc's, `map-lit-payload-vs-
call`), a literal inside the ARGUMENT subtree of an ordered call that
precedes the next event (forced: `composite-ptr-in-arg-then-call`, R2'-1
— the first fix round over-refused it), the no-event / event-inside-
the-literal / variadic-pack shapes.

THE NARROWED A6 GUARD'S RESIDUE: a compound/IncDec target that CONTAINS
A CALL (`x[fnine()] += len(b[j]) + wit(5)`) — `emitReadWriteTarget`
hoists its ADDRESS to a temp (`$p := &x[$f]`), so its bounds check is
unprobed material left of the len hoist: refused by name (the guard is
wired at the len/cap/min/max hoists and the unconditional make/append/
copy hoists — R1'-2). Its no-len sibling `x[fnine()] += wit(5)` LOWERS
and is ∉ gc: BUG-104 (open, differential).

WHY AN ENTRY: BUG-032 and BUG-083 are `fixed` and the check-bugs
invariant requires their Cases lines to be PASS-only; these six rows
are red BY DESIGN and must trip the gate if the refusal ever stops
firing (a designed red that turns green is a retirement that skipped its
record — the BUG-093 mold). `tools/lowerdiag` causes
`len-hoist-panic-order` and `alloc-payload-panic-order` classify the
texts; ledger FR-28 (CLOSED for probed material, REOPENED NARROWED — the
narrowing itself narrowed at the re-audit); inventory E6 (narrowed, in
§5) and E13 residuals 3/5; design `docs/2026-09-05_e13-b-design.md` §4
D5/D6. RETIREMENT PATH: for the structural class, a lowering that
evaluates a literal's panicky payload in the RESIDUAL (gc's member) —
or a probe shape that can defer an allocation's payload; for the
compound-call residue, BUG-104's fix (a decomposed target — base and
index temps, the bounds check in the residual). Each retirement flips
its rows green and must move them to a `fixed` entry's Cases line with
the reason written, as the six above did.

## BUG-103 — conversions whose TARGET's resolved shape is an ARRAY (`Raw(cs)` between two defined `[3]Code` types, `[3]Code(r)` to the unnamed array type) are refused by `convertValueToTy`'s catch-all — BUG-020 added the pointer/slice/map/func arms and left the array arm out [coverage; GoCore conversions; fail-closed refusal of legal Go; surfaced by the C-arc C2 audit fix round (R11 rows), 2026-09-05]

- Status: open
- Pinned-by: differential
- Cases: structs/decl-order-reversed/conversion-array-target

WHAT (spec#Conversions: a non-constant value `x` can be converted to `T` when `x`'s type
and `T` have identical underlying types — `Codes`, `Raw` and `[3]Code` all have underlying
type `[3]Code`, so both `Raw(cs)` and `[3]Code(r)` are legal and are the identity on the
value): `GoLean/GoCore/Ops.lean` `convertValueToTy` matches the target's `TypeEnv.resolve`d
body against the value and has arms for `.plain (.int _)`, `.plain (.float _)`, `.plain
.string`, `.plain (.pointer/.slice/.map/.funcType …)` (BUG-020), `.struct`, `.opaque`,
`.interfaceDecl`; a `.plain (.array n elem)` target falls to the catch-all —
`unsupported "conversion to GoLean.GoCore.Ty.array 3 (GoLean.GoCore.Ty.defined 2)"` — at
the FIRST array-shaped conversion (`Raw(cs)` here; the wire elides nothing). Fail-closed,
never a wrong answer; gc returns `104`, the machine refuses at `lean-observation`. Detected
[AGENT] while writing the C2 order-coverage rows (`structs/decl-order-reversed/`, audit fix
R11): the row was meant to exercise the defined-over-array edge through a conversion and
found the arm missing. Root cause: the MACHINE (a missing kernel arm), not the frontend or
the type table — the same class as BUG-020, one target kind further. Per the [USER]
2026-09-03 direction (every detected gap is rowed at detection), the row is pinned RED-FIRST
here rather than rewritten to avoid the shape; the PASS half of the same story is
`structs/decl-order-reversed/defined-array-values` (defined array values built, copied,
compared and indexed without a conversion).

PLAN [AGENT]: one arm — `| .ok (.plain (.array n elem)), .array values => normalizeValueForTy
state (.array n elem) (.array values)` — legal exactly when go/types accepted the conversion
(identical underlying types), and the machine's `.array` carries no type tag, so the
conversion is a COPY normalized at the target's element type (arrays are values; the
normalization re-checks length `n` and every element at `elem`, refusing a malformed value
by name as every other arm does). Needs its own slice with a full run: the arm is reached by
every array-shaped conversion in the corpus (the `BUG-020` fix's `structs/unnamed-conversion-targets/*`
rows are the template: red-first, then the arm, then PASS on this Cases line). Ledger:
`docs/language-coverage-ledger.md` §2 Conversions row names it.

## BUG-104 — a compound-assignment target whose ADDRESS or KEY is hoisted to a temp panics at the hoist, BEFORE the RHS's ordered events (calls, receives, method calls); gc reads the target in the residual, AFTER them (`x[f()] += wit(5)`: gc `f`, `wit 5`, then `index out of range [9]`; the machine `f` then the panic — `m[t[k]] += wit(5)`: gc `wit 5` then `[5] with length 1`, the machine the panic alone — `x[f()] += <-ch`: gc receives first, the machine panics first) [frontend lowering; evaluation order; spec#Assignment_statements phase 1 vs the eval-once rewrite]

- Status: open ([AGENT], e13-b re-audit fix round 2026-09-05 — found by the re-audit's measurements, pre-existing on main b77f3298; three more spellings rowed at the final verification fix round the same day, R''-2)
  Round-17 rebase note ([AGENT] reconciler, 2026-09-05): the renumber the Status line describes was applied at the rebase of the lane's re-audit commit itself (main's BUG-103, c-arc-c2's array-conversion entry, landed at this train before this lane), so no rebased commit ever carried two BUG-103 headings.
- Pinned-by: differential
- Cases: builtins/e13-sibling-panic-order/compound-call-target-vs-call, builtins/e13-sibling-panic-order/map-compound-index-key-vs-call, builtins/e13-sibling-panic-order/compound-call-target-vs-recv, builtins/e13-sibling-panic-order/map-compound-index-key-vs-recv, builtins/e13-sibling-panic-order/map-compound-index-key-vs-method

MERGE-TRAIN NOTE ([AGENT], 2026-09-05, final verification fix round): this
entry was filed on lane `e13-b` under the NEXT free number at the time,
103. Branch `c-arc-c2` filed its own entry under 103 and merges ahead of
this branch (lane `fr19-bug097` holds 100; BUG-101/BUG-102 are this
branch's alone), so the entry is RENUMBERED to BUG-104 here, before the
merge, to keep the index's ids unique — every record on this branch
(corpus comments, baseline header, doctrine, inventory, design, evidence,
ledger) says BUG-104, and no record on the branch spells the former id
(a train-side grep for c2's id finds nothing here; the number is c2's).

WHAT: `x op= y` evaluates `x` once (spec#Assignment_statements). Two
lowering paths realize the "once" by hoisting a TEMP at the target's
lexical position, ahead of the RHS's hoisted ORDERED EVENTS — a call, a
receive, a method call (the class is every ordered event the RHS carries,
not calls alone: final verification fix round R''-2): `emitReadWriteTarget`
when the target CONTAINS A CALL (`x[f()]` → `$f := f(); $p := &x[$f]` —
the `index-addr` bounds-checks at that hoist, Machine.lean
`indexTargetLoc`), and `emitMapCompound` for every map target (`m[t[k]]`
→ `$m := m; $k := t[k]`). gc's `order.go` `safeExpr` saves the target's
OPERANDS (base, index/key VALUE — `t[k]`'s operands, not `t[k]`) to temps
and leaves the index/read node in the RESIDUAL, so its bounds check fires
after the RHS's event temps: `f`, `wit 5`, then the panic; the machine
panics before `wit 5` on every stream. Observed (gc) ∉ modeled: a
lower-bound violation, deterministic, on any compound target whose
hoisted temp can panic (a call-bearing slice/array index; a map key
that is itself a panicky index) beside ANY ordered event on the RHS.
The other spellings, measured at the final verification audit (R''-2)
and rowed red-first with gc's output pinned: a RECEIVE as the event —
`x[f()] += <-ch` (gc `f`, then the receive — witness `len(ch)` 0 after
recovery — then the index panic; the machine `f` then the panic before
the receive, witness 1: `compound-call-target-vs-recv`) and `m[t[k]] +=
<-ch` (gc receives first, witness 0; the machine's hoisted key temp
panics first, witness 1: `map-compound-index-key-vs-recv`); a METHOD
CALL as the event — `m[t[k]] += q.M()` (gc `M` then the panic; the
machine the panic alone: `map-compound-index-key-vs-method`). The map
path's `probeSuppress` in `emitMapCompound` (held across the target's
base and key) is the one UNFORCED suppression in the frontend (design §4
D4; its every other site is spec-forced) — it does not cause the bug
(the hoisted temp is not an inline operand either way) but it is the
rule that goes with the fix. The spec orders neither (the target's read
is phase-1 material against the RHS's ordered events — E2/E13's
omission), so the fix is an ENVELOPE, not a pin. Inventory §10 lists this
entry on the known-≠-oracle list (added at the final verification fix
round, R''-1: an open observed-∉-modeled debt with a queue position, not
a pin). Pre-existing: measured at
b77f3298 with the re-audit probes (`P3_compound_call_index`,
`P23_mapcompound_index_call`); untouched by e13-b's probe (the hoisted
temp's panic is not an inline operand's — no probe hook fires) and by
the first fix round. The call-free compound target (`x[iv.(int)] +=
wit(5)`) is NOT this bug: it is read inline and probed (`compound-
assert-vs-len`, `compound-index-vs-len` — two members, gc's in the set).

FIX DIRECTION: decompose the target the way gc's `safeExpr` does —
temps for the base and the index/key VALUE (`$b := x; $i := f()` /
`$m := m; $kk := k`), the indexing/read itself left in the residual
(`$b[$i] = $b[$i] + $w`, `$m[$t[$kk]]`) — so the bounds check is inline
material the E13 probe covers, realizing both orders (for the map path
this also retires `emitMapCompound`'s unforced `probeSuppress`). Until
then the compound-call target beside a hoisted len refuses by name
(BUG-102's `compound-call-target-vs-len`) and these five rows are
red-first with gc's output pinned.
