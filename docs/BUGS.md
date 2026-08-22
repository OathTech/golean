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

- Status: open
- Pinned-by: differential
- Cases: multipkg/same-name-identity-panic

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
> below is semantic-core work (the W3.2 lane's), and this red is
> "inclusion not yet checkable", never relaxed.

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
  reds by design.)
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
- Triage record: docs/goose-parity-parked.md P4.

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
  docs/goose-parity-buildout-log.md and ledger entry P3.

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

- Status: open
- Pinned-by: differential
- Cases: race/free/array-read-write
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
  projected field path (`fieldChainTarget`; covers `p.a` on struct
  locals and on `*struct`, green-pinned by
  `race/free/{field-read-write,ptr-field-read-write}`) — leaving
  exactly: value-path ARRAY-element reads (`a[1]`: the index operand
  is unevaluated when the base cell is read, so no continuation
  narrowing exists) and composite reads whose continuation is not a
  fieldGet chain. Over-refusal is the FAIL-CLOSED direction (a
  refusal, never a wrong value), recorded as O1 in
  `GoLean/GoCore/Race.lean`'s inventory.
- Fix shape: path-precise element reads need either provenance-carrying
  array values or frontend address-based element reads
  (indexAddr+deref, which the deref arm then narrows) — a frontend/
  machine movement with its own guardrails, not a detector patch.
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
  equality.)
- Pinned-by: none (the discriminating shape now fails closed at the
  frontend — channels/recv-order/dead-recv-len-operand is a permanent
  frontend-export refusal, tracked as coverage, not a fidelity pin)
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
  the first non-racy cross-goroutine shape. Kit obligations recorded
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
> CONFORM, and producing ours is semantic-core work owned by the
> W3.2 lane). No red was relaxed; the conversion completes when the
> member lands.
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
  (this figure said 46 while the family has 51 rows — five were added
  after the entry was written; re-counted 2026-08-22, launch audit D7)
  new package `spec-examples-decl/var-comma-ok-matrix/` walk the full
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

- Status: open
- Pinned-by: differential
- Cases: builtins/len-vs-call-order/chan, builtins/len-vs-call-order/slice, builtins/min-max-vs-call-order/min-value, builtins/min-max-vs-call-order/max-value, builtins/min-max-vs-call-order/min-arg-panic

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
docs/language-coverage-ledger.md).

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
  (slice 5) or a per-row ruling.
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
