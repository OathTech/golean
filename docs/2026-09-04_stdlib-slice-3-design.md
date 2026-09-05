# Stdlib slice 3 — `print`/`println` as machine built-ins with an output observable, plus the `float-bits` primitive (2026-09-04)

**Lane:** `stdlib-slice-3` (branch off `main` @ ac45aedd; rebased onto main
fc9bbef1 at merge train round 14, 2026-09-05 [AGENT] — the figures in
this note are the lane's own on ac45aedd unless marked; the rebased
tracked figure is in §8's last bullet). **Status:**
branch complete, gate PASS (§8), NO merge — the audit ask is the
coordinator's. **Provenance:** [AGENT] worker under three [USER]
rulings relayed by the [AGENT] coordinator (cited as relayed
throughout): stdlib gates G1–G9 as recommended («(3) agree, go ahead
with the plan»; G2 = «print/println as machine built-ins with a stderr
observable: admit with gc's pinned format for int/uint/bool/string,
refuse address-printing kinds and initially floats»); the `float-bits`
primitive («so the question is whether to add this as a primitive
language operation? This sounds reasonable, do it», 2026-09-04, with
the audit's condition: NaN payloads bit-exact, ±0 and quiet/signalling
probes); design gate G-OUT («Program output is a per-step EVENT
(`StepEvent.out`), folded by the driver into `Readout`, not a `Store`
field; `Obs.terminal` carries the stderr prefix»). Every decision
INSIDE those rulings is tagged [AGENT] in §7 and disclosed.

Reads first: memo `docs/2026-09-03_stdlib-boundary-design.md` §4/§5
(G2, G8), plan `docs/2026-09-04_reasoning-surface-plan.md` §1.5/§4.1
(G-OUT), register `docs/stdlib-admission-register.md` (slice log
2026-09-04), latitude inventory rows R7 (amended), R17, R18, ledger §2
Bootstrapping / §4 FR-29 / §5.1 item 3, BUGS.md BUG-093..096, evidence
`docs/evidence/2026-09-04_stdlib-slice-3/`.

## 0. What landed, in one paragraph

Two library-origin machine ops fill the register's primitive class
(0/2 → 2/2). **`float-bits`**: `math.Float64bits`/`Float64frombits`/
`Float32bits`/`Float32frombits` as one strict expression op with a
direction/width tag — the identity on the machine's float
representation (a float IS its bit pattern), so payloads round-trip
bit-exact by construction; one fail-closed arm (the canonical NaN, R7).
**`print`/`println`**: the `Stmt.print` wide statement whose apply step
validates the operands against gc's printable kinds and changes no
state; its bytes are the pool layer's OUTPUT EVENT (`StepEvent.out`),
folded by the driver in step order into `Readout.output` / the
terminal's prefix (`RunResult`), and emitted as the new `output`
observation field on every observation — compared byte-exactly against
gc's fd 2, which the coverage harness now captures separately and
splits fail-closed. 20 green rows, 14 designed reds (BUG-093/094), 120
of the 195 formerly print-refused `$GOROOT/test` files now MATCH with
their output compared, and the observable surfaced two real model bugs
(BUG-095 interface embedding in type switches, BUG-096 huge shift
counts) that the status-only comparison had hidden.

## 1. Output as an event — the G-OUT realization

**Where the bytes live: nowhere in the state.** `StepEvent` (Multi.lean)
gains `out : List GoString := []`. A `print` apply step emits one
element; every other step emits none. `stepThread`'s ordinary-step arm
derives it from the PRE-configuration with `printOut? : Config → Option
GoString` (Machine.lean): at `.retV v (.stmtOpK (.print nl) _ done [] _
_)` it renders `(v :: done).reverse` through the SAME `renderPrint` the
apply step validates through, so a successful step's event carries
exactly the validated bytes and a refusing step has no event. This is
the detector's own pattern (footprints classified from the
pre-configuration) and it keeps `stepFn`'s signature — and the hundreds
of pinned `stepFn` equations in MachineSound/StateWf — untouched:
the event channel stays at the pool layer, as the wave-3 scope note
already recorded for picks.

**The fold.** `execProgLoopOut : Nat → MultiConfig → RaceState →
Choices → GoString → GoString × Except Stop (ExecOutcome × Choices)` is
`execProgLoop` with the accumulator threaded (`ev.out.foldl
GoString.append acc` after every `stepMulti`) and returned on BOTH
paths — a Go terminal carries the bytes printed before it, exactly as
gc's stderr carries the prints before the `panic:` block. Theorem
`execProgLoopOut_snd : (execProgLoopOut fuel m r ch acc).2 =
execProgLoop fuel m r ch` pins the outcome component to the old driver
(same terminal-classification order, same L5 window, same detector
ride-along), so `execProgLoop_mono`/`_single`/`_unfold` and the
certificate checker's replay transfer unchanged. `runProgramPoolOutM`
returns `RunResult := Except (Stop × GoString) Readout` (`Readout` gains
`output : GoString := empty`); `runProgramPoolM` is its `(·.1)`
projection, so every existing test keeps its type.

**Who folds.** The CLI's `native-json-run` (through `runProgramPoolOutM`),
the per-stream enumerator `enumPoolRun` (an `acc` parameter), the
stepwise path enumerator `poolDFS`/`poolStepDFS` (a PATH-LOCAL `acc` —
two interleavings printing `ab`/`ba` are two members, R18), the tracer's
driver-agreement pin (`observationOfRunOut`). The dedup engine
(`EnumDedup.explore`) REFUSES by name any step with a non-empty `out`:
its nodes key on (pool, detector) and output is a trace — merging two
paths with different prefixes would lose a member; printing rows use
the default enumerator (row `goroutine-interleaving` does).

**Where it is NOT folded — refused, never dropped.** The `$pkginit`
phase runs on the sequential driver (`runConfig`), which has no event
channel; stepping through a print there would validate it and DROP its
bytes (a silent fail-open). `runPkgInitM` now runs `runInitConfig` —
`runConfig` plus `initPrintRefusal?` at every step — and the CLI's
three init mirrors (`enumInitRun`, `initDFS`, the tracer's `initLoop`)
carry the same guard. Row `builtins/print/in-init` is the designed red
(BUG-093; FR-29 iii). The Surface-layer sequential wrappers
(`execStmt`/`runConfig`/`stepFnIter`/`runProgramM`) keep their result
types and observe no output; no CLI subject runs on them.

**The observation.** `runJson`/`errorJson` (CLI.lean) emit `"output"` on
EVERY status (possibly `""`), so the comparator is total and an
old-shape observation without it fails the exact-key decode rather than
comparing; the schema tag stays `golean-observation-v1` ([AGENT]: the
memo's `v2` bump was proposed to make old/new non-confusable, and the
exact-key decoder already does that — one fewer string to move across
ten scripts and two baselines). Bytes are carried as a JSON string;
non-UTF-8 output is emitted as an object the decoder refuses BY NAME
(the harness refuses the same bytes on its side).

## 2. The `float-bits` primitive

`FloatBitsOp := f64bits | f64frombits | f32bits | f32frombits`;
`Expr.floatBits op e`; `StrictOp.floatBits op`; wire
`{"expr":"float-bits","op":…,"x":…}`; `floatBitsApply` (Ops.lean):
`*bits` of `.float bits kind` is `.int bits .uint64/.uint32`;
`*frombits` of `.int b .uint64/.uint32` is `.float (normalizeBits b)
kind`; any other operand kind is `stuck` (the frontend pins the
signatures: `emitFloatBitsCall` re-checks `math`'s declared param/result
kinds at every call and refuses on drift). Pure, total, structural;
`StateWf` arm `floatBitsApply_locSup` (the result carries no location);
the Step relation's generic strict-op rules cover it (no new rule).
Frontend: `isFloatBitsFunc` routes the four `math` package-level
functions (by `*types.Func` identity, methods excluded) in the
selector-call path right after the atomics hook; the node is a PURE op,
never hoisted. `math.Sqrt` and the rest of `math` keep their standing
by-name refusal (test `TestFloatBitsOtherMathMembersStillRefuse`).

**2.3 The canonical-NaN refusal ([AGENT], disclosed).** Latitude R7
narrows every NaN the machine PRODUCES to `0x7FF8000000000000`
(softfloat64.go's `return nan64`), on the argument that payloads are
unobservable in-language. This primitive makes them observable, and
gc/amd64 realizes different bits: `0xFFF8000000000000` for a runtime
0/0 (SSE "real indefinite"), and first-operand payload propagation
through arithmetic. Reporting the canonical pattern would be the
narrowing presenting as a wrong answer, so `*bits` REFUSES it by name —
under EITHER sign since the audit fix round A1 (2026-09-05): `fneg64` is
a bare sign flip, so the machine DOES produce the negated default
(`-(zero/zero)` = 0xFFF8…, where gc gives 0x7FF8…); the first cut's
exact-pattern guard REPORTED it — a wrong answer, closed. The
producible-NaN set is {default, −default} (and the 32-bit pair) —
`floatMinMaxBits` keeps it so (§2.4) — and every other pattern entered
through `*frombits` and passes bit-exact — which is what the audit's
condition asks for and rows `roundtrip-payloads` (9 of its 10 patterns:
`0x7FF8000000000001`, sNaN, ±0, ±Inf, subnormal min, finite max, 1.0 —
its 0xFFF8… entry refuses since A1, the row's PASS→FAIL flip),
`nan-semantics`, `float32` (quiet and signalling 32-bit payloads, −0f)
pin. The over-refusals (`Float64bits(Float64frombits(0x7FF8000000000000))`,
the −default round-trip) are rowed red (BUG-094: `canonical-nan-refused`,
`neg-canonical-refused{,/float32}`, `roundtrip-payloads`).

**2.4 `min`/`max` payloads (audit fix round A1).** gc/amd64 lowers float
`min` to `t1 = MINSD x y; t2 = MINSD t1 x; POR t1 t2` and `max` to
`-min(-x,-y)` (`AMD64.rules` @ go1.26.5): with a NaN operand the result
is the OR of both operands' bits — `Float64bits(min(Float64frombits
(0x7FF8000000000001), 2.5))` = 0x7FFC000000000001 — where the first cut
returned the NaN operand (0x7FF8000000000001): a wrong answer once
payloads were observable. `floatMinMaxBits` is now that idiom,
bit-probed (rows `min-max-payload{,/float32}`: both operand orders, ±0
ties, NaN/NaN, sNaN — green; the spec-example `min-max-float-specials`
pins unchanged), with ONE pre-check: if either operand is the default
NaN (either sign) the result is the default NaN, not the OR — gc's
default has the opposite sign, so the OR would carry a sign-wrong
pattern the `*bits` guard could not recognize (row
`min-max-canonical-refused` red). The pure-Go `runtime.fmin` of the
other ports returns the NaN operand: a (b)-pin to the oracle platform,
in R7's amendment. Alternatives rejected: (i) admit and let the mismatch stand —
a wrong answer at a forced point, against doctrine; (ii) make the
softfloat payload-faithful to x86 SSE now — a floats-design decision of
R4's class (platform-scoped), out of this slice's scope; recorded as
R7's live re-envelope obligation.

Register: primitive `float-bits`, 1 of 2. Anchor: `deps/go/src/math/
unsafe.go:21-41` @ go1.26.5 — a file:line citation, NOT the `godoc:`
grammar the brief named: `godocanchors` (gate G3) admits only packages
in the lowered-library pin manifest, and `math` is not source-through
([AGENT] deviation from the brief's spelling, disclosed; widening G3's
citable set to primitive-row packages would be a G3 amendment, posed in
§4, not taken).

## 3. `print`/`println`

**3.1 The pin (R17).** `renderPrintOperand`/`renderPrint` transcribe
`deps/go/src/runtime/print.go` @ go1.26.5: `printbool` (`true`/`false`),
`printint`/`printuint` (decimal; `-` for negatives; the KIND decides —
a defined type prints as its underlying kind, `print` never calls
methods), `printstring` (bytes verbatim); `println` = operands joined by
`printsp` (` `) + `printnl` (`\n`); `print` = concatenation. One
statement is one machine step, matching gc's per-statement
`printlock`/`printunlock` WITHIN a statement — but the machine switches
goroutines only at registry boundaries and back-edges, so a registry-free
run of several prints is atomic on the machine where gc may preempt
between them (audit fix round C1: R18's live obligation, ledger FR-30,
the `c1-probe` in the evidence dir; no strict or membership row over
that shape).
`Stmt.print (newline : Bool) (args : Array Expr)` rides the wide-
statement mold (`StmtOp.print`, `stmtPlan` with zero targets,
`applyStmtOpCore` = validate through `renderPrint`, state unchanged);
StateWf/MachineEqb/SyntaxEqb/NativeToIR arms; the Step relation's
generic wide-op rules cover it. Frontend `emitPrintStmt` admits exactly
bool / every integer kind / string (go/types has already recorded the
default type of untyped constant operands) and refuses everything else
at the call, per-function (H-3), naming the kind.

**3.2 Address-printing kinds — permanent.** Pointers, channels, maps,
funcs, slices (`[len/cap]0xaddr`), interfaces (`(0xtype,0xdata)`),
unsafe.Pointer: gc prints addresses the machine does not have and gc
does not keep stable across runs. Refused by name at the frontend
(`prints an address in gc …`); ledger §5.1 item 3 re-posed to say
exactly this; rows `builtins/print/refused/{pointer,nil-pointer,slice,
map,chan,func,interface}`.

**3.3 Floats and complex — refused THIS slice ([AGENT] call, disclosed).**
The brief allowed either transcribing gc's float printing "(~40 lines)"
or refusing and rowing. Measured: `printfloat64` is
`internal/strconv.AppendFloat(v, 'g', -1, 64)` — the SHORTEST
round-trip decimal, a Ryū-class `ftoa` with the `bigFtoa`/`roundShortest`
fallback, several hundred lines, and a go1.26 CHANGE (commit 9035f7ae
"runtime: use internal/strconv"; 1.25 printed `+1.500000e+000`). Not a
transcription this slice can take faithfully. Demand: 33 of the 195
gotest print files mention a float kind at all; 8 refused on a float
print operand in the re-run (§6); 3 print a decimal literal. The
faithful route is now UNBLOCKED by this very slice: source-through
`internal/strconv` (its deps.go casts are the `float-bits` primitive)
CALLED from the print arm — but "a machine op calling a library `Func`"
is a new shape needing its own argument. Refused by name, rowed
(`refused/float`, `refused/float32`), ledger FR-29 (i). Complex rides
floats (and refuses earlier at FR-15's type rule anyway).

**3.4 Init-phase prints — refused THIS slice ([AGENT]).** §1 above;
FR-29 (iii); 3 of the 195 files. Threading the fold through
`runPkgInitM`/`runProgramSetupM` and the four init mirrors is the fix;
not taken here.

**3.5 Zero-operand spellings — refused THIS slice ([AGENT]).** `print()`
writes nothing, `println()` writes `\n`; the wide-statement mold has no
nullary plan (A8, the dead `stmtOpNullary` rule was deliberately
deleted), and adding a dedicated `stepFn` arm would renumber all 102
`fun_cases` case tags in `stepFn_sound`. 2 of the 195 files. Refused at
the frontend AND the decoder (a hand-edited wire cannot reach an
unplanned statement). FR-29 (ii). The alternative — lowering `println()`
as `println("")` (byte-identical output) — is frontend text in the wire
and was not taken.

## 4. Owed / posed (not decided here)

- **EnumSpec `Obs` is still output-free.** The slow spec (`SlowObs` over
  `execProgLoop`) and `checkCert_slowObs` speak of values/terminals;
  output enters the EXECUTABLE driver and the CLI enumerators now.
  G-OUT's «`Obs.terminal` carries the stderr prefix» is realized at the
  driver's observation (`RunResult`'s error path) and in every emitted
  member JSON; the Prop-level `Obs` gains it when the C-arc re-homes
  `run` (plan §1.5) — with the dedup engine refusing printing rows, no
  certified set today contains an output-bearing member, so nothing is
  claimed that the theorem does not cover. [AGENT] scoping, disclosed.
- **G3 and primitive anchors.** `godoc:` covers source-through packages
  only; a primitive's doc comment lives in a package we do not lower.
  Posed: admit `godoc:` for packages named by the register's `primitive`
  rows (still resolved at the pinned rev). Until ruled, file:line.
- **R7 re-envelope** (BUG-094), **FR-29** (BUG-093), **BUG-095**
  (interface embedding in type-switch satisfaction — a real fidelity
  bug, three pins), **BUG-096** (huge shift counts abort the machine).
- **Race rows with program output** are not comparable (TSan's report
  interleaves asynchronously; the split requires an empty prefix and
  does not detect prints AFTER the report — rowed limitation:
  `builtins/print/refused/race-with-output`, FR-29 (iv), §5).
- **C1 / FR-30:** the machine's statement-level atomicity of registry-
  free print runs vs gc's preemption between statements (R18's
  obligation) — fix direction: a scheduling point between statements or
  an output-order latitude at the fold.
- **C9 (reconciler, MEDIUM):** the certified record's stamp precedes the
  branch's wire-schema commits (the enumeration ran before them; the
  `print`/`float-bits` nodes do not appear in the fixture, wire sha
  unchanged) — the merge train's standing step-5a re-certification at
  the merged tip clears it; disclosed, not re-stamped.
- **C15 (owed, reconciler):** a check for bare `R\d+` latitude citations
  resolving to a `### R\d+.` heading — this slice's first cut cited
  R17/R18 in eight places before the rows existed (A3). Recorded in
  TODO.md; not implemented here.

## 5. The harness split (apparatus, TRUST-ADJACENT)

`scripts/diff-coverage` builds `tools/coverageharness` ONCE per run
(`$OUT/bin/coverageharness`; it is now invoked twice per case) and
`go_run_oracle` captures the child's stdout and stderr to SEPARATE files
(`oracle.stdout` = the harness JSON on a green run, `oracle.stderr` = the
program's prints, then gc's abort report, then `go run`'s `exit status N`
trailer). `attach_output <status>` splices `"output":<literal>` into the
observation, the literal produced by `coverageharness --split-stderr F
--expected-status S` (`split.go`), FAIL-CLOSED: ok = whole stream (an
exit trailer refuses); panic = the ONE occurrence of `panic: ` anywhere
in the stream (repanic continuations `\n\tpanic: ` excepted), at a line
start, followed by gc's goroutine trace header — zero, several, glued or
header-less refuse by name (hardened at the audit fix round A2, which
found four shapes the first cut UNDERSTATED: a printed `panic: fake`
line or marker text glued to the report was taken as the block start);
fatal/deadlock = the one `fatal error: `/`panic: ` marker IN TOTAL (the
panic-then-fatal unwinding shape counts once); race = the prefix must
be empty; invalid UTF-8 refuses; `GOFLAGS` scrubbed on the oracle run
(C3: build chatter must never reach the compared channel). Red-first tests
(`split_test.go`, transcript in the evidence dir). The membership
sampler injects the same way; `scripts/gotest-triage` captures
separately too and its `.out`-golden files are now COMPARED (the
`output-uncompared` flag survives only for fd 1 — G7). Other scripts
that synthesize observations (`cedar-census`, `membership-sampling`,
`test-lane-validation`'s fakes, the deviation pin
`baselines/pins/hidden-dep-order.observation.json`) gained `"output":""`
— a format move, not a semantic one (the twin wire pin did NOT move:
raft prints nothing and calls no float-bits function).

## 6. Rows and the gotest delta

Strict green (19 at the slice; 20 after the audit fix round): 13
`builtins/print/{ints,uints,bool,string,mixed,println-spacing,
print-no-spacing,multiple-calls-order,values-and-output,print-then-panic,
print-then-runtime-panic,print-then-recover,goroutine-ordered}` + 6
`builtins/float-bits/{roundtrip-payloads,nan-semantics,literals-and-zero,
frombits-arith,float32,widening}` (A1: `roundtrip-payloads` → red,
`min-max-payload{,/float32}` born green: 5 + 2 = 7 float-bits green).
Membership green (1): `builtins/print/goroutine-interleaving` (members=2,
R18). Designed red: BUG-093's thirteen (`refused/*` ×12 incl.
`unsafe-pointer` and `race-with-output`, `in-init`) and BUG-094's seven
(A1 added `neg-canonical-refused{,/float32}`, `min-max-canonical-refused`,
`roundtrip-payloads`). Bug pins born red (4): BUG-095's three (order-
fragile — the fix lane adds robust ones), BUG-096's one.

Gotest (`scripts/gotest-triage run --only …` over the 195 files the
2026-09-01 triage recorded as print-refused; evidence
`gotest-results.tsv`): **120 MATCH** (output compared byte-exactly,
`.out` goldens included), 62 FRONTEND-REFUSED (print kinds: 10 float, 13
address — counted on the refusal texts, C2; os.Exit ×14 — gate G7; time.Sleep, runtime.FuncForPC,
reflect.TypeOf, math.Pow, range-over-func, a duplicate-FuncId
decoder refusal …), 10 MACHINE-REFUSED (5 wall-clock timeouts, 3
init-phase prints, method5.go's array conversion, recover2.go's
`$runtime.Error` method-set record), **2 MISMATCH**: `fixedbugs/bug352.go`
— the machine prints `BUG: bug352 …` where gc prints nothing: zero-size
element addresses compare UNEQUAL in the machine and EQUAL in gc, the
recorded R15 latitude (never-same singleton vs gc's non-single-valued
realization), now visible through output rather than only through the
`pointers/zero-size-address` pin — not a new bug, the recorded
deviation; `typeparam/typeswitch3.go` — `T 11` vs `myint 11`, reduced to
BUG-095 (interface embedding, not generics: the non-generic twin fails
too). **1 INFRA**: `fixedbugs/bug356.go` — `INTERNAL PANIC: Nat.pow
exponent is too big`, reduced to BUG-096.

## 7. Decision log

- [USER] G2 (relayed): print/println admitted for int/uint/bool/string;
  address kinds refused; floats initially refused.
- [USER] float-bits primitive admitted (relayed), condition: NaN payloads
  bit-exact, ±0 / quiet/signalling probes — met (rows) except the
  machine's own canonical NaN, which refuses (§2.3, [AGENT]).
- [USER] G-OUT (relayed): event, driver fold, terminal carries prefix —
  realized §1; the EnumSpec `Obs` half owed to the C-arc ([AGENT] scoping).
- [AGENT] output field named `output` (one fd-2 stream; the memo's
  `stdout`/`stderr` pair arrives with G7), schema tag unchanged (§1).
- [AGENT] floats/complex refused this slice (§3.3); zero-operand (§3.5);
  init-phase (§3.4); canonical NaN (§2.3); file:line anchors for `math`
  (§2); dedup engine refuses printing rows (§1); race rows require an
  empty prefix (§5); non-UTF-8 output refuses on both sides (§1/§5).
- [AGENT] BUG-095/BUG-096 opened from the gotest MISMATCH/INFRA rows;
  bug352's mismatch attributed to R15 (recorded latitude), no entry.

## 8. Gate

- First full run: `scripts/capped scripts/ci --slow` on the dirty branch
  tree (all slice work in place): every fast step green except the two
  expected pre-re-pin ones (bug-index: Cases ids not yet in the baseline;
  baseline diff: 38 NEW ids, 0 flips) plus one genuine finding fixed on
  the spot — the escape-hatch preflight matched the WORD "admit" in a
  Syntax.lean docstring (reworded). The GOLEAN_SLOW=1 re-enumeration of
  `imported-goose/channel/google-search` reproduced the six members
  (format-only record change, re-certified in commit bde76b1c).
- Second full run: `scripts/capped scripts/ci --diff` — 3440 cases, 3209
  PASS / 231 FAIL, the certified row CERTIFIED-CACHED against the new
  record, `test-lane-validation --with-go` green (a T5 fixture pinned the
  decoder's error ORDER — the status word must name itself before the
  `output` check — and the S3 fixture caught a double injection; both
  fixed), 153 eval tests, twin wire pin UNCHANGED (4ee39f732d51…), deviation
  pin re-recorded with `"output":""`. Drift vs the previous pin: exactly
  38 born rows, 0 flips → re-pinned in commit 1e177465 (baseline header
  note; ledger §8p — lettered §8o on the lane, re-lettered at the round-14
  rebase because `fr27-fr28`'s §8o landed first).
- Final fast gate at the clean tip (a4865e66): `RESULT: PASS`, 0 HIGH.
- **Audit fix round (2026-09-05, A1–A3, B1/B2, C1–C6, D):** A1 closed two
  wrong-answer families (§2.3/§2.4; `roundtrip-payloads` PASS→FAIL on
  BUG-094's line; 7 new rows); A2 made the fd-2 split refuse the four
  attack shapes (§5; `race-with-output` rowed) and scrubbed GOFLAGS; A3
  wrote R7's amendment, R17, R18 (the first cut's edits never landed —
  a backgrounded script failed silently, caught by the audit); B1
  redirected BUG-095's diagnosis to the frontend's `noteInterface`; C1
  recorded FR-30/R18's obligation with the `c1-probe`; numbers, lowerdiag
  classification, evidence paths and the D items corrected. Gate line
  and SHA in the coordinator report.
- **Rebase onto main fc9bbef1 (merge train round 14, 2026-09-05
  [AGENT]):** main had gained flaky-panic-wait (+1 PASS row),
  g6-reflect-memo (docs), fr27-fr28 (+31 rows, frontend changes) and
  c-arc-gu (the G-U choice-consumption rule in GoCore/State.lean) since
  ac45aedd. Conflicts were confined to the baseline header/tally and the
  ledger §8 records and were reconciled by hand; the Lean/Go code
  auto-merged textually and the round-14 gate is what verifies it. The
  tracked figure re-derived from the data rows: 3479 = 3230 PASS / 249
  FAIL = main's 3434 (3209 / 225) + the lane's 45 born (21 PASS / 24
  FAIL), 0 flips of main's rows (`roundtrip-payloads` is a born FAIL
  against main; it stays on BUG-094's Cases line). The lane's
  pre-rebase figure was 3447 = 3210 / 237. Gate line and SHA in the
  coordinator report.
