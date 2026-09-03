# The noodler — a semantic-edge hunt across the whole language (2026-09-03)

Lane: `noodler` (worktree `.claude/worktrees/noodler`, branch `noodler`
off main @ b5abacc1). [USER]-directed 2026-09-03; the brief reached this
lane by [AGENT]-coordinator relay, not firsthand — Mike, verbatim as
relayed: «send off an agent briefed to be 'the noodler' - i.e to write
new test cases which expose semantic edges we haven't already
discovered. The noodler's job is to persistently poke and prod, find
places that our semantics either (1) doesn't match what gc does, or
(2) where our semantics does something the go semantics implies it
shouldn't do. Broad brief in a worktree, making sure to rule out of
scope all the seams we already know about. The noodler's test cases
themselves should be rolled into our suite, whether or not they found
new issues». Everything below is [AGENT]-executed and [AGENT]-judged
inside that brief: tests and records only — no GoLean/, tools/,
scripts/ change; no merge, no push; born-FAIL rows re-pinned with zero
PASS→non-PASS flips. Evidence: `docs/evidence/2026-09-03_noodler/`.
Oracle: go1.26.5 (the pin).

## 1. Headline

- **Rows added: 562 in 90 packages** under `Corpus/coverage/exec/noodler/`
  (539 PASS / 23 born-FAIL; 4 membership-lane rows + 1 strict
  upper-bound guard, 8 deadlock/fatal rows, ~45 panic rows).
- **The executable core matched gc on every deterministic program that
  lowered**: zero wrong values, zero wrong panic kinds, zero
  termination mismatches, across ~30 areas (§2). The membership rows'
  admitted sets were exactly the spec-bounded sets — no upper-bound
  violation found (§3).
- **Two new fidelity findings**, both at the edge of the trusted
  surface, filed as BUG-085 and BUG-086 (§3).
- **Five refusal families on legal Go that no ledger row names** (§4) —
  the frontend's own `unsup(...)` census was the most productive probe
  source of the lane.
- Known seams re-hit: 8 (§5). Could-not-probe: 4 (§6). One incident (§7).

## 2. Areas probed (package → what it pokes)

| package | rows | what it pokes | result |
| --- | --- | --- | --- |
| `conversions` | 22 | string↔[]byte/[]rune with invalid UTF-8, surrogates, rune overflow; int↔float rounding, ties-to-even; narrowing wraps; non-nil `[]byte("")` | 21 PASS; 1 known FR-10 re-hit |
| `arith` | 19 | MinInt/−1, truncated division signs, shifts ≥ width and by signed counts, untyped-1 shift typing, wraps | all PASS |
| `names` | 15 | shadowing `len`/`true`/`nil`/`string`/`iota`/`append`, labels vs variables, Unicode identifiers, local types in type switches | all PASS |
| `local-types/*` | 2 | same-named function-local types across functions; local type shadowing a package type | 2 refused (known rider, §5) |
| `bounds` | 20 | every slice/index/3-index/string/array-pointer bounds text; slicing within cap | all PASS |
| `ifaces` | 26 | switch-on-interface constant typing, `case nil`, NaN in interfaces, uncomparable dynamic types, promotion through nil embedded pointers, assertion texts, nil-receiver dispatch | 23 PASS; **3 born-FAIL = BUG-085** |
| `closures` | 20 | Go 1.22 per-iteration variables incl. body modification and copy-back, defers/goroutines capturing, range-over-int assignment | all PASS |
| `defers` | 18 | recover directly-vs-indirectly, method/method-value recover, payload kinds, goroutine panics, nested recover levels | 17 PASS; 1 refused (`defer delete`, §4) |
| `maps` | 24 | `m[k] op= f()` ordering, NaN inside array/struct/interface keys, zero-size keys, nil inner maps, tuple targets | 21 PASS; 3 refused (F6/A3 known, §5) |
| `evalorder` | 22 | the spec-ORDERED axes: calls/receives/logical ops across literals, targets, defers, sends | all PASS |
| `latitude` | 12 | the spec-UNORDERED axes (E12's census follow-ons): non-call operand beside a mutating call in literals, receivers, args, concat, deref, return lists | all PASS (gc = call-first on every shape) |
| `select` | 24 | nil channels, closed channels, `select` self send/recv, NaN/array/struct switch tags, fallthrough into a middle default | all PASS |
| `generics` | 19 | untyped-constant inference (1 with 2.5 → float64; 'a' with 1 → rune), zero values, interface type args, `~T` constraints, Go 1.24 generic alias, embedded generic promotion | all PASS |
| `structs` | 21 | NaN inside arrays/structs, pointer identity, zero-length arrays, deep copy, recursive types | all PASS |
| `methods` | 18 | methods on func/array/slice/map/chan/string/bool types, binding time, depth rule, explicit-path disambiguation | all PASS |
| `literals` | 17 | 0b/0o/0x_/1_000 forms, hex floats, rune escapes, exact constant arithmetic vs runtime, typed float32 constants, iota patterns | all PASS |
| `builtins` | 19 | min/max with NaN and ±0, clear on nils/subslices, copy overlap both ways, append nil/aliasing, len/cap of nil kinds | all PASS |
| `goroutines` | 16 | HB-forced concurrent programs (handoff, close broadcast, worker pool, Once, Mutex/RWMutex, semaphore, pipeline), WaitGroup/Mutex deadlocks | all PASS (gc `-race` clean) |
| `init` | 5 | dependency-driven var init through function bodies, blanks, multi-value init, two `init()`s, package-level method value | all PASS |
| `initpanic/*` | 4 | panic in `init()`, deadlock in `init()`, panicking var initializer, recovered init panic | all PASS |
| `strings` | 19 | multibyte range indices, byte-copy independence, ordering, and the shim subset: Fields/TrimSpace/Split/Join/Repeat edges, ParseUint error texts, Sprint spacing, Stringer rendering | all PASS |
| `strconv-formatint` | 2 | `strconv.FormatInt` used alone | **2 born-FAIL = BUG-086** |
| `misc` | 21 | `for range n` without variables, goto forward, labeled continue, curried closures, named func-type conversions, iota flag masks, indexed array literals | all PASS |
| `membership` | 5 | two-sender buffer order {12,21}; 3-key map order (6 perms); select two-ready {1,2}; insert-then-delete during range {2,3}; strict guard: deleting the UNREACHED key gives exactly 1 iteration | all PASS (sets exactly as bounded) |
| `frontier/*` | 32 | one-case packages aimed at the frontend's own refusal strings | 21 PASS; 11 refused (§4, §5) |
| `frontier2/*` | 22 | second frontend sweep: builder chains, typed-nil error returns, recover-into-named-error, embedded-pointer field promotion, nil func/interface calls | all PASS |
| `floats` | 15 | float32 per-op rounding, Inf/NaN arithmetic, signed zero, denormals, float32 overflow, 2^53 boundary, cancellation | all PASS |
| `panics` | 14 | the type-assertion panic-text matrix (pointer↔value, missing method, nil named/any → interface, defined/slice/func/map dynamic types) | all PASS |
| `slices` | 16 | append aliasing at/below cap, prefix overwrite, array storage, full-slice realloc, delete idiom tail, callee append | all PASS |
| `ranges` | 14 | assignment-form range with identifiers, array value copy vs array pointer, writes seen during range, range-int evaluated once, typed range var | all PASS |
| `syncmisuse` | 12 | RUnlock/Unlock-of-unlocked fatals, nested Once deadlock, mutex copies carry state, cross-goroutine unlock, WaitGroup reuse | all PASS |
| `gostmt` | 8 | go-statement argument / receiver / function-value evaluation at spawn, arg panic in the parent | all PASS |
| `typeswitch` | 8 | first-matching-clause rule with overlapping interface cases, `case any` vs `case nil`, typed nil pointer, generic instance cases | all PASS |
| `indexkinds` | 9 | every integer kind as index/bound/shift/make operand; out-of-range texts through uint32/int8 indices | all PASS |
| `gotchas` | 16 | goto over defer, return inside deferred closure, Once with panicking f, arrays through channels/interfaces copy, byte/rune wrap | all PASS |
| `budget` | 6 | recursion depth, loop length, slice size, map size, string build — sized to pass; the cliffs are §6 | all PASS |

## 3. Findings, ranked

### F1 — BUG-085 (wrong-answer, panic TEXT at an R9-pinned point; observed ∉ modeled)

Program: `type Inner struct{v int}; func (i Inner) Val() int`; `var p
*Inner; var v Valuer = p; f := v.Val; f()` (also: `v.Val()` through a
`//go:noinline` parameter, or through a package-level interface
variable). gc: `value method main.Inner.Val called using nil *Inner
pointer` — `runtime.panicwrap`'s `plainError`, a `runtime.Error` with NO
"runtime error: " prefix (`deps/go/src/runtime/error.go:324-348`).
Machine: `runtime error: invalid memory address or nil pointer
dereference`. Spec: the panic is forced (spec#Method_values,
spec#Calls, spec#Address_operators, spec#Run_time_panics); the text is
gc's realized string (latitude R9). gc is NOT single-valued here: the
same source shape with the dynamic type statically visible (`var v
Valuer = p; v.Val()` in one function) devirtualizes — even at
`-gcflags='-N -l'` — and gives the nil-deref text the machine produces
(`noodler/ifaces/iface-dispatch-value-nil` PASS). So the machine
realizes exactly one of gc's two texts, everywhere. Cases:
`noodler/ifaces/{mv-iface-nil-call,iface-param-value-nil,global-iface-value-nil}`.
Evidence: `docs/evidence/2026-09-03_noodler/transcripts/gc-wrapper-text.txt`.
The method-EXPRESSION column of the same probe is FR-3's row, not a new
finding.

### F2 — BUG-086 (spurious refusal, whole-program, inside the frozen stdlib allowlist)

Program: any program calling `strconv.FormatInt` without also calling
`strconv.FormatUint`. Frontend: `nativefrontend: type-check:
golean-stdlib-shims.go:11:16: undefined: goleanShimStrconvFormatUint`
— `stdlibshim.go:234` lists FormatInt's injected declarations as
{FormatInt} while its body (:982/:984) calls the FormatUint shim. The
existing pin `strconv/format-parse` calls both, hiding it. Bisect: five
one-function programs (bases 2/10/16/36, constant/variable, ±) all
refused; the both-functions control exports. Cases:
`noodler/strconv-formatint/{edges,positive}`. Not a widening of the
D-002 surface; a defect in an existing entry's dependency set.

### A1 — apparatus note (not a fidelity bug; scripts are out of this lane's remit)

A strict-lane Lean TIMEOUT is reported as `stage=lean-observation
detail=expected status ok, got ` — an EMPTY observation. The
membership/confluent/racy paths of `scripts/diff-coverage` say
"enumerator TIMED OUT after Ns"; the plain `lean()` path does not name
its cause (charter: a refusal names its cause at the point of
failure). Seen on `recursionDepth(20000)` (123 s standalone) and
`bigSliceSum(100000)` (> 150 s) before those rows were re-sized.

### Not findings (checked and rejected)

- `[0]int(nilSlice)` value-form conversion refused — FR-10 records the
  value-copy form as riding the array-pointer row (triage L2b).
- `%x`/`%v`-on-float in `fmt.Sprintf` refused — D-002's frozen verb/kind
  matrix, by design.
- Recovering a runtime error and asserting it to `error` refused —
  BUG-009/053's `$runtime.Error` MethodSetRecord class (BUG-059's
  KIND clause records it BLOCKED).

## 4. Frontier discussion — refusals on legal Go with no ledger row

Each is a `frontend-export` refusal (outside the fidelity filter; born-FAIL rows re-pinned). None is a wrong answer. Proposed for the language-coverage ledger §4 as new FR rows (the [USER]'s call; this lane did not edit the §4 table — [AGENT] decision, so the §8 closing arithmetic stays the ledger owner's):

| id | shape (legal Go) | refusal string (source) | rows | recorded where today |
| --- | --- | --- | --- | --- |
| FG-1 | two functions each declaring `type T int`; a local type shadowing a package-level type | `duplicate TypeId main.T (a function-local type collides with another declaration)` (emit.go:554) — a WHOLE-EXPORT kill; this lane tripped it three times by accident (4 unrelated packages killed until the local names were made unique) | `noodler/local-types/{distinct,shadow}` | `docs/2026-08-04_control-flow-design.md` ("fail-closed rider"); BUG-011's generic-instantiation cousin; NOT in ledger §4 |
| FG-2 | `defer delete(m, k)` (and by the same arm `defer panic(v)`, `defer print…`) | `defer of builtin delete` (emit.go:2591 — only `recover`/`close` lower) | `noodler/defers/deferred-delete` | nowhere (spec#Defer_statements permits it) |
| FG-3 | an allocation / tuple-splat / interface method value in a `&&` or `\|\|` RIGHT operand: `make`, `new`, slice literal, map literal, `f(g())`, `(i.M)()` | `<X> in short-circuit operand` (emit.go: hoistForbidden="short-circuit operand"; :2330/:2355/:6031/:6572/:6626/:8170/:8925) | `noodler/frontier/short-circuit-{alloc-make,alloc-new,slice-literal,map-literal,splat-call,iface-method-value}` | FR-2 / triage F24 record only the channel-RECEIVE case |
| FG-4 | forward `goto` to a label inside the same nested block (a for body) | `goto target label skip not at function body top level` (emit.go:1743/:2069) | `noodler/frontier/goto-forward-in-block` | control-flow design doc's "outside the envelope" list; FR-11's string covers backward-goto hoists only |
| FG-5 | inner-scope `x := f(x)` (the call reads the outer `x`) | `self-shadowing define with call RHS` (emit.go:3057) | `noodler/frontier/self-shadow-define` | W7 desugar inventory A-9 ("one arm still fail-closed"); NOT in ledger §4 |

Also re-hit, already recorded as red-by-design: BUG-068's `range-clause`
/ `ts-guard` refusals (`noodler/frontier/named-result-shadow-{range,typeswitch}`),
FR-3 (`noodler/frontier/promoted-method-expression-ptr`), triage F6 /
mini-slice A3 (`noodler/maps/{swap-with-missing,tuple-two-map-targets,tuple-map-and-var}`).

## 5. Known seams re-hit (the coverage the coordinator asked to see)

| seam hit | rows | record found |
| --- | --- | --- |
| slice→array VALUE conversion (succeeding form) | `conversions/nil-slice-zero-array` | ledger §4 FR-10 + triage L2b ("the value-copy form rides the same frontier row") |
| `$runtime.Error` has no MethodSetRecord → `.(error)` on a recovered runtime error refuses | (row rewritten to observe `recover() != nil` only) | BUG-009/BUG-053 class; BUG-059 KIND clause |
| duplicate local TypeId | `local-types/{distinct,shadow}` | control-flow design doc rider (→ FG-1: not in the ledger table) |
| map elements as multi-assignment targets | `maps/{swap-with-missing,tuple-two-map-targets,tuple-map-and-var}` | triage F6 / mini-slice A3 QUEUED; 5 baseline reds already |
| `(*T).M` method expression over a value-receiver method (via promotion) | `frontier/promoted-method-expression-ptr` | FR-3 |
| named-result shadow outside the rename set (range clause, type-switch guard) | `frontier/named-result-shadow-{range,typeswitch}` | BUG-068 red-by-design rows |
| fmt verb/kind matrix (`%x` int, `%v` float64) | (rows rewritten to the modeled verbs) | D-002 frozen surface, by design |
| `[]rune`/`[]byte` conversion capacity | (deliberately not observed) | R3 |

## 6. Could not probe / cliffs

- **Enumerator budget**: a membership row for two goroutines appending
  under a Mutex ({12,21}) exceeded `work=20000000` and then the 300 s
  enumerator timeout even after unrolling the spawn loop and removing
  the WaitGroup; dropped (the strict Mutex rows in `goroutines` cover
  the forced half).
- **Wall-clock cliffs** (single measurements, shared box): non-tail
  recursion depth 5000 → 5.1 s, 10000 → 22.6 s, 20000 → 122.8 s
  (super-linear); slice fill+sum of 3000 elements → 33.0 s, 10000 →
  >150 s (the BUG-078 residual-(3) class: element stores re-normalize).
  A 1e6-iteration loop exhausts the 10M-step fuel (`fuel-out`, cause
  named). The `budget` rows were sized to pass (recursion 5k, slice 1k,
  loop 100k); the cliff numbers live here and in the evidence notes.
- **Atomics** — out of scope by the brief (the `atomics-w1` lane).
- **Abort-line rendering of error/Stringer payloads**, hidden-dep init
  order, float→int out-of-range — (c)-pinned classes, deliberately not
  re-probed.

## 7. Incident

At ~02:40 this lane killed processes matching `scripts/ci --diff`
machine-wide while stopping its own background gate; the `atomics-w1`
worktree's `artifacts/coverage/latest.meta.tsv` was written at 02:40,
so that lane's gate was very likely killed. The coordinator should have
atomics-w1 re-run its gate. Recorded in the evidence README; the retry
recorded its own PID and killed only that.

## 8. Gate, re-pin, reconcile

<<GATE>>

## 9. What I would probe next

- gc's other autogenerated-wrapper texts (embedded-interface method
  wrappers on nil, `panicwrap` for promoted methods through nil
  embedded VALUES in interfaces) — F1's family is probably wider.
- A systematic sweep of every `unsup(...)` string in
  `tools/nativefrontend` against a legal-Go witness (this lane covered
  ~25 of ~190; the frontier hunt was the lane's best yield per row).
- Multi-package shapes (exported/unexported promotion across packages,
  init order with imports) — the multipkg harness exists.
- Panic payload rendering for non-error struct/pointer payloads at the
  abort line (R10 edges beyond BUG-004's three rows).
- Select-with-select and Cond/TryLock once their design questions rule.
