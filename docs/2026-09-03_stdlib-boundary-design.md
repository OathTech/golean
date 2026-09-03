# The standard-library boundary of GoLean — design memo (2026-09-03)

**Status:** DESIGN MEMO with NAMED DECISION GATES for the [USER]. Not a
plan of record until the gates in §5 are ruled. Docs only: no code, no
corpus, no baseline change rides with this note.

**Provenance.** [USER]-directed lane (Mike, 2026-09-03, relayed by the
[AGENT] coordinator — not firsthand: «let's launch an agent to figure
out the stdlib design»). Every judgment below is [AGENT] unless marked
[USER]; every number is measured at `main @ b5abacc1` (worktree
`stdlib-design`) or cited to the tracked record that measured it. The
two ad-hoc census programs this memo ran (a GOROOT purity census and a
`print`/`println` argument-kind census over the $GOROOT/test triage
rows) are reproduced verbatim with their raw output in the appendix
file `docs/2026-09-03_stdlib-boundary-design-census.md`, so the counts
are derivation-anchored, not asserted.

**What this memo is for.** Discrepancy D-002 (`docs/discrepancy-backlog.md`)
parks the frontend's stdlib INJECTION surface under a freeze ([AGENT]
policy, confirmed [USER] 2026-09-01) with the retirement condition
"the retirement design note ([USER] design gate) + its first
implementation", review by 2026-10-31. This is the retirement design
note. §6 names the first implementation.

**Reading behind this memo** (all read in full or at the cited spans):
`CLAUDE.md`, `AGENTS.md`, `docs/discrepancy-backlog.md` D-002,
`docs/assessment/p2-fact-verification.md` §9–§10,
`docs/assessment/synthesis.md` C1, `docs/assessment/lane-a2-ledger-frontier.md`
§0.2 / A2-F2, `docs/assessment/lane-a3-shims-spectruth.md` S1–S7,
`docs/assessment/decisions-2026-08-31.md` decision 2,
`docs/language-coverage-ledger.md` §2 Bootstrapping/Qualified_identifiers
rows, FR-14, §5.1, §6, `docs/2026-09-01_gotest-triage.md`,
`docs/2026-08-16_overrides-design.md` (the ruling and its linked-registry
proposal), `docs/2026-08-31_qrow-rulings.md` rows 6–7,
`docs/2026-08-09_sync-package-design.md` §7/§9,
`docs/2026-07-30_quorum-extern-policy.md`, `docs/2026-08-18_multipackage-identity.md`
§1, `docs/spec-sources.md`, `docs/2026-08-11_latitude-inventory.md`
R10–R13, `tools/nativefrontend/{stdlibshim,fmtdesugar,fmtcomposite,genericshim,importedmodel,load,inittask}.go`,
`GoLean/GoCore/{Machine,Race,Syntax,FloatBits}.lean` (sync ops,
`sortSlice`, the panic-payload renderer), `deps/go/src/{fmt,strings,strconv,errors,slices,cmp,sort,math,bytes,unicode/utf8,internal/bytealg,internal/strconv,runtime/print.go}`
at the go1.26.5 pin, and a read-only survey of
`/home/dev/projects/cerberus-lean-proj` (Appendix C).

---

## 0. Summary and recommendation

**The recommendation ([AGENT]): option (C), the hybrid, in this
specific shape:**

1. **Source-through at FUNCTION granularity.** The real GOROOT source
   at the oracle pin (`deps/go/src`, rev `go1.26.5` — already a pinned
   `scripts/setup-deps` row, `docs/spec-sources.md`) is loaded as
   ordinary SOURCE PACKAGES by the multi-package loader (`load.go`),
   type-checked whole, and EMITTED reachability-pruned: only the
   declarations the program reaches lower; every reached declaration
   the pipeline cannot lower becomes the existing per-declaration
   quarantine stub (`emit.go` H-3), so a call to it refuses BY NAME at
   run time. Nothing is pasted into the user's package. FuncIds are
   the path-qualified ones the identity design already mints
   (`strings.Fields`, `strings.Builder.WriteString`).
2. **A portable-substitution table for the assembly-backed leaves**
   (`internal/bytealg` native → its own `*_generic.go` siblings;
   `math` `*_asm.go` → `*_noasm.go`), tracked, counted, each entry
   carrying the reason.
3. **A pinned OVERLAY for the handful of `unsafe` idioms in otherwise
   pure library text** (`strings.Builder.String` = `string(b.buf)`,
   `Builder.grow`'s `bytealg.MakeNoZero` = `make`, `errors.Join`'s
   `unsafe.String`, `internal/strconv`'s four float-bits casts onto
   the machine's `FloatBits`). The overlay is a DIFF against upstream
   at the pin, byte-checked at the pin, counted, and governed by the
   admission rule in §2.2 — it is the honest successor of the shim
   mechanism, an order of magnitude smaller, and it cannot grow
   silently.
4. **A minimal set of MACHINE primitives only for what is language,
   not library:** `print`/`println` (spec#Bootstrapping — they are
   built-ins of the language, with gc's realized formatting at the pin
   as the (b)-pin), with a **stderr observable** added to the
   observation schema (§4). `fmt`'s reflective core is NOT made a
   machine op: `fmt` is library, and a `format` op inside `stepFn`
   would be exactly the in-machine library table the 2026-08-16 note
   forbids ("THE TCB CONSTRAINT").
5. **`fmt` is split, not shimmed:** static call sites keep the emit-time
   SPECIALIZATION (a frontend lowering strategy over static types —
   legitimately frontend work) but its leaf renderers become calls into
   the real, source-through `strconv` (`FormatInt`, `Quote`,
   `FormatBool`, `AppendFloat`), which deletes the hand-written digit
   loops and quoters and their recorded bounds (%q non-ASCII); dynamic
   sites (`[]any` spreads) keep a runtime type switch over the basic
   kinds; the reflective remainder (arbitrary structs/maps at dynamic
   sites, `%T`, `%p`) stays REFUSED by name until a modeled `reflect`
   subset is a ruled decision (§5 G6) — not this memo's ask.
6. **An explicit out-of-scope list with reasons** (§2.3.4): `unsafe`,
   `reflect`, `runtime` (except a two-entry no-op-by-spec list posed as
   a gate), `os`/`io`/`syscall`/`time`/`net`, cgo, finalizers/weak
   pointers, `sync.Pool`/`sync.Map`, `testing`.

Why not the alternatives, in one line each: (A) pure source-through
is blocked at the leaves by `unsafe`/asm/reflect and would still need
primitives for `print`; (B) pure primitives re-creates the shim
surface inside the trusted core, which is worse than where it is now;
(D) status-quo-plus keeps a mechanism the [USER] ordered retired at
instance 2 and now stands at 20 (10× — p2 §9), and buys the least.

The trusted-surface delta of (C) is small and legible: one new machine
op family (`print`), one observation-schema field pair (`stdout`/
`stderr`), and the library source at the pin as a trusted-ADJACENT
input validated by the same differential that validates everything
else (the circularity argument is in §2.1.4 — it is not circular).

**The first implementation slice (§6):** `strings.{Fields,TrimSpace,Split}`
+ `strconv.{FormatUint,FormatInt,ParseUint}` through the library
loader, deleting 6 of the 20 shims, exercising the loader, the
reachability pruning, the quarantine stubs, and the bytealg
substitution table, with the existing conformance suites as the
regression and a tracked library-pin hash. `print`/`println` is the
second slice if G2 is ruled as recommended.

---

## 1. The problem, measured

### 1.1 What real Go code demands (four sources, one picture)

**(a) The $GOROOT/test triage** (`docs/2026-09-01_gotest-triage.md`;
raw rows re-read this session from the t4-gotest lane's
`artifacts/gotest/results.tsv`, 1,013 in-scope cases, commit 670d3351):

| refusal cause (triage bucket) | count | this memo's finer census |
|---|---|---|
| builtin `println` in statement position | 159 (158 direct + cascades) | see below |
| builtin `print` in statement position | 28 | see below |
| `fmt.*` outside the modeled subset | 82 | `fmt.Printf` 32, `fmt.Sprintf` 29, `fmt.Println` 21, `fmt.Errorf` 1 (rows may name several) |
| `runtime.*` | 55 | `GC` 18, `SetFinalizer` 10, `GOMAXPROCS` 9, `Callers` 6, `Caller` 6, `Stack` 2, `Gosched` 2, `ReadMemStats`/`NumGoroutine`/`NumCPU`/`FuncForPC` 1 each |
| other stdlib | 51 | `reflect.{TypeOf 10, ValueOf 6, DeepEqual 5, ArrayOf 2, …}`, `math.{NaN 5, Signbit 2, Inf 2, Float* 2, Trunc, Sqrt}`, `time.{Sleep 4, Tick, After}`, `os.{Exit 11, Args 4, Getenv 3, Stdout 1}`, `sort.Ints` 2, `atomic.*` 4, `utf8.DecodeRuneInString` 2, `strings.Contains` 3, `strconv.Itoa` 2, `bytes.Compare` 2, singletons (`maps.Clone`, `log.Fatalln`, `json.Unmarshal`, `big.NewInt`, `md5.New`, `filepath.Join`, `context.Background`, …) |
| `unsafe.*` | 46 | out of language (ledger §2 Package_unsafe) |

**The `print`/`println` argument-kind census** (Appendix B, program
`plncensus`): 195 refused test files name a builtin print (186 direct
+ 9 through a method-body quarantine cascade). **169 of 195 (87%) pass
only integers, strings and booleans.** The rest need floats (12 files),
interfaces (7), complex (4), pointers (4), slices (3), maps (2), or
multi-value call spreads (3). **34 of 195 have a `.out` golden file**;
the other 161 must print NOTHING on success (the testdir driver
compares against the `.out` file or the EMPTY string —
`deps/go/src/cmd/internal/testdir/testdir_test.go:1134-1141`), i.e.
their prints are failure reports inside dead branches on a passing
run.

**(b) The raft subject** (`raftsubject/`, 31 non-test files; selector
census this session): `fmt.Fprintf` 30, `errors.New` 27, `fmt.Sprintf`
25, `fmt.Errorf` 16, `fmt.Fprint` 13, `strings.Builder` 10,
`slices.Sort` 10, `math.MaxUint64` 6 (constant-folded — free),
`fmt.Sprint` 5, `strings.Repeat` 4, `sync.Mutex` 3, `cmp.Compare` 3,
`slices.SortFunc` 2, `os.Exit` 2, `log.New` 2, `bytes.Buffer` 2,
`binary.LittleEndian` 2, and singletons `strings.{TrimSpace,Split,Join}`,
`strconv.{ParseUint,FormatUint,FormatInt}`, `rand.Rand`, `os.Stderr`,
`io.Discard`, `bytes.Equal`. Imports by file: `fmt` 14, `strings` 8,
`errors` 7, `sync` 5, `slices` 5, `time` 3, `strconv` 3, `math` 3,
`context` 3, `os` 2, `log` 2, `encoding/binary` 2, `bytes` 2. This is
exactly the set the 20 shims were grown to cover — the shims ARE the
raft subject's import census, hand-modeled.

**(c) grossmith** demands nothing: its programs are "self-contained,
`go run`-able, no imports" by design (`deps/grossmith/BRIEF.md:227-245`);
its spec-ledger covers constructs, not packages. The fuzzer is not a
stdlib consumer and does not bear on this design.

**(d) The assessment's 41 refusals** (`lane-a2-ledger-frontier.md`
§0.2 groups 1 and 4; synthesis C1): 30 shim-surface reds (fmt 15,
quarantine-blocked method calls 4, `slices.Sort*` 4, strconv 1,
strings 1, shim-refusal-unrecoverable 3, qualified-identifier/timezone
2) + 11 init-order-quarantine reds whose root is also the stdlib
boundary (`os.Getenv` etc. poisoning package-var initializers). Only 7
of the 41 have an FR row (FR-14).

**(e) The corpus today**: 2,575 exec rows, 204 tagged `stdlib` across
36 suites (`fmt/sprintf-verbs` 33, `fmt/v-composites` 25,
`fmt/sprintf-dyn` 15, `examples/wordfreq` 14, …); in
`baselines/native-full.tsv` the shim suites stand at **162 PASS / 35
FAIL** (the FAILs are the recorded-bound and refusal pins: Formatter
family 7, shim-value-refused 2, shim-refusal-unrecoverable 3,
sprintf-dyn bounds 4, sprintf-verbs 3, v-composites 3, sortfunc 3,
fprint-writers 2, init/quarantined-var 5, and one each for the Split
empty-separator, Repeat bound and ParseUint deltas). These 197 rows
are the regression suite for any retirement (§3).

### 1.2 What we have today (supply)

**Hand-modeled by frontend injection — FROZEN (D-002):** 20 functions/
methods in four dispatch tables (`stdlibshim.go:148-199`): direct-call
shims `strings.{Fields,Join,Split,TrimSpace,Repeat}`, `errors.New`,
`bytes.Equal`, `strconv.{FormatUint,FormatInt,ParseUint}`; generic
desugars `slices.SortFunc`, `cmp.Compare`; fmt desugars
`fmt.{Sprintf,Errorf,Fprintf,Fprint,Sprint,Sprintln}`; package-variable
method desugars `binary.LittleEndian.{Uint64,PutUint64}`. Two shadow
types `strings.Builder`, `bytes.Buffer` (`importedmodel.go`). 45
injected declarations. Five mechanisms. **3,801 lines at b5abacc1**
(`stdlibshim.go` 1,522 + `fmtdesugar.go` 1,401 + `fmtcomposite.go` 413
+ `genericshim.go` 139 + `importedmodel.go` 326; p2 §9 measured 3,305
at its 2026-08-31 checkout — the growth is the BUG-071/072/073 closures
landed under the freeze's "Fields-standard validation on any shim that
changes" clause). Three real shim bugs on the record were found by
adversarial audit, not by the conformance rows (A3-S2: R1-F3 ParseUint
saturation, R4-M-5 trailing-`%+`, R4-C-3 recoverable refusals).

**Modeled in the MACHINE proper (library semantics that the machine
legitimately owns):** the four `sync` primitives as `Ty.sync` values
with ten `SyncOp`s (`Machine.lean:1422-1460`, `applySyncOp` :2589;
go_mem-keyed detector kinds in `Race.lean` `syncEntryKinds`
:1231/:1270) — justified by the memory model's normative deferral to
the `sync` docs (ledger §3 "more" row) and by the Q-SYNCVAL identity
principle (indirection consumes the same machine op or refuses — never
variant semantics; [USER] 2026-08-31, row 6); and the `sortSlice` wide
op for `slices.Sort` at integer kinds (`Syntax.lean:269`, the
quorum-extern precedent, whose "drags in generics" justification the
launch audit already marked expired — `quorum-extern-policy.md`
SUPERSEDED PREMISE). Nothing else. The machine has **no output
observable** (p2 §10; `gotest-triage` header).

**Refused by name:** every other `pkg.Fn` call
(`emit.go:7978-7982` "package-selector call %s.%s (package %q surface
not modeled)"), builtin `print`/`println` in statement position
(`emit.go:2472-2483`), `unsafe.*` (BUG-070 mechanism), stdlib imports
absent from the inittask table (`inittask.go`), `sync` members outside
the modeled ten.

### 1.3 What the real implementations depend on — the purity census

Method: a `go/build` walk of `deps/go/src` at the pin with
`GOOS=linux GOARCH=amd64 CgoEnabled=false`, per package: own `.go`
files/lines, direct imports, transitive closure, and — summed over the
closure — assembly files, `//go:linkname` directives, body-less
declarations; plus whether the closure reaches `unsafe`,
`reflect`/`internal/reflectlite`, `runtime` (Appendix A, program
`purity`).

**Finding 1 — the LEAF packages are pure Go text.** Own-package
counts (asm / linkname / bodyless) are 0/0/0 for `cmp`, `unicode/utf8`,
`unicode`, `strings`, `strconv`, `internal/strconv`, `slices`, `sort`,
`errors`, `fmt`, `encoding/binary`, `io`, `context`, `container/list`,
`internal/byteorder`; `bytes` has one linkname (the hall-of-shame
`Repeat` export, not a dependency), `math/bits` two (runtime's
`overflowError`/`divideError` VALUES — the language's own panics).

**Finding 2 — the impurity is concentrated at five well-defined
points**, and every candidate package's CLOSURE reaches `runtime`
through them, so package-granular source-through is impossible and
function-granular source-through is the only shape:

| impurity | where | what a portable stand-in is |
|---|---|---|
| assembly | `internal/bytealg` (5 `.s`, 11 body-less declarations — the `IndexByte`/`IndexByteString`/`Count`/`Compare`/`Index`/`Equal` family plus `MakeNoZero`), `math` (5 `.s`: floor/exp/hypot/log/dim on amd64) | bytealg ships `*_generic.go` bodies behind `!amd64…` build tags — the same functions in pure Go; math ships `*_noasm.go` twins (float last-ulp agreement with the asm is a latitude question — §2.1.2) |
| `unsafe` idioms in otherwise pure bodies | `strings/builder.go:39,47,67` (`abi.NoEscape`, `unsafe.String(unsafe.SliceData(b.buf), len)`, `bytealg.MakeNoZero`), `errors/join.go:58` (`unsafe.String(&b[0], len(b))`), `internal/strconv/deps.go:13-16` (four float-bits casts), `slices/slices.go:457-464` (`overlaps` via `unsafe.Sizeof`/pointer arithmetic) | `string(b.buf)`; `make([]byte, n)`; the machine's `FloatBits` (already a softfloat64 port, `FloatBits.lean:145-235`); a refusal for `overlaps` (used only by `Replace`/`Insert`) |
| reflection | `fmt/print.go` (41 `reflect.` uses — `printValue`, `%T`, `%p`, maps via `internal/fmtsort`), `errors/wrap.go` (`Is`/`As` via reflectlite), `sort/slice.go` (`sort.Slice` via `reflectlite.Swapper`), `encoding/binary` (`Read`/`Write` reflect paths) | none — this is the genuine frontier (§2.3.3) |
| runtime hooks | `iter` (coroutines: `runtime.newcoro` via linkname), `sync` (semaphores, `internal/sync`), `math/rand/v2` (`runtime.rand`), `time`, `os`, `syscall` | the machine's own model where one exists (`sync`: already modeled as ops); otherwise out of scope |
| OS | `os`, `io/fs`, `internal/poll`, `syscall` | out of scope (no OS model; §2.3.4) |

**Finding 3 — `fmt` is reflection all the way down.** `printArg`'s
fast switch (`fmt/print.go:707-741`) handles the basic kinds without
reflection; everything else (`printValue`) is `reflect.Value`
recursion, and `%v` over a map goes through `internal/fmtsort`
(sorted keys — deterministic since Go 1.12, so map printing order is
NOT latitude in gc, but it is `reflect`).

### 1.4 The table: package → demanded → dependency class → status

| package | demanded (source) | real-impl dependency class | today |
|---|---|---|---|
| `strings` | Fields, Join, Split, TrimSpace, Repeat, Builder (raft, corpus); Contains, Index (gotest) | pure Go except: `Builder` (unsafe idiom ×3), `Index`/`Count`/`Split` (→ `internal/stringslite` → `internal/bytealg` asm) | 5 fns SHIMMED, Builder SHADOW-TYPED, rest REFUSED |
| `strconv` | FormatUint, FormatInt, ParseUint (raft); Itoa (gotest) | pure Go (`internal/strconv`; four float-bits casts = `FloatBits`) | 3 fns SHIMMED (with recorded deltas: error type, base 0, bitSize), rest REFUSED |
| `errors` | New (raft, corpus, 27 sites); Is/As (not measured, ubiquitous in real code) | `New` pure; `Is`/`As` reflectlite; `Join` unsafe idiom | New SHIMMED (dynamic-type-name delta), rest REFUSED |
| `fmt` | Sprintf, Errorf, Fprintf, Fprint, Sprint, Sprintln (raft); Printf, Println (gotest 53) | reflect (`printValue`), `os.Stdout` for Print*, `internal/fmtsort` | 6 fns DESUGARED at static types over a verb×kind matrix; Print*/Printf/Println REFUSED (no stdout observable) |
| `slices` | Sort (raft 10), SortFunc (raft 2) | pure generic Go (pdqsort in `zsort*.go`); `overlaps` unsafe (Replace/Insert only) | Sort MACHINE OP at int kinds (`sortSlice`); SortFunc SHIMMED (insertion sort, tie latitude R13) |
| `cmp` | Compare (raft 3) | pure | SHIMMED at int/string kinds; floats REFUSED |
| `bytes` | Equal, Buffer (raft) ; Compare (gotest) | Equal pure (`string(a)==string(b)`); Buffer pure; Compare → bytealg asm | Equal SHIMMED, Buffer SHADOW-TYPED, rest REFUSED |
| `encoding/binary` | LittleEndian.Uint64/PutUint64 (raft) | pure (`internal/byteorder`) for the ByteOrder methods; `Read`/`Write` reflect | 2 methods DESUGARED, rest REFUSED |
| `unicode/utf8`, `unicode`, `math/bits` | DecodeRuneInString (gotest); transitively by strings | pure (unicode: 10,335 lines of tables) | REFUSED |
| `math` | MaxUint64 (raft, folded), NaN/Inf/Signbit/Trunc/Sqrt (gotest) | pure Go twins exist for every asm file; `Sqrt` is a compiler intrinsic on amd64 | constants FREE; fns REFUSED |
| `sync` | Mutex/RWMutex/WaitGroup/Once (raft, corpus) | runtime semaphores — the machine OWNS this | MACHINE-MODELED (10 ops); Cond/Pool/Map/atomic REFUSED (Q-COND/Q-ATOMIC ruled envelopes) |
| `sort` | Ints (gotest) | pure generic except `sort.Slice` (reflectlite) | REFUSED |
| `os` | Exit (raft 2, gotest 11), Args, Getenv, Stderr | OS | REFUSED (init/quarantined-var pins the Getenv poisoning) |
| `runtime` | GC, SetFinalizer, GOMAXPROCS, Caller(s), Gosched (gotest 55) | runtime internals | REFUSED |
| `reflect` | TypeOf, ValueOf, DeepEqual (gotest 25) | runtime type metadata | REFUSED |
| `time`, `log`, `io`, `context`, `math/rand/v2` | raft harness/logging paths | OS / runtime / fmt | REFUSED |
| `unsafe` | Sizeof/Offsetof/Pointer (gotest 46) | out of language | REFUSED (BUG-070 mechanism) |
| builtin `print`/`println` | gotest 195 files | `runtime/print.go`: `gwrite` → fd 2; `printfloat64` = `strconv.AppendFloat(…, 'g', -1, 64)` since 9035f7ae (2025-10-28, "runtime: use internal/strconv") | REFUSED (ledger §5.1 item 3) |

---

## 2. The options

### 2.0 The evaluation criteria (derived from the charter, not invented here)

- **T — trusted-surface growth.** CLAUDE.md names the trusted surface
  as the interpreter + the native lowering + the differential
  apparatus. Anything a stdlib design adds to `GoLean/GoCore/` or to
  the wire grammar is trusted; anything in the frontend is trusted
  lowering; anything that changes what the observation compares is
  apparatus. Less is better; legible is mandatory.
- **F — fail-closed-ness.** Unknown → refusal that names its cause;
  no absorbing defaults; refusals are not passes.
- **V — differential validatability.** The design must make library
  behaviour something `go run` can contradict. Mock-vs-real (the
  2026-08-16 note's layer 3) is validatable; an in-machine table that
  both sides cannot disagree on is not.
- **U — upper-bound faithfulness.** The machine is the weakest machine
  Go permits. Library DOCS grant latitude too (sort stability: "not
  guaranteed to be stable"; `print` formatting: "implementation-
  specific"; `fmt` on `%v` of a NaN map key; `errors.Join` text). A
  design that silently bakes gc's member in is a (b)-pin that must be
  RECORDED, like R13, never hidden.
- **R — what the reasoning consumer needs.** The reasoning repo will
  consume this one as a pinned dependency and prove things about
  programs that call libraries. It needs stable identities for library
  functions and something to reason against: either the callee's body
  (inlined, stepped) or a spec (opaque). §2.6.
- **N — no semantic choice hidden in evaluator recursion** (AGENTS.md):
  frontend concerns stay in the lowering; library behaviour is not
  language behaviour and does not belong in `stepFn`.

### 2.1 Option (A) — source-through

#### 2.1.1 Mechanics, blockers, and the purity census as an instrument

**Mechanics.** Extend `load.go`'s import-driven discovery with a second
root: a stdlib SOURCE root pinned to the oracle rev (`deps/go/src`, rev
= `scripts/setup-deps`' `go` row). An import path that is neither
case-local nor on the out-of-scope list resolves to a source unit
under that root, type-checked with `go/types` exactly like a case-local
package (its own imports resolving recursively the same way, or, for
out-of-scope packages, to `importer.Default()` export data so the
TYPE-CHECK still succeeds while the BODIES are absent). Emission is
reachability-pruned from the program's roots (main package
declarations + `$pkginit`): only reached functions, methods (the
method-set completeness invariant applies — a reached TYPE brings its
whole exported method set as stubs, bodies only for reached members),
types and package-level variables lower. A reached declaration whose
body hits an unlowerable construct (an `unsafe` operation, a body-less
declaration, a linkname'd runtime hook) becomes an H-3 quarantine stub
whose call refuses by name (`emit.go:191-242`). The wire is unchanged
in grammar: these are ordinary path-qualified `Func`s and `TypeDef`s
(`docs/2026-08-18_multipackage-identity.md` §1 — `strings.Fields`,
`strings.Builder.WriteString`, exactly what the shadow-type harvest
already mints).

**What blocks a NAIVE source-through, and what dissolves each block.**

| blocker | measured extent | resolution |
|---|---|---|
| `reflect` | `fmt` (41 sites), `errors.Is/As`, `sort.Slice`, `encoding/binary.Read/Write` | not resolved by (A): these functions quarantine; §2.3.3 |
| `unsafe` | `strings.Builder` ×3, `errors.Join` ×1, `internal/strconv` ×4, `slices.overlaps` ×1, `math/bits` (linkname vars only), `bytes` (linkname only) | the OVERLAY (§2.3.2): 9 sites in 4 files |
| assembly | `internal/bytealg` 5 `.s`/11 body-less; `math` 5 `.s` | the SUBSTITUTION TABLE: pick `*_generic.go`/`*_noasm.go` twins (§2.3.2) |
| `runtime` hooks | `iter` (coroutines), `sync` internals, `math/rand/v2`, `time`, `os` | `sync` → the machine's ops (already the design); the rest out of scope or quarantined |
| init graphs | `unicode` 10k lines of `RangeTable` literals; `strings.asciiSpace`; `strconv` tables | package-level vars are lowered ONLY when reached; the frontend's pruned-init model (`inittask.go`, `load.go` `specInitOrder`) already places stdlib packages in gc's schedule — a source-lowered package's `$init` replaces its ordering-only placeholder, at the SAME position (BUG-060/L-011 pins guard it) |
| GOROOT vendoring | `deps/go` is gitignored; the frontend must FAIL CLOSED when the root is absent or at the wrong rev | rev check against `deps/go/VERSION` = the oracle `go version` (the existing spec-pin ⟷ oracle preflight, `spec-sources.md`) |
| generics | library generics (`slices.*`, `cmp.Compare`, `maps.*`) cannot be pre-lowered | they are stenciled per program by `mono.go` exactly like user generics (the SortFunc shim already does this) — which is why the library is lowered PER PROGRAM from source, not shipped as a pre-lowered artifact (the 2026-08-16 "pre-lowered registry" needs this correction) |
| interpreter cost | real bodies are longer (pdqsort vs insertion sort; `unicode.IsSpace` table lookups) | fuel/wall budgets are honest refusals; measure on the conformance suites at slice 1 |

**Which packages go through TODAY at function granularity** (from
Appendix A + the impurity table): `cmp` (whole), `unicode/utf8`
(whole), `unicode` (whole; init cost), `math/bits` (whole — the two
linknames are runtime error VALUES the machine's own division/overflow
panics realize), `internal/byteorder` (whole), `container/list` (whole),
`strconv` + `internal/strconv` (whole, given the 4-cast overlay),
`strings` minus `Builder` (given bytealg substitution) and `Builder`
given the overlay, `bytes` (same shape), `errors.New`/`Unwrap`
(`Is`/`As`/`Join` quarantine), `slices` minus `Insert`/`Replace`
(`overlaps`), `sort` minus `Slice*`, `encoding/binary` ByteOrder
methods, `math` (given the noasm substitution; latitude note below),
`container/heap` (pure but imports `sort`). `fmt`, `sync` (owned by the
machine), `iter`, `maps` (iterator-based), `os`, `time`, `io` do not.

**The purity census as a standing instrument.** The Appendix A program
is 150 lines; promoted to `scripts/stdlib-purity-census` it becomes the
re-pin-time check that the substitution/overlay tables still cover
every impurity a lowered package reaches (a new `unsafe` site in a
package we lower must appear as a NEW quarantine stub, never as a
silent lowering — the fail-closed direction is automatic because the
emitter refuses `unsafe` operations; the census makes the drift
VISIBLE at re-pin rather than discovered at run time).

#### 2.1.2 Latitude under source-through — the (U) cost, stated plainly

Source-through realizes gc's member of every library-doc envelope,
because it lowers gc's implementation. Three classes:

1. **Docs grant latitude, gc realizes one member, the member is
   observable:** `slices.SortFunc` / `sort.Slice` tie order ("not
   guaranteed to be stable"), `strings.Builder` capacity growth
   (`Cap()`), `map` iteration inside library code that ranges over a
   map (`fmt` sorts; `maps.Keys` yields in map order — LANGUAGE
   latitude the machine already reifies as a choice, so a lowered
   library body inherits it correctly). Posture: RECORD each as a
   version-tracked (b)-pin in the latitude inventory (R13 is the
   template), reify as a choice site only when a consumer needs the
   envelope (G4).
2. **Assembly-vs-Go twins may differ in the last ulp** (`math.Exp`,
   `Log`, `Floor`…): the pure-Go twin is the SPEC of the function in
   the only sense the docs give ("returns e**x"), and the asm is gc's
   realization; the Go project tests both against the same tables.
   Posture: record as float latitude beside R4 (fusion narrowed) and
   let the differential catch any realized divergence (a mismatch row
   is a discovered latitude point, recorded, not a bug).
3. **No latitude, exact:** `strconv`, `strings` text functions,
   `errors.New`, `bytes.Equal`, `binary` — the rows bite hard here,
   one row per behaviour class pins the class (the 2026-08-16 layer-3
   argument, unchanged).

#### 2.1.3 The pin discipline

The stdlib source at the pin becomes a **trusted-ADJACENT input**: it
is not trusted (the machine's answer about a program is still
validated against `go run`), but its REV is load-bearing for
reproducibility — a different rev lowers different bodies. Rules:

- The source root is `deps/go/src` at `scripts/setup-deps`' `go` row
  (= the oracle `go version`); the frontend refuses to lower library
  units when the rev check fails (the same preflight the corpus runner
  applies to the oracle).
- A **library pin** is tracked: per lowered package, a hash of the
  lowered wire of its reached declarations under the conformance
  suites (Cerberus's `tests/libc/libc.core.sha256` is the precedent —
  Appendix C). It moves only with the oracle re-pin, with a written
  reason, alongside the full differential (CLAUDE.md gates).
- Stdlib DOC anchors: the docs ARE the doc comments in the pinned
  source, so no new checkout is needed; the anchor scheme is
  `godoc:<import path>.<Ident>@go1.26.5` resolving to the declaration's
  doc comment in `deps/go/src` (Appendix D). `docs/spec-sources.md`
  gains a "library docs" row stating this; the language-coverage
  ledger's grade vocabulary already has a DOCS class (the `sync` rows
  cite docs text) — this makes it a pinned truth source rather than an
  ad-hoc citation (G3).

#### 2.1.4 Is validating pinned source against the binary compiled from it circular? — No, and here is the argument

The differential claim is: **the machine's semantics of the LANGUAGE
constructs in a body agrees with gc's compilation of that body**, on
the observations the row exercises. When the body is `strings.Fields`
from `deps/go/src`, the row tests (i) the frontend's lowering of that
body and (ii) the interpreter's execution of the lowered constructs
(byte indexing, `append`, `unicode` table lookups, `utf8.DecodeRuneInString`'s
bit arithmetic) against gc's compiled version of the SAME text. That is
the same test the corpus runs on every fixture — with the difference
that the Go team wrote this fixture, and it is one real programs
actually call. Nothing about the library's DOCS is assumed; the oracle
could contradict us on any row.

What the differential does NOT establish — and did not before either —
is the UPPER bound: whether the pinned body is the weakest machine the
library DOCS permit. Source-through makes the machine realize gc's
member (§2.1.2); the shims did the same thing with a hand-written
member and a written argument per function. The honest difference:
under the shims the member was OURS (and could be wrong in ways the
rows did not enumerate — three audit-found bugs); under source-through
the member is gc's exactly, and the only remaining daylight is the
substitution/overlay sites, which are enumerated and byte-checked.

The residual circularity worth naming: go/types is the same type-
checker gc uses, and the frontend consumes its output (the A3-D2
common-mode channel, already recorded). Source-through adds no new
common mode.

#### 2.1.5 Cost, sessions ([AGENT] estimate)

- Loader root + rev check + reachability-pruned emission over a
  library unit + quarantine stubs for unlowerable members: **2–3
  sessions** (the loader, mono, quarantine and identity machinery all
  exist; the new part is the second root and the pruning walk).
- Substitution table (bytealg, math): **0.5 session**.
- Overlay mechanism (a per-package `golean_overlay.go` diffed against
  upstream at the pin, byte-check script): **1 session**.
- Init-order integration (a lowered stdlib package's real `$init`
  replacing its inittask placeholder at the same position, pinned by
  the existing multipkg init-order rows): **1 session**, risk of
  surprises in `unicode`'s table initialization cost.
- Per-package conformance and shim deletion (§3): **0.5–1 session per
  package**.

### 2.2 Option (B) — specified primitives

Keep a SMALL set of machine-level ops for what cannot go through
source, each with: a written spec pinned to the library docs anchor
(§2.1.3), a latitude-inventory entry if the docs grant latitude,
differential rows, and a refusal for every input outside the spec'd
domain.

**Where (B) is RIGHT:** language built-ins the spec names but leaves
implementation-specific — `print`/`println` (§4) — and behaviour the
machine already owns because the memory model defers to it (`sync`).
These are not library in the charter's sense; putting them in the
machine is putting Go semantics in the machine.

**Where (B) is WRONG:** any exported library function. An in-machine
`fmt.Sprintf` or `strings.Fields` op is the "override table consulted
by `stepFn`" the 2026-08-16 note rules out ("THE TCB CONSTRAINT … it
must never become a machine mechanism"), and it fails criterion (V):
the machine's answer for the op cannot be contradicted by `go run`
EXCEPT through the same rows the shims already had — with the
difference that the model now lives in the trusted core instead of
the frontend. The quorum-era `sortSlice` op is the one existing
instance, its justification already recorded as expired; §3 retires
it onto source-through `slices.Sort` (pdqsort at any ordered kind).

**The admission rule — "the second shim, done right".** The 2026-08-16
trigger failed because it named a threshold (2) with no owner, no
census, and no place the count was visible — it was outgrown 10× and
cited by nothing (A3-S1). The rule proposed here has three parts,
each mechanical:

1. **A tracked census file** (`docs/stdlib-boundary-register.md`, or a
   TSV under `tools/nativefrontend/`) listing every machine primitive,
   every substitution-table entry and every overlay function, with:
   the godoc anchor at the pin, the reason source-through fails for
   it, its validation rows, its latitude entry (or "none, exact").
   The file header carries the COUNT per class. `scripts/ci` fails if
   the code's tables and the register disagree (the same shape as
   `inittask-std.tsv`'s generated-header check).
2. **A hard cap per class** that requires a [USER] re-ratification to
   raise, recorded in the register: primitives (machine ops of library
   origin) cap **2** (`print`, `println` — `sync` and `sortSlice`'s
   successor are language/memory-model, listed but not counted);
   overlay functions cap **12**; substitution entries uncapped but
   each must name the upstream twin file (a substitution has no
   hand-written text).
3. **Fields-standard validation on every entry**: behaviour-class rows
   + a randomized entry-vs-upstream fuzz under the real runtime for
   pure functions (the 600k-trial pattern, `g2.md:739-746`) + the
   delta list restated. For overlay functions the fuzz is
   `overlay body` vs `upstream body` compiled side by side — the
   cheapest possible shape.

### 2.3 Option (C) — the hybrid (recommended)

#### 2.3.1 The shape

(A) for every pure or purifiable function, (B) only for `print`/
`println` and the memory-model-owned `sync`, plus the two small tracked
tables (substitution, overlay), plus the split treatment of `fmt`, plus
the out-of-scope list. §0 states it; the rest of this section argues
the parts that are not obvious.

#### 2.3.2 The two tables — why they are not "shims by another name"

A **substitution** swaps one upstream file for another upstream file of
the same package (`indexbyte_native.go` + `indexbyte_amd64.s` →
`indexbyte_generic.go`). No text is ours. The Go project maintains and
tests both files as implementations of one contract. The frontend's
build context is `GOOS=linux GOARCH=amd64` (the oracle's; L:R1's 64-bit
`int`) with an explicit file-level override list — NOT a synthetic
GOARCH (an unknown arch loses `internal/goarch`'s constants and every
`zgoarch_*.go`).

An **overlay** function IS our text — a diff against upstream — and is
therefore governed like a shim: counted, capped, Fields-validated. The
difference from injection is structural: the overlay lives at the
library's own path (`strings.Builder.String` stays
`strings.Builder.String` — no reserved names in the user's package, no
type-checker seeing a program the user did not write), it is expressed
as a diff whose base is byte-checked at the pin (so a re-pin that
changes the upstream body FAILS the check rather than silently
diverging), and its size is bounded by the census: **9 sites in 4 files
today** (§1.3), of which the four `internal/strconv` casts are one
overlay function each onto `math.Float64bits`-shaped machine ops that
`FloatBits.lean` already implements (the language has no float-bits
operation; `math.Float64bits` is the doc anchor; the machine's
softfloat port is the realization — an existing trusted component,
not a new one).

`abi.NoEscape(unsafe.Pointer(b))` in `Builder.copyCheck` is `b` — escape
analysis is not modeled (the shadow model already says so,
`importedmodel.go` FIDELITY notes). `bytealg.MakeNoZero(n)` is
`make([]byte, n)` — the non-zeroing is unobservable (the slice is
`[:len]`-truncated before use). `unsafe.String(unsafe.SliceData(b.buf), len(b.buf))`
is `string(b.buf)` — the aliasing is unobservable because `Builder`
never mutates `buf` after `String()` returns without the copy check
firing… except that it can (`WriteString` after `String()` appends in
place if capacity allows, and the returned string ALIASES; gc's string
does not change because `string` bytes are immutable at the language
level and the append writes beyond `len`). The overlay is faithful:
both produce the same bytes at `String()` time and neither mutates a
returned string.

#### 2.3.3 The `fmt` crux

`fmt`'s `%v` over an arbitrary value is reflection. The options, each
evaluated:

(i) **A machine-level `format` primitive over runtime values with a
pinned verb matrix** (what exists today, moved from frontend injection
into a spec'd machine op). Rejected on (N) and the TCB constraint: it
puts ~1,400 lines of library semantics into `stepFn`, every theorem
about a program that formats a value would quantify over it, and gc
could not contradict it except through the same rows. It would also
freeze the verb matrix into the trusted core, where widening it is a
trusted-surface change instead of a lowering change.

(ii) **Real `fmt` via a modeled `reflect` subset.** `reflect` is 8,694
lines with 42 linknames and 69 body-less declarations; `fmt` needs
`TypeOf`, `ValueOf`, `Kind`, `Len`, `Index`, `Field`/`NumField`/
`Type().Field(i).Name`, `MapRange` (via fmtsort), `IsNil`, `Elem`,
`Interface`, `CanInterface`, method lookup for `Stringer`/`error`/
`Formatter`. The machine HAS the dynamic type of every value
(`TypeId`, method sets, dynamic values — the interfaces campaign), so
a `reflect` subset as a MACHINE FACILITY (reflection is arguably
language-adjacent: it exposes the type system the spec defines) is
conceivable and would unblock `fmt`, `errors.Is/As`, `sort.Slice`,
`encoding/json`, `reflect.DeepEqual` (5 gotest rows) at once. It is a
LARGE design of its own (what `reflect` exposes of gc's layout —
`Size`, `Align`, `UnsafePointer` — is out of language; the subset must
be the layout-free one) and is posed as a gate (G6), not recommended
here.

(iii) **Split by call-site kind — recommended.** Static sites
(constant format, statically typed args — the raft subject's 89
`fmt.*` sites are predominantly of this kind; its logger's `[]any`
spreads are the dyn route) keep the emit-time specialization:
it is a FRONTEND lowering strategy (compile-time specialization of
`fmt` at the static types, the way gc's own `fmt` has a no-reflection
fast path for basic kinds) and has been validated by 46+25 rows and
the Formatter/precedence family. What changes: its leaf renderers stop
being hand-written injected text and become calls into the real
source-through `strconv` (`FormatInt`, `FormatUint`, `Quote`,
`QuoteToASCII`, `FormatBool`, `AppendFloat` for the float verbs that
are refused today) — deleting `goleanShimFmtUint/Int/Hex/Bool/Quote*`
and the `%q` non-ASCII bound at a stroke, and shrinking the hand-written
remainder to the rules that ARE `fmt`'s own (`handleMethods`
precedence, `%!verb(...)` error shapes, padding, composite layout),
each cited to `fmt/print.go` at the pin and — once `fmt` is a source-through package with a library-pin row — to `godoc:<fmt>.<Sprintf>@go1.26.5`-shaped anchors (the resolver refuses anchors into unpinned packages). Dynamic
sites (`[]any` spreads) keep the runtime type switch over basic kinds
and named-type Stringers; the reflective remainder (a struct or map
reaching a dynamic `%v`, `%T`, `%p`) REFUSES by name, as today. The
`Print*` family (`Printf`/`Println`/`Print`) becomes `Sprint*` +
`os.Stdout.Write` → requires the stdout observable of §4 and a
two-entry `os` primitive (`os.Stdout`/`os.Stderr` as the two output
streams; `os.Exit` as a termination status) — posed in G2/G7.

Where the `fmt` text lives after retirement: a library overlay package
is the wrong home (it would be a 1,000-line overlay, blowing the cap by
design). The honest home is `tools/nativefrontend/fmtdesugar.go` as a
LOWERING STRATEGY with NO injected Go text: helper functions it needs
beyond `strconv` are emitted as wire `Func`s directly (the way the
composite renderer already emits lifted `$fmtc<N>` functions), each
carrying its `fmt/print.go` line anchor. That keeps the count honest:
the register lists `fmt` as "frontend specialization, N emitted helper
shapes, 0 overlay functions".

#### 2.3.4 The out-of-scope list, with reasons

| package / feature | reason | how a call fails |
|---|---|---|
| `unsafe` | out of language (ledger §2; the doctrine's anti-goal: modeling gc's layout) | refused at the export (BUG-070 mechanism); inside library bodies → quarantine stub |
| `reflect`, `internal/reflectlite` | exposes layout and runtime metadata; a layout-free subset is G6 | package-selector refusal / quarantine stub |
| `runtime` | GC, finalizers, stacks, `Caller`s are not language behaviour; `GOMAXPROCS` would pin scheduling latitude; `Gosched` is a scheduling hint the L1 envelope already contains — G7 poses a two-entry no-op list (`GC`, `Gosched`) with `godoc` anchors stating "no observable effect absent finalizers/weak pointers" | refused by name |
| `os`, `io`, `io/fs`, `syscall`, `net`, `time` | no OS model; wall clock and I/O are outside the machine's observables; `os.Exit`/`os.Stdout`/`os.Stderr` are the three candidates for a spec'd primitive because they map onto observables the machine will have (§4) — G7 | refused by name |
| cgo, `//go:linkname` into `runtime`, assembly bodies | not Go source | quarantine stub (body-less declaration) |
| `sync.Pool`, `sync.Map`, `sync.Cond` (until Q-COND is implemented), `sync/atomic` (until the atomics arc lands — RULED A′) | runtime-internal or ruled-elsewhere | refused by name (sync design §7/§9) |
| `iter`, range-over-func, `maps` | coroutines via runtime linkname; FR-12 owns the language side | refused (FR-12) |
| `testing`, `log`, `flag`, `encoding/json`, `math/big` | dependents of the above | refused by import |
| GC-dependent behaviour (finalizers, weak pointers, `runtime.KeepAlive`) | the machine has no collector (D-001 posture: memory unbounded) | refused by name |

### 2.4 Option (D) — status quo plus

Keep the freeze; grow the allowlist function by function under
Fields-standard validation with a [USER] exception each time. Honest
baseline: it is what the raft push did for four weeks and it produced
a faithful-enough surface for one subject. What it costs: every new
function is hand-written text (the 20 → 30 → 50 curve), every one owes
a fuzz, the mechanism the [USER] ordered retired stays and grows, the
type-checker keeps checking a program the user did not write five ways
(A3-S1), and the gotest lever (`print`/`println`, 195 files) is
untouchable because it is not a shim at all. It unblocks the raft
harness's next ten functions and nothing structural.

### 2.5 Comparison

| | (A) source-through | (B) primitives | (C) hybrid | (D) status quo plus |
|---|---|---|---|---|
| gotest unblocked (of 1,013; [AGENT] estimates, §4 for print) | stdlib rows only: ~20–40 (strings/strconv/math/sort/utf8 singletons) — `print` untouched | `print`+fmt as ops: ~200–350 (the triage's own estimate for print), at the TCB cost | `print` primitive (169 simple-arg files + cascades) + stdlib source rows: **~200–350**, trusted-surface delta = one op family + schema fields | ~0–10 per session |
| trusted-surface delta | frontend only (loader root, pruning); wire unchanged; source at the pin trusted-adjacent | LARGE in-core growth (library tables in `stepFn`) | one machine op family (`print`), two observation fields, source trusted-adjacent | none (frontend text grows) |
| fail-closed | by construction (unlowerable → quarantine stub) | per-op domain checks | both | per-shim checks (three audit-found leaks on record) |
| differential validatability | mock = real (the daylight is the enumerated tables) | rows only; `go run` cannot contradict an in-core table beyond them | as (A) + print rows against gc's stderr | rows + fuzz per shim |
| upper-bound posture | gc's member of every doc envelope, RECORDED (§2.1.2) | each op's envelope written from the docs — the only option that can reify library latitude as choices | (A)'s posture + `print` as a (b)-pin | our member, argued per function |
| cost (sessions) | 5–7 to first three packages | 3–4 per primitive family incl. proof-side shape | (A) + 2–3 for print/observable | 0.5 per function |
| risks | interpreter speed on real bodies; init cost of `unicode`; re-pin churn in overlays | TCB growth; theorem statements quantify over library tables | the two above, smaller; the observable bump is an apparatus change touching every runner | mechanism keeps growing against a [USER] ruling |
| reasoning consumer sees | library `Func`s with bodies — specs are THEOREMS about them (§2.6) | opaque ops — specs are AXIOMS of the machine | bodies for library, axioms only for `print` | injected bodies under reserved names in the user's package (identity differs per program) |

### 2.6 The reasoning consumer: opaque specs vs inlined code

Both ways, honestly:

**For inlined code (source-through).** The consumer can prove a
specification of `strings.Fields` ONCE, about the library `Func` at the
pin, and reuse it at every call site through the call-span combinator
(2026-08-16 note layer 2, R5's P-H). The spec is then a theorem whose
truth rests on the machine's semantics of ordinary constructs — no
new axiom, no new trusted text. If the consumer has no spec yet, it
can still step through the body (expensive but complete). Costs: the
library `Func` bodies are large (pdqsort), so proving specs is real
work; and every oracle re-pin changes bodies, so proofs about them are
versioned artifacts (which the library pin makes explicit — the
consumer pins THIS repo, and this repo pins the source).

**For opaque specs (primitives).** The consumer reasons against a spec
the machine asserts; it is an axiom in exactly the sense the charter
forbids in `GoLean/` ("no axioms anywhere") — the machine op's
definition IS the spec, and its trust is the differential rows. It is
cheaper to consume (no body to step) and it is the only way to give
the consumer a LATITUDE envelope wider than gc's member (a `sort` op
whose spec is "a sorted permutation" lets the consumer prove things
that hold under any stable-or-not implementation). This is genuinely
more USEFUL for verification of the sort-using program — and is why
the quorum pilot chose `sortSlice`.

**Cerberus's answer** (Appendix C): libc is source-implemented (191
procs from 12 musl-derived TUs, elaborated like user code, linked from
a hash-pinned artifact) EXCEPT the memory-model and I/O primitives
(`malloc`/`free`/`memcpy`/`memcmp`/`printf`-family/FS ops ≈ 60 Core
proxies) — and unimplemented calls fail as link errors, not UB. For
verification, CN/refined-C-style tools then write SPECS for the libc
functions they call, proved or assumed per function. So Cerberus took
(C): source for what is expressible, primitives for what touches the
memory model or the outside world, fail-closed for the rest — and the
proof tools layer opaque specs on top by choice, not by necessity.

**The synthesis for this repo:** source-through gives the consumer the
STRONGER position (specs as theorems) and never precludes the weaker
one (the consumer may assume a spec and discharge it later). The place
where an opaque envelope is more useful — `sort` — is exactly a place
where the docs grant latitude, and the right move is not a machine op
but a LATITUDE ENTRY the consumer's spec can quantify over (G4). The
one true primitive family, `print`, needs no consumer spec beyond "the
output is this string" — and a `print` that is a machine op with a
`stderr` observable is also what makes program-level statements about
output possible at all.

---

## 3. The retirement plan for the current shims

Every row: the shim's fate under (C), what proves no corpus row moves,
and the rows expected to FLIP (FAIL→PASS flips are free; a
PASS→non-PASS flip must be on a BUGS.md Cases: line — none is
expected). The regression is the differential: the 197 baseline rows
of §1.1(e) re-run with the machine executing the REAL source where it
executed the shim, plus the `stdlib`-tagged consumer rows
(`examples/wordfreq` 15, `multipkg/errors-new` 3).

| # | shim (mechanism) | fate | validation / expected flips |
|---|---|---|---|
| 1 | `strings.Fields` (direct-call) | **source-through** — pure (ASCII fast path + `unicode.IsSpace` tables) | `strings/fields-conformance` 8 rows stay green; the 600k fuzz becomes moot (no mock); `unicode` table init cost measured |
| 2 | `strings.Join` | **source-through** via `Builder` (overlay #1–#3) | `join-conformance` 5 green; upstream's `"strings: Join output length overflow"` panic becomes real |
| 3 | `strings.Split` | **source-through** (`genSplit` → `Count`/`Index` → bytealg SUBSTITUTION) | `split-conformance` 7 green; the empty-separator refusal row FLIPS FAIL→PASS (`explode` is pure) — recorded delta retires |
| 4 | `strings.TrimSpace` | **source-through** — pure | `trimspace-repeat` rows green |
| 5 | `strings.Repeat` | **source-through** via `Builder` + chunking | the 1<<24 bound row FLIPS FAIL→PASS if the linear body fits fuel, else stays an honest budget refusal (re-expected with reason); BUG-073 closes |
| 6 | `errors.New` | **source-through** — pure (`*errors.errorString`) | `new-conformance` 6, `new-sentinel` 4, `multipkg/errors-new` 3 green; the dynamic-type-NAME delta retires (now exactly gc's) |
| 7 | `bytes.Equal` | **source-through** — `string(a) == string(b)` | `equal-conformance` 3 green |
| 8–10 | `strconv.{FormatUint,FormatInt,ParseUint}` | **source-through** (`internal/strconv`, overlay #4–#7 for the four float-bits casts — not reached by these three) | `format-parse` 7 green; the `*strconv.NumError` type delta, base-0 and bitSize refusals retire (the ParseUint delta row FLIPS) |
| 11–12 | `binary.LittleEndian.{Uint64,PutUint64}` (var-method desugar) | **source-through**; the desugar mechanism is replaced by the GENERAL lowering of a method call on an imported package variable of unexported type (a frontend generality gap, not a semantics gap) | `little-endian` 4 green; the mechanism deletes |
| 13 | `slices.SortFunc` (generic desugar) | **source-through** — `pdqsortCmpFunc` stenciled per E by `mono.go` | `sortfunc-cmp` 6 green; tie-order rows are tie-insensitive by design; R13 updated: the machine now realizes gc's member |
| 14 | `cmp.Compare` (generic desugar, int/string kinds) | **source-through** — pure generic, floats/NaN included | float exclusion retires |
| 15–20 | `fmt.{Sprintf,Errorf,Fprintf,Fprint,Sprint,Sprintln}` (desugar + 2 injected bundles) | **re-homed as a frontend specialization with NO injected text** (§2.3.3): leaf renderers → real `strconv`; `Errorf` → real `errors.New`; `Fprint*` writer set → real `Builder`/`Buffer` `WriteString`; dyn route keeps its basic-kind type switch as emitted helper `Func`s | `sprintf-verbs` 30, `v-composites` 22, `sprintf-dyn` 11, `errorf` 4, `fprint-writers` 3, `fprintf-builder` 2 green; `%q` non-ASCII bound rows FLIP; `sprintf-dyn/struct-bound` stays a by-design red until G6 |
| T1 | `strings.Builder` (shadow type) | **source-through + overlay** (`String`, `grow`, `copyCheck`'s NoEscape) | `builder-model` 7 green incl. the copy-panic row; `Cap`/`Grow` become real (capacity growth = allocator latitude → R-entry) |
| T2 | `bytes.Buffer` (shadow type) | **source-through** — pure | `buffer-model` 5 green |
| M | `sortSlice` machine op (`slices.Sort` at int kinds) | **retire onto source-through `slices.Sort`** (pdqsort at any ordered kind) — a MACHINE change: `Syntax.lean:269`, `Machine.lean:726/762/914`, `Ops.lean:2042-2062`, its eqb/sound twins, and the `sort-slice` wire node | the `slices/*` rows (11 files) green; `slices-sort-non-integer-refusal` FLIPS; R13 rewritten; own slice with `--diff`, after the library loader lands |
| H | `goleanShimUnsupported` / `goleanShimStringsRepeatBound` (force-quarantined refusal helpers) | **retained as frontend infrastructure** (they are the callable form of the H-3 quarantine, not library models) — renamed out of the `goleanShim` namespace | `panic-recover/shim-refusal-unrecoverable` 3 rows stay red-by-design (the unrecoverable-refusal contract) |
| F | `checkFormatterDynHole`, `refuseFormatter` (BUG-071 closures) | retained in the fmt specialization | `formatter-*` 7 rows stay red-by-design until G6 |
| D | the injection driver `injectStdlibShims`, `stdlibShimSources`, `stdlibShimDeclNames`, the reserved-name check, `harvestImportedModels` | **deleted** when their last consumer moves | `strings/shim-value-refused` 2 rows: the refusal string changes (the function VALUE `f := strings.Fields` becomes a real function value under source-through — FLIPS FAIL→PASS); BUG-072's phantom is moot |

**D-002 exit.** The exit condition is "the retirement design note +
its first implementation". This memo is the note; §6's slice deletes
shims 1, 3, 4, 8, 9, 10 (six of twenty) and lands the mechanism every
other row depends on. The freeze stays in force for the remaining
shims until each row above executes; the register (§2.2) replaces the
freeze as the standing rule when the last injected declaration is
gone.

---

## 4. `print` / `println` — the single biggest lever, argued

**Spec status.** spec#Bootstrapping (`deps/go/doc/go_spec.html:7928-7940`):
"Current implementations provide several built-in functions useful
during bootstrapping. These functions are documented for completeness
but are not guaranteed to stay in the language. They do not return a
result. … `print` prints all arguments; formatting of arguments is
implementation-specific; `println` like print but prints spaces
between arguments and a newline at the end." The ledger grades the
section out-of-language and §5.1 item 3 keeps them out of the queue
"by the spec's own sentence".

**Re-reading that sentence for the charter.** Two things are true at
once: (1) they ARE in the language — they are built-in functions the
spec defines, type-checked by go/types, present in 195 of the 1,013
real programs the triage ran; (2) their FORMATTING is implementation-
specific — which is exactly the (b)-pin class the latitude inventory
already holds for panic-payload rendering (R9) and abort lines (R10),
both realized by the SAME runtime printing code (`printpanicval` →
`print*` in `runtime/print.go`; the machine's `renderPanicPayload`,
`Machine.lean:1649-1660`, already renders gc's shapes for string, int,
bool and defined-int payloads and FAILS CLOSED elsewhere). "Not
guaranteed to stay in the language" is a version-tracking obligation
(the inventory's ARCH class), not an exclusion: the pin models Go 1.26,
where they exist. [AGENT] judgment: the §5.1 exclusion was a scoping
choice under the raft plan, and under "everything real Go code does"
it should be re-posed, not assumed.

**What the observable would be.** `print`/`println` write to file
descriptor 2 (`runtime/print.go:89-107` `gwrite` → `writeErr`),
atomically per statement (the compiler brackets each statement with
`printlock`/`printunlock`, `:60-87`). The machine's observation today
is `{status, values | message}` (`CLI.lean:397-420`); the harness
observes reflected return values and stray stdout is a LOUD parse
failure (p2 §10 — the strict decoder is what makes the current
"no output observable" safe). The model:

- The observation schema gains two REQUIRED byte-array fields,
  `stdout` and `stderr`, under a new schema tag
  (`golean-observation-v2`) so an old and a new observation can never
  be confused (fail-closed schema bump; `requireExactKeys` enforces
  it). The machine's `ExecState` gains two append-only byte buffers;
  `print`/`println` append to `stderr`.
- The oracle side: the coverage harness stops writing its JSON to
  stdout (`coverageharness/main.go:479-485`) and writes it to a file
  under its existing `--out` dir; `scripts/diff-coverage` captures the
  subject process's fd 1 and fd 2 separately into the two fields. This
  also closes p2 §10's recorded latent coupling (a subject printing a
  line beginning `panic: ` could spoof the extracted panic message):
  once program stderr is a COMPARED field rather than a stream the
  runner scans, the panic message must be taken from the harness's own
  status report, and a spoofed line simply shows up as a stderr
  inequality.
- Concurrency: output order across goroutines is scheduling latitude
  the L1 envelope already reifies; a multi-goroutine printer belongs in
  the membership lane (`observed ∈ modeled`), where the machine's set
  of possible `stderr` strings is enumerated like any other
  choice-dependent observable; strict-lane rows are single-goroutine.
  gc's per-statement atomicity means the machine's `print` is ONE step
  — matches by construction.
- The `.out`-golden gotest tests (34) become fully comparable; the 161
  no-`.out` tests compare status + EMPTY stderr on both sides — a
  strictly stronger check than today's status-only match.

**The formatting spec, pinned.** `runtime/print.go` at go1.26.5:
`printbool` → `true`/`false`; `printint`/`printuint` → decimal
(`strconv.RuntimeFormatBase10`); `printstring` → the bytes verbatim;
`printsp` = `" "`, `printnl` = `"\n"`; `println` inserts `printsp`
between arguments (probed this session: `println(true, "str", 'c', 42, -7, uint8(200))`
→ `true str 99 42 -7 200`; `print("a", 1, 2, "b\n")` → `a12b`).
Floats: `printfloat64` = `strconv.AppendFloat(buf, v, 'g', -1, 64)`
(shortest round-trip: probed `println(1.5, 0.1+0.2, 1e100, float32(1.5), 3.0)`
→ `1.5 0.3 1e+100 1.5 3`) — **a Go 1.26 change** (commit 9035f7ae,
2025-10-28 "runtime: use internal/strconv"; earlier releases printed
`+1.500000e+000`), which is precisely why the format is a version-
tracked (b)-pin and not a spec envelope. Complex → `(1+2i)`. Pointers,
maps, channels, funcs, slices (`[len/cap]0xaddr`) and interfaces
(`(0xtypeword,0xdata)`) print ADDRESSES — probed non-stable across
runs — which the machine cannot realize (it has no addresses): these
kinds REFUSE by name, permanently, like `unsafe`. That is 26 of the
195 files; 169 use only int/string/bool.

**Cost.** Slice A (ints/uints/bools/strings; refusal for every other
kind): one machine op family (`print`/`println` as wide statement ops
over evaluated operands, the `clearSlice` shape), the `ExecState`
buffers, the observation-schema bump on BOTH sides, the harness/runner
fd separation, the decoder, `observation-eq`, and the corpus rows
(~10 behaviour-class rows + 5 refusal pins): **2–3 sessions**, most
of it apparatus, all of it touching the trusted surface (a `--diff`
full run and a baseline re-pin with reason). Slice B (floats via the
shortest-repr algorithm): either a Lean port of `internal/strconv`'s
`ftoa` (Ryū-class, ~600 lines) or — the cheaper and gc-faithful-by-
construction route — lower `internal/strconv.AppendFloat` through
source-through and have the `print` op's float arm CALL it (a machine
op calling a library `Func` is a new shape; it would need its own
argument). Slice B is deferred until floats are demanded (12 files).

**Is a machine `print` charter-compatible?** [AGENT] yes, on three
grounds: it is language (spec#Bootstrapping), its latitude is of the
(b)-pin class the inventory already holds for the sibling runtime
printing paths, and it fails closed at exactly the kinds where gc's
output is an address. The genuine cost is not the op but the new
observable: it changes what EVERY differential row compares (empty
output on both sides for every existing row — a full run with a
written baseline re-pin reason). That is a [USER] decision (G2), not a
lane's.

---

## 5. Decision gates for the [USER]

Numbered, each with options, the [AGENT] recommendation, and its
grounds. None was decided at writing.

**RULED [USER] 2026-09-03 — G1–G9 each as recommended.** The quote,
relayed by the [AGENT] coordinator to the recording worker (citation,
not firsthand; full text and provenance chain in
`docs/2026-08-31_qrow-rulings.md`, 2026-09-03 ruling record): «(3)
agree, go ahead with the plan». Each gate below carries the ruling
line; the first implementation slice (§6) is implemented by a separate
lane.

**G1 — The retirement design.** Options: (A) source-through only, (B)
primitives only, (C) hybrid as shaped in §0/§2.3, (D) status quo plus.
Recommendation: **(C)**. Grounds: it is the only option that shrinks
the hand-written surface to an enumerated, capped set (9 overlay sites
+ 2 language primitives) while keeping library semantics OUT of the
trusted core; it unblocks the largest measured slice; Cerberus took the
same shape. RULED [USER] 2026-09-03 — as recommended.

**G2 — `print`/`println` as machine built-ins with a stderr
observable.** Options: (a) admit, with gc's pinned format for
int/uint/bool/string and by-name refusal for address-printing kinds
and (initially) floats/complex; (b) admit as effect-DISCARDED
evaluation with the runner flagging every such row `output-uncompared`
(no observable, honest but weaker); (c) keep refusing (§5.1 item 3
stands). Recommendation: **(a)**. Grounds: 195 gotest files, 169 of
them simple-kind; the (b)-pin class already exists (R9/R10); (b) makes
no differential claim about output and would be a permanent
`output-uncompared` asterisk on 195 rows. The observable bump is the
real cost and is why this is a gate. RULED [USER] 2026-09-03 — as recommended.

**G3 — The stdlib source and its doc comments become a pinned truth
source.** Options: (a) add a "library docs at the pin" row to
`docs/spec-sources.md` with the `godoc:` anchor scheme (Appendix D)
and grade library rows in the coverage ledger under the existing DOCS
class; (b) keep library docs unpinned (cite ad hoc, as the sync design
did). Recommendation: **(a)**. Grounds: the checkout is already pinned
(`go` row); only the anchor discipline is new; A3-P2/P5 already flag
unmechanized quotes as a C3/C4 debt. RULED [USER] 2026-09-03 — as recommended.

**G4 — Library latitude posture under source-through.** Options: (a)
record gc's realized member as a version-tracked (b)-pin per
doc-latitude point (R13 template), reify as a choice site only on
consumer demand; (b) reify every doc-latitude point as a choice site
up front (sort ties as an L-class choice; Builder capacity; float ulp).
Recommendation: **(a)**. Grounds: (b) is the doctrine's pure form but
each reification is a machine change with membership rows, and no
consumer has asked; (a) keeps the record honest and the door open. RULED [USER] 2026-09-03 — as recommended.

**G5 — `fmt`'s home.** Options: (i) machine `format` op; (ii) real
`fmt` over a modeled `reflect` subset; (iii) frontend specialization
at static sites with real `strconv` leaves, basic-kind runtime switch
at dynamic sites, reflective remainder refused. Recommendation:
**(iii) now**, with (ii) posed separately as G6. Grounds: (i) violates
the TCB constraint and (N); (ii) is a large design of its own; (iii)
deletes the hand-written renderers and their bounds while changing no
trusted surface. RULED [USER] 2026-09-03 — as recommended.

**G6 — A modeled, layout-free `reflect` subset as a machine facility
(future arc, not this memo's ask).** Options: (a) commission a design
memo (what `reflect` exposes of the type system vs of gc's layout;
which of `fmt`, `errors.Is/As`, `sort.Slice`, `encoding/json`,
`reflect.DeepEqual` it unblocks — 25 gotest rows directly, the
reflective `fmt` remainder indirectly); (b) declare `reflect`
permanently out of scope like `unsafe`. Recommendation: **(a), after
the first two slices land** — it is the next frontier behind `print`,
and the machine already has the dynamic-type facts; but it must not
ride this decision. RULED [USER] 2026-09-03 — as recommended.

**G7 — The three-entry `os`/`runtime` primitive list.** Options: (a)
admit `os.Exit(n)` (termination status = exit code, an observable R12
already keys on), `os.Stdout`/`os.Stderr` (the two output streams, as
`io.Writer`s whose `Write` appends to the §4 buffers — what makes
`fmt.Print*` lower as `Sprint*` + write), and `runtime.GC()`/
`runtime.Gosched()` as documented no-ops ("no observable effect absent
finalizers/weak pointers" / "yield" — the L1 envelope already contains
every yield) — each with a `godoc:` anchor and a register entry
counted against the primitive cap; (b) admit only the `os` trio; (c)
admit none. Recommendation: **(b)**, `runtime` deferred: `os.Exit` and
the two streams map onto observables the machine will have and are
demanded (11 + 53 gotest rows, 2 + 1 raft sites); `runtime.GC` as a
no-op is defensible but is the first entry of a list that has no
natural end (`SetFinalizer` is next and is NOT a no-op). RULED [USER] 2026-09-03 — as recommended.

**G8 — The admission rule and caps (§2.2).** Options: (a) adopt the
register + caps (primitives 2 language + G7's list if ruled, overlay
12, substitutions uncapped-but-named) with `scripts/ci` checking code
against register; (b) adopt the register without caps; (c) keep the
freeze as the only rule. Recommendation: **(a)**. Grounds: the
2026-08-16 rule failed for want of a place the count was visible and a
mechanical check; a cap without a check is that rule again. RULED [USER] 2026-09-03 — as recommended.

**G9 — The first slice (§6).** Options: (a) `strings`+`strconv`
source-through as proposed; (b) `print`/`println` first; (c) the
`fmt` re-homing first. Recommendation: **(a)**. Grounds: it is a real
instance of every mechanism in (C) except the observable, it deletes
six shims, its regression suite exists, and it touches no trusted
surface — the right order is mechanism first, observable second. RULED [USER] 2026-09-03 — as recommended.

---

## 6. The first implementation slice

**Name:** `stdlib-source-1` (worktree lane off `main`).

> **DONE 2026-09-03 ([AGENT], within G9 as ruled; landing SHA in the
> lane's commit — see `docs/evidence/2026-09-03_stdlib-source-1/`).**
> Mechanisms 1–7 landed as described below, with two recorded
> departures: (i) **shim 10, `strconv.ParseUint`, was NOT retired** —
> upstream's error path (`syntaxError`/`rangeError`) routes through
> `internal/stringslite.Clone`, whose body is
> `unsafe.String(&b[0], len(b))`: a reached `unsafe` site the impurity
> census in §1.3 did not list (it names `strings/builder.go`,
> `errors/join.go`, `internal/strconv/deps.go`, `slices.overlaps`).
> Retiring it before the overlay mechanism (slice 2) would have turned
> the green error-path rows into refusals (a PASS→non-PASS flip the
> gate forbids), so the shim stays, re-bodied to construct the REAL
> `*strconv.NumError` (the delta this memo called "unobservable" was
> observable: `*strconv.NumError` is exported). Frontier row:
> `stdlib-source/frontier/atoi-error-path-clone`; register:
> `docs/stdlib-admission-register.md`. (ii) The predicted flip of the
> "ParseUint-delta row" was the L-3 row `strconv/format-parse/
> unmodeled-member` (`strconv.Atoi("42")`) — it flipped because Atoi
> now lowers, not because of the error type. Unpredicted FAIL→PASS:
> `strings/shim-value-refused/unmodeled-value` (`strings.Contains` as a
> value lowers). Cost finding: a program reaching `strconv.Quote`
> (through `NumError.Error`) pays ~340 ms of `$pkginit` for the isPrint
> tables — a 15× per-subject slowdown on `strconv/format-parse` (24 →
> 360 ms), well inside the budget, recorded not re-budgeted.

**Scope.** Source-through for `strings.{Fields,TrimSpace,Split}` and
`strconv.{FormatUint,FormatInt,ParseUint}` from `deps/go/src` at the
pin, replacing shims 1, 3, 4, 8, 9, 10 (§3). Deliberately EXCLUDES
`Join`/`Repeat`/`Builder` (the overlay mechanism — slice 2, so that
slice 1 is a pure instance of loader + pruning + quarantine +
substitution with zero hand-written library text).

**Mechanisms exercised (each a real instance of §2.3):**

1. **Library source root in `load.go`**: `--stdlib-src <dir>` (default
   `deps/go/src`) with a rev check (`<dir>/../VERSION` must equal the
   oracle's `go version`; refusal names both). An import path resolves
   to a library source unit iff it is on the ALLOWED-LIBRARY list for
   this slice (`strings`, `strconv`, `internal/strconv`,
   `internal/stringslite`, `internal/bytealg`, `unicode`,
   `unicode/utf8`, `math/bits`, `errors` for `strconv`'s
   `ErrSyntax`/`ErrRange` — `errors.New` is pure; `io`/`iter`/`sync`
   imported by `strings` resolve to export data for type-checking
   only, their bodies absent → quarantine stubs). Anything else keeps
   today's refusal.
2. **Reachability-pruned emission** of library units from the
   program's roots, with the method-set completeness invariant (a
   reached type's exported methods are all on the wire — bodies for
   reached ones, stubs otherwise).
3. **Per-decl quarantine stubs** for every reached library declaration
   the pipeline cannot lower (`unsafe` sites, body-less declarations,
   `//go:linkname` targets) — `emit.go`'s existing H-3 path, with the
   stub's reason naming the library site (`strings.Builder.String:
   unsafe.String (library overlay pending — slice 2)`).
4. **The substitution table** (`tools/nativefrontend/stdlib-substitutions.tsv`,
   tracked): `internal/bytealg/{indexbyte,index,count,compare,equal}_native.go`
   + `.s` → the `_generic.go` twins; each row = upstream file pair +
   reason ("assembly on amd64; generic twin is the same package's
   portable implementation"). `math` rows land when `math` is allowed.
5. **The library pin**: `baselines/stdlib-pin.tsv` — per allowed
   package, the hash of its lowered reached-declaration wire over the
   conformance suites, plus the source rev; `scripts/ci` recomputes
   and fails on drift.
6. **Init integration**: `strings`, `strconv`, `unicode`'s real `$init`
   (package-level vars reached: `strings.asciiSpace`, `unicode`'s
   reached `RangeTable`s, `strconv`'s `ErrSyntax`/`ErrRange`) replaces
   the inittask placeholder at the SAME schedule position;
   `multipkg/init-order-{pruned,stdlib,tiebreak}` and BUG-060's rows
   guard it.
7. **Deletion**: the six shims' sources and table rows; the reserved-
   name entries; `stdlibShimAllowlist`'s `strings`/`strconv` maps
   (Join/Repeat stay until slice 2).

**Gate plan.**

- `scripts/ci` via `scripts/capped` with `--diff` (runtime change: the
  frontend is trusted lowering; `sortSlice` is untouched this slice).
- Expected baseline movement, all FAIL→PASS or refusal-string
  changes, each listed in the re-pin reason: `strings/split-conformance`
  empty-separator row (→ PASS), `strconv/format-parse` ParseUint-delta
  row (→ PASS: real `*NumError`), `strings/shim-value-refused/shimmed-value`
  (→ PASS: `f := strings.Fields` is a real function value), and
  `fixedbugs/issue19911`-class gotest rows (`strings.Index` now
  lowers). PASS→non-PASS: none expected; any that appears is a STOP
  (BUGS.md entry before any baseline change).
- Fidelity evidence at landing: the existing conformance rows (Fields
  8, Split 7, TrimSpace/Repeat 9, format-parse 7) green with the
  machine executing upstream text; plus a differential fuzz of the
  SAME shape as the Fields fuzz but now pointless for the mock
  argument — replaced by a **library-vs-oracle fuzz**: random inputs
  through `golean` on the lowered `strings.Fields` vs `go run` on the
  real one (this is the first time a fuzz can target the MACHINE's
  execution of the library rather than a Go-vs-Go mock check; 10k
  trials is enough to be evidence, the count is recorded).
- Interpreter cost measured: wall time of the conformance suites
  before/after; `unicode` table init cost reported in the slice log
  (a >2× slowdown is a finding, not a blocker).
- The gotest standing-lane trigger fires (a frontend fragment
  widening): full 1,013-case re-run, delta reported.
- Register + ledger updates: FR-14 narrows; `docs/spec-sources.md`
  gains the library-docs row (if G3 rules (a)); the latitude inventory
  gains nothing (no latitude in these six functions — exact);
  `docs/discrepancy-backlog.md` D-002 gains "first implementation
  landed <sha>" and its retirement condition's second half is met; the
  freeze text is amended to name the remaining 14 shims + 2 types by
  row of §3.
- The audit ask, unconditional; merge only on at-that-moment
  sign-off; push separate.

**Size:** M (3–4 sessions), one worker; the loader/pruning work is the
bulk, the rest is deletion and rows.

**Slice 2 (pre-announced, not scoped here):** the overlay mechanism
(`Builder` ×3, `errors.Join`, `internal/strconv` casts) + `Join`/
`Repeat`/`Builder`/`Buffer`/`errors.New`/`bytes.Equal`/`binary`/
`cmp.Compare`/`slices.SortFunc` → 14 more rows of §3, and the register
with its caps. **Slice 3:** `print`/`println` + the observable (G2).
**Slice 4:** `fmt` re-homing (G5) and `sortSlice` retirement.

---

## Appendix A — purity census (summary; raw output in the census file)

Method and program: `docs/2026-09-03_stdlib-boundary-design-census.md`
§A. `GOOS=linux GOARCH=amd64 CgoEnabled=false`, GOROOT =
`deps/go` at go1.26.5. "closure" = transitive imports (excluding the
root); asm/linkname/bodyless are SUMMED over the closure; "own" is the
package's own count.

| package | own .go / lines | own asm/linkname/bodyless | closure size | closure reaches unsafe / reflect(lite) / runtime |
|---|---|---|---|---|
| `cmp` | 1 / 77 | 0/0/0 | 0 | no / no / no |
| `unicode/utf8` | 1 / 578 | 0/0/0 | 0 | no / no / no |
| `unicode` | 5 / 10,335 | 0/0/0 | 0 | no / no / no |
| `container/list` | 1 / 235 | 0/0/0 | 0 | no / no / no |
| `internal/byteorder` | 1 / 149 | 0/0/0 | 0 | no / no / no |
| `math/bits` | 3 / 693 | 0/2/0 | 1 (`unsafe`, import for linkname) | yes / no / no |
| `internal/strconv` | 14 / 4,036 | 0/0/0 | 2 (`math/bits`, `unsafe`) | yes (4 casts) / no / no |
| `internal/bytealg` | 9 / 299 | 5/3/11 | 2 (`internal/cpu`, `unsafe`) | yes / no / no |
| `internal/stringslite` | 1 / 150 | 0/0/0 | 3 | yes / no / no |
| `math` | 53 / 6,016 | 5/1/8 | 3 (`internal/cpu`, `math/bits`, `unsafe`) | yes / no / no |
| `sync/atomic` | 4 / 768 | 1/0/41 | 1 | yes / no / no |
| `errors` | 3 / 362 | 0/0/0 | 32 | yes / **yes** (`Is`/`As`) / yes |
| `strconv` | 5 / 1,689 | 0/0/0 | 34 | yes / yes (via `errors`) / yes |
| `slices` | 5 / 1,799 | 0/0/0 | 32 | yes (`overlaps`) / no / yes (via `iter`) |
| `sort` | 5 / 1,457 | 0/0/0 | 35 | yes / **yes** (`Slice`) / yes |
| `strings` | 8 / 2,435 | 0/0/0 | 41 | yes (`Builder`) / yes / yes (via `sync`, `io`) |
| `bytes` | 4 / 2,211 | 0/1/0 | 41 | yes / yes / yes |
| `encoding/binary` | 3 / 1,214 | 0/0/0 | 46 | yes / **yes** (`Read`/`Write`) / yes |
| `fmt` | 5 / 3,547 | 0/0/0 | 60 | yes / **yes** (41 sites) / yes (`os`) |
| `io` | 3 / 1,089 | 0/0/0 | 37 | yes / yes / yes (`sync`) |
| `iter` | 1 / 473 | 0/2/2 | 30 | yes / no / **yes** (coroutines) |
| `sync` | 11 / 1,697 | 0/5/18 | 33 | yes / no / **yes** |
| `time` | 10 / 5,623 | 0/12/8 | 44 | yes / yes / yes (`syscall`) |
| `os` | 45 / 6,109 | 0/5/7 | 54 | yes / yes / yes (`syscall`) |
| `reflect` | — | 1/42/69 (8,694 lines) | — | — |
| `runtime` | — | 11/358/172 (88,404 lines) | — | — |

## Appendix B — the gotest censuses (summary)

From `artifacts/gotest/results.tsv` at 670d3351 (1,013 in-scope rows)
— program and raw output in the census file §B.

- `print`/`println`-refused files: **195** (186 direct + 9 method
  cascades); with `.out` golden: **34**; argument kinds: 169 files
  int/string/bool only; floats in 12; interfaces 7; complex 4;
  pointers 4; slices 3; maps 2; multi-value spreads 3.
- `fmt.*` by function: Printf 32, Sprintf 29, Println 21, Errorf 1.
- `runtime.*`: GC 18, SetFinalizer 10, GOMAXPROCS 9, Callers 6, Caller
  6, Stack 2, Gosched 2, ReadMemStats/NumGoroutine/NumCPU/FuncForPC 1.
- `os.*`: Exit 11, Args 4, Getenv 3, Stdout 1.
- Other: reflect 25 (TypeOf 10, ValueOf 6, DeepEqual 5, ArrayOf 2,
  StructOf/New/MakeFunc 1), math 12, time 6, atomic 4, sort.Ints 2,
  utf8 2, strings.Contains 3, strconv.Itoa 2, bytes.Compare 2,
  singletons listed in §1.1(a).

## Appendix C — Cerberus's libc split (read-only survey, [AGENT])

Surveyed at `/home/dev/projects/cerberus-lean-proj/cerberus-lean/`
this session (details relayed from a read-only sub-survey; paths
verified against the tree):

- **Source-implemented, elaborated like user code:** `runtime/libc/`
  — musl-derived, 15 `.c` + 120 `.h`; the dune rule builds `libc.co`
  from exactly 12 TUs (`ctype stdio stdlib string time utime unistd
  stat uio internal vfscanf signal`); the Lean side consumes a
  **hash-pinned** dump (`tests/libc/libc.core` = 191 `proc` + 68
  `glob`, `tests/libc/libc.core.sha256`) — the library-pin precedent.
- **Primitives:** `runtime/libcore/std.core` (~60 `proc [ailname=…]`
  proxies): `malloc`/`free`/`realloc`/`aligned_alloc` → memory-model
  actions; `memcpy`/`memcmp` → memops; `printf`/`vprintf`/`vsnprintf`
  → a Lem format-string interpreter (`frontend/model/formatted.lem`)
  writing to a driver-state `stdout : Dlist string`; POSIX FS ops → a
  SibylFS-style model; GCC builtins (`__builtin_ctz`, `bswap`, `ffs`)
  → `ocaml_frontend/ocaml_gcc_builtins.ml`. **printf is a primitive,
  not source-through of musl's `vfprintf`** — the same shape this memo
  proposes for `print` and declines for `fmt` (Cerberus's printf spec
  is C11 §7.21.6 text; `fmt` has no such text beyond godoc).
- **Stdout/stderr are first-class observables:** the batch result is
  `Defined {exit; stdout; stderr; blocked}` (`backend/common/driver_ocaml.ml:38,78-101`);
  `tests/libc_exec/` compares value + stdout + stderr between the OCaml
  oracle and the Lean port (7/7 MATCH).
- **Out of scope fails closed as a LINK error, not UB:** a call to a
  declared-but-undefined function raises `Errors.Unresolved_symbol`
  ("calling an unknown procedure") — the analogue of the H-3 quarantine
  stub. Unimplemented regions (`setjmp.h`, `threads.h`, `wchar.h`,
  multibyte `mbtowc` class) are header stubs or `assert(0)` sites.

## Appendix D — the stdlib doc anchor scheme (proposal for G3)

- Anchor: `godoc:<import path>.<Ident>[.<Method>]@<rev>` — e.g.
  `godoc:strings.Fields@go1.26.5`, `godoc:strconv.NumError.Error@go1.26.5` (a method); an anchor into a package the machine does not lower from the pin — `godoc:<sync>.<WaitGroup>.<Add>@go1.26.5` — is REFUSED by the resolver: only source-through packages (rows in `baselines/stdlib-pin.tsv`) are citable evidence.
- Resolution: the doc comment attached to the declaration in
  `deps/go/src/<import path>/*.go` at the pinned rev (via `go/doc` or
  `go/parser` + `ast.CommentGroup`); a resolver script
  (`scripts/check-godoc-anchors`, the `check-spec-anchors` shape)
  fails closed on an unresolvable anchor or a rev mismatch with the
  `go` row of `scripts/setup-deps`.
- Quote discipline: as for spec anchors, a quoted sentence beside the
  anchor; the resolver's job is resolution, quote fidelity rides the
  covmap question (A3-P2) unchanged.
- Latitude vocabulary in godoc text worth recognizing mechanically:
  "not guaranteed", "implementation-specific", "may", "unspecified",
  "undefined" — each occurrence in a lowered package's reached
  declarations is a candidate latitude row (the R13 shape) and the
  census could list them at re-pin time.
