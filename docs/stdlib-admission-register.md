# The stdlib admission register

**Status:** STANDING RULE for the standard-library boundary (memo
`docs/2026-09-03_stdlib-boundary-design.md` §2.2 "the second shim, done
right"; gate **G8 ruled AS RECOMMENDED** — [USER] Mike, 2026-09-03,
relayed by the [AGENT] coordinator, cited as relayed: «(3) agree, go
ahead with the plan»). Established by the first implementation slice
`stdlib-source-1` (2026-09-03, [AGENT]). It replaces the D-002 freeze as
the rule of record for the classes below when the last injected
declaration is gone; until then the freeze stays in force for the
retained shims (listed here so the count is visible).

## Why a register

The 2026-08-16 retirement rule ("a second shim triggers the design")
named a threshold with no owner, no census, and no place the count was
visible; it was outgrown 10× and cited by nothing (assessment A3-S1).
This file is the census, and `scripts/check-stdlib-register` (a
`scripts/ci` step) is the mechanical check: the fenced block below must
equal, byte for byte, what the frontend renders from its own tables
(`nativefrontend --stdlib-register`). A table widened in code without
this file fails the gate; so does a register claiming what the code
does not do. **Red-first verified** at landing: mutating one detail
column of the block made the check fail naming the line
(`docs/evidence/2026-09-03_stdlib-source-1/README.md`).

## Classes and caps

| class | what | cap | raising the cap |
|---|---|---|---|
| source-through | a standard-library package loaded from the pinned GOROOT source (`deps/go/src` @ go1.26.5) as a source unit, emitted reachability-pruned; NO text of ours | uncapped | admission = a row here with its reason and an **init-pure at the pin** argument (see below) |
| substitution | one UPSTREAM file swapped for another UPSTREAM file of the same package (`*_native.go` + `.s` → `*_generic.go`); no text of ours | uncapped | every row names its upstream twin (`tools/nativefrontend/stdlib-substitutions.tsv`) |
| overlay | OUR text at a library path: ONE pure-Go expression substituted for ONE unsafe (or runtime-implemented) expression at ONE named site, recorded in `tools/nativefrontend/stdlib-overlay.tsv` (package, file, line, the upstream bytes, the substitute, the semantic argument + its verified premise) and BYTE-CHECKED at every load — the recorded line must carry the recorded bytes exactly once or the unit refuses by site (slice 2, 2026-09-03: `internal/stringslite.Clone`, `errors.joinError.Error`, `strings.Builder.{String,copyCheck,grow}`). `internal/strconv`'s float-bits casts are NOT overlaid (see the slice log: a primitive admission, [USER]-gated) | **12** `expr` rows | [USER] re-ratification |
| overlay-import | the consequential neutralization of an import a file no longer uses once its `expr` rows apply (`"unsafe"` -> `_ "unsafe"`); no semantics; admitted only for a file that has an `expr` row (parser-enforced); an `expr` row may NOT target an import line (audit fix round F2), and after the rows apply no LIVE binding to `unsafe`/`internal/abi` or to a neutralized path may survive (post-hoc check); the overlaid package must type-check (`--stdlib-overlay-check`, F3) | **8** (own cap, enforced by the dump; the NUMBER is [AGENT]-provisional pending [USER] — 5 today + headroom for bytes' MakeNoZero import) | [USER] re-ratification |
| intercept | a source-through library member whose DIRECT CALL the frontend lowers to a machine op or a retained desugar instead of the library body. **EMPTY since 2026-09-04**: `cmp.Compare` → the kind desugar at integer/string type arguments RETIRED (lane `fr24`, per the [USER] ruling «(2) given we have a plan, I think this should be an honest red», relayed); `slices.Sort` → the `sortSlice` machine op RETIRED (lane `fr4-rowm`, memo §3 row M — the G1-G9 plan ruled «(3) agree, go ahead with the plan» [USER], relayed): the real generic at every ordered kind. ONE predicate (`interceptedLibraryCall`) still serves the reach walk and the emitter; `defer`/`go` of an intercepted member refuses by name (audit fix round F1) — dead code until a member is re-admitted, which is a widening of this frozen class | frozen at 0 (shrinks only) | n/a |
| primitive | a machine op of LIBRARY origin (`print`/`println` when G2's slice lands; `sync` is memory-model and listed elsewhere, not counted; the `sortSlice` op is unreferenced since row M — its deletion is the hygiene arc's) | **2** | [USER] re-ratification |
| shim | a RETAINED user-package injection (`stdlibshim.go` and the fmt desugar; the cmp.Compare kind-dispatch desugar `cmpshim.go`, retained by slice 2's STOP rule, RETIRED 2026-09-04 by [USER] ruling — 6 remain, all fmt) — frozen under D-002, retired row by row per memo §3 | frozen | n/a — shrinks only |
| shadow-type | an E5-T shadow model (`importedmodel.go`); since slice 2 only the `sync/atomic` wrappers (the atomics arc's intrinsics) — `strings.Builder`/`bytes.Buffer` RETIRED onto source-through + overlay | frozen | n/a |
| init-callee | an UNMODELED stdlib function a package-level initializer may CALL and still have the initializer SKIPPED with its declared vars poisoned per declaration (H-11's `pureUnmodeledCallees`, `emit.go`; the `$poisoned` cell + `globalAddr` refusal on every reference). A row is an ADMISSION with a written argument that the callee is result-only (no output stream, no filesystem, no process state, no argument referent mutated) and panic-free over the argument shapes `initializerEffectIsolated` admits — never a "not modeled yet" list (H-11 audit F1/F1b, 2026-08-20) | uncapped, each row argued | a row here with its argument; [AGENT] rows are flagged in the slice log for the [USER] |

Every source-through and substitution row owes **Fields-standard
validation** in the differential: behaviour-class rows in the corpus
(`Corpus/coverage/exec/stdlib-source/*` for slice 1) plus, for the
first library function through the loader, the library-vs-oracle fuzz
(`stdlib-source/fields-fuzz`, 500 inputs, generator
`tools/stdlibfuzz/fieldsgen`). The refusal register for what a
source-through package CANNOT lower is the frontier suite
`stdlib-source/frontier` (every detected gap is rowed — [USER]
direction 3, relayed).

### The init-pure-at-the-pin argument (per source-through package)

Reachability pruning drops an UNREACHED library variable's initializer,
calls included (`errors.errorType = reflectlite.TypeOf(...)`,
`strconv.ErrRange = errors.New(...)` when nothing reads them —
`tools/nativefrontend/stdlibreach.go`, INITIALIZERS). That is
unobservable iff the initializer has no effect beyond its own cell and
cannot panic. For every package admitted here both hold: the purity
census (memo §1.3, Appendix A, `docs/2026-09-03_stdlib-boundary-design-census.md`)
shows the closure reaches no OS, no output stream and no runtime hook
other than through `unsafe`/`reflectlite` sites that are themselves
pure type-metadata reads, and gc executes exactly these initializers at
every `go run` of every program importing the package — a panicking or
printing one would have shown on every differential row. A future
package whose initializers DO have effects (`os`, `time`, `log`,
`flag`, `testing`) must not be admitted on this argument; it needs the
G7 primitive route. This is NOT "unmodeled means effect-free" (the
refuted H-11 reasoning, audit F1 2026-08-20): it is a census fact about
nine named packages, re-checked at every re-pin by the purity census.

### Caps — where they are enforced (slice 2 closed the F12 owed item)

The overlay (12 `expr` rows) and primitive (2) caps are enforced INSIDE
the frontend's `--stdlib-register` dump (`stdlibregister.go`: an
over-cap table refuses to render, so `scripts/check-stdlib-register`
fails; red-first test `TestStdlibRegisterDumpCaps`). Slice 1 recorded
an OWED ci-side assertion that the EMITTED wire carries no overlay
outside the register (audit fix round F12). Slice 2 closes it
structurally and mechanically: (i) the overlay table
`tools/nativefrontend/stdlib-overlay.tsv` is the SINGLE SOURCE both for
what the loader applies (`applyStdlibOverlay`, at parse time, after the
pin check hashed the upstream bytes) and for the register's overlay rows
(the dump renders the same table), so a substitution the register does
not list cannot be applied; (ii) `scripts/check-stdlib-register` also
runs `nativefrontend --stdlib-overlay-check`, which re-verifies EVERY
row against the pinned checkout with no program in hand (file selected
under the oracle context and pinned; the recorded bytes present exactly
once at the recorded line), so a stale or fabricated row fails the gate
even if no corpus program reaches it; (iii) any `unsafe` site the table
does not cover keeps the by-name H-3 quarantine (`emit.go`, the
library-body `unsafe.` arm), so a row that failed to apply could never
present as a lowered body. Red-first at landing: `TestStdlibOverlayMovedBytesRefuseByName`
(a mutated Builder.String row refuses naming `strings/builder.go:47`),
`TestStdlibOverlayTableRules` (one probe per parser rule).
The primitive table is still empty (print/println is slice 3).

### Residual channels (recorded)

- **Host export data.** The library units' unmodeled imports
  (`internal/cpu`, `internal/abi`, `internal/reflectlite`, `io`, `sync`,
  `iter`) are type-checked from the HOST toolchain's export data
  (`importer.Default()`), not from the pinned checkout's text. The
  frontend refuses unless `runtime.Version()` equals the oracle pin
  (`stdlibsource.go` `checkHostToolchainPinned`, audit fix round F4),
  which closes the rev half; the content half — export data is the
  compiled host's view — remains a channel. The one place a host-layout
  fact could enter the model through it, `internal/bytealg/bytealg.go`'s
  `unsafe.Offsetof(cpu.X86…)` constants, is unreached (and would refuse
  the export through the reached-decl unsafe scan if it were).
- **The bytealg substitution changes init.** Dropping `index_amd64.go`
  drops its `init()` (MaxLen from CPU features); `index_generic.go`
  declares none, so `internal/bytealg.MaxLen` stays 0 — this is what
  makes the placeholder `panic("unimplemented")` bodies of the generic
  twin unreachable (`stdlib-substitutions.tsv` rows 2–3 state the
  argument; `emit.go` `isUnimplementedPanicBody` quarantines any such
  body by name should a call ever reach one).
- **Library initializers that do not lower** (`errors.errorType =
  reflectlite.TypeOf(...)`, reached through errors.Is/As) are quarantined
  per declaration — the var poisoned, its readers H-3 stubs — under the
  same init-pure argument; never a whole-export refusal.

## Slice log

- **2026-09-03 `stdlib-source-1`** ([AGENT], within G9 as ruled):
  `strings`, `strconv`, `internal/strconv`, `internal/stringslite`,
  `internal/bytealg`, `unicode`, `unicode/utf8`, `math/bits`, `errors`
  admitted as source-through; 5 substitution rows (all
  `internal/bytealg`); shims RETIRED: `strings.Fields`, `strings.Split`,
  `strings.TrimSpace`, `strconv.FormatUint`, `strconv.FormatInt`,
  `strconv.ParseUint` (memo §3 rows 1, 3, 4, 8, 9, 10) — 14 shims remain.
  ParseUint: upstream's error path reaches `internal/stringslite.Clone`'s
  `unsafe.String` (a site the memo's census did not list); the lane first
  RETAINED the shim re-bodied to construct the real `*strconv.NumError`
  (a body change under the D-002 freeze plus a new shim→library import
  coupling, `stdlibShimImports`) and posed it as a D-002 exception. **The
  exception was DENIED** — [USER] Mike, 2026-09-03, relayed by the [AGENT]
  coordinator (cited as relayed): «(a) we're not running Raft right now, I
  think going red is simpler and safer, and lets us do a clean
  retirement». ParseUint therefore lowers from source like the rest; its
  ERROR-path rows are [USER]-directed designed reds on BUG-089's Cases
  line pending the slice-2 overlay for `Clone`; `stdlibShimImports` is
  GONE; the freeze is intact — no shim body changed. Other reached-
  library refusal classes rowed at the audit fix round —
  `stdlib-source/frontier/{index-rune-goto,format-float-unsafe}`,
  `stdlib-source/errors-wrap/{is,as}` (ledger FR-21) — so the register
  claims exactly what lowers: every reached member of the nine packages
  that is free of `unsafe`, linkname pulls, placeholder bodies,
  `internal/reflectlite`, and FR-11's goto shape. Overlay 0/12, primitive
  0/2. Evidence: `docs/evidence/2026-09-03_stdlib-source-1/`.

- **2026-09-03 `stdlib-source-2`** ([AGENT], within G1/G8/G9 as ruled
  and the 2026-09-03 ParseUint ruling — [USER] Mike, relayed by the
  [AGENT] coordinator, cited as relayed: «(a) we're not running Raft
  right now, I think going red is simpler and safer, and lets us do a
  clean retirement»). **The OVERLAY mechanism landed**: `stdlib-overlay.tsv`,
  5 `expr` rows (of the cap of 12) + 5 consequential `import` rows,
  byte-checked at every load: `internal/stringslite.Clone` (`string(b)`
  — closes BUG-089's nine designed reds, FAIL→PASS), `errors.joinError.Error`
  (`string(b)`), `strings.Builder.String` (`string(b.buf)`),
  `strings.Builder.copyCheck` (`b` for `abi.NoEscape(unsafe.Pointer(b))`),
  `strings.Builder.grow` (`append([]byte(nil), make([]byte, 2*cap(b.buf)+n)...)`
  for `bytealg.MakeNoZero(…)` — MakeNoZero's documented "capacity of at
  least n" realized as the language's own append-spill latitude, the
  machine's R2 envelope, which contains gc's size-class point; membership
  rows `stdlib-source/builder-cap/*`). Every row's semantic argument and
  its premise (verified over the callers at the pin) is in the table and
  rendered below. **NOT overlaid, refused by name**: `internal/strconv/deps.go`'s
  four float-bits casts — the memo (§2.3.2) planned them "onto the
  machine's FloatBits", but the machine has NO float-bits op reachable
  from the wire (FloatBits.lean is the softfloat kernel; `Syntax.lean`
  has no bit-reinterpretation node and `math.Float64bits` does not
  lower): realizing them is a PRIMITIVE admission (cap 2, [USER]-gated),
  which the rulings so far did not cover — posed in the slice-2 evidence
  README, not self-admitted; `stdlib-source/frontier/format-float-unsafe`
  stays red on FR-21. `slices.overlaps` (unsafe.Sizeof + pointer
  arithmetic) REFUSED as the memo says (row `stdlib-source/frontier/slices-overlaps`).
  **Source-through admitted**: `bytes`, `slices`, `cmp`, `encoding/binary`
  (init-pure arguments in each row below; `slices.Sort` stayed the
  `sortSlice` machine op via `frontendInterceptedLibraryMembers` until
  memo §3 row M landed 2026-09-04, lane `fr4-rowm`). **Shims RETIRED**: `strings.Join`, `strings.Repeat`,
  `errors.New` (user-facing), `bytes.Equal`, `slices.SortFunc`,
  `binary.LittleEndian.{Uint64,PutUint64}` (the package-variable method
  desugar mechanism deleted), and the two E5-T shadow types
  `strings.Builder`/`bytes.Buffer` (memo §3 rows 2, 5, 6, 7, 11, 12, 13,
  T1, T2). **Shims RETAINED — 7**: the fmt desugar's six (G5, slice 4; its
  bundle keeps `goleanShimErrorsNew` as `fmt.Errorf`'s constructor only —
  a recorded delta, `*main.goleanShimErrorString` vs `*errors.errorString`,
  unobservable without errors.Is/As), and `cmp.Compare`'s kind-dispatch
  desugar (`cmpshim.go`) by the slice's STOP rule: retiring it flipped the
  GREEN row `slices/sortfunc-cmp/cmp-compare-kinds` red — the real generic
  instantiated at a FUNCTION-LOCAL defined type hits mono.go's naming
  refusal (audit response M3: "refused rather than guessed"), the same gap
  that already reds `slices/sortfunc-cmp/sortfunc-local-type`; a frontend
  generality gap, not a cmp gap — posed to the [USER] (README). The
  strings.Repeat shim's golean-invented 1<<24 output bound went with it:
  `strings/trimspace-repeat/repeat-bound-refused` (16 MiB) is now a
  RUNNER-BUDGET red (the machine cannot materialize 16 MiB of bytes in
  30 s; the runner names the timeout) — BUG-073 updated. Overlay 5/12,
  overlay-import 5, primitive 0/2, shim 7, shadow-type 5. Pins moved:
  `baselines/stdlib-pin.tsv` 48 → 61 files (the four new packages);
  twin wire `45cd882a…` → `6a9ef8bb…` ([USER]-authorized G9 + ruling (a),
  relayed; structural diff in the evidence dir; RE-DERIVED at the round-10
  merge train 2026-09-04 over main 1b8401c0 as `f2309df2…` → `69a538de…` —
  the same structural delta on top of q-trylock's TryLock stub,
  `twin-pin-round10-hashes.txt`). Evidence:
  `docs/evidence/2026-09-03_stdlib-source-2/`.

- **2026-09-04 `stdlib-source-2` AUDIT FIX ROUND** ([AGENT]; verdict
  FIX-FIRST, no wrong answer found). F1: `defer`/`go` of a frontend-
  intercepted member refuses by name (one predicate for the reach walk and
  the emitter; rows `stdlib-source/sort-op-shapes/*`). F2/F3/F6: overlay
  guards hardened — expr rows barred from import lines, post-hoc live-
  binding check, the overlaid package type-checked inside
  `--stdlib-overlay-check`, every row must apply. F7: the `intercept` class
  above (2 rows). Import-row cap 8 ([AGENT]-provisional). F5: the cost
  finding re-derived → **BUG-090** (assoc-list heap, allocation-count
  quadratic). **Gates recorded for the [USER], both views verbatim, not
  decided:** (i) float-bits primitive — worker: posed (see the slice-2
  README); auditor: «ADMIT, with the condition that it preserve NaN
  payloads exactly (deps.go:29 builds nan() from payload
  0x7FF8000000000001) and ±0 / quiet/signaling round-trip probes». (ii)
  cmp.Compare desugar — worker: posed (retire onto a Cases-line red, land
  the local-type naming first, or keep); auditor: «KEEP (C6 in ledger §5.1
  is a ratified impossibility so the red would be permanent; the shim
  intercepts EVERY int/string Compare call site, not just the local-type
  row … it masks C6 for int/string kinds only, a float local type still
  refuses — an asymmetry to row)» — rowed: `stdlib-source/cmp-compare/local-float-type`;
  coordinator: «FR-19's plan (scope-qualified TypeId key with gc-spelled
  rendered name) may make C6 revisitable». Counts after the round:
  overlay 5/12, overlay-import 5/8, intercept 2, primitive 0/2, shim 7,
  shadow-type 5.

- **2026-09-04 `fr22-fr23`** ([AGENT]; ledger FR-22/FR-23, [USER]
  direction 3 relayed): the `init-callee` class is added to this
  register — the H-11 allowlist `pureUnmodeledCallees` was the ONE stdlib
  admission table the register did not render (a table widened in code
  without this file would have passed the gate). Its two founding rows
  (`os.Getenv`, `os.LookupEnv`) are listed with their argument; ONE row
  added, `time.Date` — result-only (constructs a `Time`; its doc comment at the pin,
  deps/go/src/time/time.go @ go1.26.5, normalizes out-of-range values —
  `time` is not source-through, so no `godoc:` anchor is available), panic-free over the admitted
  shapes (its only panic is a nil `Location`; the predicate admits the
  Location position only as an exported non-source package variable —
  `time.UTC`/`time.Local`, non-nil at the pin — and refuses untyped `nil`
  and every source-declared pointer). This is the cedar-go census's
  first kill (`types/datetime.go:16,19`). No shim, overlay, primitive or
  source-through change; the `time` package itself stays a design-memo
  question (specified primitive vs source-through). The FR-22 re-run also
  found `encoding/binary`'s "unreached sync.Map" reachable through
  `binary.Write` (ledger FR-24) — the row text above is unchanged (it is
  the register's INIT-PURE claim, which still holds; the kill is a TYPE
  refusal at `collectGlobals`, rowed with its plan).
- **2026-09-04 (lane `fr24`, checkpoints A–C; `docs/evidence/2026-09-04_fr24-fr25/`).**
  (A) FR-24: the `encoding/binary` row re-worded — `structSize sync.Map`
  is POISONED per declaration when reached (the `$poisoned` cell; every
  reader an H-3 stub naming it), no longer a whole-export kill; the
  init-pure claim unchanged — and, audit fix round L6: `structSize` is the
  ONLY live library var of an unlowerable type in the admitted set today
  (zero-valued, no initializer), so the "library initializer skipped
  without the isolation test" exposure FR-24's doc comment names has no
  instance; a future one is a row here first. (B) FR-25: no table moved.
  (C) **cmp.Compare
  desugar RETIRED — [USER] Mike 2026-09-04, relayed by the [AGENT]
  coordinator (cited as relayed): «(2) given we have a plan, I think this
  should be an honest red».** `cmpshim.go` deleted with its three kind
  shims (`goleanShimCmpCompare{Uint,Int,String}`), the `intercept` row and
  the `stdlibGenericDesugarInject` entry gone (table kept, EMPTY);
  `cmp.Compare` is the real generic at every type argument. Consequence,
  taken as ruled: `slices/sortfunc-cmp/cmp-compare-kinds` (a function-
  local `index` type argument) goes RED on mono.go's C6 naming refusal —
  FR-19's line (plan: the scope-qualified TypeId key), BUGS.md BUG-092
  Cases line; every OTHER cmp.Compare row stays green through the real
  generic (verified row by row at the checkpoint). The raft twin pin MOVES
  (quorum's `majority.go` calls cmp.Compare inside `MajorityConfig.Describe`,
  an H-3 quarantined stub — the ONLY wire change is the three dead injected
  kind shims leaving; 0 added, 0 changed): re-pinned 69a538de → b4458244
  with the structural diff in the evidence dir. Counts: intercept 2 → 1, **shim 7 →
  6 (the fmt desugar's six); the D-002 freeze is intact — no retained body
  changed.**

- **2026-09-04 `fr4-rowm` — memo §3 row M DONE: the `slices.Sort` intercept
  RETIRED** ([AGENT] worker; the G1-G9 stdlib plan ruled «(3) agree, go
  ahead with the plan» [USER], relayed by the coordinator and cited as
  relayed; posture «break rather than preserve incorrect behaviour»).
  `emit.go`'s `emitSortStmt` and the ExprStmt intercept are gone; the
  `frontendInterceptedLibraryMembers` table is EMPTY (class frozen at 0,
  the predicate and the `defer`/`go` refusal kept as dead machinery); the
  reach walk therefore marks the real `slices.Sort` reached and mono.go
  stencils `Sort` → `pdqsortOrdered` per element type — gc's exact member
  at EVERY ordered kind (ints as before, now via the real generic; strings;
  floats with NaN-first and ±0 by `cmpLess`; named kinds; inside an
  `init()`, cedar-go's shape). The `sortSlice` machine op and the
  `sort-slice` wire node are UNREFERENCED by the frontend — not deleted
  here (no `GoLean/GoCore` change on this lane; the decoder key stays, no
  wire-schema change); their removal is owed to the hygiene arc. Rows:
  `slices/slices-sort-non-integer-refusal` FLIPS green (its refusal no
  longer exists), `stdlib-source/sort-op-shapes/{defer-sort,go-sort}` FLIP
  green (nothing is intercepted, so the deferred/spawned FUNCTION VALUE is
  the real generic with its closure on the wire), every existing
  `slices.Sort` row stays green byte-for-byte, and `slices/slices-sort-kinds/*`
  are born (string, float NaN/±0, float32, named string/float kinds, a
  >12-element pdqsort path, `init()`). The raft twin pin MOVES (quorum,
  tracker, raft and raftpb call `slices.Sort` at uint64 kinds — 9 sites;
  `tracker/progress.go`'s call is inside an H-3 quarantined body): the `sort-slice` nodes become static calls to the `slices.Sort[…]`
  stencils and the pdqsort closure joins the wire — a ruled consequence of
  row M, re-pinned with the structural diff in
  `docs/evidence/2026-09-04_fr4-rowm/twin-repin/`. D-002 unchanged (no
  retained shim body involved). Counts: intercept 1 → **0**; shim 6; the
  `slices` source-through row re-worded; `tools/lowerdiag`: the static
  `slices-sort-kind` check removed (the member is judged source-through),
  the `slices-sort-kind`/`intercepted-defer-go` cause rows kept as
  "NONE remains" so a reappearance classifies by name.

## The machine block

Rendered by `GO111MODULE=off go run ./tools/nativefrontend --stdlib-register`
and compared byte-for-byte by `scripts/check-stdlib-register`. Do not
edit by hand: change the code table and re-render, in the same commit,
with the reason in the slice log above.

<!-- register:begin -->
```
class	entry	detail
count	source-through	13 (uncapped)
count	substitution	5 (uncapped; each names its upstream twin)
count	overlay	5 / cap 12 (expr sites, stdlib-overlay.tsv; byte-checked at every load)
count	overlay-import	5 / cap 8 (consequential import neutralizations of overlaid files; no semantics; own cap, [AGENT]-provisional pending [USER])
count	intercept	0 (library members whose direct call the frontend lowers to a machine op or a retained desugar instead of the library body — stdlibreach.go frontendInterceptedLibraryMembers, one predicate for reach walk and emitter)
count	primitive	0 / cap 2
count	shim	6 (frozen, D-002; retired by rows of memo §3)
count	shadow-type	5
count	init-callee	3 (H-11 pureUnmodeledCallees: unmodeled stdlib functions a package-level initializer may call and still be SKIPPED with its vars poisoned; each row states result-only + panic-free over the admitted argument shapes; a row is an admission, not a model)
source-through	bytes	slice-2 target (Equal retired from shim; Buffer retired from the E5-T shadow model — pure Go, its growth idiom `append([]byte(nil), make([]byte, c)...)` is the overlay's model); ReadFrom/WriteTo reach `io` (export data only) and quarantine by name; init-pure: three errors.New sentinels + the asciiSpace table
source-through	cmp	slice-2 target; Compare is the REAL generic at EVERY type argument since 2026-09-04 (lane fr24: the retained integer/string kind-dispatch desugar RETIRED per the [USER] ruling «(2) … an honest red», relayed — a function-local defined type argument now refuses at mono.go's C6 naming rule, rows slices/sortfunc-cmp/cmp-compare-kinds + stdlib-source/cmp-compare/local-float-type on FR-19's line; NaN arm included); pure, no imports; init-pure: no package-level state
source-through	encoding/binary	slice-2 target (LittleEndian.Uint64/PutUint64 retired from the package-variable method desugar — the exported vars and their unexported receiver types lower as ordinary library declarations); Read/Write/Size are reflect and refuse by name (export data); init-pure: two errors.New sentinels, zero-valued ByteOrder vars, a sync.Map (structSize, dataSize's cache) reached whenever Write/Read/Size is — its TYPE does not lower, so the var is POISONED per declaration (`$poisoned` cell; dataSize and every reader an H-3 stub naming the var, its type and the cause — ledger FR-24, PARTIALLY CLOSED 2026-09-04, lane fr24; the init-pure claim itself holds: the var has no initializer)
source-through	errors	errors.New (slice 2: the user-facing SHIM retired — every errors.New is the real *errors.errorString), Join (its unsafe.String OVERLAID), Unwrap; Is/As reach internal/reflectlite and refuse by name (FR-21 → G6)
source-through	internal/bytealg	the byte-search leaves strings.Index/Count/Split reach; assembly on amd64, swapped for the package's own *_generic.go twins by stdlib-substitutions.tsv; MakeNoZero (body-less) is overlaid away at its one strings caller
source-through	internal/strconv	strconv's implementation package; pure Go except deps.go's four float-bits casts — a bit reinterpretation the language has no operation for and the machine has no op for (a PRIMITIVE admission, [USER]-gated; NOT overlaid in slice 2): FormatFloat/ParseFloat/AppendFloat quarantine by name (FR-21 row stdlib-source/frontier/format-float-unsafe)
source-through	internal/stringslite	strings/strconv's shared Index/Cut/Clone helpers; Clone's unsafe.String is OVERLAID to string(b) (slice 2, byte-checked)
source-through	math/bits	internal/strconv's formatBits uses bits.TrailingZeros, strings.Repeat uses bits.Mul, slices uses bits.Len; pure except the two runtime-linknamed error VALUES (poisoned by the linkname rule)
source-through	slices	slice-2 target (SortFunc retired from the generic desugar — pdqsortCmpFunc stenciled per element type by mono.go, gc's exact member incl. tie order); Sort is the real generic too since memo §3 row M landed 2026-09-04 (lane fr4-rowm: the sortSlice MACHINE OP intercept retired — pdqsortOrdered stenciled per element type at EVERY ordered kind, NaN-first at floats; the intercept class is empty); Insert/Replace reach `overlaps` (unsafe.Sizeof/pointer arithmetic) and refuse by name — REFUSED, not overlaid (FR-21 row stdlib-source/frontier/slices-overlaps); iter-typed members are unreached unless called; init-pure: no package-level initializers
source-through	strconv	slice-1 target (FormatUint, FormatInt, ParseUint retired from shims); thin wrappers over internal/strconv; the Parse* ERROR paths reach internal/stringslite.Clone, OVERLAID in slice 2 (BUG-089's nine designed reds closed)
source-through	strings	slice-1 target (Fields, TrimSpace, Split retired from shims); slice 2: Join, Repeat and the Builder TYPE retired from shim/shadow model — Builder's three unsafe sites (String, copyCheck's NoEscape, grow's MakeNoZero) are OVERLAID (stdlib-overlay.tsv); pure Go at function granularity given the bytealg substitution
source-through	unicode	unicode.IsSpace and its White_Space RangeTable (strings.Fields/TrimSpace's non-ASCII path); pure tables, reached ones only
source-through	unicode/utf8	rune decoding used by strings' non-ASCII paths and explode; pure
substitution	internal/bytealg/indexbyte_native.go -> indexbyte_generic.go	IndexByte/IndexByteString are assembly on amd64 (indexbyte_amd64.s); the generic twin is the same package's portable implementation
substitution	internal/bytealg/index_native.go -> index_generic.go	Index/IndexString are assembly on amd64 (index_amd64.s). The generic twin's Index/IndexString/Cutover bodies are `panic("unimplemented")` placeholders (NOT implementations — the frontend quarantines such bodies by name, emit.go isUnimplementedPanicBody) and it declares `const MaxBruteForce = 0`; together with MaxLen == 0 (next row) every call site is DEAD: internal/stringslite/strings.go:42 (`n <= bytealg.MaxLen` false for n >= 2) and strings/strings.go:128,167,177 (same guard) never reach them, so strings.Index/Count/Split run the pure IndexByte + Rabin-Karp paths — the exact code gc compiles for the arches without an assembly Index
substitution	internal/bytealg/index_amd64.go -> index_generic.go	the amd64 file's init() sets MaxLen from CPU features (internal/cpu, AVX2: 63 or 31) — a machine-specific value. Dropping it leaves `var MaxLen int` (bytealg.go) at its ZERO value — index_generic.go declares NO init() — which is what makes the previous row's placeholder bodies unreachable and selects the portable brute-force/Rabin-Karp search path; the substitution does not add an init, it removes one (the register records this init difference)
substitution	internal/bytealg/count_native.go -> count_generic.go	Count/CountString are assembly on amd64 (count_amd64.s); the generic twin is the same package's portable implementation
substitution	internal/bytealg/compare_native.go -> compare_generic.go	Compare is assembly on amd64 (compare_amd64.s) and CompareString pulls runtime.cmpstring by linkname; the generic twin is pure Go (its own runtime_cmpstring linkname push is a body-less-free definition)
overlay	internal/stringslite/strings.go:149	`unsafe.String(&b[0], len(b))` -> `string(b)` — Clone: `b` is a fresh local `make([]byte, len(s))` filled by `copy` and RETURNED through this expression — nothing holds `b` afterwards (the only later reference is this return), so the aliasing `unsafe.String` avoids one copy and nothing else; `string(b)` yields the identical bytes. `len(s) == 0` is handled above the site, so `&b[0]` never indexes an empty slice. Reached by every strconv Parse* error path (syntaxError/rangeError/baseError/bitSizeError) — closes BUG-089's nine designed reds. godoc:strings.Clone@go1.26.5 is the idiom's exported twin.
overlay	errors/join.go:58	`unsafe.String(&b[0], len(b))` -> `string(b)` — joinError.Error: `b` is a local `[]byte` built by `append`s from the elements' Error() texts and RETURNED through this expression; no later reference exists, so the aliasing is unobservable and `string(b)` is byte-identical. `len(e.errs) >= 2` on this path (the single-element case returns above), so `b` has at least one byte ('\n') — `&b[0]` is in range, as the upstream comment on the preceding line states.
overlay	strings/builder.go:47	`unsafe.String(unsafe.SliceData(b.buf), len(b.buf))` -> `string(b.buf)` — Builder.String: upstream ALIASES buf's backing array as the returned string; `string(b.buf)` copies the same len(b.buf) bytes. The alias is observable only if a byte in [0, len(b.buf)) is later overwritten — and no Builder method ever writes below the current len: Write/WriteByte/WriteRune/WriteString only `append` (writes at index >= len at that moment, possibly into spare capacity the returned string does not cover), grow copies into a NEW array, Reset drops buf; `buf` is unexported, so no user code reaches it. Hence every string String() ever returned keeps its bytes under both bodies. nil buf: unsafe.String(nil, 0) == "" == string([]byte(nil)). Premise (no write below len) verified over every method of builder.go at the pin.
overlay	strings/builder.go:39	`(*Builder)(abi.NoEscape(unsafe.Pointer(b)))` -> `b` — Builder.copyCheck: abi.NoEscape is the IDENTITY on the pointer value (paraphrasing internal/abi/escape.go at the pin: the body converts p to uintptr, XORs with 0 and converts back) whose only purpose is to hide `b` from gc's escape analysis (issue 23382); escape analysis has no semantics in the machine (no stack/heap distinction is observable), so `b.addr = b` is the same store. The copy check that follows (`b.addr != b` panics) compares the stored pointer, which is identical.
overlay	strings/builder.go:67	`bytealg.MakeNoZero(2*cap(b.buf) + n)` -> `append([]byte(nil), make([]byte, 2*cap(b.buf)+n)...)` — Builder.grow: MakeNoZero(n) is a runtime-implemented leaf (body-less; runtime/slice.go bytealg_MakeNoZero) whose DOCUMENTED contract is "a slice of length n and capacity of AT LEAST n bytes" with unspecified contents. The substitute is the same contract in the language: `make` gives len n zeroed, and the spilling `append` gives a capacity the spec leaves to the implementation ("sufficiently large", spec#Appending_and_copying_slices) — the machine's R2 append-spill CHOICE envelope [newLen, max(32, 2*growth)], which contains gc's size-class rounding for every n: below 32 bytes the floor 32 covers every class; above, the worst size-class step is 48/33 = 1.45 and the page-rounding regime (> 32 KiB) at most 1.25, both < 2 (latitude inventory R2; membership rows stdlib-source/builder-cap/*). Contents: the result is immediately resliced to [:len(b.buf)] and `copy` fills exactly that prefix; bytes beyond len are written by a later `append` before any method can read them (String/Len read only [0,len)), so zeroed-vs-uninitialized is unobservable. The same idiom is upstream's own in bytes/buffer.go growSlice (`append([]byte(nil), make([]byte, c)...)`).
overlay-import	internal/stringslite/strings.go:13	`"unsafe"` -> `_ "unsafe"` — consequential: the file's only `unsafe.` use is the line-149 site; go/types refuses an unused import.
overlay-import	errors/join.go:8	`"unsafe"` -> `_ "unsafe"` — consequential: the file's only `unsafe.` use is the line-58 site.
overlay-import	strings/builder.go:8	`"internal/abi"` -> `_ "internal/abi"` — consequential: the file's only `abi.` use is the line-39 site.
overlay-import	strings/builder.go:9	`"internal/bytealg"` -> `_ "internal/bytealg"` — consequential: the file's only `bytealg.` use is the line-67 site.
overlay-import	strings/builder.go:11	`"unsafe"` -> `_ "unsafe"` — consequential: the file's `unsafe.` uses are the line-39 and line-47 sites.
shim	fmt.Errorf	fmt desugar (fmtdesugar.go; memo §2.3.3 / G5 — slice 4 re-homes it; its bundle keeps goleanShimErrorsNew as Errorf's error constructor only)
shim	fmt.Fprint	fmt desugar (fmtdesugar.go; memo §2.3.3 / G5 — slice 4 re-homes it; its bundle keeps goleanShimErrorsNew as Errorf's error constructor only)
shim	fmt.Fprintf	fmt desugar (fmtdesugar.go; memo §2.3.3 / G5 — slice 4 re-homes it; its bundle keeps goleanShimErrorsNew as Errorf's error constructor only)
shim	fmt.Sprint	fmt desugar (fmtdesugar.go; memo §2.3.3 / G5 — slice 4 re-homes it; its bundle keeps goleanShimErrorsNew as Errorf's error constructor only)
shim	fmt.Sprintf	fmt desugar (fmtdesugar.go; memo §2.3.3 / G5 — slice 4 re-homes it; its bundle keeps goleanShimErrorsNew as Errorf's error constructor only)
shim	fmt.Sprintln	fmt desugar (fmtdesugar.go; memo §2.3.3 / G5 — slice 4 re-homes it; its bundle keeps goleanShimErrorsNew as Errorf's error constructor only)
shadow-type	sync/atomic.Int32	E5-T shadow model whose methods lower to machine atomic-op intrinsics (atomics arc wave 1, atomics.go; sync/atomic is memory-model-owned, memo §2.3.4 — listed, not a source-through concern)
shadow-type	sync/atomic.Int64	E5-T shadow model whose methods lower to machine atomic-op intrinsics (atomics arc wave 1, atomics.go; sync/atomic is memory-model-owned, memo §2.3.4 — listed, not a source-through concern)
shadow-type	sync/atomic.Uint32	E5-T shadow model whose methods lower to machine atomic-op intrinsics (atomics arc wave 1, atomics.go; sync/atomic is memory-model-owned, memo §2.3.4 — listed, not a source-through concern)
shadow-type	sync/atomic.Uint64	E5-T shadow model whose methods lower to machine atomic-op intrinsics (atomics arc wave 1, atomics.go; sync/atomic is memory-model-owned, memo §2.3.4 — listed, not a source-through concern)
shadow-type	sync/atomic.Uintptr	E5-T shadow model whose methods lower to machine atomic-op intrinsics (atomics arc wave 1, atomics.go; sync/atomic is memory-model-owned, memo §2.3.4 — listed, not a source-through concern)
init-callee	os.Getenv	reads the ambient environment — permanently outside the machine's world (no shim can model it); result-only, never panics (founding row, H-11 2026-08-20)
init-callee	os.LookupEnv	reads the ambient environment — permanently outside the machine's world; result-only, never panics (founding row, H-11 2026-08-20)
init-callee	time.Date	constructs a Time value from its arguments (the time.Date doc comment at the pin, deps/go/src/time/time.go @ go1.26.5: out-of-range values are normalized, never rejected); result-only in the oracle-visible sense — no output stream, no process state, no argument referent mutated — with ONE transitive READ disclosed: Date -> loc.lookup -> (*Location).get -> localOnce.Do(initLocal) when loc == time.Local, and initLocal reads the TZ environment variable and /etc/localtime (zoneinfo_unix.go @ the pin); a read is not an effect any oracle observes, and initLocal cannot panic (every error path falls back to UTC); panic-free over the admitted argument shapes: Date's only panic is a nil Location, and the Location position can only be an exported non-source package variable (time.UTC or time.Local, both non-nil at the pin) — untyped nil and every source-declared expression of pointer type are refused. SCOPE NOTE: foreignPackageValue admits ANY exported variable/constant of ANY non-source package in ANY argument position, so what closes this row is its enumeration of the callee's own behaviour on such inputs, not the predicate (FR-22 row, 2026-09-04 [AGENT]; cedar-go census 2026-09-03 §3.2: `types/datetime.go:16,19`; argument amended at the audit fix round, item 1)
```
<!-- register:end -->
