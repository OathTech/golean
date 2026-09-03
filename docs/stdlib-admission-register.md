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
| overlay | OUR text at a library path, expressed as a diff against upstream at the pin (slice 2's mechanism — `strings.Builder.String`, `errors.Join`, `internal/strconv`'s float-bits casts, `internal/stringslite.Clone`) | **12** | [USER] re-ratification |
| primitive | a machine op of LIBRARY origin (`print`/`println` when G2's slice lands; `sync` and `sortSlice` are language/memory-model and are listed elsewhere, not counted) | **2** | [USER] re-ratification |
| shim | a RETAINED user-package injection (`stdlibshim.go` and the fmt/generic/var-method desugars) — frozen under D-002, retired row by row per memo §3 | frozen | n/a — shrinks only |
| shadow-type | an E5-T shadow model (`importedmodel.go`); `strings.Builder`/`bytes.Buffer` retire onto source-through + overlay in slice 2; the `sync/atomic` wrappers are the atomics arc's intrinsics | frozen | n/a |

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

### Caps — where they are enforced today (owed before slice 2)

The overlay (12) and primitive (2) caps are enforced INSIDE the
frontend's `--stdlib-register` dump (`stdlibregister.go`: an over-cap
table refuses to render, so `scripts/check-stdlib-register` fails) and
nowhere else: the caps bind the register's machine block, not the
emitter's behaviour at lowering time. Both tables are empty in slice 1,
so nothing is exposed; a ci-side assertion that the EMITTED wire carries
no overlay/primitive outside the register is OWED before slice 2 lands
its first overlay ([AGENT], audit fix round F12 — recorded, not deferred
silently).

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

## The machine block

Rendered by `GO111MODULE=off go run ./tools/nativefrontend --stdlib-register`
and compared byte-for-byte by `scripts/check-stdlib-register`. Do not
edit by hand: change the code table and re-render, in the same commit,
with the reason in the slice log above.

<!-- register:begin -->
```
class	entry	detail
count	source-through	9 (uncapped)
count	substitution	5 (uncapped; each names its upstream twin)
count	overlay	0 / cap 12
count	primitive	0 / cap 2
count	shim	14 (frozen, D-002; retired by rows of memo §3)
count	shadow-type	7
source-through	errors	errors.New for strconv's ErrRange/ErrSyntax package variables (pure); the user-facing errors.New SHIM is not retired this slice
source-through	internal/bytealg	the byte-search leaves strings.Index/Count/Split reach; assembly on amd64, swapped for the package's own *_generic.go twins by stdlib-substitutions.tsv
source-through	internal/strconv	strconv's implementation package; pure Go except deps.go's four float-bits casts (unreached by the integer paths; quarantine by name if reached)
source-through	internal/stringslite	strings/strconv's shared Index/Cut/Clone helpers; Clone uses unsafe.String (quarantines by name when reached)
source-through	math/bits	internal/strconv's formatBits uses bits.TrailingZeros; pure except the two runtime-linknamed error VALUES (poisoned by the linkname rule)
source-through	strconv	slice-1 target (FormatUint, FormatInt, ParseUint retired from shims); thin wrappers over internal/strconv; every Parse* ERROR path reaches internal/stringslite.Clone's unsafe.String and refuses by name (BUG-089 designed reds; overlay pending, slice 2 — the re-bodied-shim alternative was a D-002 exception DENIED by the [USER] 2026-09-03)
source-through	strings	slice-1 target (Fields, TrimSpace, Split retired from shims); pure Go at function granularity given the bytealg substitution — Builder stays the E5-T shadow model until slice 2's overlay
source-through	unicode	unicode.IsSpace and its White_Space RangeTable (strings.Fields/TrimSpace's non-ASCII path); pure tables, reached ones only
source-through	unicode/utf8	rune decoding used by strings' non-ASCII paths and explode; pure
substitution	internal/bytealg/indexbyte_native.go -> indexbyte_generic.go	IndexByte/IndexByteString are assembly on amd64 (indexbyte_amd64.s); the generic twin is the same package's portable implementation
substitution	internal/bytealg/index_native.go -> index_generic.go	Index/IndexString are assembly on amd64 (index_amd64.s). The generic twin's Index/IndexString/Cutover bodies are `panic("unimplemented")` placeholders (NOT implementations — the frontend quarantines such bodies by name, emit.go isUnimplementedPanicBody) and it declares `const MaxBruteForce = 0`; together with MaxLen == 0 (next row) every call site is DEAD: internal/stringslite/strings.go:42 (`n <= bytealg.MaxLen` false for n >= 2) and strings/strings.go:128,167,177 (same guard) never reach them, so strings.Index/Count/Split run the pure IndexByte + Rabin-Karp paths — the exact code gc compiles for the arches without an assembly Index
substitution	internal/bytealg/index_amd64.go -> index_generic.go	the amd64 file's init() sets MaxLen from CPU features (internal/cpu, AVX2: 63 or 31) — a machine-specific value. Dropping it leaves `var MaxLen int` (bytealg.go) at its ZERO value — index_generic.go declares NO init() — which is what makes the previous row's placeholder bodies unreachable and selects the portable brute-force/Rabin-Karp search path; the substitution does not add an init, it removes one (the register records this init difference)
substitution	internal/bytealg/count_native.go -> count_generic.go	Count/CountString are assembly on amd64 (count_amd64.s); the generic twin is the same package's portable implementation
substitution	internal/bytealg/compare_native.go -> compare_generic.go	Compare is assembly on amd64 (compare_amd64.s) and CompareString pulls runtime.cmpstring by linkname; the generic twin is pure Go (its own runtime_cmpstring linkname push is a body-less-free definition)
shim	bytes.Equal	direct-call shim (stdlibshim.go)
shim	cmp.Compare	generic desugar (genericshim.go)
shim	encoding/binary.LittleEndian.PutUint64	package-variable method desugar (fmtdesugar.go)
shim	encoding/binary.LittleEndian.Uint64	package-variable method desugar (fmtdesugar.go)
shim	errors.New	direct-call shim (stdlibshim.go)
shim	fmt.Errorf	fmt desugar (fmtdesugar.go)
shim	fmt.Fprint	fmt desugar (fmtdesugar.go)
shim	fmt.Fprintf	fmt desugar (fmtdesugar.go)
shim	fmt.Sprint	fmt desugar (fmtdesugar.go)
shim	fmt.Sprintf	fmt desugar (fmtdesugar.go)
shim	fmt.Sprintln	fmt desugar (fmtdesugar.go)
shim	slices.SortFunc	generic desugar (genericshim.go)
shim	strings.Join	direct-call shim (stdlibshim.go)
shim	strings.Repeat	direct-call shim (stdlibshim.go)
shadow-type	bytes.Buffer	E5-T shadow model (importedmodel.go); source-through + overlay pending (memo §3 rows T1/T2, slice 2)
shadow-type	strings.Builder	E5-T shadow model (importedmodel.go); source-through + overlay pending (memo §3 rows T1/T2, slice 2)
shadow-type	sync/atomic.Int32	E5-T shadow model whose methods lower to machine atomic-op intrinsics (atomics arc wave 1, atomics.go; sync/atomic is memory-model-owned, memo §2.3.4 — listed, not a source-through concern)
shadow-type	sync/atomic.Int64	E5-T shadow model whose methods lower to machine atomic-op intrinsics (atomics arc wave 1, atomics.go; sync/atomic is memory-model-owned, memo §2.3.4 — listed, not a source-through concern)
shadow-type	sync/atomic.Uint32	E5-T shadow model whose methods lower to machine atomic-op intrinsics (atomics arc wave 1, atomics.go; sync/atomic is memory-model-owned, memo §2.3.4 — listed, not a source-through concern)
shadow-type	sync/atomic.Uint64	E5-T shadow model whose methods lower to machine atomic-op intrinsics (atomics arc wave 1, atomics.go; sync/atomic is memory-model-owned, memo §2.3.4 — listed, not a source-through concern)
shadow-type	sync/atomic.Uintptr	E5-T shadow model whose methods lower to machine atomic-op intrinsics (atomics arc wave 1, atomics.go; sync/atomic is memory-model-owned, memo §2.3.4 — listed, not a source-through concern)
```
<!-- register:end -->
