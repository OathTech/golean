# stdlib source-through slice 2 (`stdlib-source-2`) — the overlay mechanism and the shim retirements (2026-09-03)

[AGENT] Worker record for the `stdlib-source-2` lane (design memo
`docs/2026-09-03_stdlib-boundary-design.md` §2.3.2 item 3 "a pinned
OVERLAY", §2.2 admission rule, §3 retirement rows 2, 5, 6, 7, 11–14, T1,
T2; the second implementation slice pre-announced at the end of §6).
Consuming docs (rule 8): the memo's §6 "SLICE 2 DONE" marker,
`docs/stdlib-admission-register.md` (class table, caps section, slice log,
machine block), `docs/discrepancy-backlog.md` D-002, `docs/BUGS.md`
BUG-089 (fixed) and BUG-073 (updated), `docs/language-coverage-ledger.md`
FR-14 / FR-21 and the red-by-design table, `docs/coverage-ledger.md`
(Standard library semantics row), `docs/2026-08-11_latitude-inventory.md`
(R2 note: Builder.grow rides the append-spill envelope; R13 note:
SortFunc realizes gc's pdqsort), the baseline re-pin header of
`baselines/native-full.tsv`, `baselines/stdlib-pin.tsv`,
`baselines/pins/twin-chdriver.wire.json`.

## Authorization (provenance, rule 7)

[USER] Mike, 2026-09-03, relayed to this worker by the [AGENT]
coordinator — NOT firsthand: «(3) agree, go ahead with the plan» (gates
G1–G9 AS RECOMMENDED; G8 = the register + caps: overlay 12, primitives 2)
and «(a) we're not running Raft right now, I think going red is simpler
and safer, and lets us do a clean retirement» (the ParseUint ruling: the
shim RETIRED, BUG-089's nine reds pending THIS slice's overlay). The pin
moves below (stdlib pin, twin wire) are authorized by G9 + ruling (a),
both relayed. Every other decision here is [AGENT], each argued at its
place: the `import` overlay rows' counting, the `Builder.grow` substitute,
the cmp.Compare STOP, the float-bits refusal, the fuzz and row sizing.

## Toolchain, tree, host (rules 3–5)

- Oracle: `go version go1.26.5 linux/amd64` = `baselines/go-oracle-pin`;
  `deps/go` at `c19862e5f8` (= go1.26.5), VERSION `go1.26.5`; host
  toolchain = the pin (the frontend refuses otherwise).
- Machine: `.lake/build/bin/golean` built by `scripts/capped lake build
  golean gocore-eval-tests` on this worktree (65/65 jobs, a cache hit
  from main — this slice changes NO Lean).
- Tree (rule 4): branch `stdlib-source-2` off main `221d8964` (the
  stdlib-source-1 train). Checkpoint commit `9fc4a4b7` = everything but
  the baseline re-pin and this README's gate section; every run below
  was made on the worktree at that content (the coverage metas say
  `git_dirty=true` where uncommitted). The OLD side of every before/after
  used the PRIMARY checkout's frontend at main `221d8964` (read-only;
  artifacts redirected into this worktree).
- Host: linux/amd64, shared box with other lanes' builds; wall times are
  ±1 s noisy and reported as such.

## What landed (the question this directory evidences)

Does the machine, executing the pinned GOROOT bodies of
`strings.Builder`, `strings.Join`, `strings.Repeat`, `errors.New`,
`errors.Join`, `bytes.Equal`, `bytes.Buffer`, `slices.SortFunc`,
`binary.LittleEndian.*` and the `strconv` Parse* ERROR paths — with ONE
pure-Go expression substituted for ONE unsafe expression at five named,
byte-checked sites — agree with `go run` on every row that used to
exercise the hand-written shims and shadow models, on the documented
edges the substitutions claim, and on a randomized Builder workload?

### The overlay mechanism (`tools/nativefrontend/stdlib-overlay.tsv`)

- Table columns: package, file, line, kind (`expr` | `import`), the
  upstream bytes, the substitute, the reason (semantic argument + the
  premise it rests on). Parsed by `parseStdlibOverlay` (stdlibsource.go)
  with one refusal per rule: 7 columns, all non-empty; line ≥ 1; package
  on the allowed list; bare `.go` file; kind ∈ {expr, import}; an `expr`
  substitute may not mention `unsafe`, `abi.`, `bytealg.`; an `import`
  row must be exactly `"p"` → `_ "p"` AND its file must have an `expr`
  row; old ≠ new; no duplicate site.
- Applied by `applyStdlibOverlay` in `parseLibrary`, AFTER the pin check
  hashed the upstream bytes: the recorded line must contain the recorded
  bytes EXACTLY ONCE (zero → "NOT on that line … the text under the
  overlay moved"; two → "ambiguous"; a short file → "only N line(s)"),
  else the unit refuses by site. Line-local, so every later row and every
  reported position keeps upstream's line numbers.
- Register: `count overlay 5 / cap 12` (`expr` rows) and
  `count overlay-import 5` (consequential, uncounted — [AGENT] decision,
  stated in the table header and the register; the [USER] may re-rule);
  one row per site with bytes, substitute and reason; the cap refuses to
  render at 13 (`TestStdlibRegisterDumpCaps`, red-first).
- The F12 owed ci-side assertion (slice 1): closed. `scripts/check-stdlib-register`
  now also runs `nativefrontend --stdlib-overlay-check`, which verifies
  EVERY row against the pinned checkout with no program (file selected
  under the oracle context and pinned; bytes present exactly once); the
  table is the single source for both the applied substitutions and the
  register's rows; any `unsafe` site not in the table keeps the by-name
  H-3 stub. Red-first: `TestStdlibOverlayMovedBytesRefuseByName`,
  `TestStdlibOverlayTableRules` (13 probes), `TestStdlibSourceUnsafeSiteQuarantinesByName`
  (Clone bodied; `slices.overlaps` still a named stub).

### The five sites (file:line — upstream bytes → substitute — premise, verified at the pin)

| site | upstream | substitute | premise / argument |
|---|---|---|---|
| `internal/stringslite/strings.go:149` (Clone) | `unsafe.String(&b[0], len(b))` | `string(b)` | `b` is a fresh local filled by `copy` and RETURNED here; nothing references it afterwards, so aliasing vs copying is unobservable; `len(s)==0` returns above the site. Reached by every strconv Parse* error path → BUG-089 closes. |
| `errors/join.go:58` (joinError.Error) | `unsafe.String(&b[0], len(b))` | `string(b)` | `b` local, built by appends, returned immediately; ≥ 2 elements on this path so `b` has ≥ 1 byte. |
| `strings/builder.go:47` (Builder.String) | `unsafe.String(unsafe.SliceData(b.buf), len(b.buf))` | `string(b.buf)` | upstream aliases; observable only if a byte below the current len is later overwritten — no Builder method writes below len (Write* only `append`, grow copies to a new array, Reset drops buf; `buf` unexported). Row `builder-overlay/string-stable-in-place` exercises the in-place append after String(). |
| `strings/builder.go:39` (copyCheck) | `(*Builder)(abi.NoEscape(unsafe.Pointer(b)))` | `b` | NoEscape is the identity on the pointer value (`unsafe.Pointer(uintptr(p)^0)`); escape analysis has no semantics in the machine; the following `b.addr != b` check compares the same pointer. Rows `copy-panics-after-grow`, `strings/builder-model/copy-panics`. |
| `strings/builder.go:67` (grow) | `bytealg.MakeNoZero(2*cap(b.buf) + n)` | `append([]byte(nil), make([]byte, 2*cap(b.buf)+n)...)` | MakeNoZero is body-less (runtime) with contract "len n, cap AT LEAST n, contents unspecified"; the substitute has len n, zeroed (unobservable: immediately resliced to [:len] and `copy`-filled; bytes beyond len are appended before any read), and a spec-latitude capacity realized as the machine's R2 append-spill CHOICE — which contains gc's size-class point for every n (gc probe: `builder-cap-gc-probe.tsv`). The idiom is upstream's own (`bytes/buffer.go` growSlice). Membership rows `builder-cap/*` (4). |

Import neutralizations (kind `import`, no semantics): `stringslite/strings.go:13`,
`errors/join.go:8`, `strings/builder.go:{8,9,11}` (`"unsafe"`,
`"internal/abi"`, `"internal/bytealg"` → blank imports; go/types refuses an
unused import).

### Sites refused or gated (not overlaid)

1. **`internal/strconv/deps.go:13–16` — the four float-bits casts:
   REFUSED, a PRIMITIVE admission posed, not self-admitted.** The memo
   (§2.3.2) planned them "onto `math.Float64bits`-shaped machine ops that
   `FloatBits.lean` already implements". Checked: `FloatBits.lean` is the
   softfloat kernel (fadd64/fmul64/…); `GoLean/GoCore/Syntax.lean` has no
   bit-reinterpretation node; `math.Float64bits` does not lower anywhere
   in `tools/nativefrontend`. A substitute would need a NEW machine op
   (a GoCore change this slice may not make) of library origin (the
   primitive class, cap 2, [USER]-gated at G7/G8), and no ruling so far
   covers it. `strconv.FormatFloat/ParseFloat/AppendFloat` stay red by
   name (`stdlib-source/frontier/format-float-unsafe`, FR-21).
   **Question for the [USER] (verbatim):** "Admit a `float-bits`
   primitive (float64⇄uint64 and float32⇄uint32 bit reinterpretation,
   the four `internal/strconv/deps.go` casts, docs anchor
   `math.Float64bits`/`Float64frombits`/`Float32bits`/`Float32frombits`),
   counted 1 of the 2 primitive slots, realized on the machine's existing
   float bit-pattern representation — or keep the float formatting paths
   refused until `print`/`println` (slice 3, which needs float printing
   too) forces the question?"
2. **`slices/slices.go:453–465` `overlaps`:** REFUSED as the memo says
   (unsafe.Sizeof + pointer arithmetic on element addresses; the machine
   has no address arithmetic to substitute). `slices.Insert/Replace`
   quarantine by name; row `stdlib-source/frontier/slices-overlaps`.
3. **`bytealg.MakeNoZero` at bytes' four sites** (`bytes.go:584,678,705,735`
   — Join, Repeat, ToUpper, ToLower): NOT overlaid this slice (the census
   named the strings site only; the four would spend 4 of the 7 remaining
   cap slots for members no corpus row needed). Row
   `stdlib-source/frontier/bytes-toupper-makenozero`.
4. **`io`-reporting library bodies** (`bytes.Buffer.Read/ReadByte/ReadRune/
   ReadBytes/ReadString`, `ReadFrom`, `WriteTo` reference `io.EOF` etc.;
   `io` is export-data only): quarantine by name per method; row
   `stdlib-source/frontier/buffer-readbyte-io`.

### Shims retired vs kept (memo §3 rows)

RETIRED (real source lowers; every prior row PASS — see Results):
`strings.Join` (2), `strings.Repeat` (5), `errors.New` (6, user-facing),
`bytes.Equal` (7), `binary.LittleEndian.{Uint64,PutUint64}` (11–12; the
package-variable method desugar MECHANISM deleted from fmtdesugar.go),
`slices.SortFunc` (13; `genericshim.go` deleted), shadow types
`strings.Builder` (T1) and `bytes.Buffer` (T2; `importedmodel.go` keeps
only the atomics wrappers). Source-through admitted for them: `bytes`,
`slices`, `cmp`, `encoding/binary` (init-pure arguments in the register).

KEPT — 7 shims:
- the `fmt` desugar's six (G5, slice 4 — out of this slice's scope); its
  bundle keeps `goleanShimErrorsNew` as `fmt.Errorf`'s constructor ONLY
  (recorded delta: `*main.goleanShimErrorString` vs `*errors.errorString`,
  unobservable without errors.Is/As — G6);
- **`cmp.Compare`'s kind-dispatch desugar — RETAINED by the slice's STOP
  rule (FINDING 1).** Retiring it flipped the GREEN row
  `slices/sortfunc-cmp/cmp-compare-kinds` red: the real generic
  `cmp.Compare[index]` at a FUNCTION-LOCAL defined type hits mono.go's
  naming refusal ("function-local defined type index as a type argument —
  gc renders these with a compiler-internal unique suffix … refused rather
  than guessed", audit response M3). The old desugar never instantiated
  anything (kind dispatch + converts), so it sidestepped the rule. The
  same gap already reds `slices/sortfunc-cmp/sortfunc-local-type`. The
  desugar lives in `cmpshim.go` unchanged in body (D-002 freeze intact);
  float call sites fall through to the REAL generic (`stdlib-source/cmp-compare/*`
  — the old float refusal is gone, `slices/sortfunc-cmp/float-compare-bound`
  green). **Decision posed to the [USER]:** retire it and take
  `cmp-compare-kinds` red on a BUGS Cases line (the ParseUint shape), or
  land the local-type instantiation naming first (a frontend generality
  arc), or keep the desugar.

## Results

### Differential — the shim/shadow suites stay green; BUG-089's nine flip

`scripts/coverage run --prefix <suite>` at the checkpoint: every row of
`noodler/strings` (19), `strings/join-conformance` (5),
`strings/trimspace-repeat` (10 — see repeat-bound-refused below),
`strings/builder-model` (7), `bytes/buffer-model` (5),
`bytes/equal-conformance` (3), `binary/little-endian` (4),
`slices/*` (all but the two pre-existing reds), `errors/new-conformance`
(6), `errors/new-sentinel` (4), `multipkg/errors-new` (3),
`fmt/fprint-writers` (5, its two pre-existing fmt-bound reds unchanged),
`fmt/fprintf-builder` (2), `fmt/errorf`, `fmt/sprintf-dyn` (its four
pre-existing reds unchanged), `interfaces/assert-imported-method-set`
(2), `panic-recover/shim-refusal-unrecoverable` (3),
`examples/wordfreq` (15), `quorum/committed-index-real` (17),
`noodler/frontier2` (22), `strconv/format-parse` (8),
`stdlib-source/*` (slice 1's 56) PASS.

FAIL→PASS (all free): the nine BUG-089 rows
`strconv/format-parse/parse-uint-{errors,range-value,bitsize}`,
`noodler/strings/parse-uint-edges`,
`stdlib-source/strconv-parseuint/{numerror-type,range-sentinel,error-texts,error-quoting,bitsize-saturation}`
(the real `*strconv.NumError` values, texts, `Unwrap` sentinels and quoting
now come from upstream text end to end), plus
`stdlib-source/frontier/atoi-error-path-clone`,
`slices/sortfunc-cmp/named-slice-bound` (real SortFunc takes `S ~[]E`) and
`slices/sortfunc-cmp/float-compare-bound` (real cmp.Compare at floats).
PASS→non-PASS: NONE at the landing tree. (During the slice
`cmp-compare-kinds` flipped and was flipped back by the STOP rule — the
finding above.) FAIL→FAIL with a changed stage:
`strings/trimspace-repeat/repeat-bound-refused` (frontend-export refusal
→ lean-observation 30 s timeout; BUG-073 updated — the real Repeat has no
golean bound; see the cost finding).

New rows (60, `Corpus/coverage/exec/stdlib-source/`): `builder-overlay`
11/11, `builder-cap` 4/4 (membership; every draw inside the enumerated
set, gc's point exhibited in each), `builder-fuzz` 10/10 (strict,
`depth=4096`), `errors-join` 8/8, `cmp-compare` 4/4, `slices-sortfunc` 8/8
(incl. `sortfunc-ties-realized`, the (b)-pin of gc's pdqsort tie order),
`bytes-buffer` 10/10, `binary-order` 5/5, `frontier` +3 born red by name
(`slices-overlaps`, `bytes-toupper-makenozero`, `buffer-readbyte-io`).

Two authoring corrections recorded: `builder-cap/grow-after-write` was
first pinned `members=139` from a derivation that forgot Grow's
"already fits" arm; the enumerator reported 112 (= [25,32] ∪ [30,136]) and
the row now carries the correct derivation. `sortfunc-ties-projected` and
`builder-overlay/grow-contract` first exceeded the strict lane's 10-pick
invariance streams (every Builder growth is a wide pick) and were
reshaped to pre-`Grow` once.

### The Builder fuzz — 10 × 300 operations, 0 mismatches (not the 100k asked)

`stdlib-source/builder-fuzz/*`: an in-program xorshift64* drives
WriteString/WriteByte/WriteRune (incl. RuneError-producing code points)/
Write/Grow/Len/String/Reset; every String()/Len() folds into an FNV-1a
hash; observation = (hash, final Len, String prefix). Strict rows with
`depth=4096` (six seeded invariance streams cover the thousands of wide
append-spill picks). **Sized by measurement, not by the brief:** the
brief asked for 100k operations; the machine's cost per subject rises
superlinearly (`append-cost-probes.tsv`: 100 ops 0.26 s, 300 ops 1.4 s,
600 ops 8.5 s, 1,000 ops 38 s — over the 30 s row budget), so the fuzz is
3,000 operations in total; the residual to the asked count is recorded,
not hidden.

### Interpreter cost (FINDING 2 — the in-place `append` cost)

`interpreter-cost.tsv` — golean `native-json-run` per subject, avg of 3,
old wire (main's frontend) vs new wire, same binary: every shim/shadow
row moved by +0–13 ms (the pdqsort stencils add ~10 ms and grow the
`slices/sortfunc-cmp` wire 110 KB → 1.37 MB); `parseUintErrors` went
unsupported → ok at 379 ms (slice 1's `strconv.Quote` table cost).

`append-cost-probes.tsv` — the finding: **an in-place `append` into
spare capacity costs O(cap) per call in the interpreter** (256 one-byte
appends 0.07 s; 512 0.26 s; 1,024 1.6 s; 2,048 10.8 s; 4,096 > 60 s;
`make`/`string()`/spilling `append` of 4 KB are instant). Consequences,
all recorded: Builder/Buffer workloads beyond ~1 KB exceed the 30 s row
budget; `strings.Repeat`'s 8 KB chunk-limit arm cannot be exercised;
`repeat-bound-refused` (16 MiB) is a runner-budget red; the fuzz is
10 × 300. No machine change was made (out of this slice's scope); the
remedy belongs to the interpreter's `appendSlice` in-place path and is
owed as its own arc.

### Pins (rule 7: [USER]-authorized by G9 + ruling (a), both relayed)

- `baselines/stdlib-pin.tsv`: 48 → 61 files (+13: `bytes` 4, `cmp` 1,
  `encoding/binary` 3, `slices` 5; no row removed).
- `baselines/pins/twin-chdriver.wire.json`:
  `45cd882a6e09c8942fbc5f2f774480af26b6703bbc4ad246d4b609f123c5deda` →
  `6a9ef8bb5ba80c4c7346a0ff18f7b7dd5601bf30fb2bd4dfbf3802906d5e23e3`
  (10.35 MB → 10.72 MB). `twin-structural-diff.txt` (producer: slice 1's
  `twin-structural-diff.py`, same normalizations and the same stated
  limits): funcs removed = exactly the 6 retired shim bodies
  (`quorum.goleanShimStringsRepeat{,Bound}`, `raft.goleanShimBytesEqual`,
  `raft.goleanShimLEPutUint64`, `raft.goleanShimLEUint64`,
  `raft.goleanShimStringsJoin`); funcs added = the 18 reached library
  functions (`bytes.Equal`, `strings.Join`, `strings.Repeat`,
  `math/bits.Mul*`/`Len*`, `slices.nextPowerOfTwo`, …); methods added =
  `bytes.Buffer.{empty,grow,readSlice,tryGrowByReslice}`,
  `encoding/binary.littleEndian.*` (12), `slices.xorshift.Next`,
  `strings.Builder.grow`; methods changed = the Buffer/Builder members
  (shadow-model bodies → real bodies, stubs → bodies) and the raft/
  confchange callers of the retired shims; globals added = `bytes.{ErrTooLarge,
  errNegativeRead,errUnreadByte}`, `encoding/binary.LittleEndian` (in gc's
  schedule slot between `unicode` and `strings`); types added =
  `encoding/binary.littleEndian`, `slices.{sortedHint,xorshift}`;
  `fileOrder` gains `cmp`, `slices`, `bytes`, `encoding/binary`. The
  deviation pin (`hidden-dep-order`) did NOT move.

### The gotest standing lane (trigger: a frontend fragment widening)

`gotest-delta.txt` (+ `gotest-results.tsv`, `gotest-results.meta.tsv`):
full 1,013-case run (`scripts/gotest-triage run --jobs 6`) at `4176f7f1`
vs the `stdlib-source-1` lane's record (its worktree's
`artifacts/gotest/results.tsv`, frontend @ `f02cf8e0` = main's
stdlib-source-1 train). Categories 344 MATCH / 637 FRONTEND-REFUSED /
11 MACHINE-REFUSED / 21 INFRA / 0 MISMATCH → **345 / 635 / 12 / 21 / 0**.
Transitions: `fixedbugs/issue19201.go` FRONTEND-REFUSED → MATCH
(`binary.BigEndian` as a value — the real `encoding/binary` package);
`fixedbugs/issue24419.go` FRONTEND-REFUSED → MACHINE-REFUSED
(its `defer bytes.Compare/Equal/IndexByte(nil, …)` calls inside
goroutines now lower instead of refusing at the frontend; the machine
run then hits the 30 s wall-clock timeout on that goroutine/defer/channel
shape — "did not decide", a cause-named budget stop, not a wrong answer;
the shape, not the library, is the cost). Of the 4 files whose OLD refusal named a
retired member or a slice-2 package, 2 stayed FRONTEND-REFUSED on their
NEXT cause (`fmt.Sprintf`; an anonymous struct embedding `*bytes.Buffer`).
LOST MATCH: none. MISMATCH: none. Honesty note: the two runs' base
commits differ only by this lane (the OLD record's frontend is the train
this branch forks from), so the delta is this slice's.

## Reproduction (rule 2; from the repo root, deps/go at the pin, golean built)

```
GO111MODULE=off go run ./tools/nativefrontend --stdlib-overlay-check      # every overlay row vs the pinned checkout
GO111MODULE=off go run ./tools/nativefrontend --stdlib-register           # the register's machine block
GO111MODULE=off go run ./tools/nativefrontend --stdlib-pin-manifest | diff - baselines/stdlib-pin.tsv
scripts/check-stdlib-register ; scripts/check-frontend-pins ; scripts/check-spec-anchors
(cd tools/nativefrontend && GO111MODULE=off go test .)                    # incl. the overlay red-first tests
scripts/coverage run --prefix stdlib-source                               # slice 1 + slice 2 suites
scripts/coverage run --prefix strings/builder-model   # and the other shim/shadow suites named above
python3 docs/evidence/2026-09-03_stdlib-source-1/twin-structural-diff.py <(git show 221d8964:baselines/pins/twin-chdriver.wire.json) baselines/pins/twin-chdriver.wire.json
# interpreter cost: emit each suite with the main-@221d8964 frontend and this one, then
.lake/build/bin/golean native-json-run --input <wire> --function <subject>   # timed, avg of 3 (interpreter-cost.tsv)
# append-cost-probes.tsv: the shapes listed in its rows, emitted with --dir and timed the same way
scripts/gotest-triage run --jobs 8 ; scripts/gotest-triage report
scripts/capped scripts/ci --diff                                          # the gate
```

## Gate result (rule 6)

Appended after the runs (below).
