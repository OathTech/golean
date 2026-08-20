# Raft W4.0 campaign log — the export unblock

Lane: `raft-w4` (worktree `.claude/worktrees/raft-w4`), supervised arc under
the standing merge/audit protocol. Charter: harness design
(`docs/2026-08-20_machine-twin-harness-design.md`) §8's W4.0 slice — the two
measured export blockers (H-9, H-10) plus H-11's package-level-var quarantine —
then the post-W4.0 census. Owns frontend, `Corpus/`, `baselines/`,
`raftsubject/`, `tools/raftsubject/`, and this log.

Base: `main` @ `422e9aa3`. Predecessor: `docs/raft-w3-log.md` (the gap census
this slice consumes: H-9/G-2/G-3 rows). `deps/raft` @ `56e32004` (unchanged).
Conventions: the bug-fix arc charter's (`docs/2026-08-19_bugfix-arc-charter.md`)
— guardrails first, predicted flips stated pre-run, same-commit re-pins.

---

## Item 1 — H-9, the inittask double-escape (BUG-064)

**Root cause, re-derived** (matches the W3 diagnosis, sharpened):
`buildInitGraph` (`tools/nativefrontend/load.go`) closes over the program's
imports with a worklist that mixed two NAMESPACES. Source units push their
imports as import PATHS; the closure loop pushes each table entry's `deps` —
which are linker symbol PREFIXES, gc's own R_INITORDER edges read from the
compiled archives, already percent-escaped — onto the same list, and applies
`pathToPrefix` to every popped item. `pathToPrefix` escapes `%` (objabi's
does; it must, or escaping wouldn't round-trip), so the stdlib's one escaped
prefix `crypto/internal/entropy/v1%2e0%2e0` became
`crypto/internal/entropy/v1%252e0%252e0` and `stdInitLookup` missed a row the
table has (line 64, unescaped path in column 4). The refusal message printed
the SINGLE-escaped name because it formats the popped item, not the lookup key
— which is why the message looked self-contradictory ("not in the table"
naming exactly a table row).

**Blast radius, measured from the table** (closure over `inittask-std.tsv`
dep columns): 39 non-internal std packages' init closures reach the escaped
prefix — the whole crypto family (`crypto/rand`, `crypto/sha256`, ..., via
`crypto/internal/fips140/drbg`), `net/http` and friends, `expvar`,
`go/importer`. Any MULTI-package program importing any of them refused.
Single-package programs are immune (`specInitOrder` returns early below two
source units — the init graph is never built), which is why the pre-W4 corpus
never saw it.

**Guardrails (landed first, red witnessed pre-fix):**

| case | shape | pre-fix | post-fix (predicted) |
|---|---|---|---|
| `multipkg/inittask-escape` | 2-pkg, blank `crypto/rand` (raft's route) | whole-export refusal (`frontend-export`) — witnessed 2026-08-20 against the unfixed frontend, exact message above | PASS |
| `multipkg/inittask-escape-closure` | 2-pkg, blank `crypto/sha256` — the escaped prefix arrives deps-of-deps, never named by the source program | same refusal — witnessed | PASS |
| `multipkg/inittask-escape-single` | 1-pkg, blank `crypto/rand` — the immunity control | EXPORTS clean — witnessed | PASS (must not move) |

**The fix:** the worklist carries PREFIXES only (`workItem{prefix, display}`):
source imports convert via `pathToPrefix` exactly once, on push; table deps go
on verbatim (`display` = the prefix — the unescaped path of a dep is not
recorded, and it is only a refusal-message string). Graph CONTENT is unchanged
(the `deps` arrays were always prefixes); only the closure's lookups change.
No wire, decoder, or table change. Frontend unit tests pass.

**Predicted flips for the full differential (stated before the run):** exactly
2 red→green (`multipkg/inittask-escape`, `multipkg/inittask-escape-closure` —
NEW ids recorded directly as PASS since guardrails and fix land in one
commit-group), 1 NEW green control (`inittask-escape-single`), zero movement
on all pre-existing ids. Baseline re-pinned same-commit with this reason.

## Item 2 — errors.New as a stdlib shim (G-2/H-10)

**Design: an E5 STDLIB-SHIM surface entry, not a GoCore change.** The shim is
Go's own implementation modulo names (`go/src/errors/errors.go`): an injected
`goleanShimErrorString struct{ s string }` + pointer-receiver `Error()` +
`goleanShimErrorsNew(text string) error` returning `&goleanShimErrorString{s:
text}`. It lowers through the ordinary pipeline; the `error`-interface boxing
rides the EXISTING interface machinery — **no GoCore, wire-schema, or decoder
change anywhere in this item** (nothing had to be stopped).

**Capability probe first** (scratch, 2026-08-20, `artifacts/w40/probe-cap`):
a hand-written local equivalent of the shim — same type/method/constructor
shapes — was exported and run on the machine before any frontend edit. All
five capabilities the shim rides are already there and agree with `go run`:
fresh-per-call inequality (two same-text News are `!=`), self-`==`, sentinel
identity through a helper return, nil-ness both directions, and `Error()`
dispatch through the interface. gc semantics probed the same day
(`artifacts/w40/probe-errnew`): `errors.New("same") == errors.New("same")` is
**false** (fresh cell per call, exactly the doc's "distinct error value even
if the text is identical"), identity survives stores/returns, and the dynamic
type is `*errors.errorString`.

**The fidelity argument** (recorded in full in the shim source,
`tools/nativefrontend/stdlibshim.go`): identity is (dynamic type, dynamic
value) and the value is a fresh pointer per call, so freshness/sentinel
discrimination inherit from the machine's allocator; the ONE observable delta
is the dynamic type NAME (one shim type per injected package vs upstream's
single unexported type), and it is unobservable in the modeled subset — user
code cannot name `errors.errorString` (unexported), fmt/reflection refuse, and
the type component of `==` cannot flip an answer between distinct pointers.
`.Error()` liveness in the raft census, checked: ONE live site
(`raft.go:441`, `panic(err.Error())` in `newRaft` — the validate-failure
path); `util.go:226/233` are in `DescribeEntry`, which is quarantine-dead
(W3 §2.3's dead-27). The readback rows pin it anyway.

**Two frontend mechanisms rode along, both shim-scoped:**
- **Per-unit injection** (`load.go`, `parseLocal`): shims used to inject into
  the MAIN package only; raft's sentinels live in non-main units (`raft`,
  `confchange`), where an allowlisted call would have hit the "shim not
  injected" refusal. Each local unit now injects its own shim declarations
  before its type-check. No existing corpus case calls an allowlisted
  function from a local unit (grepped: both `strings.Fields` callers are
  main-package), so nothing pre-existing moves.
- **Qualified shim FuncIds** (`emit.go`, `emitStdlibShimCall`): the emitted
  call now targets `funcWireName(shim)` — bare in main (byte-identical to the
  existing `strings.Fields` pins), path-qualified in a local unit.
- Reserved-name collision checking generalized to EVERY name a shim injects
  (`stdlibShimDeclNames`) — the errors shim injects its concrete type too.

**Guardrails (landed first, reds witnessed pre-shim):** 13 rows across three
suites, expectations from `go run` (values recorded in the case files'
printlns; statuses all `ok`):

| suite | rows | pre-shim (witnessed) |
|---|---|---|
| `errors/new-conformance` | fresh-not-eq, self-eq, nilness, readback, cross-impl (== is identity, never text), assert-ok (interface round-trip through `any`) | all 6 subjects per-decl quarantined (`package-selector call errors.New`) → FAIL `frontend-export` |
| `errors/new-sentinel` | identity, distinct, classify (the raft `err == errBreak` discrimination shape), readback — all package-level `var Err… = errors.New(…)` | whole-export refusal (init code has no per-decl quarantine) |
| `multipkg/errors-new` | identity-across, distinct-across, text-across — the sentinel lives in a local unit `liberr`, the raft shape exactly | whole-export refusal |

**Predicted flips (stated before the full run):** exactly the 13 NEW ids, all
PASS; zero movement on the 2229 pre-existing ids (no local-unit allowlisted
callers exist; main-package shim wires are byte-identical). Focused slice
confirms 13/13 PASS against the go oracle. Baseline re-pinned same-commit.

**Differential obligation:** the 13 rows are the shim's standing conformance
suite (the E5 pattern's "the corpus is the shim's conformance suite") — every
future run re-validates the shim against real `errors.New` through `go run`.

## Item 3 — H-11, package-level var quarantine — pending
