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

## Item 3 — H-11, package-level var quarantine

**The mechanism** (all frontend; no wire-schema, decoder, or GoCore change):

1. **A dry-run pre-pass** (`quarantineUnlowerableGlobals`, emit.go) emits
   every package-level initializer once, in program initialization order,
   BEFORE any function body — with ALL side effects rolled back (the H-3
   rollback set: lifted, local types, iface methods, named structs,
   deferNoop, the mono journal). The only question asked is "does it lower".
2. An initializer that fails with an UNSUPPORTED refusal AND is
   **effect-isolated** (below) quarantines its declared vars: reason
   recorded per `*types.Var`, initializer marked skipped. Any other failure
   keeps today's whole-export refusal.
3. **The poison lives at the single choke point** every reference shape
   resolves through — `globalAddr` (reads, writes, address-of, qualified
   `pkg.V` included; its signature now returns an error and all 7 call
   sites propagate). A function body referencing a quarantined var refuses
   emission and lands as an H-3 per-declaration stub NAMING THE VAR; the
   runtime stop is the standing `frontend-quarantined:` refusal (stage
   `frontend-export`). Init code referencing one refuses the whole export —
   except another initializer, which fails its own dry-run through the
   poison and CASCADES (its RHS is a pure read — eligible), reason chained.
   InitOrder guarantees the dependency direction, so the cascade is one
   pass.
4. **The cell is never dropped and never silently zero**: the var keeps its
   typed globals entry (gid density, driver zero-seeding untouched), and
   the poison makes the zero unreachable — no emitted body can contain a
   reference. `$pkginit` skips exactly the quarantined initializers (and
   its recv scan ranges over the kept ones).

**Effect-isolation, the eligibility predicate** (`initializerEffectIsolated`)
— sound direction false = refuse the export: no receives anywhere; every
call is a type conversion or a direct `pkg.Fn(...)` into a NON-source
package (a body the machine does not model in any case) whose arguments are
effect-free syntax (no calls/receives/`&`/func-literals) of value-isolated
static type (basics, arrays/structs of basics); method calls, builtins, and
source-package calls all refuse. **Why this makes the skip sound:** an
eligible initializer's lowerable parts cannot touch modeled state, so after
the skip the machine differs from Go only in the poisoned cells, which
nothing can read. Residual, recorded: a skipped initializer that would
PANIC (or print) under Go diverges VISIBLY in the differential (machine ok
vs go panic/output) — never silently. The transitive shape (`var x =
quarantinedSourceFn()`) is deliberately OUT of v1: the initializer lowers,
so the dry-run never fails on it, and the standing C3 rule
(`checkInitQuarantine`) keeps refusing the whole export — widening that owes
a fresh effect argument (the callee's lowerable parts have modeled effects).

**Guardrails (landed first, reds witnessed pre-fix — all three suites were
whole-export refusals):**

| suite | rows | post-fix (predicted and focused-run confirmed) |
|---|---|---|
| `init/quarantined-var` | siblings + read, cascade, write, addr, multi (one os.Getenv var, a cascade dependent, two healthy siblings, a two-var os.LookupEnv, a blank `var _`) | `siblings` PASS; the 5 reference-shape rows FAIL `frontend-export` BY DESIGN (frontend-quarantined naming the var — a silent-zero regression would flip them, which is the pin's point) |
| `init/quarantined-var-callee` | sibling | stays whole-export red (C3 preserved) |
| `init/quarantined-var-impure` | counter (source-call argument: `os.Getenv(bump())`, bump mutates a modeled global) | stays whole-export red (not effect-isolated) |

os.Getenv/os.LookupEnv are the unlowerable initializers of choice because
ambient-environment reads can never gain a faithful shim — the rows won't
change meaning when other stdlib surface lands.

**Predicted flips for the full differential (stated before the run):** exactly
the 8 NEW ids (1 PASS, 7 FAIL/frontend-export as above), zero movement on the
2242 pre-existing ids (the dry-run rolls back everything; all-healthy packages
emit byte-identical wires — golden pins are the check). Baseline re-pinned
same-commit.

**The first full run REFUTED that prediction by two rows — both investigated
before landing, honesty over tidiness:**

- `spec-examples-decl/generic-type-switch` PASS→FAIL — **a real defect in the
  first H-11 cut, caught by the full run and fixed in this commit.** The
  dry-run ran before the FuncDecl loop, which was where generic declarations
  registered (`genericFuncDecls`/`recordGenericMethod`), so an initializer
  instantiating a generic (`var v1 = f[string]("foo")`) failed its dry-run
  with "generic function f has no declaration in this package" — ineligible
  (a call) — whole-export refusal. Fix: `registerGenericDecls`, a dedicated
  pre-scan before the pre-pass; the FuncDecl loop now only SKIPS generic
  declarations (`recordGenericMethod` appends, so re-registering would
  duplicate method stencils). Post-fix the whole `spec-examples-decl/generic*`
  and `generics/` slices reproduce their baseline exactly.
- `spec-examples-decl/compile-only-forms` FAIL→PASS — **an unpredicted but
  correct consequence of the blank-var skip, kept.** The case's package-level
  `var _ = satTildeInt[int]` rows (generic func VALUES, unlowerable) used to
  refuse the whole export; they are pure, effect-isolated, blank-target
  initializers, so H-11 skips them — faithfully: gc evaluates a generic func
  value with no observable effect, so machine and go AGREE (the PASS is a
  true differential agreement, not a masked skip). Noted honestly: the case's
  green no longer witnesses that the frontend can EMIT those forms — the
  generic-func-value feature itself stays red where it is load-bearing
  (`generics/` reds unchanged).

---

## The post-W4.0 census (sweep re-run, 2026-08-20)

Instruments re-run against the W4.0 frontend (built from this branch;
`frontier.py`, `sweep.py`, `derive.py --check`). The tracked plan
(`tools/raftsubject/frontier-plan.tsv`) is re-pinned to its TERMINAL ROW ALONE
— the subject tree exports clean with ZERO probe deltas, which is §8's W4.0
done criterion verbatim. `probe/errors_new.go` is deleted (its body was lifted
into the frontend shim); `sweep.py` is updated for the unmasked world (no
errors.New flattening — it lowers for real; the `globalRand.Intn` call site
joins the PASS-2 flatten so the census closes behind the one new PASS-1 sink;
the standalone G-1 probe becomes a CROSS-CHECK that must agree with PASS 1's
own Intn row, and does).

**Headline: 22 LIVE quarantined subject declarations (19 first-order + 3
behind sinks), residual sinks NONE — the census is CLOSED.** PASS 1: 49
quarantined subject declarations (was 53) and 113 imported stdlib stubs (was
36 — the growth is H-9's fix letting `crypto/rand`, `math/rand`, `math/big`
resolve as imports, landing their declaration-only marker stubs: math/big 61,
bytes 24, math/rand 16, strings 9, sync 3; the pre-existing contract, not a
raft gap).

**Retired by W4.0, confirmed on the wire:**
- **H-9 / BUG-064** — fixed; the multi-package export proceeds.
- **G-2 (`errors.New`)** — retired everywhere: the nine sentinel globals AND
  every in-body site lower through the shim. The four declarations whose ONLY
  refusal was errors.New now lower fully (`Changer.{EnterJoint, LeaveJoint,
  Simple}`, `Config.validate` — checked by name against the wire);
  `(*raft).Step`'s census cause shifted to `bytes.Equal`, exactly W3's
  second-cause prediction (G-7).
- **G-3** — the mechanism (H-11) landed as the general backstop; with
  errors.New modeled, nothing in this tree needs it.
- **G-1's MASKING** — gone: `(*lockedRand).Intn` appears in PASS 1 with its
  real refusal (`package-selector call rand.Int`). The DRAW itself is of
  course not retired — it is W4.1's H-15 choice site.

**What remains, and it is exactly the run-blocker set (26 → 22 live, 9 → 7
causes):** the live partition is an exact cover, 8 + 10 + 1 + 1 + 2 = 22 —
- **G-6** promoted `sync.Mutex` (H-12): the 8 `MemoryStorage` methods;
- **G-5** fmt (H-6, ruled Option 1): 10 declarations — `Changer.apply`,
  `checkInvariants`, `newRaft`, `(*raft).restore`, `raftLog.scan`,
  `stepLeader`, `voteRespMsgType`, `ConfChangeV2.EnterJoint`,
  `Progress.SentEntries`, `DescribeConfChange`;
- **G-7** `bytes.Equal` (H-13): `(*raft).Step`;
- **G-1** the jitter draw (H-15): `(*lockedRand).Intn`;
- **G-8** `binary.LittleEndian` (H-14): `readOnly.{recvAck, heartbeatCtx}`.
Plus the two run-blockers that never were quarantines: **G-4** the proto codec
(H-1 — `Clone`/`Size`/`Unmarshal` lower as explicit fail-closed panics, all
three live) and the two G-5 riders **G-9** (`strings.Join` inside `newRaft` —
still the reason H-6 alone does not unblock `NewRawNode`) and **G-10**
(`strings.Builder` via `DescribeConfChange`).

**What W4.1 inherits** (harness design §8, unchanged in substance, sharpened
in numbers): H-12, H-13, H-14, H-6's implementation (+H-17/H-18 riders), H-15,
and H-1's codec — 7 causes over 22 live quarantined declarations + 3 live
codec panics + 1 live imported stub (`strings.Builder.String`). G-2's in-body
ninth cause retired with W4.0, as §8 predicted.

**Instrument status at the census:** `frontier.py` (terminal-only plan):
EXPORTS CLEAN, exit 0. `sweep.py`: the report above, fixpoint in 2 rounds,
residual sinks none, G-1 cross-check OK. `derive.py --check`: clean (the tree
is untouched by this arc — nothing in W4.0 edited `raftsubject/`).
`difftest.py`: **NOT RUN — environment, not signal**: this workspace's sandbox
denies both the shared Go module cache (`/home/dev/go/pkg/mod`, foreign
ziphash unreadable) and `proxy.golang.org`, so the throwaway module linking
real protobuf cannot build. raftpb/plainpb is untouched by this arc (the
differential's subject), and the last green run is the raft-w3 tip. To re-run
outside the sandbox: `python3 tools/raftsubject/difftest.py` with normal
GOPROXY access. Recorded per the ask-don't-hack rule rather than worked
around.

## W4.0 exit state

The three items are landed, each guardrails-first with its full-gate run and
same-commit re-pin: BUG-064 (+3 ids), the errors.New shim (+13 ids), H-11
(+8 ids, +1 explained flip, one pre-landing defect caught and fixed by the
gate's own refutation of a prediction). `frontier-plan.tsv` is the terminal
row alone. The export blockers of the W3 measurement are ZERO; every remaining
gap is a run-blocker, enumerated above, owned by W4.1.
