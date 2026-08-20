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

*(Byte-identity corrected in the audit fix round, 2026-08-20 — finding F2. The
claim was FALSE as shipped: `e.tmpSeq` was missing from the rollback set, so
the dry run's discarded temporaries leaked counter increments and 9 wires came
out alpha-renamed — semantically inert, function-local names, and outside
golden-pin coverage, but not byte-identical. Fixed by rolling `tmpSeq` back
with the rest; the claim is now MEASURED, not asserted: over all 1103 corpus
package directories, `nativefrontend` at this tip vs the pre-branch binary
differs in exactly 1 wire — `errors/new-conformance`, item 2's errors.New
shim — plus the 6 export-status flips, all recorded W4.0 ones. Zero
alpha-renames. Three rollback-set gaps stay RECORDED rather than fixed —
`syncUsed`, `importedNamed`, `badKeyPaths` — with the direction argued at the
rollback site: worst case an extra unreferenced stub or an over-refusal, never
a changed answer for emitted code, and no corpus case reaches one today.)*

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
  correct consequence of the blank-var skip, kept.** *(Reason corrected in the
  audit fix round, 2026-08-20 — finding F3. The text below is the corrected
  one; the original named "generic func VALUES, unlowerable" as the skipped
  form, which is WRONG: generic function values lower fine, and the case was
  never red for them.)* The case's ONE unlowerable package-level row is
  `var _ = satComparable[struct{ f any }]` — an anonymous NON-EMPTY struct as
  a type argument, refused by the mangler at `mono.go:965`
  (`anonymous non-empty struct as a type argument`), which is ledger row
  FR-13. It used to refuse the whole export; it is a pure, effect-isolated,
  blank-target initializer, so H-11 skips it — faithfully: gc evaluates the
  generic func value with no observable effect, so machine and go AGREE (the
  PASS is a true differential agreement, not a masked skip).
  **The witness that flip LOST is now restored**: `generics/`
  `anon-struct-type-argument` pins the same FR-13 boundary in a form the
  quarantine cannot mask (the instantiation is in a function BODY, so it is
  emitted, not skipped) and is red at `frontend-export` by design. The
  `generics/` reds are otherwise unchanged.

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

---

## Audit fix round (2026-08-20)

Pre-merge adversarial audit of the branch tip. Five findings, all
auditor-verified, all fixed here; the auditor's probes are reused as the
guardrail material rather than re-derived.

### F1 (CRITICAL) — the effect-isolation predicate admitted real effects

H-11's `initializerEffectIsolated` admitted **any** direct `pkg.Fn(...)` call
into a non-source package whose arguments were value-isolated, on the stated
reasoning that such a body "the machine does not model in any case". That
reasoning is **false**, and the counterexample is one line: a package-level
`var _ = fmt.Println("x")` was declared effect-isolated, quarantined and
SKIPPED — so the machine ran the program printing nothing where `go run`
prints. Unmodelled ≠ effect-free: the effect landed on the very stdout the
differential compares. `os.Mkdir` and `os.Setenv` were admitted the same way.

**Fix: a positive allowlist**, `pureUnmodeledCallees` (emit.go), keyed by
`<import path>.<name>` so an import alias cannot smuggle anything in, and
minimal by charter — `os.Getenv`, `os.LookupEnv`, exactly what the existing
guardrails use. The bar for a row is written above it: no effect observable by
ANY oracle the differential uses, and no panic on the arguments the predicate
admits. Everything else refuses the whole export, which is the pre-H-11
behavior and the sound direction. **It is not a "not modelled yet" list** —
that was the refuted reasoning.

### F1b — panic-freedom is a SECOND property, and it was missing entirely

The conversion-operand recursion admitted `[4]int(shortSlice)`. Probing that
out showed the hole is not conversion-specific: paired with an admissible
`os.Getenv` call, **six panicking shapes were all admitted and skipped** —
slice→array conversion, index-out-of-range, nil deref, divide-by-zero, failed
type assertion, negative shift — each turning go's init panic into a clean
machine run. A skipped panic is a SILENT wrong answer, not the "visible
divergence" the old soundness comment claimed.

**Fix: `initializerEffectIsolated` is now a POSITIVE ALLOWLIST OVER EXPRESSION
SHAPES** rather than a walk that refuses a denylist. An expression is
admissible only if its form is listed, so every form the frontend grows later
defaults to refusal. The panicking shapes are excluded by construction:
array-target conversions (the one conversion class that can panic), indexing,
slicing, pointer deref, type assertion, `/` and `%` and shifts by a
non-constant, interface `==`/`!=` (uncomparable dynamic types), and method
values (whose receiver evaluation can deref nil). `IndexExpr` is admitted ONLY
as a generic instantiation — which is what keeps `compile-only-forms` green.
The old `pureArg` helper is gone: call arguments now go through the same
admissibility walk, which strictly subsumes it (it used to permit `sl[7]` as
an argument).

The soundness comment on `quarantineUnlowerableGlobals` now states the ACTUAL
argument — allowlist purity plus panic-freedom — and records verbatim that the
argument it made before was refuted, so nobody re-derives it.

### F1/F1b guardrails (written before the fix, and deletion-tested)

- `init/quarantined-var-syscall` — `os.Mkdir("")` (always ENOENT, creates
  nothing, no platform dependence): whole-export refusal, red at
  `frontend-export`. The subject is a sibling that touches nothing, so a
  re-opened allowlist flips the row PASS.
- `init/quarantined-var-panicking` — an allowlisted `os.Getenv` call beside
  `[4]int(sl)` on a length-2 slice: whole-export refusal. Go's own behavior
  (`expected_status panic`) is recorded in the row, so a re-opened predicate
  moves the row's STAGE to `go-observation` — tracked-baseline drift either
  way.
- `init/quarantined-var/siblings` is the green control for the allowlist's
  positive half and stays PASS.
- **`fmt.Println` is NOT expressible as a differential row** — measured, not
  assumed: the harness reads a case's observation off the subject program's
  stdout, so a program that prints during init dies at stage
  `go-observation` before the frontend is ever consulted. It would be a red
  row pinning nothing. That pin therefore lives in
  `tools/nativefrontend/effectisolation_test.go`, run by the gate's
  `go test ./tools/nativefrontend` step, together with the whole panicking-shape
  family (11 shapes) and the call shapes outside the allowlist.
  **Deletion test RUN**, not asserted: against the pre-fix `emit.go`, 15 of
  the 16 new sub-tests fail and the positive control passes (the 16th,
  an immediately-invoked function literal, was already refused).

### F2 (LOW) — the dry run leaked `tmpSeq`

`e.tmpSeq` was missing from the rollback set, so the discarded temporaries of
the dry-run pre-pass still bumped the program-wide counter and **9 corpus
wires came out alpha-renamed**. Semantically inert — the names are
function-local and stay unique because the counter is still monotonic within
each real emission — but it made item 3's "byte-identical wires" claim false,
and golden pins compare bytes. **Rollback taken (the preferred fix), and it is
safe for a checkable reason**: no `$c` name crosses a declaration boundary
(lifted closures carry `liftSeq`, already reset per dry run). Verified by
measurement, not argument: all 8 of the affected non-`errors.New` wires are now
BYTE-IDENTICAL to the pre-branch binary's, and over all 1103 corpus package
directories the tip differs from pre-branch in exactly 1 wire
(`errors/new-conformance`, item 2's shim) plus the 6 recorded status flips.

Three rollback-set gaps are RECORDED rather than fixed (the auditor's
could-not-verify): `syncUsed`, `importedNamed`, `badKeyPaths` accumulate during
the dry run and are not restored. The direction is argued at the rollback site —
worst case a stale `badKeyPaths` entry over-refuses, or a stale
`syncUsed`/`importedNamed` entry adds an unreferenced method-set row or stub;
never a changed answer for emitted code. No corpus case reaches one today
(the quarantined initializers are `os.Getenv`/`os.LookupEnv` calls, which touch
none of the three), and the fix shape if one ever does is the two lines above
it.

### F3 (MEDIUM) — the compile-only-forms flip's recorded reason was wrong

Item 3 and the baseline header both recorded the flip as caused by
"`var _ = satTildeInt[int]` rows (generic func VALUES, unlowerable)". Wrong:
generic function values lower fine. The case's single unlowerable row is
`var _ = satComparable[struct{ f any }]` — an anonymous NON-EMPTY struct as a
type argument, refused at `mono.go:965`, ledger row FR-13. Both records are
corrected in place, with the wrong text quoted so the correction is legible.

**The lost witness is restored.** The flip was correct, but it left FR-13's
type-argument half with no red row. `generics/anon-struct-type-argument` pins
it in a form the quarantine structurally cannot mask — the instantiation is in
a FUNCTION BODY, so it is emitted (as an H-3 quarantined stub) rather than
skipped — and is red at `frontend-export` by design. The ledger's FR-13 row
and its `Satisfying_a_type_constraint` row now cite it instead of
`compile-only-forms` (and their stale `wire.go:495` / `mono.go:960` line
anchors are corrected to 508 / 965).

### BUG-064 residuals (LOW)

- The dead, path-shaped `initSortKey(path string)` is **deleted**. It is the
  exact shape that caused BUG-064 — outside `inittask.go` every identifier in
  flight is already a PREFIX, and handing a prefix to a path-shaped function
  silently double-escapes it. A comment in its place says so; the one real
  caller (`load.go:387`) appends `initTaskSuffix` to the prefix it holds.
- `load.go`'s comment claimed the unescaped path "is not recorded". It **is** —
  column 4 of `inittask-std.tsv`, for exactly the rows where prefix and path
  differ (`crypto/internal/entropy/v1%2e0%2e0` → `crypto/internal/entropy/v1.0.0`).
  Comment corrected AND the column put to use: `stdInitEntry.path` +
  `stdInitDisplay`, so a refusal message names the package the way it is
  written in source. Display only — the schedule still keys on the prefix.

### The gate, and the raft subject re-censused

`scripts/ci --diff` at the fix-round tip: **green**, with the differential
baseline diff reporting exactly the three predicted NEW ids and nothing else —
the prediction was stated before the run and held. 2253 cases, 2113 PASS /
140 FAIL; negative lane 390/390, no regression; frontend unit tests ok; eval
tests 136 ok. Baseline re-pinned in the same commit with the reason.

**The F1 tightening does not touch the raft subject**, which was the risk worth
checking (a narrower allowlist can only ever over-refuse, and over-refusal on
the north-star target would have cost the W4.0 unblock). Re-run at this tip:
`frontier.py` — **EXPORTS CLEAN, exit 0**, terminal-row plan unchanged;
`sweep.py` — the census reproduces the W4.0 report **exactly**: PASS 1 49
quarantined subject declarations / 113 imported stdlib stubs, 19 first-order
LIVE, PASS 2 fixpoint in 2 rounds adding 3 behind the sinks, **HEADLINE 22
LIVE**, residual sinks NONE, G-1 cross-check OK. The mechanism is the expected
one: every package-level initializer in the subject tree is a composite literal
or an `errors.New` call, both of which LOWER, so none of them ever reaches the
eligibility predicate the fix narrowed.
