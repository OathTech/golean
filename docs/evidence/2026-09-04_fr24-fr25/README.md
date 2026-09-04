# FR-24 per-declaration quarantine, the FR-25 rider, the cmp.Compare retirement — three checkpoints (2026-09-04)

Lane `fr24` ([AGENT] worker; the coordinator brief relayed the [USER]
rulings cited below — citation, never firsthand). Consuming docs:
`docs/language-coverage-ledger.md` §4 rows FR-24, FR-25, FR-26, FR-19,
§5 queue rows 24/25/26, §8k; `docs/2026-09-03_cedar-go-coverage-census.md`
§10 (addendum); `docs/stdlib-admission-register.md` (the `encoding/binary`
row, the `intercept`/`shim` rows, slice log); `docs/discrepancy-backlog.md`
D-002; `tools/lowerdiag/causes.tsv`. Tree: branch `fr24` off main
`aceb0dcb`; the three checkpoint commits are named in the Gate section
(each gate tail names the exact tree it certified). Host: linux/amd64
(shared build box, other lanes active — no timing-sensitive numbers
here). Toolchain: `go version go1.26.5 linux/amd64` = `baselines/
go-oracle-pin`; golean from `scripts/capped lake build` on this tree
(GoCore untouched — the binary is main's).

## Conclusion (one paragraph)

Checkpoint A (FR-24): a package-level var whose TYPE does not lower is
POISONED per declaration (the cell seeds as the reserved `$poisoned`
placeholder, gid kept; every reference — read, write, method call,
address-of — refuses by name naming the var, its type and the type's
cause) instead of killing the export; user and library vars alike. The
H-3 residue the handoff found (an imported named type a REFUSED body had
registered for the D5 stub pass surviving into the export — a user
`reflect.ValueOf(x).Len()` was a whole-export kill on main) rides the
mono journal and rolls back with the body. On cedar-go the FR-24 kill is
gone; the export fraction does not move at A because the next kill
(FR-25: `complex128` in `reflect.Type`'s requirement list, reached from
the now-lowering `encoding/binary.sizeof`) sits directly behind it — as
the handoff predicted. Checkpoints B and C: see their sections below
(filled in as each lands).

## Decisions ([AGENT] unless marked)

- [USER] (Mike, 2026-09-04, relayed by the [AGENT] coordinator — cited
  as relayed): «(2) given we have a plan, I think this should be an
  honest red» = RETIRE the cmp.Compare shim (checkpoint C); «(3) yes,
  makes sense» = APPROVE the FR-25 rider (checkpoint B). Standing
  posture (relayed): break rather than preserve incorrect behaviour;
  every detected gap rowed with a plan.
- D1 [AGENT]: USER-package vars of an unlowerable type poison the same
  way as library vars (the ledger FR-24 row asked for the decision): the
  soundness argument is identical — a zero-valued var has no initializer
  to skip, the cell is unreachable by construction — and the rows
  `init/user-var-type-unlowerable/*` pin both halves (healthy siblings
  lower and keep their init order; references refuse by name).
- D2 [AGENT]: the `importedNamed` journal fix ships in checkpoint A
  (guard-strengthening in the shape the dry-run comment prescribed —
  "add them here with marks"); the comment's "never a changed answer"
  claim for `importedNamed` was measured FALSE and is rewritten.
- D3 [AGENT]: the struct-field kill (`type holder struct{ m sync.Map }`)
  is ROWED (FR-26) with a plan, not fixed here (scope: FR-24 + the two
  riders); `TestStructFieldOfUnlowerableTypeStillRefusesExport` pins the
  blast radius so a change is deliberate.
- D4 [AGENT]: `tools/lowerdiag` — `global-type-unlowerable` becomes
  decl-scoped and the static pass no longer marks it an export kill; the
  poison reference text gets its own cause row (`global-type-poisoned`,
  pattern-classified); `unclassified-formats.txt` regenerated (the
  retired whole-export format leaves the list).
- The scratch `FR24_TRACE*` hooks of the prototype were NOT ported
  (brief rule); the prototype's traces are kept here, sanitized
  (`traces/`, absolute paths replaced by `<repo>/`, `<proto>/`).

## Checkpoint A — FR-24 (commit named in the Gate section)

Mechanism: `emit.go collectGlobals` (poison arm), `poisonGlobal` /
`globalPoison{cause,typeName}`, `quarantineUnlowerableGlobals` (lazy
init — the FR-24 poisons armed in `collectGlobals` survive into the H-11
dry run, which rides the same map), `globalAddr` (the FR-24 text),
`poisonGlobalCells`; `mono.go monoLogImportedNamed` + `rollbackMono`;
`wire.go` journals first-time `importedNamed` registrations; unit tests
`fr24_test.go` (3). Rows: `init/user-var-type-unlowerable/{unused,
order-kept}` PASS, `{used,addr-of}` red by name (FR-24);
`init/library-var-type-poisoned/{sibling,write-int,write-struct,
size-int}` born-FAIL on FR-25 (the comments in the row state what flips
when FR-25 lands and what stays red by design — Write/Size are one H-3
stub each on `reflect`); `init/user-var-struct-field-unlowerable`
born-FAIL on FR-26; `methods/quarantine-imported-type-residue/unrelated`
PASS (the journal fix's witness), `uses-reflect` red by name (FR-14).
The FR-24 witness `init/library-var-type-unlowerable` does NOT flip at A
(cause `sync.Map` → `basic type complex128`). `wires-A/` holds the emit
of each row dir at A (`*.wire.json` for the two exporting dirs — the
`$poisoned` cell `cache`, the stubs naming it; `*.stderr` for the three
refused dirs).

## Checkpoint B — FR-25, the rider (commit named in the Gate section)

Mechanism: `wire.go emitBasic` — under `sigOpaque` an unlowerable basic
type (`complex64`, `complex128`, `unsafe.Pointer`; `opaqueBasicMarker`)
is an opaque `named <basic>` marker recorded in `opaqueBasics`;
`opaqueMarkerTypeDefs` mints its existence-only `unsupported` TypeDef
(text `FR-25: basic type complex128 is not modeled (FR-15: …) — carried
as an opaque marker in declaration signatures only …`); `withOpaqueSigs`
returns the FR-23 and FR-25 markers a window TOUCHED (minted or re-used
— "minted only" left a stub whose marker an earlier requirement list had
minted with no clause naming it; fixed before landing) and
`opaqueSigClauses` renders them into every stub's reason; the D5
`importedMethodStubs` now emit under the same opaque window (D5 [AGENT]
below). Tests: `fr25_test.go` (5), `TestQuarantinedMethodUnlowerable
SignatureRefuses` re-aimed at the arm's remaining reach (an anonymous-
struct parameter). Rows: `methods/signature-basic-unlowerable/
{iface,func,method}-uncalled` PASS, `*-called` red BY DESIGN (the call
sites mention a complex VALUE — `constant kind Complex` / `builtin real`,
FR-15's text; counted on FR-25's line); FLIPPED FAIL→PASS:
`init/library-var-type-unlowerable` (the FR-24 witness — two checkpoints
deep, as the handoff predicted) and `init/library-var-type-poisoned/
sibling`; `init/library-var-type-poisoned/{write-int,write-struct,
size-int}` red by name at `encoding/binary.Write/Size: package-selector
call reflect.Indirect` (moved to FR-14's line — exactly what their row
comment said would remain). `wires-B/` holds the emits: the
`complex128` marker TypeDef and the `main.Yes.OverflowComplex` stub
naming it; the binary row's wire with `encoding/binary.structSize` as a
`$poisoned` cell, `dataSize` a stub naming it, and the `reflect.Value`
D5 marker + stubs with `complex128`/`unsafe.Pointer`/`iter.Seq[…]`
markers in their signatures.

- D5 [AGENT]: the D5 imported-type stub pass (`importedMethodStubs`)
  emits under the opaque window too. Before, ONE unlowerable signature
  skipped the type's whole method set (no marker, no stubs — a dangling
  `named` on the wire, and the interfaces the other signatures had noted
  still reached the fixpoint); now the type gets its marker and its FULL
  stub set, each stub naming its markers. The twin is unaffected (its one
  D5 type, `log.Logger`, was already stubbed whole; pin 69a538de
  unchanged — checked before landing and by the gate). The item-7 rule
  is met: a basic type has no methods, and an imported generic
  instantiation WITH exported methods still refuses in opaque mode.
- D6 [AGENT]: the body-value refusal text stays FR-15's (`basic type
  complex128`, `builtin real`, `constant kind Complex`) — the brief's
  "refuses by name" is met (the type is named) and the FR-15 row cites
  that text for 27 rows; the FR-25 text is on the STUB and the marker
  TypeDef, which is what a call would reach if one could be emitted (it
  cannot: every call site mentions a value of the type).

## Checkpoint C — the cmp.Compare retirement (commit named in the Gate section)

[USER] ruling (Mike 2026-09-04, relayed by the [AGENT] coordinator, cited
as relayed): «(2) given we have a plan, I think this should be an honest
red». Mechanism: `cmpshim.go` DELETED; `stdlibshim.go` loses the three
kind shims (`goleanShimCmpCompare{Uint,Int,String}`) and its
`stdlibGenericDesugarInject` entry (the table stays, EMPTY — the one place
a future entry lands, against the frozen count); `stdlibreach.go` loses
the `cmp` `intercept` row and the `cmp.Compare` arm of
`interceptedLibraryCall`; `emit.go` loses the dispatch hook. `cmp.Compare`
is the real source-through generic at every type argument. Rows,
verified one by one (`scripts/coverage run` over every id of
`slices/sortfunc-cmp`, `stdlib-source/cmp-compare`,
`stdlib-source/slices-sortfunc`): EXACTLY ONE flip —
`slices/sortfunc-cmp/cmp-compare-kinds` PASS→FAIL (`function-local defined
type index as a type argument … refused rather than guessed`, mono.go's
C6 rule; FR-19's line, BUGS.md BUG-092 Cases line); `stdlib-source/
cmp-compare/local-float-type` and `slices/sortfunc-cmp/sortfunc-local-type`
already red the same way; all 17 other rows PASS through the real generic
(ints, strings, floats incl. NaN, named non-local types, struct keys,
Less/Or). No FINDING (nothing went red for another reason). Register:
intercept 2 → 1, shim 7 → 6; D-002: "6 fmt shims remain; the freeze is
intact". Twin pin MOVED, a ruled consequence checked before landing
(`twin-repin-C/`): raft's `quorum/majority.go` calls `cmp.Compare` inside
`MajorityConfig.Describe`, an H-3 quarantined stub, so the ONLY wire
change is the three dead injected shims leaving (0 added, 0 changed;
methods/types/globals/method sets identical) — 69a538de → b4458244.

- D7 [AGENT]: `stdlib-source/cmp-compare/local-float-type` MOVES from the
  C6 (c)-pin bucket to FR-19's line (with `cmp-compare-kinds`): same
  refusal, and the brief names FR-19's scope-qualified TypeId KEY as the
  plan — where the local type's NAME is unobservable (no `%T`/`%v` of a
  value of the type) the key can carry the scope; C6 keeps the
  observable-name cases (ledger §5.1 item 1 re-worded). Both rows sit on
  BUG-092's Cases line (the re-pin guard's requirement for a PASS→non-PASS
  flip; Status open, Pinned-by none, Expect FAIL).

## cedar-go: after (tip — every checkpoint measured; A, B, C agree)

`census-A/` (checkpoint A, tree 83b71132 = A before its header-only
amend) and `after/census/` (the C tree; `meta.tsv` names the commit the
runner saw — see the Gate section for the tip re-run): **29
FRONTEND-REFUSED / 5 EXPORT-OK of 34 — export fraction UNCHANGED**, but
the FR-24 kill is GONE and the 29 refusals are the two causes §9.3's
pass C had predicted counterfactually, now measured on the UNRELAXED
copy: 25 × `method stencil cedargo/internal/mapset.ImmutableMapSet[…].All
does not lower (… iter.Seq[…] …) — FR-4` and 4 × `slices.Sort at
non-integer element type string` (an `init()` body). FR-25 never
surfaces on cedar-go itself because the FR-4 stencil refusal fires in
the mono drain before the interface fixpoint; the corpus rows carry the
FR-25 witness. `after/lower-diagnose/`: static 1554/1671 (93.0%)
UNCHANGED (kills became stubs; the values stay refused), export-kill
declarations 11 → 3 and packages export-killed 21/26 → 7/26 — the
remaining three are FR-19's `nodeJSONAlias` ×2 and the `slices.Sort`
`init()`. Next blockers, in order: FR-4 stencils → `slices.Sort` at
string in `init()` (memo §3 row M) → FR-19 `nodeJSONAlias` → the
per-declaration surface (`encoding/json` FR-14/G6 64 decls, `net/netip`
methods 19, `errors.Is/As` reflect 10, `iter.Seq` values FR-23→FR-12).
Every cause in the report has a ledger row — no UNROWED cause appeared.

## cedar-go: before (main aceb0dcb)

`before/census/` = `scripts/cedar-census run` on main's frontend (the
worktree at `aceb0dcb`, no edits): 29 FRONTEND-REFUSED / 5 EXPORT-OK of
34; every refusal `package-level var encoding/binary.structSize: its
TYPE does not lower (sync.Map …) — FR-24 …`. `before/lower-diagnose/` =
`scripts/lower-diagnose artifacts/cedar/cases/all --json --tsv --include
cedark8s/cmd/schema-formatter,cedark8s/internal/schema`: first refusal
FR-24; static: 1554/1671 declarations demanding nothing refused (93.0%),
11 export-kill declarations, 21/26 packages export-killed; top blockers
FR-14 `encoding/json` (64 decls), FR-14 type methods (19), reflect (10),
`slices.Sort` at string (10), FR-23 signatures (8), FR-19
`nodeJSONAlias` (2, export). (Paths in the copied artifacts are
sanitized to `<repo>/`.)

## Gate

- **A** (`ci-diff-A.txt`): `scripts/capped scripts/ci --diff` on the
  committed checkpoint A (83b71132; amended to 4359dc2e for the
  baseline's `# cases:` header line only — the reconciler's C1H) —
  RESULT PASS; 3376/3376 no regression; negative 394/394; re-pin guard 0
  PASS→non-PASS; twin 69a538de unchanged; register ok; frontend unit
  tests (incl. `fr24_test.go`) and lowerdiag tests ok; eval tests 148;
  reconciler 1 HIGH = the header count line (fixed by the amend).
- **B** (`ci-diff-B.txt`): on the committed checkpoint B (65676c84) —
  RESULT PASS; 3382/3382 no regression; re-pin guard 0 PASS→non-PASS (2
  FAIL→PASS flips, the FR-25 witnesses); twin 69a538de unchanged;
  reconciler 0 HIGH.
- **C / tip** (`ci-diff-C.txt`): on the committed checkpoint C — see the
  file's tail for the RESULT line, the ruled flip on BUG-092's Cases
  line, the moved twin pin b4458244, register intercept 1 / shim 6.

## Files

| file | producer | what |
|---|---|---|
| `before/census/*` | `scripts/cedar-census run` at main aceb0dcb (worktree, unedited) | results/histogram/per-package/meta of the BEFORE census |
| `before/lower-diagnose/*` | `scripts/lower-diagnose artifacts/cedar/cases/all --json --tsv --include cedark8s/cmd/schema-formatter,cedark8s/internal/schema` at main | the standing full-blocker report BEFORE |
| `wires-A/*` | `GO111MODULE=off go run ./tools/nativefrontend --dir Corpus/coverage/exec/<row> --out wires-A/<row>.wire.json 2> wires-A/<row>.stderr` at checkpoint A | wires of the exporting row dirs; first-refusal stderr of the refused ones |
| `wires-B/*` | `GO111MODULE=off go run ./tools/nativefrontend --dir Corpus/coverage/exec/<row> --out wires-B/<row>.wire.json` at checkpoint B | the `complex128` marker + stubs (`methods_signature-basic-unlowerable`), the poisoned `encoding/binary.structSize` cell beside the lowered package and the `reflect.Value` D5 marker/stubs (`init_library-var-type-poisoned`), the flipped FR-24 witness (`init_library-var-type-unlowerable`) |
| `ci-diff-A.txt` | `scripts/capped scripts/ci --diff` on the committed checkpoint A (pre-amend tree 83b71132; the amend touched only the baseline's `# cases:` header line the reconciler flagged, C1H) | RESULT PASS, 3376/3376 no regression, 0 flips, twin 69a538de unchanged, reconciler 1 HIGH = the header count line (fixed by the amend) |
| `ci-diff-B.txt`, `ci-diff-C.txt` | `scripts/capped scripts/ci --diff` on the committed checkpoints B and C (tails; paths sanitized to `<repo>/`) | the gates |
| `census-A/*`, `after/census/*` | `scripts/cedar-census run` at checkpoint A and at C | 29 FRONTEND-REFUSED (25 FR-4 + 4 `slices.Sort`) / 5 EXPORT-OK, both |
| `after/lower-diagnose/*` | `scripts/lower-diagnose artifacts/cedar/cases/all --json --tsv --include cedark8s/cmd/schema-formatter,cedark8s/internal/schema` at C | the standing full-blocker report AFTER |
| `twin-repin-C/structural-diff.txt`, `hashes.txt` | python3 JSON diff of `baselines/pins/twin-chdriver.wire.json` (pinned) vs the fresh emit; `sha256sum` | the SOLE change: 3 dead shim funcs removed |
| `traces/*` | the parked prototype's `FR24_TRACE*` stack traces (NOT ported), sanitized | the diagnosis trail: `basic type complex128` reached from `reflect.Type`'s requirement list / `reflect.Value`'s D5 stubs |

## Reproduction

```
scripts/setup-deps --only go,goose,cedar-go,cedar-access-control-for-k8s --from <sibling>
scripts/capped lake build
GO111MODULE=off go test ./tools/nativefrontend ./tools/lowerdiag
scripts/check-frontend-pins && scripts/check-stdlib-register
scripts/capped scripts/ci --diff
scripts/cedar-census run
scripts/lower-diagnose artifacts/cedar/cases/all --json --tsv --include cedark8s/cmd/schema-formatter,cedark8s/internal/schema
```
