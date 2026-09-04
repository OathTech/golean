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

(filled per checkpoint)

## Files

| file | producer | what |
|---|---|---|
| `before/census/*` | `scripts/cedar-census run` at main aceb0dcb (worktree, unedited) | results/histogram/per-package/meta of the BEFORE census |
| `before/lower-diagnose/*` | `scripts/lower-diagnose artifacts/cedar/cases/all --json --tsv --include cedark8s/cmd/schema-formatter,cedark8s/internal/schema` at main | the standing full-blocker report BEFORE |
| `wires-A/*` | `GO111MODULE=off go run ./tools/nativefrontend --dir Corpus/coverage/exec/<row> --out wires-A/<row>.wire.json 2> wires-A/<row>.stderr` at checkpoint A | wires of the exporting row dirs; first-refusal stderr of the refused ones |
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
