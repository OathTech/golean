# FR-4 per-declaration stencil quarantine + memo §3 row M (slices.Sort intercept retired) — cedar-go before/after, twin re-pin (2026-09-04)

Lane `fr4-rowm` ([AGENT] worker; the coordinator brief relayed the [USER]
rulings cited below — citation, never firsthand). Consuming docs:
`docs/language-coverage-ledger.md` §4 rows FR-4 (PARTIALLY CLOSED), FR-27,
FR-28 (born), §5 queue rows 4/27/28, §8n; `docs/2026-09-03_cedar-go-coverage-census.md`
§11 (addendum); `docs/2026-09-03_stdlib-boundary-design.md` §3 row M (DONE);
`docs/stdlib-admission-register.md` (the `intercept` class, the `slices` row,
the slice log); `docs/discrepancy-backlog.md` D-002 (note); `tools/lowerdiag/causes.tsv`;
`scripts/check-frontend-pins` (re-pin history). Tree: branch `fr4-rowm` off
main `9128e6c0` (3382 rows, 3172/210); the commit is named in the Gate
section. Host: linux/amd64 (shared build box, other lanes active — no
timing-sensitive numbers here). Toolchain: `go version go1.26.5 linux/amd64`
= `baselines/go-oracle-pin`; golean from `scripts/capped lake build golean`
on this tree (`GoLean/` untouched — the binary is main's, seeded by copying
main's `.lake/`).

## Conclusion (one paragraph)

(A) A method STENCIL whose body does not lower is a per-declaration,
signature-carrying stub under its instantiation's key (`mono.go
quarantinedStencilStub`, reusing H-3's `quarantinedMethodStub` under the
stencil's substitution; SIGNATURE-OPAQUE mode composes FR-23's `iter.Seq`
marker); the export survives, satisfaction stays exact, calls refuse by
name with the inner cause. (B) The `slices.Sort` machine-op intercept —
the register's last `intercept` row — is retired: `slices.Sort` is the real
`pdqsortOrdered` stencil at every ordered kind, including inside `init()`;
the `sortSlice` op and `sort-slice` wire node are unreferenced (deletion
owed to the hygiene arc; no `GoLean/GoCore` change here, no wire-schema
change). On cedar-go the two whole-export kills of census §10.2 (25 + 4 of
34 cases) are gone: EXPORT-OK 5 → 25 of 34; the 8 functional drivers now
reach the machine and stop at a per-declaration stub (fmt verbs, io.EOF,
encoding/json, net/netip, and two newly rowed shapes FR-27/FR-28) — every
first refusal classified. The raft twin pin MOVED as row M predicted
(nine `sort-slice` nodes → static calls to `slices.Sort[[]uint64,uint64]`
+ 16 stencils; 0 removed, 0 types/globals changed).

## Decisions ([AGENT] unless marked)

- [USER] (relayed, cited as relayed): the frontier queue is ratified with
  FR-4 at slot 4; the stdlib plan G1-G9 «(3) agree, go ahead with the
  plan» — memo row M names this retirement; direction 3 (every detected
  gap rowed with a plan), direction 4 (report every blocker — lower-diagnose
  before/after); posture «break rather than preserve incorrect behaviour».
- D1: a stencil stub classifies (tools/lowerdiag) by its INNER cause — the
  row whose plan unblocks it — with the FR-4 `stencil-refusal` row moved
  LAST as the fallback for a stencil whose inner cause no row knows (never
  UNCLASSIFIED). Audit fix round M3 (lane fr24) had made the whole-export
  text classify FR-4 because the KILL was FR-4's; the kill is gone.
- D2: FR-4 is PARTIALLY CLOSED, not RETIRED: the FR-4-shaped residual is
  a stencil whose SIGNATURE does not lower even in opaque mode
  (`sigRefusal`, shared with H-3), and an instantiated TYPE whose field type
  does not lower (FR-26's neighbourhood) — both still whole-export.
- D3: `anonymousTypeRefusal` — a `box[localT].m()` call used to refuse
  "method on anonymous type main.box[main.localT]" (lowerdiag: FR-13); it
  now re-raises mono.go's C6 text. Found by
  `TestQuarantinedStencilRollbackKeepsSharedInstantiation`; six sites.
- D4: the `sortSlice` op is reachable ONLY through the retired intercept
  (`sort-slice` was emitted by `emitSortStmt` alone — grep at the
  retirement); it is dead code from the wire's point of view. Its deletion
  (Syntax/Machine/Ops/eqb/Race/NPDRF + the NativeToIR arm) is OWED to the
  hygiene arc (`hygiene-wave3` owns GoCore concurrently — not touched).
- D5: the `go-sort` row (`go slices.Sort(s)`) is kept STRICT with a declared
  `depth=64` (the sizing convention, min 64) rather than routed confluent:
  the real pdqsort goroutine consumes picks past the 8-entry fixed streams
  (measured: 1 wide pick after exhaustion at consumption 8, default w=2).
- D6: FR-27 (explicit instantiation of a qualified source generic,
  `mapset.Immutable[EntityUID](args...)`) and FR-28 (BUG-062's recorded
  len/cap-hoist residual) are ROWED with plans, not fixed here (scope: FR-4
  + row M). A causes.tsv row each, plus `imported-type-zero-value` (FR-14)
  for the machine-side `default value for imported named type net/netip.Addr`.
- D7: the twin re-pin is taken as the ruled consequence of row M
  (`twin-repin/structural-diff.txt` enumerates it: 16 funcs added, 9 bodies
  changed, 0 removed, 0 `sort-slice` nodes remain).

## cedar-go: before (main 9128e6c0) → after (lane tip)

`before/` and `after/`: `results.tsv` (per case), `histogram.tsv`,
`demand-histogram.tsv` (census), `lower-diagnose-report.txt`. Per case
(34): EXPORT-OK 5 → 25; FRONTEND-REFUSED 29 → 8 (all 8 now `at run`, a
per-declaration stub — never at export); MACHINE-REFUSED 0 → 1
(`drv-ext-ipaddr`: `default value for imported named type net/netip.Addr`).
Transitions: 5 stay EXPORT-OK; 20 FRONTEND-REFUSED → EXPORT-OK; 8 stay
FRONTEND-REFUSED (at run); 1 → MACHINE-REFUSED. Before, the 29 first
refusals were 25 × FR-4 (`method stencil …ImmutableMapSet[EntityUID].All
does not lower … FR-4`) + 4 × `slices.Sort at non-integer element type
string`. After, the 8 + 1: see census §11.2's table (fmt verbs ×3,
io.EOF ×2, json.Unmarshal, FR-27, FR-28, netip zero value). Static
(`lower-diagnose`): 1455/1569 (92.7%) → 1460/1569 (93.1%) declarations
demanding nothing refused; export kills 3 → 2 declarations, 7/24 → 5/24
packages; the `slices-sort-kind` cause (9 decls) left the table.

## Corpus movement (the differential, `ci-diff.txt`)

FLIPPED FAIL→PASS (4): `generics/stencil-quarantine/sibling` (the FR-4
witness), `slices/slices-sort-non-integer-refusal`,
`stdlib-source/sort-op-shapes/{defer-sort,go-sort}`. BORN (18 at the slice
+ 2 residual pins at the audit fix round A5 = 20): 
`generics/stencil-quarantine/{stencil-call-refuses,iface-satisfied,
iface-dispatch,transitive-lowers,transitive-call,dedup-second-body,
local-type-c6}` (7: 3 PASS / 4 FAIL by design), `generics/stencil-quarantine-iterseq/
{sibling,satisfies,call}` (3: 2 PASS / 1 FAIL by design),
`slices/slices-sort-kinds/{string,named-string,float-nan-first,
float-signed-zero,float32,named-float,string-large,init-sort}` (8 PASS),
`generics/stencil-residual-{sig-anon-struct/sibling,field-iterseq/healthy}`
(2 FAIL by design, whole-export kills — the FR-4 residual).
Every existing `slices.Sort` row (`slices/slices-sort*`, `quorum/
committed-index-real/*`, `stdlib-source/slices-sortfunc/others`) stays
PASS through the real generic. 0 PASS→non-PASS. Figures: see the Gate
section and ledger §8n.

## Gate

Slice commit `88445d1c` (branch `fr4-rowm` off main `9128e6c0`; this
README's gate paragraph and the `ci-diff.txt` transcript land in the
records follow-up commit — the tree the gate certified is `88445d1c`,
which the follow-up changes only under `docs/evidence/`).
`scripts/capped scripts/ci --diff` at `88445d1c` (clean tree):
**RESULT: PASS** — `differential coverage summary: cases=3400 pass=3189
fail=211 export_status=0`; baseline re-pin guard (HEAD-vs-HEAD~1) clean,
0 PASS→non-PASS; frontend pins ok (realized init-order deviation + twin
wire = pinned bytes `4ee39f73…`; stdlib pin 61 files unchanged); stdlib
admission register = frontend tables; `go test ./tools/nativefrontend`
(incl. the four new FR-4 stencil tests, the row-M shape test, wire-
integrity, determinism) and `go test ./tools/lowerdiag` (causes.tsv vs
ledger, calibration vs wire, vocabulary) ok; check-spec-anchors,
check-bugs, check-coverage ok; eval tests 148 ok; reconciler 3 findings,
**0 HIGH** (C13 historical Go versions and C5 FR-7's `=` citation pre-date
this lane; **C14 did NOT** — this lane's D-002 note had been appended to
the `review by` cell, making `2026-10-31` unparseable; pristine main shows
2 findings. Corrected at the audit fix round A1: the note moved to the
description cell, the date restored, C14 gone). The
drift run BEFORE the re-pin (same tree content, dirty) is
`ci-diff-1-drift-run.txt`: its baseline diff lists exactly the 18 born
rows and 4 FAIL→PASS flips, nothing else.

## Audit fix round A1–A10 (2026-09-04, verdict FIX-FIRST)

- A1 D-002 `review by` cell restored (`2026-10-31`), note moved to the
  description; the gate paragraph above corrected (C14 was this lane's).
- A2 `tools/lowerdiag`: the retired whole-export stencil text is a TRIPWIRE
  row again (`stencil-kill-tripwire`, FR-4 export, before
  `imported-generic-inst`); `classifyText` strips `at run: `,
  `frontend-quarantined: `, the stub's closing clause and the FR-4 wrapper
  before matching, so anchored rows match inside a stencil stub (the
  `drv-eval-operators` text now classifies FR-27, not generics-corner);
  `TestStencilTripwireAndWrapperStripping`.
- A3 `NativeToIR.lean`: the `sort-slice` decoder arm and its key list are
  GONE — the node is refused by name (`unsupported statement sort-slice`);
  eval tests pin the refusal and that `clear-slice` of the same shape still
  decodes. A wire-schema move (C9 fires; the train re-certs). The GoCore op
  stays — hygiene arc item **A11** (dated OWED) rows its deletion.
- A4 `after/` regenerated at the tip (59-row causes table): FR-27 ×3, FR-28
  ×2 replace the unrowed generics-corner/expression-shape hits; census §11.2
  says so.
- A5 two FR-4 RESIDUAL pins, red by design on FR-4's line:
  `generics/stencil-residual-sig-anon-struct/sibling` (stencil signature
  unlowerable even opaque → `sigRefusal` whole-export kill) and
  `generics/stencil-residual-field-iterseq/healthy` (instantiated type with
  an `iter.Seq[T]` field reached from a zero-valued local → the TypeDef
  stencil kill; a composite literal in the body quarantines per declaration
  instead — measured, and the row says why the local is zero-valued).
- A6 `interceptedLibraryCall` fails CLOSED: the empty table is an explicit
  early return; a member LISTED without an arm (`interceptedMemberArm`) is a
  NAMED refusal at the reach walk and in defer/go position;
  `TestInterceptedLibraryCallFailsClosedOnListedMemberWithoutArm`.
- A7 records: latitude inventory §R13 (mechanism = the real pdqsort
  stencils; row M done), dossier-r13 note, ledger FR-14 (deleted refusal
  text), memo §3 row M / register slice log "10 sites" → 9 (progress.go's
  call is inside an H-3 stub), Machine.lean:1016 comment (dead since
  2026-09-04; A11).
- A8 `anonymousTypeRefusal` re-raises via `instTypeIdForWire` (both the C6
  key refusal and enqueueTypeInst's FR-23); no emission path reaches the
  anonymous-type text before the type refuses, so the helper is pinned
  directly (`TestAnonymousTypeRefusalNamesEnqueueCause`).
- A9 rowed on FR-26: the TypeDef-stencil kill names the LAST-emitted
  function (`curFuncName` leak) — not this lane's fix.
- A10 `generics/stencil-quarantine-iterseq/call` counted on FR-23's line
  only (FR-23 4 → 5 reds, FR-4 3 + 2 residual); lowerdiag emits
  repo-relative keys (`relativizeKey`); the census `results.tsv` detail
  column still carries the frontend's absolute position text — stripped
  in the evidence copy by `sed "s|$PWD/||"` (recorded here).

### Gate after the fix round

`scripts/capped scripts/ci --diff` at `7c858b6a` (clean tree): **RESULT:
PASS** — `cases=3402 pass=3189 fail=213 export_status=0` (the two A5
residual pins born FAIL, pre-pinned; 0 PASS→non-PASS, re-pin guard clean);
frontend pins ok — twin wire UNCHANGED at `4ee39f73…` (A3 is decoder-only);
stdlib register = tables; frontend unit tests (incl. the A6 fail-closed and
A8 tests), lowerdiag tests (incl. the A2 tripwire), eval tests (incl. the
A3 `sort-slice` refusal) ok; check-spec-anchors / check-bugs / check-coverage
ok. Reconciler at the tip: **C13 + C5** (FR-7's pre-existing `=` citation)
+ the C9 certified-record currency note the coordinator expects from the
decoder move — **C14 GONE, 0 HIGH**. Transcript: `ci-diff-fix-round.txt`.

## Files

- `before/`, `after/` — census + lower-diagnose records (absolute worktree
  paths stripped to repo-relative).
- `twin-repin/structural-diff.txt` — the JSON diff behind the twin re-pin
  (`b4458244…` → `4ee39f73…`).
- `ci-diff.txt` — the clean gate's transcript from the baseline diff to the
  summary (`88445d1c`); `ci-diff-fix-round.txt` — the same at `7c858b6a`
  (the audit fix round); `ci-diff-1-drift-run.txt` — the pre-re-pin drift
  run's tail (the 22-line drift list = the movement).

## Reproduction (from the repo root, on the lane tip)

```
scripts/setup-deps --only go,goose,cedar-go,cedar-access-control-for-k8s
scripts/capped lake build golean
scripts/cedar-census run                         # -> artifacts/cedar/{results,histogram,demand-histogram}.tsv
scripts/lower-diagnose artifacts/cedar/cases/all --tsv --out artifacts/lower-diagnose/after
# the twin diff: assemble as scripts/check-frontend-pins does, then
GO111MODULE=off go run ./tools/nativefrontend --dir <assembly> --out <new.wire.json>
python3 -  # the JSON diff at the head of twin-repin/structural-diff.txt
scripts/capped scripts/ci --diff
```
(the `before/` records were produced by the same commands at main
`9128e6c0` on this worktree before any frontend edit.)
