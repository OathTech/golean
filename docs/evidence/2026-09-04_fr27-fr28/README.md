# FR-27 qualified explicit instantiation + FR-28 make-hoist guard / nil-deref transparency — cedar-go before/after, M1 table re-measured (2026-09-04)

Lane `fr27-fr28` ([AGENT] worker; the coordinator brief relayed the [USER]
rulings cited below — citation, never firsthand). Consuming docs:
`docs/language-coverage-ledger.md` §2 (Order_of_evaluation,
Length_and_capacity), §4 rows FR-27 (RETIRED) and FR-28 (PARTIALLY CLOSED),
§5 queue rows 27/28, §8 headline + bucket table, §8o;
`docs/2026-09-03_cedar-go-coverage-census.md` §12 (addendum); `docs/BUGS.md`
BUG-083 (fixed AS A NAMED REFUSAL), BUG-032 (FR-28 amendment), BUG-062
(note); `tools/lowerdiag/causes.tsv` rows `explicit-instantiation-call`,
`len-hoist-panic-order`; `baselines/native-full.tsv` (re-pin header).
Tree: branch `fr27-fr28` off main `56982423` (3402 rows, 3189/213); the
slice commit is named in the Gate section. Host: linux/amd64 (shared build
box, other lanes active — no timing-sensitive numbers here). Toolchain:
`go version go1.26.5 linux/amd64` = `baselines/go-oracle-pin`; golean from
`scripts/capped lake build golean` on this tree (`GoLean/` untouched — the
binary is main's, seeded by copying main's `.lake/`; the gate rebuilt it
no-op). deps: go @ c19862e5f8, goose @ 3be88bb, cedar-go @ cda92d0,
cedar-access-control-for-k8s @ 660c637 (`scripts/setup-deps`).

## Conclusion (one paragraph)

(A) FR-27: an explicit instantiation whose base is a package-qualified
selector (`gset.Immutable[string](…)`, cedar-go's
`mapset.Immutable[EntityUID](args...)`) lowers in callee and value
position: `genericFuncUse` (emit.go) resolves the `SelectorExpr` base to the
generic `*types.Func` and hands `funcInstanceAt` the selector's identifier —
the SAME stencil the inferred spelling registers; any SOURCE package
qualifies (main, case-local, source-through stdlib: `slices.Index[[]int,
int]` stencils the real generic); a qualified instantiation into a stdlib
package the register does NOT admit refuses BY NAME on FR-14's value-
position text. FR-27 RETIRED; 7 rows (6 PASS + `stdlib-refused` red by
design). (B) FR-28: the A6 unordered-panic guard is `hoistReordersPanic`
(BUG-032's predicate pair) and `emitMake` calls it over every size/hint
operand, so BUG-083's silent wrong answer (`iv.(int) + len(make([]int,
t[k]))` realizing the hint's panic) is a named refusal — at the priced cost
of refusing the M1 table's four gc-MATCHING index/division/nil-deref-left
shapes too (conservative guard; posture «break rather than preserve
incorrect behaviour», relayed). Two exact refinements narrow the refusal:
nil-deref-ONLY compositions are order-transparent (one runtime error,
nothing effectful between the two tests) — cedar-go's lexer idiom `l.pos <
len(l.src) && l.peek()` lowers; a map read with a non-interface key is
panic-free. `residualPanicFreeOperand` recurses into an inline builtin's
operand (hole closed). FR-28 PARTIALLY CLOSED: the residual — two panics of
differing kind on the two sides — stays refused until BUG-032's
linearization. cedar-go: 25/34 EXPORT-OK unchanged in category; the two
witnesses lower and their drivers stop at FR-14 stubs further in;
histogram FR-27 ×3 → 0, FR-28 ×2 → 0; static census unchanged (these are
dynamic-pass judgements). Twin wire pin unchanged.

## Decisions ([AGENT] unless marked)

- [USER] (relayed, cited as relayed): the frontier queue is ratified with
  FR-27/FR-28 at slots 27/28; direction 3 (rowed gaps fixed in queue order
  with plans), direction 4 (`scripts/lower-diagnose` before/after); posture
  «break rather than preserve incorrect behaviour».
- D1: the qualified base resolves ONLY for source packages
  (`isSourcePackage`); a non-source-through stdlib generic refuses by name
  with FR-14's `stdlib-qualified selector <pkg>.<F> in value position` text
  (handled=true, never the shape-blind fallback) — the admission answer is
  the register's, not the arm's. The arms' remaining fallback names the
  shape and the base's kind (`explicit instantiation … the base (%T) is not
  a generic function of a source package — FR-27 residual`); the old
  `generic instantiation <pos>` text is RETIRED and kept as a causes.tsv
  tripwire.
- D2: the make guard has NO "ordered event after" condition — the make hoist
  is unconditional, so the reorder is unconditional. It applies to every
  size/hint operand (slice len+cap, map hint, chan cap).
- D3: nil-deref transparency (BUG-032's FR-28 amendment has the argument):
  taken because the two candidate panics are the SAME runtime error with no
  effect between them; pinned on all four nil-ness combinations for len and
  for make (`{len,make}-nil-only-*`) and on the lexer idiom; the arm is
  nil-deref ONLY (`len-assert-vs-nil-operand`, `len-nil-left-vs-index-
  operand` red by design). Conservative on anything not recognized.
- D4: map reads with a non-interface key type are panic-free
  (spec#Index_expressions); an interface-typed key can still panic on an
  uncomparable dynamic key and keeps the conservative answer.
- D5: `gAssertVsHintCall` (`iv.(int) + len(make(map, boom()))`) and
  `gAssertVsPlainCall` are NOT refused and NOT pinned: the hint is a real
  call whose residual is its temp (BUG-032's F23 arm) — E13's call-first
  family, where E13 forbids a pin. BUG-083's original instance list put the
  `boom()` shape beside the hint shapes; its mechanism is E13's. Recorded on
  BUG-083.
- D6: TENSION recorded for the audit (on BUG-083, ledger §8o): E13 reads the
  assert-vs-sibling-call axis as latitude with no pin and `make` is a call
  ("called like any other function"), so the make guard is STRICTER than
  E13's treatment of `min`/`max`/user calls (which still run first). The
  refusal is honest under either reading; the brief asked for it.
- D7: BUG-083 → `Status: fixed`, `Pinned-by: none`, `Expect: FAIL` (the
  BUG-070/078/084 precedent for red-by-design refusal pins; check-bugs (3)
  forbids a FAIL row on a fixed differential entry). The four make rows are
  counted on FR-28's frontier line in §8 (the FR-28 refusal is what they
  exhibit) and listed on BUG-083's Cases line (existence-checked);
  `hint-panicky-between` stays in the post-vintage bucket (stage change
  only).
- D8: `scripts/lower-diagnose` was run over the ASSEMBLED whole-library case
  (`artifacts/cedar-<before|after>/cases/all`), as §11 did — the raw
  `deps/cedar-go` checkout has dotted import paths the loader refuses by
  design (its first-refusal record is the loader's type-check failure, not a
  coverage fact; not copied here).

## cedar-go: before (main 56982423) → after (lane tip)

`before/` and `after/`: `results.tsv` (per case), `histogram.tsv`,
`demand-histogram.tsv` (census), `lower-diagnose-report.txt` (static, the
whole-library case). Per case (34): EXPORT-OK 25 → 25; FRONTEND-REFUSED
8 → 8 (all `at run`, per-declaration stubs); MACHINE-REFUSED 1 → 1
(`drv-ext-ipaddr`, `net/netip.Addr` zero value). No category transition.
First refusals that MOVED: `drv-eval-operators` FR-27
(`mapset.Immutable[EntityUID]`) → FR-14 `maps.Keys`; `drv-validate` FR-28
(`lexer.skipWhitespaceAndComments`) → FR-14 `fmt.Errorf` verb
(`resolved.resolverState.resolveEntities`). Whole-library case `all`:
quarantined 571 → 567 (`cedargo.NewEntityUIDSet`, `types.NewEntityUIDSet`,
`lexer.scanIdent`, `lexer.skipWhitespaceAndComments` → lowered;
`doInEval` lowers past the instantiation and stops at `iter.Seq[types.
Value]`, FR-23 — histogram 7 → 8). Histogram: FR-27 ×3 → 0, FR-28 ×2 → 0,
nothing else moved; 0 UNCLASSIFIED. Static (`lower-diagnose`): UNCHANGED
1460/1569 (93.1%), funcs+methods 980/1086 (90.2%), refused 108, export
kills 2 declarations / 5 of 24 packages (FR-27/FR-28 are "not judged
statically").

## The M1 table re-measured (`m1-table.tsv`)

The BUG-083 probe bodies (copied verbatim to `m1-probes/`) at the FR-28
frontend: 7 REFUSED by name (the 3 assert-left WRONG shapes + the 4
gc-MATCHING index/division/nil-deref-left shapes — the priced trade), 6
lower (`fHintIndexVsRightIndex` — nothing to the left; `gAssertVsNewCall`;
`gAssertVsHintPlainVar`; `gAssertVsMapIndexHint` — refinement D4;
`fLeftIndexHintCallPanic`, `gAssertVsHintCall`, `gAssertVsPlainCall` —
call residuals, E13). Corpus rows in the table's last column re-measure gc
through the harness for every shape that has one.

## Corpus movement (the differential)

STAGE CHANGE (FAIL → FAIL): `builtins/len-vs-call-order/hint-panicky-between`
differential → frontend-export. BORN (25): `generics/qualified-instantiation/
{call,func-value,nested,method-value,method-expr,source-through}` PASS,
`stdlib-refused` FAIL by design; `builtins/len-vs-call-order/{make-hint-
panic-free,make-hint-call,make-hint-map-read}` PASS (guard controls),
`{len,make}-nil-only-{none,left,operand,both}` PASS, `lexer-idiom` PASS,
`{make-slice-panicky-between,make-chan-cap-panicky-between,make-index-left,
make-inner-len,len-assert-vs-nil-operand,len-nil-left-vs-index-operand}`
FAIL/frontend-export by design. 0 PASS→non-PASS. 3402 + 25 = 3427 = 3207 /
220 (ledger §8o).

## Reproduction (repo root)

```
scripts/setup-deps --only go,goose,cedar-go,cedar-access-control-for-k8s
# cedar-go census, before = main 56982423 / after = the slice commit (checkout each):
GOLEAN_BIN=$PWD/.lake/build/bin/golean CEDAR_CENSUS_ARTIFACTS=artifacts/cedar-<before|after> scripts/cedar-census run
scripts/lower-diagnose artifacts/cedar-<before|after>/cases/all --tsv --out artifacts/lower-diagnose/<before|after>
#   -> results.tsv / histogram.tsv / demand-histogram.tsv from artifacts/cedar-<w>/, report.txt from
#      artifacts/lower-diagnose/<w>/artifacts__cedar-<w>__cases__all/ (absolute worktree prefix stripped with sed)
# M1 table (frontend column):
export GO111MODULE=off GOCACHE=$PWD/artifacts/go-build-cache
for p in p4 p5; do D=artifacts/m1-probes/$p; mkdir -p $D; cp docs/evidence/2026-09-04_fr27-fr28/m1-probes/$p-body.go $D/body.go
  printf 'package main\n\nfunc main() {}\n' > $D/main.go
  grep -q "func boom" $D/body.go || printf '\nfunc boom() int { panic("boom-call") }\n' >> $D/body.go
  grep -q "func zero" $D/body.go || printf '\nfunc zero() int { return 0 }\n' >> $D/body.go
  go run ./tools/nativefrontend --dir $D --out $D/wire.json
  python3 -c 'import json,sys; [print(f["name"], "REFUSED" if "unsupported" in f else "lowers") for f in json.load(open(sys.argv[1]))["funcs"]]' $D/wire.json
done
# focused differential:
scripts/capped scripts/diff-one generics/qualified-instantiation/call builtins/len-vs-call-order/lexer-idiom  # etc.
# gate:
scripts/capped scripts/ci --diff
```

## Gate

Slice commit `6441bd37` (branch `fr27-fr28` off main `56982423`; this
README's gate paragraph and the `ci-diff.txt` transcript land in the
records follow-up commit — the tree the gate certified is `6441bd37`, which
the follow-up changes only under `docs/evidence/`).
`scripts/capped scripts/ci --diff` at `6441bd37` (clean tree):
**RESULT: PASS** — `differential coverage summary: cases=3427 pass=3207
fail=220 export_status=0`; `baseline diff FULL (3427/3427, no regression)`;
`re-pin guard (0 PASS→non-PASS flip(s), all listed in BUGS.md Cases)`;
`frontend pins (realized init-order deviation + twin wire = pinned bytes)`
— the twin wire pin 4ee39f73… UNCHANGED; `stdlib admission register =
frontend tables`; `spec-anchor citations resolve at the pin`; frontend unit
tests + lowering-diagnostic tables green; `check-bugs: ok (92 bug(s))`;
reconciler 3 finding(s), 0 HIGH (the three MEDIUMs — C13 historical Go
version strings, C5 FR-7's pre-existing `=` citation, C9 the wire-schema
commit 65272847 of lane fr4-rowm vs the certified set's date — are all
pre-existing on main 56982423). Transcript: `ci-diff.txt` (absolute
worktree prefix stripped). An earlier full run on the DIRTY tree before the
records were finished also passed (3427/3427, 0 flips) and is not kept.
