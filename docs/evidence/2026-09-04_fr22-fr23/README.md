# FR-22 / FR-23 — two whole-export kills made per-declaration (2026-09-04)

Lane `fr22-fr23` ([AGENT] worker; coordinator brief relayed the [USER]
rulings cited below — citation, never firsthand). Consuming docs:
`docs/language-coverage-ledger.md` §4 rows FR-22, FR-23, FR-24, §5, §8i;
`docs/2026-09-03_cedar-go-coverage-census.md` §9 (addendum);
`docs/stdlib-admission-register.md` (class `init-callee`, slice log).
Tree: commit <SHA> on branch `fr22-fr23` (clean; the gate tail below
names the exact tree it certified). Host: linux/amd64 (shared build box,
other lanes active — no timing-sensitive numbers here). Toolchain:
`go version go1.26.5 linux/amd64` = `baselines/go-oracle-pin`; golean
from `scripts/capped lake build golean` on this tree.

## Conclusion (one paragraph)

Both census kills are gone as KILLS: a `time.Date` package-level
initializer now poisons its var per declaration (the var's cell seeds
as the reserved `$poisoned` placeholder; every reference refuses by name
naming the var and the callee; the healthy initializers keep their
order), and an imported generic instantiation in a method / func /
interface / promoted-method SIGNATURE is an opaque marker under its
mangled TypeId so the declaration is a fail-closed stub, satisfaction
stays exact, and every CALL refuses by name. Neither MEMBER lowers —
FR-22's residual (unregistered callees, non-isolated dependents) and
FR-23's residual (the calls; FR-12 for their `range` bodies) stay red by
name — so both rows are PARTIALLY CLOSED, not retired. No wire-schema
change (the D5 marker shape + a `named`/`struct` placeholder), no GoCore
change, the twin wire pin did not move. On cedar-go the export fraction
is UNCHANGED (5/34): the next kill is FR-24 (rowed here: a reached
library var whose type does not lower — `binary.Write` → `structSize
sync.Map`), and behind it (pass C, counterfactual) FR-4 and a
`slices.Sort`-at-string `init()`.

## Decisions ([AGENT] unless marked)

- D1 [AGENT]: FR-22 is NOT made per-declaration for arbitrary callees.
  The brief asked for poisoning "outside the allowlist"; the standing
  H-11 soundness argument (audit F1/F1b, 2026-08-20 — a skipped
  effectful or panicking initializer is a machine run gc never
  performs) forbids it, so the sound reading was taken: the allowlist
  becomes a register class with per-row arguments, `time.Date` is
  admitted with its argument, and unregistered callees keep the
  whole-export refusal — now NAMING the var, the callee and the
  register. Raised in the report for the coordinator/[USER].
- D2 [AGENT]: poisoned cells seed as `$poisoned` (uniformly, not only
  when the real type has no default) — the placeholder is the honest
  description of what the machine holds, the cell is unreachable, and
  the poison becomes visible on the wire. The twin has no poisoned var,
  so the pin is unaffected (checked before landing and by the gate).
- D3 [AGENT]: the opaque marker is minted ONLY inside `withOpaqueSigs`
  (stub signatures, interface requirement lists, promoted-method stubs);
  a body use refuses at `enqueueTypeInst` as before. An imported generic
  instantiation used as a type ARGUMENT of a SOURCE generic in a
  signature (`Box[iter.Seq[int]]`) still refuses whole (type-stencil
  policy) — unchanged from before, recorded as a known edge.
- D4 [AGENT]: FR-24 is rowed, not fixed (scope: the brief's two kills);
  posed as the smallest-diagnosed next item. The FR-4 stencil refusal is
  made to NAME its stencil (guard-strengthening only).
- D5 [AGENT]: the pass-C relaxation (`record.go:35` `binary.Write` →
  byte-identical `PutUint64` + `Write`) on the census COPY, labelled
  counterfactual, never `deps/`.

## BUG-091 (coordinator addition, 2026-09-04): emitter output determinism

Finding (lane `hygiene-a-series`, relayed by the coordinator): `emit.go`'s
goto restructuring refused by ranging a Go MAP (`for name := range
e.gotoLabels`), so the refusal text — and, since the refusal lands as a
per-declaration STUB, the WIRE BYTES — varied between runs (26× `next`,
4× `fallback` in 30 runs of one 2-label program). Fix: collect, `sort.
Strings`, loop (`// deterministic refusal message (BUG-091)`), the same
shape `emit.go` already used at its two other sorted refusal sites.

- `bug091-red-first.txt` — `TestEmitIsDeterministic` (20 emissions of a
  2-label goto shape and of a multi-quarantine shape, byte-compared) run
  against MAIN's emitter (`git archive 415f959a tools/nativefrontend` +
  the test file): FAILS at emission 14 (`next` vs `fallback` in the stub's
  `unsupported` text). Green on this branch; the test is the standing
  guard.
- `bug091-map-range-audit.tsv` — EVERY `for … := range <map>` in
  `tools/nativefrontend` (57 sites, go/types-typed inventory, not a grep),
  each classified: SORTED / SET / FIXPOINT / INTERNAL, or FIXED. Three
  FIXED: `emit.go` goto labels (the reported one), `langversion.go:178`
  (a build-constraint refusal returned on the FIRST reserved tag of a
  multi-tag constraint), `stdlibreach.go:580/585` (the library
  layout-constant scan returned on the FIRST reached type/value spec that
  hit — now visited in source-position order). No site was found where
  method-set order, field order or import order reached the wire
  unsorted (those tables were already sorted: interface anchors, method
  sets, imported-named markers, file order at the E8 site).
- BUG-091's BUGS.md entry is being filed by `hygiene-a-series` and is not
  on main at this branch's base; the fix + guard land here, and the entry
  is to be marked fixed (Cases: none — a frontend nondeterminism, not a
  differential row; guard = the unit test) at whichever landing comes
  second. [AGENT] note for the coordinator.

## Files

| file | producer | what |
|---|---|---|
| `ci-diff-run1.txt` | `scripts/capped scripts/ci --diff` on the uncommitted slice tree at 415f959a, BEFORE the re-pin | the run the re-pin consumed: 3365 rows, the DRIFT block (below), re-pin guard 0 PASS→non-PASS; its two expected reds (baseline DRIFT; the `godoc:time.Date` anchor, replaced before run 2) |
| `ci-diff.txt` | `scripts/capped scripts/ci --diff` on the COMMITTED, rebased tip (tail) | the clean-tip gate: RESULT PASS, 3365/3365 no regression, reconciler 0 HIGH |
| `baseline-drift.txt` | `diff <(git show 415f959a:baselines/native-full.tsv \| grep -v '^#') <(grep -v '^#' baselines/native-full.tsv)` | every row that moved: 2 FAIL→PASS, 15 born, 0 PASS→non-PASS |
| (in `ci-diff*.txt`) | `scripts/check-frontend-pins` (a ci step) | twin wire 69a538de… + hidden-dep + stdlib pin (61 files): all ok, no pin moved |
| (in `ci-diff*.txt`) | `scripts/check-stdlib-register` (a ci step) | the register block equals the code's tables (class `init-callee`, 3 rows) |
| (in `ci-diff*.txt`) | `go test ./tools/nativefrontend` (a ci step) | frontend unit tests incl. `perdecl_kill_test.go` (7 tests) and `determinism_test.go` (BUG-091 guard) |
| `cedar-passA-prime.txt` | pre-landing preview with the prototype frontend (header names the command) | 29 FRONTEND-REFUSED (all `sync.Map`) / 5 EXPORT-OK |
| `census-passA-prime/` | `scripts/cedar-census run` on THIS branch (git_commit in `meta.tsv`) → `results.tsv`, `census.tsv`, `histogram.tsv`, `per-package.tsv`, `meta.tsv` | the landed-tree census: identical categories (29 / 5), every refusal `sync.Map` |
| `cedar-passC.txt` | the pass-C loop in the addendum §9.3 (commands inline in the file header) | 25 FR-4 + 4 `slices.Sort` / 5 EXPORT-OK |
| `trace-syncmap.txt` | the two probe programs + emits that trace `sync.Map` to `binary.Write` → `dataSize` → `structSize` | the FR-24 diagnosis |
| `twin-precheck.txt` | prototype frontend over the twin assembly vs `baselines/pins/twin-chdriver.wire.json`, before landing | `cmp` equal |
| `wires/` | `GO111MODULE=off go run ./tools/nativefrontend --dir Corpus/coverage/exec/<row> --out …` for the 5 exporting rows; stderr for the 3 whole-export rows (`*.refusal.txt`) | the `$poisoned` globals table (`init_stdlib-initializer-poison.wire.json`: `maxDatetime`/`minDatetime`/`minAlias` typed `named $poisoned`; the unreferenced `time.*` D5 markers registered by collectGlobals before the poison are a harmless known residue), the opaque `iter.Seq[int]`/`iter.Seq2[string,int]` marker TypeDefs and stubs, and the three named whole-export refusals |
| `bug091-red-first.txt`, `bug091-map-range-audit.tsv` | see the BUG-091 section | the red-first run on main's emitter; the 57-site inventory |

## Reproduction

```
scripts/setup-deps --only go,goose,cedar-go --from <sibling>
scripts/capped lake build golean
GO111MODULE=off go test ./tools/nativefrontend
scripts/check-frontend-pins
scripts/check-stdlib-register
scripts/capped scripts/ci --diff
scripts/cedar-census run                       # pass A′
# pass C: copy artifacts/cedar/cases elsewhere, apply the record.go:35 sed in §9.3, re-drive with
#   GO111MODULE=off go run ./tools/nativefrontend --dir <case> --out <case>/wire.json
```
