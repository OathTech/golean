# Evidence — lane `e13-b`: latitude E13 option (b), the sibling panic order as a choice site (2026-09-05)

Design of record: `docs/2026-09-05_e13-b-design.md`. Ruling: E13 option (b)
RULED [USER] Mike 2026-09-05, verbatim as relayed by the [AGENT]
coordinator (cited as relayed, not firsthand): «we should do what the
standard supports, and avoid over-refusal if we can. That's what (b) means
right?». Worker [AGENT]. Tree: branch `e13-b` off main `b77f3298`. Host:
linux/amd64 (shared build box, other lanes active — no timing-sensitive
numbers here). Toolchain: `go version go1.26.5 linux/amd64` =
`baselines/go-oracle-pin`; golean from `scripts/capped lake build golean`
on this tree. deps: go @ c19862e5f8 (`scripts/setup-deps`).

## Conclusion (one paragraph)

The spec-unsequenced order of a panicky non-call operand (type assertion,
slice expression, interface comparison, index, dereference, division,
shift, slice→array conversion) against a SIBLING ordered event (call,
method call, receive, hoisted built-in) is now a machine choice:
`Stmt.unseqProbe` / `Cont.probeK` / `ChoiceSite.unseqPanic` (bound 2,
consulted only when the operand panics at its lexical position — DEFER =
the sibling events first, the pre-change machine's only member; RAISE =
the operand's panic first). The frontend emits `unseq-probe` at every such
operand's lexical position (`emitExpr`, one census `probeKind`), forced
positions (an event's own operands, assignment targets, `recover()`
operands) are never probed, and the A6 unordered-panic guard family
(`hoistReordersPanic` and its predicates; BUG-032/BUG-062/BUG-083, FR-28)
is DELETED — its refusals stood in for this latitude. gc's realization is
ONE member on every probed shape (EARLY for assertions/slices/comparisons,
LATE for index/deref/division/shift/conversion — `gc-realization.txt`),
certified inside the enumerated set on all 39 membership rows this lane
touches. Corpus: 12 FAIL→PASS (every id on a BUGS.md Cases line), 3
strict→membership lane moves, 31 born rows all PASS, 0 PASS→FAIL; tally
3498 = 3252 / 246 → 3529 = 3295 / 234. No row outside the E13 family moved
(the noodler value rows are singletons: the probe consults only on an
early panic). The twin wire pin moved by exactly 119 `unseq-probe`
statements (7 funcs + 33 methods, 0 other changes).

## Decisions ([AGENT] unless marked)

- [USER] (relayed, cited as relayed): option (b) — admit BOTH orders as
  latitude via a membership shape wherever the spec leaves the sibling
  order UNSEQUENCED; retire the make and len/cap refusals into it; FORCED
  positions stay gc-exact.
- D1: the choice is consulted on the PANIC PATH only (`.panicking _
  (.probeK _)`, bound 2 constant) — never at the probe statement itself.
  Consequence: an existing row acquires a pop only when an unsequenced
  operand actually panics early, so no non-E13 row's stream moved
  (design §3/§7; measured: 16 result/stage moves in the first full run,
  all E13 shapes).
- D2: `Cont.probeK` is its own `FrameClass` (`.probe`): not glue —
  `panicPassthrough` does not strip it, `recover` does not cross it, the
  statement travellers have no rule at it (unreachable; fail closed).
- D3: DEFER is `canonicalSlot0` — the empty stream reproduces every
  pre-change trajectory byte for byte (the default runs of the strict lane
  are unchanged).
- D4: the frontend never probes an event's OWN operands (`pushHoist`
  drops the trailing probes of the node being hoisted — F2), assignment
  TARGETS (`probeSuppress` — E2/E3/E4 are not this lane's), or an operand
  containing `recover()` (double evaluation would consume it; the decoder
  refuses such a probe by name as the fail-closed backstop). Trailing
  probes (no event after them in their sweep) are pruned at every
  accumulator capture.
- D5: the retired-refusal rows whose two orders COINCIDE observably stay
  strict (`panicky-between`'s witness is 0 either way; `len-assert-vs-nil-
  operand` and `len-nil-left-vs-index-operand`'s left operands cannot
  panic at run time; `make-hint-{panic-free,map-read,generic-int-key}`'s
  hints are panic-free) — a membership row on a singleton set is refused
  by the harness by design.
- D6: `expected_reason` on a panic-status membership row is the substring
  gc's draws carry (the pre-filter is over gc samples only; a draw on the
  other member would fail the row loudly — the honest outcome of the
  oracle moving). Rows whose members differ in status declare
  `statuses=`.
- D7: the twin wire pin is RE-PINNED under the ruling (`scripts/check-
  frontend-pins` history block cites it); the structural diff is
  `twin-repin/structural-diff.txt` — flagged for the audit (design §7).
- D8: BUG-083 → `Pinned-by: differential`, `Expect: FAIL` dropped (status
  change with its written reason on the entry: the refusal stood in for
  latitude); BUG-032's residual clause retired; FR-28 CLOSED; E6 tagged
  (a) via E13 (zero sites) so its history stays readable in place; E13
  (b) → (a); E13 left the known-≠-oracle list (doctrine register #2
  re-synced in the same change).

## gc's realization (`gc-realization.txt`, producer `probes/gc-realization.go`)

32 recover-based probes at go1.26.5; `w` is an effect witness the sibling
calls accumulate (`w=0` = the operand panicked before every sibling
event). EARLY: type assertion (a, e, g, j, k, l, n, r, s, w, w2, y, z,
z2), slice expression (p), interface comparison (p3). LATE: index (b, f,
i, j2, k2, m), nil dereference (c), integer division (d), shift (p2),
slice→array conversion (p4). Forced-position controls: v, x (the
argument's panic first — the machine's present behaviour, unchanged); u
(an operand RIGHT of the call: lexical order); o (a value — E12's pin).
Each realization is one of the two members the machine now offers.

## The machine, smoke-tested (`probes/machine-smoke.go`)

`native-json-run` under the default stream vs `--choices 1`, and
`coverage-observations` (width 2): `assertLeftCall` {5, 0}, `indexLeftCall`
{5, 0}, `callArgSibling` {7, 0}, `twoProbes` 2 observations over 2 sites,
`loopCond` {277056, 8937} (the loop condition's index vs the call, per
iteration), `forcedArg` a singleton (the argument never waits for the
call), `targetIndex` sites=0 (targets are not probed), `recoverOperand`
probes=0.

## Enumeration statistics (`enumeration-stats.txt`)

`golean coverage-observations --max-width 2 --max-sites 8 --cap 64
--work-cap 200000 --expect-status ok,panic` over every row of
`builtins/e13-sibling-panic-order`, `builtins/len-vs-call-order` and
`binop-order/operand-panic-vs-call`: observations, steps, probes (the
enumerator's own probe count, unrelated to `unseq-probe`), sites, leaves,
depth, and the observation set. Two-member sets on 37 rows, three-member
sets on `two-index-left-call` and `index-assert-left-call` (the
DEFER×RAISE interleaving), singletons on the strict controls and the
coincident-order rows.

## The focused run (`focused-run.log`, `focused-run-results.tsv`)

`scripts/capped scripts/diff-one` over the 65 touched rows: 65 PASS — 39
membership rows (`enumerated=N exhibited=1 draws=32 (K=32; pin members=N
NOT reached — 1 distinct drawn)`: gc's deterministic member inside the
set on every draw, plain and `-race` alternating) and 26 strict rows.

## gc draw tables (`gc-draws.tsv`)

Per membership row: the number of draws, the distinct observations drawn,
and each observation with its plain/-race counts (from
`artifacts/coverage/membership/<id>/draws.txt`).

## The full run at the lane tip (before the corpus edits) and the gate

`scripts/capped scripts/diff-coverage` over the untouched corpus at the
code tip (3498 rows): 16 result-or-stage moves, ALL E13 shapes —
`builtins/len-vs-call-order/{panicky-between,len-assert-vs-nil-operand,
len-nil-left-vs-index-operand}` FAIL/frontend-export → PASS; the nine
BUG-083 rows FAIL/frontend-export → FAIL/differential|nondet (two members,
strict rows — routed to membership in this slice); `make-hint-call`
PASS → FAIL/nondet and `binop-order/operand-panic-vs-call/{call-before-
left,call-before-left-div}` PASS → FAIL/lean-observation (a refusal under
a variant stream is reported there — the three strict rows that pinned
one member of a two-member set, routed to membership); plus
`channels/select-select/beside-loop`'s recorded stage alternation
(unchanged, kept verbatim in the re-pinned baseline). No other row moved
— in particular none of `noodler/latitude/*` (E12's value observable is
untouched, measured).

Gate: `scripts/capped scripts/ci --diff` at the lane tip — tail in
`gate-tail.txt`.

## Twin wire re-pin (`twin-repin/`)

`hashes.txt` (4ee39f73… → 11270c55…), `structural-diff.txt`: 430/430
functions, 537/537 methods, 0 added/removed; 7 functions and 33 methods
gain `unseq-probe` statements (119 in total, every probed operand a
`field-get` — pointer-selector reads such as `pr.Match` left of a method
call); stripping the probes makes every changed entry byte-identical to
the pinned one; no other top-level key changed. The twin driver reaches no
early panic on these operands, so its observations are unchanged.

## Reproduction (repo root)

```
scripts/setup-deps --only go,goose
scripts/capped lake build golean
# gc's realization:
mkdir -p .tmp/e13probe && cp docs/evidence/2026-09-05_e13-b/probes/gc-realization.go .tmp/e13probe/main.go
(cd .tmp/e13probe && GO111MODULE=off GOCACHE=$PWD/../gocache go run .)
# enumeration (per row): GO111MODULE=off go run ./tools/nativefrontend --dir Corpus/coverage/exec/builtins/e13-sibling-panic-order --out wire.json
.lake/build/bin/golean coverage-observations --input wire.json --function assertLeftCall --max-width 2 --max-sites 8 --cap 64 --work-cap 200000 --expect-status ok,panic
# focused differential:
scripts/capped scripts/diff-one builtins/e13-sibling-panic-order/assert-left-call builtins/len-vs-call-order/hint-panicky-between   # etc.
# twin wire structural diff: regenerate per scripts/check-frontend-pins §2 and run the python in twin-repin/structural-diff.txt's header
# gate:
scripts/capped scripts/ci --diff
```
