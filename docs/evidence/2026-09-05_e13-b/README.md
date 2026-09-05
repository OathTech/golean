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
was DELETED at the lane tip — its refusals stood in for this latitude
WHERE THE LEFT MATERIAL IS PROBED. AUDIT FIX ROUND (2026-09-05, [AGENT];
the adversarial audit returned BLOCK — see "The audit fix round" below):
on the material the envelope does NOT probe (assignment/IncDec/compound
targets, address-of operands, `recover()`, allocating conversions) the
deletion had turned a visible refusal into a silent single-member answer
≠ gc; a NARROWED A6 guard is reinstated there, a structural allocation's
panicky payload before an ordered event is refused, the value axis
reached through the len shape is BUG-101. gc's realization is
ONE member on every probed shape (EARLY for assertions/slices/comparisons,
LATE for index/deref/division/shift/conversion — `gc-realization.txt`),
certified inside the enumerated set on all 39 membership rows this lane
touches. Corpus at the lane tip b2fd9f15: 12 FAIL→PASS (every id on a
BUGS.md Cases line since the fix round — three sat in BUG-032's prose
only, audit R3), 3 strict→membership lane moves, 31 born rows all PASS,
0 PASS→FAIL; tally 3498 = 3252 / 246 → 3529 = 3295 / 234. The fix round
adds 10 born rows (1 PASS control, 8 refusals by design, 1 open BUG-101
red): the final tally is in "The audit fix round" below. No row outside
the E13 family moved (the noodler value rows are singletons: the probe
consults only on an early panic). The twin wire pin moved by exactly 118
`unseq-probe` statements after the fix round (119 at the lane tip; the D4
map-assign rule removed one — 7 funcs + 33 methods, 0 other changes).

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
  re-synced in the same change). FIX ROUND: FR-28 is CLOSED for probed
  material and REOPENED NARROWED; E6 re-enters inventory §5 narrowed;
  E13's obligation reads "measured-discharged for the probed axis".
- D9 (FIX ROUND, [AGENT]): the R2 disposition is (b) — REFUSE the
  structural-allocation composition — because (a) was measured not to
  reach gc's member (a deferred probe panic is re-raised by the
  allocation statement at the same early position; both slots panic
  with no output where gc prints `wit 5` first).
- D10 (FIX ROUND, [AGENT]): the single map-assign target path is brought
  under D4 (probing suppressed) rather than rowed as a membership set —
  one rule for every target; the twin loses one probe.
- D11 (FIX ROUND, [AGENT]): R12's explicit `.probeK` arms in `stepFn`'s
  travellers were NOT added — both an added arm and a nested match inside
  the catch-all shift `MachineSound`'s positional case tags (`case183`/
  `case184`/`case186`, three theorems) and reworking the verified core's
  proofs is outside this round; the reachability invariant is written at
  the `Step` rules (Machine.lean) and the catch-all `.internal` throw
  stands.

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
`artifacts/coverage/membership/<id>/draws.txt`). FIX ROUND (audit R10):
the `assert-left-recv-w` line read `draws=2` at the lane tip where
`focused-run-results.tsv` and the artifact carry 32 — the table had been
produced from an earlier 2-draw smoke artifact for that one row;
regenerated from the fix round's artifact (32 draws, 16 plain / 16 race,
one distinct observation).

## Enumeration statistics — one line is a REFUTED width (audit R12)

`enumeration-stats.txt` line 94 (`builtins/len-vs-call-order/slice`)
reads `site bound 30 exceeds the case's width 2 — the width assertion is
REFUTED`: that strict row (`lenVsCallSlice`, an `append` spill) was run
under the sweep's uniform `--max-width 2` for the statistics only — its
consuming site is `appendSpill` (bound 30), not `unseqPanic`; the line is
the enumerator refusing the sweep's width, not a finding about the row
(which is strict, PASS, and has no probe). Kept verbatim as the honest
output of the sweep.

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
`gate-tail.txt`. FIX ROUND (audit R6): the tail committed at b2fd9f15
was recorded on a DIRTY tree (`git_dirty=true` on both baseline notes —
it certified that worktree state, not the commit, while the commit body
claimed a gate at the tip). The fix round's gate ran on the CLEAN
committed tree and its tail REPLACES that file; the dirty-tree history is
stated here and in design §10.

## Twin wire re-pin (`twin-repin/`)

`hashes.txt` (4ee39f73… at main b77f3298 → 7c545840… at the lane tip
b2fd9f15 → d531a225… after the fix round; the lane tip's README and
`scripts/check-frontend-pins` wrote 11270c55…, a WRONG hash — audit R5,
corrected), `structural-diff.txt` (regenerated at the fix round against
b77f3298's pin): 430/430 functions, 537/537 methods, 0 added/removed; 7
functions and 33 methods gain `unseq-probe` statements (118 in total,
every probed operand a `field-get` — pointer-selector reads such as
`pr.Match` left of a method call); stripping the probes makes every
changed entry byte-identical to the pinned one; no other top-level key
changed. vs the lane tip's 7c545840…: exactly ONE probe fewer, on
`raft.readOnly.recvAck`'s map-assign TARGET `ro.acks[from] = max(…)` (D4,
audit R1); the narrowed A6 guard and the allocation guard fire nowhere in
the twin (the nil-deref transparency keeps raftpb's six `CloneMessage`
bodies — `out.Data = make([]byte, len(x.Data))` — lowering). The twin
driver reaches no early panic on these operands, so its observations are
unchanged. Producer of the structural diff:

```
python3 - <<'PY'
import json,subprocess
base=json.loads(subprocess.check_output(['git','show','b77f3298:baselines/pins/twin-chdriver.wire.json']))
cur=json.load(open('baselines/pins/twin-chdriver.wire.json'))
key=lambda f,k: f['name'] if k=='funcs' else json.dumps(f.get('recv'),sort_keys=True)+'.'+f['name']
def strip(o):
    if isinstance(o,dict): return {k:strip(v) for k,v in o.items()}
    if isinstance(o,list): return [strip(x) for x in o if not (isinstance(x,dict) and x.get('stmt')=='unseq-probe')]
    return o
for k in ('funcs','methods'):
    A={key(f,k):f for f in base[k]}; B={key(f,k):f for f in cur[k]}
    for n in B:
        if json.dumps(A[n],sort_keys=True)!=json.dumps(B[n],sort_keys=True):
            print(k,n,'probes',json.dumps(B[n]).count('"unseq-probe"'),'probes-only',json.dumps(strip(B[n]),sort_keys=True)==json.dumps(A[n],sort_keys=True))
PY
```

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

## The audit fix round (2026-09-05, [AGENT] worker; the adversarial audit returned BLOCK)

Findings R1–R12 and their dispositions are in the fix-round commits
(ids cited per commit); the substance:

- R1 (BLOCKER) — the guard retirement over-reached. Reproduced with the
  auditor's witnesses (`.tmp/audit/probes/*`), gc go1.26.5 vs the
  machine on every stream, then re-run at the fix round:

  | witness | gc | machine at the lane tip (every stream) | fix round |
  |---|---|---|---|
  | `x[iv.(int)] = len(b[j]) + wit(5)` | `interface conversion: interface {} is string, not int` | `index out of range [5] with length 1` | REFUSED: `len of a potentially-panicking operand hoisted past UNPROBED panicky material to its left (index expression at main.go:L:C) with a later ordered call/receive in the same statement — …; refused by name (narrowed A6 guard, BUG-032/BUG-083; E13 (b) boundary, e13-b audit fix round R1)` |
  | `x[iv.(int)] = len(make([]int, t[k]))` | same conversion | `index out of range [5] with length 1` | REFUSED: `make of a potentially-panicking size/hint operand hoisted past UNPROBED panicky material to its left (index expression …) in the same statement — …` |
  | `x[iv.(int)] += len(b[j]) + wit(5)` | same conversion | index panic | REFUSED (len text, index expression) |
  | `m[iv.(string)] = len(b[j]) + wit(5)` | `interface conversion: interface {} is int, not string` | set {index panic (slot 0), conversion (slot 1)} ∋ gc, slot 0 ≠ gc, no row | REFUSED (len text, type assertion — D4 now covers the map-assign target) |
  | `r = recover().(int) + len(b[j]) + wit(5)` in a defer | final panic `index out of range [5] with length 1` (`3 [recovered]`) | `3 [recovered]`-style value 3 | REFUSED (len text, type assertion) |
  | `int([]byte(s)[7]) + len(b[j]) + wit(5)` (R7) | `index out of range [5] with length 1` | (never probed) events-first = gc | REFUSED (len text, index expression) — conservative |
  | `iv.(int) + len(b[j:]) + func() int { iv = "s"; return 1 }()`, iv = 3 | `mut` then `6` | `mut` then the conversion panic, both slots | NOT refusable — BUG-101, red-first row `assert-ok-early-len-hoist` (FAIL/lean-observation: `expected status ok, got … panic`) |
  | `sinkP(&a[i], len(b[j]), wit(5))` | `index out of range [5] with length 1` | same (len hoisted first) | lowers; strict PASS control `addr-index-left-len-hoist` (address-of inside an argument list is a forced position for the census) |

  All eight lane-tip machine answers above were `unsupported` by name at
  b77f3298 (the whole A6 guard). Mechanism: design §4 D5.
- R2 (HIGH) — `(&T{x: s[i]}).x + wit(5)`: gc `wit 5` then `index out of
  range [9] with length 1`; machine the index panic with NO output on
  every stream (lane tip and main). Disposition (b): REFUSED —
  `structural allocation (&composite literal) with a potentially-
  panicking payload (a probed operand in the payload) followed by an
  ordered call/receive in the same statement — …; refused by name
  (structural-allocation class, E13 (b) residual; e13-b audit fix round
  R2)`; likewise `[]int{s[i]}[0] + wit(5)` (`slice literal`). Rows
  `composite-ptr-payload-vs-call`, `slice-lit-payload-vs-call` (BUG-102's
  Cases line, with the six narrowed-guard rows — the designed-red entry:
  BUG-032/BUG-083 are `fixed` and check-bugs keeps their Cases lines
  PASS-only). Design §4 D6, §6 item 5; inventory E13 residual 5, E12
  census note corrected.
- R3 — the three len-path ids are on BUG-032's Cases line; the five
  sites (baseline header, ledger, README, design) now say so.
- R4 — E6 / E13 residual bullets rewritten; "DISCHARGED" only for the
  probed axis, as measured.
- R5 — twin hash 11270c55… → the true 7c545840… at the lane tip → the
  final d531a225… (above).
- R6 — dirty-tree gate tail disclosed (above); the clean-tree tail
  replaces it.
- R7 — `[]byte(s)`/`[]rune(s)` never probed (frontend) + decoder refusal
  by name (closed enumeration of two); design §3/§6 item 7.
- R8 — race sentence restated as an over-approximation; §6 item 8.
- R9 — `CLI.lean` accountant inventory row 8 for `.unseqPanic`.
- R10 — `gc-draws.tsv` regenerated (above).
- R11 — ledger §8p → §8t (fr19-bug097 holds §8s on its branch), cites
  fixed; FR-28 row and queue row 28 rewritten (CLOSED for probed
  material, REOPENED NARROWED; 8 reds by design + BUG-101).
- R12 — design §3 "four constructors", §5 nine membership ids, §9
  MultiSound removed; `MachineSound` docstring six shapes + `hnu`;
  `ChoiceTrace.allSites_complete`; `Machine.lean` reachability invariant
  docstring; the bare `[USER]` cites carry "relayed"; the `.probeK`
  traveller arms declined (D11 above); `emit.go`'s `panicFreeOperand`
  docstring corrected (`residualPanicFreeOperand` is reinstated).

Focused run at the fix round (`focused-run-fixround.tsv`): the 76-row
E13 family — the 65 lane-tip rows PASS unchanged (39 membership, 26
strict), 10 born (1 PASS, 8 FAIL/frontend-export by design, 1
FAIL/lean-observation = BUG-101).

