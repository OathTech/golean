# Stage E6a of the evaluation-order model v2.1 — lane handoff (`core/unseq-stage-e6a-0924`)

[AGENT] worker, 2026-09-24. Worktree `.claude/worktrees/unseq-stage-e6a`, branch `core/unseq-stage-e6a-0924`, based on
main `3fb4a0d1` (the window charter rev. 2 ruled). Brief: the [AGENT] coordinator's E6a dispatch under [USER] Mike's
rulings of 2026-09-22 (the Stage E5 landing record items 1, 2, 3, 6) and 2026-09-24 («I'm happy to go with your rec»),
relayed — cite as relayed; the window: `docs/2026-09-23_batched-window-charter.md` (row 1, the slice table's E6a row, §6).
Design: `docs/2026-09-24_unseq-stage-e6-design.md` §E6a (every [AGENT] choice with its alternatives). Evidence:
`docs/evidence/2026-09-24_unseq-stage-e6a/`. NOT merged, NOT pushed. Scratch under the worktree's `.tmp/` only.

## 1. State at park

| commit | step | gate | rows | census (admitted / probes corpus+twin) | trace |
|---|---|---|---|---|---|
| `dc8d4372` | **the frontend**: the trigger refinement (event-mediated panic identity), `len`/`cap` over map / channel operands, the unit boundary generalized to every source unit (bare, `pkg.F` and method callees), the twin re-pin e1a87725… → 1c4e7038… (3 graphs born, 128 probes unchanged), the 14 probe → graph rows' manifests, the 2 red-first lane moves, the born status-diverse row + the lane-validation shapes, the baseline 3760 = 3524 / 236 → 3761 = 3525 / 236 | `ci --diff` EXIT=1 in 871 s (the lock 02:18:22Z–02:32:53Z); cases=3761 pass=3524 fail=237 = the pin 3525 / 236 with the one 5a-class row red; RESULT FAIL on EXACTLY the two 5a-class items (`certificate provenance` STALE for `scripts/check-frontend-pins` — the twin re-pin; the `google-search` drift line); every other step ok (`ci-diff-c1.tail.txt`) | 1 born (`evalorder/unseq-strings/str-index-status-diverse` PASS/membership {102, panic}); 2 strict → membership red-first (`e13-sibling-panic-order/assert-left-min-inline`, `channels/recv-order/dead-recv-len-operand`); 14 rows probe → graph unchanged; 375 other rows of the 41 affected packages unchanged (`diff-one-e6a.txt`, 395 rows) | 179 → 265 (+86 corpus, +7 twin; 0 lost); probes corpus 58 → 47, twin 128 → 128 | 3725 ids: 3694 SAME, 30 DIFFER (all in the affected packages: the 14 probe → graph rows, the 2 moves, 14 rows with new one-observation picks), 1 ONLY_B (the born row); `unseqNext` 2147 → 2550, `unseqPanic` 168 → 96 (§4) |
| `eb2bff6b` | **the decoder follow-ups** (`GoLean/NativeToIR.lean`): F8 — an `after` edge on a literal `allocate` refused by name; R1 — every source-local atom's `type` annotation checked against the enclosing function's declarations (`LowerCtx.locals`, `jsonDeclaredLocals`, `unseqCheckLocalAtoms`); mutants 49 → 52 (`mut-alloc-literal-after`, `mut-local-annotation-forged`, `mut-local-undeclared`; `mut-guard-type` re-pointed), `check-wire-boundary` 11 + 52 | `check-unseq-wire` PASS (52), `check-wire-boundary` PASS (11 + 52); `ci --slow` EXIT=1 in 1097 s (the lock 02:34:54Z–02:53:11Z); cases=3761 pass=3523 fail=238; RESULT FAIL on `certificate provenance` (STALE for `scripts/check-frontend-pins`) and `baseline diff` with TWO drift lines — the 5a-class `google-search` line and `race/negative/struct-tag-alias-field` PASS/racy → FAIL/go-observation, an ORACLE-side sample (`go run -race` stayed green under the box's load — the racy lane's three-way rule, case (b); the row's package untouched by E6a; re-run alone it PASSes, cases=1 pass=1); every other step ok (`ci-slow-c2.tail.txt`); the tip's `--slow` re-run is the park gate (`ci-slow-tip.tail.txt`) | no row moves (the checks refuse only forged wires) | unchanged | byte-identical outside E6a's rows |
| C3 (the records commit that carries this handoff; its hash and the tip's gate line in the records addendum C4) | **records**: this handoff, the design §0/§E6a, the inventory (E13, E3, E4, E12 bullets), the ledger §8 sentence + §8al, BUG-032's amendment, the E5 records' dated corrections (the status set WAS reachable), the evidence dir | the tip's `ci --slow` after this commit (C4's addendum records it) | — | — | — |

The slice's EXIT as the charter states it («non-main 151 → 0 and panic-vs-panic 21 → 0») is **NOT reached** — reported, not
forced: 11 of the 21 panic-vs-panic emitters close; 0 of the 151 non-main ones do. §3 names every remaining emitter and the
reason it stays; the summary: every one is a TYPE-GRAMMAR axis (E5z's list) that the unit boundary had hidden behind its own
first refusal reason in the E5 census.

## 2. PENDING [USER] — posed at the audit ask, never self-adjudicated

Each item is an [AGENT] choice the rulings did not make, with its alternative stated; a (b) pin, a new entry class as an
ENTRY, or a refusal of a covered program is a HARD STOP and is posed here rather than taken.

1. **The trigger refinement's SCOPE — the general form POSED, the event-mediated form shipped** (design §E6a «the
   scope»). The ruling's words «… OR against another FAILING occurrence» admit (A) ANY two unordered failing occurrences
   (no event between them: `a[i] + b[j]`, BUG-032's `xs[ys[9]], b = zs[7], 2`) and (B) the pair ACROSS an E1 participant's
   window (`iv.(int) + len(make([]int, t[k]))`, `iv.(int) + len(b[j])` — the legacy probe's own class, plus its mirror on the
   right of the window). E6a ships (B): it serves the ruling's purpose (the probe can retire without narrowing its rows),
   admits 48 sweeps by the trigger, and moves no inventory ENTRY (E13's axis is (a) ENVELOPED already). (A) is MEASURED and
   POSED: 856 newly admitted sweeps in 197 packages, 57 in the raft twin, hundreds in stdlib library units (`strings` 132,
   `internal/strconv` 88, `math/bits` 84, `unicode` 81, …) — hot loops whose strict rows would meet the depth guard — and it
   moves E3, E4 and E12's «left-to-right among non-calls» from (b) PINNED to (a) ENVELOPED as ENTRIES (a HARD STOP).
   Evidence `trigger-general-footprint.txt`. THE ALTERNATIVE: take (A) in a later slice with its own re-pin of the affected
   strict rows (`depth=` declarations / confluent moves), and re-envelope E3/E4/E12 by name.
2. **`len`/`cap` over map / channel operands admitted to the type grammar** (design §E6a). Needed to reach 10 of the 21
   panic-vs-panic emitters (`len(make(map[int]int, t[k]))`, `cap(make(chan int, t[k]))` were refused by the GRAMMAR, not the
   trigger — the E5 census printed only the first refusal reason). A widening within E6a's own class, no core / decoder /
   schema change (the emitter's `builtin-len`/`builtin-cap` node, the decoder's D8 head). THE ALTERNATIVE: refuse — then E6a
   closes 1 emitter and those 10 rows stay probes.
3. **The unit boundary generalized to EVERY source unit** — main, case-local imports, stdlib source-through library units —
   at once (design §E6a «non-main units»; the ruling named «imported source units» and the twin). THE ALTERNATIVE: case-local
   imports only, a second pilot scope with no semantic ground (the library units' 44 + 14 `strings`/`bytes` sweeps ride the same
   wire spellings; their rows reproduce their pinned results, `diff-one-e6a.txt`).
4. **The R1 check as a flat per-function declaration table** (design §E6a «R1»): a name Go's block scoping declares twice with
   DIFFERENT types in one function is checked against the SET of its declared types — a forged annotation equal to the other
   declaration's type passes. THE ALTERNATIVE: a scope-exact environment threaded through every statement kind's decoder (not
   built; the residual is stated in the docstring and here).
5. **The status set reused from `params` — no apparatus change** (design §E6a «the owed status-diverse row»): `statuses=ok+panic`
   existed since BUG-044 (2026-08-08) and is in corpus use; the E5 records' «unreachable from a row» was wrong and carries a dated
   correction in each place (design §E5e/F4, handoff §3/§6, the inventory's E13 bullet, the ledger's E5e bullet). THE
   ALTERNATIVE the brief sketched — an `expected_status` SET column routed to the CLI — would be a second spelling of the same
   set; not built. `scripts/test-lane-validation` gained the rejecting shapes (an empty set, a set on a strict row, a status word
   outside {ok, panic}) and the accepting shape of the born row.
6. **Two strict rows moved to membership after going RED-FIRST** (design §E6a «rows»): `assert-left-min-inline` and
   `dead-recv-len-operand` — the machine's canonical tape realized the index panic where gc realizes the conversion; both members
   spec-legal (E13's axis). THE ALTERNATIVES: narrow the graph to gc's member (a (b) pin the doctrine forbids) or leave the rows
   red (they are not wrong answers). E5c's F6 precedent applied; gc's draws inside (20/20).
7. **E6's exit, re-scoped by measurement** — for the coordinator, not a choice taken here: after E6a the census residue is 47
   corpus + 128 twin, and E6b (4) + E6c (2) + E6d (9) account for 15 of it. The other 160 are the classes §3 names (struct types
   with interface / defined-non-struct fields — the twin's 128 and `mini-raft-twin`'s 7; interface comparison; library structs
   with `error` fields; arrays as index bases; generic stencils' unsubstituted locals; a `for` condition as a sub-accumulator
   sweep; a send statement; captured reads in lifted bodies; slice-to-array conversion). Each is a grammar axis of E5z; NONE is
   a trigger question. E6e (the retirement at ZERO) is unreachable until they are dispositioned — the charter's §6 rule («if a
   slice is REFUSED … the triple stays») applies to each. POSED: whether E6d absorbs them as named axes, or the retirement moves
   to a later window under a new ruling.

## 3. What remains — the E6b–E6e residue (measured with the E6a frontend: `probes-e6a.txt`)

Legacy `unseq-probe` emission after E6a: **47 in 17 corpus packages + 128 in the twin** (from 58 + 128). By class:

| class | count | emitters (probed head) — and WHY each stays after E6a |
|---|---|---|
| E6b — element / field addresses | 4 | e13 `addrIndexLeftLenHoist`, `addrAssertLeftCall`, `arrayBaseTargetVsLen` (`index-addr`); `imported-goose/generics/generic-conversion` `genericConversions` (`index-addr`) — «unary operator & on an element (&a[i])» / an array base |
| E6c — `recover()` in a lifted body | 2 | e13 `recoverAssertVsLen$lit0`, `recoverAssertVsCallW$lit2` (`type-assert`) |
| E6d — the nine singletons | 9 | `channels/recv-edge` `recvNilIndexBaseSecond$lit0` (`deref`); `channels/recv-map-elem` `mapKeyPanicDrains$lit0` (`index-get`); `fmt/sprintf-dyn` `Infof` (`field-get`); `noodler/frontier2/array-of-funcs-indexed-call` (`index-get`, array base); `noodler/frontier2/typed-nil-error-return` (`binary`, interface ==); `noodler/misc` `copyIntoArrayView` (`slice`, array); `noodler/strings`, `panic-recover/shim-refusal-unrecoverable`, `strconv/format-parse` — `Error` methods (`field-get`, a library struct with an `error` field) |
| the NON-MAIN class, unchanged by the boundary's fall | 23 corpus + 128 twin | `mini-raft-twin` 7 (`field-get` on `*mnode.Node` — «field selector on a struct type outside the grammar»); `stdlib-source/errors-join` 5 + `errors-wrap` 2 `binary` (interface comparison `err == nil`); `strconv-parseuint` 3 + `Error` 1, `errors-wrap` `Error` 1, `frontier` `Error` 1 (`field-get` on `*strconv.NumError` — an `error` field); `frontier` `internal/strconv.pow10` (`index-get`, an array), `slices.Insert[[]int,int]` (`slice`, a generic stencil); the twin's 128 `field-get` — `raft.stepLeader` 29, `raft.(*raft).Step` 23, `stepCandidate` 6, `stepFollower` 6, `handleAppendEntries` 6, `DescribeConfState` 4, `loadState` 4, `newRaft` 3, `send` 3, `CreateSnapshot` 3, … — every one «field selector on a struct type outside the grammar» (`raft.raft`, `raftpb.Message`, `tracker.Progress`, `raft.raftLog`, `raft.unstable`: an interface field — `Logger`, `Storage` — or a defined non-struct field type — `StateType`, `MessageType`) or «method receiver type outside the grammar (raft.raft)». The twin's top legacy reasons after E6a: statement form 3143, no call 2782, no non-event 638, `error` results 385, … `raft.raft` receiver 89, `raftpb.Message` fields 85 (`census-e6a.txt`) |
| the PANIC-vs-PANIC residue after the refinement | 10 | `len-vs-call-order` `makeHintStructAnyKey`, `makeHintArrayAnyKey`, `lenStructAnyKeyLeftAssert` (an interface-containing map KEY — a hash-panicking map read; E2 admits hash-safe keys only), `lexerIdiom` (`for l.pos < len(l.src) && l.peek() != '\n'` — a `for` CONDITION is a sub-accumulator sweep the whole-sweep grammar never visits), `makeHintGenericKey[interface {}]` and `[int]` (a generic stencil: the classifier reads a local's type unsubstituted — `map[K]int`); e13 `convLeftCall` (slice-to-array conversion), `ifaceCmpLeftCall` (interface comparison), `sendChanIndex` (a SEND statement), `assertReturnList$lit0` (a captured read inside a lifted body) |

The whole-sweep census after E6a (`census-e6a.txt`): 108 258 corpus sweeps, **265 admitted** (179 at the branch point; `main`
205, `strings` 44, `bytes` 14, `wirepb` 2), the twin 10 203 / 7 (3 reach the wire); the main-unit legacy reasons are led as
before by «no call occurrence» and «statement form outside the pilot grammar».

**The general trigger form's footprint** (`trigger-general-footprint.txt`, PENDING item 1): 179 → 978 admitted (856 newly, 0 lost),
57 in the twin; with E6a's other widenings 179 → 1034 (955 newly, 65 twin); probes corpus 58 → 47 either way (the general form
closes no emitter the event-mediated form does not — the probe fires only beside an event).

## 4. Whole-corpus choice trace

`docs/evidence/2026-09-24_unseq-stage-e6a/choice-trace-main-vs-e6a.txt`: main `3fb4a0d1`'s binary (`63e9c661…`, the E5 fix round's = main's sources; main's frontend from a `git archive main` export) vs the E6a tip's binary and frontend, `scripts/choice-trace-corpus --dump --jobs 4` per side (the two standing spin exclusions `goroutines/send-then-spin` and `strings/trimspace-repeat/repeat-bound-refused` traced by no side; the rows the wrapper had not reached traced by a direct `golean choice-trace --batch` per side — the wrapper's summary step did not run), Stage D's `trace-compare.py`: **3725 ids, 3694 byte-identical, 30 DIFFER, 0 ONLY_A, 1 ONLY_B** (the born row). EVERY differing id lies in a package whose sweeps entered the grammar — the 14 probe → graph rows (`unseqPanic` 6 → 0, `unseqNext` 0 → 6/9/11), the 2 moved rows (`unseqNext` 0 → 6), and 14 rows whose newly admitted sweeps add `unseqNext` picks with one observation (`functions/untyped-nil-sinks/slice-lit-elem`, `interfaces/tuple-forward-boxing/{fixed-any, interface-source-control, variadic-any}`, `multipkg/wire-codec/size`, `new/new-slice-pointer`, `noodler/bounds/slice-within-cap`, `noodler/builtins/cap-after-slicing`, `noodler/indexkinds/slice-bounds-kinds`, `slices/append-spill-below-formula`, `stdlib-source/{binary-order/be-roundtrip, builder-overlay/repeat-doubling-loop, strconv-format/siblings, strings-split/empty-sep-invalid-utf8}`); the one non-`unseq` site movement — `multipkg/wire-codec/size` `appendSpill` 21 → 19 — is the finite fixed streams' knock-on (the new picks shift the slots the later spill picks read; the observation unchanged). Site census: `unseqNext` 2147 → 2550, `unseqPanic` 168 → 96, `appendSpill` 4874 → 4872, every other site identical; 34 export refusals each, identical sets.

## 5. Gates

Standalone (captured exits, `gate-exits-e6a.txt`): `go test ./tools/nativefrontend/ ./tools/lowerdiag/` ok (incl. the E6a
witnesses `e6a*` and `TestUnseqNonMainUnitsLower`); `check-unseq-wire` PASS (52 mutants; `Tests/UnseqWire.lean` exact sets);
`check-wire-boundary` PASS (11 + 52); `check-mem-callsites` PASS; `check-core-audit` PASS; `scripts/capped check-unseq-scheduler`
PASS; `check-frontend-pins` PASS (the twin re-pinned); `check-bugs` ok; `check-evidence-size` PASS; `check-spec-anchors` PASS;
`check-agents-alias` PASS; `test-lane-validation` PASS (the E6a shapes); `tools/reconcile-records` [filled at park].

Full gates under the box-wide lock (the wire / twin / apparatus changed, so the 5a pair — `certificate provenance` STALE for
`scripts/check-frontend-pins`; the `imported-goose/channel/google-search` drift line — is EXPECTED red and recorded; the train
installs the candidate, this lane does not): the C1 `ci --diff` (§1 row C1; `ci-diff-c1.tail.txt`) — red on EXACTLY the 5a pair;
the C2 `ci --slow` (§1 row C2; `ci-slow-c2.tail.txt`) — red on the 5a pair PLUS one oracle-side racy sample under load
(`race/negative/struct-tag-alias-field`, PASS when re-run alone); the tip's `ci --slow` after the records commit: [filled at park
— `ci-slow-tip.tail.txt`].

## 6. Operational notes for the next session

- Scratch under the worktree's `.tmp/`: `.tmp/census/{run.sh,summarize.py,diff.py,probes.sh,probe-sites.py}` (E5's tooling,
  copied); the census TSVs `before.tsv`, `trigger.tsv` (the GENERAL trigger form alone), `generalA-e6a.tsv` (general + widenings),
  `e6a.tsv` (the shipped rule + widenings) with their `probes-*.tsv`; `.tmp/nativefrontend-{main,e6a-trigger,e6a}`;
  `.tmp/golean-{main,e6a}`; `.tmp/main-tree` (a `git archive main` export with `deps` symlinked — the trace's main side; the
  tracer's `--out` is ROOT-RELATIVE, an absolute path is prefixed and fails); `.tmp/e6a/` (the gate / build / census / trace
  scripts, `diff-one-run.sh`, `gc-draws.sh` + `gc-draws-args.sh`, `c2-backup/`, `probe1/` the hand shapes).
- The lock protocol: atomic `mkdir /home/dev/projects/golean/artifacts/build-lock.d` at the PRIMARY root, an owner file,
  trap-protected release, wait-retry 120 s — never take over a live lock. Explicit-target Lean builds ≤ 48G ran without it
  (`docs/operational-lessons.md`).
- The C1 gate ran with the C2 files STASHED (`git stash` «e6a C2: decoder follow-ups + wires + gate scripts», backup
  `.tmp/e6a/c2-backup/`, snapshot `refs/snapshots/e6a/pre-c1-worktree`) so that its tree was exactly C1's.
- `build.py --check` under a changed frontend: the NATIVE wires did not drift at E6a (no witness sweep changed class); the
  three new mutants and `mutants.tsv` were the only regenerated files besides `mut-guard-type.json`.
- The R1 check runs BEFORE the occurrence arms and AFTER the cells decode: a mutant whose edit forges a source local's annotation
  meets R1's refusal first — pin another rule's needle through a cell or a constant head (the `mut-guard-type` lesson), and a
  binder without `$` is a CELL (skipped by R1) so D2 keeps its needle.
- The classifier reads a generic stencil's local types UNSUBSTITUTED (`loc.Type()`, not `goTypeOf`), so a stencil's sweeps are
  legacy by «local of a type outside the pilot grammar» even where the instantiation is admitted — a generics axis for a later
  slice (`makeHintGenericKey[int]`).
- The census's `admitted units` column is the unit path; `TWIN` rows are the twin assembly's. A `for`/`if`/`switch` HEAD is
  never a census row (sub-accumulator sweeps).

## Changelog lines for the window (`docs/changelog/61958f2e-WINDOW.md`, for the coordinator to merge)

- **E6a (2026-09-24) — the `unseq` grammar.** The observability trigger admits a FAILING occurrence unordered against an E1
  participant's window that holds another failing occurrence or may itself fail (panic identity); `len`/`cap` over map / channel
  operands; callees and methods of EVERY source unit (bare, `pkg.F`-qualified, receiver-qualified) — sweeps in imported and
  stdlib source-through units lower as `unseq` graphs. A consumer of a GoCore program sees `Stmt.unseq` where the legacy
  `unseq-probe` / ANF hoist stood in those sweeps (14 corpus rows; the raft twin's `raft.isHardStateEqual`, `raft.MustSync`,
  `raftpb.(*Snapshot).SizeMessage`). No core constructor, `Step` rule or choice site changed; the legacy triple stays (E6e).
- **E6a — the wire decoder** (`GoLean/NativeToIR.lean`): two named refusals — an `after` edge on a literal `allocate`
  (`slice-lit`, `map-lit`, `new` over a `struct-lit`); a source-local atom whose `type` annotation disagrees with the enclosing
  function's declaration, or which names no declared local (`LowerCtx.locals`). Emitted wires are unaffected.
- **E6a — the raft twin pin** e1a87725… → 1c4e7038… (three graphs born; `scripts/check-frontend-pins`).
- **E6a — the corpus**: `evalorder/unseq-strings/str-index-status-diverse` born (the first status-diverse `unseq` row);
  `builtins/e13-sibling-panic-order/assert-left-min-inline`, `channels/recv-order/dead-recv-len-operand` strict → membership.
