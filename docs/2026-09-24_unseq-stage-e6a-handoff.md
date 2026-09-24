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
| `973119c2` (the fix round's RUNTIME commit) + the records commit that follows | **the audit fix round** (docs/2026-09-24_unseq-stage-e6a-audit.md, FIX-FIRST records small; §5 the dispositions): the decoder's R1 environment SCOPE-EXACT (audit F2; `GoLean/NativeToIR.lean`; mutants 52 → 55, two NATIVE witnesses); SEVEN rows born in `builtins/e13-sibling-panic-order` + BUG-116 + BUG-032's A6 corrected (audit F1); the baseline 3761 = 3525 / 236 → 3768 = 3532 / 236; the pin-script header corrected (audit F3); the records (design, this handoff, inventory, ledger, charter line, evidence `fix-round/`) | standalone gates all green (`fix-round/gate-exits-fix.txt`; the twin unchanged); `ci --diff` EXIT=1 in 742 s (the lock 2026-09-24T04:46:13Z–04:58:35Z); cases=3768 pass=3531 fail=237 = the pin 3532 / 236 with the one 5a-class row red; RESULT FAIL on EXACTLY the two 5a-class items (`certificate provenance` STALE for `GoLean/NativeToIR.lean`; the `google-search` drift line); every other step ok (`fix-round/ci-diff-fix.tail.txt`) | 7 born PASS/membership (red-first on main: FAIL/membership as born, FAIL/differential as strict twins); 0 moves, 0 flips | at this tree 180 → 273 (108 294 sweeps; 100 newly, 0 lost); probes corpus 58 → 47, twin 128 → 128 with 3 graphs | vs the audited tip `1f0dee94`: 3732 ids, 3725 byte-identical, 0 DIFFER, 0 ONLY_A, 7 ONLY_B (the born rows); `unseqNext` 2550 → 2595 (their picks), every other site identical; 34 / 34 export refusals (`fix-round/choice-trace-e6a-vs-fix.txt`) |
| `e453bb38` (C3) + C4 (this addendum) | **records**: this handoff, the design §0/§E6a, the inventory (E13, E3, E4, E12 bullets), the ledger §8 sentence + §8al, BUG-032's amendment, the E5 records' dated corrections (the status set WAS reachable), the evidence dir | `ci --slow` at the tip `e453bb38` (the tree CLEAN): EXIT=1 in 899 s (the lock 02:56:19Z–03:11:18Z); cases=3761 pass=3524 fail=237 = the pin 3525 / 236 with the one 5a-class row red; RESULT FAIL on EXACTLY the two 5a-class items — `certificate provenance` (STALE: changed dependency `GoLean/NativeToIR.lean`) and the `baseline diff` DRIFT block's ONE line (`imported-goose/channel/google-search`); the C2 run's racy sample did not recur; every other step ok (`ci-slow-tip.tail.txt`) | — | — | — |

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
   strict rows (`depth=` declarations / confluent moves), and re-envelope E3/E4/E12 by name. [The audit's F4 (2026-09-24): (B)
   is a faithful SUBSET of the ruled wording — a narrowing of the ruling's literal scope by [AGENT] choice, posed here as such;
   gc realizes the LEXICAL order (20/20) on every general-form probe the audit ran (`a[i] + b[j]`, `x/y + s[i]`, `p.f + q.g`,
   `iv.(int) + s[i]`, the tuple `x, y = a[i], b[j]`, two failing operands inside one `make` window) EXCEPT BUG-032's tuple
   `xs[ys[9]], b = zs[7], 2` (gc `[7]`, the machine `[9]` on both sides — E3's recorded (b) pin), so not taking (A) creates no
   new observed-∉-modeled; (A) would fix that one pin. The event-mediated form itself fixed a WRONG-ANSWER class (F1, item 6).]
2. **`len`/`cap` over map / channel operands admitted to the type grammar** (design §E6a). Needed to reach 10 of the 21
   panic-vs-panic emitters (`len(make(map[int]int, t[k]))`, `cap(make(chan int, t[k]))` were refused by the GRAMMAR, not the
   trigger — the E5 census printed only the first refusal reason). A widening within E6a's own class, no core / decoder /
   schema change (the emitter's `builtin-len`/`builtin-cap` node, the decoder's D8 head). THE ALTERNATIVE: refuse — then E6a
   closes 1 emitter and those 10 rows stay probes.
3. **The unit boundary generalized to EVERY source unit** — main, case-local imports, stdlib source-through library units —
   at once (design §E6a «non-main units»; the ruling named «imported source units» and the twin). THE ALTERNATIVE: case-local
   imports only, a second pilot scope with no semantic ground (the library units' 44 + 14 `strings`/`bytes` sweeps ride the same
   wire spellings; their rows reproduce their pinned results, `diff-one-e6a.txt`).
4. **The R1 check as a flat per-function declaration table** — RESOLVED at the audit fix round (2026-09-24): the audit's F2 showed
   the flat table's residual reaching TYPE-SWITCH clause binders (the emitter declares `v` PER CLAUSE with the clause's type; the
   audit's `mS1-via-typeswitch-binder` forgery DECODED AND ANSWERED 1 on the tip) — one common idiom, not the «declared twice with
   different types» corner the tip stated. THE ALTERNATIVE WAS TAKEN: the environment is SCOPE-EXACT (design §E6a «R1»: the `block`
   arm folds declarations statement by statement; `if` / `for` inits, `range` variables and `select` clause targets extend it for
   their bodies; the innermost declaration in scope wins) — no wire-schema change was needed (the wire's block structure and its
   in-order declaration spellings carry the scope). The auditor's mutant + a legal-shadowing and a type-switch positive control are
   tracked (`Tests/unseq-wire/{native-e6ats,native-e6ashadow}.json`, mutants 52 → 55); the audit's own forged files refuse by name
   under the fix-round binary; every corpus wire and the pinned twin wire decode (the gate; the trace). Nothing left to decide here;
   what remains outside R1 is stated in the design (the `$`-temps and cells — D2's; a store TARGET's id — the late-named F7 class).
5. **The status set reused from `params` — no apparatus change** (design §E6a «the owed status-diverse row»): `statuses=ok+panic`
   existed since BUG-044 (2026-08-08) and is in corpus use; the E5 records' «unreachable from a row» was wrong and carries a dated
   correction in each place (design §E5e/F4, handoff §3/§6, the inventory's E13 bullet, the ledger's E5e bullet). THE
   ALTERNATIVE the brief sketched — an `expected_status` SET column routed to the CLI — would be a second spelling of the same
   set; not built. `scripts/test-lane-validation` gained the rejecting shapes (an empty set, a set on a strict row, a status word
   outside {ok, panic}) and the accepting shape of the born row.
6. **Two strict rows moved to membership after going RED-FIRST** (design §E6a «rows»): `assert-left-min-inline` and
   `dead-recv-len-operand` — the machine's canonical tape realized the index panic where gc realizes the conversion; both members
   spec-legal (E13's axis). THE ALTERNATIVES: narrow the graph to gc's member (a (b) pin the doctrine forbids) or leave the rows
   red (they are not wrong answers). E5c's F6 precedent applied; gc's draws inside (20/20). [REWORDED at the audit fix round — the
   audit's F1: these two moves are the ASSERTION-LEFT EXCEPTION, not the general story. The class they belong to — a late-realized
   failing NON-CALL operand (index / slice expression / dereference / pointer-field / division / shift / compound LOAD) LEFT of an
   inline built-in whose operand panics, call-free — was a WRONG ANSWER on main: the legacy lexical singleton held the LEFT panic
   where gc realizes the BUILT-IN's OPERAND's panic (20/20 on all fifteen audited shapes); only for a type assertion on the left
   does gc happen to agree with the lexical order (assertions are EARLY in gc), so those two rows were (b) pins of one spec-legal
   order and the rest were observed ∉ modeled. The candidate's refined trigger fixed the class SILENTLY; the fix round files BUG-116
   (`Status: fixed`, `Pinned-by: differential`) and bears SEVEN membership rows in `builtins/e13-sibling-panic-order`, red-first on
   main's frontend + binary (FAIL/membership as born, FAIL/differential as strict twins) and PASS/membership on the candidate with
   gc's draw inside; BUG-032's A6 sentence is corrected. The moves themselves stand; nothing to decide.]
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
| the NON-MAIN class, unchanged by the boundary's fall | 22 corpus + 128 twin (`generic-conversion` counted ONCE, under E6b — the audit's F4c; 4 + 2 + 9 + 22 + 128 + 10 = 175) | `mini-raft-twin` 7 (`field-get` on `*mnode.Node` — «field selector on a struct type outside the grammar»); `stdlib-source/errors-join` 5 + `errors-wrap` 2 `binary` (interface comparison `err == nil`); `strconv-parseuint` 3 + `Error` 1, `errors-wrap` `Error` 1, `frontier` `Error` 1 (`field-get` on `*strconv.NumError` — an `error` field); `frontier` `internal/strconv.pow10` (`index-get`, an array), `slices.Insert[[]int,int]` (`slice`, a generic stencil); the twin's 128 `field-get` — `raft.stepLeader` 29, `raft.(*raft).Step` 23, `stepCandidate` 6, `stepFollower` 6, `handleAppendEntries` 6, `DescribeConfState` 4, `loadState` 4, `newRaft` 3, `send` 3, `CreateSnapshot` 3, … — every one «field selector on a struct type outside the grammar» (`raft.raft`, `raftpb.Message`, `tracker.Progress`, `raft.raftLog`, `raft.unstable`: an interface field — `Logger`, `Storage` — or a defined non-struct field type — `StateType`, `MessageType`) or «method receiver type outside the grammar (raft.raft)». The twin's top legacy reasons after E6a: statement form 3143, no call 2782, no non-event 638, `error` results 385, … `raft.raft` receiver 89, `raftpb.Message` fields 85 (`census-e6a.txt`) |
| the PANIC-vs-PANIC residue after the refinement | 10 | `len-vs-call-order` `makeHintStructAnyKey`, `makeHintArrayAnyKey`, `lenStructAnyKeyLeftAssert` (an interface-containing map KEY — a hash-panicking map read; E2 admits hash-safe keys only), `lexerIdiom` (`for l.pos < len(l.src) && l.peek() != '\n'` — a `for` CONDITION is a sub-accumulator sweep the whole-sweep grammar never visits), `makeHintGenericKey[interface {}]` and `[int]` (a generic stencil: the classifier reads a local's type unsubstituted — `map[K]int`); e13 `convLeftCall` (slice-to-array conversion), `ifaceCmpLeftCall` (interface comparison), `sendChanIndex` (a SEND statement), `assertReturnList$lit0` (a captured read inside a lifted body) |

The whole-sweep census after E6a (`census-e6a.txt`): 108 258 corpus sweeps, **265 admitted** (179 at the branch point; `main`
205, `strings` 44, `bytes` 14, `wirepb` 2), the twin 10 203 / 7 (3 reach the wire); the main-unit legacy reasons are led as
before by «no call occurrence» and «statement form outside the pilot grammar». [The audit's F5: measured on the working tree
BEFORE `str-index-status-diverse` existed; at the tip `1f0dee94` both frontends admit its sweep — 108 264 sweeps, **180 → 266**
(the audit's reproduction; the 93 newly admitted identical by name). At the fix round's tree (the seven BUG-116 rows born): 108 294
sweeps, **180 → 273** (100 newly admitted; 0 lost); probes corpus 58 → 47, the twin 128 → 128 with 3 graphs — `fix-round/
census-fix.txt`.]

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
`check-agents-alias` PASS; `test-lane-validation` PASS (the E6a shapes); `tools/reconcile-records` 2 findings, both standing (C9 the certificate-provenance STALE item — the 5a class; C13 the doc-version note), 0 new.

Full gates under the box-wide lock (the wire / twin / apparatus changed, so the 5a pair — `certificate provenance` STALE for
`scripts/check-frontend-pins`; the `imported-goose/channel/google-search` drift line — is EXPECTED red and recorded; the train
installs the candidate, this lane does not): the C1 `ci --diff` (§1 row C1; `ci-diff-c1.tail.txt`) — red on EXACTLY the 5a pair;
the C2 `ci --slow` (§1 row C2; `ci-slow-c2.tail.txt`) — red on the 5a pair PLUS one oracle-side racy sample under load
(`race/negative/struct-tag-alias-field`, PASS when re-run alone); the tip's `ci --slow` after the records commit: `ci --slow` at the tip `e453bb38` (the tree CLEAN): EXIT=1 in 899 s (the lock 02:56:19Z–03:11:18Z); cases=3761 pass=3524 fail=237 = the pin 3525 / 236 with the one 5a-class row red; RESULT FAIL on EXACTLY the two 5a-class items — `certificate provenance` (STALE: changed dependency `GoLean/NativeToIR.lean`) and the `baseline diff` DRIFT block's ONE line (`imported-goose/channel/google-search`); the C2 run's racy sample did not recur; every other step ok (`ci-slow-tip.tail.txt`).

### The audit fix round (2026-09-24) — dispositions, what changed, witnesses

The adversarial audit of the candidate `1f0dee94` (`docs/2026-09-24_unseq-stage-e6a-audit.md`, branch `review/unseq-stage-e6a-0924` @
`300f0e74`; evidence `docs/evidence/2026-09-24_unseq-stage-e6a-audit/`) returned FIX-FIRST (records, small). Under the [USER]'s standing
direction that every merge is audited and its findings fixed before landing (Mike 2026-09-11, relayed), the dispositions below are the
[AGENT] coordinator's, disclosed at the merge ask, executed by the [AGENT] worker; nothing here is a [USER] ruling. Trust surface #1
changed (the decoder's R1 environment — refuses forged wires only); the frontend, the core, the wire schema and the twin pin did not.
Evidence `docs/evidence/2026-09-24_unseq-stage-e6a/fix-round/`.

| finding | disposition | what changed | evidence |
|---|---|---|---|
| **F1** RECORDS — a main-side WRONG-ANSWER class the candidate fixed silently (a late-realized failing NON-CALL operand left of an inline `len`/`cap`/`min`/`max` whose operand panics, call-free: main the LEFT panic, gc the built-in's operand's 20/20 on 15 shapes) | **BUG-116 FILED** (`Status: fixed`, `Pinned-by: differential`, the born rows on its Cases line; main's wrong answer and gc's draw recorded) + **BUG-032's A6 sentence CORRECTED** (the claim holds for the assertion-left exception only) + **SEVEN membership rows BORN** in `builtins/e13-sibling-panic-order` (index / index-vs-slice-expr / deref / pointer-field / division / shift / compound LOAD — the audit's litmuses), RED-FIRST on main's frontend + binary, PASS/membership on the candidate with gc inside (20 draws each); handoff §2 item 6 reworded (the two moves = the assertion-left exception); inventory E13 bullet; ledger §8 tally + §8am; baseline 3761 → 3768 = 3532 / 236 with the written reason (the main-side PASS → non-PASS is not a flip of a tracked row — the seven are born) | `diff-one-fix.txt` (7 PASS/membership, enumerated=2), `diff-one-main-red-first.txt` (7 FAIL/membership — main's machine a singleton), `diff-one-main-strict.txt` (7 FAIL/differential — Lean the left panic ≠ Go the built-in's operand's), `gc-draws-fix.txt` (7 × 20/20) |
| **F2** FAIL-OPEN minor (decoder; forged wires only) — the flat R1 table admits a type-switch clause binder forged to the OTHER clause's type (`mS1-via-typeswitch-binder` decoded and answered 1) | **FIXED at decode — the scope-exact environment BUILT** (no wire-schema change: the wire's block structure and in-order declaration spellings carry the scope): `decodeStmt`'s `block` arm folds `LowerCtx.locals` statement by statement; `jsonDeclaredLocals` stops at a block-scoping statement's nested bodies (`nestedStmtKeys`); `decodeIf` / `decodeFor` (init), `decodeRange` (key / value), the `select` arm (clause targets) extend it for their bodies; `decodeFunc` / `decodeMethod` open it with params + results; `unseqCheckLocalAtoms` resolves to the INNERMOST declaration in scope. The auditor's mutant + a legal-shadowing + a type-switch positive control tracked: NATIVE witnesses `e6ats`, `e6ashadow`; mutants `mut-local-{annotation-shadowed,shadow-other-decl,out-of-scope}` (52 → 55); `check-wire-boundary` 11 + 55; design §E6a «R1» rewritten to the true reach and what remains outside R1; §2 item 4 RESOLVED | `mutants-fix.txt` (the 3 mutants refuse by name; the audit's own `mS1-via-typeswitch-binder`, `mR1-typeswitch-binder`, `mR1-shadow-other-decl-type` refuse under the fix-round binary; the legal p4 wire runs; the pinned twin wire decodes), `gate-exits-fix.txt` (`check-unseq-wire` 55, `check-wire-boundary` 11 + 55 — and the FIRST run's failure: a positional pick hit the wrong clause, a no-op forgery the gate caught) |
| **F3** RECORDS — the twin's three born graphs mis-described (no failing occurrence in two; none born by the refinement) | **REWORDED** in four places: design §E6a «the twin re-pin» (dated correction), `scripts/check-frontend-pins` header (dated correction; the pin's bytes unchanged — `check-frontend-pins` ok), this handoff (§1 row C1 stands as written — «3 graphs born» — the description lived in the design / script), the changelog lines; the conclusion (all-forced singletons) stands for a stronger reason | `gate-exits-fix.txt` (`check-frontend-pins`: fresh emit = pinned wire 1c4e7038…) |
| **F4** RECORDS — (a) the trigger a faithful SUBSET of the ruled wording; (b) the charter's «21 panic-vs-panic with no effectful event» mis-labels 7 emitters that contain calls; (c) `generic-conversion` double-counted; (d) gc's lexical order on every general-form probe except BUG-032's tuple | (a)+(d) design «the scope» and §2 item 1 carry the phrase and the gc facts; (b) ONE dated correction line appended under the charter's slice table (`docs/2026-09-23_batched-window-charter.md`; [AGENT] fix round; the row's text kept as ruled); (c) the residue tables (design, §3) count it once: 22 corpus + 128 twin | the records themselves |
| **F5** NIT — census figures pre-born-row | **RE-TAKEN at this tree**, both frontends: 108 294 sweeps, 180 → 273 (100 newly = the audit's 93 + the seven born rows' sweeps; 0 lost); probes 58 → 47 corpus, the twin 128 → 128 with 3 graphs; the tip's 180 → 266 stated in the design and §3 | `census-fix.txt` |
| **F6** NIT — the changelog pointer | **STATED** in the changelog section: packet A creates `docs/changelog/61958f2e-WINDOW.md`; the lines live there until then | — |
| **F7** NIT — the forged store-target id sticks late | **RECORDED** as a NAMED LATE REFUSAL of the standing class in design §E6a «R1» (a store target is not an atom; a declared-id check on targets optional, not taken) | — |

Gates and the trace of the fix round: the standalone gates all green at the fix round's tree (`gate-exits-fix.txt`; `check-frontend-pins` the
twin unchanged; `check-bugs` ok with 116 entries; `tools/reconcile-records` 2 findings, both standing — C9 the 5a-class STALE certification,
C13 the doc-version note — 0 new); the full `ci --diff` and the whole-corpus choice trace vs the audited tip: the paragraph below this table
(appended after the gate).

**The fix round's full gate and trace.** `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff` at the fix round's tree (the runtime files
of `973119c2` + the records of the commit that follows, all in the working tree; the box-wide lock 2026-09-24T04:46:13Z–04:58:35Z): EXIT=1 in 742 s;
`cases=3768 pass=3531 fail=237` = the re-pinned 3768 = 3532 / 236 with the one 5a-class row red; RESULT FAIL on EXACTLY the two
5a-class items — `certificate provenance` (STALE: changed dependency `GoLean/NativeToIR.lean` — the train installs the candidate at step
5a, this lane does not) and the `baseline diff` DRIFT block's ONE line (`imported-goose/channel/google-search` PASS/membership →
FAIL/membership); the re-pin guard 0 PASS → non-PASS; the seven born rows PASS/membership in the run; every other step ok
(`fix-round/ci-diff-fix.tail.txt`). A FIRST run of the same gate (04:29:46Z–04:44:22Z, EXIT=1 in 876 s, the same counts) is SUPERSEDED
and recorded (`fix-round/ci-diff-fix-run1.tail.txt`): its `baseline diff` step REFUSED — the first re-pin edit had hoisted the `# reason:`
block that must sit above `channels/select-select/beside-loop` into the header (a malformed stage alternation the check names; this
worker's error, caught by the gate — «NOT a drift verdict»); the file was rebuilt from HEAD's text line by line (+28 / −1) and
`scripts/coverage-baseline-diff` against run 1's `latest.tsv` judged DRIFT = exactly the one 5a-class line before run 2. The whole-corpus choice trace vs the AUDITED TIP `1f0dee94` (`fix-round/choice-trace-e6a-vs-fix.txt`):
**3732 ids, 3725 byte-identical, 0 DIFFER, 0 ONLY_A, 7 ONLY_B** — exactly the born rows; the decoder change moves NO pick (every site
census identical except `unseqNext` 2550 → 2595, the born rows' own); 34 / 34 export refusals, identical sets; the two standing
exclusions (`goroutines/send-then-spin`, `strings/trimspace-repeat/repeat-bound-refused`) traced by neither side, as in every prior trace.

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
- THE AUDIT FIX ROUND's scratch, `.tmp/fix/` (replayable edit scripts and drivers): `edit-decoder.py` (the scope-exact R1
  environment, exact-anchor replacements over the tip's `GoLean/NativeToIR.lean`), `edit-buildpy.py` (the two NATIVE witnesses +
  three mutants in `Tests/unseq-wire/build.py`; the graph to mutate is selected BY CONTENT — the emitter's JSON has sorted keys, so
  an `if`'s `else` precedes its `then` in a walk and a positional pick hit the WRONG clause on the first try, a no-op forgery the
  wire gate caught), `edit-bugs.py` (BUG-116 + BUG-032's A6 correction), `edit-baseline.py` (the seven rows are inserted INTO the
  sorted e13 block — the baseline's data rows are in MANIFEST order, not bytewise-sorted: a global re-sort reordered 56 rows on the
  first try), `edit-pins-header.py`, `edit-design.py`, `edit-handoff.py`, `edit-inventory-ledger-charter.py`; drivers
  `build-decoder.sh` (`GOLEAN_MEM_MAX=32G scripts/capped lake build golean UnseqWireTests`, 20 s), `diff-one-fix.sh`,
  `diff-one-main2.sh` + `diff-one-main-strict.sh` (main's tree `.tmp/main-tree` with the PRIMARY's `.lake` rsynced in so `lake
  build` is a no-op — the first take ran diff-coverage's bare `lake build` from an empty `.lake` and hit its 120 s timeout;
  strict rows must leave `why` as `-`), `gc-draws-fix.sh`, `census-fix.sh`, `wire-gates.sh`, `gates-small.sh`, `trace-fix.sh`
  (`.tmp/trace/fix-rel` vs the audited tip's `.tmp/trace/e6a-rel`, `.tmp/trace-compare.py`), `gate-ci.sh` (the lock protocol).
  The audit's forged files live in the read-only audit worktree's `.tmp/audit/mutants/` (replayed, not copied).

## Changelog lines for the window (`docs/changelog/61958f2e-WINDOW.md`, for the coordinator to merge)

The file `docs/changelog/61958f2e-WINDOW.md` does not exist yet on any branch (the audit's F6): packet A of the window creates it;
until then this lane's lines live HERE, in this section, and nowhere else.

- **E6a (2026-09-24) — the `unseq` grammar.** The observability trigger admits a FAILING occurrence unordered against an E1
  participant's window that holds another failing occurrence or may itself fail (panic identity — the EVENT-MEDIATED form, a
  faithful subset of the ruled wording; the general form posed); `len`/`cap` over map / channel operands; callees and methods of
  EVERY source unit (bare, `pkg.F`-qualified, receiver-qualified) — sweeps in imported and stdlib source-through units lower as
  `unseq` graphs. A consumer of a GoCore program sees `Stmt.unseq` where the legacy `unseq-probe` / ANF hoist stood in those sweeps
  (14 corpus rows; the raft twin's `raft.isHardStateEqual`, `raft.MustSync`, `raftpb.(*Snapshot).SizeMessage` — admitted through the
  unit boundary by Stage E's E3 rule, not by the refinement; all-forced singletons). No core constructor, `Step` rule or choice site
  changed; the legacy triple stays (E6e).
- **E6a — the wire decoder** (`GoLean/NativeToIR.lean`): two named refusals — an `after` edge on a literal `allocate`
  (`slice-lit`, `map-lit`, `new` over a `struct-lit`); a source-local atom whose `type` annotation disagrees with the declaration
  IN SCOPE at its statement, or which names no local in scope (`LowerCtx.locals` — scope-exact since the audit fix round: block /
  clause scope, the innermost declaration wins). Emitted wires are unaffected.
- **E6a — the raft twin pin** e1a87725… → 1c4e7038… (three graphs born by the unit boundary under E3's rule; `scripts/check-frontend-pins`).
- **E6a — the corpus**: `evalorder/unseq-strings/str-index-status-diverse` born (the first status-diverse `unseq` row);
  `builtins/e13-sibling-panic-order/assert-left-min-inline`, `channels/recv-order/dead-recv-len-operand` strict → membership.
- **E6a audit fix round (2026-09-24) — the corpus and BUGS.md**: BUG-116 filed (fixed) — a late-realized failing NON-CALL operand
  left of an inline `len` / `cap` / `min` / `max` whose operand panics, call-free, answered the LEFT panic on main where gc realizes
  the built-in's operand's; seven membership rows born in `builtins/e13-sibling-panic-order` (`idx-left-vs-min-operand`,
  `idx-left-vs-len-slice-expr`, `deref-left-vs-len-operand`, `ptr-field-left-vs-len-operand`, `div-left-vs-len-operand`,
  `shift-left-vs-len-operand`, `compound-load-vs-len-operand`); BUG-032's A6 sentence corrected. Baseline 3761 → 3768 = 3532 / 236.
