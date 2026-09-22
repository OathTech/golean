# Stage E5 — the residue families of the evaluation-order model v2.1: the design record, per family (2026-09-22)

[AGENT] Lane `core/unseq-stage-e5-0922` (worktree `.claude/worktrees/unseq-stage-e5`), branch off main
`d76721bd` (train r46's 5a records; main gained the records-only close `dc5de785` after the branch —
rebased at the lane's end). Dispatched by the [AGENT] coordinator under [USER] Mike's 2026-09-22
sign-off «Agree on the judgements, go ahead» (relayed — cite as relayed), which landed Stage E E1–E4
(`docs/2026-09-21_unseq-stage-e-design.md`) and ordered the E5/E6 lane. Design of record:
`docs/2026-09-16_evaluation-order-model-v2.md` (v2.1) §7 row E; the Stage E handoff's §3 «Next families»
is this lane's scope. THE RULINGS IN FORCE ([USER] 2026-09-22, the seven-item record in
`docs/2026-08-31_qrow-rulings.md`): READING (a) — the built-ins are the «function calls» of
spec#Order_of_evaluation's ordering sentence, so `min`/`max`/`copy`/`append`/… are E1 participants
(ordered call events), never unordered reads; the OBSERVABILITY trigger stands (a sweep enters the graph
iff some occurrence is unordered against an EFFECTFUL event); E2/E12 move (b) → (a) ONLY on named rows;
composite literals are nodes without E1 edges, `make`/`new` E1 participants; the `allocate` body is ONE
constructor over `AllocSpec`, extended by ARMS (map literals, array literals) rather than by statement
bodies. Everything below is [AGENT] unless marked; every new construct beyond an `AllocSpec` arm is
tagged «[AGENT] choice, PENDING [USER] ratification at the merge ask» here, in the handoff §2 and in the
inventory. Handoff: `docs/2026-09-22_unseq-stage-e5-handoff.md`; evidence
`docs/evidence/2026-09-22_unseq-stage-e5/`.

## 0. The residue, measured, and the families' order

**The census BEFORE** (`census-before.txt`; main's frontend over 1360 corpus packages + the raft twin):
108 102 corpus sweeps, 131 admitted (the E1–E4 families' rows), 24 421 legacy sweeps in MAIN units and
93 753 in imported source units (the twin's 10 203 among them — refused by their callees: «callee outside
the main package», «method callee outside the main package» — before any E5 reason is reached). The
main-unit residue by FIRST refusal reason: 8747 «no call occurrence», 6025 «statement form outside the
pilot grammar» (if/for/switch heads, sends, declarations, …), 1953 «no non-event occurrence» and 210 «no
occurrence observable against an effectful event» (the trigger: every edge forced), then the E5 reasons —
**577 multi-target or tuple assignment + 139 blank target**, **338 `builtin append` + 30 `builtin copy`**
(`min`/`max` below the top 45), **254 float targets/results**, **217 string len/index/slice**, **149 map
literal**, **101 `unary operator &`**, ~60 array types, 48 `nil`. Sampled, the multi-target sweeps are
comma-ok forms (`v, ok := <-ch` / `m[k]` / `x.(T)`), swaps (`a, b = b, a%b`, `s[i], s[j] = s[j], s[i]`)
and multi-value calls (`lo, hi := minMax(s)`) — most CALL-FREE, hence legacy under the trigger whatever
the grammar admits; the same holds of every E5 reason. The admitted-sweep payoff of every family is
therefore SMALL (E1–E4 admitted +10 / +27 / +18 / +13); what decides the order is (i) what the RULINGS
direct, (ii) what closes LEGACY PROBE EMITTERS (E6's metric), (iii) dependencies between families.

**The legacy probe emission census BEFORE** (`probes-before.txt` — E6's entry metric, measured for the
first time as EMISSIONS rather than as census reasons or trace consumptions): main's frontend emits
**70 `unseq-probe` nodes in 21 corpus packages and 128 in the raft twin** (0 `unseq` graphs there). By
probed head: the twin's 128 are 125 `field-get` + 2 `index-get` + 1 in `main` (`deliverIdx`), all but
one inside the raft packages' NON-MAIN units (`raft.stepLeader` 29, `Step` 24, `handleAppendEntries` 6,
…); the corpus's 70 are 22 `type-assert` (`iv.(int)` beside `make`/`append`/`copy`/`min`/`len` in
`builtins/e13-sibling-panic-order` and `builtins/len-vs-call-order`), 12 `index-get`, 12 `field-get`
(`Error()` methods of non-main units, `makeNilOnly`, `lexerIdiom`, the mini-raft-twin drivers), 8
`binary` (interface comparisons — `err == nil` in `stdlib-source/errors-*`), 3 `index-addr`, 3 `slice`,
1 `deref`. TWO structural facts decide E6 before any family lands: (1) 128 + 12 of the emitters sit in
NON-MAIN units, which the whole-sweep grammar refuses by design («callee outside the main package»; the
census's admitted units are `main` only) — reaching zero needs the graph lowering for imported source
units, a grammar widening the brief forbids «merely to reach zero»; (2) ~30 emitters are PANIC-vs-PANIC
pairs with NO effectful event (`iv.(int) + len(make([]int, t[k]))`: two failing occurrences unordered
against each other, `make`/`len` effect-free) — the RATIFIED trigger routes them to the legacy path,
whose probe realizes their two members; retiring the probe with the trigger as ratified would NARROW
those rows to one member. Both are POSED in the handoff §2/§3 (a trigger refinement is a change to a
ratified item — not this lane's to take). **E6 is NOT entered by this lane.**

| family | what enters the grammar | closes / decides | core change |
|---|---|---|---|
| **E5a** the reading-(a) built-ins `min`/`max`/`copy`/`append` (§E5a) | `min`/`max` as E1-ordered PURE heads (`after`, no effect); `append`/`copy` as E1-ordered EFFECTFUL statement-bodied occurrences (they write memory: the append's in-place element store, the copy's destination) | the ratified item 1's consequence; 4 probe emitters (`e13-sibling-panic-order/{assert-left-append,tgt-assert-vs-min-call,tgt-assert-vs-copy-call,tgt-assert-vs-append}` + `assert-left-copy`) move to the graph with their sets | **`UnseqBody.wide (binds) (spec : WideSpec)`** — ONE new body kind over a closed spec (`append`, `copy`; E5b adds `mapLookup`, `typeAssert`) mirroring `allocate`; two Step rules (`unseqRunWide`/`unseqWideDone`) — [AGENT] choice, PENDING [USER] |
| **E5b** multi-target / tuple assignment, blank targets, the comma-ok forms (§E5b) | `a, b = e1, e2`, `a, b := f()`, `_ = e`; `v, ok := <-ch` (a two-binder `recv`), `v, ok := m[k]` / `x.(T)` (two-binder `wide` bodies); every target a PHASE-1 SIBLING plan, the stores left to right in phase 2 | E3/E4 (inter-target order): the graph shape; BUG-032's rows stay legacy under the trigger (call-free) — E3 stays (b) PINNED, stated | `WideSpec.mapLookup`/`.typeAssert` arms; `unseqAtom`'s `.global` arm (a package-level target plan); D13's `.addr (.global _)` |
| **E5c** map literals (§E5c) | `map[K]V{k: v, …}` as an `allocate` body WITHOUT E1 edges (`AllocSpec.mapLit`); entry reads the occurrences | the E13 guard's measured note; `evalorder/unseq-conv-alloc/map-lit-control` becomes a graph (singleton) | `AllocSpec.mapLit` arm (+ names/eqb/indices/sup arms) |
| **E5d** `&x` of a variable (§E5d) | the address of a local / package-level variable as an ATOM-LIKE operand (`ref x` / `globaladdr`): no read, no failure | 101 main-unit first-reason sweeps; `spec-examples-decl/address-op-*` shapes | none (decoder: `ref`/`globaladdr` where an atom is admitted, never `ref $binder` — F2) |
| **E5e** strings: `s[i]`, `s[lo:hi]`, `len(s)` (§E5e) | a string index / slice as a FAILING PURE OP (bounds), `len(s)` an E1 participant | 217 main-unit sweeps; probe emitters `bytes-conv-payload-vs-call`, `noodler/strings` | none (heads `index-get`/`slice`/`builtin-len` exist; the machine indexes and slices strings) |
| deferred, STATED (§E5z) | interface conversions (`to-interface` heads — audit F6: a strict row of the boxed-payload shape flips default ≠ gc, so every born row is membership), method values/expressions, defined non-struct types, floats/complex, array types/literals, non-main units, sub-accumulator sweeps | — | — |

**Why this order** ([AGENT]). E5a first: it is the one family a RULING directs («E5 admits `min`/`max`/`copy`/`append`
as E1 participants under the same reading» — item 1), it closes the most probe emitters of any family (the
`e13-sibling-panic-order` rows with a `wit` beside an assertion and a built-in), and its core change — the one
statement-bodied kind — is the dependency E5b's comma-ok forms reuse (arms, not a second kind). E5b second: it
decides the graph shape for E3/E4 (targets as phase-1 siblings) and needs E5a's kind. E5c third (an `AllocSpec`
arm, the ratified extension mechanism). E5d/E5e are grammar-only widenings with no core change, ordered by
payoff. Floats, defined types, method values, arrays and interface conversions are stated with their counts and
left to the next lane — none is a dependency of the others, none closes a probe emitter the earlier families do
not, and each carries a design question of its own (floats: the NaN lane; interface conversions: F6's default
tape; arrays: the frozen-anchor rule on array variables; defined types: the machine's kind typing).

The whole-sweep boundary rule is unchanged (v2.1 §3.7; Stage C design §1): one sweep is EITHER one `unseq`
graph OR the legacy path, decided by `unseqClassify` alone — never by fixture name, never a mixture (the
mixture guard and decoder D14 stay).

## E5a. The reading-(a) built-ins `min`/`max`/`copy`/`append` (landed 2026-09-22)

**The ruling executed.** READING (a) ([USER] 2026-09-22, item 1): the built-ins are the «function calls» of
spec#Order_of_evaluation's ordering sentence (spec#Built-in_functions «called like any other function»), so
`min`/`max`/`copy`/`append` are E1 PARTICIPANTS — ordered lexically among the calls, receives and logical
operations, their operands evaluated inside their windows (forced before every later participant) — never
unordered reads. gc's `order.go` call class (`OMIN, OMAX, OCOPY, OAPPEND, …`) is this reading; every draw below
agrees. Two kinds inside the reading: `min`/`max` have NO effect and cannot fail (pure heads over their operand
atoms — `Expr.minOf`/`maxOf` exist; like `len`/`cap`/`make` they do not admit a sweep by themselves); `append`
and `copy` are EFFECTFUL — the append stores its elements IN PLACE when the base has capacity (observable
through every alias of the backing array) and always returns a fresh header, the copy writes its destination —
so a sibling read is observable against them and the trigger admits the sweep (they count toward `calls`).

**The grammar widening** (`tools/nativefrontend/unseq.go`, `unseqCall`'s built-in switch): `min`/`max` —
a result type in the grammar (int kinds, string), ≥ 1 operand, each classified (`unseqMinMax`); `append` — a
slice result in the grammar, the base classified, a non-spread element list classified element by element
(an interface-typed element type boxes the atom in the packed literal's payload), a spread operand a slice in
the grammar or a string onto a byte slice (`unseqAppend`); `copy` — a slice destination in the grammar, a
slice or string source (`unseqCopy`), in value AND statement position (the statement form's count is
discarded; `unseqClassify`'s ExprStmt arm admits `copy` beside `print`/`println`). `clear`/`delete`/`close`
statements stay legacy by name (no result; alone in their sweeps).

**The lowering** (`unseq_lower.go`): `min`/`max` → an `eval` occurrence whose head is the emitter's own
`{"expr": "min"|"max", "args": [atoms]}` with the E1 `after` edge — an event block like `len`'s; `append` →
inside the call's operand frame the base atom, the ELEMENTS (a non-spread list packed into a `slice-lit`
`allocate` in the frame — the legacy hoist's own packing, no E1 edge — a spread slice as its atom, a spread
string as a pure `bytes-from-string` head), then the `wide` occurrence `{"stmt": "append", elem, slice,
elems}` as the E1-ordered event (`wideAppend`, `wideOcc`); `copy` → the destination and source atoms (a string
source as a `bytes-from-string` head), then `{"stmt": "copy", dst, src}` producing the count (`wideCopy`).

**The machine** (TRUST SURFACE #1; [AGENT] choice, PENDING [USER] ratification at the merge ask): **`WideSpec`**
(`append (elem : Ty) (slice elems : Expr)` | `copy (dst src : Expr)`; `WideSpec.arity` = 1 for both) and
**`UnseqBody.wide (binds : List String) (spec : WideSpec)`** — ONE statement-bodied occurrence kind over a
CLOSED spec, mirroring `allocate`: `unseqWideStmt binds spec` is the hoisted wide statement with the binder
cells as its targets (`Stmt.appendSlice (.var b) elem slice elems`, `Stmt.copySlice (.var b) dst src`; a
binder list of another arity reaches the machine's own `unsupported` refusal by name behind
`UnseqGraph.wellFormed?`'s static arity check), two Step rules `unseqRunWide`/`unseqWideDone` mirroring the
alloc pair (StepFn's `.run`/`.wait` arms; `stepFn_sound`, `step_complete`, `step_complete_any_wf`,
`stepUnseqNext_run_wait_stream`, `step_preserves_wf` with `unseqWideStmt_locSup` (trivial — program text is
loc-free), `wideSpecSup`/`wideSpecSup_eq_zero` in the bound network, `unseq_record_stable` and the
done-monotone lemma; `WideSpec.names`, `valueBinds`/`mentions`, `WideSpec.eqbF` + soundness,
`wideSpecIndices`). No new pick: `checkCert_slowObs` and the accountant are untouched (the append's own
`appendSpill` capacity pick is the statement's, as on the legacy path — the born spread row keeps its base
under capacity so no spill site joins; a full base was REFUTED by name at width 2, «site bound 30»).
ALTERNATIVES NAMED: (a) `AllocSpec.append`/`.copy` arms — the ruling's extension mechanism for ALLOCATION
shapes, a misnomer for `copy`, which never allocates, and a stretch for `append`, which allocates only on
spill; (b) one body kind PER built-in — four constructors and eight Step rules for one shape; (c) the general
`exec binds stmt` body the E4 design rejected (a `Stmt` inside `UnseqBody` is a nested-inductive cycle). The
closed kind is the E4 pattern applied to the wide statements the machine already has; E5b adds the comma-ok
`mapLookup`/`typeAssert` arms to it (arms, not a second kind).

**The decoder** (`GoLean/NativeToIR.lean`): the `wide` kind (keys name/kind/binds/wide/after/region; the spec
tag ∈ {append, copy} with exact keys; every operand an ATOM — a `ref` of a `$` binder cell refused as audit F2
refuses it elsewhere; the binder arity the statement's; the cell typed by the statement's result — the slice
type for append, `int` for copy's count); D8 admits the `min`/`max` heads over atom args (≥ 1). Mutants
`mut-wide-kind` (a `clear` tag), `mut-wide-nonatom` (a hidden read in copy's destination), `mut-wide-binds`
(two binders for one result), `mut-wide-cell-type` (the count cell typed bool), `mut-min-nonatom` — 33 → 38,
every one refused by name through the CLI (`check-unseq-wire`; `check-wire-boundary` 11 + 34 controls: the
positive control `e5copy` answers 9 on the canonical tape — the copy first, gc's).

**References lead** (`docs/evidence/2026-09-16_eval-order-v2-spike/enumerate.py`, `outcomes.txt` PASS): E5a1
`min(x, 100) + m()` → {6}, forbidding 15 (x's read inside min's window, forced); E5a2 `append(s, 3)[0] + m()`,
s = make([]int, 2, 4) → {6, 15}; E5a3 `d[0] + copy(d, s)` → {2, 9}; E5a4 E13's `x[iv.(int)] = min(q, t[k]) +
wit(5)` → {the assertion's panic, the index panic} (wit never runs); E5a5 `min(x, 100) + y + m()` → {7, 16};
E5a6 `x[iv.(int)] = copy(d, s) + wit(5)` → {the assertion alone, `wit 5` then the assertion}; E5a7
`len(append(b, "xy"...)) + x + m()` → {9, 18}. Wires: hand-built `Tests/unseq-wire/{e5append,e5copy,e5minmax}.json`
+ the frontend's own `native-e5*.json`, EXACT over the wire (`Tests/UnseqWire.lean` 106 ok, 38 mutants);
`Tests/UnseqScheduler.lean`'s hand-built `wide` graph (E5a2) exact and route-α CERTIFIED {6, 15} (411 nodes /
422 edges / 12 dedup hits). The frontend's unit tests: witnesses `e5aAppendRead` (calls 2, nonEvents 2),
`e5aCopyRead` (1, 3), `e5aAppendSpreadStr` (2, 1), `e5aTgtAssertMin` (1, 3); legacy by the trigger `e5aMin`,
`e5aMaxForced` («no occurrence observable against an effectful event» — a read inside min's window is forced
before a later call), `e5aCopyStmt` («no non-event»); the canonical shapes (`eval:ident allocate wide
invoke/after eval:index-get eval:binary` for the append row); the E13 guard test's `tgtAssertVsMin` moves from
the probed-legacy map to the one-graph list.

**The census** (`census-e5a.txt`; main's frontend vs E5a's over 108 102 corpus sweeps + the twin): admitted
**131 → 137** (+6 in 2 packages, 0 lost) — by former reason `builtin copy` 3, `builtin append` 2, `builtin
min` 1: `builtins/e13-sibling-panic-order/{assertLeftAppend, assertLeftCopy, tgtAssertVsMinCall,
tgtAssertVsCopyCall, tgtAssertVsAppend}` and `slices/copy-min/copyMin` (`z := n*1000 + dst[0]*100 +
dst[1]*10 + copy(nilSlice, src)` — the checked accesses beside a copy into a nil slice: same observation on
every order). The twin 10 203 / 0. LEGACY PROBE EMISSIONS (`probes-e5a.txt`): the corpus **70 → 63** (e13
17 → 12, copy-min 2 → 0), 20 packages; the twin 128 unchanged. The 338 `builtin append` / 30 `builtin copy`
main-unit first-reason sweeps are call-free or all-forced beyond these six — legacy under the trigger, as
measured §0 predicted.

**Rows** (`scripts/diff-one` on all 12 affected rows — twice: the first run REFUTED `append-spread-str-vs-call`'s
width 2 by name («site bound 30 exceeds the case's width 2» — the append on a FULL base spills, and the
`appendSpill` capacity site joins the sweep at bound 30; the row's purpose is the spread-string head, so its base
took capacity (make([]byte, 1, 8)) — the pick never arises; recorded, not widened to 30) and showed
`copy-stmt-control` ADMITTED (the captured d's HEADER read vs f inside copy's window — one pick, one
observation; its comment corrected); the second run is the table, 12 PASS — `diff-one-e5a.txt`; gc's draws
`gc-draws-e5a.txt`, 20/20 per subject under GOMAXPROCS 1/8, default and `-N -l`):

| row | before → after | set (output · result) | gc |
|---|---|---|---|
| `evalorder/unseq-builtins/min-vs-call` | born PASS strict, wide=0 | 6 (E5a1 — legacy by the trigger, every edge forced: the [AGENT] reading-(a) control) | 6 |
| `evalorder/unseq-builtins/min-read-vs-call` | born PASS/membership | {7, 16} (E5a5) | 16 |
| `evalorder/unseq-builtins/append-read-vs-call` | born PASS/membership | {6, 15} (E5a2) | 15 |
| `evalorder/unseq-builtins/copy-effect-vs-read` | born PASS/membership | {2, 9} (E5a3) | 9 |
| `evalorder/unseq-builtins/append-spread-str-vs-call` | born PASS/membership | {9, 18} (E5a7) | 18 |
| `evalorder/unseq-builtins/copy-stmt-control` | born PASS strict, wide=1 | 78 (the header read vs f: one observation) | 78 |
| `builtins/e13-sibling-panic-order/{assert-left-append,assert-left-copy,tgt-assert-vs-min-call,tgt-assert-vs-copy-call,tgt-assert-vs-append}` | PASS/membership, sets UNCHANGED (2 members each) | the graph reproduces the legacy probe's two members (E5a4/E5a6's shapes; the assertion vs the index panic inside the built-in's window, or vs `wit`) | unchanged |
| `slices/copy-min` | PASS strict (unchanged), wide=5 | the checked accesses vs a copy into a nil slice — every order agrees | = |

NO lane move, NO widened pin, NO PASS → non-PASS. Baseline 3732 = 3497 / 235 → **3738 = 3503 / 235** (+6 born;
the header carries the reason). Gates in-process at this tree: `check-unseq-wire` PASS (38 mutants),
`check-wire-boundary` PASS (11 + 34), `check-mem-callsites` PASS (70 — the `wide` body performs no raw memory
operation: its statements are the legacy path's own), `check-unseq-scheduler` PASS (35 theorems, classical trio
only), `check-core-audit` PASS; the full gate line is in the evidence README.

**Latitude.** E2's and E12's VALUE axis is (a) ENVELOPED on the four born membership rows (a sibling read
beside an effectful `append`/`copy`, or beside a call after a pure `min`) — posed for ratification at the merge
ask with the E1–E4 precedent; the entries stay (b) PINNED for the rest of their families. The five E13 rows are
NOT a reclassification: their legacy `unseqPanic` sets are reproduced exactly by the graph. `min-vs-call` is a
FORCED singleton under reading (a) (as `make-len-vs-call`); reading (b) is the named alternative, NOT taken.

**[AGENT] choices (alternatives named).** (i) The `wide` kind (above; PENDING). (ii) `append`/`copy` are
EFFECTFUL for the trigger while `min`/`max`/`len`/`cap`/`make`/`new` are not — the alternative (every built-in
effect-free, admitting only through a later user call) would send `d[0] + copy(d, s)` to the legacy path, whose
hoist realizes gc's member alone: a (b) pin presented as forced, the audit's F4 class. (iii) The non-spread
element list is PACKED as a slice-literal `allocate` inside append's window rather than passed as payloads on the
`wide` body — the machine's `appendSlice` takes ONE elements slice, and the packed literal is exactly the legacy
hoist's shape (`hoistSliceLit`); the alternative (an `elems : List Expr` on the spec) would restate the packing
in the core. (iv) `copy`'s statement form is admitted (the count discarded) so that `copy(d, f())` classifies
like every other call statement; `clear`/`delete`/`close` statements are not (no result, and alone in a sweep by
Go's grammar — nothing to reorder against). (v) The spread-string row keeps its base under capacity rather than
declaring `width=30`: the `appendSpill` site's latitude is CAPACITY, observable only through `cap()`, which the
row does not read — a 30-way pick with one observation would document a non-site (the depth-guard note's
capacity rows are the precedent).

## E5b. Multi-target assignments, blank targets, the comma-ok forms (landed 2026-09-22)

**The spec clause and the graph shape.** spec#Assignment_statements: «The assignment proceeds in two phases. First,
the operands of index expressions and pointer indirections … on the left and the expressions on the right are all
evaluated in the usual order. Second, the assignments are carried out in left-to-right order.» In the graph every
TARGET is a phase-1 SIBLING: a PLANNED target (a slice element, map element, dereference or field — E2's frozen plans)
is a `target` occurrence on its frozen operand atoms; a PLAIN local target beside a planned sibling is a `target` plan
on its own address (`{"target": "var"}` → the machine's `.var` plan through `.ref`, checks nothing); the stores ride
the phase-2 `stores` list in target order — the inventory's E3/E4 INTER-TARGET axis is thereby the graph's own shape
(the plans unordered among themselves and against the right-hand reads; the events E1-ordered). When NO target is
planned (plain / blank / package-level targets only) the multi-assign rides `then` — the legacy `assign` shape with
its declares, blank discards and interface-boxing wraps — because plain-variable stores never fail and their order is
unobservable (Stage C's `x := e` precedent, E1's global store). The forms: a TUPLE `a, b = e1, e2` (equal arity; blanks
allowed), a MULTI-VALUE CALL `a, b = f()` (an `invoke` with two binders — Stage C's fragment), the COMMA-OK RECEIVE
`v, ok = <-ch` (E3's `recv` body with TWO binders — the machine's `chanRecv` always wrote both; the decoder now admits
the pair, the flag cell bool), the comma-ok MAP LOOKUP `v, ok = m[k]` and TYPE ASSERTION `v, ok = x.(T)` (two-binder
`wide` bodies — `WideSpec.mapLookup` / `.typeAssert`, ARMS of E5a's kind: `Stmt.mapLookup` / `Stmt.typeAssert` with
the binder cells as targets; a mutable READ never failing / a pure op never failing — RESIDUAL occurrences, no E1
edge), and the single blank `_ = e` (the value's occurrences, nothing stored).

**Refused by name** ([AGENT] choices): a PACKAGE-LEVEL target beside a planned sibling («the global plan atom is
deferred» — every target must ride the same store phase, and `unseqAtom` has no `.global` arm: the alternative, a core
arm returning the seeded cell's address behind the heap-size check, is one lemma and posed for the next lane rather
than taken beside the family's other changes); an INTERFACE-TYPED target beside a planned sibling («the store's value
would box inside the graph» — `to-interface` is not an admitted head); a compound multi-target (Go has none); a
non-call single right-hand side of arity ≠ 1.

**The lowering** (`unseq_lower.go`, `multiAssign`): phase 1 IN SOURCE ORDER — every planned target's OPERANDS first
(`prepareTarget`: their events chain lexically before the right-hand side's — the plan node itself is emitted later,
on the frozen atoms, `emitPrepared`), then the right-hand values (a tuple's expressions; the call's binders; `recvN(u,
2)`; the `wide` lookup / assertion via `wideOcc(…, event=false)`), then — some target planned — the plan nodes and
the `stores` in target order (blanks skipped; `ensureCell` copies a constant into a cell), else the `then` multi-assign.
**A WRONG ANSWER caught RED-FIRST by the spec's own example** (`spec-examples-stmt/eval-order-calls/{verbatim,
traced-recv}`: `y[f()], ok = g(z || h(), i()+x[j()], <-c), k()`): the first E5b cut lowered the right-hand values
BEFORE the targets' operands, so `f()` — lexically first — received its E1 edge after `k()` and the machine traced
`h,i,j,g,k,f` where the spec fixes `f h i j <-c g k`. Both rows went FAIL/differential on the candidate (`diff-one-e5b.txt`
run 1), the lowering was corrected (target operands first), both PASS strict again (run 2) with the graph's chain
`call0(f) → guard2(||) after f → call3(h) in the region → join4 → call5(i) after the completion → call6(j) → recv9
after j → call10(g) → call11(k)`. The canonical LIST order (events first, residual after, per level) is unchanged —
only the `after` edges moved.

**The machine**: `WideSpec.mapLookup (base key) (keyTy valueTy)` and `.typeAssert (operand) (target)` — arms of E5a's
`wide` kind (`unseqWideStmt` writes `.mapLookup (.var v) (.var ok) …` / `.typeAssert (.var v) (.var ok) …`;
`WideSpec.arity` 2; names, `eqbF` + soundness, indices, `wideSpecSup` arms). No new constructor, no new Step rule, no
new pick; `check-mem-callsites` unchanged. **The decoder**: the `wide` arm's `map-lookup` (keys stmt/base/index/keyType/
valueType; the value cell typed `valueType`, the flag cell bool — `twoBinds`) and `type-assert` (keys stmt/operand/
target; the value cell typed `target`); the `recv` kind admits 2 binders with a bool flag cell. Mutants
`mut-wide-two-binds`, `mut-recv-ok-type`, `mut-wide-assert-nonatom` (38 → 41); E3's `mut-recv-two-binds` RE-POINTED —
two binders are now the admitted comma-ok form, so its refusal is the flag cell's type (`$u2` an int cell), and the
gate control's needle moved with it.

**References lead** (`enumerate.py` E5b1–E5b4, PASS): E5b1 `s[0], x = m(), 3` (m rebinding s) → {(old[0], s[0])} = {(5, 7),
(1, 5)}; E5b2 `_, x = a[9], wit(1)` → {panic · ``, panic · `wit 1`}; E5b3 `xs[a[9]], ok = <-ch` → {panic · len 1, panic
· len 0}; E5b4 `x, s[0] = two()` (two rebinding s) → {(5, 7), (1, 5)}. Wires: hand-built `e5btuple` {57, 15}, `e5brecv2`
(the comma-ok receive, two binders, a planned target) and `e5bassert` (the comma-ok assertion as a `wide` body, a
singleton — the decoder's arm) + native `e5btuple`/`e5brecv2` (`Tests/UnseqWire.lean` 114 ok / 41 mutants; `check-wire-
boundary` 11 + 38 — the tuple positive control answers 15 on the canonical tape: m first, the NEW header). Frontend
unit tests: witnesses `e5bTupleHeader` (tuple-assign, 1/2), `e5bBlankPanic` (1/1), `e5bCommaOkRecvTarget` (comma-ok,
1/2), `e5bMultiCall` (multi-call, 1/2), `e5bDefineTuple` (1/2), and the Stage C witnesses `multiTarget` (`a, b = s[0],
wit(1)`) and `blankTarget` (`_ = s[0] + wit(1)`) MOVE from the legacy list to the admitted list (a checked access beside
`wit` — their former refusals were the grammar's, not the trigger's); legacy `e5bSwap`, `e5bCommaOkMapOnly`,
`e5bCommaOkAssertOnly` («no call occurrence»), E3's `e3commaOk` now «no non-event occurrence» (the comma-ok receive alone
is all-forced).

**The census** (`census-e5b.txt`): admitted **137 → 154** — +12 from the widening in 10 packages (by former reason
`multi-target or tuple assignment` 11, `blank target` 1; by form multi-call 6, tuple-assign 4, comma-ok 1, blank-assign 1:
`multi-assign/{call-write-back/callPanicIdentity, call-write-back-order/{derefTarget,sliceHeaderBase},
call-write-back-order-value/valueCallDerefTarget, lhs-index-eval-order, target-eval-before-call}`,
`returns/multi-result-assign-order`, `channels/recv-edge/recvDepIndexTarget`, `spec-examples-stmt/eval-order-calls/
{evalOrderCallsVerbatim,evalOrderCallsTracedRecv}`, `noodler/evalorder/logicalShortCircuit`, `noodler/latitude/
rhsListIndexCallIndex`) and +5 the E5a package's sweeps born after its census; 0 lost; the twin 10 203 / 0. Legacy probes
63 → 60 (corpus), the twin 128 unchanged (`probes-e5b.txt`). The 577 + 139 main-unit first-reason sweeps beyond these are
call-free (comma-ok forms, swaps, multi-value calls into plain locals) — legacy under the trigger, as §0 measured.

**Rows** (`scripts/diff-one` on all 65 affected rows, three runs — `diff-one-e5b.txt`; gc's draws `gc-draws-e5b.txt`,
20/20 per subject):

| row | before → after | set | gc |
|---|---|---|---|
| `evalorder/unseq-multi/tuple-header-vs-call` | born PASS/membership (width 4: call, header read, the plain target's plan and the constant's copy all ready) | {57, 15} (E5b1) | 15 |
| `evalorder/unseq-multi/blank-panic-vs-call` | born PASS/membership | {panic · ``, `wit 1` · panic} (E5b2) | `wit 1` · panic |
| `evalorder/unseq-multi/comma-ok-recv-target-vs-panic` | born PASS/membership (width 3) | {`len 1` · panic, `len 0` · panic} (E5b3) | `len 0` |
| `evalorder/unseq-multi/multi-call-header-vs-call` | born PASS/membership (width 3) | {57, 15} (E5b4) | 15 |
| `evalorder/unseq-multi/define-tuple-vs-call` | born PASS/membership | {6, 15} | 15 |
| `evalorder/unseq-multi/{swap-control,comma-ok-map-control}` | born PASS strict, wide=0 | 21; 21 (call-free — legacy by name) | = |
| `multi-assign/call-write-back-order/deref-target` (BUG-052) | PASS strict → PASS/membership (width 3) | {42007, 4207} — the frozen pointer plan before / after `swapPtr` redirects `pg` | 4207 |
| `multi-assign/call-write-back-order/slice-header-base` (BUG-052) | PASS strict → PASS/membership | {1120003, 774203} — the frozen header before / after `replaceHeader` rebinds `sg` | 774203 |
| `multi-assign/call-write-back-order-value/deref-target` | PASS strict → PASS/membership | {42007, 4207} (the call through a func value) | 4207 |
| `noodler/latitude/rhs-list-index-call-index` | PASS strict → PASS/membership (members 4) | {(1,5,1), (1,5,9), (9,5,1), (9,5,9)} — `x, y, z := a[0], f(), a[0]`: two reads of `a[0]` each unordered against `f`, and against each other (R1) | (9,5,9) |
| `spec-examples-stmt/eval-order-calls/{verbatim,traced-recv}` | PASS strict, UNCHANGED (red on the first cut, above) | the forced trace `f h i j <-c g k` · 192 · true | = |
| the other 52 affected rows (`multi-assign/*`, `channels/recv-edge/*`, `returns/multi-result-assign-order`, `noodler/evalorder/*`, `noodler/latitude/*`) | UNCHANGED | every admitted sweep beside these has ONE observation on every order (a plan checking nothing, a call that cannot write the plan's frozen operands) | = |

Baseline 3738 = 3503 / 235 → **3745 = 3510 / 235** (+7 born; 4 stage moves strict → membership; the header carries the
reason). NO PASS → non-PASS. Gates in-process: `check-unseq-wire` PASS (41), `check-wire-boundary` PASS (11 + 38),
`check-mem-callsites` PASS (70), `check-frontend-pins` PASS (the twin byte-identical), `check-unseq-scheduler` PASS,
`check-core-audit` PASS; the full gate line is in the evidence README.

**Latitude.** E2/E12's VALUE axis is (a) ENVELOPED on the five born membership rows and the four moved rows (BUG-052's
three: the fixed post-call target-operand order — gc's — is ONE member of the frozen-plan set, the pre-call plan the
other; `rhs-list-index-call-index`) — posed for ratification at the merge ask; BUG-052's entry carries an ENVELOPED
paragraph. **E3/E4 (inter-target operand order)**: the MECHANISM now exists — targets are phase-1 siblings and the
graph realizes every order of their operand evaluations — but BUG-032's own rows (two panicking target operands, no
call: `aa[5][0], b[*pn] = f6()` has its call as the forced multi-value RHS; `xs[ys[9]], b = zs[7], 2` is call-free) are
routed to the legacy path by the RATIFIED trigger (no effectful event beside the failing operands), so E3 stays (b)
PINNED known-≠-gc and E4 (b) PINNED as entries; their re-envelope is the trigger refinement POSED in the handoff §2 item
2 (panic identity as an observable), one ruling away — not this lane's to take.

**[AGENT] choices (alternatives named).** (i) Plain targets beside a planned sibling become `.var` plans (one store
phase) — the alternative, plain stores in `then` with planned stores in `stores`, would store the planned targets
BEFORE the plain ones regardless of source order (observable when a planned store panics after a plain store that
recovery reads). (ii) All-plain multi-assigns ride `then` (the legacy shape) — the alternative mints a plan and a wide
pick per target for stores that cannot fail. (iii) The comma-ok lookup / assertion are RESIDUAL `wide` bodies (no E1
edge): a map lookup is a read, an assertion a pure op — neither is a call, receive or logical operation. (iv) Target
operands lower first — the lexical E1 chain (the red-first fix). (v) The global-beside-planned and interface-beside-
planned refusals (above).

## E5c. Map literals as `allocate` bodies (landed 2026-09-22)

**The ruling executed.** Item 6/7 ([USER] 2026-09-22): a composite literal is a node WITHOUT E1 edges (v2.1 R3 —
spec#Order_of_evaluation orders calls, method calls, receives and logical operations; a literal is none of those), its
payload reads the occurrences; the `allocate` body is ONE constructor over `AllocSpec`, extended by ARMS. **`AllocSpec.mapLit
(key value : Ty) (entries : List (Expr × Expr))`** is that arm: `unseqAllocStmt` runs `makeMap` into the binder cell then the
keyed entry stores in source order (`mapAssign` — a later duplicate DYNAMIC key overrides, as Go's successive stores do); names
(`pairExprNames`), `eqbF` + soundness, indices (`pairExprIndices`), the loc bound (`pairExprListSup`, `_eq_zero` by
induction) gain the arm. No new constructor, no new Step rule, no new pick.

**The grammar and lowering.** `unseqCompositeLit`'s `*types.Map` case admits a literal of a grammar map type (int/bool/string
key, admitted value) whose every element is keyed (Go's map literals are); each key and value is classified (its reads are the
occurrences). `compositeLit` lowers it as `allocOcc("lit", …, {"stmt": "map-lit", keyType, valueType, entries: [{key, value}]},
event=false)` — in the RESIDUAL, no `after`. **The decoder**'s `map-lit` arm: exact keys, every key and value a PAYLOAD, the
cell typed `map[K]V`, and duplicate CONSTANT keys refused by name (a compile-time error in Go, spec#Composite_literals —
compared on the constants' wire spelling; audit F3's class); mutants `mut-maplit-dup-key`, `mut-maplit-nonatom` (41 → 43). E4's
`mut-alloc-kind` (a slice literal re-tagged `map-lit`) is RE-POINTED at `array-lit`: `map-lit` is an admitted kind now, so its
refusal text had become the exact-key check's. **Audit F8, POSED** (handoff §2 item 4): the wire still does not express the
lowering's «no E1 edge on literals» policy — an `after` edge on a literal `allocate` decodes; making it a named refusal (the
frontend never emits one) is a design choice, not this lane's.

**gc's member.** The E13 guard's measured note holds: gc realizes a map literal at its LEXICAL position — its dynamic entries
BEFORE a later sibling call — where it realizes slice and struct literals AFTER the call (E4's rows). Both are members of the
same sets; the born rows' gc draws are the literal-first ones (6, 6), the noodler row's the call-first one (50 — its call is
INSIDE the literal), and `map-lit-payload-vs-call`'s the panic alone. **The F6 shape realized**: that e13 row was a STRICT
control pinning gc's literal-first panic; under the graph the machine's canonical (call-first) tape prints `wit 5` first — a
strict row whose default ≠ gc — so it becomes a membership row with the reason written (the audit's rule), never a silent
default flip.

**References lead** (`enumerate.py` E5c1 {6, 15}, E5c2 {5, 50}; PASS). Wires: hand-built `e5cmaplit` + native, EXACT
(`Tests/UnseqWire.lean` 118 ok / 43 mutants; `check-wire-boundary` 11 + 41 — the map-literal positive control answers 15 on
the canonical tape). Frontend unit tests: `e4mapLit` MOVES from the legacy list to the admitted list (1/2 — the key's checked
read and the fresh map's read), its canonical shape `invoke eval:index-get allocate eval:map-get eval:binary`; the E13 guard
test's `mapLitPayloadVsCall` moves to the one-graph list.

**The census** (`census-e5c.txt`): admitted **154 → 165** — +2 from the widening (`builtins/e13-sibling-panic-order/
mapLitPayloadVsCall`, `noodler/latitude/mapLiteralKeyVsCall`, both by former reason «map literal») and +9 the born packages'
own sweeps (E5b's `unseq-multi` and `unseq-maplit`); 0 lost (the four «lost/new» pairs the diff prints in `unseq-conv-alloc`
are LINE SHIFTS of the `map-lit-control` comment edit); the twin 10 203 / 0. Legacy probes 60 → 59 (the noodler row's
`index-get` probe), the twin 128 unchanged. The 149 main-unit «map literal» first-reason sweeps beyond these are call-free
(`m := map[int]int{1: 1, …}` declarations) — legacy under the trigger.

**Rows** (`scripts/diff-one` on all 90 affected rows, two runs — `diff-one-e5c.txt`; gc's draws `gc-draws-e5c.txt`, 20/20):

| row | before → after | set | gc |
|---|---|---|---|
| `evalorder/unseq-maplit/map-lit-entry-vs-call` | born PASS/membership | {6, 15} (E5c1) | 6 (literal-first) |
| `evalorder/unseq-maplit/map-lit-key-vs-call` | born PASS/membership | {6, 5} — the key's read before m hits, after m misses | 6 |
| `evalorder/unseq-maplit/map-lit-const-control` | born PASS strict, wide=1 | 6 (the fresh map's read the only unordered occurrence — the R1-NIT class) | 6 |
| `noodler/latitude/map-literal-key-vs-call` | PASS strict → PASS/membership | {5, 50} (E5c2) — the key read vs the value's call inside the literal | 50 |
| `builtins/e13-sibling-panic-order/map-lit-payload-vs-call` | PASS strict → PASS/membership (the F6 shape) | {panic · ``, `wit 5` · panic} | panic alone |
| `evalorder/unseq-conv-alloc/map-lit-control` | PASS strict (unchanged), wide=1 — a graph now | 6 | 6 |
| the other 84 affected rows | UNCHANGED | — | — |

Baseline 3745 = 3510 / 235 → **3748 = 3513 / 235**. Gates in-process: `check-unseq-wire` PASS (43), `check-wire-boundary`
PASS (11 + 41), `check-mem-callsites` PASS (70 — the map-literal statements are the legacy path's own `makeMap`/`mapAssign`),
`check-frontend-pins` PASS, `check-unseq-scheduler` PASS, `check-core-audit` PASS; the full gate line is in the evidence README.

**Latitude.** E2/E12's VALUE axis (a) ENVELOPED on the two born membership rows and the two moved rows — posed for
ratification at the merge ask; E13's `map-lit-payload-vs-call` leaves the strict controls for the membership lane (its
legacy-path pin of gc's literal-first order was a (b) pin by construction — the structural hoist — now enveloped).
**[AGENT] choices.** (i) An `AllocSpec` ARM, not a kind (the ruling's mechanism). (ii) Duplicate constant keys refused at
decode (F3's class: Go rejects the program). (iii) `mut-alloc-kind` re-pointed rather than dropped (its purpose — a
statement kind outside the fragment — stands). (iv) The R1-NIT class recurs (`map-lit-const-control`: the fresh map's read is
a superfluous wide pick, one observation) — recorded, not fixed, with E5a's `min-vs-call` and E4's `*new(x)`: a later
refinement could mark a read of a fresh `allocate` binder stable.

## E5e. Strings — a string index / slice as a failing pure op on the string value (landed 2026-09-22)

**The class.** spec#Index_expressions (for a string `a[x]`: «a[x] is the non-constant byte value at index x … if x is out of
range at run time, a run-time panic occurs») and spec#Slice_expressions (for a string operand «the result of the slice
operation is a … string»; the indices are range-checked at run time). A string VALUE is immutable, so a byte read or a
substring observes nothing but its own operands — the string atom and the index / bounds — and its only observable is its
FAILURE: the same class as a slice's checked access (the pilot's P(ii) read, E13's sibling-panic axis), on a base the pilot's
TYPE grammar admitted as an atom but not as an index / slice base («index of a non-slice base», «slice expression on a
non-slice base (string)» — 217 main-unit «string» first-reason sweeps at the baseline, §0). `len(s)` of a string is an E1
participant like a slice's (reading (a), RATIFIED: spec#Length_and_capacity — its operand's read lies inside its window, so
`len(s) + m()` is all-forced and stays legacy under the trigger — the strict control). The conversion `int(b)` is a pure head
(E4). Refused by name: a full slice expression on a string (Go forbids it).

**The grammar and lowering.** Classifier only (`unseqExpr`, tools/nativefrontend/unseq.go): the `*ast.IndexExpr` case admits
a string base (the base and index classified — a captured or package-level string is a READ occurrence, a private one an
atom — then ONE checked occurrence, the byte read); the `*ast.SliceExpr` case admits a string base (its bounds classified, the
substring the checked occurrence); the `len` arm admits a string operand. The LOWERING already spelled these heads over a
string base (`index-get` typed `uint8`, `slice` with the base's own `builtin-len` as the default high bound, `convert`), and the
DECODER already admitted them (D8's `index-get`/`slice`/`convert` heads, D9 typing the byte cell `uint8`): NO core change, NO
decoder change, NO new mutant — the hand-built wire `e5estr` and its native are the positive controls (`Tests/UnseqWire.lean`
120 ok; `check-wire-boundary` 11 + 42 — the string wire answers 103 on the canonical tape).

**References lead** (`enumerate.py`: E5e1 `int(s[i]) + m()` {102, 103}; E5e2 `int(s[i:][0]) + m()` {102, 103}; E5e3
`len(s[i:]) + m()` {7} — the forced singleton (the substring inside len's window: a first draft of E5e2 as `len(s[i:]) + m()`
was REFUTED by the reference and by the classifier alike — «no occurrence observable against an effectful event» — before any
row was written); E5e4 `int(s[i]) + wit(5)` {panic · (), panic · (wit 5)}; PASS). Frontend unit tests: witnesses
`e5eStrSlice` 1/3 (m | i's read, the substring, its byte), `e5eStrIndexVsCall` 1/2, the legacy `e5eStrLenForced` («no
occurrence observable …»); Stage C's `stringIndex` MOVES from the refused list to the admitted list (1/1); canonical shapes
`invoke eval:ident eval:slice eval:index-get eval:convert eval:binary` / `invoke eval:ident eval:index-get eval:convert
eval:binary`; the E13 guard's `bytesConvPanickyPayload` moves to the one-graph list (its inline conversion's string-slice
operand is the occurrence now — the «probe survives» assertion retired with it).

**The census** (`census-e5e.txt`): admitted **165 → 168** — +1 from the widening (`builtins/e13-sibling-panic-order/
bytesConvPayloadVsCall`, former reason «slice expression on a non-slice base (string)») and +2 the born package's membership
sweeps; 0 lost; the twin 10 203 / 0. Legacy probes 59 → 58 (corpus — that e13 row's), the twin 128 unchanged. The remaining
main-unit «string» residue is call-free or forced (`len(s)` forms, concatenation, conversions without a sibling event).

**gc's members** (`gc-draws-e5e.txt`, 20/20 under GOMAXPROCS 1/8, default and `-N -l`): the plain byte read `s[i]` is
deferred AFTER the sibling call (call-first: `str-index-vs-call` 103; `str-index-panic-vs-print` `wit 5` then the panic) —
but the string SLICE `s[i:]` is realized BEFORE the call (`str-slice-vs-call` 102: order.go hoists the string-slice temporary).
Two different members of two isomorphic sets, both inside the machine's envelope — a measured instance of the doctrine's
«gc pins are scaffolding».

**Rows** (`scripts/diff-one` on all 68 affected rows — the 65 e13 rows and the born package — two runs; `diff-one-e5e.txt`):

| row | before → after | set | gc |
|---|---|---|---|
| `evalorder/unseq-strings/str-index-vs-call` | born PASS/membership | {102, 103} (E5e1) | 103 (call-first) |
| `evalorder/unseq-strings/str-index-panic-vs-print` | born PASS/membership | {panic · ``, `wit 5` · panic} (E5e4) | `wit 5` · panic |
| `evalorder/unseq-strings/str-slice-vs-call` | born PASS/membership | {102, 103} (E5e2) | 102 (the slice hoisted before the call) |
| `evalorder/unseq-strings/str-len-vs-call` | born PASS strict | 7 (E5e3, forced) | 7 |
| `builtins/e13-sibling-panic-order/bytes-conv-payload-vs-call` | PASS/membership, probe → graph | its 2-member set REPRODUCED (enumerated=2) | unchanged |
| the other 64 e13 rows | UNCHANGED | — | — |

**A refusal met and honoured.** The first `str-index-vs-call` (m writing i = 9) had a STATUS-DIVERSE set {102, panic}: the
membership lane refused it BY NAME («member … has status ok, outside the case's declared status set [panic] … status-diverse
envelopes declare e.g. ok,panic — audit F8»). The F8 status-set declaration exists in the harness but NO corpus row uses it;
rather than be the first consumer of an unexercised path inside a runtime lane, the row was SPLIT into the ok/ok form (m: i = 1)
and the panic/panic form (`+ wit(5)`, the E13 shape) — [AGENT] choice, recorded in the row's `why`. Baseline 3748 = 3513 / 235
→ **3752 = 3517 / 235**; NO PASS → non-PASS.

**Latitude.** E2/E12's VALUE axis (a) ENVELOPED on `str-index-vs-call` and `str-slice-vs-call` (the captured index's read vs
the call, on a string base); E13's sibling-panic axis on `str-index-panic-vs-print` and on the e13 row that leaves the probe —
posed for ratification at the merge ask with the others. **[AGENT] choices.** (i) Strings admitted as index / slice BASES in
the classifier, nothing else (no core, no decoder, no wire schema change). (ii) `len(s)` of a string an E1 participant (the
ratified reading (a) names `len` among the built-ins). (iii) The full slice expression on a string refused by name. (iv) The
status-diverse row split, not declared (above).

