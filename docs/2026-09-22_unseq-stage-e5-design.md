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
