# Adversarial audit — Stage E6a of the evaluation-order model v2.1, branch `core/unseq-stage-e6a-0924` (candidate tip `1f0dee94` over `3fb4a0d1`; main `58aa7dbe` = the same runtime tree)

**VERDICT: FIX-FIRST (records, small) — no WRONG ANSWER and no OVER-WIDE set on the candidate; one minor decoder
FAIL-OPEN inside the residual class the lane itself disclosed (its reach is under-stated, F2); one main-side
WRONG-ANSWER CLASS that the candidate silently FIXES without a BUG entry or a row (F1); the twin's three born graphs
are mis-described in four records (F3).** Every member of every born / moved / migrated set is spec-permitted and gc's
draw is inside on my own 20-draw matrices (14 corpus subjects, 61 probe subjects); the trigger as shipped is a
faithful SUBSET of the ruled wording, its complement honestly measured and posed; `len`/`cap` over map / channel
operands behave as spec#Length_and_capacity says (nil → 0, the count at the participant's position, forced orders
forced); the unit boundary resolves callee identity across units (same-name collision, qualified callee, library
method) and refuses the shapes it names (func-typed package variable, generic, variadic); the census (108 264 sweeps,
180 → 266 admitted, 93 newly admitted BY NAME = the lane's list, 0 lost; legacy probes 186 → 175: `len-vs-call-order`
15 → 6, `e13-sibling-panic-order` 11 → 9, the twin 128 → 128 with 3 graphs born; 25 export refusals identical) and the
emitter lists reproduce exactly; the twin re-emits byte-identical to the new pin (1c4e7038…) with the candidate's
frontend and to the old pin (e1a87725…) with main's; the baseline delta is exactly 1 born + 2 strict → membership +
0 removed (3524/236 → 3525/236); every R1 declaration form I could think of decodes on the legal wire and refuses my
forgeries by name except the type-switch binder (F2); the F8 refusal fires on `new`-over-struct-literal and
`map-lit` and the `make`/`new(x)` positive control still runs; the customer's 22 units still emit 0 graphs and 0 probes
under the candidate's frontend; the C2 racy sample is oracle-side (PASS alone, PASS under load 23). The seven PENDING
[USER] items are real decisions, honestly posed; none is self-adjudicated (§ PENDING). The full gate at the tip
reproduces the lane's result (§ Gates).

[AGENT] auditor, 2026-09-24, under the [USER]'s standing direction that every merge is audited adversarially (Mike,
2026-09-11, relayed by the [AGENT] coordinator — cite as relayed), the window charter's per-item audit rule
(`docs/2026-09-23_batched-window-charter.md` §6) and the coordinator's dispatch of 2026-09-24. Worktree
`.claude/worktrees/audit-unseq-stage-e6a`, branch `review/unseq-stage-e6a-0924` at the candidate tip;
`scripts/setup-deps --from` the primary (goose `3be88bb`, raft `56e3200`, go `c19862e5f8`); `.lake/build` rsynced from
the lane at `git ls-tree`-identical Lean sources, `GOLEAN_MEM_MAX=32G scripts/capped lake build` a no-op (binary
sha256 `bb607430…` = the lane's); the candidate's frontend built from this tree (`be137623…` — path-dependent, the
lane's `aead74a3…` is the same source), main's frontend from `git archive 3fb4a0d1` under `.tmp/main-tree`
(`85e055b4…`), main's binary the primary's `.lake/build/bin/golean` (`63e9c661…`, read-only, = the lane's
`golean-main`). `git diff --stat 3fb4a0d1 core/unseq-stage-e6a-0924 -- GoLean/GoCore` is EMPTY (no core change —
verified). No edit to the candidate or main; no merge; no push. Evidence
`docs/evidence/2026-09-24_unseq-stage-e6a-audit/` (`scripts/check-evidence-size` EXIT=0). Every decision below is
[AGENT].

## Findings, by severity

### F1 — RECORDS (a main-side WRONG-ANSWER class the candidate fixes silently — BUG entry and rows owed)

What I did. Probes `p1/compoundLoadVsLen`, `p6/{derefCompoundVsLen, fieldPtrCompoundVsLen, derefVsLen, fieldPtrVsLen,
idxVsLenSliceExpr, divVsLen, shiftVsLen}`, `p7/{idxVsMin, idxVsMax, idxVsCapSlice, derefVsLenStr, idxVsLenMapIdx,
compoundVsMin, idxVsLenNested}` — fifteen call-free sweeps of the shape **a LATE-realized failing non-call operand
(a slice index, a slice expression, a dereference, a pointer-field read, a division / shift by a non-constant, a
compound target's LOAD) LEFT of an inline built-in E1 participant (`len` / `cap` / `min` / `max`) whose own operand
panics** — `x[9] += len(b[j])`, `*p + len(b[j])`, `q.f += len(b[j])`, `s[i] + len(t[k:])`, `x/y + len(b[j])`,
`x<<s + len(b[j])`, `s[i] + min(t[k], 1)`, `s[i] + cap(t[k:])`, `s[i] + len(mm[t[k]])`, …. On MAIN every one is a
strict singleton holding the LEFT operand's panic (the legacy path evaluates lexically); **gc realizes the built-in's
operand's panic on all fifteen, 20/20 each** (GOMAXPROCS 1/8, default and `-N -l`) — observed ∉ modeled: a wrong
answer on main, undetected because no corpus row has the call-free shape (`e13/compound-index-vs-len` and kin carry a
trailing `wit(5)`, which admits them to the graph since Stage E). The candidate's refined trigger admits each as a
graph whose set holds BOTH panics (gc's inside). The assertion-left instances of the same class (`iv.(int) +
len(b[j])`, `iv.(int) + min(t[k], 1)` — the two red-first rows; my `assertVsLenIdx`, `minShape`, `guardRegionFail`,
`assertVsLenStrSlice`, `assertVsCapSlice`) are the exception: gc evaluates the type assertion EARLY, so main's lexical
singleton happened to be gc's member and the lane's «a (b) pin of one spec-legal order, not a wrong answer» is right
for those two rows — and wrong as a description of the class. The mirror (`len(b[j]) + s[i]`: `rightOfEvent`,
`idxVsLenRightIdx`) is inside on main (gc = the len operand = lexical) and widened by the candidate.
`probe-results.txt`, `gc-draws.txt`.

Why it matters. `docs/BUGS.md` BUG-032's A6 AMENDMENT (2026-08-31) states «with NO ordered event after the builtin
in its sweep, len stays inline and realizes gc's left-to-right point» — true only for an assertion on the left; for an
index / dereference / division / load on the left gc's point is the built-in's operand first (the built-in behaves as
the call reading (a) says it is; E12's own «call-first» half predicts gc here, and the legacy path contradicts it).
BUG-083's fix-round text recorded the same three left shapes as «MATCHED gc» for the HOISTED `make` — the inline
built-ins were never measured. The candidate retires the defect as a side effect of marking the load / deref /
division / shift / index occurrences FAILING; nothing in the design, the handoff, BUGS.md or the ledger says a
wrong-answer class died here, and no row pins the fix («every detected gap is rowed», [USER] 2026-09-03).

Disposition (small). (i) A BUG-032 amendment (or a new entry cross-referencing it): the class, the fifteen witnesses
with gc's draw, «fixed at Stage E6a by the refined trigger (the legacy path still realizes the lexical order for the
call-free general-form shapes, where gc agrees — F4)»; (ii) rows — at least one per left-operand kind
(`evalorder/unseq-…/{idx-left-vs-len-operand, deref-left-vs-len-operand, div-left-vs-len-operand,
compound-load-vs-len-operand, idx-left-vs-min-operand}`), membership with gc's member (the built-in's operand's
panic) in the set; (iii) the handoff §2 item 6 / design «rows» paragraph reworded: the two moved rows are the
assertion-left members of a class whose other members were wrong answers on main.

### F2 — FAIL-OPEN (decoder, minor — the disclosed R1 residual reaches TYPE-SWITCH binders; mS1 through one decodes and answers) + RECORDS (the residual's reach under-stated)

What I did. `p4/pTypeSwitchMap`: `switch v := iv.(type) { case map[int]int: r = v[1] + wit(1); case map[string]int:
r = v["a"] + wit(2) }` with `iv = map[int]int{}`. The emitter spells the binder PER CLAUSE — `declare v :
map[string]int` in one clause, `declare v : map[int]int` in the other (`pTypeSwitch` likewise declares `v` as
`string` and `int`) — so `jsonDeclaredLocals`'s flat table holds BOTH map types for `v`. Mutant
`mS1-via-typeswitch-binder`: in the `map[int]int` clause's graph, `v`'s annotation, the `map-get` head's `keyType`
and its key constant all forged to `map[string]int` / `string` / `"a"` — R1 passes (the set contains the type),
audit F1's base check compares against the annotation and passes, and the CANDIDATE DECODES AND ANSWERS `1` (the
empty map performs no key comparison — the E5 audit's mW12 pattern). Control: the same forgery on a name declared
once (`mR1-comma-ok-var`, `mR1-var-decl`, `mR1-if-init-var`, …) refuses by name; the legal type-switch wire runs.
`mutants.txt`.

Why it matters. The lane states the residual as «a name Go's block scoping declares TWICE with DIFFERENT types in one
function» (`GoLean/NativeToIR.lean` docstring, design §E6a «R1», handoff §2 item 4). A type switch with several
single-type clauses is ONE source declaration and a common Go idiom; the wire's per-clause spelling makes it the
residual's most likely real-world instance, and it is the exact mS1 shape the R1 follow-up was ruled to close. The
emitter never produces it (decoder latitude, not a wrong answer) — the E5 audit's F1 class, one layer down.

Disposition. Records now: the docstring / design / handoff item 4 name the type-switch binder (and the `select`
comma-ok / `range` re-declarations of one name in sibling blocks) as instances of the residual, with this mutant as
the witness (tracked as a KNOWN-DECODES witness or left in the audit evidence — it must not enter `mutants.tsv`,
whose entries must refuse). Fix (posed, a [USER] call whether now or owed): a scope-exact declaration environment —
thread `locals` through `decodeStmt` per block (a `declare` extends the environment for the rest of its block; a
`range` / type-switch / `select` binder for its body) so the check sees ONE type per name at each atom.

### F3 — RECORDS: the twin's three born graphs are mis-described (no failing occurrence in two of them; none is born by the refinement)

What I did. Decoded the three `unseq` nodes from the pinned wire (`twin-born-graphs.txt`) and re-classified the same
shapes in the main unit (`p5`). `raft.isHardStateEqual(a, b *pb.HardState)`: `a.GetTerm() == b.GetTerm() && …` — the
raftpb getters have POINTER receivers (`func (x *HardState) GetTerm() uint64 { if x != nil && x.Term != nil … }`), so
the receivers `a`, `b` are ATOMS; the graph's occurrences are six `invoke`s, three pure `binary`s, two GUARDS and
their joins — **no failing occurrence**; `raft.MustSync` the same with `||`. The census row says `nonEvents=2` (the
two guards). They are admitted by Stage E's E3 rule (a guard whose window is followed by an effectful call), newly
REACHABLE through the unit boundary — my main-unit replicas `isHSEqual` / `mustSyncShape` are admitted by MAIN's
frontend too. `raftpb.(*Snapshot).SizeMessage`: `n += 1 + plainpbSizeVarint(uint64(len(x.Data))) + len(x.Data)` —
the nil-checked `x.Data` reads beside the effectful FUNCTION call `plainpbSizeVarint` (E3's rule again, unit boundary).

Where. Design §E6a «the twin re-pin» («the HardState getters' nil-checked field reads unordered against each other
across the `&&` chain's E1 windows … a compound `n += …` whose nil-checked field read is unordered against the
sibling method call»); `scripts/check-frontend-pins` header (the same sentence); the handoff §1 row C1 / §3; the
changelog lines. The conclusion drawn from the wrong description («the born graphs' sets are singletons on the twin's
non-nil states») happens to hold — the graphs are all-forced: every occurrence is an E1-ordered call, a pure op or a
guard — so the twin's observations are unchanged for a stronger reason than the one written.

Disposition. Reword the four places: «three sweeps of the raft / raftpb units enter the graph through the unit
boundary under Stage E's E3 rule (a guard followed by effectful calls; a nil-checked field read beside a call) — none
by the E6a refinement; their graphs are all-forced (singletons)».

### F4 — RECORDS (the trigger's scope and the «21 panic-vs-panic» accounting)

(a) The shipped EVENT-MEDIATED form is a strict SUBSET of the ruled wording («… OR against another FAILING
occurrence»): it requires an E1 participant's window between the two failing occurrences. Faithful, not a
re-interpretation — but a narrowing of the ruling's literal scope by [AGENT] choice, honestly POSED (handoff §2 item
1) with the complement measured (856 sweeps). My general-form probes — `a[i] + b[j]`, `x/y + s[i]`, `p.f + q.g`,
`iv.(int) + s[i]`, `x, y = a[i], b[j]`, two failing operands inside ONE `make` window (`twoInsideWindow`) — are
legacy singletons on both sides and **gc realizes the lexical order on every one (20/20)**, so NOT taking the general
form creates no new observed-∉-modeled; the one general-form shape where gc differs is BUG-032's own
`xs[ys[9]], b = zs[7], 2` (gc `[7]` 20/20, machine `[9]` on both sides) — the inventory's E3 «(b) PINNED, known ≠ gc»,
which the general form would fix. The spec permits both orders on all of them (spec#Order_of_evaluation orders only
calls, receives and logical operations). The ruling record's «~30 rows» was loose: the census names 21 emitters.
(b) Of the 21, my reproduction of the emitter lists matches the lane's: 11 close (`len-vs-call-order` 9 incl.
`makeNilOnly`, e13 `assertLeftMakeSlice`, `tgtAssertVsMake`), 10 stay, EACH by a type-grammar refusal (an
interface-containing map key ×3, a `for` condition, generic stencils ×2, slice-to-array conversion, interface
comparison, a send statement, a captured read in a lifted body) — none is a trigger question. But the charter's label
«PANIC-vs-PANIC pairs with no effectful event (21)» was wrong for 7 of them: `lenStructAnyKeyLeftAssert`,
`convLeftCall`, `ifaceCmpLeftCall`, `sendChanIndex`, `assertReturnList$lit0` (a `wit` call), `makeHintCall`
(`boomCall`) and `lexerIdiom` (`l.peek()`) contain an effectful call and were grammar refusals from the start; the
lane's residue table classes them correctly but does not say the charter's count was mis-labelled. (c) The handoff §3
residue table counts `imported-goose/generics/generic-conversion` twice (under E6b AND in the «23 corpus» non-main
class): the class is 22 corpus + 128 twin once E6b owns it; 4 + 2 + 9 + 22 + 10 = 47 ✓.

### F5 — NIT (records): the census figures are pre-born-row

The lane's «179 → 265» was measured before `str-index-status-diverse` existed; at the tip both frontends admit its
sweep: 108 264 sweeps, **180 → 266** (the 93 newly admitted identical by name). State the tree the census was
taken on, or re-take it at the tip.

### F6 — NIT (records): the handoff's changelog pointer

`docs/changelog/61958f2e-WINDOW.md` («for the coordinator to merge») exists on no branch (main, the candidate,
`docs/window-plan-0924`); the changelog lines live only in the handoff.

### F7 — NIT (decoder latitude, late-named): a forged store-TARGET id

`mR1-target-id-undeclared` (pNamedResult's store target `r` → `zz` in the plan and the completion) is not an atom, so
R1 does not see it; the machine sticks LATE («expected array, slice, or string value for index access, got int 0»)
— closed by name, not an answer; the standing class the Stage E and E5 audits recorded.

## (a) The trigger refinement — what the shipped rule admits, and every member's permission

Rule as implemented (`tools/nativefrontend/unseq.go` `observable`, `ordered`, `unseqOccRec.failing`,
`closePF(…, name == "make")`): a FAILING occurrence `o` is observable iff some participant `x` in its unordered
window is effectful (E3), may itself fail (`make`), or holds a failing occurrence unordered against `o`. I read
`ordered` against the spec's own example (`y[f()], ok = g(h(), i()+x[j()], <-c), k()` — «the order of those events
compared to the evaluation and indexing of x … is not specified»): consumption (`i >= p.first`), completion before the
consumer's `lo`, and the guard protocol are the only orderings — matching the spec's three (operand subtree, the E1
chain, `&&`/`||` test-before-region). Probes: `guardTestRegion` (test vs region → legacy), `guardRegionFail` (two
failing inside the region across `len`'s window → {conversion, `[7]`}, gc conversion), `nestedWindow`, `threeFail`
(`iv.(int) + s[i] + len(make([]int, t[k]))` → exactly the three panic texts, gc conversion), `twoAssertsVsCall`
(four members = 2 texts × wit printed or not, gc conversion·``), `idxVsMakeNeg` (`a[i] + len(make([]int, -1))` →
{`[5]`, `makeslice: len out of range`}, gc makeslice — main already had both via the probe), `compoundDivVsLen`
(`x /= len(b[j]) + y`: the division consumes its divisor → legacy, `[5]` = gc). No member outside the spec's
permission anywhere; the corpus rows' sets in the table below.

| row / probe | main | candidate | gc (20) | permitted because |
|---|---|---|---|---|
| `e13/assert-left-min-inline` `iv.(int) + min(t[k], 1)` | {conversion} strict | {conversion, `[5] with length 2`} | conversion | the assertion is not a call / receive / logical op; `min` is (reading (a)); their relative order is spec-open |
| `channels/recv-order/dead-recv-len-operand` `iv.(int) + len(b[j])` | {conversion} strict | {conversion, `[7] with length 0`} | conversion | as above with `len` |
| `evalorder/unseq-strings/str-index-status-diverse` | — | {102 ok, panic `[9] with length 2`} | panic | E5e's axis, the STATUS observable |
| `len-vs-call-order/{hint-panicky-between, make-slice-panicky-between, make-chan-cap-panicky-between, make-inner-len}` | 2 (probe) | 2 (graph) | conversion | probe → graph, sets reproduced (`scripts/diff-one` in the gate) |
| `len-vs-call-order/make-index-left` | {`[9]`, `[5]`} | same | `[5]` | two index panics across `make`'s window |
| `len-vs-call-order/{make-hint-panic-free, make-hint-map-read, make-hint-call, make-nil-only-*}` | singletons | singletons | conversion / `boom-call` / 8 | one observation on every order |
| `e13/{assert-left-make-slice, tgt-assert-vs-make}` | 2 (probe) | 2 (graph) | conversion | as the hint rows |
| p1 `rightOfEvent` `len(b[j]) + iv.(int)` | {`[5]`} | {conversion, `[5]`} | `[5]` | the mirror; both legal |
| p1/p6/p7 the F1 class (15 shapes) | {left panic} — gc OUTSIDE | {left, built-in's operand} | the built-in's operand's | both legal; main's singleton excluded gc's |
| p1 general-form shapes (`a[i]+b[j]`, `x/y+s[i]`, `p.f+q.g`, `iv.(int)+s[i]`, tuple, `twoInsideWindow`) | lexical singleton | same (legacy) | lexical | spec permits two; UNDER-wide vs the literal ruling — POSED (item 1) |
| p1 `bug032Shape` `xs[ys[9]], b = zs[7], 2` | {`[9]`} | {`[9]`} | **`[7]`** | E3's recorded (b) pin, known ≠ gc — unchanged by the candidate; the general form's ground |

## (b) `len` / `cap` over map and channel operands (p2)

`wit(1) + len(m)` (nil map) 1; `wit(1) + len(ch) + cap(ch)` (nil chan) 1; `len(ch)*10 + cap(ch)` with 2 buffered of 3 →
24; `len(m) + add(m)` 11 (len before the inserting call, E1-forced) and `add(m) + len(m)` 12; `len(m) + reset()` with
`m` captured and REASSIGNED by reset → 11 (m's read inside len's window, before reset — legacy «no occurrence
observable», correct); `len(ch) + sendOne(ch)` 100 / `sendOne(ch) + len(ch)` 101; `cap(ch) + grow()` 5;
`iv.(int) + len(mm[t[k]])` (a map read whose key operand panics, inside len's window) → {conversion, `[5]`}, gc
conversion; `wit(2) + len(mm[3])` (nil inner map) 2, a graph now (the map read is a non-failing occurrence beside
wit) with one observation. gc 20/20 inside on all twelve; main and the candidate agree on every singleton. No hidden
pin: the widening admits two operand kinds to an existing head (`builtin-len` / `builtin-cap` over an atom, the
decoder's D8); the machine's evaluation of the head is the legacy path's.

## (c) The unit boundary (p3, the twin)

`sub.Mut(s) + s[0]` → {100, 2} (main 100 strict; gc 100); `sub.G(s, 9)` — the graph INSIDE the imported unit, `s[i] +
Wit(5)` → {panic·``, panic·`wit 5`} (main had both through the legacy probe, which fires in non-main units too);
`t.Bump() + t.N` (a method of the imported unit's struct, the field read through the pointer) → {1, 2} (gc 2); `t.Val()
+ sub.Wit(5)` (value receiver: the auto-deref is consumed by `Val`, which precedes `Wit`) → legacy, 8 = gc;
`r.Len() + s[i]` (`*strings.Reader`, a stdlib source-through METHOD callee) → a graph, singleton `[9]` (Len is pure);
`len(strings.TrimSpace(" a ")) + s[i]` likewise; `sub.F(1) + s[i]` refused by name «call through a qualified
func-typed package variable (sub.F)»; `sub.Id[int](3)` «callee expression outside the pilot grammar»; `sub.Sum(1, 2)`
«variadic callee»; `sub.H(s) + G(s, 0) + s[0]` (main's `G` beside `sub.H`, which calls `sub.Mut` and reads `s[0]`) →
exactly the five sums {4, 8, 102, 106, 200} the spec permits (the inner read before / after `Mut` × the outer read
before / between / after the two calls), gc 106 inside — identity resolves correctly across the units. The callee is
`func-value{funcWireName(obj)}` — bare for main, path-qualified otherwise, the legacy static call's own FuncId
(`unseq_lower.go` `call`, the `*ast.Ident` arm unchanged since Stage C, the qualified arm new). The twin: emitted with
the candidate's frontend = the pin byte-for-byte; with main's = the old pin; the three born graphs are all-forced (F3);
the twin's 128 probes unchanged, all `field-get` on `raft.raft` / `raftpb.Message` / `tracker.Progress` /
`raft.raftLog` / `raft.unstable` (interface or defined-non-struct fields) or the `raft.raft` receiver — a type-grammar
axis, confirmed on the reproduced census (`census-repro.txt`: «field selector on a struct type outside the grammar
(raftpb.Message)» 85, «(raft.raft)» 71, «method receiver type outside the grammar (raft.raft)» 89). NOT verified by
execution: the twin driver under the machine (`probeTwinChoice`, ~40–65 min per `tools/raftsubject/README.md`); the
singleton argument is structural (every occurrence of the three graphs is an E1-ordered call, a pure op or a guard)
and reproduced on the main-unit replicas (p5: `hsEqualNonNil` 0, `hsEqualNilRight` 1, `mustSync` 0, `sizeMessage` 5,
`sizeMessageNilMeta` 5 — one observation on both sides, gc =).

## (d) The census claims (`census-repro.txt`, `probe-census-repro.txt`)

Both frontends over every corpus package + the twin assembly with the lane's tooling copied: 108 264 sweeps (the
lane's 108 258 + the born row's 6), admitted 180 → 266 (+86 corpus in 41 packages + 7 twin), **93 newly admitted,
identical BY NAME to `census-newly-admitted-e6a.tsv`, 0 lost**, by former reason «no call occurrence» 48, «callee
outside the main package» 34, `len` over a map 5, «method callee outside the main package» 3, `pkg.F` 2, `cap` over a
channel 1 — the lane's breakdown exactly. Legacy probe emission 186 → 175 (58 → 47 corpus in 17 packages; the twin 128
→ 128, 0 → 3 graphs); the two changed packages are `len-vs-call-order` (15, 4) → (6, 13) and `e13-sibling-panic-order`
(11, 50) → (9, 53); 25 export-refused packages, identical sets. Nothing closed by refusal: the 34 export refusals of
the trace and the 25 of the census are identical on both sides, the baseline has 0 PASS → non-PASS and 0 removals, and
the 11 closed emitters' rows keep their results in the gate (§ Gates). Zero was NOT reached and is not claimed.

## (e) The decoder follow-ups — 27 audit mutants through the real CLI (`mutants.txt`, `mutants.py`)

| mutant | edit | result |
|---|---|---|
| `mR1-range-slice-valvar` / `-keyvar`, `-range-map-valvar`, `-range-chan-var`, `-range-int-var`, `-range-string-rune` (int32 → int) | a range variable's annotation forged | REFUSED «disagrees with its declaration» ×6 |
| `mR1-param`, `mR1-select-binder`, `mR1-if-init-var`, `mR1-comma-ok-var`, `mR1-var-decl`, `mR1-for-init-var`, `mR1-captured-addr-taken` | a param / `select` binder / if-init / comma-ok / `var` / for-init / address-taken local's annotation forged | REFUSED by name ×7 |
| `mR1-other-functions-local`, `mR1-undeclared-in-select` | an atom renamed to another function's local / to `zz` | REFUSED «has no declaration in the enclosing function» ×2 |
| `mR1-ref-undeclared` (on `Tests/unseq-wire/e5daddr.json`) | `ref x` → `ref nosuch` | REFUSED «names no local the enclosing function declares» |
| `mS4-map-target-plan-forged` | E5b's map target plan: base annotation + plan `keyType` forged self-consistently on a once-declared map | REFUSED by name (R1 first) |
| `mR1-shadow-other-decl-type` | the inner block's string `x` annotated `int` (the outer declaration's type) | DECODES AND RUNS — the residual exactly as the lane states it |
| **`mS1-via-typeswitch-binder`** | the int-map clause's `v` annotation, `keyType` and key constant forged to the OTHER clause's map type | **DECODES AND ANSWERS 1** (F2) |
| `mR1-typeswitch-binder` | `v` (int clause) annotated `string` | DECODES AND RUNS (the same table; answers 8 — the annotation is not used at run time) |
| `mF8-after-on-new-struct-lit`, `mF8-after-on-map-lit` | an `after` edge on `&T{…}` / a map literal's allocate | REFUSED «an `after` edge on a literal allocation» ×2 |
| `ctl-e4new-new-with-after-legal` (`Tests/unseq-wire/e4new.json`, `new1` after `call0`) | none | RUNS (110) — the positive control |
| `ctl-p4-shadow-legal`, `ctl-p4-typeswitch-legal` | none | RUN (the legal shadowing and type-switch wires decode) |
| `mR1-target-id-undeclared` | a store target's `id` → undeclared | STUCK late, named (F7) |

Coverage of declaration forms on the LEGAL wire (p4, both frontends, identical results): params, named results,
`range` over slice / map / channel / integer / string, block shadowing with different types, `select` `v :=` and
`v, ok :=`, type-switch binder, if-init, comma-ok map read, `var` (single and multi), type-assert define, channel
receive defines, address-taken capture, a `for` init, `new`, `&T{…}`, a map literal — every one decodes; no legal
wire is refused (`probe-results.txt` §p4). Lifted bodies name their captures `x$cap` as params (the emitter's
spelling), inside R1's reach.

## (f) The status-diverse row and the lane-validation shapes

`str-index-status-diverse` PASS/membership here (`scripts/diff-one`: enumerated=2, gc's draw the panic 32/32 in the
harness, 20/20 in my matrix); `coverage-observations --expect-status ok` on the graph refuses «member under pick
assignment [0] has status panic, outside the case's declared status set [ok]», `--expect-status panic` refuses the ok
member, `ok,panic` enumerates both — fail-closed in both directions. `scripts/coverage-manifest` /
`scripts/diff-coverage` `parse_lane_params` route `statuses=ok+panic` (`scripts/diff-coverage:1472–1504`, the
BUG-044 mechanism, in use on three older rows) — the E5 records' «unreachable from a row» was indeed wrong and the
dated corrections are in all five places. `scripts/test-lane-validation` gained the empty set / strict-row / foreign
word shapes (68 ok lines in the gate).

## (g) Records

Baseline `3760 = 3524/236 → 3761 = 3525/236`: by name exactly 1 born (`str-index-status-diverse` PASS/membership),
2 strict → membership (`assert-left-min-inline`, `dead-recv-len-operand`), 0 removed, 0 PASS → non-PASS; the header
carries the reason; BUG-032's Cases row `dead-recv-len-operand` has its dated amendment; the inventory's E13 bullet
names the 14 + 2 rows and the residue, E3/E4/E12 carry the «general form POSED» bullets, no entry moves; the ledger
§8 arithmetic checks (3760 + 1, 3524 + 1); `check-bugs` ok (115). The C2 racy sample (`race/negative/struct-tag-alias-
field` PASS/racy → FAIL/go-observation once, under two whole-corpus traces): the row's package has no graph and the
frontend change cannot reach `go run -race`; re-run alone PASS (26 s) and re-run under this box's load average 23
(during my full gate) PASS — oracle-side sampling, as the lane classified it. The customer inventory (§ (i)) and the
twin pin (§ (c)) reproduce.

## (h) Gates

Standalone, reproduced here: `check-evidence-size` PASS (with this audit's dir), `check-frontend-pins` (via the twin
re-emit = pin). The full gate at the tip: `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --slow` at `1f0dee94` (tree clean) under the box-wide lock 03:34:51Z–03:49:48Z: **EXIT=1 in 897 s; `cases=3761 pass=3524 fail=237`** = the re-pinned 3525/236 with the one 5a-class row red; RESULT FAIL on EXACTLY the two 5a-class items (`certificate provenance` STALE for the changed decoder / pin script; the `baseline diff` DRIFT block's one line `imported-goose/channel/google-search` PASS/membership → FAIL/membership); every other step ok; the re-pin guard 0 PASS→non-PASS; the C2 racy sample did not recur (`ci-slow-tip.tail.txt`). The run's `latest.tsv` against main `3fb4a0d1`'s baseline BY NAME: the 1 born row, the 2 moves, the 5a-class line, and one stage-string variance on a row that is FAIL on both sides (`channels/select-select/beside-loop`, `lean-observation|differential` → `lean-observation`, which the gate's own diff treats as matched) — no other row's result or stage moved: the lane's «375 rows unchanged» and the 14 migrations' unchanged results reproduce at whole-corpus scale (`latest-vs-main-baseline.txt`).

## (i) The customer inventory under the candidate's frontend

The 14 fixture directories of `/home/dev/projects/golean-logic` @ `b2c37c14` (read-only, copied out) + the 8 generated
`f2` variants (`gen-f2-variants.py` from `records/customer-fixture-inventory-0924`), lowered with the candidate's
frontend: **22/22 export (exit 0, empty stderr); 0 `unseq` graphs, 0 graph-body occurrences, 0 `unseq-probe`** in every
unit; statement totals identical to the inventory at `3fb4a0d1` (`customer-inventory-e6a-counts.tsv`,
`customer-inventory-e6a-export.txt`). E6a changes nothing for the logic team's units.

## PENDING [USER] items (handoff §2) — assessed, not decided

1. **The trigger's scope.** A real decision. The shipped form is a faithful subset of the ruled words; the general
   form is the words' literal reading. The recommendation (ship (B), pose (A)) is sound on the record: (A) moves
   E3/E4/E12 from (b) to (a) as ENTRIES (a HARD STOP by the brief) and admits 856 sweeps incl. hot library loops. My
   measurement adds two facts: on every general-form shape I probed gc realizes the lexical order (no new
   observed-∉-modeled from NOT taking (A)), and the one place gc differs is E3's recorded pin (BUG-032's tuple),
   which (A) would fix. The alternative («a later slice with its own re-pin») is honest. Note F1: the event-mediated
   form already fixed a wrong-answer class — the general form's ground is a recorded pin, not a wrong answer.
2. **`len`/`cap` over map / channel.** Sound and small; spec-exact on my probes; the alternative (refuse, 10 rows stay
   probes) is honestly stated. Recommend ratify.
3. **The unit boundary to every source unit.** Sound; the identity questions hold on my probes; the alternative
   («case-local imports only») has no semantic ground, as the lane says. Recommend ratify — with F3's records fixed.
4. **The flat R1 table.** The residual is REAL and broader than stated (F2: type-switch binders). The alternative
   (a scope-exact environment) is the actual fix; whether to take it now or owe it is the [USER]'s — the class is
   decoder latitude the emitter never produces, the same standing the R1 follow-up itself had at the E5 landing.
5. **The status set from `params`.** Correct; fail-closed both ways; the E5 corrections honest. Recommend ratify.
6. **The two red-first moves.** Both members spec-legal, gc inside; the moves are right. But see F1: the class has
   wrong-answer siblings on main that the same refinement fixes — a BUG entry and rows are owed with the moves.
7. **E6's exit re-scoped by measurement.** The 175 residue and its axes reproduce: 15 = E6b 4 + E6c 2 + E6d 9; the
   other 160 = 22 corpus non-main (F4c: `generic-conversion` counted once) + 128 twin + 10 panic-vs-panic residue —
   every one a type-grammar axis (I re-read each emitter's source: interface / defined-non-struct fields, interface
   comparison, `error`-field library structs, arrays, generic stencils, a `for` condition, a send, a captured read, a
   slice-to-array conversion); none is a trigger question. The question (E6d absorbs them as named axes, or the
   retirement moves to a later window) is the coordinator's / [USER]'s and is honestly posed; the charter §6 rule
   applies as the lane says.

## Dispositions (proposed)

| finding | severity | disposition | blocks merge? |
|---|---|---|---|
| F1 | RECORDS (main-side wrong-answer class fixed silently) | BUG-032 amendment / new entry + ≥ 5 membership rows + reword handoff item 6 | yes (records; small) — or POSE as the first follow-up with the rows' bodies from `probes/p6-main.go`, `p7-main.go` |
| F2 | FAIL-OPEN minor + RECORDS | state the type-switch reach in docstring / design / handoff item 4; scope-exact env POSED | records yes; the fix a [USER] call |
| F3 | RECORDS | reword design §E6a, `check-frontend-pins` header, handoff, changelog lines | yes (records) |
| F4 | RECORDS | (b) note the charter's mis-label; (c) count `generic-conversion` once | no |
| F5, F6, F7 | NIT | note the census tree; drop or create the changelog pointer; none | no |

## What I could not verify, and why

The twin under the machine (the driver's run is ~40–65 min; structural + replica evidence instead); the 856-sweep
general-form footprint (not rebuilt — the file is coherent with the census I reproduced, the number is the lane's);
the whole-corpus choice trace (not re-run — the full gate's `latest.tsv` against main's baseline stands in for
behavioural preservation, § Gates); gc's draws are samples (20 per subject), not proofs of gc's set.

## Evidence (`docs/evidence/2026-09-24_unseq-stage-e6a-audit/`)

`README.md` · `probes/p{1..7}-main.go`, `probes/p3-sub.go` (the probe sources) · `run-probe.sh`, `twin-emit.sh`,
`mutants.py` (producers) · `probe-results.txt` (every probe, both sides: census decision, canonical tape, set) ·
`gc-draws.txt` (tabulated 20-draw matrices, 75 subjects) · `mutants.txt` · `census-repro.txt`,
`probe-census-repro.txt` · `twin-born-graphs.txt` · `customer-inventory-e6a-{counts.tsv,export.txt}` ·
`ci-slow-tip.tail.txt`, `latest-vs-main-baseline.txt` (the gate).
