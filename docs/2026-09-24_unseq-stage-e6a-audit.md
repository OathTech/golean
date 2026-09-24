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

## Re-verification (fix round `17e12e74`, 2026-09-24)

**REVISED VERDICT: FIX-FIRST (one small decoder defect introduced by the fix round — R1 below; everything else
verified).** The fix round (`973119c2` runtime + `17e12e74` records over the audited tip `1f0dee94`) closes F1–F7 as
claimed; my own build of the fix tip (Lean `567c0289…` after a capped no-op `lake build` on the lane's rsynced
artifacts at `git ls-tree`-identical sources; frontend `45464b37…`) reproduces every measurement below. But the new
scope-exact declaration environment LEAKS a `range` statement's key / value variables into the enclosing block's
scope after the loop, and — with «innermost = last» — REFUSES a legal program that shadows an outer variable of another
type with a range variable and uses the outer one in a graph after the loop (main and the audited tip decode it; gc
agrees with main). A covered-program refusal, fail-closed, one-line fix, two witnesses supplied. Evidence
`docs/evidence/2026-09-24_unseq-stage-e6a-audit/reverify-*`. [AGENT] auditor; detached checkout
`.claude/worktrees/audit-unseq-stage-e6a-fix` at `17e12e74` (tree clean, `deps/` cloned at the pins); no edit to the
candidate or main; no merge; no push; the rebase of this branch is the coordinator's.

### R1 — FAIL-CLOSED WRONG REFUSAL (decoder, new in the fix round): range variables leak into the enclosing scope, so a legal outer-shadow program is refused

What I did. `reverify-p8-main.go` `qRangeLeakOuter`: `k := "ab"; s := []int{7, 8}; r := 0; for _, k := range s { r +=
k }; return s[len(k)-2] + wit(1) + r` — legal Go (the range's `k` is body-scoped; the final graph's `k` is the outer
string), gc 23 (20/20), main's frontend + binary 23. The FIX binary REFUSES the whole wire: «source-local atom 'k' …
is annotated string, which disagrees with its declaration int (the innermost declaration of 'k' in scope at this
statement)». Key-variable spelling the same (`qRangeKeyLeakOuter`: `i := "ab"; for i := range s {…}; s[len(i)-2] +
wit(1)` — main 9 = gc, fix REFUSED). Controls: the `for`-init spelling (`qForInitNoLeak`) and a `select` binder
(`qAfterSelect`) are scoped correctly (fix 9 / 8 = main = gc; a right-typed forged reference to the select binder after
its `select` refuses by name — `h13`). The mechanism, confirmed by `h12`: a right-typed forged reference to the range
variable AFTER the loop DECODES on the fix binary (and sticks late, «unbound GoCore variable address: k» — the
desugaring declares it inside the loop block) — `jsonDeclaredLocals` pushes a `range` node's `keyVar` / `valVar`
whenever it sees the node, and the `block` fold calls it on the range statement, so the body-scoped variables join the
ENCLOSING environment after the loop; `nestedStmtKeys "range"` skips only `body`. (`decodeRange` adds the same
variables for the body — correctly.) `reverify-probes-p8.txt` (the isolated runs), `reverify-mutants.txt` (h12, h13).

Why it matters. A legal, covered program class is refused by the decoder — the trust surface's fail-closed
direction, but a REGRESSION against the audited tip and main, and exactly the kind of «zero by refusing a covered
program» the window forbids. The whole corpus + twin pass only because no corpus row shadows an outer variable of a
different type with a range variable and then graphs the outer one.

Fix (one place). In the `block` fold (or in `jsonDeclaredLocals` when called from it), a `range` statement
contributes NOTHING to the enclosing scope — its `keyVar` / `valVar` are the body's (`decodeRange`'s `rangeLocals`
already supplies them); e.g. add `"keyVar"`, `"valVar"` handling behind a flag, or have the fold skip `range` nodes'
own declarations. Witnesses to track: NATIVE positive controls from `qRangeLeakOuter` (23) and `qRangeKeyLeakOuter`
(9) — must RUN; mutant `h12` (a right-typed reference to the range variable after the loop) — must refuse «has no
declaration … in scope». Re-gate `check-unseq-wire`, `check-wire-boundary`, `lake build`, `ci --diff`.

### The worker's claims, verified one by one

- **F1 — BUG-116 + BUG-032's A6 correction + seven rows.** Read: BUG-116 (`Status: fixed`, `Pinned-by:
  differential`, the seven Cases; its text matches my F1 witnesses — the class, gc's member, main's singleton, the
  assertion-left exception, the general form excluded), BUG-032's dated correction inside the A6 paragraph, handoff
  §2 item 6 reworded, the inventory E13 bullet, the ledger §8 + §8am. Measured (`reverify-rows.txt`): on the fix tip
  each of the seven rows PASS/membership (`scripts/diff-one`, enumerated=2) and its set is EXACTLY {the left operand's
  panic, the built-in's operand's panic}: `idx-left-vs-min-operand` {`[9] with length 1`, `[5] with length 2`},
  `idx-left-vs-len-slice-expr` {`[9] with length 1`, `slice bounds [5:2]`}, `deref-left-vs-len-operand` and
  `ptr-field-left-vs-len-operand` {nil dereference, `[5] with length 1`}, `div-left-vs-len-operand` {`integer divide
  by zero`, `[5] with length 1`}, `shift-left-vs-len-operand` {`negative shift amount`, `[5] with length 1`},
  `compound-load-vs-len-operand` {`[9] with length 1`, `[5] with length 1`}; on main's frontend + binary each is the
  singleton {left panic}; gc 20/20 the built-in operand's panic on all seven (my own draws). Both members are
  spec-permitted (spec#Order_of_evaluation orders neither check); nothing over-wide (no third member anywhere).
- **F2 — the scope-exact environment.** Read the diff (`decodeStmt` `block` fold; `nestedStmtKeys`; `initDeclaredLocals`
  for `if` / `for` init; `decodeRange` key/value; `select` clause targets; `decodeFunc` / `decodeMethod` params + results;
  `unseqCheckLocalAtoms` `findRev?`); no wire-schema change. Measured (`reverify-mutants.txt`): my 27 mutants replayed
  against the fix binary — `mS1-via-typeswitch-binder`, `mR1-typeswitch-binder`, `mR1-shadow-other-decl-type` now
  REFUSE by name («disagrees with its declaration … the innermost declaration of 'v'/'x' in scope»); every other R1 /
  F8 mutant still refuses by name; the positive controls run; the legal p4 wire (23 functions, re-lowered by the fix
  frontend) decodes and runs. The new tracked mutants (52 → 55) and `check-wire-boundary` 11 + 55 are in the gate
  (§ Gates). New probes (`reverify-probes-p8.txt`): labelled loop / labelled block with `goto`, `switch` init,
  type-switch init, a `case`-body define and `var`, `range` with a body shadow, an outer variable used AFTER an inner
  shadowing block, two sibling blocks declaring one name with two types, `else if` init, an if-init variable used in
  the ELSE branch, a closure param shadowing the enclosing block's name, captured reads in a lifted body (legacy — no
  graph, as before), a named result after a shadowing block, a method receiver, a `select` with send + recv clauses, a
  `for` init declaring two variables, a define that redeclares its own operand's name (`s := s[0] + wit(1)`), and
  range / for-init / if-init / select binders shadowing an outer name of ANOTHER type — every one decodes and matches
  main and gc on the fix side EXCEPT the range-variable leak (R1). Range over a function iterator is refused by the
  FRONTEND («range over func(yield …)») on both sides — not R1. Scoping holes CLOSED (fix refuses where the tip did
  not): a use-before-declare (`h5`, a `var` statement moved after its graph — the tip decoded it and stuck late), a
  type-switch binder / if-init variable / inner-block variable referenced after its construct (`h-after-construct-
  {v,w,z}`), the closed inner block's type on the outer variable (`h7`), the range shadow annotated with the outer type
  (`h10`), a define's own declaration type on its operand (`h11`). Left open: the range leak (R1) — `h-after-construct-k`
  refused for the wrong reason («disagrees», via the leaked int `k`) and `h12` decodes. The pinned twin decodes under
  the fix binary (`reverify-twin-decode.txt`: `probeTwinChoice --fuel 20000` → fuel-out, i.e. the whole 800+-function
  program decoded; main's binary the same).
- **F3 — the twin's graphs re-described.** Design §E6a «the twin re-pin», `scripts/check-frontend-pins` header,
  handoff §5 / changelog lines: pointer receivers, the guards, `plainpbSizeVarint` a function, «E3's rule through the
  unit boundary, none by the refinement, all-forced» — correct. Pin bytes unchanged: `baselines/pins/twin-chdriver.wire.json`
  sha256 `1c4e7038…` at `17e12e74`; `check-frontend-pins` ok in the gate.
- **F4 — the SUBSET phrase** in design «the scope» and handoff §2 item 1, with the gc facts (lexical on every general-form
  probe except BUG-032's tuple) — as I measured; the charter carries ONE dated correction line under the slice table
  naming the 7 mis-labelled emitters (the row's text kept as ruled); `generic-conversion` counted once (22 + 128, the
  sum 4 + 2 + 9 + 22 + 128 + 10 = 175) in the design's and the handoff's residue tables.
- **F5 — census re-taken.** My reproduction at the fix tree, both frontends (`reverify-census.txt`): 108 294 sweeps,
  180 → 273 admitted, 100 newly admitted (the 93 + the seven born rows' sweeps), 0 lost; legacy probes corpus 58 → 47
  (e13 11 → 9 with 50 → 60 graphs, `len-vs-call-order` 15 → 6), the twin 128 → 128 with 3 graphs; 25 refused packages
  identical — the worker's figures exactly.
- **F6** — the handoff's changelog section now states the file does not exist and packet A creates it. **F7** — the
  late-named store-target refusal is recorded in design §E6a «R1» as outside R1's reach.
- **Baseline** `3761 = 3525/236 → 3768 = 3532/236`: by name exactly the seven born rows, 0 changed, 0 removed (`git
  show 1f0dee94:baselines/native-full.tsv` vs the fix tip's); the header records the first re-pin attempt's malformed
  stage-alternation refusal (`ci-diff-fix-run1.tail.txt` — the gate caught the worker's own error, honestly kept) and
  the rebuilt header. `check-bugs` ok (116) in the gate.
- **Trace.** The worker's whole-corpus trace vs `1f0dee94` (3732 ids, 3725 identical, 0 DIFFER, 7 ONLY_B; `unseqNext`
  2550 → 2595, every other site identical) is coherent with my own outside-family check: **225 ids** from packages
  outside the 42 E6a-affected packages, main `3fb4a0d1`'s frontend + binary vs the fix tip's — **225 SAME, 0 DIFFER**,
  identical site censuses (`reverify-trace.txt`).
- **Customer inventory** under the fix frontend (unchanged by the round — the wires are byte-identical to the E6a
  emit): 22/22 export, 0 `unseq`, 0 probes (`reverify-inventory-counts.tsv`).
- **Gates on the fixed tip.** `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --slow` at `17e12e74` (the detached checkout, tree clean, `deps/` at the pins) under the box-wide lock 05:05:20Z–05:20:24Z: **EXIT=1 in 904 s; `cases=3768 pass=3531 fail=237`** = the re-pinned 3768 = 3532/236 with the one 5a-class row red; RESULT FAIL on EXACTLY the two 5a-class items (`certificate provenance` STALE for the changed decoder; the `baseline diff` DRIFT block's one line `imported-goose/channel/google-search`); `unseq wire (Stage C)` ok (55 mutants), `wire boundary` ok (11 + 55), `frontend pins` ok (the twin = pinned bytes), `bug-index cross-check` ok (116), every other step ok (`reverify-ci-slow.tail.txt`). The run's `latest.tsv` vs the fix baseline: no row moves except the 5a-class line and the standing both-sides-FAIL stage-string variance (`channels/select-select/beside-loop`); vs the audited tip's baseline: exactly the seven born rows PASS/membership and nothing else (`reverify-latest-vs-baselines.txt`) — the decoder change moves no row, as claimed.

### Anything new

R1 above (new, introduced by the fix round). Nothing else: the seven sets are exact, the decoder refuses only forged
wires plus the R1 class of legal programs, the frontend is unchanged (the census, the inventory and the twin emit are
byte-for-byte the E6a ones), the trace is byte-identical outside the seven born rows.

## Re-verification 2 (fix round `86df4cc9`, 2026-09-24)

**FINAL VERDICT: MERGE-CLEAN.** Fix round 2 (`afb25c7c` runtime + `86df4cc9` records over `17e12e74`) closes R1 as
named and disturbs nothing else. My own build of the fix-2 tip in the detached checkout (Lean `ada4125e…` — capped
no-op `lake build` on the lane's rsynced artifacts at `git ls-tree`-identical sources; the frontend `45464b37…`
byte-identical to fix round 1's — this round changed no Go) reproduces every claim. [AGENT] auditor; no edit to the
candidate or main; no merge; no push; the rebase is the coordinator's. Evidence
`docs/evidence/2026-09-24_unseq-stage-e6a-audit/reverify2-*`.

- **The change, read.** The `range` arm left `jsonDeclaredLocals` for `rangeBinderLocals`, whose ONE caller is
  `decodeRange` (for the body); the `block` fold therefore sees a `range` node contribute nothing (its `body` skipped
  by `nestedStmtKeys`, its binders no longer walked); the scope rule is stated once on `nestedStmtKeys` with the
  construct table (block / breakable / labeled body, `if` init, `for` init, `range` key/value, `select` receive-clause
  targets, func / method params + results; `switch` / type switch are desugared to `declare`s in clause blocks). No
  wire-schema change; `baselines/` and `Corpus/` untouched.
- **R1 closed.** `qRangeLeakOuter` → 23·`wit 1`, `qRangeKeyLeakOuter` → 9·`wit 1` (isolated and in the p8 wire) on
  the fix-2 binary = main = gc (20/20); `qForInitNoLeak` 9, `qAfterSelect` 8, `qAfterConstructs` 8 unchanged. My h12
  (a right-typed reference to the range variable after its loop) now REFUSES BY NAME («has no declaration in the
  enclosing function that is in scope at this statement»); `h-after-construct-k` refuses by name too (it refused for
  the wrong reason under the leak); new h14 / h15 (the post-loop OUTER variable annotated with the RANGE's type) refuse
  by name. The tracked witnesses match: `e6arange` 23, `e6arangekey` 9, `e6arangeafter` 8 (verbatim my probes), the
  mutant `mut-local-range-var-after-loop` (my h12's base) in `mutants.tsv` (55 → 56); `check-unseq-wire` 56 and
  `check-wire-boundary` 11 + 56 pass in the gate below.
- **Round-1 mutants and positives untouched.** My 27 mutants + the mS1 type-switch forgery replayed on the fix-2
  binary: every R1 / F8 forgery refuses by name, every control runs, the legal p4 wire (23 functions) decodes and runs;
  the round-1 scope holes (h5, h7–h11, h13, `h-after-construct-{v,w,z}`) still refuse by name (`reverify2-mutants.txt`).
- **The 29 p8 declaration-form / scope probes** re-run on the new binary: every canonical observation identical to
  main and to gc (`reverify2-probes.txt`); `qRangeFunc` is refused by the FRONTEND on both sides (range over a
  function iterator — outside the modeled subset, not R1).
- **New constructs (`reverify2-p9-main.go`, 14):** a range body redeclaring the key with another type; nested ranges
  reusing `i` with different element types, graphs in both bodies and after each loop; a labelled range with
  `continue` and a post-loop graph; map / string / channel / integer ranges shadowing outer strings and graphed after;
  two sequential ranges reusing `k` with different types and graphs after each; a range inside a `select` clause body,
  inside a labelled block reached by `goto`, inside a lifted closure — each with a post-construct graph on the outer
  shadowed name; a body graph on the range `k` beside a post-loop graph on the outer `k`; a same-type shadow; a
  key-only range with a blank value — **main = fix-2 on all 14, gc 20/20 the same value on all 14**; nothing leaks,
  nothing is over-refused. A range «inside an `unseq` node's region» is not a Go shape (a region is an expression's
  guard region; the node's completion is one statement) — not testable, not a gap.
- **Baseline UNCHANGED** `3768 = 3532/236` (`git diff 17e12e74 86df4cc9 -- baselines/ Corpus/` empty) — assessed: no
  corpus row is owed. R1 was a decoder wrong-refusal INTRODUCED and FIXED inside the candidate (main never had it, so
  no fidelity gap was ever observable on main); the shapes are pinned where the defect lived — as NATIVE witnesses with
  exact sets equal to gc's draw (`Tests/UnseqWire.lean`, `check-wire-boundary`) and a refusing mutant. A corpus
  membership row for `e6arange` would add a standing gc-side check cheaply; optional, not owed.
- **Trace.** The worker's whole-corpus trace vs `17e12e74` (3732/3732 byte-identical) is coherent with mine: my 225
  outside-family ids on the fix-2 binary — 225 SAME vs main's frontend + binary and 225 SAME vs the fix-round-1 binary
  (`reverify2-trace.txt`).
- **Gate at `86df4cc9`.** `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --slow` at `86df4cc9` (the detached checkout, tree clean) under the box-wide lock 06:18:01Z–06:32:38Z: **EXIT=1 in 877 s; `cases=3768 pass=3531 fail=237`** = the unchanged baseline 3768 = 3532/236 with the one 5a-class row red; RESULT FAIL on EXACTLY the two 5a-class items (`certificate provenance` STALE for the changed decoder; the `baseline diff` DRIFT block's one line `imported-goose/channel/google-search`); `unseq wire (Stage C)` ok (56 mutants), `wire boundary` ok (11 + 56), `frontend pins` ok (the twin = pinned bytes, `1c4e7038…`), every other step ok (`reverify2-ci-slow.tail.txt`). The run's `latest.tsv` vs the baseline: no row moves except the 5a-class line and the standing both-sides-FAIL stage-string variance (`channels/select-select/beside-loop`) — the decoder change moves no row (`reverify2-latest-vs-baseline.txt`).

Nothing new.
