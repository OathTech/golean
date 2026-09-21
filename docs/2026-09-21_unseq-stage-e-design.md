# Stage E — family migration of the evaluation-order model v2.1: the design record, per family (2026-09-21)

[AGENT] Lane `core/unseq-stage-e-0921` (worktree `.claude/worktrees/unseq-stage-e`), branch off main
`74d084ad` (rebased onto the train's records-only `14006270`). Design of record:
`docs/2026-09-16_evaluation-order-model-v2.md` (v2.1) §7 row E — «Family migration: by operand and
statement family: BUG-101/104, assignment targets, guards, receivers, allocations; legacy
`unseqProbe`/`probeK`/`unseqPanic` removed ONLY after all callers, tests and consumers moved;
whole-sweep boundary, no fixture-name dispatch; EXIT: per-family full gate + `--diff`, named set
changes, pins/ledgers updated». Rulings in force ([USER], `docs/2026-08-31_qrow-rulings.md`): width of
P = ALL mutable reads, STAGED (2026-09-19 «Agree, merge», relayed); N1 = SPLIT; N3 = REFUSE by name;
E2/E12 (b) → (a) on the pilot's rows (2026-09-20 «land it», relayed — extended here to every migrated
row, each named); the confluent caption covers expression-order picks (2026-09-21 «yes, I agree — go
ahead», relayed). Stage C's design (`docs/2026-09-19_unseq-stage-c-design.md`: the pilot grammar §1,
the wire §4, the decoder spec §5, the lowering §6) and Stage D's route α
(`docs/2026-09-20_unseq-stage-d-design.md`) are extended, not restated: this note records what EACH
FAMILY adds — the grammar widening, the decoder arm, the reference witnesses, the census before/after,
the rows born/flipped/moved with their sets, the latitude reclassifications posed for ratification, the
[AGENT] choices with their alternatives. Everything below is [AGENT] unless marked. The handoff is
`docs/2026-09-21_unseq-stage-e-handoff.md`; evidence `docs/evidence/2026-09-21_unseq-stage-e/`.

## 0. The families and their order

| family | what enters the grammar | closes | core change |
|---|---|---|---|
| **E1** package-level variables (LANDED, §E1) | reads `g` / `pkg.V` as READ occurrences (`deref(globaladdr)`); operand-free targets (`g = e`, `g op= e`, `g++`) | **BUG-113** (two rows FAIL → PASS) | none (decoder D8: the `deref` head) |
| E2 pointers, fields, maps | `*p`, `p.f`/`s.f`, `m[k]` reads; map-element target plans (`m[k] = e`, `m[k] op= e`) — one frozen plan shared by load and store | BUG-104's `map-compound-index-key-vs-call` | `unseqReadTarget`'s `.mapElem` arm (+ its `locSup` lemma); `unseqAtom` string constants |
| E3 receives, method calls | `<-ch` as an EVENT occurrence (E1-ordered); concrete-receiver method calls as invocations (receiver sub-evaluation = occurrences) | BUG-104's `compound-call-target-vs-recv`, `map-compound-index-key-vs-{recv,method}` | a statement-bodied occurrence kind (the receive) + its `Step` rules and coherence arms |
| E4 conversions, allocations | numeric/string/byte/rune conversions as ops; `&T{…}`, slice literals, `make` as allocation occurrences (payload reads are the occurrences; no E1 edges) | BUG-102's five designed reds | the same statement-bodied kind (allocation statements) |
| E5 multi-target forms, the residue | tuple/multi-value assignment, comma-ok forms, blank targets; the census residue migrated or stated | E3/E4 latitude entries (inter-target order) | — |
| E6 retire the legacy triple | when the census shows ZERO legacy `unseq-probe` emissions | — | delete `Stmt.unseqProbe`/`Cont.probeK`/`ChoiceSite.unseqPanic` with their arms |

The order is the brief's recommendation — the families that close open WRONG ANSWERS first (E1 closes
BUG-113, a spec-forbidden member the legacy hoister realizes; E2/E3 close BUG-104's observed-∉-modeled
rows; E4 retires BUG-102's designed reds); each family is ONE gated runtime commit with records between.
The whole-sweep boundary rule is unchanged (v2.1 §3.7; Stage C design §1): one sweep is EITHER one
`unseq` graph OR the legacy path, decided by `unseqClassify` alone — never by fixture name, never a
mixture (the mixture guard and decoder D14 stay).

## E1. Package-level variables as occurrences (landed 2026-09-21)

**The grammar widening** (`tools/nativefrontend/unseq.go`). A PACKAGE-LEVEL VARIABLE — unqualified `g`,
or source-package qualified `pkg.V` (W1.1's name resolution) — of an admitted type (int kinds, bool,
string, slices of them, `any`) is a mutable location. Its READ is a READ occurrence and counts toward
`nonEvents` (`unseqExpr`'s Ident and Selector arms). As an ASSIGNMENT / COMPOUND / IncDec TARGET
(`unseqVarTarget`, the former `unseqLocalTarget`; `unseqQualifiedTarget`) its identity has no operands —
a plan that checks nothing — so the store rides `then` exactly like an address-taken local's, and a
compound form's load is the same READ occurrence (`unseqReadWriteTarget`: `nonEvents++`). `g = f()`
alone stays legacy by the trigger (no non-event occurrence: every edge forced). A global of a type
outside the grammar refuses by name («package-level variable / target of a type outside the grammar
(T)»). WHETHER THE CELL IS SEEDED is the lowering's check, not the classifier's: the census runs before
`emitProgram` builds the globals table, and the census must not drift from the emitter; an unseeded or
FR-24-poisoned global refuses by name inside `emitIdent` (the same per-declaration quarantine as the
legacy path — `init/stdlib-initializer-dependent` refuses identically on both).

**The lowering** (`unseq_lower.go`). `value`'s Ident arm: a package variable's `emitIdent` wire is
`deref(globaladdr gid)` — the head of an `eval` READ occurrence (`read<n>`); the Selector arm does the
same through `emitQualifiedSelector`. Targets: `emitAssignTargetPhase1` already spells a global target as
`addr(globaladdr)` — `then: assign addr(globaladdr) = $u` — for both spellings; `readWrite`'s variable
arm serves `g op= e` / `g++` (the read occurrence + the op; the store in `then`). Canonical order is
unchanged (events first per frame, then the residual): the all-zero tape realizes calls first, the
global read late — gc's call-first realization on every E1 row.

**The decoder** (`GoLean/NativeToIR.lean`, D8): the `deref` head is admitted when its `ptr` is an atom
(a slot or admitted local — the E2 family's `*p`) or a `globaladdr`; any other pointer position is a
hidden read, refused by name (mutant `mut-deref-hidden`, the 20th). The `deref` keys are the standing
`["expr","ptr","type"]`; D9 types the head against its cell. No machine change: the head evaluates under
the frame like every `eval` head (`unseqRunEval`/`unseqValue`).

**The reference leads the lowering** (`docs/evidence/2026-09-16_eval-order-v2-spike/enumerate.py`,
regenerated `outcomes.txt`, RESULT PASS): E1a `v := mut() + g` (mut: g = 2) → {1, 2}; E1c `g += f()`
(f: g = 10, returns 1) → {2, 11} (the store lands in phase 2 through g's operand-free identity);
E1b = BUG-113's c01 with `left` a package-level variable — the SAME graph as R2b, the singleton
{`logical false 0`}, the legacy `logical true 0` asserted FORBIDDEN. Hand-built wires
`Tests/unseq-wire/{e1,e1c}.json` (build.py: the gid is an envelope fact read off the frontend's own
emission, like a lifted closure's name) and the frontend's OWN lowerings `native-{e1,e1c}.json` give
those sets EXACTLY over the wire (`Tests/UnseqWire.lean`: 65 ok, 20 mutants refused by name;
`scripts/check-unseq-wire` PASS; `scripts/check-wire-boundary` PASS, 11 + 11 controls — the global-read
positive control and the hidden-read refusal added).

**The census** (`docs/evidence/2026-09-21_unseq-stage-e/census-e1.txt`): main `74d084ad`'s frontend vs
the E1 frontend over 1356 corpus packages + the raft twin — 107 943 sweeps; admitted 136 → 146 (+10, in
4 packages; 0 lost); the twin 10 203 sweeps, 0 admitted before and after (pin byte-identical). The ten:
`evalorder/legacy-logical-vs-call` ×3 (the BUG-113 rows and their control), `spec-examples-decl/
select-forms` ×5 (`sLog += … + itoa(…)` compound globals; two `return sLog + … + itoa(fCalls)`),
`panic-recover/repanic-collapse` `indexTwoFaults` (`sink = idx(s, 5)`, a global target beside a call
whose argument slice is address-taken), `init/stdlib-initializer-dependent`'s `main`
(`println(unrelated(), maxYear)`). Of the BEFORE census's 169 «package-level variable» refusals only
these ten enter: the rest meet another construct outside the grammar next (the census prints the
FIRST), and the still-legacy package-level reasons are all TYPE refusals (`*int`, `[3]int`, `chan int`,
struct types — E2/E4's).

**Rows** (measured by `scripts/diff-one` on all 13 affected rows, `diff-one-e1.txt`; gc's draws
`gc-draws-e1.txt`, 20/20 per row under GOMAXPROCS 1 and 8, default and `-gcflags=all='-N -l'`):

| row | before → after | set (output · result) | gc |
|---|---|---|---|
| `evalorder/legacy-logical-vs-call/or-vs-call` (BUG-113) | FAIL/differential → PASS strict, wide=0 | {`logical false 0`} — the R2b graph, every edge forced | = |
| `evalorder/legacy-logical-vs-call/and-vs-call` (BUG-113) | FAIL/differential → PASS strict, wide=0 | {`logical false 0`} | = |
| `evalorder/legacy-logical-vs-call/call-first-control` | PASS strict (unchanged), wide=1 | the read of `left` vs `change()` (which does not write `left`) — one observation | = |
| `evalorder/unseq-globals/read-vs-call` | born PASS/membership | {1, 2} (E1a) | 2 |
| `evalorder/unseq-globals/compound-vs-call` | born PASS/membership | {2, 11} (E1c) | 11 |
| `evalorder/unseq-globals/read-vs-unrelated-call` | born PASS strict, wide=1 | `wit 1` · 2 (both orders agree) | = |
| `evalorder/unseq-globals/plain-target-call` | born PASS strict, wide=0 | `wit 1` · 2 (legacy by the trigger — the control) | = |
| `spec-examples-decl/select-forms/{ready,default,block-forever}` | PASS strict (unchanged), wide=4 / 2 / 0 | the global reads beside `itoa` — no sibling call writes `sLog`/`fCalls` | = |
| `panic-recover/repanic-collapse/index-two-faults` | PASS/membership (unchanged), enumerated=2 | the `repanicCollapse` set; the new `unseqNext` pick (the address-taken `s`'s header vs `idx`) changes no observation | = |
| `init/stdlib-initializer-dependent` | FAIL/frontend-export (unchanged, pre-existing) | the H-11 poison of `maxDatetime`'s initializer refuses the whole export on both frontends | — |

NO lane move, NO widened pin, NO PASS → non-PASS. Baseline 3705 = 3459 / 246 → 3709 = 3465 / 244
(+4 born, +2 flips); BUG-113 `Status: fixed` (`check-bugs.sh` ok). **The full gate** (`scripts/capped
scripts/ci --slow` at the E1 tree under the box-wide lock, 02:10–02:28Z): EXIT=1 in 1083 s, K=80; 3709 rows
3464 PASS / 245 FAIL in the run = the pin with the one 5a-class row red; RESULT FAIL on exactly the two
5a-class items (`certificate provenance` STALE for `GoLean/NativeToIR.lean`; the drift line
`imported-goose/channel/google-search` PASS→FAIL/membership); every other step ok — the evidence README's
gate paragraph and `ci-slow-e1.tail.txt`. The 56 label-shape facts
(`Tests/GoCoreEval.lean`) are untouched (no machine change). `scripts/check-mem-callsites` untouched.

**Latitude** (`docs/2026-08-11_latitude-inventory.md`): E2's and E12's VALUE axis is (a) ENVELOPED on
TWO more rows — `evalorder/unseq-globals/{read-vs-call,compound-vs-call}` (a package-level read beside a
call that writes it: both values are members, gc's call-first value among them) — posed for
ratification at the merge ask with the pilot's precedent; the entries stay (b) PINNED for the rest of
their families. BUG-113's fix is NOT a latitude reclassification: the `||`-before-a-later-call order
is spec-FORCED (spec#Order_of_evaluation), the graph realizes it, the legacy member was forbidden.

**[AGENT] choices (alternatives named).** (i) The classifier stays SYNTACTIC on globals (seeded-cell and
poison checks in the lowering) — the alternative, consulting `globalVars` in the classifier, would make
the census (run before `emitProgram`) disagree with the emitter. (ii) A global target's store rides
`then`, not a `target`+`store` pair — the alternative would mint a target occurrence with no operands
(a plan that checks nothing and freezes nothing), one more pick position per loop iteration for no
semantic content (the Stage C private-compound precedent, design §7). (iii) The decoder's `deref` arm
admits an atom pointer NOW (E2's `*p` spelling) beside `globaladdr` — one arm, one mutant; the
alternative (a `globaladdr`-only arm, widened at E2) would restate the arm and its refusal text one
family later. (iv) BUG-113 is fixed by MIGRATION, not by the interim E1-at-completion anchoring in the
legacy hoister the entry's fix plan also named: a second implementation of the ordering the graph
already realizes, for sweeps the later families migrate anyway. (v) No corpus row for the qualified
`pkg.V` spelling: it needs a multi-package program; the classifier/lowering arms are exercised by the
unit test's shape only through the unqualified path and by the census (0 qualified sweeps admitted in
the corpus or the twin) — recorded as a gap, not claimed covered.

## E2. Pointers, fields and maps as occurrences (landed 2026-09-21)

**The grammar widening** (`unseq.go`). TYPES: pointers to admitted types; NAMED STRUCT types (non-generic,
no embedded fields) whose every field is admitted (cycle-guarded — a self-pointing field is admitted once);
maps with an int/bool/string key (never a defined or interface-containing key: the boxed key would sit
inside the graph) and an admitted value. READS: `*p` is ONE occurrence on the pointer value (a nil check +
a mutable read, `nonEvents++`); a FIELD selection `x.f` (`unseqFieldSel`: `FieldVal`, no promoted hop, a named
struct, an admitted field type) through a POINTER is one occurrence (`nonEvents++`), on a struct VALUE it
takes the base's own classification — an address-taken struct local's read is the occurrence (the
lowering FUSES it with the selection into one `field-get` read, no struct-typed cell), a private struct
local's field is a stable read (an `eval` op, no count), a nested base (`a[i].f`) produces a slot; a MAP
element read `m[k]` is one occurrence on the frozen base and key values (`nonEvents++`; hash-safe by the
type grammar). TARGETS (`unseqDerefTarget`, `unseqFieldTarget`, `unseqMapTarget`): `*p`, `p.f` / `s.f`
(a pointer operand, or a struct VARIABLE — local or package-level — whose address is the anchor; a nested
value base refuses by name), `m[k]` — each a FROZEN plan that checks nothing and reads nothing of its own,
so a plan on atoms does NOT by itself admit a sweep (`m[1] = wit(5)`, `*p = f()` with p private stay
legacy — the [AGENT] choice below); the compound / IncDec forms' LOAD is the mutable read that does
(`nonEvents++`). Interface-typed pointees / fields / map values as targets refuse by name (boxing inside a
graph). The whole-sweep boundary and the trigger are unchanged.

**The lowering** (`unseq_lower.go`). `*p` → `eval deref(ptr atom)`; `p.f` → `eval field-get(deref(ptr atom))`
(the emitter's own `fieldBase` spelling), `s.f` → `eval field-get(ident s)` (fused) or `field-get(slot)`;
`m[k]` → `eval map-get(base atom, key atom, keyType, valueType)`. Plans: `*p` → `target $t addr(ptr atom)`;
`p.f` / `s.f` → `target $t addr(field-addr(ptr atom | ref s | globaladdr, typeId, f))`; `m[k]` → `target $t
map(base atom, key atom, keyType, valueType)` — `Assignee.mapElem`, the machine's `TargetRef.mapElem` (the
map VALUE and key VALUE frozen). `planTarget`/`plannedAssign`/`readWrite` share ONE path for every planned
target (slice element, map element, dereference, field): plan → (load → op →) store in phase 2.

**The decoder** (`NativeToIR.lean`). D8: `field-get` with an atom or `deref(atom)` receiver; `map-get` over
atoms. D13: `.addr (.var p)` (a dereference plan on a pointer atom), `.addr (.fieldAddr base …)` with an
anchor `.var`/`.ref`/`.global`, `.mapElem base key` over atoms (int/bool/string constants included). Mutants
`mut-map-target-key` (a non-atom key) and `mut-deref-target-nonatom` (a non-atom pointer position) — the
21st and 22nd.

**The machine** (`GoLean/GoCore/Machine.lean`, TRUST SURFACE #1 — ONE arm + ONE atom): `unseqReadTarget`'s
`.mapElem` arm reads the frozen map VALUE's entry at the frozen key VALUE — `valueAsMap`, `normalizeValueForTy`
at the key type, `mapLookupValue` — exactly the comma-ok source's lookup (`applyRhsOp .mapLookup`; a nil map
hashes the key and yields the zero value, an absent key the zero value); `unseqAtom` gains `.stringLit` (a
string map key). `StateWf`: `unseqReadTarget_locSup`'s map arm is `mapLookupValue_locSup`; `unseqAtom_locSup`
gains the string case. `unseqUnfrozenPlan?`'s `.mapElem` stays `none` (a map value is a reference, a key a
value — nothing re-read). No `Step` rule, no `stepFn` arm, no coherence statement changed: `unseqRunLoad`
runs the same `unseqLoad.plan`; `stepFn_sound`/`step_complete` are untouched. `check-mem-callsites`: the arm
reaches memory through the emitting `Mem.mapRead` inside `mapLookupValue` — no raw op, the inventory
unchanged. The Stage B hand-built test «target: frozen map-element plan (Stage E)» FLIPS from a refusal to
the set test «map replacement (frozen map VALUE)»: `m[1] += mut()` with `mut` rebinding the captured map →
{`old 11 m 100`, `old 10 m 101`}, the hybrids absent (the spike's R4 on a map; the Stage B acceptance
matrix's «map/pointer deferred to E» — pointer redirection was already Stage B's `ptr` test).

**The reference leads** (`enumerate.py`, a `maps` state component; `outcomes.txt` PASS): E2a `*p + setVia(p)`
→ {1, 2}; E2c `m[1] + setM(m)` → {1, 2}; E2d BUG-104's `m[t[k]] += wit(5)` → {`` · `[5]`, `wit 5` · `[5]`}; E2e
`*p += mut()` with mut redirecting p → {`x y 11 100`, `x y 10 101`}, the hybrids FORBIDDEN; E2f `m[1] += mut()`
with mut rebinding m → {`old 11 m 100`, `old 10 m 101`}, hybrids forbidden; E2g `*p + wit(5)`, p nil → the
nil dereference before or after the call. Wires: hand-built `e2ptr.json` / `e2map.json` + the frontend's own
`native-{e2ptr,e2map,e2fld}.json` (checksums 11100 / 10101) — `Tests/UnseqWire.lean`, `check-unseq-wire`,
`check-wire-boundary` (+ 3 controls: the map-plan positive, the two mutants).

**The census** (`census-e2.txt`): admitted 146 → 176 — +27 in 17 packages from the widening (0 lost) and +3 from
the E1 package `evalorder/unseq-globals`, born after the E1 census (107 943 → 107 963 sweeps); the raft twin 0
(its sweeps' callees are outside its main unit). By former reason: 5 pointer indirections, 7 map-element
targets, 5 selectors, 5 struct/map parameter types, 2 map reads, 2 assignment targets, 1 dereference
target. The 27 (`census-newly-admitted-e2.tsv`): the four E13 deref/map rows' sweeps and BUG-104's map row;
`len-vs-call-order`'s `lenNilOnly` / `lenAssertVsNilOperand` / `lenNilLeftVsIndexOperand` (field reads
through pointers beside `len`/`wit4`); `imported-goose` (`*(deferSimple()) == 10`, two `ok = ok &&
IterateMap…(m) == …` with a map argument); `maps/compound-assign-eval-once`, `maps/map-incdec`; noodler's
`mapIndexBeforeRHS`, `elidedPointerLiteralOrder`, `derefVsCall`, the two map compounds, `methodExpressions`
(`get(c), c.n`), `recursiveSliceStruct`; `pointers/deref-target-rhs-call-order`; `slices/slice-elided-high-
eval-once`'s `m[k()][1:]`; `spec-examples-decl`'s `*pf(x)` and `pp.x*10000 + …`; `method-expr-five-forms`'s
`f1(t, 7)` / `f2(t, 7)`; `structs/selector-eval-once`'s `get().x += 4`.

**Rows** — DERIVED before measurement from the graphs (the sets are the enumerator's shapes; gc's draws
`gc-draws-e2.txt`, 20/20 per row under GOMAXPROCS 1 and 8, default and `-N -l`, each inside its set):

| row | before → after | set (output · result) | gc |
|---|---|---|---|
| `builtins/e13-sibling-panic-order/map-compound-index-key-vs-call` (BUG-104) | FAIL/differential → PASS/membership | {`` · `[5]`, `wit 5` · `[5]`} (E2d) | `wit 5` · `[5]` |
| `evalorder/unseq-ptr-field-map/{deref,field,mapread}-vs-call` | born PASS/membership | {1, 2} each (E2a/E2b/E2c) | 2 |
| `evalorder/unseq-ptr-field-map/{deref,field}-compound-redirect`, `map-compound-rebind` | born PASS/membership | {11100, 10101} each (E2e/E2h/E2f; hybrids absent) | 10101 |
| `evalorder/unseq-ptr-field-map/{field-private-vs-call,map-assign-plain-vs-call}` | born PASS strict | `wit 1` · 2; `wit 5` · 6 (legacy by the trigger — the controls) | = |
| `noodler/latitude/deref-vs-call` | PASS strict → PASS/membership | {11, 12} — `*p + f()`, f redirects p (E12's value axis on a deref) | 12 |
| `noodler/maps/compound-call-mutates` | PASS strict → PASS/membership | {15, 105} — the frozen map plan's load before / after `f` writes m[1] | 105 |
| `noodler/maps/compound-call-deletes` | PASS strict → PASS/membership | {(15, 1), (5, 1)} — the load before / after `f` deletes m[1] | (5, 1) |
| `pointers/deref-target-rhs-call-order` | PASS strict → PASS/membership | {92, 19} — `*p = swapP()`, the frozen pointer plan before / after the redirect (E2's value axis; the row's call-first pin enveloped) | 19 |
| `builtins/len-vs-call-order/len-nil-only-none` | PASS strict → PASS/membership | {10, 14} — the package-level `w4` read vs `wit4` inside the `&&` region (E12's value axis; the sweep entered through its field reads) | 14 |
| `builtins/e13-sibling-panic-order/{deref-left-call,deref-left-index-arg-call,map-key-assert-vs-len,map-tgt-assert-vs-call}` | PASS/membership, sets UNCHANGED (2 members each) | a first failure ends the run; `wit` sits after `len` by E1 | unchanged |
| `builtins/len-vs-call-order/{len-nil-only-left,-operand,-both,len-assert-vs-nil-operand,len-nil-left-vs-index-operand}` | PASS strict (unchanged) | the failing operand precedes the region / the call; identical nil panics | = |
| the 12 other rows whose sweeps entered (`imported-goose/semantics/{defer,maps}`, `maps/{compound-assign-eval-once,map-incdec}`, `noodler/evalorder/{map-index-before-rhs,elided-pointer-literal}`, `noodler/methods/method-expressions`, `noodler/misc/recursive-slice-struct`, `slices/slice-elided-high-eval-once/map-index-effectful-key`, `spec-examples-decl/{address-op-nil-indirection,conversion-parse-forms}`, `spec-examples-stmt/method-expr-five-forms`, `structs/selector-eval-once`) | unchanged | every edge forced, or reads no sibling call writes (wide picks within the fixed streams) | = |

MEASURED (`scripts/diff-one` on the 38 affected rows — the 27 sweeps' subject rows, the born package,
`imported-goose/semantics/{defer,maps}`; `diff-one-e2.txt`): EXACTLY the table — the flip, the five moves, the
eight births, the four E13 sets unchanged at 2 members, every other row unchanged. One correction of my own
pin, not of the set: `len-nil-only-none`'s first `width=2,sites=8` was REFUTED by the enumerator by name
(«site bound 3 exceeds the case's width 2» — the three reads `p.n`, `q.s`, `w4` are ready at once — then «run
consumes more than --max-sites 8»: the sweep's reads, `len`, guard, region call, ops and the `b2i` call make up
to ten wide picks per run); `width=3,sites=16` closes it with the same two members. **The full gate** (`scripts/capped scripts/ci --slow` at the
E2 tree under the box-wide lock, 02:45–03:02Z): EXIT=1 in 1018 s, K=80; 3717 rows 3473 PASS / 244 FAIL in the run =
the pin with the one 5a-class row red; RESULT FAIL on exactly the two 5a-class items (`certificate provenance`
STALE for `GoLean/GoCore/Machine.lean`; the drift line `imported-goose/channel/google-search` PASS→FAIL/membership,
fresh set unchanged); every other step ok — the evidence README §E2 and `ci-slow-e2.tail.txt`.

**Latitude.** E2's and E12's VALUE axis is (a) ENVELOPED on SEVEN more rows — the four lane moves
(`noodler/latitude/deref-vs-call`, `noodler/maps/compound-call-{mutates,deletes}`, `pointers/deref-target-rhs-
call-order` — the last was E2's own (b) call-first pin row) plus `builtins/len-vs-call-order/len-nil-only-none`
(a global read) and the born `evalorder/unseq-ptr-field-map/*` membership rows — posed for ratification at the
merge ask with the pilot's and E1's precedent; the entries stay (b) PINNED for the rest of their families
(receives, methods, multi-target forms, conversions/allocations — E3/E4/E5). BUG-104's map row is an
observed-∉-modeled FIX (the row moves to BUG-112's Cases line), not latitude.

**[AGENT] choices (alternatives named).** (i) A plan on ATOMS does not admit a sweep (pointer / field / map
targets): the alternative — counting every plan as the pilot counts a slice-element plan — would admit
`m[1] = wit(5)`, `*p = f()`, `s.f = g()` on private operands (hundreds of sweeps: the census's «assignment
target outside» reason alone is 2124) for singleton sets and one wide pick per sweep; the slice rule is
left as Stage C set it (consistency of the pilot's rows), recorded as an asymmetry to reconcile at E5. (ii)
An address-taken struct local's field read is FUSED into one `field-get` read (no struct-typed cell): the
alternative (a struct-valued read cell + a pure projection) spends a cell and a copy per read for the same
observation. (iii) The machine's map read reuses `mapLookupValue` (the comma-ok lookup) rather than a new
map-read helper: one lookup semantics, one `locSup` lemma. (iv) Map keys are int/bool/string only: an
interface-containing key needs `to-interface` boxing inside the plan (Stage C's boxing rule) and a defined
key type is E5's named-type family. (v) `e2fld` is native-only (no hand-built twin): the struct type's wire
name is an envelope fact; the pointer and map hand-built wires carry the frozen-identity claim.
