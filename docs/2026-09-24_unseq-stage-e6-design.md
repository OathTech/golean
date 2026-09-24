# Stage E6 of the evaluation-order model v2.1 — the design record, per slice (2026-09-24)

[AGENT] Lane `core/unseq-stage-e6a-0924` (worktree `.claude/worktrees/unseq-stage-e6a`), branch off main
`3fb4a0d1` (the window charter rev. 2 ruled). Dispatched by the [AGENT] coordinator under [USER] Mike's rulings
of 2026-09-22 (the Stage E5 landing record, `docs/2026-08-31_qrow-rulings.md`: item 1 the trigger refinement
ADOPTED, item 2 the grammar WIDENED to non-main units with the twin re-pinned, item 3 the decoder's R1
follow-up, item 6 the named refusal for an `after` edge on a literal `allocate`) and 2026-09-24 («I'm happy
to go with your rec» — the charter rev. 2 as the window of record, E6 dispatched starting with E6a, the split
E6a–E6e approved), relayed — cite as relayed. The window: `docs/2026-09-23_batched-window-charter.md` (row 1;
the slice table E6a–E6e; §6 what happens if a slice is refused). Design of record for the model:
`docs/2026-09-16_evaluation-order-model-v2.md` (v2.1); the families landed before this note:
`docs/2026-09-21_unseq-stage-e-design.md` (E1–E4; §E3 the observability trigger as ratified),
`docs/2026-09-22_unseq-stage-e5-design.md` (E5a–E5e; §0 the residue, §E5z the deferred axes). This note
records what EACH SLICE of E6 adds; §E6a is the first, the later slices add their sections. Everything below
is [AGENT] unless marked; every choice a ruling did not make is tagged and posed in the handoff
`docs/2026-09-24_unseq-stage-e6a-handoff.md` §2. Evidence `docs/evidence/2026-09-24_unseq-stage-e6a/`.

## 0. The slices and E6's exit, restated

E6 retires the legacy triple (`Stmt.unseqProbe`, `Cont.probeK`, `ChoiceSite.unseqPanic`) at a legacy
`unseq-probe` emission census of ZERO over the whole corpus AND the raft twin (RULED; the charter's F1: zero
by dropping / refusing a covered program, or by silently fixing one order where the spec permits two, is NOT
success — E6e needs a fresh census and behavioural-preservation evidence). The census this note measures is
the E5 handoff §3's: at the branch point **58 probes in 17 corpus packages + 128 in the twin**
(`probes-before.txt`; 108 258 corpus sweeps, 179 admitted, all in main units — `census-before.txt`).

| slice | class (the charter's census heads) | this note |
|---|---|---|
| **E6a** (this lane) | NON-MAIN units (twin 128, corpus 23) + PANIC-vs-PANIC pairs with no effectful event (21) + the two decoder follow-ups + the owed status-diverse row | §E6a — LANDED on the branch; **the classes do NOT reach zero** (§E6a «the census»): 11 of the 21 panic-vs-panic emitters close, 0 of the 151 non-main ones — the operative blockers of those 151 are the TYPE grammar, not the unit boundary (the residue table names each) |
| E6b | element / field addresses `&a[i]`, `&s.f` (3 + `generic-conversion`'s 1) | later |
| E6c | `recover()` inside a lifted body (2) | later |
| E6d | the nine singletons — and, after E6a, the residue below | later |
| E6e | the retirement at census ZERO (corpus + twin) | later; NOT reachable before the residue axes are dispositioned |

## E6a. The trigger refinement, the non-main-unit grammar, the decoder follow-ups, the status-diverse row (landed on the branch 2026-09-24)

### The trigger refinement (RULED [USER] 2026-09-22 item 1, executed here)

**The rule.** Stage E E3's observability trigger («a sweep enters the graph iff some occurrence is unordered
against an EFFECTFUL event» — `docs/2026-09-21_unseq-stage-e-design.md` §E3) is amended: a sweep enters the
`unseq` graph iff some occurrence is unordered against an EFFECTFUL event, **OR some FAILING occurrence is
unordered against an E1 participant's window that holds another FAILING occurrence or may itself fail**. The
observable is PANIC IDENTITY: spec#Order_of_evaluation orders «function calls, method calls, receive
operations, and binary logical operations» against each other and forces an operand only inside the call that
consumes it («except as required lexically»); the order of two run-time checks that are neither — a type
assertion (spec#Type_assertions) beside the bounds check of `make`'s size operand
(spec#Index_expressions, spec#Making_slices_maps_and_channels), an index beside a nil-checked field read —
is spec-open, and which of them panics first is observed in the abort line's text. gc realizes either member
(`docs/evidence/2026-09-05_e13-b/gc-realization.txt`: assertions EARLY, index / dereference operands LATE).
Without the refinement, retiring the legacy probe would NARROW the panic-vs-panic rows with no effectful
event (`iv.(int) + len(make([]int, t[k]))` and kin — `builtins/len-vs-call-order`,
`builtins/e13-sibling-panic-order`) from the two members the probe realizes to one: the ruling's purpose.

**What is FAILING.** The classifier (`tools/nativefrontend/unseq.go`, `unseqOccRec.failing`) marks: a
slice-element or string-byte checked access (bounds), a slice expression (bounds), a type assertion, a
division / remainder by a non-constant, a shift by a non-constant signed count (`unseqBinaryMayFail`), a
dereference `*p`, a field read through a pointer (`p.f`: nil check + load), the nil-asserting `&*p` and the
auto-dereference of a pointer receiver operand (E3's receiver sub-evaluations), the compound / IncDec LOAD
through a slice-element plan (bounds) or a deref / pointer-field plan (nil), the compound `/` `%` `<<` `>>`
themselves. NOT failing: an address-taken or package-level variable's read, a map read (the key is hash-safe
by the type grammar), a struct-variable field read, a guard, `string([]byte)`'s backing read, a callee
value's read, the comma-ok lookup, the target PLAN of a plain slice-element store (its bounds check is the
phase-2 store's — `targetPlan`, Machine.lean: «the chain's own checks are phase-2 store-time events»). One
PARTICIPANT may itself fail: `make` (its size check — `closePF(pid, false, name == "make")`); `new`,
`len`/`cap`, `min`/`max` and guards cannot; calls and receives are effectful already.

**What is UNORDERED.** Two non-event occurrences are ORDERED (`unseqDecision.ordered`) iff the later
consumes the earlier (the earlier lies inside the later's operand subtree — `unseqOccRec.first`), or the
earlier lies inside a participant whose completion index precedes the later's `lo` (the E1 chain orders
completions, and `lo` is one past the last participant the later consumes), or the earlier lies in a
guard's TEST and the later in that guard's REGION (`unseqOccRec.inTest`, the guard protocol). The record
keeps the whole chain of open participants per occurrence (Stage E kept the innermost only) so that the
completion rule sees every enclosing window. `observable()` then asks, for each failing occurrence `o` and
each participant `x` in its unordered window `[lo, hi)`: is `x` effectful (E3's rule), may `x` itself fail,
or does `x`'s window hold a failing occurrence unordered against `o`?

**The SCOPE — [AGENT] choice, POSED (handoff §2 item 1).** The ruling's words, «… OR against another
FAILING occurrence», admit two readings. (A) the GENERAL form: any two unordered failing occurrences, no
event between them — `a[i] + b[j]`, `x/y + s[i]`, `p.f + q.g` through pointers, BUG-032's `xs[ys[9]], b =
zs[7], 2`. (B) the EVENT-MEDIATED form above: the panic-identity pair across an E1 participant's window —
exactly the shape the legacy probe realized (a panicky operand beside a following event whose window holds
another panic, or which panics itself), plus its mirror (the failing operand RIGHT of such a window, as
Stage C retired E13's «right of the event» residual for calls). Measured, the general form admits **856
sweeps in 197 packages** (179 → 978 admitted; 57 in the raft twin; `strings` 132, `internal/strconv` 88,
`math/bits` 84, `unicode` 81, `internal/bytealg` 64, `bytes` 63 — hot library loops, each a graph with
`unseqNext` picks, each strict row of theirs a candidate for the depth guard's «wide picks served after the
stream was exhausted» red) — `docs/evidence/2026-09-24_unseq-stage-e6a/trigger-general-footprint.txt`. It
also moves the inventory's E3, E4 and E12 (the left-to-right order among non-call operands) from (b) PINNED
to (a) ENVELOPED as ENTRIES — «a new entry class as an ENTRY … is a HARD STOP — pose, do not take» (the
brief). E6a ships (B): it executes the ruling's purpose (the probe can retire without narrowing its rows),
touches only E13's axis (already (a) ENVELOPED), and admits **48 sweeps by the trigger**. (A) is posed with
its footprint; the legacy path keeps realizing the general form's one lexical order, as today. [The E6a audit
(2026-09-24, F4): (B) is a faithful SUBSET of the ruled wording — a narrowing of the ruling's literal scope by
[AGENT] choice, POSED as handoff §2 item 1 with that phrase. On every general-form probe the audit ran
(`a[i] + b[j]`, `x/y + s[i]`, `p.f + q.g` through pointers, `iv.(int) + s[i]`, the tuple `x, y = a[i], b[j]`,
two failing operands inside ONE `make` window) gc realizes the LEXICAL order 20/20, so NOT taking (A) creates
no new observed-∉-modeled; the ONE general-form shape where gc differs is BUG-032's own tuple `xs[ys[9]], b =
zs[7], 2` (gc `[7]`, the machine `[9]` on both sides — the inventory's E3 «(b) PINNED, known ≠ gc»), which (A)
would fix.]

**`len`/`cap` over map and channel operands — [AGENT] choice, POSED (handoff §2 item 2).** The census
BEFORE shows the panic-vs-panic rows were refused by the GRAMMAR, not the trigger: `len(make(map[int]int,
t[k]))` — «len of a non-slice operand (map[int]int)» (9 of the 15 `len-vs-call-order` emitters),
`cap(make(chan int, t[k]))` — «cap of a non-slice operand (chan int)». `len(m)` reads a map's entry count,
`len(ch)`/`cap(ch)` a channel's buffered count / capacity (spec#Length_and_capacity) — E1 participants that
cannot fail, spelled by the emitter as the same `builtin-len`/`builtin-cap` node the legacy path emits (the
decoder's D8 admits the head over an atom; the machine evaluates it on the legacy path today). `unseqCall`'s
`len`/`cap` arm admits the two operand kinds (5 + 1 sweeps enter by that reason). Alternative: leave them
refused — then 10 of the 21 emitters stay probes and E6a closes 1.

### Non-main units (RULED [USER] 2026-09-22 item 2, executed here)

**The boundary, and why it existed.** Three refusals in `unseq.go` confined the graph grammar to the main
unit: `unseqCallee`'s «callee outside the main package» (`isMainPackage(obj.Pkg())`), `unseqMethodCallee`'s
«method callee outside the main package», and its «qualified function callee (imported source package)» for
`pkg.F(...)`. They were Stage C's PILOT SCOPE (design §1: «a call to a same-package top-level function»),
carried through E1–E5 by name (the E5 handoff §3 «refuses by design») — not a semantic fact: the pilot fixed
one namespace (bare FuncIds of `main`) and left the identity questions of the other units (path-qualified
FuncIds, receiver-qualified method keys, the stdlib source-through library units with their reachability
pruning, substitutions and shim helpers) outside. The legacy path had all of them answered: `funcWireName`
(bare for main, `<path>.F` otherwise), `methodFuncKey` over `namedTypeName` (receiver-qualified), the
`emitQualifiedCall` static call.

**The generalization.** `unseqCallee` admits a top-level function of ANY source unit (`isSourcePackage`
— main, a case-local import, a library unit; the shim runtime-refusal helpers stay refused by name) and a
QUALIFIED callee `pkg.F` (a `*types.Func` of a source unit, non-generic, non-variadic; a func-typed package
VARIABLE `pkg.V(...)` refused by name — the legacy `call-value` shape); `unseqMethodCallee` admits a method
of any source unit's named struct. The lowering (`unseq_lower.go` `call`) gains the qualified arm —
`func-value{funcWireName(obj)}`, the very FuncId `emitQualifiedCall` emits; the method key was qualified
already. The census runs the classifier over every unit (`printUnseqCensus` iterates `e.units`); the
emitter classifies under each unit's `setUnit` (its own `types.Info`). Unit test:
`TestUnseqNonMainUnitsLower` (a `sub` package's `s[i] + Wit(5)` and main's `sub.G(s, 0) + s[i]` each one
graph, the callee `sub.G`). NO core change, NO decoder change, NO wire-schema change.

**What entered, and what did not.** 34 sweeps by «callee outside the main package», 3 by «method callee
outside the main package», 2 by «qualified function callee» — in `strings` (44 admitted sweeps in the
library unit — `Trim`, `*Reader.Len`, … across 26 corpus packages that import it), `bytes` (14), `wirepb`
(2, `multipkg/wire-codec`), and the twin: 7 sweeps (`bytes.Trim`, `bytes.(*Reader).Len`,
`strings.(*Reader).Len`, `strings.Trim`, `raftpb.(*Snapshot).SizeMessage`, `raft.isHardStateEqual`,
`raft.MustSync`), of which 3 reach the wire (reachability pruning drops the library ones) — the twin's THREE
born graphs. **The 151 non-main probe emitters are unchanged: 128 twin, 23 corpus** (22 once
`imported-goose/generics/generic-conversion`'s `index-addr` is counted under E6b, where the residue table below
files it — the audit's F4c). Every one is refused by
a reason the unit boundary never was: the twin's `field-get` probes sit on `raft.raft`, `raftpb.Message`,
`tracker.Progress`, `raft.raftLog`, `raft.unstable` — «field selector on a struct type outside the grammar»
(the struct carries an interface field — `Logger`, `Storage` — or a defined non-struct field type —
`StateType uint64`, `MessageType int32`) and «method receiver type outside the grammar (raft.raft)»;
`stdlib-source/errors-{join,wrap}`'s `binary` probes are interface comparisons (`err == nil` — «interface
comparison (may panic; outside the pilot)»); `strconv-parseuint` / `errors-wrap` / `frontier` / `noodler/
strings` / `strconv/format-parse` / `panic-recover/shim-refusal-unrecoverable`'s `Error` methods select on
library structs with an `error` field (`*strconv.NumError`); `frontier`'s `internal/strconv.pow10` indexes
an ARRAY, `slices.Insert[...]` is a generic stencil; `mini-raft-twin`'s 7 `field-get` probes read
`*mnode.Node` fields — the struct holds a `map[int]*mpb.Msg`-shaped member set outside the type grammar
(the census: «field selector on a struct type outside the grammar (mnode.Node)»); `generic-conversion`'s is
an `index-addr` (E6b). The twin's top legacy reasons after E6a (`census-e6a.txt`): «statement form outside
the pilot grammar» 3143, «no call occurrence» 2782, «no non-event occurrence» 638, `error` result types 385,
… «method receiver type outside the grammar (raft.raft)» 89, «field selector on a struct type outside the
grammar (raftpb.Message)» 85, «(raft.raft)» 71, «(bytes.Buffer)» 62, «(tracker.Progress)» 44. These are E5z's
deferred axes — interface / defined-non-struct FIELD TYPES in an otherwise admitted struct, interface
comparison, library-typed receivers, arrays as index bases, generic stencils — none of them E6a's to widen
(the brief: «do not widen the grammar beyond E6a's classes to reduce the census»). The charter's E6a exit
(«non-main 151 → 0») was mis-attributed at the E5 census: the FIRST refusal reason the census prints for a
sweep was the unit boundary, and the type-grammar refusals behind it were not visible until the boundary
fell. E6d/E6e must plan for them (handoff §3).

**The twin re-pin** (`scripts/check-frontend-pins`, `baselines/pins/twin-chdriver.wire.json` e1a87725… →
1c4e7038…; the reason in the script's header; `twin-structural-diff.txt`): the SOLE structural change is
the three born graphs — `raft.isHardStateEqual` (`a.GetTerm() == b.GetTerm() && …`: the raftpb getters have
POINTER receivers, so `a` and `b` are ATOMS; the graph's occurrences are six `invoke`s, three pure `binary`s
and two GUARDS with their joins — NO failing occurrence), `raft.MustSync` (the same shape over `||`),
`raftpb.(*Snapshot).SizeMessage` (`n += 1 + plainpbSizeVarint(uint64(len(x.Data))) + len(x.Data)`: the
nil-checked `x.Data` reads beside the effectful FUNCTION call `plainpbSizeVarint`). All three enter through
the generalized UNIT BOUNDARY under Stage E's E3 rule (a guard whose window is followed by an effectful call;
a nil-checked field read beside a call) — NONE by the E6a trigger refinement; the audit's main-unit replicas
of the shapes are admitted by MAIN's frontend too. [CORRECTED at the audit fix round, 2026-09-24, the audit's
F3: this paragraph, the pin script's header, the handoff and the changelog lines first described «the
HardState getters' nil-checked field reads unordered against each other across the `&&` chain's E1 windows»
and «a compound whose nil-checked field read is unordered against the sibling method call» — wrong on both
counts.] 0 funcs / methods / types / globals / methodSets added or removed, `fileOrder` identical, the 128
`unseq-probe` statements unchanged; every other changed entry differs only by program-wide temporary
renumbering (`$uN` cells consume the counter). The born graphs are ALL-FORCED (every occurrence an E1-ordered
call, a pure op or a guard), so their sets are singletons on EVERY state and the twin's observations are
unchanged — a structural argument (reproduced by the audit on its p5 replicas: one observation on both sides,
gc =), not the «getters cannot fail on non-nil states» argument first written; the twin driver under the
machine was not re-run (40–65 min); the corpus twin rows (`multipkg/mini-raft-twin/*`) reproduce their pinned
states.

### The two decoder follow-ups (RULED [USER] 2026-09-22 items 6 and 3; `GoLean/NativeToIR.lean`, trust surface #1)

**F8 — an `after` edge on a literal allocation is refused by name.** In the `allocate` arm, after the spec
decodes: a `slice-lit`, a `map-lit`, or a `new` whose value is a `struct-lit` (`&T{…}`) carrying a non-empty
`after` list fails «an `after` edge on a literal allocation ({tag}) — a composite literal is not an E1
participant (v2.1 R3), so the lowering never orders it behind an event; the edge would narrow the set by a
policy the wire cannot express». `make` / `new(T)` / `new(x)` are E1 participants and keep their anchor. The
lowering emits no `after` on a literal (`allocOcc(…, event=false)`); a hand-built or forged wire could
(the Stage E audit's F8, the E5 audit fix round's mA5 on the `map-lit` arm). Mutant
`mut-alloc-literal-after` (e4alloc's slice literal anchored behind `wit5`'s call).

**R1 — every source-local atom's `type` annotation is checked against its declaration.** Stage C's D9
trusted a source-local atom's annotation — the wire's word, not the decoder's knowledge; the E5 audit
re-verification's mS1 / mS4 forged an annotation together with a `map-lookup`'s / `map` target plan's
`keyType` on a PRIVATE map base and the wire decoded and ANSWERED (audit F1's base check compares against the
annotation). Now `LowerCtx` carries `locals : Array Param` — the enclosing function's params, results and
every local its body DECLARES, collected by `jsonDeclaredLocals` (a whole-body walk over the wire's own
declaration spellings: every `{"target":"declare","id","type"}` target — assignment lhs, the allocation /
built-in / sync / type-assert / chan-recv targets, the emitter's one target shape; every `var` statement's
`decls`; a `range` statement's implicitly declared key / value variables, typed as `decodeRange` types
them) — set by `withReader` in `decodeFunc` and `decodeMethod` around the body decode. `decodeUnseq` walks
the WHOLE node after the cells decode (`unseqCheckLocalAtoms`): an `ident` whose name is not a reserved `$`
slot and not one of the graph's own cells must be declared («has no declaration in the enclosing
function»), and its `type` annotation, when present, must be that declaration's («is annotated …, which
disagrees with its declaration …»); a `ref` of a source local must be declared. **The environment is
SCOPE-EXACT since the audit fix round (2026-09-24, the audit's F2).** At the tip the table was FLAT — the
whole body's declarations, a name checked against the SET of every type declared under it — and the residual
stated was «a name Go's block scoping declares TWICE with DIFFERENT types in one function»; the audit showed
its true reach: the emitter spells a TYPE-SWITCH clause binder PER CLAUSE with the clause's type (`declare v
: map[int]int` in one clause body, `declare v : map[string]int` in the other — ONE source declaration, a
common idiom), so the flat table held both, and the audit's `mS1-via-typeswitch-binder` (the int-map clause's
`v` annotated, its `map-get` head keyType'd and keyed as the OTHER clause's map) DECODED AND ANSWERED 1 — the
E5 audit's F1 class one layer down. The fix, taken (no wire-schema change: the wire's block structure and its
in-order declaration spellings carry the scope already): `LowerCtx.locals` is the set of declarations IN
SCOPE at the statement being decoded — `decodeStmt`'s `block` arm folds it statement by statement (each
statement decodes under the declarations BEFORE it; its own join the environment for the statements after
it — Go: a variable's scope begins at the END of its declaration, so a statement never sees its own),
`jsonDeclaredLocals` no longer descends into a block-scoping statement's nested bodies (`nestedStmtKeys`:
`block`/`breakable`/`labeled` body, `if` init/then/else, `for` init/post/condPre/body, `range` body, `select`
clauses/default — the `unseq` node with its `then` and allocation bodies is ONE declaration site, walked
whole), `decodeIf` / `decodeFor` extend the environment with their `init`'s declarations (looking through a
wrapping block) for the condition, the branches, the body and the post, `decodeRange` with its key / value
variables for the body, the `select` arm with each receive clause's targets for THAT clause's body, and
`decodeFunc` / `decodeMethod` open it with the params and results only; `unseqCheckLocalAtoms` resolves an
atom to the LAST entry of its name — the INNERMOST declaration in scope (a shadowing redeclaration, a
per-clause binder, a per-iteration loop-variable copy sit after what they shadow) — and checks the
annotation against that one type. The auditor's mutant, the legal-shadowing positive control and the
type-switch positive control are tracked: NATIVE witnesses `e6ats` (`switch v := iv.(type) { case
map[int]int: r = v[1] + wit(1); case map[string]int: r = v["a"] + wit(2) }` → {1 · `wit 1`}) and `e6ashadow`
(`x := 0; …; r := s[x] + wit(1); { x := "ab"; r += int(x[1]) + wit(2) }; z := 0` → {108 · `wit 1` `wit 2`});
mutants `mut-local-annotation-shadowed` (the audit's mS1 edit on `e6ats`), `mut-local-shadow-other-decl`
(the inner string `x` annotated with the OUTER declaration's int — the residual the tip stated, now refused),
`mut-local-out-of-scope` (the outer graph names `z`, declared only LATER in the block — in the function, not
in scope). The audit's own forged files (`mS1-via-typeswitch-binder`, `mR1-typeswitch-binder`,
`mR1-shadow-other-decl-type`) refuse by name under the fix-round binary; its legal p4 wire decodes and runs as
before (`docs/evidence/2026-09-24_unseq-stage-e6a/fix-round/mutants-fix.txt`); the pinned raft twin wire and
every corpus wire decode (the differential gate; the whole-corpus choice trace byte-identical outside the born
rows). WHAT REMAINS OUTSIDE R1 (stated, not a residual of the environment): the emitter's `$`-temps and the
graph's own cells (D2's reservation, not R1's); a store TARGET's id — not an atom — which R1 does not see
(the audit's F7, a NAMED LATE REFUSAL of the standing class the Stage E and E5 audits recorded: `mR1-target-
id-undeclared` renames a `then` store's `{"target":"var","id":…}` to an undeclared name, and the machine
sticks by name «expected array, slice, or string value for index access, got int 0» — closed late, not an
answer; a declared-id check on store targets is optional and not taken). Mutants
`mut-local-annotation-forged` (e5blookup: the annotation, its cell and the lookup's `keyType` all say
`map[string]int` on a `map[int]int` local — D9 and audit F1's base check pass, only the declaration says
otherwise), `mut-local-undeclared` (e5daddr's `read1` names an undeclared `y`). Two existing mutants met the
new check first and were re-pointed to keep their needles: `mut-nondollar` (a cell named `u1` — a cell id is
D2's business, so the walk skips the graph's own cell ids) and `mut-guard-type` (its edit re-annotated the
source local `z` as int; the edit now forges the test CELL's type and feeds it a constant head, so D11 is
reached). 49 → 52 mutants (`Tests/unseq-wire/mutants.tsv`, `scripts/check-unseq-wire`,
`scripts/check-wire-boundary` 11 + 52 controls); every positive control unchanged. The audit fix round: 52 →
55 mutants, 11 + 55 controls, the two NATIVE witnesses above (`Tests/UnseqWire.lean` exact sets).

### The owed status-diverse manifest row (the E5 audit fix round's F4; trusted surface #2)

**The finding.** The E5 records (design §E5e, its F4, the handoff §3/§6, the inventory's E13 bullet, the
ledger's E5e bullet) said the CLI's `coverage-observations --expect-status ok,panic` path was UNREACHABLE
from a row because `scripts/diff-coverage:629` admits one `expected_status`. That was wrong: the status set
rides the membership lane's `params` column — `statuses=ok+panic` (`scripts/coverage-manifest` validates
it; `scripts/diff-coverage` `parse_lane_params` routes it to `--expect-status ok,panic` and
`member_status_allowed` widens the Go-sample check) — the BUG-044 / audit-F8 mechanism landed 2026-08-08, in
use on `binop-order/operand-panic-vs-call/{call-before-left,call-before-left-div}` and
`goroutines/wake-window`. The `expected_status` column pins gc's default-stream member (and its
`expected_reason`), the set declares the others. So the apparatus is NOT changed ([AGENT] choice: a second
spelling of the same set in the `expected_status` column would be a duplicate mechanism); the E5 records
carry a dated correction each; `scripts/test-lane-validation` gains the fail-closed shapes the brief named —
an EMPTY set (`statuses=`), a set on a STRICT row (the strict lane's «may only declare depth=» rule), a
status word outside {ok, panic} (`ok+deadlock` — deadlock is strict-only) — and the accepting shape of the
born row (a panic-pinned membership row with `statuses=ok+panic`).

**The row.** `evalorder/unseq-strings/str-index-status-diverse` (`strIndexStatusDiverse`: `int(s[i]) + m()`,
s = "ab", i captured, m: i = 9) — before m 'a' + 5 = 102 (ok), after m the bounds check fails, `index out of
range [9] with length 2` (panic; gc's member 20/20 under GOMAXPROCS 1/8, default and `-N -l`) —
PASS/membership {102, panic}, `width=2,sites=8,members=2,statuses=ok+panic`, expected_status panic with the
reason. The first status-diverse `unseq` row; E5e's two split rows stay (they are correct rows of their own
shapes).

### The census (the E6 exit is measured per slice)

Whole-sweep (`census-before.txt`, `census-e6a.txt`, `census-newly-admitted-e6a.tsv`): 108 258 corpus sweeps;
admitted **179 → 265** (+86 corpus in 41 packages + 7 twin = 93 newly admitted; 0 lost) — by former reason
«no call occurrence» 48 (the refined trigger), «callee outside the main package» 34, «len of a non-slice
operand (map)» 5, «method callee outside the main package» 3, «qualified function callee» 2, «cap of a
non-slice operand (chan)» 1; by form `return` 88, `compound` 3, `elem-assign` 1, `define` 1; admitted units
`main` 205, `strings` 44, `bytes` 14, `wirepb` 2. The twin 10 203 sweeps: 0 → 7 admitted, 3 reach the wire.
[The audit's F5 (2026-09-24): these figures were taken on the working tree BEFORE `str-index-status-diverse`
existed; at the tip `1f0dee94` both frontends admit its sweep — 108 264 sweeps, **180 → 266** (the 93 newly
admitted identical BY NAME; the audit's `census-repro.txt`). At the audit fix round's tree (the seven BUG-116
rows born in `e13-sibling-panic-order`): 108 294 sweeps, **180 → 273** (100 newly admitted = the 93 + the
seven born rows' sweeps; 0 lost; `main` 213, `strings` 44, `bytes` 14, `wirepb` 2); legacy probes corpus 58
→ 47, the twin 128 → 128 with 3 graphs — `docs/evidence/2026-09-24_unseq-stage-e6a/fix-round/census-fix.txt`.]

Legacy probe emission (`probes-before.txt`, `probes-e6a.txt`): **corpus 58 → 47** (17 → 17 packages;
`builtins/len-vs-call-order` 15 → 6, `builtins/e13-sibling-panic-order` 11 → 9, every other package
unchanged), **the twin 128 → 128**; total 186 → 175. The residue, by class, with each emitter's blocking
reason (the handoff §3 carries the same table for E6b–E6e):

| class | count | emitters (probed head) and the reason each stays |
|---|---|---|
| E6b — element / field addresses | 4 | e13 `addrIndexLeftLenHoist`, `addrAssertLeftCall`, `arrayBaseTargetVsLen` (`index-addr`); `imported-goose/generics/generic-conversion` `genericConversions` (`index-addr`) — «unary operator & on an element (&a[i])», an array base |
| E6c — `recover()` in a lifted body | 2 | e13 `recoverAssertVsLen$lit0`, `recoverAssertVsCallW$lit2` (`type-assert`) — «builtin recover statement» / a captured target in the lifted body |
| E6d — the nine singletons | 9 | `channels/recv-edge` `recvNilIndexBaseSecond$lit0` (`deref`), `channels/recv-map-elem` `mapKeyPanicDrains$lit0` (`index-get`), `fmt/sprintf-dyn` `Infof` (`field-get`), `noodler/frontier2/array-of-funcs-indexed-call` (`index-get`, array base), `noodler/frontier2/typed-nil-error-return` (`binary`, interface comparison), `noodler/misc` `copyIntoArrayView` (`slice`, array), `noodler/strings`, `panic-recover/shim-refusal-unrecoverable`, `strconv/format-parse` — each an `Error` method (`field-get`, a library struct with an `error` field) |
| NON-MAIN units — unchanged by the boundary's fall | 22 corpus + 128 twin (`generic-conversion` counted ONCE, under E6b — the audit's F4c; 4 + 2 + 9 + 22 + 128 + 10 = 175) | `mini-raft-twin` 7 (`field-get` on `*mnode.Node`: a struct type outside the grammar); `stdlib-source/errors-join` 5 and `errors-wrap` 2 `binary` (interface comparison `err == nil`); `strconv-parseuint` 3 + 1, `errors-wrap` 1, `frontier` 1 `field-get` (library structs with an `error` field: `*strconv.NumError`; the `Error` methods); `frontier` `internal/strconv.pow10` (`index-get`, an array), `slices.Insert[[]int,int]` (`slice`, a generic stencil); the twin's 128 `field-get` (`raft.stepLeader` 29, `raft.Step` 23, `stepCandidate`/`stepFollower`/`handleAppendEntries` 6 each, …) — every one «field selector on a struct type outside the grammar» (`raft.raft`, `raftpb.Message`, `tracker.Progress`, `raft.raftLog`, `raft.unstable`: interface / defined-non-struct fields) or «method receiver type outside the grammar (raft.raft)» |
| PANIC-vs-PANIC — the residue after the refinement | 10 | `len-vs-call-order` `makeHintStructAnyKey`, `makeHintArrayAnyKey`, `lenStructAnyKeyLeftAssert` (an interface-CONTAINING map key — «map type outside the grammar»: a hash-panicking map read, E2 admits hash-safe keys only), `lexerIdiom` (`for l.pos < len(l.src) && l.peek() != '\n'` — a `for` CONDITION is a sub-accumulator sweep the whole-sweep grammar never visits), `makeHintGenericKey[interface {}]` and `[int]` (a generic stencil: the classifier reads a local's type unsubstituted — `map[K]int` — «local of a type outside the pilot grammar»); e13 `convLeftCall` (a slice-to-array conversion — «index of a non-slice base ([2]int)»), `ifaceCmpLeftCall` (an interface comparison), `sendChanIndex` (a SEND statement — «statement form outside the pilot grammar»), `assertReturnList$lit0` (a captured read inside a lifted body) |

Every remaining emitter is a GRAMMAR axis (E5z's list: interface / defined-non-struct field types, interface
comparison, arrays as index bases and array literals, generic stencils, sub-accumulator sweeps, send
statements, captured reads in lifted bodies, slice-to-array conversion) — none E6a's, none reached by a
trigger change. The 11 closed: `hintPanickyBetween`, `makeSlicePanickyBetween`, `makeChanCapPanickyBetween`,
`makeIndexLeft`, `makeInnerLen`, `makeHintPanicFree`, `makeHintMapRead`, `makeHintCall`, `makeNilOnly`
(`len-vs-call-order`, 9), `assertLeftMakeSlice`, `tgtAssertVsMake` (e13, 2).

### Rows

`scripts/diff-one` on all **395** rows of the 41 packages whose sweeps entered + the born row's package
(`diff-one-e6a.txt`): **392 UNCHANGED** (result and stage as pinned — including the 14 rows that leave the
probe for the graph, whose sets are reproduced, and the `strings`/`bytes` library-unit rows), **1 BORN**,
**2 strict rows RED-FIRST** (FAIL/differential: the machine's canonical tape realized the other spec-legal
panic) and MOVED to membership with the reason written (E5c's F6 precedent; gc's draws `gc-draws-e6a.txt`,
`gc-draws-e6a-moves.txt`, 20 per subject under GOMAXPROCS 1/8, default and `-N -l`):

| row | before → after | set | gc |
|---|---|---|---|
| `evalorder/unseq-strings/str-index-status-diverse` | born PASS/membership (`statuses=ok+panic`) | {102 ok, panic `[9] with length 2`} | the panic (20/20) |
| `builtins/e13-sibling-panic-order/assert-left-min-inline` | PASS strict → PASS/membership (red-first) | {conversion, `[5] with length 2`} — `iv.(int) + min(t[k], 1)`: the assertion vs `t[k]` inside min's window | the conversion (20/20) |
| `channels/recv-order/dead-recv-len-operand` | PASS strict → PASS/membership (red-first; BUG-032's Cases line, amended) | {conversion, `[7] with length 0`} — `iv.(int) + len(b[j])` | the conversion (20/20) |
| `builtins/len-vs-call-order/{hint-panicky-between, make-slice-panicky-between, make-chan-cap-panicky-between, make-index-left, make-inner-len}` | PASS/membership, probe → graph, sets UNCHANGED (2 each) | RAISE the conversion / DEFER the size operand's panic | unchanged (the early member; `make-index-left` the index `[5]`) |
| `builtins/len-vs-call-order/{make-hint-panic-free, make-hint-map-read, make-hint-call, make-nil-only-none/-left/-operand/-both}` | PASS strict, probe → graph, UNCHANGED | singletons (one panic text on every order; the nil-deref rows two identical texts) | = |
| `builtins/e13-sibling-panic-order/{assert-left-make-slice, tgt-assert-vs-make}` | PASS/membership, probe → graph, sets UNCHANGED | the conversion vs the size operand's `[5]` | unchanged |
| the other 375 rows of the 41 packages (`strings/*`, `bytes/*`, `stdlib-source/*`, `fmt/*`, `init/*`, `multipkg/wire-codec`, …) | UNCHANGED | the newly admitted library-unit sweeps read what no sibling event writes (the same observation on every pick) or are strict rows with the same result | = |

Baseline `3760 = 3524 / 236 → 3761 = 3525 / 236` (+1 born; 2 strict → membership; the header carries the
reason). NO PASS → non-PASS.

**The audit fix round (2026-09-24, the audit's F1 — BUG-116).** The two moved rows are the ASSERTION-LEFT
members of a class whose other members were WRONG ANSWERS on main, which the refined trigger fixed
SILENTLY: a LATE-realized failing NON-CALL operand — an index, a slice expression, a dereference, a
pointer-field read, a division, a shift, a compound target's LOAD — LEFT of an inline built-in E1 participant
(`len` / `cap` / `min` / `max`) whose own operand panics, CALL-FREE. On main every such sweep is a legacy
lexical singleton holding the LEFT operand's panic; gc realizes the BUILT-IN's OPERAND's panic on all fifteen
shapes the audit probed (20/20 each) — observed ∉ modeled, undetected because every earlier E13 row of the
form carried a trailing `wit(5)` (a graph since Stage E). Only for a type ASSERTION on the left does gc
happen to agree with the lexical order (assertions are EARLY in gc) — the two moved rows; BUG-032's A6
sentence «len stays inline and realizes gc's left-to-right point» is corrected there with a pointer to
BUG-116. SEVEN rows BORN in `builtins/e13-sibling-panic-order`, one per operand class, from the audit's
litmuses: `idx-left-vs-min-operand` (`s[i] + min(t[k], 1)` {`[9] with length 1`, `[5] with length 2`}),
`idx-left-vs-len-slice-expr` (`s[i] + len(t[k:])` {`[9]`, `slice bounds [5:2]`}), `deref-left-vs-len-operand`
(`*p + len(b[j])` {nil dereference, `[5] with length 1`}), `ptr-field-left-vs-len-operand` (`q.x + len(b[j])`
{nil dereference, `[5]`}), `div-left-vs-len-operand` (`x/y + len(b[j])` {`integer divide by zero`, `[5]`}),
`shift-left-vs-len-operand` (`x<<s + len(b[j])` {`negative shift amount`, `[5]`}),
`compound-load-vs-len-operand` (`x[9] += len(b[j])` {`[9]`, `[5]`}) — each PASS/membership on the candidate
(`scripts/diff-one`: enumerated=2, gc's draw inside — gc the built-in's operand's panic 20/20 under
GOMAXPROCS 1/8, default and `-N -l`), each RED-FIRST on main `3fb4a0d1`'s frontend + binary (a `git archive`
tree with the primary's build artifacts): as the born membership rows FAIL/membership («enumerated observation
set is a singleton (1 member)» — main's machine offers ONE member), as strict twins of the same subjects
FAIL/differential (Lean the left panic ≠ Go the built-in's operand's) — `docs/evidence/2026-09-24_unseq-
stage-e6a/fix-round/{diff-one-fix,diff-one-main-red-first,diff-one-main-strict,gc-draws-fix}.txt`. Baseline
`3761 = 3525 / 236 → 3768 = 3532 / 236` (+7 born; the header carries the reason). The main-side PASS →
non-PASS is NOT a flip of a tracked row — no tracked row had the call-free shape; the seven are born here.
Latitude: E13's axis, (a) ENVELOPED — no entry moves; the inventory's E13 entry gains the fix-round bullet.

**Latitude.** The two moved rows and the fourteen moved probe rows are E13's axis ((a) ENVELOPED since
2026-09-05) — no entry moves; the inventory's E13 entry gains the E6a bullet; E3/E4 and E12 gain a bullet
stating the general rule is POSED (handoff §2 item 1). The born row is E5e's axis (E2/E12's VALUE axis on a
string base, (a) ENVELOPED on E5e's named rows — RATIFIED 2026-09-22 item 5) with its STATUS observable.

### Gates and the trace

Standalone (captured exits, `gate-exits-e6a.txt`): `go test ./tools/nativefrontend/ ./tools/lowerdiag/` ok; `check-unseq-wire`
PASS (52 mutants; `Tests/UnseqWire.lean` exact sets); `check-wire-boundary` PASS (11 + 52); `check-mem-callsites` PASS;
`check-core-audit` PASS; `scripts/capped check-unseq-scheduler` PASS; `check-frontend-pins` PASS (the twin re-pinned);
`check-bugs` ok; `check-evidence-size`, `check-spec-anchors`, `check-agents-alias`, `test-lane-validation` PASS. The C1 gate
(`GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff` at the frontend + twin + rows + baseline tree, the decoder / wire files
stashed; the box-wide lock 02:18:22Z–02:32:53Z): EXIT=1 in 871 s; `cases=3761 pass=3524 fail=237` = the pin 3525 / 236 with the
one 5a-class row red; RESULT FAIL on EXACTLY the two 5a-class items — `certificate provenance` (STALE: changed dependency
`scripts/check-frontend-pins`) and the `baseline diff` DRIFT block's one line (`imported-goose/channel/google-search`); every
other step ok (`ci-diff-c1.tail.txt`). The C2 gate (`ci --slow` at the decoder + wires tree): `ci --slow` EXIT=1 in 1097 s (the lock 02:34:54Z–02:53:11Z); cases=3761 pass=3523 fail=238; RESULT FAIL on `certificate provenance` (STALE for `scripts/check-frontend-pins`) and `baseline diff` with TWO drift lines — the 5a-class `google-search` line and `race/negative/struct-tag-alias-field` PASS/racy → FAIL/go-observation, an ORACLE-side sample (`go run -race` stayed green under the box's load — the racy lane's three-way rule, case (b); the row's package untouched by E6a; re-run alone it PASSes, cases=1 pass=1); every other step ok (`ci-slow-c2.tail.txt`); the tip's `--slow` re-run is the park gate (`ci-slow-tip.tail.txt`). The tip's `ci --slow` after the records commit: `ci --slow` at the tip `e453bb38` (the tree CLEAN): EXIT=1 in 899 s (the lock 02:56:19Z–03:11:18Z); cases=3761 pass=3524 fail=237 = the pin 3525 / 236 with the one 5a-class row red; RESULT FAIL on EXACTLY the two 5a-class items — `certificate provenance` (STALE: changed dependency `GoLean/NativeToIR.lean`) and the `baseline diff` DRIFT block's ONE line (`imported-goose/channel/google-search`); the C2 run's racy sample did not recur; every other step ok (`ci-slow-tip.tail.txt`).

**The whole-corpus choice trace** — `docs/evidence/2026-09-24_unseq-stage-e6a/choice-trace-main-vs-e6a.txt`: main `3fb4a0d1`'s binary (`63e9c661…`, the E5 fix round's = main's sources; main's frontend from a `git archive main` export) vs the E6a tip's binary and frontend, `scripts/choice-trace-corpus --dump --jobs 4` per side (the two standing spin exclusions `goroutines/send-then-spin` and `strings/trimspace-repeat/repeat-bound-refused` traced by no side; the rows the wrapper had not reached traced by a direct `golean choice-trace --batch` per side — the wrapper's summary step did not run), Stage D's `trace-compare.py`: **3725 ids, 3694 byte-identical, 30 DIFFER, 0 ONLY_A, 1 ONLY_B** (the born row). EVERY differing id lies in a package whose sweeps entered the grammar — the 14 probe → graph rows (`unseqPanic` 6 → 0, `unseqNext` 0 → 6/9/11), the 2 moved rows (`unseqNext` 0 → 6), and 14 rows whose newly admitted sweeps add `unseqNext` picks with one observation (`functions/untyped-nil-sinks/slice-lit-elem`, `interfaces/tuple-forward-boxing/{fixed-any, interface-source-control, variadic-any}`, `multipkg/wire-codec/size`, `new/new-slice-pointer`, `noodler/bounds/slice-within-cap`, `noodler/builtins/cap-after-slicing`, `noodler/indexkinds/slice-bounds-kinds`, `slices/append-spill-below-formula`, `stdlib-source/{binary-order/be-roundtrip, builder-overlay/repeat-doubling-loop, strconv-format/siblings, strings-split/empty-sep-invalid-utf8}`); the one non-`unseq` site movement — `multipkg/wire-codec/size` `appendSpill` 21 → 19 — is the finite fixed streams' knock-on (the new picks shift the slots the later spill picks read; the observation unchanged). Site census: `unseqNext` 2147 → 2550, `unseqPanic` 168 → 96, `appendSpill` 4874 → 4872, every other site identical; 34 export refusals each, identical sets.

### The audit fix round (2026-09-24)

The adversarial audit of the candidate `1f0dee94` (`docs/2026-09-24_unseq-stage-e6a-audit.md`, branch
`review/unseq-stage-e6a-0924` @ `300f0e74`; evidence `docs/evidence/2026-09-24_unseq-stage-e6a-audit/`)
returned FIX-FIRST (records, small): no wrong answer and no over-wide set on the candidate; F1 a main-side
WRONG-ANSWER class the candidate fixed silently (rowed above, BUG-116); F2 the R1 flat table reaching
type-switch binders (a minor FAIL-OPEN on forged wires; the scope-exact environment built above); F3 the
twin's three born graphs mis-described (corrected above, in the pin script's header, the handoff and the
changelog lines); F4 the trigger a faithful SUBSET of the ruled wording (posed with that phrase), the
charter's «21 with no effectful event» mis-labelling 7 emitters that contain calls (a dated correction line
appended to the charter), `generic-conversion` counted twice (once now); F5–F7 nits (the census figures at
the tip and at this tree, the changelog pointer, the late-named store-target forgery). The dispositions are
the [AGENT] coordinator's, disclosed at the merge ask, under the [USER]'s standing direction that every merge
is audited and its findings fixed before landing; executed by the [AGENT] worker; the per-finding table with
witnesses is the handoff §5. Trust surface #1 changed (the decoder's R1 environment — refuses forged wires
only); the frontend, the core and the wire schema did not. Gates and the trace: the handoff §5 (the fix
round's gate line and the trace summary vs the audited tip).

### [AGENT] choices (alternatives named) — each posed in the handoff §2

(i) The trigger's SCOPE: the event-mediated form shipped, the general form posed with its footprint
(above). (ii) `len`/`cap` over map / channel operands admitted (above; the alternative leaves 10 of the 21
emitters probed). (iii) The unit boundary generalized to EVERY source unit at once — main, case-local
imports, library units — rather than case-local imports only: the twin (the ruled re-pin) is a case-local
import set, but the stdlib-source rows are the same grammar on the same wire spellings, and a boundary at
«library units» would be a second pilot scope with no semantic ground. (iv) The R1 check as a flat
per-function declaration table at the tip (the scope-exact alternative not built there; the shadow residual
stated) — SUPERSEDED at the audit fix round: the audit's F2 showed the residual reaching type-switch clause
binders, and the scope-exact environment was BUILT (above; the alternative taken).
(v) The status set reused from `params` (above; a second spelling in `expected_status` not built). (vi) The
two red-first strict rows moved to membership (the F6 rule) rather than the graph narrowed to gc's member
(a (b) pin the doctrine forbids) or the rows left red (a wrong answer they are not — both members are
spec-legal panics). (vii) `mut-guard-type` re-pointed rather than dropped (its purpose — D11 — stands).
