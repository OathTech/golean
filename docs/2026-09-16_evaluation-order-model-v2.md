# The evaluation-order model v2.1 — the `unseq` construct in the core (2026-09-16)

[AGENT] Design note, lane `design/eval-order-model-v2-0916`, at main `433e7490`; records only. REVIEWED VERSION: v2 @
`9a8ed328` (never merged; amended in place). Second Codex review `docs/2026-09-16_evaluation-order-model-v2-review.md`
(`review/eval-order-model-v2-0916` @ `b788e582`; evidence `docs/evidence/2026-09-16_eval-order-v2-review/`, `check.py`)
— «Keep the graph architecture; revise the first implementation slice»: its R1–R6 and §2–§5 are applied below, marked
where they changed; this note is its Stage A and the implementation handoff (§7, §9). It implements as a design the
ruling of [USER] Mike, 2026-09-16, verbatim, relayed by the [AGENT] coordinator — cite as relayed: «Okay, so this feels
like sort of a profound decision, but I think the Cerberus model is the correct one (they did a lot of work thinking
through such issues). Can you go ahead with the next steps?» (record: `docs/2026-08-31_qrow-rulings.md`, «The
evaluation-order mechanism ruling record (2026-09-16)»; sequence: `docs/2026-09-11_review-dispositions.md` §4 step 4).
The v1 note (`design/eval-order-model-0915` @ `90dc66f0`, unmerged) keeps its §1 relation and doctrine rule
(spec-ordered → structural ANF in the frontend; spec-unordered with an observable → a tape choice; the rest refuses by
name); its endpoint probe-and-use mechanism is RETIRED. First review: `docs/2026-09-15_evaluation-order-model-review.md`
(F1–F9). The mechanism is decided; nothing here re-opens it. Rulings are [USER] verbatim-as-relayed or PENDING [USER];
everything else is [AGENT]. Code anchors verified at `433e7490`.

## 1. The relation, re-founded: a dependency graph over evaluation occurrences

**Sweep.** One statement's evaluation phase (a block statement, or a sub-accumulator: if/for init·cond·post, switch tag,
case values, range operand, per-spec var initializer — e13-b §1). Its OCCURRENCE GRAPH is (occurrences, value
dependencies, order prerequisites, guarded regions).

**Occurrences** (kinds, heads and contracts: §3.1, R3) — each produces zero, one or many results into predeclared
BINDERS, may fail, may change state: INVOCATION/RECEIVE (after callee value and arguments; comma-ok receive = ONE
occurrence, two outputs; `panic print println delete close clear` are their statement's event); READ (one evaluation of
a mutable location at that instant; an element `a[i]` is a base/header PRODUCER and an index producer, then ONE checked
access on those values — R6, the machine's own `strictPlan (.indexGet b i)` / `applyStrictOp .indexGet [b, i]` split,
`GoLean/GoCore/Machine.lean:183`, `:439`; §5 N1); PURE OP (on produced values; fails on its own account);
ALLOCATION/CONVERSION (its operands' reads are the occurrences; the allocation itself unobservable, C11, NO E1 edges —
R3); TARGET PLAN (a target's identity from FROZEN operand values; checks nothing — R4); GUARD ENTRY `g` and COMPLETION
`c` (R2: `g` consumes `L`'s binder and activates or skips the REGION; `c` produces the logical result — the region's on
the enabled branch, the short-circuit constant at once on the disabled one); STORE (phase 2; its own check is its
failure). A private local (neither captured nor address-taken) and a constant are order-transparent: not occurrences.

**Edges** — two sorts, kept apart (R2): VALUE dependencies (a body follows every binder it consumes) and ORDER
prerequisites (`after`; discharged by a DONE or a SKIPPED occurrence; a skip never invents a value). Each from a pinned
go1.26.5 clause:

| edge | sort | rule | clause |
|---|---|---|---|
| D data | value | producer → every occurrence that uses its binder: arguments before their call, `a[f()]`'s call before the access, a target before its read and its store | spec#Calls «arguments … are evaluated before the function is called»; spec#Order_of_evaluation «`g` cannot be called before its arguments are evaluated» |
| E1 lexical | order | among events (calls, method calls, receives) and logical operations: `o₁ → o₂` when neither lies in the other's operand subtree and `o₁` starts earlier in the source; nested events by D (`f(g())`: `g → f`, F9.1). A logical operation is anchored at its COMPLETION for later events and its ENTRY for earlier ones; its region's events follow the entry by membership (R2). Allocations carry none (R3) | spec#Order_of_evaluation «all function calls, method calls, receive operations, and binary logical operations are evaluated in lexical left-to-right order»; its `y[f()], ok = g(z \|\| h(), i()+x[j()], <-c), k()` ⇒ `f h i j <-c g k` |
| G regions | activation | `g` enabled iff its test requires `R`; every occurrence of `R` follows `g`; a disabled region's occurrences are SKIPPED (discharge order edges, produce nothing); `c` is the only join — a value use of a region-confined binder outside its region is REJECTED; regions nest (R2) | spec#Logical_operators «The left operand is evaluated, and then the right if the condition requires it» |
| P phases | order | every phase-1 occurrence → every store; stores left to right; `x op= y` has ONE target plan, shared by its read and its store; `x++` ≡ `x += 1` | spec#Assignment_statements «The assignment proceeds in two phases. First, the operands of index expressions and pointer indirections … on the left and the expressions on the right are all evaluated in the usual order. Second, the assignments are carried out in left-to-right order»; «`x op= y` … evaluates `x` only once»; spec#IncDec_statements |
| F statement positions | order | select operands once in source order, RecvStmt targets after the communication; send channel and value before the send; switch tag once, cases in order; the range expression once — «with one exception: if at most one iteration variable is present and `x` or `len(x)` is constant, the range expression is not evaluated»; results set before defers | spec#Select_statements, spec#Send_statements, spec#Expression_switches, spec#For_statements, spec#Return_statements |

Nothing else is an edge. A read or op against a sibling event, two reads or ops, a logical operation's LEFT-operand read
against events, a receiver sub-evaluation against argument events (E14), an allocation's payload reads against sibling
events — all UNORDERED: spec#Order_of_evaluation «the order of those events compared to the evaluation and indexing of
`x` and the evaluation of `y` and `z` is not specified»; read-vs-read by omission; interleavings admitted (I-2 UNSEQ,
ledger L-013). NO READ-ORDER REDUCTION (R1): v2's «non-event occurrences of which at most one can fail may be
sequentialised among themselves» is FALSE — adding `read(x) → read(y)` to `x + y + mut()` removes `read(y); mut();
read(x)` (spike R1: {0,1,2,3} vs reduced {0,2,3}). Graphs start unreduced; the only permitted early optimizations are
folding constants and operations already forced by dependencies; any future ordering optimization carries a preservation
obligation accounting for every intervening write, effect and failure, PROVED before it is USED.

**Executions and results.** A legal execution of a DYNAMIC sweep is a run of the scheduler (R2): (i) no pending active
work → phase 2 / completion; (ii) ready set nonempty (value deps produced, order prerequisites discharged, region
active) → pick one and run it — a guard entry activates or skips its region; (iii) pending active work with NO ready
occurrence → a NAMED malformed-graph refusal, never a stuck run. A failure ends the run: the prefix so far plus the
failure. Every node, region nodes included, has a STATIC canonical rank (declaration order, a region inline behind its
guard), independent of dynamic activation order. CERBERUS ADAPTATION STATEMENT (claims tightened): the SHAPE is Cerberus
Core's `unseq` — reduce any eligible element under a `Kunseq` frame (`core.lem:320–332`, `core_run.lem:1372–1396`,
`deps/cerberus-upstream` @ `b9aeedcb4` in the sibling cerberus-lean project; Memarian et al., PLDI 2016 §5.6 via
`docs/2026-08-17_prior-art-ch2o-cerberus.md` §2); those forms and that rule do NOT by themselves prove the Go occurrence
graph, whole-occurrence granularity, the E1 anchoring or the guard joins correct — this note's Go-specific obligations
(§7). SWEEP RESULT = the binder values the statement uses + the resulting state + the EFFECT PREFIX (output, channel
ops, callee stores, in order) + the first failure if any. OBSERVATION PROJECTION (what rows compare): output bytes,
terminal status, panic identity. Domain: sequential and terminating — a receive that would block is a `blocked` REFUSAL,
apart from the member set, never a panic (spike X3e); a non-returning call has no result (F9.2); recovery is outside the
sweep. THE SEMANTICS of a sweep = the SET of results over its legal executions. Lower bound: gc's draw ∈ set, per row;
upper bound: set ⊆ Go-permitted, from clauses. Identity sharing (F3): §3.4.

## 2. The reference enumerator (bounded fragment)

`enumerate.py` in `docs/evidence/2026-09-16_eval-order-v2-spike/` (R1/R2/R6 encodings adapted from the review's
`check.py`, re-encoded on the repaired protocol). WHAT: for a hand-encoded graph (a generated one in §6), every legal
run of the §1 scheduler; per run the sweep result; the MEMBER set with trajectory multiplicities, REFUSALS (`blocked`,
`Malformed`) apart, the slot-0 (canonical) draw. FRAGMENT and RESULTS: the README (its table lists every set, forbidden
hybrid, refusal and gc draw for W1–W6, X1–X3, X3e, R1, R2a–c, R4, R6, C1–C4); `outcomes.txt` PASS (exit 0); every draw a
member. TWO CHECKS, LABELLED (claims tightened): (a) REFERENCE GRAPH CHECKS PASS — this spike; (b) MACHINE EQUALS
REFERENCE — the lowered machine's enumerated set over the wire EQUALS (a)'s set over the source graph, exact, both
directions: NOT tested here (no lowered machine exists), an exit criterion of Stage C (§7). ORACLE MEMBERSHIP — gc's
draw ∈ set (K draws per `docs/coverage-suite-structure.md`) is an observation, never a guarantee.

## 3. The core construct — Cerberus-shaped `unseq`

### 3.1 The occurrence contract (R3)

A graph exposes evaluation order only if no body hides a second mutable read, a failing operation or an argument
evaluation. INTERNAL NORMAL FORM: every operand of a head is a constant, an explicitly admitted stable read (a private
local), or a typed slot reference (a binder of sort VALUE or TARGET).

| kind | permitted head (first fragment, Stage C) | declared reads | effects | may fail | results |
|---|---|---|---|---|---|
| Read | captured/address-taken/global name; `*p`; `a[i]` / `m[k]` on base+index VALUES; value-receiver copy | exactly the one location | none | bounds, nil, hash | one |
| Pure op | `+ - * / % << >>`, `== !=` on non-interface values, `!`, numeric conversion, `x.(T)`, `a[lo:hi]` on values | none | none | `/ %` zero, shift, assertion (spec#Type_assertions), slice bounds | one |
| Allocation/conversion | `[]byte(s)`, `string(b)`, slice→array, `make`, `new`, composite literal on selected payload values | the payload copied: `string(b)`, slice→array READ backing storage (spec#Conversions_to_and_from_a_string_type, spec#Conversions_from_slice_to_array_or_array_pointer) | allocates (unobservable, C11); NO E1 edges | slice→array length; `make` size | one |
| Invocation/receive | call / method call on callee + argument VALUES; `<-ch`; comma-ok `<-ch`; `f(g())` forwarding (spec#Calls); built-ins «called like any other function» (spec#Built-in_functions) — a constant `len`/`cap` is NOT an occurrence (spec#Length_and_capacity «in this case `s` is not evaluated»); `recover` — an EVENT, never an op: it changes the continuation (spec#Handling_panics) | none of its own | the callee's / one communication, once; zero-result calls and `print` still discharge E1 (spec#Expression_statements) | nil callee, callee panic | zero, one or many (comma-ok = ONE occurrence, two outputs) |
| Target plan | `x`, `a[i]`, `m[k]`, `*p`, `p.f` on FROZEN operand values | none | none | none (checks deferred to the store) | one, sort TARGET (`TargetRef`, `Machine.lean:1554` — not a `GoValue`) |
| Guard entry / join | the test binder of `&&` / `\|\|`; region membership | none | activates or skips the region | none | one decision |
| Completion | the region's result (enabled) / the short-circuit constant (disabled); `then`: stores and control transfer over results | none | stores (phase 2) | the store's check | exactly one logical result; no rerun of any source expression |

Interface `==` MAY FAIL (spec#Comparison_operators «A comparison of two interface values with identical dynamic types
causes a run-time panic if that type is not comparable») — never «pure because spelled as an expression». DECODER
CHECKS, each a refusal by name (`GoLean/NativeToIR.lean:199` key set, `:1205` arm): unknown reference; cycle in data ∪
`after`; duplicate result (a binder produced twice; a guard's `out` not produced exactly once per branch); sort/type
mismatch (VALUE vs TARGET; declared type vs head); hidden read in a pure node (an operand not a constant, admitted read
or slot); invalid branch join (a region-confined binder used outside its region other than through the completion); list
order not a linear extension; nested `unseq`; `recover` outside an invocation head. ADMITTED GRAMMAR of the first
fragment, BOUNDED: the table's heads over int/bool/string locals and globals, slices of them, closures and top-level
functions with 0–2 results, buffered channels, `+=` on `a[i]`, `x := e`, `x = e`, `a[i] = e`, tuple assignment,
`println`; every further head is an explicit adapter with its validation rule — never a GoCore type checker
(`decodeExpr` returns `Expr`, not a checked typed expression — `NativeToIR.lean:404`).

### 3.2 Wire node (sketch; no schema work) — data edges IMPLIED by binder mentions; `after` = ORDER prerequisites (E1, F); list order = canonical rank

    {"stmt":"unseq",
     "occ":[ {"bind":"$u1","kind":"op","head":OP,"args":[…binders/consts…],"type":T},
             {"bind":["$u2","$u2ok"],"kind":"event","head":CALL,"args":[…],"after":["$c1"]},   // results → predeclared binders; never define
             {"bind":"$l1","kind":"target","head":TGT,"args":[…]},                            // sort TARGET; operands frozen
             {"bind":"$u3","kind":"read","of":"$l1","type":T},
             {"bind":"$g1","kind":"guard","test":"$u5","when":false,"out":"$c1","occ":[…region incl. the completion $c1…]} ],
     "then": STMT }                                                                          // phase 2; stores name $l targets

### 3.3 Machine: runtime record, storage, scheduler (R4)

Machine facts (`433e7490`): `LocalEnv := List Scope` maps names to `Loc` (`GoLean/GoCore/State.lean:16`, `:127`);
`HeapCell.value` has NO unassigned slot (`:30–32`); `TargetRef` is a machine type, not a `GoValue`
(`Machine.lean:1554`); the decoder's `.initialization` allocates a NEW binding in the enclosing sequence
(`NativeToIR.lean:1531`, `StepFn.lean:200`) — v2's «event body with `define:true` fills the slot ENTER allocated» was
wrong. RUNTIME RECORD, carried by `Cont.unseqK rec k`:

    UnseqRec := { graph : static (occs, deps, after, regions, ranks, then) — shared, never copied per pick
                ; status : Array (active | done | skipped) — «completed» ≠ «produced»;  cells : Array Loc + assigned : bitmap — VALUE results
                ; targets : Array (Option TargetRef) — TARGET results, continuation-owned;  env : LocalEnv — the SOURCE scope;  completed : Bool }

REPRESENTATION TO PROTOTYPE [AGENT]: preallocated typed value cells (one `Loc` per VALUE binder, allocated at ENTER at
its declared type, zero-initialised) + an assignment bitmap in the continuation («produced» is a scheduler fact, not a
heap fact) + a continuation-owned target table; the source-language value/heap universe is NOT extended for scheduler
bookkeeping (a control-only slot table only with a demonstrated call-result adapter, Stage B). Event bodies WRITE
PREDECLARED RESULT DESTINATIONS: `retV v (.unseqOccK i …)` stores into `cells[i]` and sets bit `i`; multi-result
invocations route each result to its binder; never `.initialization`. SOURCE DECLARATIONS live in their source scope: `x
:= a + f()` lowers to `then` = `.initialization x; x = $u`, run in `rec.env` (extended in place, as today), so `x`
survives the sweep; temporary-scope disposal drops ONLY the scheduler cells (C4 may reclaim them). ENTER `.exec (.unseq
g) env k`: allocate the cells, bits clear, every status `active` (regions included), `targets` empty → `.next (.unseqK
rec k)`. PICK at `.next (.unseqK rec k)` — ONE `ready` function (R5) shared by execution, the `Step` premise and
`seqConsumption`: (i) no active occurrence → `.exec then rec.env k`; (ii) `ready ≠ []` → `ChoiceSite.unseqNext` at bound
`|ready|` (State.lean `:339`, `canonicalSlot0` row `:360`); slot `j` = the `j`-th ready occurrence in RANK order; bound
1 pops nothing (G-U); run it under `Cont.unseqOccK i rec k`: op/read/allocation → `.evalE head …`; event → the
invocation; target → the existing target resolution on frozen operand values; guard → decide, activate or mark the
region `skipped` and set the completion's cell; (iii) active occurrences, `ready = []` → `.stuck "unseq: malformed graph
— no ready occurrence"`, refused by name. EXIT: `then` runs in the source scope; the cells die with the statement.
FAILURE: `.panicking chain (.unseqOccK …)` → `.panicking chain k`: the sweep's first failure with the effect prefix so
far; `unseqK`/`unseqOccK` are `exprGlue` for panics (`Cont.class`, `Machine.lean:2656`, arm `:2660`); signals cannot
reach them (`:4806–4829`).

### 3.4 Target identity (R4), binder lifetime (F5), multiplicity (F6)

A shared `TargetRef` is NOT yet a shared element identity: `resolveChain` (`Machine.lean:1614`) replays the chain at
STORE time and `indexTargetLoc` (`:226`) loads the CURRENT header of the cell it is given — a plan that rereads a
rebound slice variable at the store is not the identity the read used. The adapter FREEZES the slice/map/pointer
operands whose evaluation the plan claims complete (the header, map and pointer VALUES — never the variable); the store
replays only the deferred checks on them. Tests (Stage B, hand-built node): slice replacement (spike R4), map
replacement, pointer redirection, cell mutation at a stable address — old storage retained, BOTH writes observable, no
hybrid read/store. Plain-assignment checks keep their phase-2 placement (`storeTarget`, `:1627`; BUG-029/033); compound
targets share the frozen plan. BINDER LIFETIME (F5): cells allocated at ENTER per dynamic sweep, dead at exit or panic;
a loop iteration re-enters → fresh; recursion → per activation (`enterFrame`, `Machine.lean:698`); an absent value means
«no candidate in THIS sweep» (W5). MULTIPLICITY (F6): no saved-candidate table; a value is produced once, where picked;
`k` legal runs are `k` occurrence orders, each realised by ONE OR MORE tapes (an occurrence that itself consumes choices
— a call, an allocation — adds picks; v2's «one pick sequence each» is withdrawn — claims tightened).

### 3.5 Canonical order, compatibility and the tape contract (F7; R1, R5, claims tightened)

CANONICAL (slot 0): the list order = today's ANF emission order (`tools/nativefrontend/wire.go:25–30`; `hoist` emit.go
`:2934`, `pushHoist` `:5420`): per event in lexical order its argument occurrences (post-order) then the event; after
the last event the residual's («calls first, reads late») — gc's per-kind realisation: v2 §3 @ `9a8ed328`; BUG-104's
targets move late, the intended flip. COMPATIBILITY = OBSERVATION compatibility on specified rows (output bytes,
status, panic identity), NOT byte-identical trajectories: steps, cells, allocation counts, fuel and stream indices
change. INTENDED CHANGES, listed: BUG-101 ×2 and BUG-104 ×5 rows (wrong answers → members); BUG-102
`compound-call-target-vs-len` (refusal → member); strict rows whose observation varies with the tape → lane moves, each
listed; membership sets ⊇ old, each widening named. LANE-MOVE AUDIT RULES (R5): differing observations across tapes → a
nondeterministic lane (`lane=membership`, `members=`); identical observations but the three fixed streams do not cover
the picks → strict `depth=N` or certified confluence (the strict-lane depth guard, `docs/coverage-suite-structure.md`);
budget exhaustion → REFUSAL by name, never evidence of a singleton or grounds to re-pin; `depth=N` does not make a
genuinely varying strict row pass. v2's «none on status» assurance is REMOVED: BUG-101 has both normal and panic
members. TAPE CONTRACT — CLAIMED: (i) the set of sweep results over all tapes = the set of results of the graph's legal
runs (the wire scheduler theorem, §7); (ii) the all-zero tape realises the canonical order, observation-compatible with
today's trajectory outside the intended changes. NOT CLAIMED: any non-empty tape's consumption trace (membership
certificates re-enumerate; the twin re-pins); observational equivalence of candidates; ANY ordering reduction (R1:
deleted).

### 3.6 The enumeration route (R5)

The certified dedup engine REJECTS `unseqPanic` today — `EnumDedupCheck.innerVecs` returns `none`
(`GoLean/GoCore/EnumDedupCheck.lean:101–129`), `EnumDedupSound.lean:320` cases on it, `GoLean/EnumDedup.lean:138` names
the refusal, `MultiStreams.lean:114` marks it non-oblivious — and would reject every `unseqNext` pick the same way: a
new constructor plus a flag gives NO working enumeration, and new picks occur on every ordinary SUCCESSFUL iteration, so
the path product is real. ONE MEASURED ROUTE for the vertical slice, chosen at Stage B's exit from numbers and part of
Stage B/D's exit evidence: (α) certify `unseqNext` in dedup — branch-vector construction for the pick plus its
checker/soundness arms; or (β) the default enumerator on a bounded PILOT with RECORDED budgets (repeated sweeps, a wide
argument list, a loop; unique states and paths, runtime, RSS, consumed picks). [AGENT] recommends (β) first for numbers,
(α) before Stage E. The accountant exposes EXACTLY the scheduler's bound (`seqConsumption` arm `.next (.unseqK …) ↦ some
(.unseqNext, |ready|)` when ≥ 2, beside `Machine.lean:4084–4088`; `consumesUnseqNext` beside `consumesUnseqPanic`
`:4057`). The pool/CLI path the corpus uses is NOT exempt («sequential model» exempts no continuation from the pool
driver or the output/race plumbing); a checked-read adapter preserves the accesses `Race.strictOpAccesses` reports today
(`GoLean/GoCore/Race.lean:506`, arm `:1545`).

### 3.7 Where it lands (all at `433e7490`)

The file-by-file anchor list of v2 @ `9a8ed328` §3 «Where it lands» (Syntax `:608`; Machine `Cont` arms `:2585`,
`:2598`, `:2656`, `Step` rules beside `:4830–4840`, `seqConsumption` `:4084–4088`, `:4057`; StepFn `:155`, `:355`,
`:631`; State `:339–:382`; StateWf `:221`, `:366`, `:573`; MachineSound `:172`, `:506`, `:4076`, `:4452`, `:4731`;
`EnumDedupCheck.lean:128`, `MultiStreams.lean:114`) is re-verified and stands, with `unseqTargetDone` and
`unseqMalformed` added to the `Step` rules. `Stmt.unseqProbe`, `Cont.probeK`, `ChoiceSite.unseqPanic` (`:608`, `:2567`,
`:347`) RETIRE only at Stage E, after every admitted caller, test and consumer has moved; until then a SYNTAX-BASED
MIGRATION BOUNDARY per WHOLE sweep: old lowering or graph lowering, never a mixture that evaluates an operand twice or
drops an edge; no fixture-name dispatch. One writer for the core while its types and proofs change.

**Addendum (2026-09-16, [AGENT] fix-round worker, per the Stage B audit's R4 — `docs/2026-09-16_unseq-stage-b-audit.md`;
records only): the rule names in this subsection are SUPERSEDED by the landed candidate (`core/unseq-scheduler-b-0916`).**
The `Step` relation carries TEN `unseq` rules — `unseqEnter`, `unseqPick`, `unseqComplete`, `unseqRunEval`,
`unseqRunInvoke`, `unseqRunLoad`, `unseqRunTarget`, `unseqRunGuard`, `unseqValue`, `unseqStmtDone` (`GoLean/GoCore/
Machine.lean`, the block after `probeRaise`). `unseqTargetDone` does not exist: a target plan is ONE step
(`unseqRunTarget` resolves the frozen atoms and marks the occurrence DONE in the same transition). `unseqMalformed` does
not exist BY DESIGN: a refusal is not a step — scheduler case (iii) (active work, nothing ready), the invalid join
(`UnseqGraph.skippedDep?`), the completion's production check (`UnseqGraph.unproducedConsumer?`, fix round F1), the
frozen-anchor check (`unseqUnfrozenPlan?`, fix round F2) and the static shape check (`UnseqGraph.wellFormed?`, incl. the
`$` reservation and the bool-cell checks of fix round F3/N3) are `stepFn`'s NAMED refusals with no `Step` rule, so
`stepFn_sound`/`step_complete`/`step_complete_any_wf` are stated over exactly these ten. (`unseqProbe`, the retiring
E13 probe's rule, is the eleventh `unseq*`-named constructor and belongs to the legacy lowering, not to this construct.)
The lane handoff `docs/2026-09-16_unseq-stage-b-handoff.md` §2/§9 mirrors this mapping.

## 4. Reviews dispositioned

| first review | v2.1 | second review's disposition of the first |
|---|---|---|
| F1/F2/F4/F6 placements, dependencies, failures, intermediate values | positions = readiness; occurrences produce values, parents consume binders; every failing occurrence a node; one multiway pick (§1; W1/W2/W4/W6) | addressed; retain as native exact-set regressions; R2/R6 qualify the general claim |
| F3/F5 target identity, dynamic lifetime | one FROZEN target plan shared by read and store; cells per dynamic sweep (§3.4; W3, R4, W5) | correct design intent; representation and adapters remain to establish under R4 |
| F7 tapes/observability | tape contract stated; reduction DELETED; canonical = observation compatibility (§3.5) | much clearer; R1 removed, canonical/equality claims qualified |
| F8 census | relabelled (§6); dynamic cost is Stage D's experiment | correctly relabelled; not a bound |
| F9 contract and validation | contract (§1), enumerator and labelled checks (§2), controls, certificate (§7) | improved; guard semantics (R2), the machine comparison (Stage C) and the source→wire certificate (§7) are now explicit |

| second review | resolution in v2.1 |
|---|---|
| R1 read-order reduction FALSE | deleted (§1, §3.5); unreduced graphs; fold constants / forced ops only; preservation obligation proved before use; spike R1 exact-set regression |
| R2 guards: skip / completion / three cases / rank | guard entry + completion nodes; order prerequisites ≠ value deps; skip discharges, never produces; invalid join rejected; scheduler cases (i)–(iii) with a named refusal; static rank (§1, §3.3); spike R2a/R2b/R2c, X2, C4 |
| R3 occurrence contract | normal form + kind table + classifications + decoder checks + bounded grammar (§3.1) |
| R4 storage, scope, freezing | runtime record; cells + bitmap + target table; predeclared destinations; source scope; frozen operands; tests (§3.3, §3.4); spike R4 |
| R5 enumeration route | dedup rejects `unseqNext` today; one measured route (α/β) in Stage B/D exit evidence; one `ready`; pool/race preserved; lane-move rules; «none on status» removed (§3.5, §3.6) |
| R6 N1 granularity | producers + one checked access recommended (§1, §5); spike R6 {10,20} vs {20}; a fused choice would be a narrowing recorded everywhere — PENDING [USER] |

## 5. Decisions PENDING [USER] — posed, not ruled; recommendations only

1. **E2/E12 value axis** — DISSOLVES as a mechanism question (a value is produced where picked). [AGENT]: E2/E12/E14's
   value axes → (a) ENVELOPED when their rows land; ratify at that merge ask.
2. **Width of P** (which reads are occurrences): (i) today's failing kinds (`probeKind`, emit.go `:5450`) + events;
   (ii) also the mutable reads (captured/address-taken locals, globals, heap, map, value-receiver copies, conversion
   payloads). W1/W6 are P(ii) reads: a P(i)-only pilot CANNOT pass them as graph-envelope regressions (review §2).
   [AGENT] recommends (ii), the Stage C pilot carrying the minimal P(ii) reads its fixtures need (W1/W6/R1/R6) once
   ruled; under (i), W1/W6/R1 stay reference-only, not labelled scheduler failures.
3. **Interleaving positions** — DISSOLVES: legal runs are the members; no separate widening.
4. **E3/E4 retirement + late structural allocations** — fall out of listing every phase-1 failing occurrence (X1); an
   allocation is a node without E1 edges (R3); ratify at the merge ask.
5. **N1 read granularity** (R6): base/header and index PRODUCERS + ONE checked access — the machine's own split;
   `a[f()]` = {10, 20}, gc 20. [AGENT] recommends the split; a FUSED read, if chosen, is a NARROWING recorded in the
   model, the reference generator, the inventory and every affected row — never a complete envelope.
6. **N2 canonical order**: today's emission order vs a gc-shaped per-kind order; no semantic content; [AGENT]
   recommends today's; ratify.
7. **N3 enumeration budget**: a row whose width exhausts the budget REFUSES by name — no silent sequentialisation, no
   re-pin from exhaustion (R5). [AGENT] recommends refuse + measure (Stage D).
8. **N4 ladder position** — §7.

## 6. The census, relabelled; the generator plan

v1's numbers (`90dc66f0`, `count.py`) are a RESIDUAL-NODE CENSUS OVER RETAINED INPUTS (F8): they locate where nodes
would go and bound neither nodes, picks nor evaluations. The REAL COST MEASUREMENT is Stage D's: nodes per row; dynamic
entries; picks by bound on the canonical tape; lanes before/after with every move named; enumeration size per membership
row; fuel, wall time, RSS against main; budget refusals by name. GENERATOR (`tools/evalorder-gen`; axes and layout as v1
§4, corrected per F9.5), begun at Stage C ALONGSIDE each adapter (review §2): a small EXHAUSTIVE fragment first,
pairwise (~150–200 shapes) after; each shape's set DERIVED by §2's enumerator from the source graph, independent of the
emitter's edges; machine set = reference set (exact); gc draws ⊆ set (K=32 gate / K=80 slow); singletons ONLY for
controls with no remaining unordered pair (`sink(a, mut())` is two-member).

## 7. Stages, theorems and the ladder (review §2, §4 — replaces v2's S1–S4)

| stage | deliverable | exit evidence |
|---|---|---|
| A. Repair the executable design (THIS LANE) | R1/R2 regressions; occurrence grammar, result sorts, region protocol, runtime record; the user gates the fragment needs posed | spike: reference sets and negative cases pass (exit 0); one source example with a complete graph, wire sketch, canonical order and result mapping (§3.2/§3.3 over W3/R4); this note |
| B. A small scheduler on hand-built graphs | new syntax, continuation state, `ready`/pick/completion, slot lifetime; total rules and `stepFn` cases TOGETHER; the mechanism theorem's statements and first proofs (below) established HERE to constrain the representation | successful and failing runs match the reference; arbitrary legal schedules have replay tapes; malformed / no-ready graphs refuse by name; singleton picks do not consume; §3.4's target tests on a hand-built node; first budget numbers |
| C. One native fragment end to end | decoder validation + source-to-graph lowering for §3.1's stated grammar; normal / call / return / target adapters; generated tests beside each adapter (§6) | source → actual frontend bytes → strict decoder → machine → EXACT observed sets = reference (check (b)); decoder mutations reject (§8); source declarations survive completion |
| D. Exploration economics | correct branch accounting + the chosen engine (α/β, §3.6); scope/deallocation representation measured on repeated sweeps | a workload ladder (repeated sweeps, wide argument list, loop, E13 family, twin) closes within RECORDED budgets; exact-set and accountant checks pass; no outcome-losing optimization |
| E. Family migration | by operand and statement family: BUG-101/104, assignment targets, guards, receivers, allocations; legacy `unseqProbe`/`probeK`/`unseqPanic` removed only after all callers, tests and consumers moved; whole-sweep boundary, no fixture-name dispatch | per-family full gate + `--diff`, named set changes, pins/ledgers updated; full corpus and required certified workloads pass at the final boundary |

Stages B–D overlap only in small increments; one writer alters shared core signatures; no general proof refactor bundled
in. SLICE PROMISES CORRECTED: a P(i)-only pilot cannot pass W1/W6 (§5 item 2); BUG-101 needs the
assertion-success-then-mutation-to-failure AND the slice-value witnesses (`assert-ok-early-len-hoist`,
`slice-value-early-len-hoist`), BUG-104 stable shared targets through calls with observable stores (its five rows) in
the Stage C pilot before any flip is predicted; generated tests from Stage C; the mechanism theorem during B; ESTIMATES
conditional on B–D's results — no session counts, no «months» alternative. **THEOREMS.** (b) the WIRE SCHEDULER THEOREM
(renamed from v2 §7(b)): for a well-formed `unseq` node (the §3.1 decoder checks as hypotheses) — SOUNDNESS over the
executed occurrence TRACE: a successful trace completes the active graph in an order respecting every edge; an escaping
panic is a legal prefix ending at that failure with no later effect; COMPLETENESS: every legal finite execution of the
graph — successful or failing, INCLUDING the occurrences' own nondeterminism and their choice consumption — is some
tape's `stepFn` trajectory; invariants as proof interfaces: preservation (`StateWf`), no double execution, dominance of
consumed values, region progress, target consistency (frozen operands), freshness (cells per activation). It proves
nothing about the frontend. (a) the SOURCE-TO-WIRE TRANSLATION CERTIFICATE (master plan §7.2 F6; F9.6) stays a SEPARATE
owed obligation: a small source fragment (§2's) with a checked source/graph correspondence certificate or a preservation
theorem for its lowering. Finite generated-set comparisons (§6) remain TESTS; substituting them for the certificate
would be an explicit plan-change proposal, PENDING [USER] — not proposed here. **LADDER (N4, PENDING [USER]).** [AGENT]
recommends Stages A–B BEFORE B7 (B7 rewrites every core signature; one core writer at a time; `unseqK` takes the B3
one-tail shape, C3 adds one more frame; the cells are scope temps C4 absorbs); then B7 → C1, with Stage C's
frontend/decoder work beside them ONLY under explicit file ownership and compatible interfaces; D and E after; then P →
C3 → C4 → B6 (the E13 lane is a SEMANTICS lane, `docs/2026-09-03_design-hygiene-arc.md`). Alternative: all after C3 (no
positional-tag fragility), BUG-101/104 red meanwhile.

## 8. Minimum acceptance matrix (review §3) — a row outside the fragment is DEFERRED or REFUSED-AT-BOUNDARY, never validated

| family | required discriminators | Stage C status |
|---|---|---|
| Read placement | W1/W2/W6; both lexical sides; header before an index-producing call (R6); R1's lost member | fragment (P(ii) reads per §5 item 2) |
| Logical regions | skip / right-run (R2a); nested guards (R2c); later sibling call; pure RHS read before a later call (R2b); no use of disabled data (invalid join refused) | fragment |
| Target identity | W3 + slice/map replacement (R4), pointer redirection, cell mutation at a stable address; no hybrid read/store | fragment (slice); map/pointer deferred to E |
| Phase checks | phase-1 operand panic stores nothing (X1); first phase-2 store persists when the second panics; compound read failure vs RHS event (X3) | fragment |
| Dynamic state | W5, recursion, repeated nested calls, source short declarations, escaped closures; no stale slots | fragment |
| Invocation results | zero-result call, one, two results, comma-ok receive; effect once; arguments not reread | fragment (0–2 results); comma-ok deferred to E |
| Failure/control | callee recovers and returns; callee panic escapes and cancels pending work; deferred `recover` inside a migrated sweep; blocked receive distinct from panic (X3e) | fragment; `recover` inside the sweep refused-at-boundary until E |
| Infrastructure | `unseqNext` beside an existing choice site; exact accounting; canonical replay; unsupported/malformed graphs and budgets refuse by name | fragment |

RECORD PER ACCEPTED FIXTURE: source shape · graph (independent of the emitter's edges) · expected observation set ·
forbidden members · oracle draws · actual lowered-machine set · canonical draw · budget. EDGE-MUTATION VALIDATION (a
requirement): mutate one data, one lexical, one guard and one phase edge of a lowered graph and show the decoder or the
exact-set check names the error; a handwritten graph alone validates no lowering.

## 9. Handoff

- DECIDED [AGENT] inside the ruling: §1's graph, edge table and scheduler; §2's enumerator and labelled checks; §3's
  occurrence contract, wire sketch, runtime record and representation to prototype, frozen target identity, tape
  contract without reduction, the enumeration-route choice point; §7's stages and theorems; §8's matrix.
- PENDING [USER]: §5 item 2 (width of P — recommend (ii)), item 5/N1 (recommend the split), item 7/N3 (recommend refuse
  + measure), item 8/N4 (recommend Stages A–B before B7); items 1/4/6 for ratification at the merge ask. No gate was
  ruled by this lane.
- NOT DONE HERE: no concurrency claim (racy programs refuse); no init order (E7/E8); no member for gc's early store
  (E5, L-016); no composite-literal internal store order; no claim about gc's `order.go` beyond measured draws; no
  schema work, Lean build, census re-run or baseline change; no ordering optimization of any kind.
- NEXT: Stage B — a small scheduler on hand-built graphs, one core writer; its brief carries §3.1's grammar, §3.3's
  record, §3.4's tests, §3.6's route choice and §7's theorem statements.
- AUDIT ASK for this note: the edge table and E1 anchoring against the pinned clauses; the R3 kind table's
  failure/effect columns against the pinned clauses; the runtime record against the cited machine facts; the spike's
  R1/R2/R4/R6 graphs against the review's `check.py`; the claims split.
