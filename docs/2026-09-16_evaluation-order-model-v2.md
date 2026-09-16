# The evaluation-order model v2 — the `unseq` construct in the core (2026-09-16)

[AGENT] Design note, lane `design/eval-order-model-v2-0916`, at main `433e7490`; records only. It
implements as a design the ruling of [USER] Mike, 2026-09-16, verbatim, relayed by the [AGENT]
coordinator — cite as relayed: «Okay, so this feels like sort of a profound decision, but I think the
Cerberus model is the correct one (they did a lot of work thinking through such issues). Can you go
ahead with the next steps?» (record: `docs/2026-08-31_qrow-rulings.md`, «The evaluation-order mechanism
ruling record (2026-09-16)»; `docs/2026-09-11_review-dispositions.md` §3 item 5). The v1 note
(`design/eval-order-model-0915` @ `90dc66f0`, unmerged) keeps its §1 relation — re-founded here — and
its rule R1–R3 (spec-ordered → structural ANF in the frontend; spec-unordered with an observable → a
machine tape choice; the rest refuses by name); its endpoint probe-and-use mechanism is RETIRED. The
order below is the Codex review's revision sequence (`docs/2026-09-15_evaluation-order-model-review.md`,
F1–F9). The mechanism is decided; nothing here re-opens it. Rulings are [USER] verbatim-as-relayed or
PENDING [USER]; everything else is [AGENT].

## 1. The relation, re-founded: a dependency graph over evaluation occurrences

**Sweep.** One statement's evaluation phase (a block statement, or a sub-accumulator: if/for
init·cond·post, switch tag, case values, range operand, per-spec var initializer — e13-b §1). Its
OCCURRENCE GRAPH is (occurrences, must-precede edges, guarded regions).

**Occurrences** — each produces at most one value into a BINDER, may fail, may change state:
- EVENT `o`: a call or method call (the invocation, after its callee value and arguments), a receive,
  a built-in «called like any other function» (`len cap min max append copy make new recover`,
  spec#Built-in_functions; a constant `len`/`cap` is NOT an occurrence — spec#Length_and_capacity
  «in this case `s` is not evaluated»; the statement built-ins `panic print println delete close
  clear` are their statement's event), and a `&&`/`||` GUARD (regions, below). Its own failure (nil
  call, `make` size) is the event's. Its effects (output, channel ops, callee stores) are what the
  effect prefix records.
- READ `r`: one evaluation of a mutable location at that instant — a captured, address-taken or
  global variable, a heap cell (deref, field through a pointer), an element (`a[i]` = header +
  bounds check + element, ONE occurrence — §5 N1), a map entry (hash panic), a value-receiver copy,
  and the reads an operation performs (`string(b)`, `[]byte(s)` read their payload — review F2).
- OP `p`: a pure operation on produced values — arithmetic, non-constant `/` `%`, signed shift,
  assertion, interface `==`, slice expression, slice→array conversion; fails on its own account.
- LVALUE `ℓ`: a target's IDENTITY — (header, index), (map, key), a pointer's cell, a variable —
  built from its operand occurrences; produces the identity, checks nothing.
- STORE `s` (phase 2 only): consumes an identity and a value; the store's own check (bounds, nil
  map, nil pointer) is its failure.
A private local (neither captured nor address-taken) and a constant are order-transparent: not
occurrences; their read folds into the node that uses them. (R1's node-set rule: the FRONTEND decides
what is an occurrence, the MACHINE decides the order.)

**Edges** (must-precede), each from a pinned go1.26.5 clause:

| edge | rule | clause |
|---|---|---|
| D data | producer → every occurrence that uses its binder: arguments before their call, `a[f()]`'s call before the index, an lvalue before its read and its store | spec#Calls «arguments … are evaluated before the function is called»; spec#Order_of_evaluation «`g` cannot be called before its arguments are evaluated» |
| E1 lexical, among events | `o₁ → o₂` when neither lies in the other's operand subtree and `o₁`'s expression starts earlier in the source; nested events are ordered by D — `f(g())`: `g → f` (review F9.1) | spec#Order_of_evaluation «all function calls, method calls, receive operations, and binary logical operations are evaluated in lexical left-to-right order»; its own `y[f()], ok = g(z \|\| h(), i()+x[j()], <-c), k()` ⇒ `f h i j <-c g k` |
| G regions | `L && R` / `L \|\| R`: a guard `g` consumes `L`'s binder; `R` is a REGION enabled iff `g` requires it; every occurrence of `R` has `g →` it; a disabled region has NO occurrences (contributes nothing); regions nest | spec#Logical_operators «The left operand is evaluated, and then the right if the condition requires it» |
| P phases | every phase-1 occurrence → every store; stores left to right; `x op= y` has ONE lvalue occurrence, shared by its read and its store; `x++` ≡ `x += 1` | spec#Assignment_statements «The assignment proceeds in two phases. First, the operands of index expressions and pointer indirections … on the left and the expressions on the right are all evaluated in the usual order. Second, the assignments are carried out in left-to-right order»; «`x op= y` … evaluates `x` only once»; spec#IncDec_statements |
| F statement positions | select operands once in source order, RecvStmt targets after the communication; send channel and value before the send; switch tag once, cases in order; the range expression once — «with one exception: if at most one iteration variable is present and `x` or `len(x)` is constant, the range expression is not evaluated»; results set before defers | spec#Select_statements, spec#Send_statements, spec#Expression_switches, spec#For_statements, spec#Return_statements |

Nothing else is an edge. A read or op against a sibling event, two reads or ops, a receiver
sub-evaluation against argument events (E14), an allocation's payload reads against sibling events —
all UNORDERED: spec#Order_of_evaluation «the order of those events compared to the evaluation and
indexing of `x` and the evaluation of `y` and `z` is not specified»; read-vs-read by omission;
interleavings admitted (I-2 UNSEQ, ledger L-013).

**Executions and results.** A legal execution of a DYNAMIC sweep: the top-level occurrences are
pending; repeatedly run any READY occurrence (all producers done, region enabled); a guard adds its
region's occurrences or drops them; stop at the first failure or when nothing is pending; then
phase 2. Legal executions = the linear extensions of D ∪ E1 ∪ G ∪ P ∪ F over the EXECUTED occurrence
set — Cerberus Core's `unseq` reduction exactly: pick any non-value element, reduce it under a
`Kunseq` frame (`core_run.lem:1372–1396`, `core.lem:328–332`, `deps/cerberus-upstream` @ `b9aeedcb4`
in the sibling cerberus-lean project; Memarian et al., «Into the depths of C», PLDI 2016 §5.6, cited
through `docs/2026-08-17_prior-art-ch2o-cerberus.md` §2 — the paper is not in `deps/papers`). SWEEP
RESULT = the binder values the statement uses + the resulting state + the EFFECT PREFIX (output,
channel ops, callee stores, in order) + the first failure if any (the prefix stops there).
OBSERVATION PROJECTION (what rows compare): output bytes, terminal status, panic identity; values
and state are observed only through later output. Domain: sequential and terminating — a receive
that would block is `blocked`, not a member; a non-returning call has no result (F9.2). Recovery is
outside the sweep: the first failure leaves it as a panic and the frame's defers run unchanged.
THE SEMANTICS of a sweep = the SET of results over its legal executions. Lower bound: gc's draw ∈
set, measured per row; upper bound: set ⊆ Go-permitted, argued from the clauses (no oracle).

**F1–F3 resolved in the graph** (spike: `docs/evidence/2026-09-16_eval-order-v2-spike/`). (F1)
`v := mut() + a`: occurrences `E`, `R_a`, `Op`; no edge between `E` and `R_a` → {1, 2}: a position
before a lexically earlier event is a linear extension; the lower bound on placement is readiness.
(F2) `a[b[0]] + mut()`: `R_b0 → R_ai`, `E` free → `R_b0 R_ai E` = 10, `R_b0 E R_ai` = 30,
`E R_b0 R_ai` = 40: a parent consumes its child's PRODUCED value; «re-evaluate the subtree at an
endpoint» is not a node. (F3) `a[i] += mut()`: `R_a, R_i → L → Rd → Op ← E`, `L →` the store, P.
THEOREM (identity sharing): in every legal execution the read and the store of an `op=` target consume
the same identity, because an identity is produced by exactly one occurrence exactly once — so
{[11 20] (`R_i` before `E`), [10 21] (`E` before `R_i`)} and never [10 11]. The value read `Rd` has its
own timing after `L` (a call rewriting the cell in place yields the early or the late value — I-2).

## 2. The reference enumerator (bounded fragment)

`enumerate.py` in the spike directory. WHAT: for a hand-encoded graph (a generated one in §6), every
legal execution by the readiness rule; per execution the sweep result; the SET, with trajectory
multiplicities. INPUTS: occurrences (name, deps, body), guards with regions, an initial state, a
phase-2 function. FRAGMENT: integer locals; slices of ints (nil-able headers over named backing
arrays — `a = nil` rebinds the header, elements stay); index read/write with bounds panics; closure
calls that mutate; `+`; compound assignment (identity once); tuple-assignment phases; `||` regions
with an unexecuted case; a buffered receive. FAILURE KINDS: index out of range; a blocking receive
refuses (outside the domain). NEGATIVE CONTROLS: `f(g())` and `sink(a)` are singletons (no unordered
pair remains); `sink(a, mut())` is asserted NOT singleton (F9.5). TWO CHECKS, kept separate: MODEL
COMPLETENESS — the machine's enumerated set over the lowered wire EQUALS the enumerator's set over the
source graph (exact, both directions); ORACLE MEMBERSHIP — gc's draw ∈ set (K draws per the
sampling rule, `docs/coverage-suite-structure.md`); a draw is an observation, never a guarantee.
Results (`outcomes.txt` PASS; gc in `gc-draws.txt`, every draw a member): W1 {1,2} · W2 {10,30,40} ·
W3 {[11 20],[10 21]} ∌ [10 11] · W4 both identities · W5 {print 7 then panic in iteration 2; panic in
iteration 1}, no execution completes iteration 2 · W6 {0,1,2} · X1 (E4's shape) both identities · X2
z=false {2,3}, z=true {2} · X3 {len(ch)=0, len(ch)=1} · C1/C2 singletons · C3 {1,2} (§4 has gc's draws).

## 3. The core construct — Cerberus-shaped `unseq`

**Wire node** (sketch; no schema work): a statement listing a sweep's unordered occurrences with
binders and edges, and the statement's completion over the binders:

    {"stmt":"unseq",
     "occ":[ {"bind":"$u1","kind":"op","expr":E,"type":T},
             {"bind":"$u2","kind":"event","stmt":{"stmt":"assign","define":true,"lhs":[{"id":"$u2"}],"rhs":[CALL]},"after":["$u7"]},
             {"bind":"$l1","kind":"lvalue","target":TGT},                      // identity; operands are binders
             {"bind":"$u3","kind":"read","of":"$l1","type":T},                  // the checked read through $l1
             {"bind":"$u4","kind":"guard","test":"$u5","when":false,"out":"$u6","occ":[…region…]} ],
     "then": STMT }                                                             // phase 2 / completion; stores name $l identities

Data edges are IMPLIED by binder mentions (a body follows every producer it names); `after` carries
the non-data edges (E1 among events, F positions). The list order IS the canonical order (below).
**Decoder checks**, each a refusal by name (`GoLean/NativeToIR.lean:199` key set, `:1205` arm):
acyclic (data ∪ `after`); binder names unique within the function body (static; activation freshness
is the machine's); every use dominated by its producer (inside an occurrence that transitively follows
it, in `then`, or in a region whose guard follows it); a guard's `out` produced exactly once per branch;
type agreement (an occurrence's `type` = its body's decoded type; `then` type-checks under the binders);
the list order is a linear extension of the edges (declared, not inferred); no nested `unseq`, no
`recover()` in an `op`/`read` (recover is an event); an `event` body is a hoistable statement head.
**Machine.** `Stmt.unseq (occs : Array Occ) (then : Stmt)` (Syntax.lean beside `:608`);
`Cont.unseqK (pending : List Nat) occs env k`; an occurrence runs under `Cont.unseqOccK i …`.
- ENTER: `.exec (.unseq …) env k` declares EVERY binder of the node (regions included) in a pushed
  scope, unassigned, in list order — the env is identical whatever order the occurrences later run
  (the dedup checker merges the diamonds, `EnumDedupCheck.lean`); a read of an unassigned binder is
  `stuck` by name (unreachable under dominance). → `.next (.unseqK all …)`.
- PICK at `.next (.unseqK pending …)`: ready = pending with producers assigned and region enabled;
  `ChoiceSite.unseqNext` at bound |ready| (State.lean `:339`, `canonicalSlot0` row `:360`); slot `j`
  = the `j`-th ready occurrence in LIST order, so slot 0 = the canonical order's next node; bound 1
  pops nothing (G-U). Run it: `op`/`read` → `.evalE e env (.unseqOccK i …)`, `retV v` assigns
  `$u_i`; `event` → `.exec stmt env (.unseqOccK i …)`, `.next (.unseqOccK i …)` marks done;
  `lvalue` → the existing target resolution producing a `TargetRef`, stored as the identity; `read
  of $l` → the checked read through it; `guard` → test, then append the region's occurrences or
  assign `out`.
- EXIT: pending = [] → `.exec then …`; the scope pops with the statement (binders die).
- FAILURE: `.panicking chain (.unseqOccK …)` → `.panicking chain k`: the sweep's first failure with
  the effect prefix so far; frame and binders dropped; defers/recover unchanged. `unseqK`/`unseqOccK`
  are `exprGlue` for panics (Machine.lean `Cont.class` `:2660`); signals cannot reach them (refused
  as `probeK`'s are, `:4808–4829`).
**Binder lifetime (F5):** allocated at ENTER per dynamic sweep; dead at exit or panic; a loop
iteration re-enters → fresh; recursion → per activation (`LocalEnv` is per frame; `enterFrame`
Machine.lean `:698`); a region's binders are declared with the node, assigned only if it runs. An
absent value means «no candidate in THIS sweep», never a previous execution's (W5).
**Lvalue identity (F3):** produced once by the `lvalue` occurrence, checking nothing; the `read` and
the store in `then` both consume it; the value read has its own occurrence and timing; phase-1
failures (index-operand reads) stay distinct from the store's check (in `then`).
**Candidate multiplicity (F6):** no saved-candidate table; a value is produced once, where picked;
`k` interleavings are `k` linear extensions, one pick sequence each (W6: tapes `[0]`, `[1,0]`, `[1,1]`).
**Canonical trajectory (slot 0):** the list order = today's ANF emission order (`tools/nativefrontend/
wire.go:25–30`; `hoist` emit.go `:2934`, `pushHoist` `:5420`): for each event in lexical order its own
argument occurrences (post-order, left to right) then the event; after the last event the residual's
occurrences in post-order («calls first, reads late»). That is gc's realization for index, deref,
division, shift and conversion reads and NOT for assertions, slices and interface `==` (gc early;
e13-b §2), nor for BUG-104's targets (gc late, today's temps early — the list order puts them late:
the intended flip). COST when the canonical differs from an existing row's pinned member: none on
status (both are members); a strict row whose observation now varies with the tape is refused at
stage `nondet` unless it declares `depth=N` or moves to confluent/membership (the strict-lane rule,
`docs/coverage-suite-structure.md`) — a LANE MOVE, listed per row with its set; an observation-invariant
strict row stays strict when the three fixed streams cover its picks, else needs `depth=N` (§6 measures).
**Tape contract (F7).** CLAIMED: (i) the set of sweep results over all tapes = the set of legal
executions' results of the wire's graph (mechanism soundness AND completeness; tested by the §2
equality in the fragment, the Lean statement owed in §7); (ii) the all-zero tape realizes the
canonical order, byte-identical to today's trajectory on every sweep whose list order equals today's
emission order (measured as zero strict-lane drift outside the named flips). NOT CLAIMED:
preservation of any non-empty tape's consumption trace (a sweep that gains a bound-≥-2 pick re-indexes
every later pick; membership certificates re-enumerate; the twin re-pins); observational equivalence
of candidates (there is no consult-on-difference — the pick is at the scheduling point, before
outcomes exist). PICK REDUCTION, the frontend's only optimization: non-event occurrences of which at
most one can fail may be sequentialised AMONG THEMSELVES (edges added); obligation before any pin
retires on it: the reduced graph's outcome set = the full graph's — «reads and pure ops commute: the
state is unchanged and a single failure has one identity», stated over the fragment. No reduction is
proposed against an event.
**Where it lands** (all at `433e7490`): Syntax.lean `Stmt.unseq` + `Occ`; Machine.lean
`Cont.unseqK`/`unseqOccK` with `tail`/`withTail`/`class` arms (`:2595`, `:2630`, `:2660` — the B3
one-tail algebra), `Step` rules `unseqEnter`, `unseqPick` (premise `i ∈ ready` — the relation
quantifies the pick), `unseqOpDone`, `unseqEventDone`, `unseqGuard`, `unseqExit`, `unseqFail` (beside
`:4830–4840`), the `seqConsumption` arm `.next (.unseqK …) ↦ some (.unseqNext, |ready|)` when ≥ 2
(`:4084–4088`), `consumesUnseqNext` beside `consumesUnseqPanic` (`:4057`); StepFn.lean arms at `:355`,
`:631`, `:155`; State.lean `ChoiceSite.unseqNext` (`:339–:382`); StateWf.lean arms (`:221`, `:366`,
`:573`); MachineSound.lean `stepFn_sound` (`:172`), `step_complete` (`:506`),
`stepFn_consumption_none/some` (`:4076`, `:4452`), `stepFn_oblivious` + one flag (`:4731`); the
fragment flags (`EnumDedupCheck.lean:128`, `MultiStreams.lean:114`); the inventory §0 mirror row.
`Stmt.unseqProbe`, `Cont.probeK`, `ChoiceSite.unseqPanic` (`:608`, `:2567`, `:347`) RETIRE in the same
slice: the node subsumes the probe (DEFER/RAISE are two of its linear extensions). Sequential only.

## 4. Review findings dispositioned

| F | v2 | witness (spike; gc's draw) |
|---|---|---|
| F1 | positions = readiness; edges only from clauses; every sensitive occurrence is listed whatever follows it | `mut() + a` ∋ 1 — {1, 2}; gc 2 |
| F2 | occurrences produce values, parents consume binders, no subtree re-evaluation; sensitivity from the reads an operation performs | `a[b[0]] + mut()` = {10, 30, 40}; gc 40 |
| F3 | one `lvalue` occurrence; read and store consume it; the identity-sharing theorem | `a[i] += mut()` = {[11 20], [10 21]}, ∌ [10 11]; gc 10 21 |
| F4 | every failing occurrence is a node; no eligibility rule; the pick reaches the last one | `a[1] + b[2]` both identities; gc `[1]` |
| F5 | binders per dynamic sweep, declared at ENTER, dead at exit/panic; dominance for regions | loop: iteration 2 panics in every execution; gc panics in iteration 1 |
| F6 | one multiway pick over ready occurrences replaces the two-slot table | `x + inc() + inc()` = {0, 1, 2}; gc 2 |
| F7 | tape contract stated (§3): outcome-set equality claimed, trace preservation not; reduction obligation named | — |
| F8 | census relabelled (§6); the dynamic measurement defined; no bound claimed | — |
| F9 | 1 events/nesting/regions (§1); 2 result, projection, domain (§1); 3 range and constant-`len` exceptions, built-ins scoped (§1); 4 enumerator from the source graph (§2); 5 controls rule (§2, §6); 6 certificate kept (§7). Owed: the Lean mechanism theorem, the P(ii) census by row, the reduction lemma, the generator (§7) | X1–X3, C1–C3 |

## 5. The v1 decisions re-posed — PENDING [USER], posed not ruled

1. **E2/E12 value axis** — DISSOLVES as a mechanism question: an occurrence produces its value when
   picked; both values are members by construction. What remains is item 2. [AGENT]: E2/E12/E14's
   value axes move to (a) ENVELOPED when the rows realizing them land; ratification at that merge ask.
2. **Width of P** (which reads are occurrences): (i) today's failing kinds (`probeKind`, emit.go
   `:5450`) + events; (ii) also the mutable reads (captured/address-taken locals, globals, heap, map,
   value-receiver copies, conversion payloads) — F1's `mut() + a` needs (ii). [AGENT] recommends (ii)
   as the model, landed as slice 2 after slice 1 measures cost; (i)-only rows keep E12's narrowing.
3. **Interleaving positions** — DISSOLVES: linear extensions are the mechanism's members; there is no
   separate widening to rule.
4. **E3/E4 retirement + late structural allocations** — E3/E4 fall out of listing every phase-1
   failing occurrence (X1 is E4's shape); an allocation is an event-like node whose payload reads are
   occurrences (the allocation itself unobservable, C11) — BUG-102's class becomes slice 3's emitter
   work, not a decision. For ratification at the merge ask.
5. NEW **N1 read granularity**: `a[i]` = one occurrence (header, check, element; the machine's index
   step is one step). Splitting it widens the set with no oracle member. [AGENT] recommends one
   occurrence, recorded as a (b-n) narrowing of I-2 with an obligation.
6. NEW **N2 canonical order**: today's emission order (zero drift measurable) vs a gc-shaped per-kind
   order (assertions early). No semantic content; [AGENT] recommends today's; ratify.
7. NEW **N3 enumeration budget**: a membership row whose `unseq` width exhausts the enumerator's
   budget REFUSES by name — no silent sequentialisation. [AGENT] recommends refuse + measure first;
   posed because it can turn rows red.
8. NEW **N4 the ladder position** — §7.

## 6. The census, relabelled; the generator plan

v1's numbers (`90dc66f0`, `count.py`) are a RESIDUAL-NODE CENSUS OVER RETAINED INPUTS: 1,330 of
1,353 case directories lowered (the 23 others were not classified by the script — F8); static counts
in the CLOSING residual of event-bearing sweeps only: 40,548 sweeps, 4,833 event-bearing; 118
`unseq-probe`; 383 failing-kind and 1,010 plain-read residual nodes (hoisted argument expressions
not counted; no-event sweeps not counted; signed shifts, interface `==`, slice→array conversions not
counted; private locals included); twin 7,835 / 1,359 / 128 / 277 / 628. They locate where `unseq`
nodes would go; they bound neither nodes, picks nor evaluations (static ≠ dynamic). A REAL COST
MEASUREMENT (slice 1's exit) reports on the full corpus, the E13 family (94 rows) and the twin:
`unseq` nodes emitted per row (static); dynamic node entries; picks by bound (histogram) on the
canonical tape; rows by lane before/after with every strict→membership/confluent/`depth=N` move
named; enumeration size per membership row (trajectories, dedup nodes, distinct outcomes); fuel,
wall time, RSS against main; budget refusals by name.
**Generator** (v1 §4, corrected per F9.5; `tools/evalorder-gen`, grossmith-runner precedent): axes =
operand kind (index, slice, assertion, deref, `/`, interface `==`, map read, captured read, global,
field through pointer, value-receiver copy) × role (RHS operand, composite element, return list, send
value, call argument, `&&`/`||` region, `=` target operand, compound target, IncDec, map key) × event
(call, method, receive, `len` hoist, `make`, `append`, guard with a call) × effect (none, mutates the
operand's input, makes it fail, repairs it) × 1–2 sensitive occurrences × 1–2 events; a seeded pairwise
array (~150–200 shapes) lands as `Corpus/coverage/exec/evalorder/gen-<seed>/`. Each shape's set is
DERIVED from the source graph by §2's enumerator; checks: machine set = reference set (exact); gc draws
⊆ set (K=32 gate / K=80 slow); singleton assertions ONLY for controls with no remaining unordered pair
(argument-before-call chains, private-local operands) — `sink(a, mut())` is a two-member row; gc's
draw is recorded per shape as an observation, never «gc draws ONE» as a rule.

## 7. Cost and sequencing

| slice | content | sessions | flips / measurements |
|---|---|---|---|
| S1 | the construct end to end on P(i): Syntax/Machine/StepFn/State/StateWf/MachineSound + decoder (the positional-case-tag fragility at MachineSound, e13-b R12, is the known cost); frontend emits `unseq` for every sweep with ≥ 1 event and ≥ 1 sensitive occurrence not forced against it, or ≥ 2 failing occurrences with no event; replaces `unseq-probe`; compound/map targets as `lvalue`+`read` (`emitReadWriteTargetPhase1` `:4708`, `emitMapCompound` `:4749` — its `probeSuppress` and the early once-temps retire); `unseqPanic` retires; red-first rows for W1–W6; full `scripts/ci --diff` | 4–5 | BUG-101 ×2, BUG-104 ×5 FAIL→PASS (membership); BUG-102 `compound-call-target-vs-len` → membership (off `Expect: FAIL`); twin re-pin (probes → nodes, count reported); E13 family 94 rows re-certified, sets ⊇ old with each widening named; `binop-order` ×2 and every membership row with a sibling-event sweep re-enumerated (set equality expected; a change is a finding); strict rows outrunning the fixed streams → `depth=N` or lane moves, each listed; §6 measurement |
| S2 | P(ii); `receiverAddr` (`:5865`); allocating conversions (`:8376`) as occurrences; E2/E12/E14 → (a); E3/E4 retire; the reduction lemma | 2–3 | BUG-052's 5 rows, `noodler/latitude` ×12 + `noodler/maps` ×3, `binop-order` ×3 → membership; cost re-measured |
| S3 | structural allocations as occurrences; `structuralAllocGuard` (`:11214`) and `hoistReordersUnprobedPanic` (`:11171`) retire; the A6 residue re-derived (empty expected) | 1–2 | BUG-102's 5 remaining rows lower → membership |
| S4 | the generator + the certificate fragment (F9.6) | 1 | `evalorder/gen-*` rows born; the Lean mechanism theorem |

**Ladder position (N4, PENDING [USER]).** The construct touches `Cont` (C3 list-of-frames) and the
frame env / binder allocation (B7 `ProgramCtx`/`Store`, C4 block-scoped allocation, B6). [AGENT]
recommends **S1 now, before B7 starts**: the arc record already classes the E13 lane as «a SEMANTICS
lane, not a C-item … independent of the C-arc order» (`docs/2026-09-03_design-hygiene-arc.md`); B7
rewrites every core signature and one core-refactor lane runs at a time, so S1 and B7 must not
overlap; BUG-101/104 are wrong answers waiting; S1 declares the binders as scope temps (C4 absorbs
them) and gives `unseqK` the B3 one-tail shape (C3 is one more mechanical frame). Then B7 → C1; S2–S3
(frontend-heavy) beside P; then C3 → C4 → B6. Alternative: S1 after C3 (list-of-frames removes the
positional-tag fragility) at the price of months of red on BUG-101/104.
**Translation certificate** (master plan §7.2 F6; review F9.6) — KEPT, bounded: fragment = §2's; exit
criterion (a) for every generated shape, machine set = reference set, executable per shape in the gate;
(b) ONE Lean theorem: every `stepFn` trajectory of a well-formed `unseq` node (the decoder checks as
hypotheses) runs its occurrences in a linear extension of the node's edges, and every linear extension
is some tape's trajectory — soundness and completeness over the WIRE graph. The source→wire step stays
tested by (a), not proved: stated as the plan, not silently removed.

## 8. What v2 does not do

No concurrency claim (a concurrent observer of an unordered pair is outside this model; racy programs
refuse). No init order (E7/E8). No member for gc's early store (E5, L-016). No composite-literal
internal store order. No claim about gc's `order.go` beyond measured draws. No schema work, Lean
build, census re-run or baseline change.

## Handoff

- DECIDED [AGENT] inside the ruling: the §1 graph and its edge table; the §2 enumerator and the two
  separate checks; the §3 construct (wire, decoder checks, machine, binder lifetime, identity
  contract, multiway pick, canonical = list order, tape contract, reduction obligation); the §7 slices.
- PENDING [USER]: §5 item 2 (width of P), N1 (read granularity), N3 (enumeration-budget refusal),
  N4 (ladder position: S1 before B7); items 1/4/N2 for ratification at the merge ask.
- FIRST SLICE: S1 exactly (§7) — construct + decoder + frontend emission replacing `unseq-probe`, P(i), compound/map targets by identity; flips BUG-101 ×2, BUG-104 ×5, BUG-102 ×1; twin re-pin.
- AUDIT ASK for this note: the edge table against the pinned clauses; the identity-sharing theorem
  and the tape contract's claimed/not-claimed split; the spike's graphs against the review's witnesses.
