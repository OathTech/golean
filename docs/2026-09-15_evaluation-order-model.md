# The evaluation-order model — one relation for values, effects and failures (2026-09-15)

[AGENT] Design note, lane `design/eval-order-model-0915`, at main `a7d553f7`;
records only. Owed by step 4 of the agreed sequence — «Design note before any
lane: the evaluation-order model (09-05 F6); BUG-101/104 are resolved inside
it» ([USER] Mike agreed 2026-09-11, relayed by the [AGENT] coordinator — cite
as relayed; `docs/2026-09-11_review-dispositions.md` §4), by gate-audit F6
(`docs/2026-09-05_master-plan.md` §7.2, §3.D item 2), and by the review's §5
(«preserving one panic axis does not preserve value capture or the ordering
of effects … Do not presume that more local guards can establish the complete
contract», `docs/2026-09-11_project-review.md`). Rulings are [USER]
verbatim-as-relayed or PENDING [USER]; everything else is [AGENT].

## 0. The problem

The ANF lowering (`tools/nativefrontend/wire.go:25–30`) fixes ONE position —
after all the events — for every non-call operand; the machine reifies one
axis on top, the `unseq-probe` whose early PANIC is the `unseqPanic` pick
while an early VALUE is discarded (`docs/2026-09-05_e13-b-design.md` §3;
`GoLean/GoCore/StepFn.lean:155–169`); hoisting patches (`probeSuppress`, the
A6 guard, `structuralAllocGuard`, early once-temps) each decide a position
the spec leaves open. Waiting: BUG-101/104 (wrong answers), BUG-102 (designed
reds), the E2/E3/E4/E12 «known ≠ gc» pins (`docs/2026-08-11_latitude-
inventory.md` :784, :845, :876, :1324).

## 1. The model

**Objects, per sweep** (one statement's evaluation phase, e13-b §1; a
short-circuit RHS is a nested conditional sub-sweep):

- **O, ordered events**: function calls, method calls, receives, `&&`/`||`,
  and the built-ins `len cap min max append copy make new recover` («called
  like any other function», spec#Built-in_functions). An event's own failure
  (a `make` size panic, a nil call) belongs to the event.
- **P, sensitive operands** — non-call operands whose OUTCOME can depend on
  when they run: (i) the failing kinds (today's `probeKind`, emit.go:5450:
  index/slice, interface-keyed map read, assertion, indirection, non-constant
  `/` `%` and signed shift, interface `==`, slice→array conversion); (ii) the
  mutable reads: a global, a heap cell (deref, index, field through a pointer,
  map, slice element), a captured or address-taken local, a value-receiver
  copy. A private local or a constant is order-transparent and not in P.
- **L / S**: a target's phase-1 operands (index operands, the indirected
  pointer, a map key) are in P; its phase-2 STORE and the store's check are S.
- **Outcome**: of an operand, a value or a failure; of a sweep, the ordered
  effect prefix (output, sends, stores) and the first failure if any.

**The relation.** An evaluation is a linear order over O ∪ P ∪ S satisfying
F1–F6; the semantics is the SET of outcomes of all such orders, nothing else.

| forced | clause (pinned go1.26.5) |
|---|---|
| F1 o₁ before o₂, o₁ lexically left | spec#Order_of_evaluation «all function calls, method calls, receive operations, and binary logical operations are evaluated in lexical left-to-right order» |
| F2 an event's operands before it | ibid. «g cannot be called before its arguments are evaluated»; spec#Calls «the function value and arguments are evaluated in the usual order. After they are evaluated, new storage is allocated» |
| F3 all of `&&`/`||`'s left before any of its right; the right conditional | spec#Logical_operators «The left operand is evaluated, and then the right if the condition requires it» |
| F4 sub-operands before their operation (`a[f()]`) | structural: the operation is defined on evaluated operands (spec#Index_expressions, spec#Type_assertions) |
| F5 all of phase 1 (P ∪ O) before any of S; stores left to right; `x op= y` evaluates `x` once; `x++` ≡ `x += 1` | spec#Assignment_statements «The assignment proceeds in two phases. First, the operands of index expressions and pointer indirections … on the left and the expressions on the right are all evaluated in the usual order. Second, the assignments are carried out in left-to-right order»; spec#IncDec_statements. gc's early store is a DEVIATION (L-016), never a member |
| F6 statement positions: select operands once in source order, RecvStmt targets after; send's channel and value before communication; switch tag once, cases left-to-right/top-to-bottom; range expression once; results set before defers | spec#Select_statements, spec#Send_statements, spec#Expression_switches, spec#For_statements, spec#Return_statements |

| unordered | ground | observable outcomes |
|---|---|---|
| U1 p ∈ P vs a sibling o ∈ O (neither inside the other, not across F3) | the spec's own example `x := []int{a, f()} // x may be [1, 2] or [2, 2]: evaluation order between a and f() is not specified` (spec#Order_of_evaluation) — a VALUE latitude stated in the text | p's value before/after o's effects; if p fails, whether o's effects precede it; STATUS when exactly one of early/late fails (BUG-101) |
| U2 p vs p′, both in P | omission — the left-to-right rule's scope is O (E12(ii); I-2 / L-013) | failure identity only, when both fail: pure reads commute (E3, E4, `two-index-left-call`) |
| U3 p's position among n later events: any of 0 … n | I-2 UNSEQ (`docs/spec-interpretations.md` I-2) | value/failure at an interleaving point (e13-b §6 item 9; gc realizes endpoints only) |
| U4 receiver sub-evaluation vs argument events | U1 in receiver position — the receiver is an operand of the call (spec#Calls) | as U1 (E14 sub-axis) |
| U5 a structural allocation's payload (composite literal, `&T{…}`, method value — not an event) vs a sibling o | U1 per payload operand; the allocation itself is unobservable (C11 quotient) | as U1 (BUG-102's class) |

## 2. Where each choice lives

**The doctrine rule.** (R1) A spec-ORDERED pair is the frontend's: the ANF
lowering fixes it structurally — no choice, no tape. (R2) A spec-UNORDERED
pair with an observable difference is the MACHINE's: a tape choice consulted
where the difference is decided, never a hoisting decision (a frontend fixing
a sensitive operand's position pins latitude). (R3) The rest REFUSES by name.

**The wire.** One pair per sensitive operand with an event (or, U2, a later
sensitive operand) after it in its sweep: `{"stmt":"unseq-probe","bind":"$uN",
"expr":E}` at the operand's lexical position among the hoists, and
`{"expr":"unseq-use","bind":"$uN","expr":E}` in place of the operand — in the
residual, a target's operand list, or a LATE once-temp. The decoder
(`GoLean/NativeToIR.lean:199`, :1205–1223 today) pairs them by name within
one sweep and refuses an unpaired or doubly-bound name. Non-event once-temps
(a compound target's address or key, an allocating conversion, a structural
allocation) bind LATE — at the residual — never at the lexical position:
gc's `safeExpr` discipline, permitted by F2/F5.

**The machine.** `Stmt.unseqProbe` gains the binder: a VALUE binds `$uN` in
the frame env (an ordinary temp write; the probed expression stays pure,
e13-b §3); a PANIC is the unchanged `unseqPanic` pick (`GoLean/GoCore/
State.lean:347`, :381; `Machine.lean:4830–4840`). New: `Expr.unseqUse`, its
frame `Cont.useK` (own `FrameClass`, like `.probe`), site `ChoiceSite.unseqValue`:

| configuration | site | bound | slot 0 (canonical = today) | slot 1 |
|---|---|---|---|---|
| `.panicking _ (.probeK _)` | `unseqPanic` (E13, unchanged) | 2 | DEFER | RAISE |
| `.retV v (.useK $u k)`, env `$u` = some w, w ≠ v | `unseqValue` | 2 | LATE `v` | EARLY `w` |
| `.panicking _ (.useK $u k)`, env `$u` = some w | `unseqValue` | 2 | LATE: the panic | EARLY: `.retV w k` |
| `.retV v (.useK $u k)`, env `$u` = none or = some v | — | 1 | `v` | — |

Equality is the machine's structural `BEq GoValue` (`GoLean/GoCore/Value.lean:
1001`). The bound is a function of the configuration (as `repanicCollapseWidth`
is): two `seqConsumption` arms beside `Machine.lean:4088`'s, `Step` rules
`useLate`/`useEarly`/`useAgree` (merge invariant). CONSULT ON DIFFERENCE is
the load-bearing choice: a pop only where the order is OBSERVABLE, no stream
re-indexing (the E13 §7 concern), slot 0 byte-identical to today, and the
same envelope as consulting at the probe (coinciding members collapse).

**Today's hoists, classified** (emit.go at `a7d553f7`):

| today | class | disposition |
|---|---|---|
| call/method/receive hoists in emission order (`hoist` :2934, `pushHoist` :5420); `len`/`cap`/`min`/`max` when an event follows (`sweepOrderedEventAfter` :10843, BUG-062); `append`/`copy`/`make`/`new`/`recover` | F1, F2 | keep |
| short-circuit wrapper (`emitBinary` :8159); `probeSuppress` on select/range targets (wire.go:89–95) | F3, F6 | keep |
| `unseq-probe` on `probeKind` operands left of an event (`emitExpr` :5272) | R2, panic half only | the probe/use pair — slice 1 |
| the residual reads every non-call operand LATE: E12's call-first value pin, E2's call-rule pin (`Machine.lean:4295` block) | R2 violated on P∖probeKind — a silent position pin | pairs once P widens to the mutable reads — slice 2; the machine's LATE evaluation IS slot 0, no arm moves |
| `emitReadWriteTarget` :11999 → `$p := &x[$f]` (:4708); `emitMapCompound` :4749 `$k := t[k]` under `probeSuppress` (:4750) | R2 violated: EARLY once-temps (BUG-104) | once-temps bind LATE, the read inline and paired — slice 1 |
| allocating conversion hoisted EARLY when an event follows (`allocatingConversion` :8376) | R2: EARLY pin on `s`; the LATE member missing | hoist LATE over `unseq-use(s)` — slice 2 |
| structural allocations at the lexical position, payload evaluated there (`structuralAllocGuard` :11214; BUG-102) | U5: EARLY payload pin | allocations hoist LATE (before the first event consuming them, else the residual), payloads paired — slice 3 |
| `receiverAddr` path unprobed (:5865; E14 singleton) | R2 gap | the implicit `&x` through the hook — slice 2 |
| narrowed A6 guard (`hoistReordersUnprobedPanic` :11171) | R3 | shrinks per slice; retires when the unprobed residue is empty |

## 3. BUG-101 and BUG-104 inside the model

**BUG-101** (`docs/BUGS.md:6156`; `assert-ok-early-len-hoist`): `iv.(int) +
len(b[j:]) + func() int { iv = "s"; println("mut"); return 1 }()`. U1: p =
`iv.(int)` (P(i), and a read of the captured `iv`) vs o₂ = the closure call;
`len` is o₁ (F1; F2 puts `b[j:]` inside it). Members: EARLY → 6, `mut`, ok
(gc); LATE → `mut`, then `interface conversion: interface {} is string, not
int` (the machine today, the probe discarding 3). Lowering: `unseq-probe $u1
iv.(int); $c1 := len(b[j:]); $c2 := <closure>(); return unseq-use $u1 iv.(int)
+ $c1 + $c2`. Tape: the probe binds `$u1 = 3` (no pop); the events print
`mut` and set `iv`; the late evaluation panics with `$u1` bound →
`unseqValue` bound 2: slot 0 the panic, slot 1 `6`. Row → membership, width
2, {ok 6; panic} ∋ gc; `slice-value-early-len-hoist`: {12, 22}.

**BUG-104** (`docs/BUGS.md:6365`; `compound-call-target-vs-call`): `x[fnine()]
+= wit(5)`. F1: `fnine` before `wit`; F4: `fnine` before the index. U1: p =
the READ `x[$f]` (P(i), phase-1 material of `x = x + wit(5)`, F5) vs o =
`wit(5)`; the STORE's check is S. Members: EARLY → `f`, then `index out of
range [9] with length 1` (the machine's `$p := &x[$f]`, alone — ∉ gc); LATE →
`f`, `wit 5`, the panic (gc). Lowering: `$c1 := fnine(); unseq-probe $u1
x[$c1]; $c2 := wit(5); compound-assign target x[$c1] read (unseq-use $u1
x[$c1]) rhs $c2` — the
address is computed at the store, the read is inline. Tape: the probe PANICS
→ `unseqPanic`: RAISE = EARLY; DEFER → `wit 5`, the late read panics with
`$u1` unbound → LATE. Two members ∋ gc. Map spelling `m[t[k]] += wit(5)`:
`unseq-probe $u1 t[k]; $c1 := wit(5); $k := unseq-use $u1 t[k]; map-compound-
assign m $k …` — a LATE once-temp, so read and store see one key; the same
two members; `emitMapCompound`'s `probeSuppress` retires. BUG-104's five rows
and BUG-102's `compound-call-target-vs-len` become membership rows.

## 4. Generated interaction tests

A small tracked generator (`tools/evalorder-gen`; precedent: the grossmith runner) over:

| axis | values |
|---|---|
| operand kind (P) | index, slice, assertion, deref, `/`, iface `==`, map read (iface key), captured-local read, global read, field-through-pointer, value-receiver copy |
| role | RHS operand, composite element, return list, send value, call argument (F2 control), `&&` RHS (F3 control), `=` target operand, compound target, IncDec target, map key |
| event | call, method call, receive, `len` hoist, `make`, `append`, `&&` with a call in its RHS |
| the event's effect on the operand | none, mutates its value, makes it fail, repairs it |
| sensitive operands / events after | 1 or 2 operands (both failing, one, neither) × 1 or 2 events (the U3 point, once enveloped) |

A seeded pairwise covering array (~150–200 shapes of the ~24,600-point
product) lands as `Corpus/coverage/exec/evalorder/gen-<seed>/` rows. A
REFERENCE ENUMERATOR in the generator (F6's «bounded prototype») computes each
shape's member set from §1 — positions per operand, DEFER×RAISE permutations
for failures — and the check is threefold: the machine's enumerated set = the
reference set (exact); gc's draws ⊆ the set (K=32/K=80 per the 2026-09-03
sampling ruling, `docs/coverage-suite-structure.md`); the F2/F3 controls are
singletons. HONEST LIMIT: sampling establishes observed ⊆ modeled, never
maximality — gc draws ONE member per shape; the others rest on §1's argument
and on gc realizing them on other kinds. Modeled ⊆ Go-permitted is argued
from the clauses, not measured. No translation certificate (F6's last item):
the lowering is checked against the reference set by enumeration, not proof.

## 5. Decisions the model needs — PENDING [USER], posed not ruled

1. **The E2/E12 value axis** (master plan §5.4 «now»; BUG-101): (a) ENVELOPE
   via the probe/use pair; (b) keep the (b) call-first pin, BUG-101 red.
   [AGENT] recommends (a): the value latitude is the spec's own example, gc
   realizes EARLY on assertion/slice kinds so no pin holds its draw, and
   consult-on-difference confines pops to observable rows.
2. **The width of P**: (i) failing kinds only (fixes BUG-101/104; the
   plain-read pin — `noodler/latitude/*`, BUG-052 — stays a (b-n) narrowing
   with an obligation); (ii) P(i) ∪ P(ii) as §1 states, at ≤ one extra pure
   evaluation per mutable read in an event-bearing sweep (≤ 1,010 nodes, §6).
   [AGENT] recommends (ii) as the model, landed as slice 2 after slice 1 has
   measured the double-evaluation cost.
3. **Interleaving positions** (U3): widen {lexical, residual} to {0 … n} by
   re-emitting the probe after each event. No oracle member lies there (gc
   realizes endpoints) — decided by argument; pops unchanged. [AGENT]
   recommends yes, last: the doctrine's machine is the weakest Go permits.
4. **[AGENT] decisions for ratification at the merge ask, not gates**: E3/E4
   fall out of pairing every failing operand that has a later failing operand
   even with no event between (DEFER×RAISE gives the permutations; pops only
   when ≥ 2 fail) — their pins retire into (a), their strict rows move to
   membership; structural allocations hoist LATE (§2); E13's site is untouched.

## 6. Cost and sequencing

**Spike** (`docs/evidence/2026-09-15_eval-order-model-spike/`, static, at
`a7d553f7`; 1,330 of 1,353 case directories lower, 23 refuse by design).
Corpus: 40,548 sweeps, 4,833 event-bearing (12%); 118 `unseq-probe` today;
in event-bearing sweeps 383 failing-kind operand nodes (slice 1's pairs) and
1,010 plain mutable-read nodes (slice 2's; both upper bounds, private locals
included); 10 EARLY once-temps of BUG-104's shape; 17 E2-shaped statements.
Twin: 7,835 sweeps, 1,359 event-bearing, 128 probes (the e13-b record), 277
failing-kind, 628 plain-read nodes. So ≤ ~1,400 pairs corpus-wide, at most
that many extra pure evaluations, and POPS bounded by the rows where a sibling
event changes an operand's outcome — ~30 known (BUG-101 ×2, BUG-052 ×7,
`noodler/latitude/*` ×15, `binop-order/operand-panic-vs-call` ×3).

**Slices** (sessions are estimates):
1. **Value axis + BUG-104** (~3 sessions): the §2 machine construct
   (`canonicalSlot0` = LATE; oblivious-fragment flag; `stepFn_sound` cases;
   decoder pairing); the binder on today's probes and the use in residual/
   target operands; LATE once-temps in `emitReadWriteTarget`/`emitMapCompound`.
   Red-first first: 3–5 E2 value rows in target position (`x[iv.(int)] =
   mut()`, `mut` changing `iv`, the early assertion succeeding). Flips:
   BUG-101 ×2, BUG-104 ×5 FAIL→PASS as membership rows; BUG-102's
   `compound-call-target-vs-len` lowers → membership (off its `Expect: FAIL`
   line); the twin pin moves. Full `scripts/ci --diff`.
2. **P widens; receiverAddr; allocating conversions** (~2–3 sessions):
   `sensitiveKind` = `probeKind` ∪ P(ii) (the lifter's capture set + an
   address-taken pass); E2's call-rule block becomes «the LATE position»;
   E2/E12/E14 → (a); BUG-052 ×7, noodler ×15, binop ×3 → membership; E3/E4 via
   probes without events (§5.4). Measure fuel/time on the full corpus.
3. **Allocations hoist LATE** (~1–2 sessions): BUG-102's structural class
   lowers; `structuralAllocGuard` retires; the A6 residue is re-derived.
4. **Interleaving positions** (PENDING §5 item 3; ~1–2 sessions).

Every slice moves inventory rows E2/E3/E4/E6/E12/E13/E14, the doctrine register's known-≠-gc sentence, BUG Cases lines and the §0 mirror with it.

## 7. What this note does not do

No concurrency-order claim (the latitude propagates into sequenced-before —
mem#model delegates to spec#Order_of_evaluation — but a concurrent observer of
an unordered pair is outside this model; racy programs refuse). No init order
(E7/E8). No change to E13's ruling or its `unseqPanic` site. No member for
gc's early store (E5, L-016). No composite-literal internal store order (the
spec's `{a: 1, a: 2}`; `maps/map-literal-duplicate-eval-order` pins it). No
claim about gc's `order.go` beyond measured members. No translation certificate.

## Handoff

- DECIDED [AGENT]: the §1 model; R1–R3; the probe/use pair with consult-on-difference and LATE once-temps (§2); BUG-101/104 as U1 pairs resolved by it (§3); the four-slice order (§6).
- PENDING [USER]: §5 items 1–3 (value-axis gate, width of P, interleavings); item 4 for ratification at the merge ask.
- FIRST SLICE: §6 slice 1 exactly — `Expr.unseqUse`/`Cont.useK`/`ChoiceSite.unseqValue` + decoder pairing + binders on today's probes + LATE once-temps for compound/map targets + 3–5 red-first E2 value rows; expected flips BUG-101 ×2, BUG-104 ×5, BUG-102 ×1 → membership PASS; twin pin moves.
- GATE BEFORE IT STARTS: §5 item 1 ruled (a) — otherwise slice 1 reduces to BUG-104's LATE once-temps alone.
- AUDIT ASK for this note: the F1–F6/U1–U5 classification against the pinned clauses; the consult-on-difference envelope claim (= consult-at-probe); the spike's definitions (`count.py`).
