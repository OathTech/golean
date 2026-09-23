# Proposal to the GoLean logic team: one batched breaking window, one re-pin, and what we owe you (2026-09-23)

[AGENT] writer, GoLean semantics repo, lane `docs/roadmap-customer-alignment-0922`. Addressed to the team building the
program logic in `golean-logic` (surveyed READ-ONLY at your `main` `b2c37c1`, «Merge F2 scoped cleanup»; nothing there was
modified, built or run). Ordered by [USER] Mike, 2026-09-23, verbatim, relayed by the [AGENT] coordinator — cite as
relayed: «Can you write a note addressed at the logic team, proposing your updated design, then we'll get their review».
Provenance: [USER] = Mike's rulings (verbatim, relayed); [AGENT] = our proposals; **[inf]** = an inference about your
code or plans that you should correct. The analysis behind this note is `docs/2026-09-22_roadmap-customer-alignment.md`
(rev. 2); the rulings are in `docs/2026-08-31_qrow-rulings.md`, «The roadmap review under the customer framing».
Paths `G:` are ours; `L:` are yours. Nothing here is decided for you: §6 lists what we ask you to answer.

## 0. Summary

We propose to land the remaining shape-breaking changes to the sequential machine in ONE window and to offer you ONE
re-pin after it, with a changelog ([USER]-ruled). The window's contents, in our proposed order: (a) the sequential step
label becomes the FULL event label (memory accesses ⊕ choice picks ⊕ output — the shape the pool already emits; [USER]:
«as regular as possible»); (b) native method promotion (deletes `Func.wrapper`); (c) `Cont := List Frame`; (d) numeric
locals; (e) block-scoped allocation. Riding the label change we deliver the sequential half of the end-to-end statement
we owe you — a terminal classification (a permitted panic is not «stuck»), output observable from the sequential
relation, and the `execStmtLoop` bridge in both directions including the terminal case. We propose a stable interface in
the form you actually consume: a NAMED SET of bridge declarations whose statements we gate, a per-pin changelog, and —
optionally, your call — per-arm `stepFn` equation lemmas so your universal-equation premises rewrite by `simp` instead
of by unfolding. Deferred with no customer stake, unless you object: NaN latitude, the `unseq` confluence lemma, the
access-granularity reduction, the typed-admission profiles. We ask ten questions (§6): the window's contents and order,
whether our E6 lane precedes it, the label's type, the stable set, the equation lemmas, which form of the end-to-end
statement you need first, the timing of the records, the drops, the corpus weighting, and your planned re-pin point.

## 1. Where we are relative to your pin

Your pin is GoLean `61958f2e` (train r39 close, 2026-09-17; `L:provenance/pins.json`). Our `main` is `9269912e`
(train r47 close, 2026-09-22): 92 commits, seven merge trains (r41–r47). A «train» is one gated merge to `main`:
the full differential against `go run` green, an adversarial audit, and a re-certification receipt.

**What changed that touches you** (verified on `main` unless marked [inf]):

1. **C1 — the memory module with an access trace** (trains r41–r43). The sequential relation and the interpreter now
   emit a per-step LABEL of memory-model events: `Step : Config → Store → Config → Store → AccessTrace → Prop`
   (5-ary; was 4-ary at your pin, `G:Machine.lean:4390`@pin → `:5315`@main) and `stepFn s c ch : Except Stop
   (Config × Store × Choices × AccessTrace)` (a 4-tuple; was a 3-tuple, `G:StepFn.lean:255`@pin → `:326`@main), with
   `AccessTrace := List MemEvent` (`G:Ops.lean:1841`; `MemEvent = access | hb | attributed`). `stepFn_sound` and
   `step_complete` carry the label: `stepFn ctx s c ch = .ok (c', s', ch', tr) → Step ctx c s c' s' tr` and its
   converse `∃ ch ch', …` (`G:MachineSound.lean:1681`, `:2079`). This is the only API-SHAPE drift between your pin and
   `main`: every `∀ s ch, stepFn ctx s c ch = .ok (c', s, ch)` premise (116 `stepFn` occurrences at your tip) gains a
   fourth component, and for a pure step that component is `[]`. Also in C1: `Store.alloc` normalizes the allocated
   value and `HeapNormal` became a `StateWf` conjunct (S1) — your `wp_alloc_step` equations see a normalized cell
   [inf: no observable effect on scalar cells]; the sequential runtime no longer holds the pre-step store across a
   failing step (S3, validate-then-commit — an interpreter-internal change; the relation's rule shapes are unchanged).
2. **BUG-111** (r42): the race detector's shadow keys are canonical-path keys. Detector-only; you use no `AccessTrace`
   (0 occurrences) and no race machinery — [inf] no effect on your `WordMap` entry-identity model (B1's stamps are
   unchanged).
3. **The `unseq` construct, Stages C–E5** (r44–r47). Background, since you predate it: where the Go spec leaves the
   order of operands unspecified (spec#Order_of_evaluation: «the order of those events compared to the evaluation and
   indexing of `x` and the evaluation of `y` and `z` is not specified»), the frontend now lowers the statement to a
   dependency GRAPH of evaluation occurrences (`Stmt.unseq`), and the machine runs the graph under a scheduler frame
   (`Cont.unseqK` and its occurrence frame) that picks the next ready occurrence through a CHOICE SITE
   (`ChoiceSite.unseqNext`).
   A choice site is where the machine consults the choice tape (`Choices := List Nat`, `G:State.lean:166`) — the same
   tape your equations quantify over; consulting at bound ≤ 1 pops nothing. The graph is entered only when the
   OBSERVABILITY TRIGGER fires: some occurrence is unordered against an effectful event (a call, a receive) or against
   another failing occurrence; otherwise the legacy structural lowering is kept. The construct itself (`Stmt.unseq`,
   `Cont.unseqK`, `ChoiceSite.unseqNext`) was already at your pin (Stage B, the scheduler, then unreachable from the
   frontend); new since are the LOWERING that emits graphs (Stages C–E5), the decoder's grammar, and six `Step` rules for
   the graph-body kinds (122 → 128). The `Stmt` constructor list and the `Cont` constructor count (33) are identical at
   both ends. **[inf]** None of your fourteen fixtures (`L:examples/fixtures/*/main.go`) enters a graph: every
   statement with a call has private-local or address-of arguments and a local target (`seen = Nested(&p, &q, …)`),
   and the call-free statements (`value, present = t.values[key]`, `*seen = *p`) have no effectful event. We have NOT
   verified this by lowering your fixtures with `main`'s frontend (your tree is read-only to us); the check is one
   command per fixture (`scripts/lower-diagnose`, grep the wire for `"stmt":"unseq"`) and we will run it on the
   re-pin's dry run (§5) or on request.
4. **The decoder** (`G:NativeToIR.lean`, +774 lines: the `unseq` grammar, map-arm type checks, named refusals). Your
   fixtures' wires are re-emitted at a re-pin; the shapes you consume are unchanged unless item 3's trigger fires.

**What did NOT change.** All 33 GoLean declarations you name exist on `main` under the same names (checked: `stepFn_sound`,
`step_complete`, `run_ok_iff`, `Trace.erase`, `execProgLoop_single`, `execProgLoopOut_snd`, `program_run_iff`,
`observation_iff`, `runProgramSetupM`, `loadMany`, `enterFrame`, `enterFramePick`, `seqCont`, `stepFrameExit`,
`recoverResult`, `pushDefer`, `execStmtLoop`, `stepFnIter`, `Steps`, `seqOpCount`, `Config.abort?`). The statements of
`run_ok_iff` (`execStmtLoop … = .ok (sf, chf) ↔ ∃ n ≤ fuel, Trace …`) and `Trace.erase` (`Trace … → Steps …`) are
textually unchanged — your `adequate_execStmtLoop` (`L:Adequacy.lean:71-76`) consumes exactly these two; only `Trace.step`'s
internal equation destructures the 4-tuple. `Func.wrapper`, `Stmt.initialization` (44 `Stmt` constructors at both ends),
string-named locals, the `Cont` shape: all still there — P, C4, B6 and C3 have not landed. `ProgramCtx`/`Store` (B7) is
as you pinned it.

**First-cut changelog `61958f2e → 9269912e`** (the format we propose to maintain per re-pin, §4-ii):

| Arm / shape | Before (your pin) | After (`main`) | What a re-pin must touch on your side [inf] |
|---|---|---|---|
| `Step` arity | `Config → Store → Config → Store → Prop` | `… → AccessTrace → Prop` | `Prim.step_iff`, `Prim` (`L:Language.lean:33-41`): quantify or fix the label |
| `stepFn` result | `Config × Store × Choices` | `… × AccessTrace` | all 116 `stepFn` sites: `= .ok (c', s, ch)` → `= .ok (c', s, ch, tr)`; `step_unique`/`pure_of_stepFn` destructure one more component |
| `stepFn_sound` / `step_complete` | 3-tuple ↔ 4-ary `Step` | 4-tuple ↔ 5-ary `Step` | as above (16 + 5 uses) |
| read / write / alloc steps | silent | emit `[.access .read key]` etc.; alloc normalizes | `wp_read_step`/`wp_write_step`/`wp_alloc_step` equations name the singleton label |
| `Trace.step` | 3-tuple | 4-tuple | none (you use `run_ok_iff` + `erase` only) |
| `Step` rules | 122 | 128 (`unseq` graph-body kinds) | exhaustive `cases` on `Step` gains six arms; `Stmt`/`Cont`/`ChoiceSite` constructor lists identical |
| the wire | — | `unseq` nodes when the trigger fires; map-arm annotations | re-emit fixtures; [inf] no `unseq` node for your fourteen |

What we have not verified: a build of your tree against `main` (never attempted); whether your 151 `with_unfolding_all
rfl` and 6 `cbv` sites stay inside their heartbeat budgets once the label is in the tuple; the fixture-lowering claim above.

## 2. The proposal: one batched breaking window, one re-pin

[USER] ruling (2026-09-22/23, verbatim, relayed): «I think we'll want to give them one repin after all the breaking
changes have landed. Can we batch these together» — RULED: the remaining shape-breaking reshapes land in ONE window; you
receive ONE re-pin offer after all of them, with a changelog; no breaking change lands outside the window without a
separate ruling. Since you consume a pin, nothing on our `main` reaches you until you move it; «window» therefore means:
the offer comes after everything below, so you port your `stepFn` sites once. Names: B7/C1/C3/C4/B6/P are the items of
our 2026-09-03 design-hygiene arc (`G:docs/2026-09-03_design-hygiene-arc.md`; B7 = the `ProgramCtx`/`Store` split you
already have; C1 = §1 item 1). Proposed landing order, with the dependency reasons:

**(a) The full event label on the sequential relation** — [USER]-ruled («we should make the model as regular as
possible»), first in the window, before C3. What: `Step`'s fifth argument and `stepFn`'s fourth component become
`StepLabel := { trace : AccessTrace, picks : List PickRecord, out : List GoString }` — the three fields the pool's
`StepEvent` already carries (`G:Multi.lean:1009`: `who, action, picks, out, trace`), so the pool event becomes
`{ who, action, label : StepLabel }` and there is ONE label type at both layers. `PickRecord = { site, bound, pick }`
(`G:State.lean:457`) is one consultation of the tape at a site with bound > 1; `out` is the bytes a `print`/`println`
step wrote. Why: today output and picks are observable only from the pool (`StepEvent`), not from `Step` — your O-TRACE
(«Empty observations and heap ownership do not supply this», `L:docs/2026-09-18_logic-obligations.md` §2) and your
«observation before later failure» test (`L:docs/2026-09-22_post-f2-next-steps.md`) need an observation on the
sequential step. For your proofs: your equations gain the label (`= .ok (c', s, ch, l)`); for every step your current
fragment takes, `l.picks = []` and `l.out = []`, and `l.trace` is what C1 already gives; `Obs := Empty` can stay until
you want `Obs := StepLabel` (or its `out` projection) for A-TRACE. Alternative form (ask, Q3): one interleaved
`List Event` (`Event = mem | pick | out`) preserving gc's instrumentation order across the three kinds — more regular as a
trace, less convenient to project. Our cost: 2–3 sessions (the C1 4-tuple precedent) + the pool refactor.

**(b) P — native method promotion.** What: today the frontend synthesizes a forwarding function per PROMOTED method (a
method reached through an embedded field), marked `Func.wrapper = true`; the core carries the flag for `recover`'s
frame-skipping (`recoverThroughWrappers`) and two other consumers. After P the frontend emits no wrappers, the core
resolves `x.M` through the embedding chain, and `Func.wrapper` is deleted. Why: one method-call shape; `recover`'s rule
loses a special case; the method-set contract on the wire says «declared». For your proofs: `entry_step`'s premise
`hw : f.wrapper = false` (`L:Logic/Control.lean:42`) disappears; every `.frame targets env results ds k wrapper` pattern
(the `w` slot, 24 `.wrapper` uses) loses its last field; `recoverThroughWrappers` (9 uses) loses its `true` arm. Your
next target, `Progress.MaybeUpdate` (a pointer-receiver method, not promoted), does not involve promotion — [inf] the
direct method path is unchanged in intent. Before C3 so that `Frame.frame` is born without the slot. Cost: 3–4 sessions
+ a detector re-run.

**(c) C3 — `Cont := List Frame`.** What: the 33-constructor `Cont` becomes `abbrev Cont := List Frame` with `Frame` the
constructors minus their `k` field; the constructor NAMES survive as `@[match_pattern] abbrev`s (`Cont.seq rest env k :=
Frame.seq rest env :: k`, `Cont.stop := []`), so existing patterns elaborate unchanged. Why: `tail`/`rebuild`/unwinding
become list operations; one induction principle. For your proofs: `Control.Agrees : List Authority → Cont → Prop`,
`pushDefer` («map at the first call frame») and the `Cont.rebuild_*` lemmas become list induction; `Kernel.Triple`'s
`∀ k : Cont` is unchanged. This is NOT a context-fill law: `fill K c := ⟨mode, k ++ K⟩` exists definitionally, but we
claim no commutation theorem for it — your `recover`-vs-helper counterexample (`L:…obligations.md` §4 row 1) is real and
we agree the side condition stays yours. Cost: 3–4 sessions.

**(d) B6 — numeric locals** (`VarId := Nat`). What: the frontend numbers every local per function; `LocalEnv` is keyed
by index; source names travel as a debug table. Why: no string keys or reserved-prefix conventions inside the machine;
α-renaming disappears from the semantics. For your proofs: `Source.Context.lookup` by spelling and `LocalEnv.declare
name …` sites [inf: `L:Logic/Source.lean`, `Binding.lean`] become index-keyed; specs that name «variable `x`» name a
slot with a name table. Cost: 2–3 sessions; a parallel lane inside the window.

**(e) C4 — block-scoped allocation.** What: all locals of a block are allocated at BLOCK ENTRY; `.seq` frames carry a
fixed environment; `Stmt.initialization` (and its `Step`/`stepFn` arm, and your `wp_initialize` rule's subject) is
deleted. Why: a statement whose meaning depends on its continuation goes away; frame environments are static. For your
proofs — the honest cost: allocation ORDER changes, so `Loc.base` ids differ from today's; your `Frame.roots base n`,
`initialCells`, `declareRoots` address arithmetic [inf: `L:Readback.lean`, `Call.lean`] shifts. Observations are
address-free (pointer `==` survives any bijective renaming), so this is semantics-preserving UP TO HEAP ISOMORPHISM,
and we will disclose the exact shift in the changelog. After B6. Cost: 2 sessions + the twin re-pin.

**Not in the window, and why.** NaN latitude (BUG-094; [USER]: «if this isn't in the target, we can defer it» — floats
are outside your `ScalarTy`). The `unseq` DRF-confluence lemma (that every schedule of a data-race-free `unseq` sweep
yields the same result) — additive, matters when you reach concurrency/F4; owed, not scheduled. The reduction of the
machine's concurrency granularity to Go's access granularity (NPDRF) — restate-only as a design note; very high cost, no
stake before Raft. The typed-admission profiles — parked 2026-09-16; your boundary table puts them downstream. A
GoLean-side `Language`-instance spike — DROPPED: your `L:Language.lean` answers the shape questions.

**E6 — before or inside the window? (Q2.)** E6 finishes the evaluation-order model: the trigger refinement, the graph
grammar for non-main units, two decoder follow-ups, and — once the legacy census is zero — retiring the legacy E13 probe:
`Stmt.unseqProbe`, `Cont.probeK`, `Step.unseqProbe`, `ChoiceSite.unseqPanic` (one `Cont` constructor fewer for your
`cases k`, one `Step` rule fewer, one site fewer). ~2 sessions. Our current plan is BEFORE the window (it is removal-only
and your fixtures do not reach it [inf]); under the ruling's letter a removal is breaking, so we pose it: before (starts
now; you port once at the re-pin either way) or inside (delays nothing for you; delays E6 for us). We recommend before.

## 3. The end-to-end statement we owe you

Our charter owes «the single end-to-end labelled simulation (initialization, choice consumption, memory effects,
output, terminal priority, the refusal/domain hypotheses)» — kept in step with the interpreter. Your obligations name the
same gap from your side: **O-TERMINAL** («Uncaught panic is a terminal classification without a successful sequential
successor. It is not a value of today's Iris adapter»), **O-TRACE** (observations from the sequential step), **O-CLOSE**
(a program-level bridge without the `hr : execStmtLoop … = .ok` and `hop : seqOpCount … = 0` premises of your
`adequate_program_result`, `L:Readout.lean:25-33`), and the pool/registry half. Your two newly designed tests — «write,
call, panic: a receiver write survives a later callee panic» and «observation before later failure: the observed prefix
must survive» — are instances of the first two. Proposed STATEMENT shape ([AGENT]; one relation, fuel-free):

```
inductive LRun (pctx) : Config → Store → Choices → List StepLabel → Outcome → Prop
  | done     : c = .next .stop                       → LRun c s ch [] (.ok s ch)
  | aborted  : Config.abort? c = some (e, chain)     → LRun c s ch [] (.aborted (abortMsg e chain))
  | step     : Step pctx c s c' s' l → consumes ch l.picks = ch' → LRun c' s' ch' ls o → LRun c s ch (l :: ls) o
```

with `Outcome = ok (final store, residual tape) | aborted (Terminal)`, and the theorems: **terminal priority** — an
abort configuration has no `Step` successor (`Config.abort? c = some _ → ¬ Step pctx c s c' s' l`), so `.aborted` is not
a stuck state but a classified end; **output** — the run's output is the fold `(ls.map (·.out)).flatten`, the same fold
the pool driver already performs (`execProgLoopOut`); **choice consumption** — `ch'` is `ch` after exactly the picks in
the label (so a run with `picks = []` throughout is tape-independent, which is your `step_unique` argument stated once);
**the bridge, both directions** — `execStmtLoop fuel s c ch = .ok (sf, chf) ↔ ∃ ls, |ls| ≤ fuel ∧ LRun c s ch ls (.ok sf
chf)`; `execStmtLoop … = .error (.terminal t, out) ↔ ∃ ls, LRun … ls (.aborted t) ∧ out = fold ls`; `.error .fuelOut ↔`
every run is longer than `fuel`; **the refusal/domain hypothesis** — a refusal (`.error (.refusal r)`) has NO relation
successor, so the bridge holds under the hypothesis that no reachable step refuses on any tape; we state that hypothesis
explicitly and prove what we can of it from `StateWf` (`step_preserves_wf`) — discharging it for a syntactic fragment is
your O-REFUSAL and stays yours (we make no typed-admission claim). **Readout**: `loadMany pctx sf locs = .ok vs` gives
`Observation.normal {values, output}`; an abort gives `Observation.terminal t out` (`G:ProgramTrace.lean:63`). **Init**:
`runProgramSetupM fuel p name args ch = .ok (pctx, c₀, s₀, locs, ch₁)` stays the premise your `ProgramExecution.setup`
discharges. **The pool half**: `program_run_iff`/`observation_iff` already relate the pool driver to `ProgramRun`; the owed
piece is (i) the single-goroutine embedding without the `seqOpCount = 0` premise (a run that never reaches a registry
boundary IS a pool run), and (ii) the labelled pool relation over the same `StepLabel`.

Order of delivery: the sequential `LRun`, terminal priority, output, and the two-directional bridge ride the label
change (window item (a); 1–2 sessions on top of it); the program-level bridge for single-goroutine programs next; the
pool half when you reach E2/F4 concurrency. We ask (Q6) which form your adequacy needs FIRST: the terminal classification
(your write-call-panic test), the output prefix (your observation test), or the pool.

## 4. The interface we propose to keep stable — explained from scratch

The earlier phrasing was not understood, so plainly. You do not import an abstraction of our machine: you import
`GoLean.GoCore.Multi`/`Syntax`/`Trace`, quantify over the real `Cont`, and prove your rules by UNFOLDING `stepFn` on
concrete configurations (151 `with_unfolding_all rfl`, 113 `decide`, 35 `simp [… stepFn …]`, 6 `cbv` at your tip; your
2026-09-19 log records `cbv` exceeding its heartbeat budget on the full artifact — [inf] `stepFn`'s size is part of that
cost). A re-export module (`GoLean/Interface.lean`, which we once had and parked) would therefore not help you: you would
unfold through it. What DOES make a re-pin cheap is three things, none of them a facade:

**(i) A named STABLE SET of bridge declarations**, with their statements pinned. We promise: the names stay, the
statements change only inside the batched window, and every change is a changelog line. Proposed initial set, all
verified on `main`: `stepFn_sound`, `step_complete`, `run_ok_iff`, `Trace.erase`, `execProgLoop_single`,
`execProgLoopOut_snd`, `program_run_iff`, `observation_iff`, `runProgramSetupM`, `loadMany`, `enterFrame`, `seqCont`,
`stepFrameExit`, `recoverResult` — plus, from your census, `enterFramePick`, `pushDefer`, `execStmtLoop`, `Steps`,
`Config.abort?`, `findFunctionIn?`, `methodInfoByFuncId?` (49 and 39 uses). Mechanism [AGENT]: a tracked Lean file
`GoLean/GoCore/BridgeSet.lean`, outside the semantic core's proof graph, containing one `example : <pinned statement> :=
<name>` per member — so a statement drift FAILS OUR BUILD (fail-closed, no scan to forget), and the file's diff between
two pins IS the interface diff. Ask (Q4): what to add.

**(ii) A per-pin CHANGELOG** in the §1 table's format — arm/shape → before → after → what a re-pin must touch — written
at each re-pin offer (`docs/changelog/<from>-<to>.md`), covering the `stepFn` arms whose equations changed, the
`Step`/`Cont`/`Stmt`/`ChoiceSite` constructor deltas, the wire deltas, and any address-arithmetic shift (C4).

**(iii) OPTIONAL — per-arm `stepFn` EQUATION LEMMAS.** One lemma per statement/expression form, stated over a SYMBOLIC
continuation and proved once on our side: `stepFn_assign : stepFn ctx s (.exec (.assign tgt e) env k) ch = …`,
`stepFn_call_enter`, `stepFn_frame_exit`, `stepFn_defer`, `stepFn_return`, `stepFn_if`, `stepFn_load`, `stepFn_store`,
`stepFn_seq_nil`, `stepFn_block_enter`, …, each `@[simp]`-usable, each re-proved by us whenever the arm changes. Your
`hred : ∀ state choices, stepFn ctx state c choices = .ok (c', state, choices)` premises would then close by `simp
[stepFn_assign, …]` rather than by unfolding the whole match; where your configuration is concrete (`entry_step`'s
`simp [Kernel.invoke0, stepFn, …]`) the gain is smaller, where `k` is a variable (your CPS `Triple`) it is the whole
proof. Cost to us: ~2 sessions for the fifteen most-used arms, ~4 for all. Ask (Q5): do you want them; which arms first;
and whether to state them over the NEW event-labelled `stepFn` of the window so you port once, or over today's.

## 5. Timing and the re-pin offer

Precedents for the estimates: B7 one session; C1 three sessions + audits; each `unseq` stage one session. Proposed
sequence (one core lane; a second lane where marked ‖):

| Step | Content | Sessions | What you get at this point |
|---|---|---|---|
| now (records) | your review of this note; the final `61958f2e → main` changelog; the stable-set file; the statement note for §3 | 1–2 | a rehearsal of the re-pin with no code moved (Q7: now or with the window) |
| E6 | trigger refinement, non-main grammar, legacy probe retired | ~2 | one `Cont` ctor / one `Step` rule / one site fewer (Q2: before or inside) |
| window (a) | the full event label + the sequential `LRun`, terminal priority, output, bridge | 3–4 | O-TERMINAL and O-TRACE's semantics side; one label type |
| window (b) | P | 3–4 | `Func.wrapper` gone; one method-call shape |
| window (c) | C3 | 3–4 | `Cont := List Frame` |
| window (d) ‖ (e) | B6, then C4 | 2–3 + 2 | numeric locals; static block environments (address shift disclosed) |
| close | the re-pin OFFER | — | a tagged commit `customer-pin/<date>` on `main`; the changelog; `BridgeSet.lean` green; the differential-green receipt (`scripts/ci --diff` tail + the round's certification receipt); optional equation lemmas |

Total ≈ 13–17 sessions of ours at one lane (≈ 10–13 with the parallel lane). Each item lands through our normal gate
(full differential green, adversarial audit, merge train) — none is visible to you before the offer. With the offer we
propose a DRY RUN on our side, if the [USER] approves the access: a gitignored clone of your tip under our `deps/`, pin
bumped, `lake build` attempted, and the breakage list written into the changelog — your repo untouched. Corpus weighting
(item 7 of the review, referred to you): we can weight our differential corpus toward your features — today's:
Boolean/`uint64`/pointer scalars, one-field structs, `map[uint64]uint64` get/comma-ok/store, direct nonrecursive calls,
closures capturing by address, `defer`, `panic`/`recover`; next, from your post-F2 note: multi-field records,
pointer-receiver methods (`Progress.MaybeUpdate`), `UInt64` wrapping arithmetic, then E2's bounded byte-slice reads and
the `readOnly.recvAck` map update, then callee-panic-after-write and observation-before-failure shapes. Ask (Q9).

## 6. Questions for the logic team

1. **Window contents/order** — (a) label → (b) P → (c) C3 → (d) B6 → (e) C4: anything to add, remove, or reorder?
2. **E6** — before the window (our recommendation) or inside it?
3. **The event label** — exactly what do you want observable from a sequential step: output bytes, picks, both? In
   which type: the record `{trace, picks, out}` (the pool's shape) or one interleaved `List Event`?
4. **The stable set** — additions to the list in §4-i? Any name there you do NOT need us to freeze?
5. **Equation lemmas** — yes or no; which arms first; stated over the new event-labelled `stepFn` (port once) or today's?
6. **The end-to-end statement** — which form does your adequacy need FIRST: the terminal classification, the output
   prefix, or the pool/registry bridge? Is `LRun`'s shape (§3) usable as the source of your `Prim`, or do you want it
   projected (e.g. a labelled `Steps` with the output fold as a separate theorem)?
7. **Timing of the records** — the changelog + stable-set file + statement note now (a re-pin rehearsal), or with the window?
8. **The drops** — any objection to deferring NaN latitude, the `unseq` confluence lemma, the granularity reduction,
   and keeping typed profiles parked?
9. **Corpus weighting** — confirm or extend the feature list in §5; anything you will need within two milestones that is
   not on it (slices, strings, `range`, interfaces, goroutines)?
10. **Your re-pin point** — after which of your milestones (the receiver pilot, E2, F3) would you take the offer, and is
    there a bound on how long our window may stay open before an interim offer (C1 + `unseq` only, ported twice) is
    worth more to you than one offer?

Answers in a sentence each are enough; we will record them with [USER]/logic-team provenance in our rulings ledger and
revise the window before dispatching it.
