# G-C3 design note — `Cont := List Frame` (window row 4, packet C)

STATUS: **PROPOSED — HARD-STOP design gate. The [USER] passes or amends it. Nothing here is decided until the [USER] rules
(§5).** [AGENT] design writer, 2026-09-29, branch `docs/gc3-design-0929` forked from `train/r55` @ `fb93f822`, with P landed.
Inputs: `docs/2026-09-03_design-hygiene-arc.md` (C3; G-C3 RULED in principle [USER] 2026-09-04, relayed);
`docs/2026-09-04_reasoning-surface-plan.md` §3.C3, §5.4; charter row 4; window plan row 4; packet C brief
`docs/codex-briefs/2026-09-24_packet-C-continuations.md`; logic team response §4/§Recommendation and note 2026-09-28
(requests 6, 7); `docs/2026-09-28_method-promotion-handoff.md`; `GoLean/GoCore/Machine.lean` at `fb93f822`.

## 1. What changes and why

**The count at this tip.** `inductive Cont` (Machine.lean:3353) has **33 constructors**: `stop` plus 32 frames, each with
exactly one `k : Cont`. `probeK` survives ([USER] 2026-09-27). P changed one frame: `frame targets tenv results defers k fid`.
The `wrapper` field is gone, and `fid : FuncId` now comes AFTER `k` (logic team request 6, [USER] 2026-09-28). So `k` is no
longer last everywhere. The brief's «OLD argument order (`k` last)» is wrong for `frame` and gets corrected at refresh (D3).
The ruled 2026-09-04 text says «31 constructor names». The correct count is now 33.

**The change.** Add `inductive Frame` with 32 constructors, one per non-`stop` frame. Each keeps its fields verbatim, minus
`k`. Then define `abbrev Cont := List Frame`. Each old name becomes an `@[match_pattern] abbrev` with its current argument
order, for example `Cont.stop : Cont := []`, `Cont.seq rest env k := Frame.seq rest env :: k`, and
`Cont.frame t te r ds k f := Frame.frame t te r ds f :: k`. With these, every existing pattern and term (`stepFn`, `Step`,
`signalStep`, `seqConsumption`, the eqb/hash walks, the tests) elaborates unchanged. The operations become list operations:
`Cont.tail` is `tail?`-shaped (`[] ↦ none`); `withTail` replaces the tail under the head; `Cont.class` is the head's class
via a new `Frame.class` (`[] ↦ .stop`); `Cont.rebuild` is list recursion; `pushDefer`, `seqCont`, `recoverAtDeferred`,
`recoverResult`, `panicPassthrough`, `stepFrameExit`'s frame handling, `Cont.locSup`/`ownSup` and `Cont.eqbF` are
re-expressed on the list.

The brief's §3 still lists `recoverThroughWrappers` and `Cont.recoverTransparent`. P deleted both. The refresh drops them.

**Gain for the logic team.** Their `Control.Agrees : List Authority → Cont → Prop`, `pushDefer` («map at the first call
frame») and the `Cont.rebuild_*` lemmas become ordinary list induction: one `cons` case plus `cases` on a flat frame, instead
of 33-way recursion. `Kernel.Triple`'s `∀ k : Cont` does not change. Their words: «a useful simplification, not a
prerequisite for our CPS bind».

**What it is NOT.** It is not a context-fill law. `k ++ K` becomes available definitionally, because `Cont` is a `List`. We
name no `fill` and claim no commutation theorem. The logic team's `recover`-vs-helper counterexample is real, and that side
condition stays theirs (proposal §2 (c)). It is also not a `Config` reshape (D1). And it changes no rule, pick, choice site,
wire or behaviour.

## 2. Decisions

**D1 — GENUINE: narrow the 2026-09-04 ruled text.** That ruling also covered «`Config := Mode × Cont`; `fill` is append»,
tied to the `EctxLanguage` instance. That claim was withdrawn 2026-09-05 (F3), and the proposal disclaims a fill law.
- (a) C3 is `Cont := List Frame` only. `Config` keeps its 10 constructors, and no `fill` is defined.
- (b) Also reshape `Config := Mode × Cont`: every `Config` pattern rewritten, a second refactor no one has asked for.
- **Rec (a).** The arc doc records the amended G-C3; (b) can return as its own gate if ever wanted.

**D2 — GENUINE, low stakes: where the request-7 unwinding equations go.** These are `panicPassthrough` over seq/block glue,
`panicResumeK` with an unrecovered chain, `CallSite.deferPanic` entry, and stripping a frame whose defer list is empty.
- (a) Leave them in packet D, as the coordinator dispositioned 2026-09-28 (`docs/2026-08-31_qrow-rulings.md`). D states
  equations over the FINAL shape, after C4 has reshaped frame entry and scope exit.
- (b) Deliver them in C, now in list form, and re-state them after C4.
- **Rec (a).** C's walk laws (D6) are the list-shaped base D reuses.

**D3 — routine: shape and naming.** `Frame` is a separate `inductive` and `Cont` an `abbrev` of `List Frame` (not a
`def`, not an inductive kept with nil/cons views). `Frame` constructors keep the old names and field order minus `k`; every
view keeps its CURRENT argument order (for `frame`, `k` before `fid`); `k`-only frames (`breakableK`, `boolK`,
`panicArgK`, `probeK`) become nullary; `.stop ↦ []`. Rec: as stated; reordering or renaming would edit every site for no gain.

**D4 — routine: fuel and hash behaviour preserved exactly.** `Cont.eqbF` spends one unit of fuel per frame, as today,
so exhaustion at `stateEqbFuel` and dedup verdicts are unchanged; `EnumDedup.contDepth` keeps its values. `sizeOf` numbers
change, but only as a termination measure; `Cont.sizeOf_tail_lt` is re-proved AS STATED.

**D5 — routine, required: C re-pins `BridgeSet.lean`.** C holds the core, so BridgeSet is its responsibility (window plan
§2). The pins are `example : T := @name`. `Cont` still prints as `Cont`, so most pins should stay byte-identical. The report
lists every pin that changed and why. Either way, the full file elaborates in C's gate.

**D6 — routine: list laws.** C proves the old equations under new names (`pushDefer_eq`, `seqCont_eq`, `recoverResult_eq`,
already present and kept, and `panicPassthrough_eq`). It re-proves `Cont.rebuild_*`, `withTail_tail`, `tail_withTail` and
`rebuild_locSup` by list induction under the same names and statements. New lemmas are added to the core audit's required
list. Nothing already on that list is removed.

## 3. Acceptance (from the brief §5; zero behaviour change)

1. `GOLEAN_MEM_MAX=48G scripts/capped scripts/ci --diff` is green with the baseline UNCHANGED (3791 = 3554 / 237). No
   `baselines/` edit. A moved row means STOP. `scripts/capped scripts/check-core-audit` passes, and the required list is kept
   (plus D6's additions).
2. The whole-corpus choice trace is byte-identical. `scripts/choice-trace-corpus --dump` runs with the pre-C3 binary (built
   in `.tmp/pre-c3` at the fork base) and with the post-C3 binary. `diff -r` on the `dump-*`/`results-*` files is EMPTY. The
   only exclusions allowed are timestamp/commit header lines, each named.
3. The twin is byte-identical. **The wire does not change**: C3 touches no file under `tools/nativefrontend`, and nothing in
   `NativeToIR.lean` builds a `Cont` (checked at `fb93f822`). `scripts/check-frontend-pins` is green with `baselines/pins/`
   untouched. The twin and `multipkg/mini-raft-twin` rows are unchanged in (1).
4. Every coherence theorem (`stepFn_sound`, `step_complete`, the driver/trace/run/observation bridges, `StateWf`
   preservation) and every packet A/B statement is proved AS STATED. `Step`'s rule count is recorded before and after, and
   must be equal. At `fb93f822` no packet A/B statement matches `Cont` structurally: `Prefix.lean` and the BridgeSet rows
   mention `.stop`/`.frame …` only as terms, which the views preserve. So the expected list of list-shaped restatements is
   EMPTY. Any such restatement the lane finds needed is listed in the report and not silently accepted.

## 4. Estimate and risk

The estimate is **3–4 sessions**, as planned: 1 for type, views and walks; 2–3 for re-proving the `cases k`/`induction k`
proofs in MachineSound, StateWf, StepFn, PrefixFacts, Machine, EnumDedup, MultiSound, Race and the tests.

**The main risk is elaboration cost.** An `@[match_pattern]` view unfolds to `List.cons (Frame.x …) k`. That makes
`stepFn`'s large match, and `fun_cases stepFn` (MachineSound:1688, StepErrors:792) and `fun_cases stepFrameExit`,
nested-pattern compilations over `List` then `Frame`. This can raise elaboration time and heartbeats, which is the logic
team's pain point. It can also renumber the positional `case caseN` tags. Renumbering is a local proof edit, not a behaviour
change. A second, smaller risk is dot-name resolution: `.seq` resolves through `Cont` only when the expected type is
syntactically `Cont`. In goals already unfolded to `List Frame`, the lane spells `Cont.seq` out. Per-view `@[simp]` fold
lemmas handle goals that `split`/`fun_cases` leave unfolded.

**Measurement (in the lane, before and after, same box, capped, locked).** `scripts/capped lake env lean -Dprofiler=true
-Dprofiler.threshold=100 <file>` on `Machine`, `StepFn`, `MachineSound`, `StateWf`, `MachineEqb`, `StepErrors` and
`BridgeSet`: per-file wall time plus the profiler's elaboration / match-compilation / tactic totals. Also recorded: the whole
`lake build golean` wall time, the `fun_cases stepFn` case count, every `maxHeartbeats` setting, and the differential gate's
wall time (a frame push now allocates a cons cell). Any module slower than 1.5×, or any NEW or RAISED `maxHeartbeats`, is
reported with the numbers and the lane stops for the coordinator. The permitted fallback is a LOCAL explicit list-form
match at the costly site, listed in the report. `stepFn`'s rules do not change.

## 5. Decisions for the [USER]

1. **Pass G-C3 as `Cont := List Frame` only.** `Config := Mode × Cont` and «`fill` is append» are dropped from the
   2026-09-04 ruled text (D1). Rec: YES.
2. **Leave the request-7 unwinding equations in packet D**, stated after C4, as dispositioned 2026-09-28 (D2). Rec: YES.
3. **Accept D3–D6 as routine lane choices** (field order kept, `frame` has `k` before `fid`; fuel/hash preserved; C
   re-pins BridgeSet; list laws added to the audit list), and refresh the packet C brief accordingly (33 constructors; the
   `k`-last and deleted-helper corrections; §3 of this note as acceptance). Rec: YES.
4. **Accept §4's elaboration-cost threshold** (1.5× per module, or any heartbeat raise, means a reported stop) as the lane's
   stop rule. Rec: YES.
