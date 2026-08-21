# The second PL-nitpicker review — W3.2 slice 5b (2026-08-21)

**Charter:** `docs/2026-08-20_w32-re-envelope-charter.md` §Slice 5b,
added at G0 (§11 of the first audit): once the surgery is done, the
persona returns and grades the outcome against the slice-0 findings,
supplies the deferred Q6 evidence, and feeds the opsem write-up's
structure. This is again a DESIGN audit, not a bug hunt.

**Ground truth:** branch `w32-5b` @ `521f5b57` (the post-merge main
tip), tree clean. Every `file:line` below is against that commit.
Files read IN FULL:
`GoLean/GoCore/{State,Machine,StepFn,Ops(targeted+delta),Multi,
MultiStreams,Race,EnumSpec,EnumDedupCheck,MachineEqb(structure+key
defs),EnumDedupSound(statements+headline proofs)}.lean` (~13.2k
lines), plus the w32 log (all slices), the boundary-set note, and the
POR design note. The surgery under review = slice 1 stages A–E
(Q1 tagged choice sites, Q2 step-event channel, B1 `.opDone`
post-op boundaries, B2 back-edge boundaries) + the POR slice
(SlowObs/EnumSpec, the dedup certifier, the sound-eqb tower). Slices
2–5 of the charter have NOT run; queue items routed to them (Q3→4,
Q10→5, Q11→4) are graded here as *carried*, not as failures.

**Verdict in one paragraph.** The three queue items that rode the
surgery DELIVERED, and delivered in the shapes the first audit asked
for: the choice-site census is now a datatype with a one-table policy
(the C-1/C-2/C-3 findings are structurally discharged — verified by
grep: zero bare `Choices.consume` calls remain in interpreter code);
the detector is a genuine event fold with the two worst
reconstructions (`wokenPartner`, the three-way stream replay) deleted
and the deleted-lemma tombstones honestly recorded; and `.opDone` is
one site-tagged marker, uniformly emitted at 42 completion points,
whose constructor docstring is now the best envelope statement in the
core. The POR additions are trust-surface work of unusually high
quality: `EnumSpec.lean` passes the "very dumb" test outright (64
lines; the whole meaning of a certified row is three definitions over
the unmodified driver), and the checker is readable in one sitting.
The new winces are few, real, and all second-order: the detector's
outcome discrimination now pattern-matches the B1 marker in the
POST-step pool (a coupling found by eval pins, not by types — the Q2
principle stops one level short), the `Obs` vocabulary structurally
excludes the FATAL outcome class without saying so (the slice-0 T-5
wince, untouched, now costs more because EnumSpec made outcomes a
statement vocabulary), and the eqb tower is a sixth full walk over the
still-unbundled 30-constructor `Cont` (the Q3/Q4 debt now taxes three
consumer families). On Q6 the recommendation is: do NOT unify the
signal carriers before the opsem write-up — the 34 control-transfer
rules tabulate perfectly as a 5×7 frame×signal matrix TODAY, so the
document gets its table for free as presentation, while the surgery
*grew* the code change's blast radius (the eqb tower and the dedup
chain now case on all five carriers). Details and reopen trigger in §5.

---

## 1. Q1 — tagged choice sites: DID IT DELIVER?

**Verdict: yes, fully; the census-as-code is legible AS a system.**

- **One place.** `ChoiceSite` (State.lean:207-213) is the census —
  9 constructors, one per consumption site, with the site→consuming-
  definition→envelope-statement map in the type's docstring
  (State.lean:162-206) and the scheduling subset (`{l1Sched,
  l5ExitWindow, postOp, backEdge}` — the future `Fair` quantification
  target) stated at the bottom of it. `SitePolicy`/`ChoiceSite.policy`
  (State.lean:215-256) is the ONE policy table; `Choices.consumeAt`
  (State.lean:263-266) the one combinator; `Choices.consume` is
  demoted to the raw primitive with a docstring saying interpreter
  code never calls it (State.lean:151-155).
- **Verified, not asserted:** grep at this tip finds ZERO bare
  `.consume` calls outside State.lean's own definitions — every
  remaining bare use is proof-layer case analysis
  (MultiStreams/EnumDedupSound/MultiWfSound `rcases`), which is the
  documented carve-out. The seven interpreter consumption sites all
  carry tags: `.mapIter` (StepFn.lean:621), `.appendSpill`
  (Machine.lean:946), `.l2Entry` (Machine.lean:2799), `.l2Arrival`
  (Multi.lean:853), `.l4Waiter` (Multi.lean:1039), `c.boundarySite`
  covering l1Sched/postOp/backEdge (Multi.lean:1153), `.l5ExitWindow`
  (Multi.lean:1628), plus the CLI mirrors.
- **The C-1 payoff realized.** The five-sites-three-policies mess is
  now two declared policy classes (`consumeAtOne` true/false), and the
  width-1 nuances the first audit had to *discover* are one-line
  DECLARATIONS with their load-bearing reasons attached — the
  policy-row docstrings are genuinely good (the `l1Sched` row names
  sequential conservation's hinge; the `backEdge` row carries THE
  FAIRNESS-EXPRESSIBILITY NOTE in full, State.lean:255-256). The old
  caller-side singleton special cases (L1's `[i]`, L4's `[cand]`) are
  confirmed GONE — `stepMulti` (Multi.lean:1143-1158) and `stepThread`
  (Multi.lean:1039) consult the site uniformly and the non-consumption
  is the table's row.
- **C-2 discharged as designed:** slot 0 = canonical member is now a
  per-row `canonicalSlot0` field. It is a `String` — prose-as-data,
  docstring-checked rather than machine-checked. That was the plan's
  stated shape and it is the right cost point today; noted (not
  queued) that a future `Fair`/canonicalization proof would want the
  slot-0 semantics as a definition, not a sentence.
- **C-3 discharged:** the doctrine preamble and inventory §0 now point
  at the type; the F16-style hand-sync sweeps are retired. Adding a
  site requires a constructor (exhaustiveness-checked policy match) —
  exactly the "census is a datatype" shape the first audit asked for.
- **C-4 improved, residual noted:** the L2 site's three textual
  consumers are down to two — `applySelect`'s own pick (entry path)
  and `arrivalPlan`'s (arrival path), the detector replay deleted —
  and the bound-equality argument moved from prose into the code at
  the `.cellPath` route (Multi.lean:817-823). What remains: one
  semantic latitude, two census rows (`l2Entry`/`l2Arrival`), because
  readiness is waiter-extended on one path. Declared and
  cross-referenced; carried as N-5 (§6), post-launch.

One small deviation from the boundary note, rightly made and rightly
logged: the shipped `consumeAtOne` flags differ from the note's sketch
(`appendSpill`/`l2Entry`/`l2Arrival` are `true`, vacuously at width 1
by construction) — the log's rationale (byte-identical transcription +
rfl-simp proof bridges) is correct, and the policy docstring says the
`true` is vacuous at 1 and why (State.lean:220-229). No complaint.

## 2. Q2 — the step-event channel: DID IT DELIVER?

**Verdict: yes — the detector became a fold; the event vocabulary is
principled; one structural residual survives at the outcome level.**

- **The fold is real.** `raceUpdate` (Multi.lean:1384-1547) takes
  `(sPre, tsPre, ev, m', r)` and NO stream; dispatch is on
  `ev.action`. The two reconstructions the first audit called the
  worst smear are dead: `wokenPartner` is a tombstone comment
  (Multi.lean:1212-1214), and the select-commit identity arrives in
  `.selectCommit cl` — emitted by `applySelect`'s 4th component
  (Machine.lean:2784-2807), ONE consuming definition, the sequential
  arm projecting it away (StepFn.lean:464-465). The deleted
  `raceUpdate_oblivious` is recorded where it stood
  (MultiStreams.lean:392-396: "the lemma's whole content moved into
  the types") — a model of honest deletion.
- **The event vocabulary is principled.** `StepAction`
  (Multi.lean:570-593) has seven arms and each is either (a) something
  only the step could know (`spawned child`, `paired partner`,
  `selectCommit cl`) or (b) an honest "classify from the
  pre-configuration as before" (`privateStep`, per the
  footprint-table-not-autologging decision, which this stage correctly
  did NOT relitigate). `StepEvent.picks` carries the pool-layer
  consumption with the scope deviation from the boundary note §3
  recorded IN the module docstring with its reopen trigger
  (Multi.lean:534-561) — the right way to ship a scope cut.
- **The residuals, honestly ledgered:** (i) `raceWakeEvent`'s
  `.blockedSelect` arm still re-derives `resumeThread`'s deterministic
  head-commit (Multi.lean:1281-1286) — recorded in the module
  docstring with the fold-it-too condition; shape-derived and
  stream-free, so lockstep-by-construction. Acceptable. (ii) NEW WINCE
  (N-1, §4): the `.privateStep` arm discriminates a chan/sync apply's
  outcome by matching `m'.threads[i]? = some (.opDone _ _)` in the
  POST-step pool — ten such probes (Multi.lean:1435-1539). This is the
  one place where the surgery's own B1 wrap became load-bearing for
  the detector *by shape inspection*, and the stage-C log admits it
  was found by eval pins going red, not by the build. The Q2 principle
  applied one level deeper — a `privateStep (outcome : proceeded |
  parked | panicked)` emitted by the step — would delete all ten
  probes and make the next boundary-shape change type-checked instead
  of pin-checked. Graded in §6.
- **The strengthened obliviousness story is nicer than the old one:**
  `stepThread_oblivious` now concludes same-successor AND same-event
  (MultiStreams.lean:195-209), and verdict stream-independence is a
  SIGNATURE fact. The checker (`stepAllBranchesOk`) needed no
  oblivious-detector lemma at all. Net −88 lines in MultiStreams and
  the file reads better than before the surgery.

## 3. B1 — the `.opDone` unification: site-tagged, one marker?

**Verdict: one marker, one mechanism, no sprawl; the constructor
docstring is the best envelope statement in the core.**

- **One shape.** `Config.opDone (sched : ChoiceSite) (inner : Config)`
  (Machine.lean:2295) replaced `.spawned` in place — the audit's T-6
  "use the `.spawned` mold, don't invent a second mechanism" is
  exactly what happened. Its only step is the strip
  (`Step.opDoneStrip`, Machine.lean:3567; `stepFn`'s arm,
  StepFn.lean:769), identical on both drivers.
- **The wrapping did not sprawl.** 42 emission points (22 in
  Machine.lean's applies, 20 in Multi.lean's resume/pairing/spawn),
  every one the same literal shape (`.opDone .postOp …`, or
  `.opDone .l1Sched …` at spawn's two arms), every non-wrapped
  outcome class (blocked, panicking) non-wrapped for the same stated
  reason (B3 deferred; parks are boundaries already), and the one
  subtle non-wrap — the select default-take — carries its
  envelope-neutrality argument in situ (Machine.lean:2750-2767, the
  audit-fix A-W-1). The passive pairing partner's non-wrap is argued
  at `applyPairing` (Multi.lean:874-879). This is uniformity
  maintained by convention plus grep, which at 42 sites is fine; a
  one-line `postOp`-wrap helper would centralize the convention for
  B3's eventual landing, but the per-site placement is also defensible
  (each emitter's docstring cites B1). Optional, N-4.
- **The tag design survived contact with the proofs.** Keeping
  `ChoiceSite` as the tag type (instead of a fresh 2-value type) means
  junk tags like `.opDone .mapIter c` are representable;
  `Config.boundarySite` CLAMPS them to `.l1Sched`
  (Multi.lean:1099-1104) so the non-popping policy is provable for
  arbitrary configs. The make-illegal-states-unrepresentable
  alternative was considered and rejected for a stated,
  checkable reason (the sequential-conservation lemmas quantify
  arbitrary configs — `Config.boundarySite_consumeAtOne`). A
  defensively-clamped representable-junk state is a wince I would
  normally flag; here the trade is documented at the clamp and the
  clamped behavior is the pre-widening universal one. Accepted.
- **The spawn tag is the detail that shows the design was done
  carefully:** `spawnStep` emits `.opDone .l1Sched` (Multi.lean:335),
  NOT `.postOp`, preserving BUG-040's shipped slot-0 =
  lowest-index-runnable default bit-for-bit — one untagged marker
  would have silently changed the spawn default. The docstring at the
  constructor says exactly this (Machine.lean:2286-2294).
- **B2 rode the same mechanics for free:** the back-edge boundaries
  are `atBoundary` arms + a `boundarySite` tag + the shared
  `schedSlots` menu (Multi.lean:286-288, 1101-1103, 1120-1124) — no
  new configuration, no new rule, and the envelope statement lives at
  the `atBoundary` arms with the dossier citations
  (Multi.lean:260-285). The stage-D log's "proof cost absorbed by
  stage C's generalizations" claim is consistent with what the code
  shows (two tag arms and a menu case).

## 4. NEW WINCES — what the surgery (and its speed) left rough

Ordered by how much they matter to the launch audit.

- **W-1 (= T-5 grown teeth): the `Obs` vocabulary structurally
  excludes FATAL outcomes and does not say so.** `Obs`
  (EnumSpec.lean:35-39) is ok/panic/race; `obsOf?` maps
  `.error (.fatal msg)` to `none` via the catch-all
  (EnumSpec.lean:54), and the docstring's exclusion list
  ("Deadlock, fuel exhaustion, stuck/unsupported/internal errors are
  NOT observations", EnumSpec.lean:32-34) omits fatal — the one
  excluded class that IS a differentially-compared Go behavior
  (exit 2 + fixed text: unlock-of-unlocked, go-of-nil-func). Today no
  membership row has a fatal member, so nothing is wrong; but a
  membership row whose envelope contains a fatal would silently be
  un-statable, and a cold reader of the trust surface is not told.
  The slice-0 wince (T-5, one Go-observable class split across two
  carriers) is thus not just untouched — EnumSpec promoted outcome
  vocabulary to statement vocabulary, so the split now has a
  statement-level cost. Cheap immediate fix: one docstring sentence
  at `Obs`/`obsOf?` naming the exclusion and pointing at Q8. Real
  fix: Q8's `.fataled` terminal (or `Obs.fatal`), unchanged grade.
- **W-2: the detector's post-shape probes on the marker** — §2's
  N-1. Ten `some (.opDone _ _)` matches in `raceUpdate`'s
  `.privateStep` arm (Multi.lean:1435-1539) couple the detector's
  success test to B1's wrap shape; the coupling's discovery mode
  (eval pins) is the warning. The event should say what the outcome
  WAS. Witness-to-metatheory-lite; post-launch, but do it before B3
  (the abort window will add a third outcome shape to discriminate).
- **W-3: the eqb tower is a sixth full `Cont` walk and the
  positional-soup bill arrived.** `Cont.eqbF` (MachineEqb.lean:386,
  125 lines) spells all 30 constructors; `tgtOpK`'s 11 fields force
  `andSplit11` (MachineEqb.lean:74-81) and the soundness proof walks
  every position. K-1's census is now: `panicPassthrough`,
  `recoverThroughWrappers`, `recoverResult`, `pruneIterFramesKey`,
  `pruneIterFramesAll`, `Cont.eqbF` (+ partial `pushDefer`, + the
  proofs-side Sym/Walk/Rename walks). The debt grows a consumer
  family per arc, exactly as the first audit predicted. Q3 (bundle
  `mapIterK`/`tgtOpK`) is already routed to ride slice 4's respin —
  this is fresh evidence it must not slip past it; Q4 (generic
  traversal) would now delete more code than it would have in
  slice 0. Grades unchanged, priority up.
- **W-4: the select interception's byte-identity obligation.**
  `stepThread`'s interception (Multi.lean:1055-1076) must stay
  byte-identical to `stepFn`'s `selectOpsK` apply arm
  (StepFn.lean:458-468). The load-bearing part — ONE consuming
  `applySelect` — is structurally shared, so the drift surface is
  only the 3-line defensive panic wrapping around it, and the comment
  says "byte-identical" out loud. This is the slice-0 U-2 smell
  (same family dispatched by two routes) reborn one level up, at
  minimum severity. Acceptable; fold into Q9's eventual
  uniform-dispatch cleanup.
- **W-5: the certified-fragment ladder exists twice.**
  `poolThreadOblivious` (MultiStreams.lean:87-104) and `innerVecs`
  (EnumDedupCheck.lean:100-126) walk the same flag ladder
  (blocked/opDone/spawn/select/append/mapIter), the latter re-testing
  flags after calling the former to find the N-L4/N-APP refinements.
  Layered rather than duplicated, and both total + fail-closed (worst
  case is refusal, never unsoundness) — but a third fragment class
  will want a single `FragmentClass` classifier both consume.
  Post-launch, witness.
- **Small change (noted, below the queue bar):** `SlowObs`'s proof
  layer erases the L5 tag in `execProgLoop_unfold`'s equation
  (`ch.consume 2`, MultiStreams.lean:480) — correct (bound 2 > 1
  makes `consumeAt` the raw pop) but the canonical unfolded form a
  proof reader sees loses the census tag; `StepEvent` derives nothing
  (no `Repr`), which will annoy the first person to debug an event
  stream; `schedSlots`' postOp/backEdge arms are verbatim twins
  (Multi.lean:1122-1123); U-4's `initialization` env-equality test
  and its missing "defensive; unreachable from lowered Go" docstring
  (StepFn.lean:130-137) are carried from slice 0 unchanged.

**And the cold-read test on the new trust surface, plainly:**
`EnumSpec.lean` is the best 64 lines in the core — a newcomer can
hold `Obs` + `obsOf?` + `SlowObs` in one glance and state what a
certified row means without reading any enumeration machinery
(modulo W-1's missing fatal sentence). `EnumDedupCheck.lean` (237
lines) reads top-to-bottom in one sitting; `checkCert`'s four
conjuncts (root pinned, sizes match, every node checked, every
witness replayed) are exactly the story the design note tells, and
the `nodeEqb`-as-parameter-with-soundness-hypothesis design
(EnumDedupCheck.lean:30-35, EnumDedupSound.lean:944-950) puts fuel
exhaustion on the refusal side by construction. The
checker/engine split is legible: the engine imports appear only in
CLI.lean (deletion-tested per the log), the import-direction gate
carries the isolation clause, and nothing in the statement chain
mentions `EnumDedup`. This is the strongest new work in the arc.

## 5. THE Q6 EVIDENCE — the five unwinders, post-surgery

**The question:** with the post-surgery shape in hand, how badly do
`breaking/continuing/returning/breakingTo/continuingTo` read, and
would the derived opsem document be materially more beautiful under a
frame×signal table?

**The measurements at this tip:**

1. **34 relation rules** are signal-unwinding rules
   (Machine.lean:2888-3011 + the mapIter and frame signal arms) —
   grep-counted. The executable side is five compact per-signal
   matches (StepFn.lean:648-748) that already read AS the transposed
   table: each is ~10 lines of frame dispatch.
2. **The rules tabulate with THREE footnotes.** Signals {break,
   continue, return, breakTo L, continueTo L} × frames {seq, loop,
   breakableK, labelK, mapIterK, frame, stop} fills a 5×7 matrix
   whose cells are one of four outcome forms (pass through / absorb
   to `next` / redirect to re-exec / fail closed), with footnotes for
   the `labelK` match/skip pair, `contHeadLabel`'s loop-head test,
   and the frame row's defer drain. I attempted the tabulation while
   reading; no cell resists it. The rule NAMES (`loopBreak`,
   `breakToLabelMatch`, …) are already the cell labels — N-4 of the
   first audit, still true.
3. **The surgery grew Q6's blast radius, materially.** The five
   carriers are now cased in ≥14 files, including three NEW consumers
   this arc added: `Config.eqbF`/`Cont.eqbF` (MachineEqb.lean:660,
   386), the dedup checker/soundness chain (via `threadDone`,
   `mainOutcome?`, and every Config case analysis in
   EnumDedupSound), and the widened `atBoundary`/`boundarySite`
   arms that now match signal×frame pairs directly
   (`.continuing (.loop …)`, Multi.lean:287, 1102). A
   `Config.signal sg k` unification restates all of it — metatheory
   grade, and a bigger metatheory than it was at slice 0.
4. **The surgery produced zero evidence the split taxes new work.**
   B2 added no signal rules (boundary arms only); B1 added one
   non-signal rule (`opDoneStrip`). Nothing in stages A–E or the POR
   slice would have been cheaper under unified signals; the one
   place unification would have paid this arc is the eqb tower's
   five identical `k`-only arms — ~10 lines.

**RECOMMENDATION to the opsem gate (feeds slice 6a and the deferred
Q6 ruling):**

- **Write the opsem document's control-transfer section AS the 5×7
  frame×signal matrix, without changing the machine.** The rules'
  regularity licenses the presentation directly — each cell cites its
  rule name; the three footnotes are the honest irregularities and
  belong in the document anyway. The document gets Q6's whole
  readability payoff at docs cost.
- **Do NOT land Q6 before the write-up.** The remaining payoff of
  the code change is compression (~34 rules → ~10 + a
  `signalStep : Signal → Frame → Outcome` table function), which is
  maintenance economics, not statement quality: the signals are
  mid-run control vocabulary, not part of the trust-surface
  statement vocabulary (terminal outcomes are — and THAT vocabulary's
  real gap is W-1/Q8, which is cheaper and pays more).
- **The reopen trigger, stated falsifiably:** if the 6a author finds
  the matrix does NOT render (more than the three footnotes above, or
  a cell that needs prose a rule name can't carry), that failure is
  the evidence Q6 needs; land it then, bundled with Q4's generic
  traversal (same re-proof wave, shared consumers), never alone.

## 6. THE UPDATED REFACTOR QUEUE

Grades as in the first audit ((a) blast radius, (c) payoff), plus
**launch-relevant?** — does it affect what the whole-stack audit or
the opsem write-up can honestly say, vs. maintenance that can wait.

| # | Item | Status / grade | Launch-relevant? |
|---|------|-----------------|------------------|
| Q1 | Tagged choice sites | **DONE** (stage A), verified §1 | — |
| Q2 | Step-event channel | **DONE** (stage B) with recorded pool-layer scope + reopen trigger; residuals ledgered | — |
| Q3 | Frame-payload bundling (`mapIterK`/`tgtOpK`) | CARRIED — rides slice 4's respin (G0). Evidence grew: the eqb tower is a third consumer family of the positional soups (W-3; `andSplit11`) | Post-launch, but MUST ride slice 4 — do not let it slip again |
| Q4 | Generic `Cont` traversal | CARRIED (operator discretion). Walk census now SIX + partials; deletes more than it would have at slice 0. witness | Post-launch |
| Q5 | Dead-code/dedup sweep (`stmtOpNullary` still live Machine.lean:3079/StepFn.lean:278-280; `_nt` still unused Machine.lean:747; `.next`/`.returning` frame twins still verbatim StepFn.lean:552-575/673-696; 41 `.panicking [⟨runtimeErrorValue …` singleton sites, `panicStep` helper unmade) | CARRIED, witness/none | Post-launch (rides any core-touching slice) |
| Q6 | Signal unification | **RECOMMEND: defer past 6a; table-as-presentation in the document; reopen trigger stated** (§5) | The DOCUMENT half is launch-relevant; the code half is not |
| Q7 | Structured `enterFrame` panic classes | CARRIED — the spawn hazard docstring still stands (Multi.lean:306-317); slice 1 touched spawn but did not take the opportunistic fix | Post-launch |
| Q8 | `.fataled` terminal / `Obs.fatal` | CARRIED, **priority RAISED** — EnumSpec made outcomes statement vocabulary and fatal is silently excluded (W-1). Immediate: one docstring sentence at `Obs`/`obsOf?`. witness | The docstring sentence is launch-relevant (statement honesty); the terminal is post-launch |
| Q9 | `spinePlan` + uniform `chanPlan` in stepFn | CARRIED — U-2 asymmetry intact (StepFn.lean:194-209); fold W-4's interception note in | Post-launch |
| Q10 | Granularity-in-code | CARRIED — still PRECEDES slice 5's U-5 re-audit, which has not run | Pre-slice-5, so effectively launch-adjacent if slice 5 is in the launch path |
| Q11 | Entry-identity stamps | CARRIED — correctly NOT consumed by the POR slice (logged as a judgment call); still slice 4's E9 input | Post-launch |
| **N-1** | **StepAction outcome class**: `privateStep` carries proceeded/parked/panicked; deletes raceUpdate's ten post-shape `.opDone` probes (W-2) | NEW, witness→metatheory-lite (Multi+MultiSound) | Post-launch; land BEFORE B3 |
| **N-2** | **FragmentClass classifier**: one certified-fragment ladder consumed by `poolThreadOblivious` + `innerVecs` (W-5) | NEW, witness | Post-launch |
| **N-3** | **`Obs` fatal-exclusion docstring** (W-1's cheap half) | NEW, none — one sentence | **Yes — do at 6a prep or the next touching slice** |
| **N-4** | `.opDone .postOp` wrap helper (42 sites, one shape; centralizes the convention for B3) | NEW, none/witness | Post-launch, optional |
| **N-5** | L2 one-latitude-two-rows residual (`l2Entry`/`l2Arrival`; C-4's remainder) | NEW (carried from C-4), metatheory | Post-launch |
| N-6 | Cosmetics: `StepEvent` deriving `Repr`; `schedSlots` twin arms; U-4's defensive-arm docstring | NEW, none | Post-launch |

Nothing on this queue blocks the opsem write-up. Two items touch what
6a can honestly SAY: N-3 (say the fatal exclusion) and Q6's document
half (the matrix presentation).

## 7. What is already good — said plainly (the 6a evidence base, updated)

The first audit's §9 list stands in full; the surgery ADDED to it:

1. **The census-as-code** — the policy table with load-bearing
   docstrings is now itself a piece of the opsem document (the
   latitude chapter can render `ChoiceSite.policy` almost verbatim).
2. **Envelope statements kept pace with the widening** — B1's lives
   at the `Config.opDone` constructor with both dossier directions
   cited (Machine.lean:2266-2294); B2's at the `atBoundary` arms
   (Multi.lean:260-285). The doctrine's requirement 1 held through
   the largest envelope change the machine has had.
3. **Honest deletion as a practice** — the `wokenPartner` and
   `raceUpdate_oblivious` tombstones say what died and where its
   content went. Rare and valuable.
4. **The statement-spec discipline** — `SlowObs` over the unmodified
   driver, checker soundness as the only bridge, engine deletable and
   deletion-TESTED, node equality sound-only so fuel exhaustion
   refuses. The binding constraint ("slow but obviously correct")
   is visibly satisfied by construction.
5. **Scope deviations shipped with reopen triggers** — the stage-B
   pool-layer scope cut and the stage-C tag-clamp trade are both
   documented at the decision site with the condition that reopens
   them. This is how velocity avoids becoming debt.

## 8. FOR THE LAUNCH AUDITORS — the core's design state in five points

1. **The trust chain to read, in order:** `EnumSpec.lean` (64 lines —
   the meaning of every `engine=dedup` claim), `EnumDedupCheck.lean`
   (237 lines — what is checked), `checkCertM_slowObs`
   (EnumDedupSound.lean:999 — the bridge, axiom-pinned in
   `proofs/Audit.lean`), then `ChoiceSite`+`policy` (State.lean) and
   `Config.opDone`'s docstring (Machine.lean:2250-2294) for the
   envelope story. That chain is short, and it is honest.
2. **Where review is still the only check:** (i) the footprint
   table's lockstep obligation (unchanged, by design — Race.lean's
   inventory is the audit surface); (ii) raceUpdate's ten post-shape
   `.opDone` probes (W-2 — shape coupling the types don't see; its
   eval pins are the current guard); (iii) the select interception's
   3-line byte-identity margin (W-4); (iv) `raceWakeEvent`'s
   head-commit mirror (ledgered in the module docstring). All four
   are recorded in code at their sites.
3. **One statement-vocabulary gap to know about:** fatal outcomes
   are not `Obs` members and the exclusion is currently undocumented
   (W-1/N-3). No current row is affected; any future
   fatal-containing envelope would be un-statable until Q8.
4. **The deferred-work register is load-bearing:** slices 2–5 have
   not run; Q3/Q10/Q11 are ROUTED to them, and this audit's grades
   assume those routings hold (especially Q3-rides-slice-4 — the eqb
   tower made the bundling debt strictly worse).
5. **The Q6 ruling this audit recommends** (§5): matrix in the
   document, machine unchanged, falsifiable reopen trigger. If the
   6a author overrides it, the override should cite which cell of
   the matrix refused to render.

## 9. Gate record

Docs-only slice (this note + the log entry; zero code changes):
`GOLEAN_ALLOW_NO_DIFF=1 GOLEAN_MEM_MAX=24G scripts/ci` on the fresh
`w32-5b` worktree (deps bootstrapped offline via
`scripts/setup-deps --from /home/dev/projects/golean`, Lake packages
included). Result recorded in `docs/w32-log.md` at the slice-5b
checkpoint entry.
