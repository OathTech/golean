# Lane A1 — shortcut census: the simplifying-assumptions register + the latitude inventory

STATUS: [AGENT] assessment artifact (fidelity assessment, lane A1;
plan `docs/2026-08-31_fidelity-assessment-plan.md`). Produced
2026-08-31 on branch `fidelity-assessment`. Scope: EVERY set-aside in
`docs/2026-08-11_essence-of-go-doctrine.md` (the register, all 7
entries including discharged ones) and
`docs/2026-08-11_latitude-inventory.md` (all 1465 lines), each
re-derived under the new goal (semantics-only product; lower bound =
everything real Go does, upper bound = everything the standard
permits, incredibly well validated). Old justifications are NOT
self-certifying; every KEEP below carries a fresh argument.

Abbreviations: D = `docs/2026-08-11_essence-of-go-doctrine.md`,
L = `docs/2026-08-11_latitude-inventory.md`. Line numbers at this
worktree's tip (branch `fidelity-assessment`, base `main` 118d31aa).

## Summary table

| Verdict | Count | Rows |
|---|---|---|
| KEEP | 22 | A1-02, A1-04, A1-11, A1-12, A1-13, A1-17, A1-18, A1-20, A1-21, A1-22, A1-25, A1-27, A1-28, A1-29, A1-30, A1-31, A1-32, A1-33, A1-34, A1-38, A1-40, A1-41 |
| REOPEN | 21 | A1-01, A1-03, A1-05, A1-07, A1-09, A1-10, A1-14, A1-15, A1-16, A1-19, A1-24, A1-26, A1-35, A1-36, A1-37, A1-39, A1-42, A1-43, A1-44, A1-45, A1-46 |
| ESCALATE | 2 | A1-06, A1-08 |

(45 verdict-bearing rows. ID hygiene: A1-23 is unassigned — a
drafting artifact, left so cross-references stay stable; A1-47 is a
record-only row riding A1-20's verdict.)

### The 5 highest-stakes rows

1. **A1-07 — the racy-program refusal's completeness** ("racy →
   refused" is per-RUN and per-enumeration, not per-PROGRAM; NPDRF is
   a draft statement that is refutable as written; the DRF-SC premise
   quantifies over programs). Touches C2, C3, C4.
2. **A1-09 — the allocator-quotient discharge is now orphaned**
   (theorem `Frame.allocatorIndependence` and its design note left
   the repo with the reasoning park; and R15 shows gc realizing a
   NON-injective address labeling observable by pointer equality —
   outside the quotient's injection class). Touches C3, C4.
3. **A1-42 — the inventory's own completeness argument** is
   heading-granularity + audit-driven; every external prod (CH2O
   prior-art, grossmith fuzzing, launch audit) found a missing row,
   and E12's admitted follow-on axes are still uncensused. Touches
   C3, C4.
4. **A1-15 — E7 hidden-dep init order is still UNGUARDED**: a
   soundness-direction (observed-∉-modeled) silent-divergence class,
   with a LOW-cost detector queued since 2026-08-11 and never built.
   Touches C1, C2.
5. **A1-05 — one implementation / one platform / one GOMAXPROCS
   evidence base** (register #3 + §8 entry 9): every "believed
   MAXIMAL" envelope and every version-tracked pin rests on gc
   go1.26.5 linux/amd64 GOAMD64=v1. Touches C2, C4.

(Close sixth: A1-01, the B3 abort-window deferral — its "no clean
oracle observable" premise looks refutable by a deferred-print probe.)

---

## Part 1 — the doctrine's simplifying-assumptions register (7 entries)

- **A1-01** | Register #1 residue (i): the abort window at panic
  terminals (B3) — the moment any goroutine reaches `.panicked` the
  program aborts on every stream; no post-raise partner progress is
  modeled | D:109 (residue (i)); L:236–239 (C3), L:314–334 + 703–705
  of `docs/2026-08-20_w32-boundary-set.md` (the G1 deferral);
  `GoLean/GoCore/Multi.lean` (`panicMsg?` classified before stepping)
  | ORIGINAL: deferred at G1 because "no observed member needs it" —
  every U-1 probe member is admitted by B1+L5, and post-raise progress
  is "distinguishable only by output-interleaving with the panic
  message on stderr — no clean oracle observable in our harness" |
  FRESH: the deferral's evidence premise is weaker than it reads. The
  U-1 probe (wake-then-abort) never separated post-raise progress; the
  "no clean observable" claim is probably FALSE: a worker that runs
  `defer print("A")` before `panic(...)` puts a definitionally
  post-raise event on STDOUT, and a spinning main printing "B" gives a
  stdout-ordering observable ("B" after "A" = post-raise partner
  progress). If gc exhibits it — plausible, since gc runs other
  goroutines during unwinding — that is observed ∉ modeled TODAY, the
  doctrine's own always-red class. The deferral was legitimate
  scheduling triage in the W3.2 arc; under the new goal an unprobed
  potentially-red class cannot stay deferred on an untested
  no-observable claim | VERDICT: REOPEN — (S) run the directed
  deferred-print probe first; if gc exhibits post-raise progress, the
  B3 window lands in the L5 mold (M, the boundary-set note already
  designed it: bound-2 site at `panicMsg?`) | C2, C3.

- **A1-02** | Register #1 residue (ii): ∀-stream termination of
  spinner shapes is the liveness tier's `Fair` question | D:110–112;
  L:155–159 (C2's non-vacuity note) | ORIGINAL: fairness is a
  claim-layer (reasoning-side) question; B2's back-edge site is what
  makes `Fair` non-vacuous | FRESH: post-split this repo makes no
  ∀-stream termination claims, and the semantics-side obligation — the
  back-edge choice site existing so a fair scheduler is EXPRESSIBLE —
  is met in code (`ChoiceSite.backEdge`, Multi.lean:1101–1103). The
  residue is real but lives in the reasoning repo's claim shapes.
  NOTE: `FairStream` itself no longer exists in this repo (grep
  empty), so the doctrine's pointer is dangling here — recorded in
  A1-46 | VERDICT: KEEP (the semantics-side half is discharged by the
  site; the claim-side half is out of this repo's scope by the
  [USER] split decision) | C3 (marginal).

- **A1-03** | Register #1 residue (iii) + register #5: scheduling
  points are registry/back-edge-granular, not per-instruction; the
  gap to full interleaving is the NPDRF reduction obligation | D:
  108–112, 134–142; L:129–132 (C1 "NOT maximal absolutely"),
  L:150–153; `GoLean/GoCore/NPDRF.lean` | ORIGINAL: sound where
  scheduling is unobservable between points for race-free programs;
  the NPDRF/mover line (Xiao et al. ICTAC 2018, Lipton movers, CHESS)
  is the named classic; the mover theorem "resumes over the widened
  point set (slice 5)" | FRESH: the architecture is coherent and the
  classic lineage is right, but the load-bearing statement is
  explicitly a SCAFFOLD: `NPDRF.lean`'s own header says
  `NPDRFReduction` is "a DRAFT STATEMENT — no theorem in the repo
  claims it, nothing may cite it … it is REFUTABLE as written
  (obstruction 4)", with 6 recorded obstructions (allocator
  interleaving non-commutation among them). So TODAY the claim
  "registry-granularity behaviors = full-interleaving behaviors for
  DRF programs" is a conjecture with a known-wrong first formalization.
  Everything concurrency-side ("believed MAXIMAL at registry
  granularity", C1/C4/C5/C8) is conditioned on it. Post-split the
  obligation is also HOMELESS: NPDRF.lean sits here (inert,
  Prop-level, destined for extraction per the split plan) while the
  proof effort is reasoning-side — see A1-08 | VERDICT: REOPEN — (L)
  weaken the statement past obstruction 4 and prove, or (S interim)
  add the explicit scope sentence to every concurrency envelope's
  "believed MAXIMAL" that it is maximal-at-granularity conditional on
  an UNPROVED reduction | C2, C3, C4.

- **A1-04** | Register #2: sequential evaluation-order latitude pinned
  per axis (gc's point where pinnable, OURS where compiler-internal,
  go/types' for hidden-dep init), E3/E5/E7 carried as deviation
  records "queued for re-envelope" | D:113–124 | ORIGINAL: velocity
  scaffolding; each pin a recorded debt; "permanent deviation records"
  wording deliberately rejected | FRESH: as a REGISTER ENTRY the
  wording is now accurate and honest (the 2026-08-12 correction did
  its job); the substance is graded at the per-axis rows A1-14/15/16.
  The register's own framing survives re-derivation: pins are debts
  with queue positions, and the bug-definition reading (a probed
  gc-elsewhere observation is an observed-∉-modeled candidate) is
  exactly the new goal's lower-bound demand | VERDICT: KEEP (the
  entry; the axes it covers are reopened below) | C2, C3.

- **A1-05** | Register #3 (+ §8 entry 9): the differential oracle is
  ONE implementation (gc) at ONE version (go1.26.5) on ONE platform
  (linux/amd64, GOAMD64=v1), effectively one GOMAXPROCS regime |
  D:125–126; L:1315–1321 (§8 e9) | ORIGINAL: no cross-implementation
  lane exists yet; XIMPL noted per-row where it would bear (R1 width,
  R2 upper end, R4 fusion, R9/R11 texts, E2 operand-first) | FRESH:
  under "incredibly well validated" this is the single largest C2
  exposure, and the register states it honestly but UNDERSELLS the
  scope: it is not just that the lower bound has one witness family —
  several rows' ENVELOPE ARGUMENTS quietly inherit the platform
  (R4's no-fusion singleton is platform-scoped; R1's 64-bit is
  host-inherited including the NEGATIVE lane's acceptance via
  go/types on the host; R6's refusal hides a real cross-target value
  divergence). A version sweep (previous gc) is nearly free; a
  GOOS/GOARCH sweep and a gccgo/tinygo feasibility probe are bounded
  experiments; each buys a different class (drift detection; width/
  endianness/fusion; envelope-vs-gc-point discrimination). Lane B
  owns the measurement design; this census confirms the register
  entry cannot be KEEP under the new goal | VERDICT: REOPEN — (M)
  the oracle-matrix program (version sweep S, platform sweep M,
  second-implementation probe M) | C2, C4.

- **A1-06** | Register #4, the POSITION: SC-only interleaving within
  DRF; racy programs refused; "racy semantics is undefined by Go and
  unmodelable as a testable artifact today, a position the plmm
  record shows is state-of-the-art-aligned, not a shortcut" |
  D:127–133; L:393–430 (C10) | ORIGINAL: DRF-SC promise (mem#model,
  Boehm–Adve) makes SC sound for accepted programs; go_mem's
  report-and-terminate license is a refusal license; plmm: no language
  has a satisfactory formal racy semantics (OOTA unsolved) | FRESH:
  three corrections to the position's WORDING, then the decision. (a)
  "Undefined by Go" is false by the project's own pinned sources:
  mem#restrictions gives racy programs a BOUNDED semantics (word-sized
  reads see actually-written values, no out-of-thin-air; the prior-art
  note `docs/2026-08-17_prior-art-fg-and-memory-model.md`:72–73, 111
  says exactly this — "invalid-but-bounded", "less like C and C++").
  (b) "Unmodelable as a testable artifact" is overstated: operational
  limited-outcomes models exist in the literature (Fava/Steffen/Stolz's
  operational weak-memory-with-channels semantics for Go); what is
  true is that the OOTA frontier is unsolved everywhere and that the
  limited-outcomes envelope has NO DIFFERENTIAL ORACLE (gc -race halts;
  plain gc exhibits one point) — the honest ground for refusal is
  cost + unvalidatability, not impossibility. (c) "State-of-the-art-
  aligned" remains TRUE for the refusal itself — every comparable
  stack (Goose/Perennial, Gobra, CH2O's UB analog as our REFUSED
  class) draws the same boundary — but the alignment argument was made
  for a VERIFIER; this repo is now a SEMANTICS product, and for a
  portable Go semantics, permitted ⊆ modeled FAILS at every racy
  program a conforming non-halting implementation runs. That is a
  scope boundary on C3, and only the [USER] can set it | VERDICT:
  ESCALATE — decision: "C3's upper-bound claim is scoped to DRF
  programs; the mem#restrictions limited-outcomes envelope is
  declared OUT of the product's scope (recorded as the one normative
  behavior class the model refuses rather than models) — yes or no?"
  If yes: fix the register's wording ("undefined" → "bounded but
  oracle-less"; S). If no: a limited-outcomes racy tier is an L-sized
  arc with no differential validation story — say so before choosing
  | C1, C3.

- **A1-07** | Register #4, the REFUSAL's own soundness: "racy programs
  refused fail-closed" — does racy → refused actually hold? |
  D:132–133; L:393–430 (C10); `GoLean/GoCore/Race.lean` (detector +
  footprint inventory), `GoLean/GoCore/Multi.lean`:1168–1196
  (`raceUpdate` fold; "races fail closed per run, on every run where
  the conflicting accesses execute"), Multi.lean:1635 (fold on every
  pool step); `GoLean/GoCore/NPDRF.lean` (the coupling's statement);
  `scripts/diff-coverage`:354–386 (lane criteria) | ORIGINAL: the
  detector is HB-complete-by-construction per run (FastTrack
  skeleton, event-fold, no choice consumption); the racy lane
  requires "every enumerated path refuses + one -race red sample";
  under-approximations U1–U5 individually argued benign or closed;
  the registry-vs-full-interleaving gap is NPDRF's obligation |
  FRESH: the refusal is honest PER RUN, but the register's sentence
  reads PER PROGRAM, and the per-program claim has four open holes.
  (1) DRF-SC quantifies over PROGRAMS (all-SC-executions-race-free ⇒
  SC), so giving SC semantics to the non-refused runs of a program
  that is racy on OTHER schedules is not covered by the Boehm–Adve
  premise; the machine has no program-level acceptance judgment —
  only the corpus apparatus approximates one by enumeration. (2) The
  enumeration that approximates it is fuel-bounded and
  tractability-bounded (the stage-C log's "intractable five" left
  exhaustive certification; strict lane runs 3 streams only), so a
  race whose accesses co-execute only on unexplored schedules or
  paths passes silently with SC semantics — exactly the "racy
  program slips through" failure mode the mandate names. (3) The
  granularity half of completeness is NPDRF, which is a draft and
  refutable as written (A1-03): a program DRF at registry granularity
  but racy under fine interleaving is refused on NO path. (4) The
  footprint's recorded under-approximations (U2 chan len/cap
  uninstrumented — spec-argued benign; U4 sync-object internals —
  misuse-only) are each argued, but the argument chain is per-row
  prose, not a theorem. Mitigations that ARE real: detection is
  HB-based (fires when both accesses execute, regardless of adverse
  interleaving), the confluent lane's enumeration refuses on any
  refusing path, and refusals never count as passes. | VERDICT:
  REOPEN — (S) rewrite the register/C10 sentence to the true claim
  ("racy executions refuse; program-level refusal holds exactly as
  far as enumeration reaches and the NPDRF conjecture holds"); (S)
  add a guard that concurrency-featured rows cannot sit in the
  strict lane without a recorded reason; (L) the NPDRF program
  (shared with A1-03) | C2, C3, C4.

- **A1-08** | Post-split OWNERSHIP of the DRF/NPDRF soundness
  obligation (register #4/#5's structural half) | split plan
  `docs/2026-08-31_repo-split-plan.md` (Prop-level relation "stays
  here, inert, until its extraction slice"); `GoLean/GoCore/NPDRF.lean`
  present at tip; CLAUDE.md ("This repo makes NO verification
  claims") | ORIGINAL: (pre-split) the reduction line was slice 5 of
  the W3.2 arc — one repo, one owner | FRESH: the refusal boundary is
  a SEMANTICS-product claim (C10 is what makes SC-only honest), but
  its soundness theorem is verification work slated to leave with the
  reasoning extraction. If NPDRF/mover work migrates out, this repo's
  own doctrine cites an obligation whose statement, proof effort, and
  eventual theorem live in another repo pinned AGAINST this one — a
  circularity nobody has ruled on | VERDICT: ESCALATE — decision:
  "does the NPDRF reduction (and the per-run→per-program refusal
  argument) belong to the semantics repo's validation story, or is it
  a reasoning-repo import this repo's claims may cite? Name the owner
  and the citation direction." | C3, C4.

- **A1-09** | Register #6: sequential allocation addressing,
  DISCHARGED BY QUOTIENT, conditional on the pointer-equality-only
  observation surface | D:143–155; L:432–463 (C11's (q) upgrade,
  re-opening condition) | ORIGINAL: `Frame.allocatorIndependence`
  (executable frame theorem note §5b) proves every conforming
  injective address relabeling observationally equal; condition:
  modeling `%p`, pointer order, `unsafe`, or any address-exposing
  channel re-opens it | FRESH: three problems. (1) THE EVIDENCE IS
  ORPHANED: at this repo's tip neither the theorem
  (`proofs/GoLeanProofs/Frame/AllocIndep.lean` — park branch only;
  `git grep allocatorIndependence` over GoLean/ is EMPTY) nor the
  design note (`docs/2026-08-13_executable-frame-theorem.md` — not in
  the tree) exists; nothing in this repo's build re-checks the
  discharge. A (q) row whose theorem is off-repo is, for THIS
  product's readers, a (b) pin with a citation. (2) THE CONDITION'S
  GUARD is real but implicit: the frontend fails closed on `%p`
  (fmtdesugar.go's verb-set default arm), `unsafe`, and uintptr
  observations — adequate today, but no single recorded sentence says
  "these three refusal sites ARE the quotient's guard", so a future
  fmt/unsafe extension can silently break the condition. (3) THE
  CONDITION IS ALREADY TOO WEAK AS STATED: pointer EQUALITY is inside
  the modeled surface, and R15 (L:1120–1148) shows gc realizing a
  NON-INJECTIVE labeling on zero-size allocations (`runtime.zerobase`
  collapse — two model cells, one gc address, `==` observably true
  where the model says false; standing red pin
  `pointers/zero-size-address/escaped-same`). Injective renamings
  cannot reach that member, so the quotient's class does not cover
  gc's realized allocator on zero-size cells; entry 6 and R15 never
  cross-reference | VERDICT: REOPEN — (S) re-home or re-label the
  discharge (either the theorem's statement+check returns with the
  extraction story, or the entry downgrades to (b)-with-external-
  theorem at this repo); (S) write the guard sentence naming the
  refusal sites; (S/M) sharpen the condition to non-zero-size
  allocations and fold R15's envelope in | C3, C4.

- **A1-10** | Register #7: unbounded memory / allocation never fails;
  runs start from an empty heap | D:156–173 | ORIGINAL: standing
  idealization, not a gc-pin, no re-envelope obligation — the
  too-wide direction does not threaten theorem transfer to real runs
  that allocate successfully; domain conditions state the model's
  domain | FRESH: the idealization argument survives — it is the
  standard operational-semantics memory idealization (CompCert's
  memory model idealizes similarly), and widening it buys nothing
  without resource-bounded claims. But under the new goal it
  COLLIDES with the doctrine's own bug definition (D:32–35:
  "if a conforming Go implementation does something our machine
  cannot, that is definitionally a bug… always red"): a real gc run
  that OOMs (`fatal error: out of memory`, exit 2) is observed
  behavior no machine stream exhibits — observed ∉ modeled BY
  DESIGN, and the doctrine never carves it out. The lower-bound
  claim is silently scoped to "runs whose allocations succeed";
  honest, but unstated | VERDICT: REOPEN — (S, doc-only) add the
  carve-out sentence to the doctrine (the bug definition excludes
  resource exhaustion, named as such) and the same scope note
  wherever C2 is stated. The idealization itself: keep | C2, C3.

## Part 2 — the latitude inventory, row by row

Rows already covered above are not repeated (C10→A1-06/07;
C11(q)→A1-09; C2/C3 granularity→A1-03; B3→A1-01).

- **A1-11** | C1/C4/C5/C8 — the ENVELOPED concurrency rows' "believed
  MAXIMAL at registry granularity" | L:109–138, 250–269, 270–289,
  339–369 | ORIGINAL: spec-silence + MM blocking rules argue the
  upper bound; envelope-width review argued no admitted member is
  outside conforming Go | FRESH: for each row the demonic width at
  the site is genuinely spec-argued (the anchors are verbatim and the
  absence-anchors are the right evidence form), and the too-wide
  direction is transfer-safe. The maximality qualifier "at registry
  granularity" is doing ALL the work — that condition is A1-03's
  conjecture. With that dependence stated, these rows are the
  inventory at its best | VERDICT: KEEP (conditional on A1-03's
  scope sentence landing) | C3.

- **A1-12** | C6 — select clause choice weakened from "uniform
  pseudo-random" to possibilistic "any ready clause"; distributional
  facts out of scope by declaration | L:291–313 (C6);
  `docs/2026-08-04_nondeterminism-doctrine.md` (the declaration) |
  ORIGINAL: support-equality: the envelope's support equals the
  spec's; no-distributional-claims rule | FRESH: re-derived, this
  holds. Any FINITE observation sequence has non-zero probability
  under uniform choice, so no finite differential observation can
  distinguish the possibilistic model from the spec's distributional
  text — support equality is exactly what a demonic semantics can
  and should claim. The cost is real but claim-side: no
  probabilistic-liveness property (e.g. "the second clause is
  eventually taken almost surely") is expressible — a consumer
  caveat worth one sentence in the row | VERDICT: KEEP (add the
  consumer-caveat sentence — trivial) | C3.

- **A1-13** | C9 — global deadlock pinned to gc's detect-and-classify
  (vs a conforming silent hang) | L:371–391 | ORIGINAL: observable
  difference is temporal only; within a terminating-run corpus the
  pin and envelope coincide; widening weakens claims for zero gain |
  FRESH: correct as argued — the only conforming alternative
  behavior (hang) has no finite observation, so modeled ⊆ permitted
  holds and permitted ⊆ modeled fails only at a member with no
  observable content. The message/exit pin rides R9's class. This is
  a justified permanent pin | VERDICT: KEEP | C3.

- **A1-14** | C7 (+§8 entry 12) — a woken parked select head-commits
  the first wake-ready clause; no L2 re-draw at wake | L:315–337,
  1333–1338 | ORIGINAL: gc's wake outcomes are arrival-order
  outcomes (the waking event commits one sudog), each realized by a
  prompt-wake L1 schedule — path-structural narrowing, [ANALYSIS]
  not theorem; re-argue on wake-machinery changes | FRESH: the
  gc-direction (lower bound) argument is sound. The UPPER-bound
  direction has an unprobed corner: a select parked with TWO clauses
  on the SAME channel, woken by `close` — one registry event makes
  both clauses wake-ready simultaneously, so "any wake-ready clause"
  has width 2 and no arrival-order schedule can split one event; our
  machine deterministically head-commits clause order. If the spec's
  uniform-choice sentence reaches the wake path (the row's own
  reading: a woken select is "still a select choosing"), the second
  member is permitted ∉ modeled on that shape. Also note the
  re-argue TRIGGER was defined pre-B1/B2 and the wake machinery DID
  change (resumeThread's classification moved to the marker) — the
  re-argument this row promises on wake-machinery change is owed by
  its own terms and was not recorded | VERDICT: REOPEN — (S) probe
  the two-clauses-one-channel wake shape against gc and re-run the
  coverage argument post-B1/B2; (M) wake-path L2 draw only if the
  probe or the reading demands it | C3.

- **A1-15** | E7 — hidden-dependency init order pinned to go/types'
  point, gc KNOWN elsewhere, UNGUARDED | L:595–628; §7 item 3
  (L:1257–1262); frontend grep: no hidden-dep detector exists in
  `tools/nativefrontend/` at tip | ORIGINAL: standing deviation
  record with a queue position; the interim fail-closed frontend
  detector is LOW cost; full envelope MODERATE | FRESH: this is the
  census's worst live combination: soundness-DIRECTION (results over
  our order do not transfer to gc), SILENT (no refusal — any new
  hidden-dep program lowers without complaint; only the one known
  fixture is red-pinned), and CHEAP TO GUARD (the row itself prices
  the detector LOW). It has sat queued since 2026-08-11 through
  multiple arcs that shipped larger items. Under a mandate whose
  first target is silent shortcuts, an unguarded known-≠-oracle
  class with a priced-low guard cannot stay queued | VERDICT:
  REOPEN — (S) build the fail-closed hidden-dep-shape detector NOW;
  (M) the conforming-orders envelope stays queued behind it | C1,
  C2.

- **A1-16** | E3/E4/E5 — inter-target operand order, targets-vs-RHS
  panic order, early store across the phase boundary: pinned to OUR
  points, gc probed elsewhere (E3/E5) | L:526–583; §7 item 5
  (L:1267–1272); D:113–124 | ORIGINAL: gc's realization is
  compiler-internal and unpinnable; divergence cannot escape panic
  selection into side effects (calls hoisted); queued for the
  membership/panic-identity envelope treatment | FRESH: these are
  standing observed-∉-modeled candidates on the SEQUENTIAL side —
  the doctrine's always-red class — held open only by the queue.
  The containment argument (panic-identity-only observable) was
  probed and is credible, which bounds the blast radius; but "the
  observable is only which panic wins" is itself the claim a richer
  observable would break (E3's own F2 note records this). The
  panic-identity membership mechanism is one design serving three
  axes plus E12/E13's family | VERDICT: REOPEN — (M) the
  panic-identity membership envelope (§7 item 5, promoted: it is the
  only queue item that clears recorded sequential reds) | C2, C3.

- **A1-17** | E6 — `len`/`cap` hoist discriminating shapes REFUSED |
  L:584–594 | ORIGINAL: a coverage refusal that exists because
  realizing gc's point inside E3/E4's latitude needs unbuilt
  linearization; reach calibrated (goose-parity cliff F23) | FRESH:
  fail-closed, named-cause, reach-measured — the honest form. The
  cost calibration (whole-package export kills via method refusals)
  is a C1 frontier fact for the feature-ladder lane, not a fidelity
  defect. Retirement condition exists (rides A1-16's mechanism) |
  VERDICT: KEEP (retire with A1-16) | C1.

- **A1-18** | E8 — multi-file declaration order narrowed to the go
  command's file-name sort | L:630–639 | ORIGINAL: spec delegates to
  "the order presented to the compiler"; the go command sorts;
  revisit only if a target ships a non-go-command build | FRESH: the
  spec's latitude here is latitude over BUILD SYSTEMS, not over
  executions of a fixed build; pinning to the ecosystem's sole
  deployed build system with a named revisit trigger is a justified
  idealization for a portable semantics whose input artifact is a
  go-command package | VERDICT: KEEP | C3.

- **A1-19** | E12/E13/E14 (+E2) — the structural call-first family:
  frontend-ANF pins on operand/sibling/receiver order, incl.
  E13's PROBED both-directions divergence (gc panics the assertion
  first where the machine runs the calls) and E14's owed F2 ruling |
  L:717–775 (E12), 777–851 (E13), 855–871 (E14), 496–525 (E2) |
  ORIGINAL: spec-silent or quote-grounded latitude; realization is a
  frontend normalization; E13: "no pin may be taken" (census row
  only); all ride E2's re-envelope | FRESH: the honesty machinery
  here is exemplary (E13 refusing to pin either axis is exactly
  right). But E13 is ANOTHER standing known-≠-gc member (assertion
  axis) in the always-red class, and the family's re-envelope is
  "until E2 opens, no new machine arms" — i.e., the whole family's
  debt is gated on the family's most expensive member. The
  panic-identity membership treatment (A1-16's mechanism) covers
  E12/E13's observables without opening E2's machine arms — the
  rows say so themselves | VERDICT: REOPEN — rides A1-16 (one
  mechanism, five consumers: E3, E4, E12, E13, E14's panic sites);
  E2's full two-point envelope stays queued behind XIMPL evidence |
  C2, C3.

- **A1-20** | E9 residual — delete-prune rewrites only same-goroutine
  continuations; cross-goroutine delete during another goroutine's
  range unpruned | L:672–681 | ORIGINAL: such a shape is already
  racy by the pick-time read footprint (U1 closed), so the narrowing
  is unobservable for accepted programs; obligation triggers at the
  first non-racy-red cross-goroutine-range case | FRESH: the
  argument reduces to "every cross-goroutine map write during a
  range is a race" — true at the footprint (`mapIterK` reads the
  live cell every pick; a concurrent write conflicts), so any
  observing program refuses before the narrowing could show. Sound —
  but note it leans on A1-07's refusal completeness for its
  unobservability, one more consumer of that chain | VERDICT: KEEP
  (conditional on A1-07's chain; the trigger condition stands) | C3.
  [2026-09-02 [AGENT] annotation — frozen artifact, text above left as
  written: the phase-2 re-derivation (`p2-keeps-a1.md` A1-20) REFUTED
  this KEEP's premise — the unpruned case is a DRF (handshake-ordered)
  cross-goroutine delete, which the detector never refuses — and the
  Tier-5 slice `t5-e9-prune` CLOSED it by the pool-level
  `pruneForeign` (Multi.lean); the "unrealizable" member is
  gc-exhibited (~87% with one intervening insert). Inventory E9 REOPEN
  → CLOSED; evidence dir
  `docs/evidence/2026-09-02_e9-cross-goroutine-prune/`.]

- **A1-21** | E10 — `==`-equal map-key retention pinned always-replace
  | L:683–698 | ORIGINAL: spec-silent; matches gc where pinned;
  exposure enumerated (float/complex/string/interface/array/struct
  keys); transfer caveat recorded | FRESH: a genuine two-member
  latitude with the observable enumerated and version-tracked; the
  other member has no witness implementation and the re-envelope is
  one arm when XIMPL evidence arrives. Correctly parked | VERDICT:
  KEEP | C3.

- **A1-22** | E11 — runtime-check order within one operation pinned to
  gc | L:700–713 | ORIGINAL: message identity is already gc-pinned
  (R9); an order envelope without a message envelope buys nothing |
  FRESH: the coupling argument is right — check ORDER is observable
  only through message TEXT, and R9 pins text; widening order alone
  is incoherent. Permanent-pin-with-R9 is the honest disposition |
  VERDICT: KEEP (rides R9's caveat) | C3.

- **A1-24** | R1 (+§8 entry 6) — `int`/`uint`/`uintptr` pinned to 64
  bits, including the NEGATIVE lane's acceptance via go/types on the
  host | L:873–896, 1288–1296; §9 flag 2; `GoLean/GoCore/Value.lean`
  :32–34 (verified: still no site-level caveat) | ORIGINAL: one
  concrete width keeps the machine executable and matches the only
  oracle; parameterization worthless without a 32-bit oracle |
  FRESH: the pin is fine; the RECORD is not — the inventory itself
  flagged the missing site-level envelope statement in 2026-08-11
  (§9 flag 2, "owed" repeated at §8 e6) and it is STILL absent from
  Value.lean, meaning the singleton-narrowing rule the project's own
  doctrine imposes (every pin carries a site caveat) has a two-week-
  old known violation. Parameterization stays XIMPL-gated | VERDICT:
  REOPEN — (S) write the Value.lean site caveat (hours); (L,
  gated) width parameter when a 32-bit lane exists | C3, C4.

- **A1-25** | R2 — append spill capacity: declared PRAGMATIC SUBSET
  [newLen, max(32, 2·growth)] of an unbounded spec latitude |
  L:898–914 | ORIGINAL: envelope ⊇ gc across probed regimes,
  version-tracked by three escaping-regime pins; "widen deliberately
  if a toolchain leaves the window; never narrow" | FRESH: the spec
  latitude ("any capacity ≥ newLen") is UN-ENUMERABLE — a maximal
  envelope is not a finite object, so a declared subset with
  membership tripwires and a widening rule is the strongest honest
  form available; the -race allocator landing on OTHER members is
  live in-envelope validation. modeled ⊊ permitted here is
  irreducible and recorded | VERDICT: KEEP | C3.

- **A1-26** | R3 — `[]byte(s)` / `[]rune(s)` conversion capacity
  singleton cap=len; gc KNOWN outside on the escaping path (bytes)
  and even on small shapes (runes: the 32-rune buffer, probed cap
  32) | L:916–940; §7 item 4 (L:1263–1266); §8 entry 10 | ORIGINAL:
  shipped before the append-spill precedent; queued at priority 4,
  priced LOW (the append mold, one arm + one membership pin) |
  FRESH: identical in kind to pre-widening BUG-021 — a PROBED real
  behavior outside the model, i.e. the doctrine's own red class,
  guarded only by a prose caveat; the rune arm has NO agreeing pin
  at all (a red case was measured and deliberately not added). The
  fix has been the queue's best value-per-cost since 2026-08-13 and
  remains unbuilt — the same queue-discipline finding as A1-15 |
  VERDICT: REOPEN — (S) do it (both arms, the row already contains
  the design) | C2, C3.

- **A1-27** | R4 — float fusion/extra-precision narrowed to per-op
  rounding, platform-scoped | L:942–958 | ORIGINAL: matches the
  oracle platform (GOAMD64=v1 emits no FMA); tripwire
  floats/fma-shape; choice-space is whole-DAG rewritings, wrong
  shape for a Choices site | FRESH: the wrong-shape argument is
  real and the tripwire is the right guard; but the entry is the
  clearest instance of A1-05's platform scoping — gc/arm64 runs of
  fusable shapes are ALREADY outside the envelope, so the C2
  sentence "observed ⊆ modeled" is true only with "on linux/amd64
  GOAMD64=v1" attached. Keep, with the scope surfaced at every C2
  statement (A1-05's work) | VERDICT: KEEP (scope-condition owned
  by A1-05) | C2, C3.

- **A1-28** | R5 — float division by zero narrowed to no-panic |
  L:960–968 | FRESH: spec grants the latitude but no conforming
  panicking implementation is known to exist; the narrowing matches
  every observed implementation and the widening is one arm behind
  XIMPL/ARCH evidence. Textbook record-and-wait | VERDICT: KEEP |
  C3.

- **A1-29** | R6 — out-of-range float→int conversion REFUSED |
  L:970–979 | FRESH: the latitude is real and CROSS-TARGET DIVERGENT
  (amd64 0x8000… vs arm64 saturate) with no oracle for the envelope;
  refusing is the only resolution that is neither a silent pin nor
  an unvalidatable guess. Fail-closed with named cause at the site |
  VERDICT: KEEP | C1, C3.

- **A1-30** | R7 — NaN payload narrowing (canonical quiet NaN;
  operand-bits propagation), first-classified 2026-08-22 with
  rejected alternatives recorded | L:981–1013 | FRESH: unobservable
  in-language at the modeled surface (math.Float64bits out of
  scope); the row's own honesty apparatus (recording it as a FIRST
  classification, rejecting (q) because no theorem exists) is the
  standard the rest of the corpus should meet. The re-decide trigger
  (math landing) is the right condition | VERDICT: KEEP | C3.

- **A1-31** | R8 — WaitGroup counter pinned to gc's bit layout |
  L:1015–1028 | FRESH: DOCS underdetermine only at misuse-scale
  deltas (≥2^31); the pin matches the sole oracle and diverging
  implementations are hypothetical. Permanent-pin candidate stands |
  VERDICT: KEEP | C3.

- **A1-32** | R9 — runtime panic values/messages pinned to gc's
  strings | L:1030–1048; §8 entry 8 | FRESH: the spec explicitly
  unspecifies these; the pin is what makes the strict equality lane
  exist at all, and the standing caveat (no message-content claim
  transfers beyond gc) is recorded. The alternative (message
  envelopes) dissolves the differential's decisive signal for zero
  fidelity gain. This is a load-bearing, correctly-priced pin |
  VERDICT: KEEP | C3, C4.

- **A1-33** | R10 — abort-line rendering pinned to gc's
  preprintpanics, fail-closed at eface-identity/method-call/
  multi-line edges (BUG-004 open) | L:1050–1062 | FRESH: not spec
  behavior at all — pure runtime realization; the unmodelable edges
  refuse with red pins rather than guess. The deep dependency
  (allocation identity) is A1-09's territory and correctly
  cross-referenced | VERDICT: KEEP | C1, C3.

- **A1-34** | R11 + R12 — sync-misuse fatal class and exit-code/
  terminal classification pinned to gc | L:1064–1088 | FRESH: DOCS
  underdetermine the CLASS; gc's throw realization is the only
  observed point; ARCH (pre-1.8 realizations) is the named evidence
  class that would size the envelope. Exit codes are harness-side
  keys, not machine content. Version-tracked. | VERDICT: KEEP | C3.

- **A1-35** | R13 (+the SortFunc shim + the parked relocation arc +
  U-5's granularity split) — comparator-sort tie order: the injected
  insertion sort realizes ONE member of the unstable-sort envelope
  where ties ARE observable; `slices.Sort([]uint64)` is one machine
  step while `slices.SortFunc(x, cmp.Compare)` is a per-element shim
  loop — two granularities for one Go operation | L:1090–1106,
  1206–1220 | ORIGINAL: int-sort instability declared unobservable
  (sound); the comparator case is "declared latitude, comparator
  lane"; the granularity split "unobservable while racy programs
  fail closed (C10)"; resolution parked (relocation arc) | FRESH:
  the int-only argument is scoped and fine. The COMPARATOR tie-order
  is real observable latitude realized as an undocumented-in-corpus
  singleton — a (b-n) needing a membership row TODAY, not after
  relocation; and the granularity split's unobservability leans on
  A1-07's contested chain. A PARKED arc is carrying a live latitude
  record | VERDICT: REOPEN — (S) a tie-order membership row for
  SortFunc now; (M) un-park or explicitly re-scope the relocation
  arc with a date | C1, C3.

- **A1-36** | R14/U-3 — constant arithmetic precision wholly delegated
  to go/types; acceptance-relevant extremes UNANALYZED | L:1108–1118,
  1200 | ORIGINAL: machine and oracle share one realization; negative-
  lane relevance only; open question as stated | FRESH: the delegation
  is the right TCB call (Lane A's delegation row), but "not analyzed"
  is not a disposition under the new goal: spec#Constants sets MINIMUM
  requirements (≥256-bit integer precision, may round), so a
  conforming implementation stricter than go/types could REJECT
  programs our negative lane certifies as accepted — the negative
  corpus's claim silently narrows to "gc's frontend accepts/rejects".
  The desk analysis (compare spec minima against go/types' actual
  limits, write the scope sentence) is hours | VERDICT: REOPEN — (S)
  the desk analysis + scope sentence on the negative-lane claim |
  C1, C4.

- **A1-37** | R15 — zero-size variable address identity: machine is
  the deterministic never-same singleton; gc probed NON-single-valued
  (stack distinct, escaped both on `runtime.zerobase`); standing red
  pin | L:1120–1148 | ORIGINAL: the red IS the honest version-tracked
  pin; re-envelope (may-equal choice or membership {0,1}) queued for
  W3.2 | FRESH: a PROBED observed-∉-modeled member held as a
  permanent red is the same class as A1-26 — and this one additionally
  undercuts the allocator-quotient's injection class (A1-09 item 3).
  The membership-{0,1} form is cheap and turns a deviation record
  into an inclusion check | VERDICT: REOPEN — (S) the membership row
  or may-equal site; fold into A1-09's condition rewrite | C2, C3.

- **A1-38** | U-2 — L4 ⊆ L1-reachability ([ANALYSIS], no theorem, no
  counterexample search beyond probed shapes) | L:1197–1199 | FRESH:
  this unknown is about internal REDUNDANCY (whether the L4 site's
  members are independently reachable via arrival timing), not about
  envelope width — the L4 site exists and is demonic, so neither
  bound is at risk from the open question; per-shape membership
  polices it where it matters | VERDICT: KEEP (as a recorded open
  question) | C3 (marginal).

- **A1-39** | U-4 — overlapping copy/append aliasing differential
  coverage owed on a FORCED point | L:1201–1205 | FRESH: forced
  semantics ("as if" intermediate copy) with no validating fixtures
  is a plain lower-bound evidence hole on an aliasing-heavy arm —
  cheap fixtures, no design needed. That it has sat in a (d) row
  since founding is the same queue-discipline pattern as
  A1-15/A1-26 | VERDICT: REOPEN — (S) write the overlap fixtures |
  C2, C4.

- **A1-40** | U-6 — future atomics: mem#atomic pins sync/atomic to SC
  | L:1221–1228 | FRESH: verbatim-anchored, forced-when-modeled, and
  the residual latitude (surrounding plain accesses) is correctly
  deferred to the atomics arc. Nothing to reopen before that arc |
  VERDICT: KEEP | C3.

- **A1-41** | §5 — the refusals-standing-in-for-latitude list
  (select-with-select rendezvous, `go` during `$pkginit`, uintptr
  observations, + R6/E6/C10 covered above) | L:1172–1179 | FRESH:
  each is a visible red naming its cause, listed as coverage debt
  and explicitly NOT a fidelity claim ("none is a fidelity
  achievement"). This is the C1 boundary working as designed; the
  select-with-select and go-during-pkginit rows belong on the
  feature ladder (Lane A's C1 disposition list), not in fidelity
  debt | VERDICT: KEEP (as refusals; ladder placement is C1 work) |
  C1.

- **A1-42** | The inventory's own COMPLETENESS argument | L:1–13 (the
  dual sweep), L:64–72 (ChoiceSite census-is-code),
  `docs/language-coverage-ledger.md` §0 + `docs/spec-archaeology/
  section-census.tsv` (158 spec + 18 mem headings, heading-granularity,
  no latitude column — verified) | ORIGINAL: produced by a dual sweep
  (records + code, code wins); machine-side census is the
  exhaustiveness-checked `ChoiceSite` datatype; spec-side crosswalk
  is the section census | FRESH: the argument decomposes into three
  legs of very different strength. (i) MACHINE-side: strong for
  REIFIED latitude (a new consumption site cannot exist without a
  constructor) but structurally blind to latitude the machine bakes
  in deterministically WITHOUT a site — which is exactly the class
  every discovered hole belonged to (E12 via CH2O prior-art, E13 via
  grossmith fuzzing, E14 via launch audit, R15 via audit, R7 untagged
  since founding). (ii) SPEC-side: the 158+18 census is
  HEADING-granularity with no per-sentence latitude extraction — a
  section graded "active" can hide an uncensused latitude sentence
  (E12/R15 did exactly this). (iii) AUDIT-side: repeated adversarial
  passes are the leg that actually found things — strong evidence the
  PROCESS converges, and equally strong evidence no single sweep was
  complete. And the document itself ADMITS present incompleteness:
  E12's "RECORDED CENSUS FOLLOW-ONS" (L:771–775 — composite-literal
  element order vs a call among elements, duplicate-map-key
  evaluation order, map-literal key-vs-value order) name axes with
  corpus fixtures but NO census rows, still, at tip. There is no
  mem-model-sentence sweep either. Verdict on the argument's
  strength: MODERATE for the machine side, WEAK-to-MODERATE for the
  spec side | VERDICT: REOPEN — (M) a sentence-level latitude pass
  over the pinned spec + memory model (grep-assisted:
  unspecified/implementation-specific/"may"/"not specified"/
  "implementation-dependent", one disposition per hit, appended to
  the census as the denominator the heading census cannot be); (S)
  close E12's three admitted follow-on axes | C3, C4.

- **A1-43** | E12's census follow-on axes as concrete rows |
  L:771–775; corpus has `maps/literal-eval-order`,
  `maps/map-literal-duplicate-eval-order` fixtures but the inventory
  has no rows | FRESH: a fixture without a census row pins a
  realization while leaving the LATITUDE CLASSIFICATION unrecorded —
  the exact failure shape R15 had before 2026-08-19 (silent
  singleton at a spec-open point). Three named axes, spec text
  already located | VERDICT: REOPEN — (S) probe + classify + write
  the three rows | C3.

- **A1-44** | U-7 — the assumption that version-tracking pins
  actually FIRE on toolchain movement ("believed true … not
  re-audited here") | L:1229–1233 | ORIGINAL: they are
  membership/eval pins, so a moved toolchain should flip them |
  FRESH: this is the validation apparatus's own fail-open risk — if
  a pin does NOT fire on toolchain movement, every "version-tracked"
  caveat in the inventory silently expires. "Believed true" about
  the mechanism that guards ~17 pins is exactly the class of
  unexamined assumption the mandate names, and it is cheaply
  testable (run the pin subset against a different toolchain in a
  sandbox and count the flips; requires no baseline change) |
  VERDICT: REOPEN — (S) the one-session pin-firing audit | C4.

- **A1-45** | The register's NUMBERING COLLISION: the doctrine's
  entries 6 (allocator quotient) and 7 (unbounded memory) collide
  with the inventory §8 extension's entries 6 (int width) and 7
  (library-doc-silent pins) — §8 says "Numbering continues the
  doctrine draft's 1–5" but the doctrine later grew to 7 | D:143,
  156 vs L:1288, 1297 | FRESH: "register #6"/"register #7" is now
  ambiguous across the two binding documents (the fidelity plan
  itself cites doctrine numbering; the inventory cites its own).
  For a register whose whole job is unambiguous reference, this is
  a small defect with outsized citation risk | VERDICT: REOPEN —
  (S, doc-only) renumber the §8 extension (e.g. X1–X8) and fix the
  cross-references | C4.

- **A1-46** | Post-split DANGLING EVIDENCE in the two doctrine
  artifacts: L:453 cites `docs/2026-08-13_executable-frame-theorem.md`
  (not in the tree); the (q) discharge cites
  `Frame.allocatorIndependence` (park branch only, A1-09); D:110 and
  L:157 lean on the liveness tier's `Fair` (`FairStream` — no longer
  in GoLean/); NPDRF's proof line references W3.2 "slice 5" of a
  campaign whose repo half left | verified by grep/ls at tip |
  FRESH: the split plan moved the reasoning product wholesale, and
  the semantics doctrine's citations were not re-pointed; a reader
  of THIS repo cannot check the register's only theorem-closed entry
  or the fairness residue. Honest doctrine requires its evidence
  reachable from its repo (or the entry re-labeled) | VERDICT:
  REOPEN — (S) a split-aftermath citation sweep over D and L:
  re-point to the park branch explicitly, or re-home the artifacts,
  or downgrade the affected entries | C4.

- **A1-47** | E9's user-ruled full map envelope — the one entry where
  the [USER] explicitly widened past every narrowing ("any latitude
  in the Go spec should be supported", 2026-08-19) | L:641–681 |
  FRESH: censused here as the POSITIVE model: full literal envelope
  of the spec's production table, interpretation recorded as I-1 with
  a ledger id, fail-closed on the genuinely-unbounded shapes, and
  membership rows for the created-entry latitude. This is what every
  REOPEN above should converge to. (Residual: A1-20.) | VERDICT:
  (counted under A1-20's KEEP; listed for the record) | C3.
  [2026-09-02 [AGENT] annotation — frozen artifact: the A1-20 residual
  was REOPENED at phase 2 (`p2-keeps-a1.md`; A1-47's positive-model
  status was made conditional on it) and CLOSED 2026-09-02 by the
  `t5-e9-prune` slice (pool-level `pruneForeign`); the conditional is
  discharged — see the discharge note under A1-20 in `p2-keeps-a1.md`.]

---

## Findings the plan did not anticipate

1. **The split orphaned the register's only theorem-closed discharge**
   (A1-09/A1-46): `Frame.allocatorIndependence` and its design note
   exist only on `park/reasoning-2026-08-31`; nothing at this tip
   re-checks the (q) discharge, and the inventory cites a document
   that is not in the tree.
2. **R15 is a live counterexample-shaped hole in the quotient's
   condition** (A1-09): gc's `runtime.zerobase` collapse is a
   NON-injective address labeling observable through plain pointer
   equality — inside the modeled surface, outside the theorem's
   injection class. Entry 6 and R15 never cross-reference.
3. **The register numbering collision** (A1-45): two documents, two
   different entries named "#6" and "#7".
4. **The B3 deferral's "no clean oracle observable" premise looks
   refutable** (A1-01): a deferred `print` in the panicking goroutine
   is a stdout-ordered, definitionally post-raise event.
5. **A queue-discipline pattern**: three separate S-priced,
   red-class items (E7 detector A1-15, R3 widening A1-26, U-4
   fixtures A1-39) have sat unbuilt through multiple arcs while
   larger items shipped — the priority queue optimizes for arcs, not
   for clearing known observed-∉-modeled exposure.
6. **C7's re-argue trigger already fired unnoticed** (A1-14): the row
   demands re-argument "whenever wake machinery changes"; B1/B2
   changed it (classification moved to the marker) and no re-argument
   was recorded.
7. **A1-07's chain has more consumers than C10**: E9's residual
   narrowing (A1-20) and U-5's granularity split (A1-35) both cite
   "unobservable because racy programs refuse" — the refusal's
   per-program completeness is load-bearing for entries that never
   mention NPDRF.
