# TODO

Tactical backlog for the SEMANTICS product.

**Where the pre-split TODO went ([AGENT] ruling, recorded here per the
audit):** the pre-split TODO.md (907 lines) is preserved verbatim on
branch `park/reasoning-2026-08-31`. Its sections were triaged, not
just truncated: the sections with LIVE unchecked semantics items are
carried forward below (Enumerator optimization verbatim; W3.2 items by
headline with a park pointer); the reasoning-track items (iris-lean
refresh, campaign follow-up routing, proof generation) migrate with
that product; the remaining sections (work queue, epistemic hardening,
directional audit follow-ups, priority sequence, Goose/Perennial
matrix, differential execution, hardening phase, GoCore memory
milestone, 2026-08-09 follow-ups) are completed/superseded records —
consult them on the park branch, not here. If an item in those
sections turns out to be live, carry it forward with a note.

## Design-hygiene arc ([USER]-ratified 2026-09-03)

Plan of record: `docs/2026-09-03_design-hygiene-arc.md` (source:
`docs/2026-09-03_grumpy-professor-review.md`). Sequence: (i) B1 map
entry-identity stamps [in progress, `hygiene-b1-stamps`] → (ii) the
A-series A1–A10 as small full-differential-gated commits → (iii) the
B2+B3+B8 re-proof wave (A1 folded in) → (iv) B4–B7 in any order →
(v) C1–C5 each by its own [USER] design gate. Every slice:
semantics-preserving, zero baseline drift, pre-merge audit, no gate
weakening. The "not this arc's to decide" list (semantics decisions
for the [USER]) is in the plan.

- [x] (i) B1 stamps — branch-complete 2026-09-03 (`hygiene-b1-stamps`), merge pending audit + sign-off
- [ ] (ii) A1–A10
- [ ] (iii) B2+B3+B8 wave
- [ ] (iv) B4/B5/B6/B7
- [ ] (v) C1–C5 — each a [USER] design gate when reached

## Owed from the split (tracked in the split plan)

- GoCore relational-module extraction slice → the reasoning side
  ([USER]-ruled destination; [AGENT]-deferred past this slice because
  the modules are interleaved with the executable core). The full
  dependency cluster, enumerated at the audit: `Machine.lean`,
  `MachineSound.lean`, `Multi.lean` (the concurrent relation itself —
  imported by `EnumSpec.lean`, which the executable dedup engine
  needs), `MultiSound.lean`, `MultiWfSound.lean`, `MultiStreams.lean`,
  `NPDRF.lean`, `Race.lean`, plus the `StateEqb`/`SyntaxEqb`/
  `MachineEqb` seam. Needs a design slice + full `--diff`
  revalidation.
- `tools/raftsubject/twin-chdriver.go` + `twin-chdriver-main.go`:
  their Lean-side consumer (`TwinProgram.lean`) is parked; on main
  they remain exercised only by the twin-wire pin
  (`scripts/check-frontend-pins`). Revisit ownership at migration.
- `docs/architecture.md` and `docs/roadmap.md` semantics-scoped
  rewrites (currently carrying split banners).
- Migration stage ([USER] decisions): new repo name/location/
  dependency mechanism/history strategy; `raft-proof-campaign`
  branch disposition.

## Enumerator optimization layer (deferred backlog, 2026-08-07)

Record only — no implementation scheduled. Design of record:
`docs/2026-08-04_membership-lane-design.md`, section "Deferred: the
enumerator OPTIMIZATION layer (2026-08-07)" (provenance: user
discussion 2026-08-07). Layers, each behind the BOTH-EXPLORERS
adoption gate (optimized vs reference explorer, identical observation
sets on every tractable instance) and each with a named soundness
obligation:

- [ ] Verified POR — race-detector footprints as the independence
      oracle; NPDRF mover lemmas as its eventual proof.
- [ ] Symmetry reduction — decidable Config equality; the
      id-relabeling lemma is the soundness obligation.
- [ ] Preemption-bound-as-metadata — certificates must NAME their
      bound (bounded tree, never silently the full one).
- [ ] State memoization on canonicalized MultiConfig — requires the
      decidable-equality/canonicalization layer first.
- [ ] PCT / portfolio sampling beyond enumeration scale — sample
      source only, never certification.
- [ ] Map-range live-pick walk cost (BUG-005 (L), audit fix round
      2026-08-19 — a PERF item, not semantics): every `mapIterNext`
      pick recomputes `mapIterCandidates` = live entries minus the
      produced-key set (a linear scan filtered by a linear membership
      walk), so a full mutation-free range is ~O(n²) picks and the
      ∀-stream confluence certifier multiplies that again — ~cubic
      pick walks at scale. Invisible on today's corpus sizes; will
      bite on raft-scale maps and enumerator workloads. Candidate:
      an indexed produced-set (or incremental candidates) behind the
      BOTH-EXPLORERS adoption gate above, with the pick-coherence
      relation (`MapMem`) as the soundness obligation. Semantics is
      NOT in question — the fuel-out on self-inserting loops is the
      ruled behavior, not this item.

## Re-homed obligations (re-homed 2026-08-31, fidelity decision 6 [USER]; R15 by [AGENT] extension — see its entry)

The W3.2 and F4 arcs these obligations routed to are parked whole on
branch `park/reasoning-2026-08-31` — the routes dangled from the
split until this entry. Live owner for ALL of them: this backlog.
Each originating site (ledger §5.1/§6, BUGS.md) carries the matching
"(re-homed 2026-08-31, fidelity decision 6)" marker; the R15 sites
(inventory R15, ledger §2/§6) carry the [AGENT]-extension variant —
see the R15 entry below.

- [x] The eight Q-row rulings — the [USER] sitting HAPPENED 2026-08-31
      (fidelity decision 3); ruling record of record:
      `docs/2026-08-31_qrow-rulings.md` (supersedes the memos doc's
      §RULING SHEET by pointer). Six ruled: rows 6+7 (Q-SYNCVAL +
      Q-SYNCLIT) IMPLEMENTED 2026-09-01 on the qrow-syncval slice
      (7 reds flipped); rows 1/4/5/8 ruled with vehicles named
      (Q-INITSPAWN → standalone $pkginit backlog item; Q-RACEPATH →
      Tier-4 detector-soundness leg; Q-TRYLOCK/Q-COND → deferred with
      envelopes pre-ruled). Rows 2/3 were OPEN with return conditions,
      both since discharged: Q-SELSEL RULED 2026-09-01 (its slot
      section below); Q-ATOMIC RULED 2026-09-02 — A′, THIS repo as
      owner, BUG-080's detector-kind slice pulled forward (the two
      items directly below). All eight rows ruled.
- [x] **BUG-080 detector atomic-access-kind slice (S–M, PULLED
      FORWARD — sequence BEFORE the atomics arc)** — LANDED on branch
      `bug080-atomic-kind` 2026-09-02 (merge pending audit + sign-off):
      `AccessKind ∈ {read, write, atomicRead, atomicWrite}` (the ruling's
      3-kind sketch refined to 4 — an atomic READ beside a plain read is
      not a race by mem#restrictions nor to TSan, measured on Once's
      done-Do and WaitGroup's Wait-at-0), `syncEntryKinds`/
      `syncReleaseTailKinds` per primitive, wgSema carve-out RETIRED into
      the data shadow; both pins flipped, +4 born-PASS rows, corpus HOLE
      cell 2 → 0, probe family u4kind 28 subjects; two residuals recorded
      at BUG-080 (TSan-invisible RWMutex-copy / WaitGroup-Done shapes
      followed to the oracle — residual (a), since RULED [USER]
      2026-09-02 Q-U4RESIDUAL option (A) and implemented on lane
      `q-u4-gomem`: go_mem's kinds recorded, the class refuses, BUG-084
      is the designed-divergence record; fatal-before-race on an
      overwrite-then-cross-goroutine-Unlock — residual (b), still owed
      below). ([USER]-ruled
      2026-09-02, `docs/2026-08-31_qrow-rulings.md` row 2; was: rides
      the arc's detector wave by [AGENT] sequencing, audit fix S4):
      the atomic access KIND in `GoLean/GoCore/Race.lean` —
      `RaceAccess := Kind × Loc`, atomic↔atomic non-conflicting,
      atomic↔plain conflicting, one atomic access recorded at the sync
      cell's path from `raceUpdate`'s sync arm. The two named costs
      are the slice's design checks: (i) one `syncData` cell per
      primitive vs the `locPrefix` over-refusal
      (`probe/u4/disjoint-field-vs-lock` must stay green) and the
      `wgSemaAccess` plain-pair carve-out; (ii) gc's per-primitive
      instrumentation differences (WaitGroup under `race.Disable` +
      the `wg.sema` pair vs Mutex's state CAS) — the per-op recorded
      set derived primitive by primitive from `-race`'s realized set
      (`scripts/detector-soundness` is the two-direction check). Exit:
      `race/negative-sync/{wg-overwrite,mutex-copy}` flip FAIL→PASS on
      BUG-080's Cases line; Race.lean's U4 inventory text updated;
      full `ci --diff`; audit ask.
- [ ] **Q-ATOMIC arc (A′, this repo owner; Tier 5; ~3–5 sessions)**
      — **WAVE 1 LANDED on branch `atomics-w1` 2026-09-03** (merge
      pending audit + sign-off; design note
      `docs/2026-09-03_atomics-w1-design.md`, evidence
      `docs/evidence/2026-09-03_atomics-w1/`): the integer core
      (Load/Store/Add/Swap/CAS × Int32/Int64/Uint32/Uint64/Uintptr,
      direct calls + the typed wrappers via the E5-T shadow model) as
      fused SC registry ops, zero new choice sites, TSan-realized
      per-address clocks + the atomic access kind; `mp-litmus` green
      with exactly {0,1,11}; +52 corpus rows (46 + the audit fix round's 6 op × kind cells), 4 frontier flips.
      REMAINING (wave 2, owed): `atomic.Value` (interface slot; nil-
      store / inconsistent-type panics red-first), `atomic.Bool`,
      `And*`/`Or*` (+ the wrappers' `And`/`Or`), the `Pointer`
      family's vehicle (unsafe policy). Q-TRYLOCK's rider was NOT taken
      in wave 1: its pre-ruled envelope is a NEW `ChoiceSite` and the
      wave-1 brief said "zero new choice sites" — rule conflict posed to
      the [USER] (design note §6). D-002 not-shim-injection reading
      stated in the design note §2 — [USER] confirmation still owed.
      Original item text follows.
      ([USER]-ruled 2026-09-02, `docs/2026-08-31_qrow-rulings.md` row
      2; charter = `docs/2026-09-01_qatomic-owner-proposal.md` §4 +
      `docs/2026-08-21_w32-qrow-memos.md` §2): a named worktree lane
      ("atomics arc"). Wave 1 integer core + `mp-litmus` (fused SC
      registry ops taking `.opDone`, zero new choice sites,
      value-returning op family in the `syncStmt` mold, TSan-realized
      detector edges over the per-address clock — the access KIND
      itself lands in the BUG-080 slice above and is CONSUMED here);
      wave 2 `atomic.Value`; Q-TRYLOCK rides wave 1 per row 5's
      pre-ruled envelope; spin-wait rows under `nonterm=` membership
      accounting, NO termination claim. Sequencing (proposal §5):
      after the gotest fix slice and the t4-detector merge; after the
      frontend-touching Q-row items ($pkginit, the Q-SELSEL slot); the
      BUG-080 slice first. OUT OF SCOPE: FairStream / the
      `Fair`-quantified claim class (reasoning-side future work — the
      fairness doctrine, [USER] 2026-09-02). D-002 not-shim-injection
      confirmation owed at dispatch, as Q-SYNCVAL's was.
- [ ] The `nonterm=`-under-`engine=dedup` ruling (charter OQ5,
      `docs/2026-08-20_w32-re-envelope-charter.md` §Open questions
      posed to the user;
      three candidate readings, and it changes what a green row
      asserts, so a [USER] ruling is owed) — live owner: this
      backlog. (Entry added at the 2026-08-31 audit fix round — the
      W3.2-section copy below is the historical text.)
- [ ] Q-ATOMICITY (= BUG-002, expression-step granularity — the
      formerly-F4 blocking precondition) and Q-GOEXIT (goroutine
      destruction): the two formerly-F4-owned design questions; held
      here until a concurrency-granularity arc exists.
- [ ] The (c)-pin re-envelope obligations (ledger §5.1 item 4): C1
      hidden-dep init order (E7 envelope), C2 staticinit `callinit`,
      C3 panic-qualifier rendering (BUG-059), C4 abort rendering
      (BUG-004), C5 float→int (R6) — formerly routed "to W3.2";
      C3/C6-class impossibility/out-of-language rows stay
      unconvertible, unchanged.
- [ ] BUG-004 + BUG-059: the display-vs-identity split and the
      abort-text member (semantic-core work formerly "owned by the
      W3.2 lane").
- [ ] BUG-065 residual (`goroutines/worker-pool/sum` honest red):
      formerly "awaiting the reduction/mover lane (slice 5)" — now a
      per-row ruling here, or a revived reduction lane.
- [ ] R15 zero-size-address re-envelope (may-equal choice or
      membership {0,1}; `pointers/zero-size-address/escaped-same`
      red) — formerly a "W3.2 re-envelope obligation". (re-homed
      2026-08-31 — [AGENT] extension of fidelity decision 6's orphan
      class; R15 fits the class; confirmed [USER] 2026-09-01)

## W3.2 re-envelope arc backlog (2026-08-20, charter DRAFT rev 1)

Semantics-side items carried by headline; full item text on the park
branch's TODO.md §"W3.2 re-envelope arc backlog". (The iris-lean
refresh and campaign-routing items from that section are
reasoning-side and migrate with that product. NOTE 2026-08-31: the
W3.2 arc itself is parked; the items below that are live semantics
obligations — the Q-row and `nonterm=` rulings — are duplicated with
owners in "Re-homed obligations" above, fidelity decision 6.)

- [ ] Trace-coverage push — PARKED POST-CAMPAIGN ([USER], 2026-08-21).
- [ ] Slice-5 probe: print-interleaving wedge-class candidate.
- [ ] RULE the eight Q-rows (charter §Slice 2 — memos written,
      rulings owed).
- [ ] RULE what `nonterm=` means under `engine=dedup`.
- [ ] Perf: map-iteration pick walks (post-BUG-005 (L) surgery; see
      the enumerator backlog's last item).

## Q-SELSEL implementation slot ([USER]-ruled 2026-09-01, option A)

- [ ] Q-SELSEL asymmetric-arrival envelope implementation (2 reds:
      the select-to-select rendezvous rows) — envelope adopted per
      docs/2026-08-31_qrow-rulings.md row 3; carry the owed C7
      wording correction at the sites; membership-lane case
      goroutines/select-wake-close-selsel recommended alongside
      (c7-refresh lane, 2026-09-01).

## Owed core fixes (BUGS.md carries the marker; this backlog the owner)

- [x] BUG-080 (race detector U4 — the atomic access KIND): FIXED
      2026-09-02 on `bug080-atomic-kind` (the item "BUG-080 detector
      atomic-access-kind slice" above). Follow-up owed, NOT a bug of
      record yet: residual (b) at BUG-080 — the detector folds only
      SUCCESSFUL steps, so a sync op whose apply is FATAL never has its
      entry access checked (machine `fatal` where gc reports the race
      first, then dies). THIS ITEM IS THE AUTHORITATIVE SCOPE (audit G2
      F5; BUGS.md BUG-080 and Race.lean's sync-words section cite it):
      the sync ENTRY access (`syncEntryKinds`) must be checked BEFORE the
      apply — or on the fatal path — at EVERY site that folds
      `raceUpdate` after `stepMulti`, which is the full call-site list
      (line numbers as of the G2 fix round): the detecting loop
      `GoLean/GoCore/Multi.lean` `execProgLoop` (:1681, :1691); the
      enumerator drivers `GoLean/EnumDedup.lean:267`,
      `GoLean/GoCore/EnumDedupCheck.lean:163`,
      `GoLean/ChoiceTrace.lean:533`, `GoLean/CLI.lean` (:811, :825,
      :1363); and the theorem-side mirrors whose statements unfold the
      loop — `GoLean/GoCore/MultiStreams.lean` (`execProgLoop_unfold`,
      `stepAllBranchesOk_sound`, `execProgLoop_ok_of_allStreamsOkPool`,
      `execProgLoop_mono`, `execProgLoop_le`, `stepAllBranchesOk_mono`,
      `allStreamsOkPool_mono`) and `GoLean/GoCore/EnumDedupSound.lean`
      (:826, :844). Size S–M (the check is S; re-proving the mirrors
      makes it M); TRUST-SURFACE (detector + every driver). Residual (a)
      — TSan-invisible go_mem-racy shapes (a plain access beside
      `RUnlock`/RWMutex `Unlock`/WaitGroup `Add`/`Done`, or an
      overwrite beside `Wait` at 0; NOT a copy beside `RLock`/`Lock`)
      followed to the oracle — is POSED to the [USER] as Q-U4RESIDUAL
      (`docs/2026-08-31_qrow-rulings.md` row 9, OPEN); its fix, if
      ruled, is its own S slice after the ruling.

- [ ] BUG-078 residual (1): the LINEAR normalize. `normalizeListWith`
      (GoLean/GoCore/Ops.lean) is non-tail-recursive over the element
      list and quadratic (`#[head] ++ tail` per element); it sits
      arm-for-arm in lockstep with `isNormalForTyFuel` and the
      MachineSound soundness proofs (the de-WF recipe, 2026-08-03), so
      the rewrite is semantic-core surgery with a proof obligation on
      the parked reasoning side. Until it lands, `arrayLenBudget`
      (GoLean/NativeToIR.lean, 1<<16 — re-derived 2026-09-01 on the
      literal/store path, docstring states each number's path) refuses
      array TYPES past the bound by name; residual (3) — one element
      store into an admitted nested `[1024][1024][128]byte` measured
      46 s — is lifted by the same fix. Owner: this item ([AGENT]-
      recorded at the gotest-fixes audit fix round, RECORD 9). Exit:
      the budget constant retired or raised on a fresh re-measure, the
      over-budget red pin flipped or re-pinned at the new bound.

## Standing semantics backlog

- Coverage ledgers: consume-on-demand growth per
  `docs/coverage-suite-structure.md`; BUGS.md triage per
  `docs/bugfix-arc-log.md`.
- Spec-truth follow-ups (covmap CIPs held for sign-off:
  `docs/covmap-cips/`).
