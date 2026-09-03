# Fidelity assessment: the [USER] decisions (2026-08-31)

Rulings on the synthesis's §4 escalations, given 2026-08-31. Each
tagged with its provenance; execution items route to the work
program's tiers.

1. **Concurrency claim scope — APPROVED as recommended [USER].**
   (What was recommended, synthesis §4.1: scope all C3/upper-bound
   claims to DRF programs NOW — ground: cost + no oracle, not
   impossibility — with the NPDRF proof investment, a weakened
   proved form (L/XL), held as a separate later decision.)
   Upper-bound claims scope to DRF programs; the racy
   limited-outcomes envelope is out of product scope (ground: cost
   + no oracle, not impossibility). NPDRF proof investment decided
   separately, later. Detector-completeness gets a named owner
   (this product; routes to Tier 4's detector-soundness leg).
2. **Stdlib shim retirement — split provenance (retagged at the
   2026-08-31 audit fix round, auditor D3-3).**
   **[USER]: design a proper retirement, park for now, on the
   backlog**: "yes we should design a proper retirement… park for
   now, deal with all the smaller things. Make sure our
   discrepancy backlog has it on the books." → entry D-002 in
   docs/discrepancy-backlog.md.
   **[AGENT] interim policy pending that design (fail-closed default;
   CONFIRMED [USER] 2026-09-01 ("the 4 confirmations all seem like reasonable interpretations… agree on all of the above"), WITH the recorded revisit trigger: the freeze trades
   away the cheapest lower-bound growth route — if the frontier
   re-ranking makes stdlib coverage urgent before the retirement
   design lands, the freeze is the first thing to revisit)**: until the retirement
   lands, NEW shims are frozen (no sixth mechanism, no new
   hand-modeled functions without a [USER] exception) and the
   Fields-standard validation rule applies to any shim that must
   change. The user's words instituted only the park + backlog
   entry; the freeze and the Fields-standard rule are the agent's
   interim policy.
3. **Frontier re-ranking + Q-row sitting — APPROVED [USER].**
   Re-rank the FR queue for the semantics-first goal (stdlib
   surface and S-priced items outrank complex-numbers); the
   eight Q-row rulings await one [USER] sitting (ruling sheet:
   docs/2026-08-21_w32-qrow-memos.md §RULING SHEET).
4. **Oracle matrix — APPROVED as recommended [USER]**: version
   sweep (existing drift mechanism), GOARCH=386 static leg, and
   the $GOROOT/test differential run. Dynamic-386 /
   gccgo / tinygo legs: deferred, needs a host-capability call
   (386 binaries currently abort in this sandbox).
5. **Unbounded memory — (a)+(b) [USER], with the residual ON THE
   BOOKS.** [USER] verbatim reasoning: "comparable to cerberus-C,
   and there I think the answer is that memory is bounded and very
   large, so any reasoning over arbitrary contexts has to account
   for potential memory failures, but in execution runs it
   essentially never happens. I think we should do (a) + (b) for
   now, but log this as a discrepancy that should eventually be
   retired." → (a) the allocation-succeeding-runs rider on
   consumer-facing claims (Tier 2); (b) the deterministic
   maxAlloc panic class modeled (Tier 5); the residual
   (bounded-very-large memory as the eventual model, Cerberus-
   style) is discrepancy D-001.
6. **Orphaned obligations re-homed — APPROVED [USER].** Q-rows,
   (c)-pin re-envelope obligations, BUG-002/004/059/065 route to
   this product's backlog (Tier 2 executes the re-homing).
7. **Decay dates — APPROVED [USER].** Every recorded set-aside
   carries an expiry/re-review date; the reconciler surfaces
   expired entries as a report-only ci note (Tier 3 implements;
   gates stay speedbumps).

Launch scope under these rulings: Tiers 1-3 now ("deal with all
the smaller things"); Tier 4 sequenced after; Tier 5 (incl. 5(b))
sized after 1-4.

## Addendum 2026-09-03 — the "decisions on deck" sitting

[AGENT] record; the [USER] quote was received by the [AGENT]
coordinator and RELAYED to the recording worker (lane
`guard-stage-alt`), so it is cited as relayed, not firsthand. The
coordinator's list: (1) the `coverage-baseline-diff` guard fix for the
oracle-schedule-dependent red, option (a) per-row stage alternation;
(2) BUG-087 panic-text latitude, demonic choice at the nil arm; (3)
stdlib gates G1–G9 as recommended; (4) atomics — TryLock own slice +
D-002 confirmation of the typed-wrapper shadow model; (5) noodler gaps;
(6) the strict-lane routing rule (put as "adopting it turns eight
scheduling rows red until routed; recommendation: adopt and route them
in the same slice" — the memo's real blast radius is 23 rows, 8
scheduling + 15 capacity; the coordinator has since disclosed this to
the [USER]; see `docs/2026-09-01_membership-depth.md` §5); others = the
periodic (non-gate) legs and the P5 filing. The reply, verbatim as
relayed:

«Re decisions on deck (1) the guard - agree with the redommendation, do (a); (2) panic-text, agree, demonic choice so both are admitted; (3) agree, go ahead with the plan; (4) Atomics - agree; (5) noodler gaps - already addressed; (6) strict-lane, agree; others: lower priority for now?»

Where each ruling is recorded: (1) `scripts/coverage-baseline-diff` +
`docs/coverage-suite-structure.md` (this lane); (2) BUGS.md BUG-087;
(3) `docs/2026-09-03_stdlib-boundary-design.md` §5; (4)
`docs/2026-08-31_qrow-rulings.md` row 5 + `docs/2026-09-03_atomics-w1-design.md`
§6 + D-002 in `docs/discrepancy-backlog.md`; (5) "already addressed" =
the noodler frontier gaps were ROWED as the five frontier-table rows
numbered 16 through 20 of `docs/language-coverage-ledger.md` on lane
`fg-gaps` (commit 40fdbe1e — not yet on main, so the reconciler cannot
resolve those ids here until that lane merges), per [USER] direction 3
(every detected gap is rowed); (6)
`docs/2026-09-01_membership-depth.md` §5/§6 (implementing lane
`strict-routing`).

**"Others: lower priority for now" — [USER] 2026-09-03 (relayed by the
[AGENT] coordinator, as above).** The periodic non-gate legs
(`scripts/choice-trace-corpus` P4, the oracle-matrix periodic legs) and
the P5 filing (variant-run status in the strict invariance check) are
DEFERRED as lower priority — not rejected; no schedule is set. Re-raise
when the routing slice and the stdlib slice 1 have landed.

**Membership sampling budget (membership-depth §6 P2) — ADOPTED [USER]
2026-09-03**, a SEPARATE exchange the same day, relayed by the [AGENT]
coordinator (not firsthand): «yeah, agree on the sampling budget, go
ahead as you propose» — alternate plain/race draws, early stop at the
`members=` pin, K=32 under `--diff` / K=80 under `--slow`. The budget
before this ruling is the implicit 10 draws (memo §1 "Membership
sampling today"); K=32 exists only inside P2. Implementing lane
`sampling-budget`. (An earlier version of this addendum said "the K=32
default STANDS; P2 is not raised" — wrong on both counts; corrected at
the guard-stage-alt audit fix round.)

Implementation record for that ruling, from lane `sampling-budget`
(folded into this single 2026-09-03 addendum at the round-8b merge
train, [AGENT]; the lane's own wording follows):

* **Membership sampling budget — APPROVED [USER]** (Mike, relayed by the
  coordinator; cited as relayed): «yeah, agree on the sampling budget,
  go ahead as you propose.» Adopts `docs/2026-09-01_membership-depth.md`
  §4.3 / P2: alternate plain and `-race` draws, stop early at the
  `members=` pin, else at K; K=32 on the gate path (`--diff`), K=80
  under `--slow`; `draws=` reported beside `exhibited=`. Gate change,
  implemented on branch `sampling-budget` (`scripts/diff-coverage`,
  `MEMBERSHIP_DRAWS`). [AGENT] follow-through inside the ruling:
  `samples=` retired and refused by name. **Effect on the assessment's
  figure** (synthesis: "441 enumerated / 45 exhibited" at the 2026-08-31
  gate budget — frozen, not edited): the lane is now 37 rows; under the
  new rule a `--diff`-budget run exhibits **68 (branch run) / 71 (gate
  run) of 470** (before, on the same 37 rows and the old budget/order:
  61 of 470); 17-18 of 25 pinned rows reach their pin within K=32.
  (The `guard-stage-alt` lane appends its own 2026-09-03 P1 block here;
  the merge train unifies the two.) The residual is the memo's
  gc-immobile set plus the `slices/*` capacity envelopes (R2). Record:
  `docs/evidence/2026-09-03_sampling-budget/`. Finding flagged, not
  self-adjudicated: `members=1` rows now take exactly one (plain) draw
  under the rule as ruled.
