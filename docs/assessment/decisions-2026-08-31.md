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
