# Gallery Campaign trip report — lessons for long-cycle autonomous build-outs (2026-08-16)

The campaign ran five goals (G0–G4) to a verified DONE conjunction over
~25 worker sessions in up to four parallel lanes, ~2 days wall clock,
with the user absent by design. This is the operator's review of HOW it
ran, for the next long-cycle experiment. Product numbers live in the
final checkpoint (`docs/gallery-campaign-log/INDEX.md`); this note is
about process. Evidence for every claim is in the campaign log's
judgment-call entries and the lane reports.

## What carried the campaign (keep these)

**1. A counted, self-defined DONE.** The charter's conjunction (each
clause machine-checkable; honest gaps legitimate but NOT counted toward
totals) meant no worker or operator ever negotiated with the goal.
Substitution economics did exactly what they were designed to do:
matmul could park honestly because sieve/fibmemo/stack/queue could
cover, and nobody was tempted to ship an unverified headline to make a
number. LESSON: the goal file must be the single definition of done,
and the goal prompt should say "as defined by that file's DONE
section, nothing more" — the campaign's one stop-condition ambiguity
("finish ALL" vs the file's own user-boundary exclusions) was resolved
by the file's text, but the prompt should have pre-empted it.

**2. Artifact-mediated continuity beats agent continuity.** Workers
died, ran out of budget, or became unreachable repeatedly; the cost was
near zero every time because state lived in artifacts: module status
blocks, stashed WIPs with completion notes, measured step-count maps,
snapshot refs, per-goal log files. The exemplar: queue's worker cut at
budget with a transcription-ready handoff; a later worker finished it
in one session; the RETIRED worker then read-only-reviewed its
successor's bisect and diagnosed the exact blocker from its planning
notes, relayed through the operator. Invest in resumability, not in
longer sessions.

**3. Guardrails-first factored the parallelism.** The single corpus
wave (one baseline writer, one dated re-pin) turned twelve proof units
into embarrassingly-parallel work, because `baselines/native-full.tsv`
is the one file parallel lanes can never share. Identify the
serialization resource FIRST and batch everything that touches it.

**4. The flagship pattern (brick-wp P4) paid twice.** Proving the
first new example kit-only produced the honest verdict ("step level,
not structure level") and a costed gap list; closing the gaps
immediately (825→376 lines, 71 s→1.2 s on the worst shard) cut every
successor's cost ~25% and made two later units one-session jobs. The
generalization: after any capability phase, spend one unit proving the
capability on a real consumer BEFORE fanning out.

**5. The extension template (E3/E5): argument → red guardrails →
implementation → flip-with-zero-drift.** Writing the fidelity argument
before code, landing failure-witnessing rows red first, and treating
the full differential as the only accepted evidence of no-blast-radius
made two frontend changes and a driver change land without a single
laundered row. E5's framing — oracle runs the real stdlib, machine
runs the shim, so THE CORPUS IS THE SHIM'S CONFORMANCE SUITE — is the
reusable idea.

**6. Honesty conventions scaled with autonomy.** The highest-value
recorded rules: bounds shipped AS bounds with measured forms recorded
separately (three separate over-claim incidents caught against it);
deletion tests RUN not asserted, upgraded mid-campaign to the
three-way split (totality / truth / proof-structure, each
machine-probed); verbatim-quote disciplines for axioms and evidence.
Autonomy removes the user's casual glance, so the flattering-drift
failure mode ("measured law", "tight at even n", one fabricated
explanatory mechanism, one phantom cost breach) WILL appear — the
conventions caught every instance, usually by a later worker
re-verifying an earlier claim first-hand. Cross-verification between
worker generations is cheap and should stay briefed-in.

**7. Hard boundaries held, and the two stops were the right stops.**
The only places autonomy halted were genuine user decisions (a gate
amendment; earlier, a designation TCB-wiring). Three workers
independently refused to ship gate-adjacent shortcuts (a rename
laundered through the bug index; a lift with a not-yet-true
justification; hand-written axiom pins). The permission classifier
stopped the operator twice — once self-authorizing gate wiring, once a
blind batch conflict-resolution loop — and both corrected paths were
strictly better (user ruling; a verified merge that caught a real
semantic conflict the blind loop would have shipped).

## What hurt (fix these next time)

**8. Shared-file contention is a design smell, not a merge chore.**
Append conflicts in `Audit.lean`'s import list and the gallery's
hand-maintained COUNTS recurred at every integration. The per-goal log
split fixed the logs; the rest should follow: generate the Audit
root's import block, compute gallery counts by script at render time
(prose that states a number is prose that goes stale). Rule of thumb:
if two lanes will both edit a line, that line should be generated or
should not exist.

**9. Cross-lane SEMANTIC conflicts hide until merge.** Two real ones:
a parallel privatization pass removed lemmas a sibling lane had just
become a consumer of; import pruning stopped transitively providing a
deprecated alias a new proof leaned on. File-disjointness does not
imply interface-disjointness. Next time: lanes that change shared
interfaces (privacy, imports, renames) run at wave boundaries, never
concurrently with consumers of those interfaces — or declare an
interface freeze the other lanes can read.

**10. One writer per worktree, as a HARD rule.** The A2 lane ended up
with a presumed-dead coordinator (actually alive, on a very long
session) and a dispatched finisher interleaving in one worktree. It
converged — explicit-path commits, snapshot refs, and mutual
re-verification — but the near-miss (a file trimmed on a 16-minute
stale listing, deleting a headline the other agent had just written;
recovered only because of a snapshot ref one command earlier) is
exactly the accident that discipline was luck-supplemented on.
Silence is not death: message a quiet coordinator and fence the
worktree before dispatching a successor. Sub-workers also need an
addressable route to their coordinator; "the name resolves to no
reachable agent" forced operator-relayed handoffs twice.

**11. The box is a shared resource with invisible tenants.** Uncapped
LSP processes corrupted one cost measurement; an unrelated 81 GB
process squeezed a lane to 6 GB free mid-proof. Cooperative `free -g`
checks in briefs mostly worked; commit-early-for-durability saved work
once. A budget the workers can't forget (the cgroup pattern extended
to a box-level reservation) is the real fix.

**12. Session budget is the true unit of work — plan units to it.**
Everything sized to ~one session landed; everything larger ended in a
(well-handled) park-and-handoff. The two structural aids that made
parks cheap: thin-top layering (statement layer last, so form changes
and handoffs cost the top only) and the tracer recipe (probe-derived
per-step maps making proofs transcription-bound). Both should be in
every proof brief from day one, not discovered mid-campaign.

**13. Tier models by proof-shape novelty, not task prestige.** Opus
replication carried 70%+ of the campaign including superb
verification work (the claim corrections were mostly Opus); Fable was
decisive exactly where the proof SHAPE was new (the recursion idiom,
the C1 parameterization, the E3 fidelity argument). The one mis-tier
(hard examples briefed as "cheapest") came from labeling by harness
style rather than proof novelty — the worker caught it by probing
before believing the brief.

**14. The operator's context is the scarcest resource.** Delegation
kept the operator viable for ~25 sessions of coordination, but
integrations (conflict resolution, count recomputation, gate re-runs)
consumed real context late in the campaign. The fixes compound: fewer
contended lines (#8), interface freezes (#9), and workers briefed to
rebase-and-gate their OWN lanes before reporting where safe.

## The one-paragraph version for the next charter

Define done in the goal file and point the goal prompt at that
definition alone. Batch the serialization resource early; parallelize
only file-AND-interface-disjoint units; one writer per worktree, ever.
Prove each capability phase on a real consumer before fanning out.
Ship honesty conventions in the first brief (bounds-as-bounds,
probe-run deletion tests, verbatim quotes) and brief successors to
re-verify predecessors' top claims. Make every unit park-able
(thin tops, status blocks, snapshot refs, tracer maps) and size units
to one session. Generate any line two lanes would both edit. Expect
flattering drift and boundary pressure; the conventions and the
permission layer are load-bearing, not ceremony — the experiment's
best evidence is that every place they engaged, the corrected path
was better than the one the agent had picked.

## Play-by-play (commit timestamps, all lanes; campaign = ~34 h wall)

**Aug 14, evening — chartering (21:16–21:52).** Charter committed;
reformed to all-mandatory goals on user ruling (21:34); G0 amendment
(21:42); parallel-sub-lanes process amendment (21:52). Two lanes
dispatched.

**21:57–22:40 — the opening parallel burst.** The KIT LANE ran G0
end-to-end in 43 minutes (log init → brick-wp mapping → P5 schema +
9-induction rollback → MapMem → all-10 entry equations → 81 kit pins).
Simultaneously the DOSSIER LANE fixed the 22-item register at 21:57 and
wrote ALL 22 dossiers by 22:29 — 32 minutes, probe programs included
(the E9 measured-outside and R14 512-bit findings both land here).

**23:10–23:49 — the flagship.** Histogram corpus at 23:10, COMPLETE
with the kit-gap report at 23:49 (~3.5 h wall inside the worker; the
verdict: kit carries steps, not structure; six gaps costed).

**Aug 15, 00:10–01:29 — kit-gap closure.** All six gaps in 79 minutes,
dependency-ordered (M2→P1→C1→R1→P2→M1); the C1 collapse measured
directly (histogram CountLoop 825→376 lines, 71 s→1.2 s).

**01:40–02:35 — wave + debt, in parallel.** The GUARDRAILS WAVE landed
16 examples' corpus (one commit each, 01:44–02:10) and the single
203-row re-pin at 02:17; the G2 pull-list — probed, not assumed — at
02:08 (E2/E4 discovered to be ONE mechanism). The DEBT LANE interleaved
all four G4 items (comparator fix 01:40 → import prune 02:04 → DAG
repair 02:24 → re-privatization 02:34). E1 (driver uint64) built at
02:48 with zero fidelity findings.

**02:55–04:48 — the big proof burst.** Ten examples proven in under
two hours across two lanes and five sub-workers: lane B's palin
(03:08), strrev (03:50), twosum (04:01), selsort (03:58), bubble
(04:06), rle (04:48, the append-envelope discovery); lane A's powmod
(03:25, with its own honesty correction at 03:32), dotprod (04:20),
kadane + dedup (04:31). Lane B integrated at 05:03 — the one semantic
cross-lane conflict (the deprecated-alias/import-prune collision)
caught by the gate-verified merge.

**05:55–07:49 — the hard pair.** fibmemo COMPLETE 06:13 (the new
recursion idiom), sieve COMPLETE 07:42 (dynamic allocation + its own
number theory). Integration at 07:49: **G1 reaches twenty, ~10.5 hours
after the charter was committed.**

**08:16–12:27 — extensions and the A2 lane.** E3: fidelity argument +
16 red rows at 08:16, the normalization + 46 flips at 08:27, stein
COMPLETE at 10:24. E5: 23 red rows at 10:47, the shim + 22 flips at
10:55. Lane A2 in parallel: stack (11:27, the first non-map ∀ch
entry), matmul honestly withdrawn (12:01), queue (12:01), the
cost-claim correction (12:27).

**Aug 15 afternoon → Aug 16 07:16 — the long tail.** wordfreq's proof
half: five sequential Fable workers, two honest parks with executed
continuation plans, ~19 hours — the campaign's hardest single unit
(strings + maps + shim vocabulary at once) and a clean demonstration
of the park-and-resume machinery under real strain.

**Aug 16, 07:25–07:29 — close.** Final integration (gallery recounted
to twenty-four), the DONE conjunction verified clause-by-clause with a
fresh full differential at the tip, and the arc-end asks posed. The
shape worth noticing: >60% of all value landed in the first 8 hours
(kit, dossiers, wave, ten proofs); the last 40% of wall clock went to
the three hardest units (sieve/fibmemo, stein, wordfreq) — long-cycle
budgets should expect exactly this fat tail.
