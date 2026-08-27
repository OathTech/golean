# The clean proof plan (2026-08-27, v2 — professor-amended) — awaiting [USER] approval

Deliverable 1 of the replanning round. The proof structure is
`docs/2026-08-27_proof-structure-explained.md` (deliverable 3 — read
first); the kill-list is `docs/2026-08-27_kill-list.md` (deliverable
2). This doc is the work breakdown: what gets built, in what order,
with gates. Nothing executes without approval.

## The quantifier audit (governs every unit below)

| quantifier of the end sentence | discharging rule | plan item |
|---|---|---|
| subject identity | reflection pair (wire + shape pins) | HAVE |
| ∀ states at spec boundaries | symbolic function specs over reader-predicates | W3 |
| ∀ iterations | the loop rule (invariant) | W2/W4 |
| ∀ ch — delivery picks | body-spec case analysis over net contents | W3/W4 |
| ∀ ch — latitude draws | choice-site rules ∀-draw + multiset loop invariants | W2/W3 |
| ∃ fuel, r (total form) | variant at the loop rule + spec totality | W4 |
| abstract trace facts | [HAVE] native chain, consumed through the invariant | W5 |

No quantifier is discharged by instances. The erasure quotient is
OFF the critical path (optional localization; built only on demand).

## W0 — the reset (the kill-list, executed)

Archive ref + ARCHIVE.md; the K-A/B/C/D deletions and splits; gate +
judge at the post-kill tip (the statement layer and trusted closure
are untouched, but Audit shrinks → judge rerun owed); ceremony as
usual. Includes **the CLAUDE.md rewrite** ([USER], this round):
CLAUDE.md is re-drafted as the WORKING CHARTER — what we are
building, the trusted surface, the proof doctrine (bounded-techniques
ban, the reasoning-layer constitution, the quantifier audit), the
gate, the merge protocol, and pointers out to everything else; the
accreted incident narratives move to a tracked
`docs/operational-lessons.md`. Draft for [USER] sign-off (it is the
charter; its content is yours).

## THE PROFESSOR'S DELTAS (final review, folded in below — the two
UNPRICED SUMMITS marked with a star)

1. W1 gains the call-span judgment shape, the runProgramM glue
   family, and (star) the frame design (footprint-annotated Spec).
2. NEW W2.5 — (star) the invariant design note + NetCorr (the Verdi
   network-invariant stratum, silently absorbed into EStep/HStep
   constructor premises until this review named it): a [USER]
   DESIGN GATE ahead of all of W3.
3. W3 gains per-handler NetCorr-preservation conclusions, the
   harvest-quiescence measure unit, the certified/leaderCommitOk
   Match-evidence unit, and the reader extension.
4. W4 gains the phase-transition round and the extended guard
   census (panic sites, blocked-sync exclusion, readback-.ok).
5. W2 gains the pick-loop element-type generalization and
   mapIter_no_stop_of_unmutated.
6. W0 amended: the two native interface witnesses RETAINED until
   W5 (non-vacuity of ClaimTrace/hgen/S23Interface; one caught the
   self-vote soundness bug); the W1 pilot may consult the archive.

## W1 — the spec former and driver (the judgment layer)

`Spec P f Q` in the CALL-SPAN shape (function entry through the
frame arm's result-read/store walk to the post-store configuration;
the `.next k` form covers statements only), the call rule, and the
deterministic driver with sealed refusals and the escape ladder.
Plus THE GLUE FAMILY (gates both sentences): runProgramM_mono,
runProgramM_readout_of_total (the bridge from ∃n specs to the
∀-fuel partial sentence), runConfig_prefix_classify + its two-phase
lift (NeverFaults' truncation half), setup/runPkgInitM unfolding,
readback-.ok. Plus (star) THE FRAME DESIGN: footprint-annotated
Spec + reader-congruence lemmas — the arc4d disjointness
enumerations exist because this is missing; the killed Shape* was
its refuted predecessor. GATE (the pilot, now three-legged): one
handler spec end-to-end via the driver + ONE TWO-FUNCTION
COMPOSITION exercising the frame + the glue family landed. Any leg
refuting the costing means redesign here before W3.

## W2 — the loop-rule family + init spec

The map-range loop rule with multiset invariants (the
iterate-then-canonicalize classic — this is where library-internal
mapIter latitude is discharged ∀-draw); the plain-`for` head schema
(harvest from arc4d's CondFor); then THE INIT SPEC — `$pkginit` +
setup as ordinary specs establishing `I₀` (replaces the seed pins;
kills the 81k-step replay obligation).

## W2.5 — (star) THE INVARIANT DESIGN NOTE + NetCorr ([USER] gate)

The full I as a written artifact BEFORE W3: the phase split
(Electing / Elected ldr tm), BOTH abstract carriers (SNet reach;
HNet/HistInv ESTABLISHED at the election win, with the noop as the
fragment's first propose and the snapshot index offset), the
pairing AS A RELATION (∃-ghost, deep readers, the shell-sync
clause, per-carrier field selection so non-election deliveries are
provable stutters), CheckerCorr (existential event histories,
fold-state equations, the reader extension for leaderOf/byIndex/
got/cursors), and NetCorr — four clauses, four consumers: hgen
(term-aware grant provenance), the MsgApp payload clause (history
slices + all-EntryNormal), the ack/Match clause, the population
clause (message vocabulary incl. no-MsgTimeoutNow — the second-
election exclusion becomes a PRESERVED INVARIANT, not an
assertion). This is Verdi's votes_nw/leaderLogs stratum, now owned.

## W3 — the function specs

The ~15 reachable handlers + library functions, the checker
(reshaped over the projections + W1's frame), and the driver body
spec (case analysis over the invariant-constrained net population
at the pick, symbolic in the net list). Named units per the
review: the HARVEST-QUIESCENCE MEASURE (the 64-round guard proved
silent — lexicographic drain measure; the hardest totality
obligation); the MATCH-EVIDENCE unit (instantiate certified,
discharge leaderCommitOk at the concrete commit-advance); the
READER EXTENSION. Every spec: ∀-state, ∀-stream,
emissions-preserve-NetCorr, guard-silence conclusions per census.

## W4 — the loop theorem and the sentences

The loop-rule instance at the driver's source-bounded loop:
`I` from W2's init spec, preservation from W3's body spec → the
partial sentence; + the variant (source counter + spec totality +
drain-bound discharge) → the total sentence and NeverFaults. The
harness-guard sites are discharged inside the relevant specs (each
guard's silence is a spec conclusion, per the T1-V census routes).

## W5 — the seam assembly

The pairing (`absTwinRead = some (proj N)` threaded through W3/W4's
postconditions) feeds the [HAVE] abstract layer: `etcd_discharges` +
`native_one_leader_per_term`(+cross-time) + `HistInv` chain +
`s1_leaf`/`s23_leaf` + the model bridges; `ClaimTrace`/`hlog`
discharged by the body spec's checker conclusions. Output:
`AgreementT1` proved; then the total form; then NeverFaults.
Ceremony: judge + milestone audit (coherence dimension per standing
practice) + [USER] designation of the final statement set.

## After (not this campaign's critical path)

T2 (`∀ n` — the abstract layer is already n-generic; the harness
quantification design comes to you), the Verdi second-dialect
instance (the interface's vacuity debt), the erasure arc on demand,
the second-target probe.

## Sequencing and effort honesty

W0 → W1 (three-legged pilot gate) → W2 → W2.5 ([USER] design gate) → W3 → W4 → W5 — W2.5 precedes ALL of W3 (it fixes every W3 postcondition). No unit-count
estimate until W1's pilot measurement (the standing rule: estimates
resume when the gate's numbers exist). Every unit charter opens with
its quantifier-audit line; every new mechanism carries lineage; no
statement contains a step count, round count, or fixture identity
outside declared reflection certificates.
