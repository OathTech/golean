# The clean proof plan (2026-08-27) — awaiting [USER] approval

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

## W1 — the spec former and driver (the judgment layer)

`Spec P f Q` over the interchange format (`stepFnIter`-level, with
`GoTriple`-shaped conclusions kept reachable); the call rule; the
deterministic driver assembling the landed rules (sym engine,
transports, lens, frame) with sealed `UNSUPPORTED payload` refusals
and the escape ladder. GATE (the pilot): ONE handler's function spec
(`becomeFollower` — smallest real handler) proved end-to-end via the
driver, cost measured. The U1 lesson applies: if the pilot refutes
the costing, redesign here before W3.

## W2 — the loop-rule family + init spec

The map-range loop rule with multiset invariants (the
iterate-then-canonicalize classic — this is where library-internal
mapIter latitude is discharged ∀-draw); the plain-`for` head schema
(harvest from arc4d's CondFor); then THE INIT SPEC — `$pkginit` +
setup as ordinary specs establishing `I₀` (replaces the seed pins;
kills the 81k-step replay obligation).

## W3 — the function specs

The ~15 reachable handlers + library functions, the checker
(reshaping arc4d's span content: predicate-level pre/post over the
`projLOf`/`projBy`/`encGS` projections + the frame rule in place of
disjointness enumerations), and the driver body spec (case analysis
over net contents at the pick; conclusions: `I` preserved, abstract
`EStep` taken, checker segment = model fold step). Specs are ∀-state
and ∀-stream by construction. Per-spec Audit pins; function-linear
statement inventory.

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

W0 → W1(pilot-gated) → {W2 ∥ W3-start} → W3 → W4 → W5. No unit-count
estimate until W1's pilot measurement (the standing rule: estimates
resume when the gate's numbers exist). Every unit charter opens with
its quantifier-audit line; every new mechanism carries lineage; no
statement contains a step count, round count, or fixture identity
outside declared reflection certificates.
