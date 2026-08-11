# Channel-logic arc — successor charter (2026-08-10)

Status: EXECUTION CHARTER (2026-08-11 upgrade of the 2026-08-10 scoping
draft; user-directed: scoped to RUN LONG under a standing goal, with
decisions FRONT-LOADED so execution never pauses on a question the
charter can answer). Successor to the spec-parity arc; assumes its
merged final state. Objective: close the *instrument-level* gaps to
Goose/Perennial equivalence that the spec-parity closure record names —
the places where our concurrency results are exhaustive-checking
certificates rather than a compositional program logic. The two
motivations, recorded from the 2026-08-11 discussion: (1) certificates
are abstract over INTERLEAVING but concrete over DATA — unbounded
iteration, quantified inputs, general heaps, and forever-running
programs (etcd-raft's node loop) need INVARIANTS, which only a program
logic supplies; (2) instrument parity with Goose/Perennial, whose
channel logic exists for the same target.

## The objective, stated as the property it buys

At this arc's end, a proved channel-program row means the same KIND of
thing on both sides: a heap-general, frame-quantified, fuel-independent
triple built compositionally from channel laws — with our standing
extras (executability, differential grounding, termination/deadlock
classes) on top. The parity table's against-us directions for the
channel class (compositionality, heap/frame generality, schedule
granularity's unproven bridge) close or become permanent recorded
asymmetries by explicit decision, never by silence.

## Work plan (slices)

1. **The channel WP law family.** `wpD` laws for the channel primitives
   (send/recv both directions, select incl. default, close, len/cap)
   over the LangD one-thread-step seam built in spec-parity slice 4
   (`goTripleC_of_wpD` is the consumer; P-S4-2 is the debt). Non-vacuity
   discipline as always: every law ships its discharge witness
   same-commit. Exemplar-first: hand-prove ONE channel program
   end-to-end through the laws before writing the rest of the family.
2. **The protocol layer.** The invariant/ghost layer for channel
   protocols (D2 NATIVE decision stands: native internally, comparison
   at the exported level; the Actris-lite port remains a recorded
   future option, not taken). Target: the dsp and muxer rows re-proved
   as compositional triples; park/deposit/wake full-strength for
   fork/join (P-S4-1's ∀-heap `ProgressExecC` closes here).
3. **Per-row frame-quantified triples.** Replace the certificate
   bundles' role for the six spec-parity channel rows (certificates
   stay as validation; the triple becomes the headline). Each row:
   triple + first-order readout (D1 BOTH), upstream status column
   maintained, deltas both directions.
4. **The NPDRF reduction proof.** The schedule-granularity bridge:
   DRF programs behave identically under communication-point
   scheduling. The current draft is marked REFUTABLE-AS-WRITTEN — this
   slice either proves the corrected statement or records precisely
   what fragment it holds for and captions every ∀-schedule theorem
   accordingly. This is the arc's hardest slice; budget for it, and
   an early design note on the corrected statement is binding before
   proof work.
5. **Race-axis decision + closure record.** Either (a) a
   detector-completeness theorem on the modeled fragment (no
   registry-point schedule of a modeled program exhibits a conflict the
   segment-HB detector misses — makes our race-freedom theorems
   sound-by-construction over modeled schedules, closing the proof-side
   asymmetry at that granularity), or (b) the asymmetry is recorded as
   permanent with the O4/T12 axis split as its statement. USER CALL,
   informed by slice 4's outcome (completeness likely composes with the
   NPDRF fragment).

## Front-loaded decisions (ALL resolved at charter blessing — none may
## pause execution; re-opening any of these mid-arc is a PARK, not a stop)

- **FD1 — sequencing: AS ORDERED.** The law family unblocks the most.
  Until slice 4 lands, every ∀-schedule statement carries the standing
  provisional caption (the NPDRF obligation, refutable-as-written
  draft cited); slice 4 updates the captions ONCE, whichever branch it
  takes (FD5).
- **FD2 — protocol style: NATIVE** (inherited from spec-parity D2,
  now binding): invariant+ghost internally over iris-lean, comparison
  at the exported level; the Actris-lite port stays a recorded future
  option. Iris strictly internal; every headline passes the deletion
  test.
- **FD3 — designation: RECORD, NEVER DESIGNATE.** Candidates
  accumulate in the manifest with the F4 def-only-hoist cost itemized
  (the dsp pair's successor triples are the expected flagships).
  Designation + the Comparator landmark happen at the arc-end merge
  window with the user — user-gated BY DESIGN, so it is end-loaded,
  not a mid-arc pause. The 48 designated statements stay byte-identical
  through the whole arc.
- **FD4 — breadth: BOUNDED DEFAULT.** After slice 3, scale to the
  15 imported-unattempted channel items in covered feature classes
  (honest 73-item tree accounting). The 10 P2-blocked and 34
  not-imported stay OUT (import work is not this arc). Trimming the 15
  with an honest per-row reason is in-lane authority; EXPANDING beyond
  them is a park.
- **FD5 — race axis: A DECISION RULE, not a deferred decision.** After
  slice 4: IF the proven NPDRF fragment supports a
  detector-completeness theorem over modeled schedules at ≤ one
  slice's cost, PROVE IT (closes the proof-side asymmetry at our
  granularity); ELSE record the asymmetry as permanent with the
  O4/T12 axis split as its statement. Either branch is SUCCESS; the
  lane takes the branch, records the reasoning, and does not stop.
- **FD6 — machine-change policy.** This is a proofs-side arc.
  GoCore THEOREM-ONLY additions are allowed (the S4/S6 precedent:
  import-downstream modules, window argument recorded per commit).
  A BEHAVIORAL machine change is allowed only as a probe-backed BUG
  FIX (gc disagrees with the model: red-first pin, full differential
  discipline, BUGS.md entry, lockstep) and is always reported as a
  finding in the slice record. Model-DESIGN changes, new Choices
  sites, and envelope changes are MUST-PARK.
- **FD7 — statement forms and axioms (inherited, binding):** ∃N-∀fuel≥N
  forms for anything fuel-dependent (execProgLoop_le/mono are the
  lifts); axiom sets [propext, Classical.choice, Quot.sound] spec
  lane, constructive [propext, Quot.sound] where the existing
  simulation lane is; statement TCB + deletion test on everything
  headline-shaped; non-vacuity witnesses same-commit, Audit-registered
  with the name-tripwire scope stated.
- **FD9 — iris-lean: STAY AT THE PIN (3877dbe)** — investigated
  2026-08-11 with network: the pin already carries the protocol
  layer's core (Invariants/WSat/FUpd, GhostMap, Auth/View/FracAuth/
  ExclAuth, Frac/DFrac/Excl/Agree, LaterCredits); upstream's 86
  newer commits add conveniences (MonoNat, BigSepMSet, SavedProp)
  but require Lean 4.32.2 (we are 4.31.0 — a bump is a WHOLE-REPO
  toolchain event) and refactor the ProgramLogic layer our
  LangC/LangD instantiate. In-lane authority: build small local
  constructions over the pin's machinery where a convenience is
  missing (mono-nat over auth, multiset big-ops, saved-prop if
  higher-order protocols demand it) — proofs-side code, recorded in
  the slice notes. The deliberate post-arc bump (toolchain +
  iris-lean + ProgramLogic migration) is queued on TODO as its own
  maintenance item; re-opening it mid-arc is a PARK.
- **FD8 — NPDRF outcome latitude (explicit):** slice 4 proves the
  corrected reduction statement OR a precisely-scoped fragment with
  every ∀-schedule caption updated to match. Both outcomes are
  success; an honest fragment beats a stalled generality.

## The standing goal (proposed /goal text, set by the user at blessing)

    Execute the channel-logic arc charter
    (docs/2026-08-10_channel-logic-arc-charter.md) on lane
    channel-logic (worktree .claude/worktrees/channel-logic).
    Done = the charter's exit criterion with all goals done, or goals
    deferred for good reason and logged — deferral with an honest log
    entry is SUCCESS; never trade soundness or the fidelity rules for
    coverage. The front-loaded decisions (FD1-FD8) are settled: apply
    them rather than re-asking. Questions outside them go to the
    parking ledger with a reversible conservative course taken
    meanwhile — hard-stop ONLY for soundness threats (a designated
    statement change, a gate weakening, an unexplainable regression).
    EXIT CONDITION: an early exit may be declared at any time, for any
    reason or none; the drift tests and fidelity rules override
    completion pressure.

## Must-park list (never decided in-lane; ledger + batch for check-in)

Designation or ANY designated-statement change; new Choices sites or
envelope changes; model-design changes (FD6's bug-fix carve-out
excepted); merges to main and pushes (operator-gated, arc end);
CLAUDE.md/doctrine amendments; certified-record re-pins beyond the
same-commit-explained discipline; anything in compat/** (the Verdi
lane's tree); grossmith-outbound communication; expansion beyond FD4's
breadth bound.

## Lane mechanics (worktree discipline, binding)

Lane branch `channel-logic`, worktree `.claude/worktrees/channel-logic`
(created at charter drafting; deps bootstrapped via scripts/setup-deps).
This lane is the MAINLINE OWNER for its duration: GoLean/, proofs/,
Corpus/, baselines/, scripts/, docs/ — disjoint from the Verdi lane
(compat/** + its dated docs). When both lanes run full gates
concurrently: GOLEAN_MEM_MAX=48G or stagger (arc-boundary events).
Sub-branches per slice off the lane branch, the established audit
cycle per slice (Opus reviewers/verifiers, Fable workers; convergence
bar: critical/major ⇒ verified fix round, note-level ⇒ converged);
delta-reviews per the substantive-fix policy; snapshot refs before any
rebase. Parking ledger lives in the lane's slice notes; the arc-end
sequence (closure record → audit-ask → designation → Comparator →
rebase → merge → push) is the user's.

## Validation discipline (inherited, with one addition)

Everything from the spec-parity arc binds unchanged (guardrails first,
lockstep, envelope statements from spec text, fail closed, zero drift,
statement TCB + deletion test, non-vacuity witnesses, honest records
with figure-emitting commands, sub-branch audit cycle, arc-end
user-asked audit + Comparator). Addition: every new law's soundness is
also exercised through the CONFLUENT lane where a deterministic
concurrent program exists for its shape — the executable differential
remains the arc's distinguishing check, and a law that cannot be
exercised by any runnable program is a red flag on its own.

## Addendum (2026-08-11, S1 audit fix round — user doctrine): the
## TCB-grounding walk is a per-slice review criterion

For every soundness property this arc ships, the TRUSTED claim must be
a boring, semantically-trivial property of the interpreter (a kernel-
evaluated completion pin, a first-order run-conditioned readout, a
differential pin); the Iris/Löb/simulation machinery is untrusted
METHOD only. Every slice record from S1 on carries a grounding walk
(the S1 form: docs/2026-08-11_channel-wp-laws.md §10) naming, per
exported artifact, (i) the interpreter proposition it reduces to,
(ii) that all machinery is proof-side, (iii) the executable anchor —
and every exported triple-carrying constant (`GoTripleC`, `GoSpecC`,
or anything whose type closure reaches them) across ALL
`GoLeanProofs.Specs.*` modules carries a `TerminatesNormallyC`
∃-completion member FOR ITS PROGRAM, enforced by the completion-pin
gate (Audit.lean — SEMANTIC since audit round 2, hardened at round 3:
exhaustive-arms closure walk (no `ConstantInfo` wildcard — the
twice-grown bug), env-wide scope over the proofs package,
conclusion-asserted CLOSED pins only, per-program pairing,
wrapper-hidden and open-term exports fail closed, an exact-name
allowlist for genuine ∀-program lemmas, and every attacker shape from
all three review rounds kept as a tracked negative-tested fixture). Run-conditioned triples ALONE anchor nothing (the
permanent demonstration: Specs/ChanVacuityWarning.lean); the
sub-branch audits review the walk as a standing dimension.

## Exit criterion

The six channel rows stand as compositional frame-quantified triples
(or per-row honest deferrals); the NPDRF obligation is proved or
precisely scoped; the race axis is decided and recorded; the parity
table's channel section re-states every delta both directions at the
new state; all inherited gates green; designated growth per D2 with
Comparator landmark. Deferring any goal with an honest log entry is
success; trading soundness for coverage is not.
