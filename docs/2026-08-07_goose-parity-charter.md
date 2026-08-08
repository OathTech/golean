# Goose-parity buildout — charter + standing-goal draft (2026-08-07)

**STATUS: BLESSED (user sign-off 2026-08-07) — charter of record for
the goose-parity buildout; the standing goal text below is ready to
set when the buildout launches (post arc-final audit). Note: grossmith
received a further upstream update 2026-08-07 (post-campaign); re-pin
its rev at buildout launch.** The buildout itself has NOT launched:
launching (setting the standing goal) is its own decision at the
channels-arc merge sign-off. (Self-contradiction cleaned at the
arc-final audit, F13, 2026-08-08: the blessing commit spliced the
BLESSED fragment into the draft's "the user has NOT signed this
charter off" sentence and left the line-11 "DRAFT for user review"
banner, so the charter of record could not be read as in force from
its own text; committed to docs/ 2026-08-07 from the working-note
.tmp/goose-parity-charter.md.)

Basis: `.tmp/goose-comparative-scoping.md` (Part B:
87 files importable today; the rung ladder) and the user's autonomy
design (2026-08-07 discussion): run long and independently; blockers
are SET ASIDE, never hard-blocking; the user checks in at the END; the
structure must never force unwise decisions or bake in what belongs in
discussion; an ESCAPE HATCH lets the agent halt at any time.

## Mission

Import Goose/Perennial's test corpus (phase-1 scope: the 87
importable files, goose @ 3be88bbb / perennial @ 43d4efab) into a
provenance-tagged corpus lane (`imported-goose/`, verbatim bodies,
wrappers below a marked line, rev-pinned) and walk each unit up the
rung ladder as far as it goes cheaply:

  R1 differential PASS (strict lane; the ~100 boolean oracles map
     mechanically onto the cases.tsv subject convention)
  R2 kernel total pin (`decide +kernel`-class, OOM convention) where
     the program is small enough
  R3 GoSpecC/GoSpec instance where existing machinery suffices
     (no new proof infrastructure for R3 in this buildout)

Maintain `docs/goose-perennial-comparison.md` (the standing matrix from
the scoping study's Part C) as rows change. Unit order: any; batch
size: worker's judgment; a natural batch is one feature class.

## Work structure

- UNITS are independent by construction. No unit's trouble may block
  another unit. There is no required completion percentage: the
  buildout's output is (landed units) + (the parking ledger) + (the
  final report), whatever the split.
- BATCH DISCIPLINE (the established cycle, batch-granular): red-first
  classification of each batch's cases before wiring; full
  `scripts/ci --diff` + same-commit re-pin per landed batch; ZERO
  drift on prior ids (any drift on an existing id = stop the batch,
  park the unit that caused it, report it in the ledger as a suspected
  GoLean bug with the repro — do NOT fix machine bugs in this
  buildout); check-bugs green; audit checkpoint (1 reviewer +
  refute-default verifiers) every ~3 batches or before any commit that
  touches shared infrastructure (scripts/, the lane definition).
- The 44 designated statements are byte-identical throughout (count
  corrected at the arc-final audit, F14: the S5 audit response added
  the 44th, goldenReturnsTwoC, before this charter was drafted; the
  mechanical list is proofs/Audit.lean + judge-config.json). proofs/
  may gain R2/R3 pins in Specs/ only; nothing joins the designated
  list in this buildout (that is an arc-level decision).

## The parking ledger — `docs/goose-parity-parked.md`

Anything blocker-shaped or decision-shaped goes here INSTEAD of being
resolved unilaterally. Entry format: unit; the precise question;
evidence gathered (probes, cites); options WITH costs; NO decision.
Parked = the unit is skipped and the buildout continues. A parked
entry is a SUCCESS outcome for a unit, not a failure — the ledger is
the deliverable the end-of-buildout check-in resolves.

MUST-PARK list (act on none of these, ever, in this buildout):
- anything touching GoCore semantics, the wire schema, or NativeToIR
  beyond mechanical decode reuse;
- any new envelope, narrowing, or latitude interpretation;
- any sync/atomic/time/FFI modeling (phase 2 by construction);
- anything statement-TCB (new designated statements, Surface changes,
  gate changes);
- any case where the honest classification is unclear under existing
  doctrine (park with the classification question);
- suspected GoLean bugs surfaced by imports (park with repro; the
  ledger is triage, the fix belongs to a maintenance round);
- any deviation from verbatim import that goes beyond the wrapper
  marker (if a file cannot be imported verbatim, park it).

MAY-DECIDE list (no parking needed): wrapper authorship below the
marker; case naming/ids; batch composition and order; oracle-to-int
encodings with corpus precedent; R2/R3 attempt-or-skip judgment per
unit (record skips with one-line reasons in the batch log).

## THE ESCAPE HATCH (user direction, verbatim intent)

The agent MAY AT ANY TIME, FOR ANY REASON, CALL A HALT. Halting means:
leave the tree clean and committed at the last green state; write
`docs/goose-parity-halt.md` stating why, the state of play (units
landed / parked / untouched), and what the agent believes should
happen next; end the goal. A halt is a LEGITIMATE terminal outcome of
the goal — the goal-completion condition explicitly includes it, so no
monitor can hold the goal open against a blocked agent. No
justification threshold applies: "something feels wrong and I want the
user to look" is sufficient reason.

## End-of-buildout report (the user's check-in package)

Counts (landed per rung / parked / skipped-with-reasons); the parking
ledger; comparison-matrix delta; suspected-bug list; anything the
agent would do differently — written as a dated docs/ note.

## Proposed standing-goal text (for the user to set, edit freely)

"Work the goose-parity buildout per docs/<charter-path>. Land
importable units up the rung ladder with the batch gate discipline;
park every blocker or decision-shaped question in the parking ledger
per the charter's MUST-PARK list — parking is success, not failure.
Never act on a MUST-PARK item. Zero drift on pre-existing corpus ids;
designated statements byte-identical. The goal is complete when every
phase-1 unit is either landed or parked AND the end-of-buildout report
is written — OR when you call a halt per the charter's escape hatch,
which you may do at any time for any reason. Do not merge to main;
the buildout branch awaits the user's check-in."
