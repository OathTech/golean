# Dossier E9-created — entries created during map iteration (singleton "never produced")

G3 register item 7. Inventory §E9 (the created-entries sub-point; §9
flag 4 records that the narrowing lives only in BUG-005's dismissal
sentence). Proposal only — batched for user ruling.

## 1. The latitude

When a map entry is CREATED during a `range` iteration, the spec
grants per-entry, per-iteration latitude: produced or skipped. The
machine's snapshot-at-entry design (`mapRangeSnapshotEntries`,
Machine.lean:873–921) resolves it to the singleton "never produced".

## 2. Evidence

### SPEC (go1.26.5, §For statements)

> "If a map entry is created during iteration, that entry may be
> produced during the iteration or may be skipped. The choice may vary
> for each entry created and from one iteration to the next."

Contrast the neighboring DELETE sentence, which is FORCED ("will not
be produced") — that is BUG-005's open violation, out of this
dossier's scope.

### GC probe (`docs/evidence/2026-08-15-dossier-e9-created/`, verbatim)

200 iterations × 2 executions, growth-regime insertions (4-entry map,
8 fresh keys inserted during the range):

    runs: 200 | runs producing >=1 created entry: 180 | total created entries produced: 542
    runs: 200 | runs producing >=1 created entry: 175 | total created entries produced: 563

**gc PRODUCES created entries in ~90% of runs on this shape.** The
per-run and per-execution variance realizes the spec's "may vary"
clause densely (the map-order re-randomization regime — the
doctrine's best-sampled envelope family).

### The consequence (the dossier's central finding)

The singleton "never produced" is a CONFORMING implementation point
(the spec permits skipping every created entry) — the machine is not
wrong as an implementation. But under the two-bounds doctrine the
machine must CONTAIN observed behavior (`observed ∈ modeled` is the
lower bound's whole meaning), and gc's produced-created-entries
observations are outside the singleton at ~90% frequency. On any
membership-lane case with this shape, `observed ∉ modeled` — the
definitional-bug class, in the too-narrow direction. The inventory's
posture ("a (b-n) narrowing INSIDE the envelope, currently recorded
only via BUG-005's dismissal sentence") records the narrowing but had
no measurement of how often gc leaves it; now it has one.

Mitigating scope fact: the E9 envelope statement is SCOPED to
mutation-free iteration (arc-final F14), so no current claim is
falsified — live-mutation shapes are outside the stated scope and are
BUG-005's red territory. The finding sharpens what the BUG-005 surgery
must deliver, it does not open a new hole in shipped claims.

### Corpus / de-facto spec

Insert-during-range is a real (if discouraged) idiom — worklist
algorithms that add follow-up keys while draining a map rely on
"produced or skipped" being harmless to termination of their logic
(each pass re-checks). Deployed code cannot rely on EITHER pure point
(gc varies per entry); de-facto pressure therefore supports a WIDE
envelope, not a singleton — the map-iteration randomization history
shows the Go team actively preventing de-facto pins here (doctrine's
own example).

### XIMPL / ARCH

NOT-OBTAINED (no second toolchain/web). ARCH note: the produce-or-skip
sentence has been stable since Go 1 (local knowledge, UNVERIFIED).

## 3. Proposed disposition

**ENVELOPE at the BUG-005 surgery: a per-created-entry produce/skip
choice (Choices-consuming, alongside the live-iteration rework);
until that slice lands, the singleton stays but its record is UPGRADED
from "fine" to "known-outside, queued" — the same honesty class as
R3.**

- ARGUMENT: gc is measured outside the singleton at ~90% on growth
  shapes — by the doctrine's §8 correction ("a probed gc-elsewhere
  observation is an observed-∉-modeled candidate, not a divergence to
  be at peace with"), the dismissal sentence's "fine" is no longer an
  adequate record. The natural mechanism (pick-next over the LIVE
  entry set, skipping absent keys) is exactly what the BUG-005 surgery
  builds; the created-entries choice is one more arm of the same
  rework, and the inventory already says the narrowing "should get its
  explicit statement at the site in the same movement".
- COUNTER-ARGUMENT (keep the singleton permanently): strict-lane
  determinism wants one point; live-mutation ranges are anti-idiom;
  the F14 scope sentence already excludes these shapes from claims.
  REBUTTAL: the scope sentence keeps claims honest but leaves the
  membership lane unable to certify a real, spec-blessed idiom
  family; the surgery is already scheduled for the FORCED delete
  violation — riding it costs one choice arm, not a new slice.
- COUNTER-ARGUMENT (widen to produce-always instead): no — gc skips
  too (20–25/200 runs produced none); only the two-outcome per-entry
  choice contains the oracle.
- WHAT WOULD CHANGE THE ANSWER: a decision to permanently REFUSE
  live-mutation ranges (fail-closed at the frontend/machine) — that
  would resolve BUG-005 and this sub-point together by refusal
  instead of envelope; honest, but it forfeits a certifiable idiom
  family and contradicts BUG-005's recorded fix direction.

## 4. Evidence gaps

- No probe of the NON-growth regime (insertions below the growth
  threshold) — gc's produce rate there may differ (bucket-position
  dependent). What would obtain it: the same probe with 1–2
  insertions into a large map. Bounded per the divergence guard; the
  growth-regime datum suffices for the disposition.
- XIMPL: NOT-OBTAINED.
