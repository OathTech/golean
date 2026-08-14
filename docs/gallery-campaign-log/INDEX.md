# The Gallery Campaign log — INDEX (2026-08-15)

Charter: `docs/2026-08-15_gallery-campaign.md`. This directory is the
campaign's running record: ONE FILE PER GOAL (`g0.md` … `g4.md`) plus
this index (per-goal totals + checkpoint summaries), so parallel
sub-lanes never write the same file (process amendment `ea7c689a`,
user-authorized 2026-08-15).

## What the log is

Per-unit entries (example / extension / dossier / debt item): status,
judgment calls, findings, costs. The log updates IN THE SAME COMMIT as
the work it describes. Checkpoint summaries land here at least every 5
units, with honest totals per goal (complete / gap / remaining).

**The tension rule** (charter §Judgment calls): where principles
tension, **honesty beats velocity beats elegance**. A recorded honest
gap outranks a ground-out grind; a grind outranks a pretty claim that
overstates.

**Judgment-call format** (one line each, in the owning goal file):
`JC: <the call> — <the principle applied>.`

## Per-goal totals

| goal | done | remaining | notes |
|---|---|---|---|
| G0 (opening kit phase) | 5 of 5 mandatory units; (d) assessed → deferred to its pulling G1 example | 0 — G0 CLOSED (flagship rule discharges inside G1 by charter design) | see `g0.md` |
| G1 (gallery to twenty) | 0 of ≥13 new COMPLETE entries | ≥13 (7 shipped pre-campaign) | |
| G2 (extensions) | 0 of ≥3 | ≥3 of E1–E4 | |
| G3 (evidence dossiers) | 0 | register = denominator, fixed at dossier-lane start | register lives in `g3.md`, **enumerated by the dossier lane's first commit** (process amendment `ea7c689a`: the register is that lane's deliverable, not G0's) |
| G4 (infrastructure debt) | 0 of 4 | 4 | |

## Checkpoint summaries

(at least every 5 units; newest first)

- 2026-08-15, checkpoint 1 (units G0.1–G0.4 + (d), 7 commits): G0
  CLOSED. Log init; brick-wp mapping note; P5 setup-iteration schema
  (kit +2 lemmas, ALL 9 shipped setup inductions retrofitted, zero
  `strongRecOn` setup copies survive); MapMem promotion (wordcount
  retrofitted −346/+17 in Pure, chartered histogram + fib-memo);
  entry-equation completion (all 10 entry eqs derived, macro gains
  the program-generic form, example modules net −131); Audit/Kit.lean
  (81 verbatim kit-surface axiom pins). (d): bounded-iteration
  variant assessed and deferred to its pulling G1 example. Totals:
  G0 5/5; G1–G4 untouched. Headline statements byte-unchanged
  throughout; every commit's tree built green (targeted builds per
  commit; full `scripts/ci` PASS at the G0.2 tip and at this tip —
  fast gate + `GOLEAN_ALLOW_NO_DIFF=1`, proofs-only lane, cached
  full differential record at the merge-base stands).
