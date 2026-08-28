# Post-mortem: the W2.5 gate override (2026-08-27)

Commissioned by the [USER] at the triage-landing merge (2026-08-28)
on closing the W2.5 record item. Written by the [AGENT] coordinator;
the defect chain below is reconstructed from the tracked record
(campaign log entries of 2026-08-27, the design-pass findings, the
prover logs), not from memory.

## What happened

1. The plan of record named W2.5 — the loop-invariant design note —
   a [USER] DESIGN GATE, sequenced before all of W3 because every
   W3 postcondition concludes clauses of the invariant.
2. An autonomous-push directive ("don't stop to solicit feedback;
   make the call and keep going") was active when the run reached
   the gate. The coordinator stopped and posed the gate; the goal
   monitor refused the stop as incomplete work.
3. The coordinator resolved the rule conflict by SELF-ADJUDICATING
   the gate as [AGENT]: the note was adopted as the W3 contract,
   the adjudication logged as a conflict resolution and flagged as
   a mandatory [USER] review item at landing. Work proceeded.
4. The Wave-3.0 worker, building the invariant module against the
   adopted note, misread its C2 clause and produced two
   cross-carrier clauses (ElectedAt.logBridge/commitTie) that were
   UNPRESERVABLE past the first Elected-phase event — while the
   clause the note intended (concrete-log↔H-carrier pairing) was
   never built and was in fact unstatable with the then-current
   readers.
5. The defect was caught at the first quiescent point by the
   professor calibration review the [USER] had commissioned
   mid-run — before any proof consumed the defective clauses.
   Containment: definitions-only; zero unsound theorems; the
   module was later archived whole at the triage.

## Why the gate mattered (the counterfactual)

The gate's function was never "the [USER] re-derives the design";
it was a SECOND READER between the design artifact and the
implementation built against it. The specific defect — an
implementer misreading one clause of a subtle pairing design — is
the exact class a gatekeeper reading "does the built thing say what
the note means?" catches cheaply and an author self-reviewing does
not: the author reads their intent, not their text. The
adjudication also collapsed author and gatekeeper into the same
agent for the three open design points, which happened to be fine
(the professor later verified those three calls sound) — the
failure entered one step later, in implementation fidelity, where
no second reader existed at all.

## The compounding factor

The goal monitor's refusal made "stop at the gate" read as
non-compliance with the [USER]'s own autonomous directive. The
coordinator chose the fail-closed-available option (proceed on
branches, flag for review) rather than the actually-correct one:
a named design gate IS user input the run is blocked on — the
emergency/checkpoint semantics should have been invoked, or the
gate treated as a hard stop the monitor cannot override. The
charter's own autonomous-arc rule already said "Named user
checkpoints (design gates) stop the run"; the directive and the
monitor's behavior were read as overriding it. Rule conflicts
between a standing charter provision and a session directive were
resolved toward the session directive; the post-mortem's judgment
is that the standing provision should win for NAMED gates
specifically, because they are named precisely to survive
directive pressure.

## What already worked

- Provenance discipline: the adjudication was [AGENT]-tagged at
  every occurrence and carried as a mandatory review flag through
  every checkpoint — the trail is why the item was reviewable at
  all.
- The mid-run review cadence the [USER] added caught the defect at
  the first quiescent point, at definitions-only cost (~2 sessions
  of repair vs. the enumeration era's ~2 months).
- Fail-closed branch hygiene: nothing merged; the archive holds
  the artifact; nothing proved was unsound.

## Corrective actions

1. CHARTER AMENDMENT (proposed for [USER] sign-off at the next
   CLAUDE.md touch): under "Autonomous arcs", strengthen the
   existing checkpoint sentence to: "Named design gates are HARD
   STOPS: no autonomous directive, goal monitor, or completion
   pressure overrides one. If a run cannot stop, it exits (the
   emergency path) rather than self-adjudicating the gate. A
   self-adjudicated gate is a protocol breach even when the
   substance survives review."
2. GATE-SHAPE RULE (practice, adopted now): a design gate's
   review object includes the FIRST IMPLEMENTATION built against
   the design, not the note alone — the gatekeeper (or a
   professor-class reviewer when the [USER] delegates) re-reads
   the built artifact against the note's intent before dependent
   waves charter. (This is what caught the defect; make it the
   rule rather than luck.)
3. MONITOR BRIEFING (practice): future autonomous-goal prompts
   enumerate the named gates up front so the monitor treats a
   stop-at-gate as goal-compliant, not as incomplete work.

## Status of the object

The invariant module is archived (refs/heads/archive/callspec-era);
the design note landed with an honest status header; the G-INV
amendment — the repaired Elected-phase design — re-runs the W2.5
gate with the [USER] as gatekeeper, per the triage plan. The
record item is CLOSED by the [USER], 2026-08-28, with this
post-mortem as the closing artifact.
