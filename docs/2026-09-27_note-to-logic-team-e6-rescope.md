# Note to the GoLean logic team: one change to the endorsed window (2026-09-27)

[AGENT] coordinator, GoLean semantics repo. Follows our proposal (`docs/2026-09-23_proposal-to-logic-team.md`), your
response (`docs/2026-09-23_response-from-logic-team.md`) and our charter (`docs/2026-09-23_batched-window-charter.md`).
Nothing else in the endorsed plan changes.

## What changed

You endorsed «E6 → label and execution bridges → P → C3 → B6 → C4», with E6 opening the window and ending in the
retirement of our legacy evaluation-order probe: `Stmt.unseqProbe`, `Cont.probeK`, `Step.unseqProbe`,
`ChoiceSite.unseqPanic`. The first slice, E6a, landed on `main` at train r49. Its census showed that retirement needs
far more grammar work than planned: 160 of the 175 remaining legacy emitters involve interface-typed and defined
non-struct fields, interface comparison, arrays and generic stencils, which no planned slice covers.

[USER] Mike ruled 2026-09-27: **the legacy triple survives into the single re-pin offer.** Retirement becomes a later
removal-only change, offered separately when the type-grammar work is done. The window proceeds directly to the label
and execution bridges.

## What it costs you

At the re-pin you port one `Cont` constructor (`probeK`), one `Step` rule and one choice site that you would otherwise
have seen deleted. Your fourteen fixtures and the eight F2 variants lower with zero `unseq` graphs and zero legacy
probes, both at our `3fb4a0d1` and under E6a (`docs/2026-09-24_customer-fixture-inventory.md`; the E6a audit re-ran
it). So the survivors cost `cases` arms, not rule proofs, for your current fragment. The changelog records it.

## What E6a changed that you will see at the re-pin

- The admission trigger refinement (a subset of the ruled rule): more statements lower as `unseq` graphs; none of yours.
- Library-unit code can now lower as graphs; the raft twin gained three graphs.
- Decoder hardening: an `after` edge on a literal `allocate` and forged source-local annotations refuse by name.
- BUG-116: main's legacy path picked the wrong panic when a failing operand sat left of an inline `len`/`cap`/`min`/
  `max` whose own operand panics. Fixed and rowed.

## Question

Does keeping the legacy triple through the re-pin change your migration plan or your preferred re-pin point
(your answer to question 10)? A sentence is enough.
