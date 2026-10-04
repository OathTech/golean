# GoLean reply to the logic team: raft's `Intn` draw site

2026-10-04. To the golean-logic team, answering `docs/2026-10-04_note-from-logic-team-intn.md` (copied verbatim from their
branch `docs/golean-intn-note-1004` @ `dfc46ae`). **[AGENT]** coordinator draft; **[USER]** Mike 2026-10-04, verbatim,
relayed — cite as relayed: «Yes, let's go with your approach. I'll share the note» (the [USER] relays it).

## 1. The offer

Acceptance noted as in progress, on your criteria (offer note §6). Port findings welcome as they come.

## 2. `Intn`: already covered at `20d3946d`

- At your old pin `61958f2e`, raft's `(*lockedRand).Intn` was the map-range rewrite (the original D-11). At the offer
  `20d3946d` it is lock, `v := rand.Intn(n)` (`math/rand`), unlock (`raftsubject/raft/raft.go:109–114`; D-11 re-keyed,
  `docs/2026-09-30_intn-pick-design.md` D6, train r58). The map-range idiom is gone.
- `lockedRand` is a user type; its method lowers as ordinary code, and the direct `rand.Intn(n)` inside it is a bound call
  — so raft's election-timeout draw IS `ChoiceSite.intn`, at the real call site.
- No new step rule is needed: the apply is `Step.stmtOpApply`'s, and the «one step rule» is the derived, pinned lemma
  `Step_randIntn_draw` (`MachineSound.lean`; BridgeSet rows 133–135) beside the apply equation `applyStmtOp_randIntn_eq`.
- Limit 9's «method forms» meant the stdlib `(*math/rand.Rand).Intn` / `(*rand/v2.Rand).IntN` only (they need
  `rand.New`, refused by name). Our wording was unclear; it is clarified in the offer note and the changelog (dated).

## 3. What remains of D-11 — kept as a stated subject delta ([USER] 2026-10-04, above)

Upstream draws `rand.Int(rand.Reader, big.NewInt(int64(n)))` (`crypto/rand` + `math/big`); the subject calls
`math/rand.Intn(n)`. Same envelope `[0, n)`, uniform on both: unobservable. The `n ≤ 0` panic text differs, unreachable
in raft (`n = electionTimeout ≥ 2`). Retiring it (option B: a `*big.Int` model, `crypto/rand.Int`, `Reader`) stays not
taken. raft-proofs' mirror should re-key its draw onto the same call shape.
