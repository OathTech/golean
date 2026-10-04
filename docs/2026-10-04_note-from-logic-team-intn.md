# golean-logic note to GoLean: the offer, and raft's `Intn` draw site

2026-10-04. To the GoLean team. **[USER]** Asked for a short note on this
point. **[AGENT]** Drafted for the user to relay.

## 1. The offer

We accept the re-pin offer (`20d3946d`, tag `logic-offer/2026-10-03`). The
port is under way on our side. Acceptance is on our criteria, as your §6
says: our full gate, the initialized and all-choice theorems, the native
edit and mutation controls, and all three isolated consumers, all at the new
pin. Your dry run's error census matches what our migration-readiness
estimate predicted. The work is concentrated in our emitter and six
hand-written modules. Thank you for the per-request mapping in §3.

## 2. One request: bind the method form of `Intn`

Your limit 9 says that native `Intn` binds only direct `math/rand.Intn` and
`math/rand/v2.IntN` call sites, not method forms (D3). Raft's election-timeout
draw is a method, `(*lockedRand).Intn`, at upstream `raft.go:2054`, in
`resetRandomizedElectionTimeout`. Our `cluster3` census found it is the only
`Intn` call site that the RawNode roots reach, and it executes on every run.
raft-proofs' mirror draws at that same call site.

So the native choice site does not yet reach raft's actual draw, and the D-11
map-range rewrite stays in place. Could the binding cover this method form?
That could be `(*lockedRand).Intn` specifically, or methods whose body is a
locked call to an `Intn`-shaped source. With it bound, D-11 could be retired
and the choice coupling would name the real call site. On our side this needs
one step rule for `ChoiceSite.intn`, which we estimate at 1–2 sessions after
the port. Whether to bind the method form, or to keep D-11 as an explicit
premise, is your decision.

Nothing else is requested now. We will send findings from the port if it
turns up any.
