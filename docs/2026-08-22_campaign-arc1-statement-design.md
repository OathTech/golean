# Campaign Arc 1 — the T1 statement: design of record

Campaign lane, 2026-08-22. Governing: the constitution §2.1/§2.2.
Every decision here is **[AGENT]** unless marked [USER]; the statement
itself is QUEUED for [USER] designation (constitution §3.2 — the
walker list is Mike's act) and lands on a branch behind the [USER]
merge gate either way.

## 1. The subject: the choice-driven twin driver

`tools/raftsubject/twin-chdriver.go` — the same n=3 RawNode twin,
S1–S3 per-step checker, and S4 stopping as the schedule battery
(`twin-lib.go`), with the DELIVERY ORDER drawn each round by a
one-draw map-range pick over the live message multiset.

**[AGENT] The ∀ch realization.** The constitution's "for ALL choice
streams" is realized through Go's own map-iteration latitude (the
machine's `mapIter` choice site): the driver ranges over a
`map[int]bool` of live multiset indices and delivers the first
element the iteration yields. This grounds the quantifier in REAL
language latitude — a conforming Go implementation genuinely may
deliver in any order, and `go run` samples different orders per
execution (measured: 8 runs → 8 distinct pick sequences, all ending
`viol=0 complete=1`) — rather than in an artificial input stream. It
is the certified miniature's mechanism
(`multipkg/mini-raft-twin/choice-order`) at the real subject. The
reliable-first envelope is exact: every message is delivered exactly
once (no drop, no dup); reordering is unbounded (any live message may
go next).

**[AGENT] The client protocol is deterministic** so the map pick is
the ONLY nondeterminism: campaign(1) once (uncontended; victory needs
only delivery), propose-at-quiescence with drop-and-retry, no ticks
(the D-11 jitter seam stays closed, as in the battery). Consequences:
one election, term 1, one claim — the v1 statement's exercise floor,
not its ceiling; richer drivers (contended elections, term-2 rounds)
are STRENGTHENINGS of the witness family, and the schedule battery
already exercises those shapes outside the ∀-form.

**[AGENT] Honest-stop discipline**: fuel-bounded outer loop; quiescent
without S4, or a propose stuck at quiescence, HALTS with
`complete=0` — an honest incomplete that can never satisfy the
completion witness, never a claim.

## 2. The observable: five integers

`twinChoiceVerdict() (violations, claims, committed, complete, floor)`
— the statement entry point. The per-round trace (`probeTwinChoice`)
is instrument-only: different orders legitimately produce different
traces, so the trace is NOT quantified over; the verdict quintuple is.

**T1 (to be pinned):** for all choice streams and all fuel, if the
lowered `twinChoiceVerdict` run completes (`.ok r`), then
`violations r = 0`.
**Completion witness:** there exist a stream and fuel with a
completing run where `complete = 1 ∧ floor = 1`.

**The aboutness seam, stated plainly** (this is the load-bearing
sentence a human must believe): "violations = 0" means the HARNESS'S
OWN CHECKER — S1 election safety, S2 log/apply agreement under the
§2.2-item-4 projection, S3 apply monotonicity with loud anomaly on
unmodeled entry types, checked at every apply/claim step inside the
program — recorded nothing at any step of that run. The per-step
character of §2.1's prose is carried by the checker's placement, not
by a Lean-side trace quantifier; the checker's Go source
(`twin-lib.go:298-334` vintage f64d9b21) is therefore statement-
adjacent trust surface, audited as such (launch audit D3/D5; the
projection fine print is constitution §2.2 item 4).

## 3. The pin: elaboration-time wire decode

**[AGENT]** The lowered program is pinned as a checked-in WIRE
(frontend JSON) decoded at elaboration — the golden-lowering
mechanism (`sliceLowered` precedent) — not as a Lean repr literal:
the twin drags the whole raft library and a repr literal would be
megabytes; the decode path fails loud on any drift and
`scripts/check-golden` gets an entry guarding staleness (additive
gate change, the mechanism working as designed). The pinned artifact:
`baselines/golden/twin-chdriver.wire.json` + its decode-and-hash
guard.

## 4. What Arc 2 owes (the witness) and the route question

The completion witness needs a kernel-checked completing run. Routes,
decided when Arc 2 opens (logged then): (a) WP walk over the twin
(the quorum-flagship mechanism — symbolic-length walks over real
lowered code — at ~30-round scale, one fixed stream); (b) a
certified-execution route (a single-run analogue of `checkCert`).
Enumeration is NOT a route at this scale and is not the claim's
mechanism.

## 5. Queued for [USER]

- Designation of T1 + the witness statement (walker list, §3.2).
- The merge of Arc 1 itself (branch-complete + audit ask, §4.1).
