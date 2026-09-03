# The discrepancy backlog

[USER]-instituted 2026-08-31 (fidelity assessment, decisions 2 and
5): the ledger of KNOWN, DELIBERATE discrepancies between the
model/apparatus and the goal state — each parked by an explicit
decision, each carrying a retirement condition and a review date.
This file is for [USER]-parked structural items; per-row latitude
debts stay in docs/2026-08-11_latitude-inventory.md and fidelity
bugs in docs/BUGS.md (this file references, never duplicates).
Under the decay-date rule (decision 7) every entry here has a
review-by date; the reconciler surfaces overdue entries.

| id | discrepancy | parked by | retirement condition | review by |
|---|---|---|---|---|
| D-001 | Memory is unbounded and every allocation succeeds (residual: allocations that pass gc's limit check and then fail to allocate). Interim: (a) the allocation-succeeding-runs rider on consumer-facing claims — IN FORCE, scoped to true OOM (R16's append band is a separately recorded deterministic-panic residual of 5(b), not a rider case); (b) the deterministic maxAlloc panic class modeled — DONE 2026-09-02 (t5-maxalloc: latitude inventory R16, BUG-081 fixed / BUG-082 frontend-side, fixed the same day on the `bug082-maphint` lane; corpus `builtins/make-maxalloc`, 15 rows PASS since that fix). Target state ([USER], Cerberus-C analogy): memory bounded-and-very-large — reasoning over arbitrary contexts accounts for allocation failure; execution runs essentially never hit it. | [USER] 2026-08-31 (decision 5) | the bounded-very-large memory model designed and landed (allocation-failure outcome + budget parameter), superseding the rider | 2026-11-30 |
| D-002 | Stdlib coverage via frontend INJECTION (5 mechanisms, ~3.3k lines, 20 functions + 2 shadow types) — vs the 2026-08-16 [USER] ruling to retire injection. Interim freeze: [AGENT] policy, confirmed [USER] 2026-09-01 (revisit trigger: stdlib-coverage urgency pre-retirement-design) — injection surface FROZEN (no new mechanisms/shims without [USER] exception); Fields-standard validation on any shim that changes (the [USER] words instituted the park + this backlog entry; the freeze/Fields-standard rule is the agent's fail-closed interim, decision 2 retag D3-3). 2026-09-03 [AGENT] note: BUG-086's repair (lane `bug086-shim-closure`) changed injection PLUMBING only — a declared per-shim dependency table (`stdlibShimDeps`) closed transitively at inject time, checked against the shim sources by a build-time test — not the allowlist and not any shim body; the frozen surface is unchanged in size and meaning. 2026-09-03 [USER] (relayed by the [AGENT] coordinator): the atomics typed-wrapper shadow model (`docs/2026-09-03_atomics-w1-design.md` §2, §6 item 2) CONFIRMED not shim injection under this entry — the surface count is unchanged by wave 1. | [USER] 2026-08-31 (decision 2: "design a proper retirement… park for now"; interim freeze [AGENT], confirmed [USER] 2026-09-01) | the retirement design note ([USER] design gate) + its first implementation | 2026-10-31 |
