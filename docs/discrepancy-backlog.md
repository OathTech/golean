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
| D-001 | Memory is unbounded and every allocation succeeds. Interim: (a) the allocation-succeeding-runs rider on consumer-facing claims + (b) the deterministic maxAlloc panic class modeled (Tier 5). Target state ([USER], Cerberus-C analogy): memory bounded-and-very-large — reasoning over arbitrary contexts accounts for allocation failure; execution runs essentially never hit it. | [USER] 2026-08-31 (decision 5) | the bounded-very-large memory model designed and landed (allocation-failure outcome + budget parameter), superseding the rider | 2026-11-30 |
| D-002 | Stdlib coverage via frontend INJECTION (5 mechanisms, ~3.3k lines, 20 functions + 2 shadow types) — vs the 2026-08-16 [USER] ruling to retire injection. Interim freeze: [AGENT] policy pending [USER] confirmation — injection surface FROZEN (no new mechanisms/shims without [USER] exception); Fields-standard validation on any shim that changes (the [USER] words instituted the park + this backlog entry; the freeze/Fields-standard rule is the agent's fail-closed interim, decision 2 retag D3-3). | [USER] 2026-08-31 (decision 2: "design a proper retirement… park for now"; interim freeze [AGENT], confirmation queued) | the retirement design note ([USER] design gate) + its first implementation | 2026-10-31 |
