package main

// BUG-005 envelope row, REWORKED to the membership lane (bug-fix arc,
// 2026-08-19 ruling — memo §5: the narrowings are REJECTED, the FULL
// literal envelope ships). The original row pinned gc's exact count 3,
// which encoded the dead narrowing 1 ("a produced key is never
// produced again, even across delete + re-create"). Under the ADOPTED
// reading (spec-interpretations.md / ledger L-012): a deleted key is
// removed from the produced-set, and a deleted-then-re-created key is
// a NEW entry — created during iteration, so spec#For_statements'
// created-entries clause applies: "may be produced during the
// iteration or may be skipped. The choice may vary for each entry
// created and from one iteration to the next."
//
// Each iteration deletes the CURRENT key and immediately re-adds it,
// so under the full envelope the trace set is genuinely UNBOUNDED
// (every re-created key is re-producible forever). The subject
// truncates its own observation at 4 productions: -1 is an ADMITTED
// member (the visible face of the unbounded tail), not a violation.
// The admitted observation set is exactly {3, 4, -1}:
//   3  — each start key produced once, stop as soon as it is legal
//        (gc's realization: 400/400 probe runs, incl. forced growth);
//   4  — one re-produced re-created entry (or one extra pick) before
//        stop — the latitude member gc never exhibits;
//   -1 — five or more productions: the unbounded tail, truncated.
// Stop is legal only once no never-removed start key remains
// unproduced (the mandatory clause, spec-forced) — every start key
// here is deleted on production, so after the three start keys are
// produced the mandatory set is empty.
//
// PRE-SURGERY COLOR: RED, deliberately (pinned on BUG-005's Cases
// line). The snapshot machine never observes the deletes/re-adds, so
// its enumerated set is the singleton {3} and the membership lint
// refuses a singleton-set membership row — the dead narrowing made
// visible as a red. The (L) surgery makes the machine realize the
// envelope; this row flips green there, and thereafter fails loudly
// if the machine admits alien keys, drops a mandatory start key, or
// exceeds the admitted set.

func mapDeleteReAddDuringRange() int {
	m := map[int]int{1: 1, 2: 2, 3: 3}
	n := 0
	for k := range m {
		n++
		if n > 4 {
			return -1 // the unbounded tail, truncated: an ADMITTED member
		}
		delete(m, k)
		m[k] = k
	}
	return n
}

func main() {
	println(mapDeleteReAddDuringRange())
}
