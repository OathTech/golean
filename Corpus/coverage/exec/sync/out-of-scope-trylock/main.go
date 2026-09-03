package main

import "sync"

// WAS the PERMANENT-until-lifted refusal marker (design note §9): TryLock
// was OUT of slice-2 scope as the spin-wait enabler whose termination
// class belongs to the fairness tier. LIFTED 2026-09-03 (Q-TRYLOCK, RULED
// [USER] 2026-08-31 — docs/2026-08-31_qrow-rulings.md row 5): TryLock is
// a width-2 choice site (acquire | mem#locks' spurious false); this row
// is a membership row over {1, 0}; termination claims for spin loops stay
// in the fairness class (sync/trylock/spin-until-trylock, nonterm=).
func tryLockUncontended() int {
	var m sync.Mutex
	if m.TryLock() {
		m.Unlock()
		return 1
	}
	return 0
}

func main() {
	tryLockUncontended()
}
