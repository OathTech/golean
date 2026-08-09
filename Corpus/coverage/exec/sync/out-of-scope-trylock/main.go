package main

import "sync"

// PERMANENT-until-lifted refusal marker (design note §9): TryLock is
// OUT of slice-2 scope — it is the spin-wait enabler whose termination
// class belongs to the atomics arc's FairStream (design note §6), so
// the frontend refuses it rather than modeling it early.
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
