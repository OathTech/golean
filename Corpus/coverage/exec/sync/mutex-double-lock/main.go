package main

import "sync"

// Lock of an already-locked mutex with no other goroutine to unlock it
// parks the only goroutine: gc's detector aborts with the fixed
// deadlock fatal (probe p06) — the EXISTING deadlock terminal; a
// parked sync op counts as asleep exactly like a parked channel op.
func doubleLock() int {
	var m sync.Mutex
	m.Lock()
	m.Lock()
	return 0
}

func main() {
	doubleLock()
}
