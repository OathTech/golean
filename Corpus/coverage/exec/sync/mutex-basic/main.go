package main

import "sync"

// Single-goroutine lock/unlock discipline (the semantics/lock.go shape:
// "locks are correctly interpreted"): Lock and Unlock are cell ops, no
// blocking, no scheduler involvement (sequential conservation).
func lockUnlock() int {
	m := new(sync.Mutex)
	m.Lock()
	x := 7
	m.Unlock()
	return x
}

// The idiomatic defer-unlock pairing through the existing defer
// machinery.
func deferUnlock() int {
	var m sync.Mutex
	f := func() int {
		m.Lock()
		defer m.Unlock()
		return 3
	}
	total := f() + f()
	return total
}

// Value semantics (probe p10): a copy of a LOCKED mutex carries the
// locked state; unlocking the copy does not unlock the original, and
// both unlocks succeed. The runtime detects nothing (copy-after-use is
// vet's business, not the runtime's — design note §3).
func copyCarriesState() int {
	var m sync.Mutex
	m.Lock()
	c := m
	c.Unlock()
	m.Unlock()
	// Both are now unlocked; locking each again must succeed.
	m.Lock()
	c.Lock()
	m.Unlock()
	c.Unlock()
	return 11
}

// A locked Mutex is not associated with a particular goroutine (probe
// p09): main locks, the worker unlocks, main re-locks. The channel
// receives order the phases deterministically.
func crossGoroutineUnlock() int {
	var m sync.Mutex
	m.Lock()
	done := make(chan int)
	go func() {
		m.Unlock()
		done <- 1
	}()
	<-done
	m.Lock()
	m.Unlock()
	return 5
}

func main() {
	lockUnlock()
	deferUnlock()
	copyCarriesState()
	crossGoroutineUnlock()
}
