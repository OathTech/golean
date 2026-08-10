package main

import "sync"

var rwOrd int

// The RWMutex acquisition-order envelope pin (audit fix round
// 2026-08-10, F1): with main holding the write lock, a writer and a
// reader both contend; which acquires first after main's Unlock is
// schedule latitude. gc's realized point is DETERMINISTIC here —
// Unlock semreleases every parked reader BEFORE rw.w admits the next
// writer (rwmutex.go:206-217), so gc exhibits 10 (reader first) on
// every run — while the model also admits 20 through the
// writer-parks-later schedules. Both accesses to rwOrd are under
// mutually exclusive lock modes (write lock / read lock), so the case
// is race-free on every path; the spawn and done edges order the reset
// and the readout.
func rwOrder() int {
	rwOrd = 0
	var m sync.RWMutex
	done := make(chan int)
	m.Lock()
	go func() {
		m.Lock()
		if rwOrd == 0 {
			rwOrd = 20
		}
		m.Unlock()
		done <- 1
	}()
	go func() {
		m.RLock()
		if rwOrd == 0 {
			rwOrd = 10
		}
		m.RUnlock()
		done <- 1
	}()
	m.Unlock()
	<-done
	<-done
	return rwOrd
}

func main() {
	rwOrder()
}
