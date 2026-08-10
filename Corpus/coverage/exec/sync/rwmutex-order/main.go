package main

import "sync"

var rwOrd int

// The RWMutex acquisition-order envelope pin (audit fix round
// 2026-08-10, F1): with main holding the write lock, a writer and a
// reader both contend; which acquires first after main's Unlock is
// schedule latitude. gc's Unlock is deterministic at the BOTH-PARKED
// state (it semreleases every parked reader BEFORE rw.w admits the
// next writer, rwmutex.go:206-217), but the program reaches other
// states too, so gc realizes BOTH members (delta-review round 2
// measurements: plain 297x10/3x20 over 300; under -race 56x10/64x20
// over 120 — the lane's own dual sampling witnesses both). Both accesses to rwOrd are under
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
