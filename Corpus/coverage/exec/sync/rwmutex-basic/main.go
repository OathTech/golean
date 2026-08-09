package main

import "sync"

var rwShared int

// Concurrent (here: sequential re-entrant, no writer pending) read
// locks are admitted: readers count up and down without exclusion.
func rlockTwice() int {
	var m sync.RWMutex
	m.RLock()
	m.RLock()
	x := 9
	m.RUnlock()
	m.RUnlock()
	// The read lock is fully released: a writer can now acquire.
	m.Lock()
	m.Unlock()
	return x
}

// The RWMutex write→read HB edge (sync/rwmutex.go: "For any call to
// RLock, there exists an n such that the n'th call to Unlock
// 'synchronizes before' that call to RLock"): the worker's write under
// Lock is visible to main's read under RLock on every schedule.
func writeThenReadOrdered() int {
	rwShared = 0
	var m sync.RWMutex
	done := make(chan int)
	go func() {
		m.Lock()
		rwShared = 42
		m.Unlock()
		done <- 1
	}()
	<-done
	m.RLock()
	r := rwShared
	m.RUnlock()
	return r
}

func main() {
	rlockTwice()
	writeThenReadOrdered()
}
