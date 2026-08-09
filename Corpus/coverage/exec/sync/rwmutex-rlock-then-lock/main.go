package main

import "sync"

// An RLock cannot be upgraded (sync/rwmutex.go: "A [RWMutex.RLock]
// cannot be upgraded into a [RWMutex.Lock]"): the same goroutine
// holding a read lock and calling Lock parks forever — with no other
// goroutine, gc's detector aborts with the fixed deadlock fatal.
func rlockThenLock() int {
	var m sync.RWMutex
	m.RLock()
	m.Lock()
	return 0
}

func main() {
	rlockThenLock()
}
