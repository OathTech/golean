package main

import "sync"

// Wait with a positive counter and nobody left to Done parks the only
// goroutine (probe p07): the fixed deadlock fatal — parked WaitGroup
// waiters count as asleep.
func waitDeadlock() int {
	var wg sync.WaitGroup
	wg.Add(1)
	wg.Wait()
	return 0
}

func main() {
	waitDeadlock()
}
