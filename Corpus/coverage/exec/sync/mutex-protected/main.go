package main

import "sync"

var shared int

// The Mutex HB edge as OBSERVABLE ordering (sync/mutex.go: "the n'th
// call to [Mutex.Unlock] 'synchronizes before' the m'th call to
// [Mutex.Lock] for any n < m"): two goroutines increment under the
// lock; every interleaving yields 2 — mutual exclusion makes the
// counter schedule-independent (confluent lane).
func protectedCounter() int {
	shared = 0
	var m sync.Mutex
	done := make(chan int)
	go func() {
		m.Lock()
		shared = shared + 1
		m.Unlock()
		done <- 1
	}()
	m.Lock()
	shared = shared + 1
	m.Unlock()
	<-done
	return shared
}

// The mutex-protected write is VISIBLE after Lock (the MP litmus's
// synchronized form, design note §10): the worker publishes under the
// lock and signals readiness through the lock itself — main loops...
// no loops needed: main's read section runs strictly after the
// channel join, and the mutex edge orders the worker's write before
// main's locked read on every schedule.
func protectedVisible() int {
	shared = 0
	var m sync.Mutex
	done := make(chan int)
	go func() {
		m.Lock()
		shared = 42
		m.Unlock()
		done <- 1
	}()
	<-done
	m.Lock()
	r := shared
	m.Unlock()
	return r
}

func main() {
	protectedCounter()
	protectedVisible()
}
