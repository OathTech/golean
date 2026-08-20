package main

// Promoted / embedded sync.Mutex operations (raft W4.1 item 5 —
// H-12/G-6, the MemoryStorage shape): `ms.Lock()` where the mutex is
// an EMBEDDED field and the receiver is the embedding struct. The
// frontend routes statement/defer-position promoted sync ops through
// the same sync-op lowering as direct ones, with the receiver address
// adjusted through the embedded-field hops at the call site; anything
// outside statement/defer position (TryLock in a condition, method
// values) keeps failing closed.

import "sync"

// store mirrors raft's MemoryStorage: a struct embedding sync.Mutex,
// operated on through pointer-receiver methods.
type store struct {
	sync.Mutex
	n int
}

func (s *store) bump() {
	s.Lock()
	s.n++
	s.Unlock()
}

func (s *store) bumpDeferred() int {
	s.Lock()
	defer s.Unlock()
	s.n += 10
	return s.n
}

func promotedStmt() int {
	s := &store{}
	s.bump()
	s.bump()
	return s.n
}

func promotedDefer() int {
	s := &store{}
	return s.bumpDeferred()
}

// Promotion from an addressable VALUE variable (no pointer in sight):
// the pointer-receiver promoted op takes the field's address.
func promotedValueVar() int {
	var s store
	s.Lock()
	s.n = 7
	s.Unlock()
	return s.n
}

// The HB edge survives promotion: two goroutines under the promoted
// lock; mutual exclusion makes the counter schedule-independent.
func promotedCounter() int {
	s := &store{}
	done := make(chan int)
	go func() {
		s.Lock()
		s.n = s.n + 1
		s.Unlock()
		done <- 1
	}()
	s.Lock()
	s.n = s.n + 1
	s.Unlock()
	<-done
	return s.n
}

// Expression-position promoted sync ops STAY refused (fail closed):
// this row is red at frontend-export by design.
func promotedTryLockExpr() int {
	s := &store{}
	if s.TryLock() {
		s.Unlock()
		return 1
	}
	return 0
}

func main() {
	println(promotedStmt(), promotedDefer(), promotedValueVar(), promotedCounter(), promotedTryLockExpr())
}
