// noodler probes — sync primitive contracts (sync design note; go_mem
// mem#locks/mem#once): misuse fatals, value-copy semantics, nested
// Once deadlock, cross-goroutine unlock.
package main

import "sync"

// RUnlock of an unlocked RWMutex is a runtime fatal.
func rUnlockOfUnlocked() int {
	var rw sync.RWMutex
	rw.RUnlock()
	return 1
}

// Unlock of an unlocked RWMutex (write side) is a runtime fatal.
func unlockOfUnlockedRW() int {
	var rw sync.RWMutex
	rw.Unlock()
	return 1
}

// Once.Do nested inside its own f deadlocks (the outer Do holds the
// once's mutex).
func onceNestedDeadlock() int {
	var once sync.Once
	n := 0
	once.Do(func() {
		once.Do(func() { n = 1 })
	})
	return n
}

// A copied Mutex carries the locked state: unlocking the copy is fine;
// the original stays locked and a second Lock deadlocks.
func mutexCopyCarriesState() int {
	var mu sync.Mutex
	mu.Lock()
	cp := mu
	cp.Unlock()
	mu.Lock()
	return 1
}

// A copied UNLOCKED mutex is independent: both lock fine.
func mutexCopyIndependent() int {
	var mu sync.Mutex
	cp := mu
	mu.Lock()
	cp.Lock()
	mu.Unlock()
	cp.Unlock()
	return 2
}

// Lock in one goroutine, Unlock in another is permitted.
func unlockFromOtherGoroutine() int {
	var mu sync.Mutex
	mu.Lock()
	done := make(chan int)
	go func() {
		mu.Unlock()
		done <- 1
	}()
	<-done
	mu.Lock()
	mu.Unlock()
	return 3
}

// WaitGroup reused after Wait returns.
func waitGroupReuse() int {
	var wg sync.WaitGroup
	total := 0
	for round := 1; round <= 2; round++ {
		res := make(chan int, 2)
		wg.Add(2)
		go func() { defer wg.Done(); res <- round }()
		go func() { defer wg.Done(); res <- round * 10 }()
		wg.Wait()
		close(res)
		for v := range res {
			total += v
		}
	}
	return total
}

// Wait on a zero counter returns immediately.
func waitOnZeroCounter() int {
	var wg sync.WaitGroup
	wg.Wait()
	wg.Add(1)
	wg.Done()
	wg.Wait()
	return 4
}

// Recursive read locking is fine when no writer waits.
func recursiveReadLock() int {
	var rw sync.RWMutex
	rw.RLock()
	rw.RLock()
	rw.RUnlock()
	rw.RUnlock()
	rw.Lock()
	rw.Unlock()
	return 5
}

// RLock while write-locked by the same goroutine deadlocks.
func rlockWhileWriteLocked() int {
	var rw sync.RWMutex
	rw.Lock()
	rw.RLock()
	return 6
}

// Once.Do with different funcs: only the first runs.
func onceDifferentFuncs() int {
	var once sync.Once
	n := 0
	once.Do(func() { n += 1 })
	once.Do(func() { n += 10 })
	once.Do(func() { n += 100 })
	return n
}

// Deferred Unlock during a panic still releases; a later Lock succeeds.
func deferUnlockDuringPanic() int {
	var mu sync.Mutex
	func() {
		defer func() { recover() }()
		mu.Lock()
		defer mu.Unlock()
		panic("x")
	}()
	mu.Lock()
	mu.Unlock()
	return 7
}

func main() {}
