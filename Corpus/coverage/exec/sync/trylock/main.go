package main

import "sync"

// Q-TRYLOCK (RULED [USER] 2026-08-31, row 5 of
// docs/2026-08-31_qrow-rulings.md; implemented 2026-09-03): TryLock /
// TryRLock modeled with mem#locks' spurious-failure member as the
// width-2 `tryLock` choice site. Result-observing rows are MEMBERSHIP
// rows over {success, spurious false} at acquirable states (gc exhibits
// only the success member — unexhibited-but-permitted: mem#locks "may be
// considered to be able to return false even when the mutex l is
// unlocked"); held states are strict (bound 1, no pick).

// unlocked Mutex: {1 (acquired), 0 (spurious false)}; gc: 1.
func tryLockUnlocked() int {
	var m sync.Mutex
	if m.TryLock() {
		m.Unlock()
		return 1
	}
	return 0
}

// locked Mutex: TryLock is false with no pick (bound 1); the holder's
// Unlock is still legal afterwards (the failed call changed nothing).
func tryLockLocked() int {
	var m sync.Mutex
	m.Lock()
	r := 10
	if m.TryLock() {
		r = 99
	}
	m.Unlock()
	return r
}

// a successful TryLock is a real acquisition: Unlock after it, then a
// second Lock proceeds. {1, 0}.
func unlockAfterTryLockSuccess() int {
	var m sync.Mutex
	if !m.TryLock() {
		return 0
	}
	m.Unlock()
	m.Lock()
	m.Unlock()
	return 1
}

// false then Lock: the worker holds the lock across main's TryLock
// (channel-ordered), releases, and main's Lock then acquires and reads
// the published value. Deterministic: 7.
func tryLockFalseThenLock() int {
	var m sync.Mutex
	held := make(chan struct{})
	release := make(chan struct{})
	done := make(chan struct{})
	x := 0
	go func() {
		m.Lock()
		close(held)
		<-release
		x = 7
		m.Unlock()
		close(done)
	}()
	<-held
	r := 0
	if m.TryLock() {
		r = 100
	}
	close(release)
	<-done
	m.Lock()
	r += x
	m.Unlock()
	return r
}

// a discarded TryLock (bare expression statement) still acquires: the
// second TryLock then sees a held mutex. 0 = the first acquired (second
// forced false) or both spuriously failed; 1 = the first spuriously
// failed and the second acquired. gc: 0.
func tryLockDiscarded() int {
	var m sync.Mutex
	m.TryLock()
	if m.TryLock() {
		return 1
	}
	return 0
}

// RWMutex: TryLock on an unlocked RWMutex. {1, 0}.
func rwTryLockUnlocked() int {
	var rw sync.RWMutex
	if rw.TryLock() {
		rw.Unlock()
		return 1
	}
	return 0
}

// RWMutex: TryRLock on an unlocked RWMutex. {1, 0}.
func rwTryRLockUnlocked() int {
	var rw sync.RWMutex
	if rw.TryRLock() {
		rw.RUnlock()
		return 1
	}
	return 0
}

// RWMutex: TryRLock while a reader holds — readers share: {1, 0}.
func rwTryRLockReaderHeld() int {
	var rw sync.RWMutex
	rw.RLock()
	r := 0
	if rw.TryRLock() {
		rw.RUnlock()
		r = 1
	}
	rw.RUnlock()
	return r
}

// RWMutex: TryLock while a reader holds — false, no pick.
func rwTryLockReaderHeld() int {
	var rw sync.RWMutex
	rw.RLock()
	r := 10
	if rw.TryLock() {
		r = 99
	}
	rw.RUnlock()
	return r
}

// RWMutex: TryRLock and TryLock while a writer holds — both false, no pick.
func rwTryWriterHeld() int {
	var rw sync.RWMutex
	rw.Lock()
	r := 20
	if rw.TryRLock() {
		r += 1
	}
	if rw.TryLock() {
		r += 2
	}
	rw.Unlock()
	return r
}

// RWMutex: TryRLock with a writer PENDING behind main's RLock. gc: the
// writer past readerCount.Add(-max) (rwmutex.go:152) forces false; a
// writer merely QUEUED behind rw.w (:150) leaves readerCount >= 0 and the
// TryRLock succeeds. The model's pendingW is one flag for both phases
// (sync design §8 R1), so the pick is OFFERED whenever no writer HOLDS
// (audit fix round F1): whether the writer has parked before main's
// TryRLock is L1 latitude and the pick is width 2 either way — set
// {0, 1}; gc (no sleep) shows 0 (the writer is past :152).
func rwTryRLockPendingWriter() int {
	var rw sync.RWMutex
	rw.RLock()
	started := make(chan struct{})
	done := make(chan struct{})
	go func() {
		close(started)
		rw.Lock()
		rw.Unlock()
		close(done)
	}()
	<-started
	r := 0
	if rw.TryRLock() {
		rw.RUnlock()
		r = 1
	}
	rw.RUnlock()
	<-done
	return r
}

// `defer m.TryLock()` (audit fix round F2): the deferred call runs at
// deferTryLock's exit and its Bool is DISCARDED (Go's rule for deferred
// results) — it still acquires. The caller's TryLock then sees a held
// mutex: {0 (deferred acquired, second forced false; or both spurious),
// 1 (deferred spurious, second acquired)}; gc: 0.
func deferTryLock(m *sync.Mutex) {
	defer m.TryLock()
}

func deferTryLockDiscarded() int {
	var m sync.Mutex
	deferTryLock(&m)
	if m.TryLock() {
		return 1
	}
	return 0
}

// spin until TryLock succeeds (the fairness-claim class, row 5): the
// CHILD spins on the mutex main holds and releases unordered with the
// spin; main blocks on the join (the atomics/spin shape — under the
// default stream main runs first, so the coupling runs terminate; the
// child-first / always-spurious schedules are nonterm branches under the
// declared accounting — NO termination claim). Terminating set {42}.
func spinUntilTryLock() int {
	var m sync.Mutex
	done := make(chan int)
	m.Lock()
	go func() {
		for !m.TryLock() {
		}
		m.Unlock()
		done <- 42
	}()
	m.Unlock()
	return <-done
}

func main() {
	println(tryLockUnlocked(), tryLockLocked(), unlockAfterTryLockSuccess(),
		tryLockFalseThenLock(), tryLockDiscarded(), rwTryLockUnlocked(),
		rwTryRLockUnlocked(), rwTryRLockReaderHeld(), rwTryLockReaderHeld(),
		rwTryWriterHeld(), rwTryRLockPendingWriter(), spinUntilTryLock(),
		deferTryLockDiscarded())
}
