// Q-TRYLOCK gc probes — one subject per claim of the TryLock/TryRLock
// model (state transition, return value, TSan realization). Run as
// `probe <subject>`; each subject prints its observable and exits 0
// (or lets -race report). Headers state the EXPECTED verdict and why.
package main

import (
	"fmt"
	"os"
	"sync"
	"time"
)

// --- sync.Mutex -------------------------------------------------------

// unlocked mutex: TryLock → true (gc realizes only the success member;
// mem#locks permits false). Plain build. Expected: "true" 20/20.
func muUncontended() {
	var m sync.Mutex
	ok := m.TryLock()
	fmt.Println(ok)
}

// locked mutex: TryLock → false deterministically (the early return on
// the plain state read; no CAS). Expected: "false" 20/20.
func muLocked() {
	var m sync.Mutex
	m.Lock()
	ok := m.TryLock()
	fmt.Println(ok)
}

// a successful TryLock is a real acquisition: Unlock after it is legal,
// a second Lock then proceeds. Expected: "true 1" 20/20.
func muUnlockAfterTryLock() {
	var m sync.Mutex
	ok := m.TryLock()
	m.Unlock()
	m.Lock()
	m.Unlock()
	fmt.Println(ok, 1)
}

// false then Lock: a holder releases after the failed TryLock; the
// subsequent Lock acquires. Expected: "false 7" 20/20.
func muFalseThenLock() {
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
	ok := m.TryLock()
	close(release)
	<-done
	m.Lock()
	v := x
	m.Unlock()
	fmt.Println(ok, v)
}

// spin until TryLock succeeds (the fairness-class shape). gc terminates
// (the holder releases). Expected: "42" 20/20 in gc; the machine carries
// the always-spin schedules as nonterm branches.
func muSpinUntilTryLock() {
	var m sync.Mutex
	m.Lock()
	go func() {
		time.Sleep(time.Millisecond)
		m.Unlock()
	}()
	for !m.TryLock() {
	}
	fmt.Println(42)
}

// RACY: a plain overwrite of the mutex struct unordered with a TryLock
// on the UNLOCKED mutex. TSan: the TryLock's state CAS is an atomic
// write; the overwrite is a plain write → RACE. Expected -race: RACE.
func muOverwriteVsTryLock() {
	var m sync.Mutex
	var c1, c2 = make(chan struct{}), make(chan struct{})
	go func() { _ = m.TryLock(); close(c1) }()
	go func() { m = sync.Mutex{}; close(c2) }()
	<-c1
	<-c2
	fmt.Println("done")
}

// The failed-path twin: the mutex is LOCKED by main before the spawns,
// so the TryLock returns false on the plain (uninstrumented) state read
// — no TSan access — while another goroutine overwrites the struct.
// Expected -race: green (TSan sees only main's Lock CAS, HB-before both
// goroutines through the go statements). The machine records nothing
// on the locked-false path, so it agrees.
func muOverwriteVsFailedTryLock() {
	var m sync.Mutex
	m.Lock()
	var c1, c2 = make(chan struct{}), make(chan struct{})
	ok := false
	go func() { ok = m.TryLock(); close(c1) }()
	go func() { m = sync.Mutex{}; close(c2) }()
	<-c1
	<-c2
	fmt.Println("done", ok)
}

// DRF: a write under a successful TryLock, read under Lock elsewhere
// after the Unlock. Expected -race: green; value 5.
func muDrfTryLockPublish() {
	var m sync.Mutex
	x := 0
	done := make(chan struct{})
	ok := m.TryLock()
	x = 5
	m.Unlock()
	go func() {
		m.Lock()
		fmt.Println(x)
		m.Unlock()
		close(done)
	}()
	<-done
	fmt.Println(ok)
}

// RACY twin of the DRF row: the reader does NOT lock. Expected -race:
// RACE (the TryLock/Unlock pair orders nothing toward an unlocked read).
func muRacyTryLockNoAcquire() {
	var m sync.Mutex
	x := 0
	done := make(chan struct{})
	go func() {
		fmt.Println(x)
		close(done)
	}()
	_ = m.TryLock()
	x = 5
	m.Unlock()
	<-done
}

// A failed TryLock has NO synchronizing effect (mem#locks): the writer
// holds the lock, publishes x, unlocks; the reader's failed TryLock (while
// held) then a plain read of x is a RACE — the failed call acquired
// nothing. Expected -race: RACE (this is the "success-edge-only" claim's
// oracle twin; the machine must refuse too).
func muFailedTryLockNoEdge() {
	var m sync.Mutex
	x := 0
	held := make(chan struct{})
	release := make(chan struct{})
	done := make(chan struct{})
	go func() {
		m.Lock()
		close(held)
		<-release
		x = 9
		m.Unlock()
		close(done)
	}()
	<-held
	ok := m.TryLock() // false: held — acquires nothing
	close(release)
	time.Sleep(2 * time.Millisecond) // no HB edge toward the writer's x = 9
	fmt.Println(ok, x)
	<-done
}

// ISOLATING twin of muOverwriteVsFailedTryLock: the overwrite stores a
// copy of a LOCKED mutex, so whichever goroutine runs first the TryLock
// sees the locked bit and takes the plain-read early return (no CAS, no
// TSan access — internal/sync is a noRaceFuncPkgs package). Expected
// -race: green 20/20 — the failed path realizes nothing. (vet's
// copylocks would flag the copy; runtime behaviour is what is probed.)
func muOverwriteLockedVsFailedTryLock() {
	var m sync.Mutex
	m.Lock()
	locked := m // plain read of m, HB-before both spawns
	var c1, c2 = make(chan struct{}), make(chan struct{})
	ok := true
	go func() { ok = m.TryLock(); close(c1) }()
	go func() { m = locked; close(c2) }()
	<-c1
	<-c2
	fmt.Println("done", ok)
}

// a plain COPY beside a failed TryLock (mutex locked by main): read-like
// beside a realized nothing. Expected -race: green 20/20.
func muCopyVsFailedTryLock() {
	var m sync.Mutex
	m.Lock()
	var c1, c2 = make(chan struct{}), make(chan struct{})
	ok := true
	var c sync.Mutex
	go func() { ok = m.TryLock(); close(c1) }()
	go func() { c = m; close(c2) }()
	<-c1
	<-c2
	_ = c
	fmt.Println("done", ok)
}

// --- sync.RWMutex ------------------------------------------------------

// rw matrix: TryLock/TryRLock against unlocked / reader-held /
// writer-held states. Expected: "true true | true false | false false" 20/20:
//   unlocked:      TryLock true (then Unlock), TryRLock true (then RUnlock)
//   reader-held:   TryRLock true (readers may share), TryLock false
//   writer-held:   TryRLock false, TryLock false
func rwMatrix() {
	var rw sync.RWMutex
	a := rw.TryLock()
	rw.Unlock()
	b := rw.TryRLock()
	rw.RUnlock()
	rw.RLock()
	c := rw.TryRLock()
	if c {
		rw.RUnlock()
	}
	d := rw.TryLock()
	rw.RUnlock()
	rw.Lock()
	e := rw.TryRLock()
	f := rw.TryLock()
	rw.Unlock()
	fmt.Println(a, b, "|", c, d, "|", e, f)
}

// pending writer excludes new readers (rwmutex.go doc): a reader holds,
// a writer blocks in Lock, then TryRLock → false (readerCount negative).
// Expected: "false" 20/20.
func rwTryRLockPendingWriter() {
	var rw sync.RWMutex
	rw.RLock()
	writerParked := make(chan struct{})
	done := make(chan struct{})
	go func() {
		close(writerParked)
		rw.Lock()
		rw.Unlock()
		close(done)
	}()
	<-writerParked
	time.Sleep(2 * time.Millisecond) // let the writer park in Lock
	ok := rw.TryRLock()
	if ok {
		rw.RUnlock()
	}
	rw.RUnlock()
	<-done
	fmt.Println(ok)
}

// RACY: plain overwrite of the RWMutex beside a TryRLock (any outcome):
// every RWMutex op opens with race.Read(&rw.w) → plain read vs plain
// write. Expected -race: RACE.
func rwOverwriteVsTryRLock() {
	var rw sync.RWMutex
	var c1, c2 = make(chan struct{}), make(chan struct{})
	go func() { _ = rw.TryRLock(); close(c1) }()
	go func() { rw = sync.RWMutex{}; close(c2) }()
	<-c1
	<-c2
	fmt.Println("done")
}

// RACY (failed path too): the RWMutex is write-LOCKED by main, so the
// TryRLock returns false — but race.Read(&rw.w) runs before the
// Disable, so a concurrent overwrite is still a RACE. Expected -race:
// RACE. (Contrast muOverwriteVsFailedTryLock.)
func rwOverwriteVsFailedTryRLock() {
	var rw sync.RWMutex
	rw.Lock()
	var c1, c2 = make(chan struct{}), make(chan struct{})
	go func() { _ = rw.TryRLock(); close(c1) }()
	go func() { rw = sync.RWMutex{}; close(c2) }()
	<-c1
	<-c2
	fmt.Println("done")
}

// DRF through TryLock (RWMutex): write under a successful TryLock,
// read under RLock elsewhere after the Unlock. Expected -race: green.
func rwDrfTryLockPublish() {
	var rw sync.RWMutex
	x := 0
	done := make(chan struct{})
	ok := rw.TryLock()
	x = 6
	rw.Unlock()
	go func() {
		rw.RLock()
		fmt.Println(x)
		rw.RUnlock()
		close(done)
	}()
	<-done
	fmt.Println(ok)
}

// DRF through TryRLock (RWMutex): main writes under Lock, unlocks; the
// reader's successful TryRLock acquires the release. Expected -race: green.
func rwDrfTryRLockAcquire() {
	var rw sync.RWMutex
	x := 0
	done := make(chan struct{})
	rw.Lock()
	x = 8
	rw.Unlock()
	go func() {
		for !rw.TryRLock() {
		}
		fmt.Println(x)
		rw.RUnlock()
		close(done)
	}()
	<-done
}

func main() {
	if len(os.Args) != 2 {
		fmt.Fprintln(os.Stderr, "usage: probe <subject>")
		os.Exit(2)
	}
	switch os.Args[1] {
	case "muUncontended":
		muUncontended()
	case "muLocked":
		muLocked()
	case "muUnlockAfterTryLock":
		muUnlockAfterTryLock()
	case "muFalseThenLock":
		muFalseThenLock()
	case "muSpinUntilTryLock":
		muSpinUntilTryLock()
	case "muOverwriteVsTryLock":
		muOverwriteVsTryLock()
	case "muOverwriteVsFailedTryLock":
		muOverwriteVsFailedTryLock()
	case "muDrfTryLockPublish":
		muDrfTryLockPublish()
	case "muRacyTryLockNoAcquire":
		muRacyTryLockNoAcquire()
	case "muFailedTryLockNoEdge":
		muFailedTryLockNoEdge()
	case "muOverwriteLockedVsFailedTryLock":
		muOverwriteLockedVsFailedTryLock()
	case "muCopyVsFailedTryLock":
		muCopyVsFailedTryLock()
	case "rwMatrix":
		rwMatrix()
	case "rwTryRLockPendingWriter":
		rwTryRLockPendingWriter()
	case "rwOverwriteVsTryRLock":
		rwOverwriteVsTryRLock()
	case "rwOverwriteVsFailedTryRLock":
		rwOverwriteVsFailedTryRLock()
	case "rwDrfTryLockPublish":
		rwDrfTryLockPublish()
	case "rwDrfTryRLockAcquire":
		rwDrfTryRLockAcquire()
	default:
		fmt.Fprintln(os.Stderr, "unknown subject", os.Args[1])
		os.Exit(2)
	}
}
