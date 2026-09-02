package main

import "sync"

// Detector-soundness probes, U5 family (Race.lean inventory: cross-goroutine
// unlock without a handoff HB edge — the machine's release is the memory-
// model MERGE ("for n < m, call n of l.Unlock() is synchronized before call m
// of l.Lock() returns", unconditional); gc's TSan hook is the OVERWRITE
// race.Release, so an owner-free unlocker lacking HB from the prior critical
// section DROPS that section's clock and TSan reports a race go_mem orders).

var u5G int

// U5-1: the eval-pin shape (Tests/GoCoreEval.lean `syncXUnlockMain`): main
// holds the lock, spawns W1 (the owner-free unlocker) and W2 (the locker-
// reader) BEFORE publishing, publishes, unlocks, re-locks; W1 unlocks
// owner-free (legal: "a locked Mutex is not associated with a particular
// goroutine", probe p09); W2 locks and reads. go_mem: DRF (Unlock #1 is
// synchronized before Lock #3). TSan: W1's overwrite-Release drops main's
// clock → DATA RACE. Expected: gc RACE / machine DRF — a HOLE-cell row whose
// diagnosis is "TSan over-reports a go_mem-DRF program" (U5), not "SC given
// to a racy program". Paths where W1 unlocks before main's own Unlock are
// the fatal "unlock of unlocked mutex" members (enumerated, never a race).
func u5CrossUnlockPublish() int {
	u5G = 0
	var mu sync.Mutex
	ch := make(chan int)
	mu.Lock()
	go func() {
		mu.Unlock()
	}()
	go func() {
		mu.Lock()
		ch <- u5G
		mu.Unlock()
	}()
	u5G = 1
	mu.Unlock()
	mu.Lock()
	z := <-ch
	return z
}

// U5-2 CONTROL: the same three goroutines with a HANDOFF — the unlocker
// receives a signal sent after the publish, so its clock carries the
// critical section and overwrite = merge here. Expect agree-DRF.
func u5HandoffUnlock() int {
	u5G = 0
	var mu sync.Mutex
	sig := make(chan int)
	ch := make(chan int)
	mu.Lock()
	go func() {
		<-sig
		mu.Unlock()
	}()
	go func() {
		mu.Lock()
		ch <- u5G
		mu.Unlock()
	}()
	u5G = 1
	sig <- 0
	z := <-ch
	return z
}

func main() {
	println(u5CrossUnlockPublish(), u5HandoffUnlock())
}
