package main

import "sync"

// Detector-soundness probes, U4 family (Race.lean inventory: sync-OBJECT data
// accesses inside ops are not modeled — gc's -race build performs plain
// instrumented reads of the primitive's own words (race.Read(&rw.w) on every
// RWMutex op; Mutex.Unlock reads m.state; the CAS on m.state is an atomic
// TSan orders against plain accesses), so an in-use primitive OVERWRITTEN or
// COPIED by another goroutine is TSan-red where our footprint records nothing
// for the op. Misuse-only (also vet-red). Each subject isolates the sync-
// object access: no plain-data race is present, so any red is the U4 gap.

type u4MuBox struct {
	mu sync.Mutex
	x  int
}

type u4WgBox struct {
	wg sync.WaitGroup
	n  int
}

type u4RwBox struct {
	rw sync.RWMutex
	n  int
}

type u4OnceBox struct {
	o sync.Once
	n int
}

// U4-1: whole-struct overwrite of a struct holding a Mutex while a child
// locks/unlocks it. Only the mutex word conflicts. Expect TSan-red /
// machine-DRF (the U4 exhibit) — a HOLE-cell row by construction, diagnosed.
func u4StructOverwriteVsLock() int {
	var b u4MuBox
	done := make(chan int)
	go func() {
		b.mu.Lock()
		b.mu.Unlock()
		done <- 0
	}()
	b = u4MuBox{}
	<-done
	return b.x
}

// U4-2: whole-struct overwrite of a struct holding a WaitGroup while a child
// Adds/Dones on it. Expect TSan-red / machine-DRF (U4).
func u4WgOverwriteVsAdd() int {
	var w u4WgBox
	done := make(chan int)
	go func() {
		w.wg.Add(1)
		w.wg.Done()
		done <- 0
	}()
	w = u4WgBox{}
	<-done
	return w.n
}

// U4-3: whole-struct overwrite of a struct holding an RWMutex while a child
// RLocks it (gc: race.Read(&rw.w) on RLock). Expect TSan-red / machine-DRF.
func u4RwOverwriteVsRLock() int {
	var r u4RwBox
	done := make(chan int)
	go func() {
		r.rw.RLock()
		r.rw.RUnlock()
		done <- 0
	}()
	r = u4RwBox{}
	<-done
	return r.n
}

// U4-4: whole-struct overwrite of a struct holding a Once while a child
// calls Do on it. Expect TSan-red / machine-DRF.
func u4OnceOverwriteVsDo() int {
	var o u4OnceBox
	done := make(chan int)
	go func() {
		o.o.Do(func() {})
		done <- 0
	}()
	o = u4OnceBox{}
	<-done
	return o.n
}

// U4-5 CONTROL: a DISJOINT sibling-field write beside the lock — no sync-
// object word is touched by the write. Expect agree-DRF.
func u4DisjointFieldVsLock() int {
	var b u4MuBox
	done := make(chan int)
	go func() {
		b.mu.Lock()
		b.mu.Unlock()
		done <- 0
	}()
	b.x = 7
	<-done
	return b.x
}

// U4-6: COPY of a locked Mutex out of the struct (the read side of the
// misuse pair) while the child holds it. Expect TSan-red / machine-DRF.
func u4StructCopyVsLock() int {
	var b u4MuBox
	done := make(chan int)
	go func() {
		b.mu.Lock()
		b.mu.Unlock()
		done <- 0
	}()
	c := b
	<-done
	return c.x
}

func main() {
	println(u4StructOverwriteVsLock(), u4WgOverwriteVsAdd(), u4RwOverwriteVsRLock(),
		u4OnceOverwriteVsDo(), u4DisjointFieldVsLock(), u4StructCopyVsLock())
}
