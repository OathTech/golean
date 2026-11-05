package main

import "sync"

// S16 sweep, family SYNC (the defect-neighbourhood campaign, lane sweep/s16-race,
// 2026-10-27; matrix §F9–F10): one primitive under two spellings, and primitives
// in slice and array elements — the sync-word keys and the handoff edge must fuse
// or stay apart as the cell does.

type muBox struct {
	mu sync.Mutex
	n  int
}

// F9: `p := &o.mu` and `o.mu` are one lock — the handoff edge orders the
// child's write before main's read; the result is one of {0, 1}.
func syncMutexTwoSpellings() int {
	var o muBox
	p := &o.mu
	done := make(chan int)
	go func() {
		p.Lock()
		o.n = 1
		p.Unlock()
		done <- 0
	}()
	o.mu.Lock()
	y := o.n
	o.mu.Unlock()
	<-done
	return y
}

// F10: two mutexes in one slice, each guarding its own variable.
func syncMutexSliceElemsDisjoint() int {
	mus := make([]sync.Mutex, 2)
	a, b := 0, 0
	done := make(chan int)
	go func() {
		mus[0].Lock()
		a = 1
		mus[0].Unlock()
		done <- 0
	}()
	mus[1].Lock()
	b = 2
	mus[1].Unlock()
	<-done
	return a*10 + b
}

// F10: one slice element contended by both goroutines.
func syncMutexSliceElemContended() int {
	mus := make([]sync.Mutex, 2)
	a := 0
	done := make(chan int)
	go func() {
		mus[0].Lock()
		a = a + 1
		mus[0].Unlock()
		done <- 0
	}()
	mus[0].Lock()
	a = a + 1
	mus[0].Unlock()
	<-done
	return a
}

// F10 (array spelling): the same two cells with a [2]sync.Mutex.
func syncMutexArrayElemsDisjoint() int {
	var mus [2]sync.Mutex
	a, b := 0, 0
	done := make(chan int)
	go func() {
		mus[0].Lock()
		a = 1
		mus[0].Unlock()
		done <- 0
	}()
	mus[1].Lock()
	b = 2
	mus[1].Unlock()
	<-done
	return a*10 + b
}

func main() {
	println(syncMutexTwoSpellings())
	println(syncMutexSliceElemsDisjoint())
	println(syncMutexSliceElemContended())
	println(syncMutexArrayElemsDisjoint())
}
