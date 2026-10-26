package main

// Defect-neighbourhood campaign, shape S2 (conversions: a missing kernel arm or a
// value not retagged), lane sweep/s2-conversions, 2026-10-26: every row is an
// agreement with gc on a route no earlier row held (the matrix is on the member
// entries' Neighbourhood lines in docs/BUGS.md; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4).
// A struct holding a sync.Mutex field converted through a pointer (the field
// arms of structTagCompatible and the sync ops through the alias) and by VALUE
// (the kernel's struct arm copying a .syncData field).

import "sync"

type L1 struct {
	mu sync.Mutex
	n  int
}
type L2 struct {
	mu sync.Mutex
	n  int
}

func syncFieldPointerConv() int {
	var l L1
	p := (*L2)(&l)
	p.mu.Lock()
	p.n = 4
	p.mu.Unlock()
	l.mu.Lock()
	l.n++
	l.mu.Unlock()
	return l.n*10 + p.n
}

func syncFieldValueConv() int {
	var l L1
	l.n = 3
	m := L2(l)
	m.mu.Lock()
	m.n++
	m.mu.Unlock()
	l.mu.Lock()
	l.n += 10
	l.mu.Unlock()
	return l.n*10 + m.n
}

func main() {}
