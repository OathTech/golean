package main

// CL5 (window charter §4.5; docs/2026-10-03_window-corpus-disposition.md):
// the customer's callback shapes. A stored `step stepFunc` that takes
// its owner (`r.step(r, m)`, raft.go) and a stored `tick func()`, both
// reassigned between calls — dispatch follows the CURRENT value; one
// interface call site reaching two dynamic types (pointer and value
// receivers); a visitor callback that mutates and then panics at
// element k (the effects on elements before k survive); a Storage-like
// interface whose (value, error) replies keep sentinel identity. The
// external Storage/timer contracts themselves are out of scope (see the
// disposition note); the election draw `globalRand.Intn` in raft's
// locked-wrapper shape (raft.go after subject delta D-11) is the
// environment contract «some v in [0, n)», a membership row. A miniature fixture is NOT a proof of Raft.

import (
	"errors"
	"math/rand"
	"sync"
)

type stepFunc func(r *node, m int) int

type node struct {
	term  int
	ticks int
	step  stepFunc
	tick  func()
	log   int
}

func stepFollower(r *node, m int) int { r.log = r.log*10 + 1; return m + r.term }
func stepLeader(r *node, m int) int   { r.log = r.log*10 + 2; return m * r.term }

func (r *node) becomeLeader() {
	r.term++
	r.step = stepLeader
	r.tick = func() { r.ticks += 10 }
}

func storedDispatch() (int, int, int, int) {
	r := &node{term: 1, step: stepFollower}
	r.tick = func() { r.ticks++ }
	a := r.step(r, 5)
	r.tick()
	r.becomeLeader()
	b := r.step(r, 5)
	r.tick()
	return a, b, r.ticks, r.log
}

type describer interface{ describe() int }

type byVal struct{ v int }
type byPtr struct{ v int }

func (b byVal) describe() int  { return b.v + 100 }
func (b *byPtr) describe() int { return b.v + 200 }

// One call site, two callees; the value box holds a copy, the pointer
// box sees the later write.
func ifaceDispatch() (int, int) {
	v := byVal{v: 1}
	p := &byPtr{v: 2}
	ds := []describer{v, p}
	v.v, p.v = 7, 8
	sum := 0
	for i, d := range ds {
		sum = sum*1000 + d.describe() + i
	}
	return sum, len(ds)
}

type progress struct{ match int }

func visit(prs []*progress, f func(id int, pr *progress)) {
	for i, pr := range prs {
		f(i, pr)
	}
}

// The callback bumps each progress and panics at element k; the bumps
// on elements before k survive the recover, the rest never ran.
func visitorPanics(k int) (a, b, c, d int, rec string) {
	prs := []*progress{{1}, {2}, {3}, {4}}
	defer func() {
		if p := recover(); p != nil {
			rec = p.(string)
		}
		a, b, c, d = prs[0].match, prs[1].match, prs[2].match, prs[3].match
	}()
	visit(prs, func(id int, pr *progress) {
		if id == k {
			panic("visit failed")
		}
		pr.match += 10
	})
	return 0, 0, 0, 0, "done"
}

var (
	errCompacted   = errors.New("requested index is unavailable due to compaction")
	errUnavailable = errors.New("requested entry at index is unavailable")
)

type storage interface {
	Term(i uint64) (uint64, error)
}

type memStorage struct{ first, last uint64 }

func (ms *memStorage) Term(i uint64) (uint64, error) {
	if i < ms.first {
		return 0, errCompacted
	}
	if i > ms.last {
		return 0, errUnavailable
	}
	return i * 3, nil
}

func storageReply(i int) (uint64, bool, bool, bool) {
	var s storage = &memStorage{first: 4, last: 8}
	t, err := s.Term(uint64(i))
	return t, err == nil, err == errCompacted, err == errUnavailable
}

type lockedRand struct {
	mu sync.Mutex
}

func (r *lockedRand) Intn(n int) int {
	r.mu.Lock()
	v := rand.Intn(n)
	r.mu.Unlock()
	return v
}

var globalRand = &lockedRand{}

// raft's resetRandomizedElectionTimeout shape at electionTimeout 5.
func lockedJitter() int {
	electionTimeout := 5
	return electionTimeout + globalRand.Intn(electionTimeout)
}

func main() {
	println(storedDispatch())
	println(ifaceDispatch())
	println(visitorPanics(2))
	println(storageReply(2))
	println(lockedJitter())
}
