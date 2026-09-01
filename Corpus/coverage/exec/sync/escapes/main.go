package main

import "sync"

// The sync-op ESCAPE shapes (audit fix round 2026-08-10, F4): each
// used to escape both interception points and land as a runtime
// `stuck`; the F4 round quarantined them per-decl. LIFT HISTORY:
// W4.1 item 5 lifted the promoted statement/defer shapes (`promoted`,
// `defer-embedded`); the Q-SYNCVAL slice (P-S2-6, 2026-09-01) lifted
// the VALUE shapes — method values (argument-taking ones included),
// go-position callees, promoted method values, and sync ops passed as
// callbacks. Every value shape lowers to a func-value over the BODIED
// sync method stub, whose body is the same sync-op the direct call
// emits (the identity principle, [USER]-RULED 2026-08-31): same op,
// same C8 site, or refusal — never a variant.

type lockedBox struct {
	sync.Mutex
	n int
}

// Promoted call on an embedding struct (statement position; W4.1
// item 5 — etcd-raft's MemoryStorage idiom).
func escapePromoted() int {
	var b lockedBox
	b.Lock()
	b.n = 5
	b.Unlock()
	return b.n
}

// Method value.
func escapeMethodValue() int {
	var m sync.Mutex
	f := m.Lock
	f()
	m.Unlock()
	return 3
}

// go-statement sync callee.
func escapeGoStmt() int {
	var wg sync.WaitGroup
	wg.Add(1)
	go wg.Done()
	wg.Wait()
	return 2
}

// defer on an embedded receiver.
func escapeDeferEmbedded() int {
	var b lockedBox
	b.Lock()
	defer b.Unlock()
	b.n = 7
	return b.n
}

// Method value WITH an argument (gc: 4): Add's delta threads through
// the bodied stub's parameter.
func escapeMethodValueAdd() int {
	var wg sync.WaitGroup
	f := wg.Add
	f(2)
	wg.Done()
	wg.Done()
	wg.Wait()
	return 4
}

// MISUSE IDENTITY through a value: the method-value invocation
// consumes the same wgAdd op, so driving the counter negative panics
// with gc's fixed message exactly like the direct form
// (sync/waitgroup-negative-panic) — never a variant that absorbs.
func escapeMethodValueNegative() int {
	var wg sync.WaitGroup
	f := wg.Add
	f(-1)
	return 0
}

// Once.Do as a method value (gc: 3): both invocations consume the same
// once cell.
func escapeOnceDoValue() int {
	var o sync.Once
	n := 0
	g := o.Do
	g(func() { n += 3 })
	g(func() { n += 5 })
	return n
}

// PROMOTED method value on an embedding struct (the last F4 shape):
// the receiver adjusts to the embedded primitive's address AT VALUE
// TIME (design note D1.2), so the func-value captures &b.Mutex and
// invokes the same bodied stub.
func escapePromotedMethodValue() int {
	var b lockedBox
	f := b.Lock
	f()
	b.n = 6
	b.Unlock()
	return b.n
}

// A sync op PASSED AS A CALLBACK: the callee invokes the caller's
// mutex op through a plain func-typed parameter.
func with(f func()) { f() }

func escapePassedCallback() int {
	var m sync.Mutex
	with(m.Lock)
	x := 12
	with(m.Unlock)
	return x
}

func main() {
	escapePromoted()
	escapeMethodValue()
	escapeGoStmt()
	escapeDeferEmbedded()
}
