package main

import "sync"

// PERMANENT-until-lifted refusal markers (audit fix round 2026-08-10,
// F4): the sync surface is DIRECT statement/defer-position calls only;
// each shape below used to escape both interception points and land as
// a runtime `stuck` on a dangling `sync.X.Y` call — not a visible
// refusal. Each now quarantines per-decl at the frontend with a
// precise reason (red at frontend-export by design). The promoted
// shape is north-star-relevant (etcd-raft's MemoryStorage embeds
// sync.Mutex) — lifting it is the recorded follow-up.

type lockedBox struct {
	sync.Mutex
	n int
}

// Promoted call on an embedding struct.
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

func main() {
	escapePromoted()
	escapeMethodValue()
	escapeGoStmt()
	escapeDeferEmbedded()
}
