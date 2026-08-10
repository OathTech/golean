package main

import "sync"

// PERMANENT-until-lifted refusal markers (arc-end fix round,
// 2026-08-10): composite-literal CONSTRUCTION of a modeled sync
// primitive (`&sync.Mutex{}`, `sync.WaitGroup{}`). Out of scope —
// the modeled construction surface is `var` declarations and `new`
// (design note §9) — but the refusal must name the capability, not
// the internal it happened to trip over: before this round the
// emitter descended into the primitive's underlying struct and
// refused on the unexported `sync.noCopy` field type. Red at
// frontend-export by design; gc runs both to completion (7 / 3).
func mutexAddrLit() int {
	m := &sync.Mutex{}
	m.Lock()
	x := 7
	m.Unlock()
	return x
}

func waitGroupValueLit() int {
	wg := sync.WaitGroup{}
	wg.Add(1)
	wg.Done()
	wg.Wait()
	return 3
}

func main() {
	mutexAddrLit()
}
