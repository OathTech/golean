package main

import "runtime"

// FRONTIER MARKER (slice 6): runtime.Goexit — the mem#goexit clause's
// API surface ("The exit of a goroutine is not guaranteed to be
// synchronized before any event in the program"). The runtime package
// is stdlib, not spec, but the memory model documents this call
// explicitly, so the mem-census row needs a visible boundary: RED at
// frontend-export by design. Owner: the F4 concurrency arc's
// goroutine-destruction design question (ledger Q-GOEXIT) — Goexit
// runs deferred calls and terminates only its goroutine, which is a
// scheduler-architecture question, never a queue slot.

func goexitChild() int {
	done := make(chan int, 1)
	go func() {
		done <- 5
		runtime.Goexit()
	}()
	return <-done // 5: the send happens before the exit
}

func main() {
	goexitChild()
}
