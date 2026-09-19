package main

import "sync"

// B3-01 — NO alias: a copy of a NESTED struct holding a Mutex beside another goroutine's Lock on it.
// (A `.data`-only canonicalization would key the copy at `.field o $canon in` and leave the sync
// word structural at `.field (.field o outN "in") inN "mu"` — no longer a prefix — so this class
// would be MISSED. Both binaries here canonicalize/structure consistently, so both must refuse.)
type inN struct {
	mu sync.Mutex
	f  int
}
type outN struct {
	in inN
	g  int
}

func nestedMutexCopyNoAlias() int {
	var o outN
	done := make(chan int, 1)
	go func() {
		o.in.mu.Lock()
		o.in.f = 1
		o.in.mu.Unlock()
		done <- 0
	}()
	t := o.in
	<-done
	return t.f + o.in.f
}

// B3-02 — NO alias: the same for a WaitGroup's first-waiter sema write vs a nested copy.
type wgN struct {
	wg sync.WaitGroup
	f  int
}
type wgOutN struct {
	in wgN
	g  int
}

func nestedWgCopyNoAlias() int {
	var o wgOutN
	done := make(chan int, 1)
	o.in.wg.Add(1)
	go func() {
		o.in.wg.Wait()
		done <- 0
	}()
	t := o.in
	o.in.wg.Done()
	<-done
	return t.f
}
