package main

// Sweep S12 — the abort REPORT from other CONTEXTS (matrix cells G02, G04,
// G05; lane sweep/s12-panic-recover, 2026-10-27): a panic two frames down,
// and a GOROUTINE's panic — the preprint rewrite (Error()) runs on the
// panicking goroutine, and a child's recovered-then-repanicked chain prints
// its head with ` [recovered]`. The machine: the pool's abort (`stepThread`'s
// tombstone arm) shares `abortMsg` with the sequential driver.

type myErr struct{ m string }

func (e myErr) Error() string { return e.m }

func level2() { panic("deep") }

func level1() { level2() }

func ctxNestedCall() { level1() }

func level2Err() { panic(myErr{"deep-error"}) }

func level1Err() { level2Err() }

func ctxNestedDefined() { level1Err() }

func ctxGoroutineErrorPayload() {
	done := make(chan int)
	go func() {
		panic(myErr{"g-text"})
	}()
	<-done
}

func ctxGoroutineRepanic() {
	done := make(chan int)
	go func() {
		defer func() {
			_ = recover()
			panic("g-second")
		}()
		panic("g-first")
	}()
	<-done
}

func main() {}
