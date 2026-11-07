package main

// Sweep lane sweep/s22-readout (2026-11-07), shape S22 — the readout (the matrix is on the member entries'
// Neighbourhood lines in docs/BUGS.md, BUG-106/107/114 above all; the plan is
// docs/2026-10-27_defect-neighbourhood-campaign.md §4). Every row: expected = gc go1.26.5.
// Group B2/C: the status word, the abort message and the output prefix at each attributable report shape.

import "sync"

type T struct{ X int }

func printThenFatal() int {
	var mu sync.Mutex
	println("before fatal")
	mu.Unlock()
	return 0
}
func printThenDeadlock() int {
	ch := make(chan int)
	println("before deadlock")
	return <-ch
}
func printInDeferDuringPanic() int {
	defer func() { println("deferred during unwind") }()
	println("body")
	panic("unrecovered")
}
func deadlockDuringUnwind() int {
	ch := make(chan int)
	defer func() { <-ch }()
	panic("x")
}
func deadlockDuringUnwindOutput() int {
	ch := make(chan int)
	defer func() { println("in defer"); <-ch }()
	println("before")
	panic("x")
}
func printThenGoroutinePanic() int {
	ch := make(chan int)
	println("main printed")
	go func() { panic("from the goroutine") }()
	return <-ch
}
func fatalFromGoroutine() int {
	var mu sync.Mutex
	ch := make(chan int)
	go func() { mu.Unlock(); ch <- 1 }()
	return <-ch
}
func printThenNilDeref() int {
	var p *T
	println("before deref")
	return p.X
}
func goroutinePrintsThenMainPanics() int {
	done := make(chan int)
	go func() { println("goroutine printed"); close(done) }()
	<-done
	panic("main after goroutine")
}

func main() {
	printThenFatal()
	printThenDeadlock()
	printInDeferDuringPanic()
	deadlockDuringUnwind()
	deadlockDuringUnwindOutput()
	printThenGoroutinePanic()
	fatalFromGoroutine()
	printThenNilDeref()
	goroutinePrintsThenMainPanics()
}
