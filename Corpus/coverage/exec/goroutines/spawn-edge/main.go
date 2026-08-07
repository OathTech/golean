package main

// Spawn edges. PROBED (2026-08-07, go1.26.5): `go f()` with f nil is
// "fatal error: go of nil func value" — an UNRECOVERABLE runtime fatal
// raised AT THE GO STATEMENT in the SPAWNING goroutine (runtime
// newproc), exit status 2. This REFUTES the machine-shape note §6's
// analysis ("nil-callee panics at invocation in the CHILD, the
// deferCall rule") — defer's nil-invocation panic does NOT carry over
// to go. The machine fails CLOSED on a nil spawn callee this slice
// (the fatal class is unmodeled); the case is a deliberate red pin.

func spawnNilFuncFatal() int {
	var f func()
	go f() // fatal error: go of nil func value (in the spawner, always)
	<-make(chan int)
	return 0
}

// An unrecovered panic in a non-main goroutine aborts the program even
// while main is parked: the abort line is the child's payload.
func spawnChildPanicAborts() int {
	go func() {
		panic("child says no")
	}()
	<-make(chan int)
	return 0
}

// A recovered panic in a child is invisible: the child continues its
// normal exit and reports.
func spawnChildRecovers() int {
	done := make(chan int)
	go func() {
		defer func() {
			recover()
			done <- 17
		}()
		panic("caught")
	}()
	return <-done
}

func main() {
	spawnChildRecovers()
}
