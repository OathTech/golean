package main

// Convergence-round pin (BUG-031, pre-existing): the synthetic
// $deferRecoverNoop registration must not outlive a quarantined
// declaration. `spawnHelper` is quarantined (the `go` statement is
// unsupported) AFTER its `defer recover()` registered the no-op
// helper; a sticky registration flag then leaves the LATER, fully
// supported `goodRecover` referencing a function that was never
// emitted — wedging an unrelated subject.

func leak() {}

func spawnHelper() {
	defer recover()
	go leak()
}

func goodRecover() int {
	defer recover()
	return 2
}

func main() {
	println(goodRecover())
}
