package main

// THE SCHEDULER WEDGE, ENVELOPED (W3.2 slice 1 stages C+D — B1+B2;
// register #1's discharge row; evidence:
// docs/evidence/2026-08-12_scheduler-wedge-probes/ (the discovery
// record) and docs/evidence/2026-08-20_w32-postop-probes/ (the flip)).
// The worker performs ONE registry op (a cap-1 buffered send that wakes
// main) and then spins with no further registry op. Pre-B1 the machine
// excluded gc's observation (exit 0, 42 — 60/60 + 20/20 at
// GOMAXPROCS=1) on EVERY stream: 511/511 fuel-out over the exhaustive
// mod-2 depth-8 sweep — `observed ∉ modeled`, the essence doctrine's
// definitional bug. Post-B1 the completing execution is a member (the
// post-op `.opDone` boundary after the worker's send lets main run;
// stream [0,0,1] realizes it), and the always-spin branches remain
// members BY RIGHT (dossier §3.1: the spec allows starvation; §4.3:
// "the portable model should include the completing execution and an
// unfair execution") — counted honestly as the row's nonterm bucket,
// never observation members. Membership = oracle observation ∈ the
// TERMINATING set {42}; ∀-stream termination of this shape is the
// liveness tier's Fair question, deliberately NOT this row's claim.
func sendThenSpin() int {
	ch := make(chan int, 1)
	go func() {
		ch <- 42
		for {
		}
	}()
	return <-ch
}

func main() {
	sendThenSpin()
}
