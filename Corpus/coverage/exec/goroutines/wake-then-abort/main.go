package main

// U-1, PROBED AND ENVELOPED (W3.2 slice 1 stage C — B1's post-op
// boundaries; latitude inventory U-1; boundary-set note §6): wake the
// partner, then panic in the issuer's private segment. The envelope is
// status-diverse {panic, ok(42)}:
//
//   panic — the worker continues past its wake-producing send and its
//     panic aborts the program (the pre-B1 machine's SOLE member on
//     every stream; gc-dominant in some sessions: silent-abort
//     140/200 this session, 11/200 at the phase-A run).
//   ok 42 — MAIN PROGRESSES between the worker's send and the
//     worker's abort: the post-op `.opDone` boundary after the send
//     (B1) lets main take the delivered value, reach its terminal,
//     and the main-exit window's exit-now pick (L5) ends the program
//     first (spec#Program_execution: "It does not wait for other
//     (non-main) goroutines to complete"). gc's print-"42"-then-abort
//     observation (60/200 this session, 189/200 at the phase-A run —
//     the class pre-B1 EXCLUDED on every stream) is this same
//     partner-progress class at the output observable: main's println
//     runs between wake and abort; the print-vs-exit split is L5-tail
//     latitude inside the admitted class (evidence:
//     docs/evidence/2026-08-20_w32-postop-probes/).
//
// The scheduling-semantics dossier grounds the width: §1.1 (scheduling
// deliberately unspecified — the widening is conservative relative to
// what the language licenses), §3.1 (no eventual-scheduling guarantee
// in the spec — the abort-first member stays by right).
func wakeThenAbort() int {
	ch := make(chan int, 1)
	go func() {
		ch <- 42
		panic("worker abort in the private segment")
	}()
	return <-ch
}

func main() {
	wakeThenAbort()
}
