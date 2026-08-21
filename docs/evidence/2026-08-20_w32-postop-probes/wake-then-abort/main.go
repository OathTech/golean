// Probe U-1 (latitude inventory; boundary-set note §6): wake the
// partner, then panic in the issuer's private segment. gc's DOMINANT
// member (189/200 at the note's phase-A run) is print-"42"-THEN-abort:
// main's println runs between the worker's wake-producing send and the
// program's abort — partner progress in the mid-program abort class.
// Pre-B1 the machine excluded it on every stream (127/127 panic, no
// output); stage C's post-op boundary admits it (see ../README.md for
// the recorded runs).
package main

func wakeThenAbort() int {
	ch := make(chan int, 1)
	go func() {
		ch <- 42
		panic("worker abort in the private segment")
	}()
	return <-ch
}

func main() {
	println(wakeThenAbort())
}
