// Probe (a): send-then-spin — the genuine observed-∉-modeled scheduler
// wedge (inventory C2+C3; register #1). The worker performs ONE registry
// op (a cap-1 buffered send) and then spins with no further registry op.
// gc: main receives and exits 0, always. Machine: after the worker's send
// apply-position boundary, the fused effect boundary (C3) provides no
// post-op scheduling point and forced continuation (C2) runs the worker's
// registry-free tail privately forever — exit-0 is unreachable on EVERY
// choice stream. See ../README.md for the recorded runs and the
// reachable-set argument.
package main

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
	println(sendThenSpin())
}
