package main

// SLICE-4 GUARDRAIL (red on purpose): a select with MORE than one ready
// case is the L2 latitude point ("uniform pseudo-random selection" —
// design of record D4: envelope = any entry-ready case, a Choices site).
// The deterministic slice-1 machine REFUSES it (fail closed,
// `.unsupported`) rather than picking silently; this case pins that
// classification until the scheduler arc's slice 4 makes the choice a
// membership-lane envelope. The two ready cases are CONFLUENT (same
// observable) so the go-run side is deterministic; the red is entirely
// ours, at the lean-observation stage.

func channelSelectMultiReadyConfluent() int {
	a := make(chan int, 1)
	b := make(chan int, 1)
	a <- 4
	b <- 4
	got := 0
	select {
	case v := <-a:
		got = v
	case v := <-b:
		got = v
	}
	return got*10 + len(a) + len(b)
}

func main() {
	channelSelectMultiReadyConfluent()
}
