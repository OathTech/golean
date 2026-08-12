// Probe (b): registry-free spinner — NOT the definitional bug. The
// spawned goroutine performs no registry op at all, so no other
// goroutine's progress can depend on it. gc: exit 0, always. Machine:
// the default stream (and every stream that never picks the spinner at
// the .spawned boundary) runs main to its terminal and takes the L5
// exit-now pick — gc's observation IS in the modeled set
// (observed ∈ modeled). The machine's extra never-yielding streams
// (fuelOut) are the too-WIDE, transfer-safe direction; ∀-stream
// termination claims on this shape are the fairness quantifier's
// territory. See ../README.md.
package main

func registryFreeSpinner() int {
	go func() {
		for {
		}
	}()
	return 7
}

func main() {
	println(registryFreeSpinner())
}
