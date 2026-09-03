// noodler frontier probe — new() inside a short-circuit right operand
package main

// new() in a short-circuit RHS.
func shortCircuitAllocNew(n int) bool {
	return n > 0 && *new(int) == 0
}

func main() {}
