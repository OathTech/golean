// noodler frontier probe — slice literal inside a short-circuit right operand
package main

// A slice literal indexed in a short-circuit RHS.
func shortCircuitSliceLiteral(n int) bool {
	return n > 0 && []int{5, 6, 7}[n] == 6
}

func main() {}
