// noodler frontier probe — f(g()) tuple splat inside a short-circuit right operand
package main

func pair() (int, int) { return 1, 2 }
func sum(a, b int) int { return a + b }

// A multi-value call spread into another call inside a short-circuit RHS.
func shortCircuitSplatCall(n int) bool {
	return n > 0 && sum(pair()) == 3
}

func main() {}
