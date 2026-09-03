// noodler frontier probe — make() inside a short-circuit right operand
package main

// An allocation (make) in a short-circuit RHS (spec#Logical_operators:
// the right operand is evaluated only if needed).
func shortCircuitAllocMake(n int) (bool, bool) {
	a := n > 0 && len(make([]int, n)) == n
	b := n < 0 || cap(make([]int, 0, n+1)) > n
	return a, b
}

func main() {}
