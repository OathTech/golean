// noodler frontier probe — map literal inside a short-circuit right operand
package main

// A map literal indexed in a short-circuit RHS.
func shortCircuitMapLiteral(n int) bool {
	return n > 0 && map[int]string{1: "one"}[n] == "one"
}

func main() {}
