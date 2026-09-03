// noodler frontier probe — func literal call as a switch case expression
package main

// A func literal invoked inside a switch case expression.
func closureInSwitchCaseExpr(x int) int {
	switch x {
	case func() int { return 1 }():
		return 10
	case func() int { return 2 }():
		return 20
	}
	return 0
}

func main() {}
