package main

// spec#If_statements block If_statements-2-3dfe8916: "if the
// expression evaluates to true, the 'if' branch is executed,
// otherwise ... the 'else' branch" (none here). The spec's clamp
// shape: if x > max { x = max }. Expected: x above max is clamped to
// max; x at or below max is unchanged.

func ifSimpleClamp(x, max int) int {
	if x > max {
		x = max
	}
	return x
}

func main() {
	ifSimpleClamp(9, 5)
}
