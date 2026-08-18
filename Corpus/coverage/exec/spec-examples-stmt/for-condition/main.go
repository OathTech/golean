package main

// spec#For_condition block For_condition-1-fcb62f60: a single-
// condition for statement repeats "as long as a boolean condition
// evaluates to true"; "the condition is evaluated before each
// iteration" — so a false condition on entry runs the block zero
// times. The spec shape: for a < b { a *= 2 }.
// Expected: (1, 100) doubles 1 to 128 (first value >= 100);
// (5, 3) never enters the loop and returns 5; (3, 3) likewise 3
// (condition strictly <, checked before the first iteration).

func forConditionDouble(a, b int) int {
	for a < b {
		a *= 2
	}
	return a
}

func main() {
	forConditionDouble(1, 100)
}
