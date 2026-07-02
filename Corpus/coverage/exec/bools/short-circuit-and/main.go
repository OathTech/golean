package main

func boolShortCircuitAnd() int {
	calls := 0
	mark := func() bool {
		calls++
		return true
	}
	if false && mark() {
		return 100
	}
	return calls
}

func main() {
	boolShortCircuitAnd()
}
