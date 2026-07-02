package main

func boolShortCircuitOr() int {
	calls := 0
	mark := func() bool {
		calls++
		return false
	}
	if true || mark() {
		return calls
	}
	return 100
}

func main() {
	boolShortCircuitOr()
}
