package main

// Output is a TRACE: successive statements append in step order across
// loops and calls (the driver's fold of StepEvent.out).
func helper(i int) {
	print("[", i, "]")
}

func multipleCallsOrder() int {
	for i := 0; i < 3; i++ {
		println("line", i)
		helper(i)
	}
	print("\n")
	return 0
}
