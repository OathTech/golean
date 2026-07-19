package main

// A blank target discarding a non-int result. A frontend that types the
// discard temp as int corrupts or gets stuck storing the bool.
func twoResults() (bool, int) { return true, 42 }

func blankDiscardNonint() int {
	_, n := twoResults()
	return n
}
