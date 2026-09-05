package main

// The observation carries BOTH the readout values and the output; each is
// compared (a wrong value with the right output, or vice versa, is red).
func valuesAndOutput() (int, string) {
	println("side effect")
	return 7, "seven"
}
