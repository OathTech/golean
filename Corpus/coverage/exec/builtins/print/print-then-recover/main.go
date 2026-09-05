package main

// A RECOVERED panic keeps the run normal: the output continues after the
// recover and the readout is the recovered payload's evidence.
func printThenRecover() (r int) {
	defer func() {
		if recover() != nil {
			println("recovered")
			r = 1
		}
	}()
	println("about to panic")
	panic("x")
}
