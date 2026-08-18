// spec#Length_and_capacity block Length_and_capacity-3-4eda3abb: len of array composite literal is not constant when it contains a (non-constant) function call imag(z)
package main

const (
	c4 = len([10]float64{imag(2i)}) // imag(2i) is a constant and no function call is issued
	c5 = len([10]float64{imag(z)})  // invalid: imag(z) is a (non-constant) function call
)

var z complex128

func main() {}
