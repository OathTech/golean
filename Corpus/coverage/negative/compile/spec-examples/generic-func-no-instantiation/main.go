// spec#Instantiations block Instantiations-2-e6028196: x := sum illegal: generic function must be instantiated when assigned to a variable of unknown type
package main

// sum returns the sum (concatenation, for strings) of its arguments.
func sum[T ~int | ~float64 | ~string](x ...T) T {
	var s T
	for _, v := range x {
		s += v
	}
	return s
}

func main() {
	x := sum // illegal: the type of x is unknown
	_ = x
}
