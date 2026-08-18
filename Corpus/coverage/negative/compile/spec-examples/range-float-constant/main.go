// spec#For_range block For_range-3-065c311b: range over numeric constant requires integer type: 1e3 is a floating-point constant
package main

func main() {
	// invalid: 1e3 is a floating-point constant
	for range 1e3 {
	}
}
