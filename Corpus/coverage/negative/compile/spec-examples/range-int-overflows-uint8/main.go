// spec#For_range block For_range-3-065c311b: range over int n with preexisting uint8 iteration variable: 256 cannot be assigned to uint8
package main

func main() {
	// invalid: 256 cannot be assigned to uint8
	var u uint8
	for u = range 256 {
	}
	_ = u
}
