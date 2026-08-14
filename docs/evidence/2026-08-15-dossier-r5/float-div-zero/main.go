// R5 probe: float division by zero — IEEE specials, and does a
// run-time panic occur? (Divisors are variables: constant division
// by zero is a compile-time error and not this latitude.)
package main

func main() {
	z := 0.0
	nz := -z
	println("1.0/z   =", 1.0/z)
	println("-1.0/z  =", -1.0/z)
	println("1.0/nz  =", 1.0/nz)
	println("z/z     =", z/z)
	var f32, z32 float32 = 1, 0
	println("f32/z32 =", f32/z32)
	println("reached end: no panic")
}
