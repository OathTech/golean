// R14 probe: float-constant precision + the mandated rounding at
// typed conversion. 1e-100 needs ~333 fractional bits relative to 1;
// a 256-bit-mantissa implementation may round tiny to 1.0 as a
// CONSTANT, while an arbitrary-precision one keeps tiny != 1.0
// exactly and rounds only at float64 conversion.
package main

const tiny = 1.0 + 1e-100

const constNE = tiny != 1.0 // constant-level comparison, exact arithmetic

func main() {
	println("const tiny != 1.0 (exact):", constNE)
	var f float64 = tiny
	println("float64(tiny) == 1.0:", f == 1.0)
}
