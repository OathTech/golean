// R14 probe: constant arithmetic THROUGH 500-bit intermediates,
// cancelling to a representable value. The spec requires only 256
// bits of integer-constant precision — a minimally-conforming
// implementation MAY reject this program; gc's go/constant is
// arbitrary-precision.
package main

const huge = 1 << 500
const x = huge / (1 << 490) // == 1024

func main() {
	println("x =", x)
}
