// R14 probe: 5000-bit intermediates (far beyond the 256-bit
// minimum). Does gc accept?
package main

const y = (1 << 5000) / (1 << 4990) // == 1024

func main() {
	println("y =", y)
}
