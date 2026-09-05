package main

import "math"

// Cross-width: a float32 pattern widened to float64 and read back
// (0x3FC00000 = 1.5f → 0x3FF8000000000000), and 1.0 narrowed.
func widening() (uint64, uint32) {
	f := math.Float32frombits(0x3FC00000)
	d := math.Float64frombits(0x3FF0000000000000)
	return math.Float64bits(float64(f)), math.Float32bits(float32(d))
}
