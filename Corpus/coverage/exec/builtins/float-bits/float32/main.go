package main

import "math"

// The float32 pair: 1.5 → 0x3FC00000; a NaN payload round trip (quiet
// 0x7FC00001 and signalling 0x7F800001); the runtime -0 (0x80000000);
// 0.1 at single precision (0x3DCCCCCD); +Inf from an overflowing product.
func float32Bits() (uint32, uint32, uint32, uint32, uint32, uint32, bool) {
	var z float32 = 0
	nz := -z
	var f float32 = 0.1
	var big float32 = 3e38
	inf := big * 10
	q := math.Float32frombits(0x7FC00001)
	return math.Float32bits(1.5), math.Float32bits(q), math.Float32bits(math.Float32frombits(0x7F800001)),
		math.Float32bits(nz), math.Float32bits(f), math.Float32bits(inf), q != q
}
