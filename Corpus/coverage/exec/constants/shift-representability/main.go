package main

func constantShiftRepresentability() int {
	const topBit = 1 << 7
	var b byte = topBit
	return int(b)
}
