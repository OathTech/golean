package main

func constantShiftWidthBoundaries() int {
	const uintTop = 1 << 15
	const intMin = -1 << 15
	var u uint16 = uintTop
	var i int16 = intMin
	return int(u) + int(i)
}
