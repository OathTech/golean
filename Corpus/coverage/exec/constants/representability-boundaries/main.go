package main

func constantRepresentabilityBoundaries() int {
	const minInt8 = -128
	const maxInt8 = 127
	const maxUint8 = 255
	const maxInt16 = 32767
	var a int8 = minInt8
	var b int8 = maxInt8
	var c uint8 = maxUint8
	var d int16 = maxInt16
	return int(a) + int(b) + int(c) + int(d)
}
