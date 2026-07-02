package main

func unsignedRightShift() int {
	var x uint8 = 0x80
	return int(x >> 7)
}

func main() {
	unsignedRightShift()
}
