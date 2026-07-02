package main

func intConversionWidthMatrix() int {
	score := 0

	var neg16 int16 = -2
	if uint16(neg16) == 65534 {
		score += 1
	}

	var max16 uint16 = 65535
	if int16(max16) == -1 {
		score += 10
	}

	var max32 uint32 = 4294967295
	if int32(max32) == -1 {
		score += 100
	}

	var neg64 int64 = -1
	if uint8(neg64) == 255 {
		score += 1000
	}

	return score
}

func main() {
	intConversionWidthMatrix()
}
