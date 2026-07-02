package main

func intShiftWidthBoundaries() int {
	score := 0

	var x uint32 = 1
	var s uint = 32
	if x<<s == 0 {
		score += 1
	}

	var y int32 = -1
	if y>>31 == -1 {
		score += 10
	}

	var z uint8 = 128
	if z>>7 == 1 {
		score += 100
	}

	return score
}

func main() {
	intShiftWidthBoundaries()
}
