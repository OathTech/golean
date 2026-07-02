package main

func rangeIntTyped() int {
	var n uint8 = 4
	var last uint8
	sum := 0
	for last = range n {
		sum += int(last)
	}
	return sum*10 + int(last)
}
