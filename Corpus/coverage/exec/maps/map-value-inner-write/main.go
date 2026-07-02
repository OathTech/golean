package main

func mapValueInnerWrite() int {
	inner := map[int]int{1: 2}
	outer := map[int]map[int]int{3: inner}
	outer[3][1] = 7
	return inner[1]*10 + outer[3][1]
}
