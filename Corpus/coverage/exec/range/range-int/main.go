package main

func rangeInt() int {
	sum := 0
	for i := range 4 {
		sum = sum*10 + i
	}
	return sum
}
