package main

func rangeStringIndexOnly() int {
	s := "hé!"
	sum := 0
	for i := range s {
		sum = sum*10 + i
	}
	return sum
}
