package main

func rangeArrayPointerNilValuePanic() int {
	var p *[4]int
	sum := 0
	for i, v := range p {
		sum += i + v
	}
	return sum
}
