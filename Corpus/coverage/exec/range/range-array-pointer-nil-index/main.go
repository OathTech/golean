package main

func rangeArrayPointerNilIndex() int {
	var p *[4]int
	sum := 0
	for i := range p {
		sum += i
	}
	return sum
}
