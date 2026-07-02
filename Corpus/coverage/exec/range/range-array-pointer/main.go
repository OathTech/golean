package main

func rangeArrayPointer() int {
	p := &[3]int{4, 5, 6}
	sum := 0
	for i, v := range p {
		sum += i*10 + v
	}
	return sum
}
