package main

func newSlicePointer() int {
	p := new([]int)
	score := 0
	if *p == nil {
		score += 10
	}
	*p = append(*p, 5)
	return score + len(*p)*100 + (*p)[0]
}

func main() {
	newSlicePointer()
}
