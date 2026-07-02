package main

func typedNilSliceInterface() int {
	var s []int
	var x any = s
	score := 0
	if x != nil {
		score += 1
	}
	if x.([]int) == nil {
		score += 10
	}
	return score + len(x.([]int))*100
}

func main() {
	typedNilSliceInterface()
}
