package main

func typedNilFuncInterface() int {
	var f func() int
	var x any = f
	score := 0
	if x != nil {
		score += 1
	}
	if x.(func() int) == nil {
		score += 10
	}
	return score
}

func main() {
	typedNilFuncInterface()
}
