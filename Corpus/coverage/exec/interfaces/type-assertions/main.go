package main

func typeAssertOk() int {
	var x any = "hello"
	_, okString := x.(string)
	v, okInt := x.(int)
	score := v
	if okString {
		score += 10
	}
	if okInt {
		score += 100
	}
	return score
}

func typeAssertPanic() int {
	var x any = "hello"
	return x.(int)
}
